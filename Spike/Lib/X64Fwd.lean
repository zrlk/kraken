/-
**Forward execution of one thread on an `ExtMachine.ofHooks` instance**:
from a configuration where thread `tid` runs alone in the sense of `Solo`
(it exists, carries no promise, has its views bounded by `|M|`, and the
hooks let it run), each of Kraken's four promise-free instruction shapes
has a step of the instance, to a configuration that is again `Solo` at the
instruction's next state.

The direction is the converse of the safety layer (`Spike/Lib/ExtThread.lean`,
"every step is …"): here a step **exists**. It is what a closed
non-vacuity statement ("some run of the loaded program reaches a state with
these facts") needs.

- `Solo c tid s`: thread `tid` of `c` is in state `s`, with no promise and
  `Thread.Bnd` against `c.1.mem.last`; the hooks record no exit and do not
  mark the thread done.
- `fwd_treeP` / `fwd_tree`: the core lemma. If `I.exec s = some tree` and,
  for every such thread, the tree has a finished run from `ctx0` to
  `(s', c'')` with no promise, the instance takes a step of `tid` with no
  events to a `Solo` configuration at `s'` with memory `c''.mem`, the
  extension state and every other thread unchanged.
- The four shapes (`LiveTicketStep`, `LiveTsoRmw`): `fwd_done` (memory
  unchanged), `fwd_silent` (a `Lower.SilentTree`: some leaf), `fwd_load` (reads `mem.finalVal l`, memory unchanged),
  `fwd_store` (appends the message), `fwd_rmw` (under `A.rmwFence`, e.g.
  TSO: reads `mem.finalVal l` and appends `g` of it).
- Each comes in a continuation form (`*_k`): the goal `∃ c', Run μ c tr c' ∧
  Q c'` is reduced to the same goal at the next configuration, so a run is
  a chain of `refine fwd_*_k … (fun c1 h1 … => ?_)`.

Nothing here is specific to an ISA or a program.
-/
import Scc.Sem.Target
import Kraken.Promising.LiveTicketStep
import Kraken.Promising.LiveTsoRmw
import Kraken.Promising.LiveSpinStep
import Kraken.Promising.ReleasePrefixNT
import Kraken.Promising.Lower.Silent

namespace Spike.Lib.Fwd

open Scc.Sem Kraken Kraken.Promising

variable {I : ISA} {A : Arch} {H : Hooks I} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat} {μ : Marks}

/-- **Thread `tid` runs alone at state `s`**: it exists in state `s` with no
outstanding promise and its views bounded by `|M|`, the process has not
exited, and the hooks do not mark the thread done. -/
structure Solo (c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg) (tid : Nat) (s : I.State) : Prop where
  thread : ∃ t : Thread I, c.1.threads[tid]? = some t ∧ t.st = s ∧ t.prom = [] ∧ t.Bnd c.1.mem.last
  exited : H.exited c.2 = none
  running : ¬ H.threadDone c.2 tid

/-- What a forward step keeps: the extension state and every other thread. -/
def Keeps (tid : Nat) (c c' : (ExtMachine.ofHooks I A H rv pl pcf).Cfg) : Prop :=
  c'.2 = c.2 ∧ ∀ i, i ≠ tid → c'.1.threads[i]? = c.1.threads[i]?

theorem Keeps.refl (tid : Nat) (c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg) : Keeps tid c c :=
  ⟨rfl, fun _ _ => rfl⟩

theorem Keeps.trans {tid : Nat} {c c' c'' : (ExtMachine.ofHooks I A H rv pl pcf).Cfg}
    (h : Keeps tid c c') (h' : Keeps tid c' c'') : Keeps tid c c'' :=
  ⟨h'.1.trans h.1, fun i hi => (h'.2 i hi).trans (h.2 i hi)⟩

/-- A step followed by a run. -/
theorem run_cons {tid : Nat} {c c' c'' : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {es tr : List Ev}
    (h : (ExtMachine.ofHooks I A H rv pl pcf).Step μ tid c es c')
    (h' : (ExtMachine.ofHooks I A H rv pl pcf).Run μ c' tr c'') :
    (ExtMachine.ofHooks I A H rv pl pcf).Run μ c (es ++ tr) c'' :=
  LRun.step ⟨tid, h⟩ h'

/-- A step is a run with its events. -/
theorem run_of_step {tid : Nat} {c c' : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {es : List Ev}
    (h : (ExtMachine.ofHooks I A H rv pl pcf).Step μ tid c es c') :
    (ExtMachine.ofHooks I A H rv pl pcf).Run μ c es c' := by
  have := run_cons (μ := μ) h (LRun.refl c')
  rwa [List.append_nil] at this

/-- **The core forward step.** A `Solo` thread whose next instruction has the
tree `tree` (off a system call and off the transfer sites), where for every
promise-free bounded thread in state `s` the tree has a finished run from
`ctx0` to some `(s', c'')` with `P s'`, no promise and memory `M'`: the
instance takes a step of `tid` with no events to a configuration that is
`Solo` at such an `s'`, with memory `M'`, keeping the extension state and
the other threads. -/
theorem fwd_treeP {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s : I.State}
    {tree : EvTree I.State} {M' : Memory} {P : I.State → Prop}
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some tree)
    (hr : ∀ t : Thread I, t.st = s → t.prom = [] → t.Bnd c.1.mem.last →
      ∃ (s' : I.State) (c'' : Ctx), P s' ∧ .ok (s', c'') ∈ runTree A tid (instrViews t (I.deps t.st))
          (Live.TicketStep.ctx0 tid t c.1.mem) tree ∧ c''.mem = M' ∧ c''.prom = []) :
    ∃ s' c', P s' ∧ (ExtMachine.ofHooks I A H rv pl pcf).Step μ tid c [] c' ∧ Solo c' tid s' ∧
      c'.1.mem = M' ∧ Keeps tid c c' := by
  obtain ⟨t, ht, hst, hp, hb⟩ := h.thread
  obtain ⟨s', c'', hP, hrun, hm, hpr⟩ := hr t hst hp hb
  subst hst
  obtain ⟨outs, o, hs, ho, hom, host, hopr⟩ := Live.TicketStep.stepOne_of_run A tid hex hrun
  have hb' := (stepOne_bnd A hs ho hb).1
  have hp' : o.thread.prom = [] := hopr.trans hpr
  have hns : ¬ (ExtMachine.ofHooks I A H rv pl pcf).atSys c tid := fun ⟨t', ht', h'⟩ => by
    have e : t = t' := Option.some.inj (ht.symm.trans ht')
    subst e
    rw [hsys] at h'
    exact Bool.false_ne_true h'
  have hnsite : ∀ k, ¬ (ExtMachine.ofHooks I A H rv pl pcf).AtSite μ k c tid := fun k ⟨a, ha, t', ht', hpc⟩ => by
    have e : t = t' := Option.some.inj (ht.symm.trans ht')
    subst e
    exact hsite k a ha hpc
  refine ⟨s', (c.1.withThread tid o.thread o.mem, c.2), hP,
    .instr ⟨⟨t, ht⟩, h.exited, h.running⟩ hns hnsite
      (.inl ⟨t, outs, o, ht, hs, ho, certOkC_of_prom_nil hp', rfl⟩),
    ⟨⟨o.thread, ExtMachine.withThread_self ht, host, hp', hb'⟩, h.exited, h.running⟩,
    hom.trans hm, rfl, fun i hi => ?_⟩
  have e := Config.withThread_get? (c.1 : Config I) (i := i) o.thread o.mem (lt_size_of_get? ht)
  rw [ite_eq_right_iff.mpr (fun h => absurd h.symm hi)] at e
  exact e

/-- `fwd_treeP` at a fixed next state `s'`. -/
theorem fwd_tree {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s s' : I.State}
    {tree : EvTree I.State} {M' : Memory}
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some tree)
    (hr : ∀ t : Thread I, t.st = s → t.prom = [] → t.Bnd c.1.mem.last →
      ∃ c'' : Ctx, .ok (s', c'') ∈ runTree A tid (instrViews t (I.deps t.st))
          (Live.TicketStep.ctx0 tid t c.1.mem) tree ∧ c''.mem = M' ∧ c''.prom = []) :
    ∃ c', (ExtMachine.ofHooks I A H rv pl pcf).Step μ tid c [] c' ∧ Solo c' tid s' ∧ c'.1.mem = M' ∧
      Keeps tid c c' := by
  obtain ⟨_, c', rfl, hs, h', hm, hk⟩ := fwd_treeP (P := (· = s')) h hsys hsite hex fun t h1 h2 h3 => by
    obtain ⟨c'', hr, hm, hp⟩ := hr t h1 h2 h3
    exact ⟨s', c'', rfl, hr, hm, hp⟩
  exact ⟨c', hs, h', hm, hk⟩

/-- The empty context of `stepOne` is bounded when the thread is. -/
theorem ctx0_bnd {t : Thread I} {tid : Nat} {mem : Memory} (hb : t.Bnd mem.last) :
    (Live.TicketStep.ctx0 tid t mem).Bnd :=
  ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩

/-! ## The four shapes -/

/-- **A no-event instruction** (`.done s'`): memory unchanged. -/
theorem fwd_done {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s s' : I.State}
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some (.done s')) :
    ∃ c', (ExtMachine.ofHooks I A H rv pl pcf).Step μ tid c [] c' ∧ Solo c' tid s' ∧ c'.1.mem = c.1.mem ∧
      Keeps tid c c' :=
  fwd_tree h hsys hsite hex fun _ _ hp _ =>
    ⟨_, Live.TicketStep.run_done_exists A tid _ _ s', rfl, hp⟩

/-- **A silent instruction** (a finite choice of `.done` leaves, x64's
undefined-flag rows, `Lower.SilentTree`): some leaf satisfying `P` is taken;
memory unchanged. -/
theorem fwd_silent {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s : I.State}
    {tree : EvTree I.State} {P : I.State → Prop}
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some tree) (hsil : Lower.SilentTree P tree) :
    ∃ s' c', P s' ∧ (ExtMachine.ofHooks I A H rv pl pcf).Step μ tid c [] c' ∧ Solo c' tid s' ∧
      c'.1.mem = c.1.mem ∧ Keeps tid c c' :=
  fwd_treeP h hsys hsite hex fun t _ hp _ => by
    obtain ⟨s', hP, hr⟩ := Lower.SilentTree.exists_run A tid (instrViews t (I.deps t.st))
      (c := Live.TicketStep.ctx0 tid t c.1.mem) hsil
    exact ⟨s', _, hP, hr, rfl, hp⟩

/-- **A load that always finishes** (`.load k false l (fun v => .done (f v))`):
it can read the last write of `l`; memory unchanged. -/
theorem fwd_load {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s : I.State}
    {k : LoadKind} {l : Loc} {f : Val → I.State}
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some (.load k false l fun v => .done (f v))) :
    ∃ c', (ExtMachine.ofHooks I A H rv pl pcf).Step μ tid c [] c' ∧ Solo c' tid (f (c.1.mem.finalVal l)) ∧
      c'.1.mem = c.1.mem ∧ Keeps tid c c' :=
  fwd_tree h hsys hsite hex fun t _ hp _ => by
    obtain ⟨c'', hr⟩ := Live.TicketStep.run_load_exists A tid (instrViews t (I.deps t.st))
      (c := Live.TicketStep.ctx0 tid t c.1.mem) hp k l f
    obtain ⟨-, -, -, -, -, -, hm, hpr, -⟩ := Live.TicketStep.run_load A tid _ hr
    exact ⟨c'', hr, hm, hpr.trans hp⟩

/-- **A plain non-exclusive store** (`.store k false l v (fun _ => .done s')`):
it appends its message. -/
theorem fwd_store {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s s' : I.State}
    {k : StoreKind} {l : Loc} {v : Val}
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some (.store k false l v fun _ => .done s')) :
    ∃ c', (ExtMachine.ofHooks I A H rv pl pcf).Step μ tid c [] c' ∧ Solo c' tid s' ∧
      c'.1.mem = (c.1.mem.append { loc := l, val := v, tid }).1 ∧ Keeps tid c c' :=
  fwd_tree h hsys hsite hex fun t _ hp hb => by
    obtain ⟨c'', hr⟩ := Live.TicketStep.run_store_exists A tid (instrViews t (I.deps t.st))
      (c := Live.TicketStep.ctx0 tid t c.1.mem) hp hb.views.le (instrViews_le hb.regs _) k l v s'
    obtain ⟨-, hm, hpr⟩ := Live.TicketStep.run_store A tid _ hp hr
    exact ⟨c'', hr, hm, hpr⟩

/-- **An always-writing RMW under `rmwFence`** (TSO's locked instructions,
`.rmw k false l (fun old => some (g old)) (fun v => .done (f v))`): it can
read the last write of `l` and append `g` of it. -/
theorem fwd_rmw {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s : I.State}
    {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State} (hA : A.rmwFence = true)
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v))) :
    ∃ c', (ExtMachine.ofHooks I A H rv pl pcf).Step μ tid c [] c' ∧ Solo c' tid (f (c.1.mem.finalVal l)) ∧
      c'.1.mem = (c.1.mem.append { loc := l, val := g (c.1.mem.finalVal l), tid }).1 ∧ Keeps tid c c' :=
  fwd_tree h hsys hsite hex fun t _ hp hb => by
    -- the run `run_rmwo_tso_exists` builds, with the write's memory kept
    let iv := instrViews t (I.deps t.st)
    let c := Live.TicketStep.ctx0 tid t c.1.mem
    have hiv : iv.Le c.mem.last := instrViews_le hb.regs _
    let c0 := fenceStep c .sy
    have hb0 : c0.Bnd := fenceStep_bnd (ctx0_bnd hb) .sy
    have hm0 : c0.mem = c.mem := Live.TsoRmw.fence_mem c .sy
    have hp0 : c0.prom = [] := by rw [Live.TsoRmw.fence_prom]; exact hp
    rw [← hm0] at hiv
    let kl := (A.rmwKind k).loadKind
    let c1 := readNext A iv c0 kl false l false (c0.mem.lastWrite l) (c0.mem.finalVal l)
    have hx : (c0.mem.lastWrite l, c0.mem.finalVal l, c1) ∈ readSuccs A iv c0 kl false l false := by
      rw [mem_readSuccs]
      refine ⟨_, _, rfl, c0.mem.lastWrite_le l, c0.mem.read?_lastWrite l, c0.mem.writeIn_lastWrite l _, ?_⟩
      rw [hp0]; rfl
    obtain ⟨c2, hw⟩ := Live.SpinStep.readLast_writeSuccs_exists A tid iv hp0 hb0 hiv k l (g (c0.mem.finalVal l))
    have hp1 : c1.prom = [] := hp0
    obtain ⟨hm2, hp2, -⟩ := Live.TicketStep.writeSuccs_nil A tid iv hp1 (.inl hw)
    obtain ⟨hm3, hp3, -, -⟩ := Live.TsoRmw.rmwPost_keeps (A.rmwKind k == .acqRel && !false) c2 l
    let v : Views := { c2.views with vrNew := max c2.views.vrNew (c2.views.getCoh l),
                                     vwNew := max c2.views.vwNew (c2.views.getCoh l) }
    let c3 : Ctx := if (A.rmwKind k == .acqRel && !false) then { c2 with rmwWrote := true, views := v }
      else { c2 with rmwWrote := true }
    refine ⟨fenceStep c3 .sy, ?_, ?_, ?_⟩
    · change Except.ok (f (c0.mem.finalVal l), fenceStep c3 .sy) ∈ runTree A tid iv c _
      simp only [runTree, hA, ↓reduceIte, Bool.false_eq_true, List.mem_flatMap]
      exact ⟨_, hx, by exact ⟨c2, hw, Live.TicketStep.run_done_exists A tid iv _ _⟩⟩
    · rw [Live.TsoRmw.fence_mem, hm3, hm2]
      rfl
    · rw [Live.TsoRmw.fence_prom, hp3, hp2]

/-! ## Continuation forms -/

section Cont

variable {Q : (ExtMachine.ofHooks I A H rv pl pcf).Cfg → Prop} {tr : List Ev}

theorem fwd_done_k {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s s' : I.State}
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some (.done s'))
    (k : ∀ c', Solo c' tid s' → c'.1.mem = c.1.mem → Keeps tid c c' →
      ∃ d, (ExtMachine.ofHooks I A H rv pl pcf).Run μ c' tr d ∧ Q d) :
    ∃ d, (ExtMachine.ofHooks I A H rv pl pcf).Run μ c tr d ∧ Q d := by
  obtain ⟨c', hs, h', hm, hk⟩ := fwd_done h hsys hsite hex
  obtain ⟨d, hr, hq⟩ := k c' h' hm hk
  exact ⟨d, by simpa using run_cons hs hr, hq⟩

theorem fwd_silent_k {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s : I.State}
    {tree : EvTree I.State} {P : I.State → Prop}
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some tree) (hsil : Lower.SilentTree P tree)
    (k : ∀ s' c', P s' → Solo c' tid s' → c'.1.mem = c.1.mem → Keeps tid c c' →
      ∃ d, (ExtMachine.ofHooks I A H rv pl pcf).Run μ c' tr d ∧ Q d) :
    ∃ d, (ExtMachine.ofHooks I A H rv pl pcf).Run μ c tr d ∧ Q d := by
  obtain ⟨s', c', hP, hs, h', hm, hk⟩ := fwd_silent h hsys hsite hex hsil
  obtain ⟨d, hr, hq⟩ := k s' c' hP h' hm hk
  exact ⟨d, by simpa using run_cons hs hr, hq⟩

theorem fwd_load_k {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s : I.State}
    {lk : LoadKind} {l : Loc} {f : Val → I.State}
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some (.load lk false l fun v => .done (f v)))
    (k : ∀ c', Solo c' tid (f (c.1.mem.finalVal l)) → c'.1.mem = c.1.mem → Keeps tid c c' →
      ∃ d, (ExtMachine.ofHooks I A H rv pl pcf).Run μ c' tr d ∧ Q d) :
    ∃ d, (ExtMachine.ofHooks I A H rv pl pcf).Run μ c tr d ∧ Q d := by
  obtain ⟨c', hs, h', hm, hk⟩ := fwd_load h hsys hsite hex
  obtain ⟨d, hr, hq⟩ := k c' h' hm hk
  exact ⟨d, by simpa using run_cons hs hr, hq⟩

theorem fwd_store_k {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s s' : I.State}
    {sk : StoreKind} {l : Loc} {v : Val}
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some (.store sk false l v fun _ => .done s'))
    (k : ∀ c', Solo c' tid s' → c'.1.mem = (c.1.mem.append { loc := l, val := v, tid }).1 → Keeps tid c c' →
      ∃ d, (ExtMachine.ofHooks I A H rv pl pcf).Run μ c' tr d ∧ Q d) :
    ∃ d, (ExtMachine.ofHooks I A H rv pl pcf).Run μ c tr d ∧ Q d := by
  obtain ⟨c', hs, h', hm, hk⟩ := fwd_store h hsys hsite hex
  obtain ⟨d, hr, hq⟩ := k c' h' hm hk
  exact ⟨d, by simpa using run_cons hs hr, hq⟩

theorem fwd_rmw_k {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} {tid : Nat} {s : I.State}
    {rk : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State} (hA : A.rmwFence = true)
    (h : Solo c tid s) (hsys : H.atSys s = false) (hsite : ∀ k a, μ.site k = some a → pcf s ≠ a)
    (hex : I.exec s = some (.rmw rk false l (fun old => some (g old)) fun v => .done (f v)))
    (k : ∀ c', Solo c' tid (f (c.1.mem.finalVal l)) →
      c'.1.mem = (c.1.mem.append { loc := l, val := g (c.1.mem.finalVal l), tid }).1 → Keeps tid c c' →
      ∃ d, (ExtMachine.ofHooks I A H rv pl pcf).Run μ c' tr d ∧ Q d) :
    ∃ d, (ExtMachine.ofHooks I A H rv pl pcf).Run μ c tr d ∧ Q d := by
  obtain ⟨c', hs, h', hm, hk⟩ := fwd_rmw hA h hsys hsite hex
  obtain ⟨d, hr, hq⟩ := k c' h' hm hk
  exact ⟨d, by simpa using run_cons hs hr, hq⟩

/-- The end of a chain: the configuration reached satisfies `Q`. -/
theorem fwd_stop {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg} (h : Q c) :
    ∃ d, (ExtMachine.ofHooks I A H rv pl pcf).Run μ c [] d ∧ Q d :=
  ⟨c, .refl _, h⟩

end Cont

end Spike.Lib.Fwd

/-- info: 'Spike.Lib.Fwd.fwd_treeP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_treeP

/-- info: 'Spike.Lib.Fwd.fwd_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_tree

/-- info: 'Spike.Lib.Fwd.fwd_done' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_done

/-- info: 'Spike.Lib.Fwd.fwd_silent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_silent

/-- info: 'Spike.Lib.Fwd.fwd_load' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_load

/-- info: 'Spike.Lib.Fwd.fwd_store' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_store

/-- info: 'Spike.Lib.Fwd.fwd_rmw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_rmw

/-- info: 'Spike.Lib.Fwd.fwd_done_k' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_done_k

/-- info: 'Spike.Lib.Fwd.fwd_silent_k' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_silent_k

/-- info: 'Spike.Lib.Fwd.fwd_load_k' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_load_k

/-- info: 'Spike.Lib.Fwd.fwd_store_k' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_store_k

/-- info: 'Spike.Lib.Fwd.fwd_rmw_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_rmw_k
