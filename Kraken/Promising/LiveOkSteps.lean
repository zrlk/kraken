/-
**`OkStepsPF` discharged generically** (ISA-neutral,
architecture-neutral, program-independent).

The no-stuck proofs (`LiveNoStuck.lean`) proved `stuckHasDeadPromise` under `OkStepsPF`:
every running promise-free thread has a successful outcome. This file
discharges that hypothesis from fault freedom alone:

- `EvTree.Total`: from every bounded (`Ctx.Bnd`), promise-free context an
  event tree has an outcome (a run or a fault). A promise-free thread can
  always read the last write to a location (`readSuccs_lastWrite`) and
  always "promise now" a write (`writeSuccs_now`): the closure lemmas
  `EvTree.Total.{done, fault, choose, load, store, fence, rmw, access, map}`
  and the value-exposing `EvTree.rmw_run` (needed for `CASP`, whose dead
  branches are `choose 0`, see `LiveOkStepsA64.lean`).
- `ISA.ExecTotal`: every instruction tree of the ISA is `Total`. Instances:
  `LiveOkStepsA64.lean` (`AArch64.isa`, `isaLSE2`), `LiveOkStepsX64.lean`
  (`X64.isa`).
- `stepOne_ne_nil`, **`okStepsPF_of_noFault`**: a bounded configuration with
  no faulting step has `OkStepsPF`; **`okStepsPF_of_faultFreeSem`**: so does
  every configuration `ReachableSem`-reachable from a bounded start under
  `Config.FaultFreeSem` (`Config.Bnd` is kept along every run).
- **`stuckHasDeadPromise_of_faultFreeSem`**, `noStuckFrom_of_faultFreeSem`:
  N1′ and `NoStuckFrom` with fault freedom in place of `OkStepsPF`.

The only facts about the thread needed are `Config.Bnd` (every view at most
`|M|`, true of `Config.init` and kept by every step) and promise freedom; a
thread's `coh` may lag other threads' writes, which is why the witness is
the *last* write (`writeIn_lastWrite` holds for every bound), not the
sequential invariant `Ctx.Seq` of `Conservative.lean`.
-/
import Kraken.Promising.LiveNoStuck
import Kraken.Promising.SLR.ChainK.FaultFree

namespace Kraken.Promising

open Kraken.Promising.Live Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

variable {I : ISA}

/-! ## Total event trees -/

/-- **Total**: from every bounded, promise-free context (with the instruction
views at most `|M|`) the tree has an outcome: a run or a fault. -/
def EvTree.Total {σ : Type} (A : Arch) (tid : Nat) (iv : InstrViews) (tree : EvTree σ) : Prop :=
  ∀ c : Ctx, c.Bnd → c.prom = [] → iv.Le c.mem.last → ∃ r, r ∈ runTree A tid iv c tree

/-- A resolved access is at its own address (`Decls.resolve`). -/
theorem Decls.resolve_ok_addr {ds : Decls} {a : BitVec 64} {n : Nat} {l : Loc} (h : ds.resolve a n = .ok l) :
    l.addr = a := by
  unfold Decls.resolve at h
  split at h
  · next l₀ hf =>
    have ha : l₀.addr = a := by simpa using List.find?_some hf
    split at h
    · cases h; exact ha
    · split at h
      · split at h
        · cases h; exact ha
        · cases h
      · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · cases h; rfl
        · cases h
      · cases h; rfl

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- A promise-free context always reads the last write to `l`. -/
theorem readSuccs_lastWrite {c : Ctx} (hp : c.prom = []) (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool) :
    (c.mem.lastWrite l, c.mem.finalVal l,
      readNext A iv c k xcl l noRet (c.mem.lastWrite l) (c.mem.finalVal l)) ∈ readSuccs A iv c k xcl l noRet :=
  (mem_readSuccs A).mpr ⟨_, _, rfl, c.mem.lastWrite_le l, c.mem.read?_lastWrite l, c.mem.writeIn_lastWrite l _,
    by rw [hp]; rfl⟩

/-- A bounded promise-free context always "promises now" a write of `l := v`,
provided the exclusive pairing timestamp `tr`, if any, is in memory and every
later write to `l` is by `tid`; the result is bounded and promise-free. -/
theorem writeSuccs_now {c : Ctx} (hc : c.Bnd) (hp : c.prom = []) (hiv : iv.Le c.mem.last) (k : StoreKind)
    (xcl : Bool) (l : Loc) (v : Val) (tr : Option Time) {extra : View} (hextra : extra ≤ c.mem.last)
    (htr : ∀ a, tr = some a → a ≤ c.mem.last ∧
      ∀ (t' : Nat) (w : Msg), a < t' → c.mem.get? t' = some w → w.loc = l → w.tid = tid) :
    ∃ c', c' ∈ writeSuccs A tid iv c k xcl l v tr extra ∧ c'.Bnd ∧ c'.prom = [] ∧ c.mem.last ≤ c'.mem.last := by
  have hok : WriteOk A tid iv c k l tr extra (c.mem.last + 1) := by
    refine ⟨?_, fun a ha => ?_⟩
    · unfold writePre
      have := hiv.addrW; have := hiv.dataW; have := hiv.condW
      have := hc.views.le.vwNew; have := hc.views.le.vCAP; have := hc.views.le.coh l
      have := hc.views.le.vrOld; have := hc.views.le.vrOldNR; have := hc.views.le.vwOld
      split
      · omega_t
      · split <;> omega_t
    · obtain ⟨h1, h2⟩ := htr a ha
      exact ⟨by omega_t, c.mem.atomic_of_forall l tid a _ fun t w hat _ hw hl => h2 t w hat hw hl⟩
  have h : _ ∈ writeSuccs A tid iv c k xcl l v tr extra := (mem_writeSuccs A tid).mpr (Or.inr ⟨hok, rfl⟩)
  obtain ⟨hb, hl⟩ := writeSuccs_bnd A tid iv hc hiv hextra h
  refine ⟨_, h, hb, ?_, hl⟩
  exact (TicketStep.writeSuccs_nil A tid iv hp (by cases xcl; exact .inr h; exact .inl h)).2.1

private theorem getLastD_le {xs : List View} {n : Nat} (h : ∀ ν ∈ xs, ν ≤ n) :
    ∀ d, d ≤ n → xs.getLastD d ≤ n := by
  induction xs with
  | nil => intro d hd; exact hd
  | cons a l ih =>
    intro d _
    rw [List.getLastD_cons]
    exact ih (fun ν hν => h ν (List.mem_cons_of_mem _ hν)) a (h a List.mem_cons_self)

variable {A tid iv}

/-- **An RMW from a bounded promise-free context reads the last write and,
if `op` says so, writes**: the context after it is bounded and promise-free,
its memory is the old one or the old one with the write appended, and every
run of the continuation at the value read is a run of the RMW. -/
theorem EvTree.rmw_run {σ : Type} {k : RmwKind} {noRet : Bool} {l : Loc} {op : Val → Option Val}
    {ret : Val → EvTree σ} {c : Ctx} (hc : c.Bnd) (hp : c.prom = []) (hiv : iv.Le c.mem.last) :
    ∃ c', c'.Bnd ∧ c'.prom = [] ∧ iv.Le c'.mem.last ∧
      c'.mem = (match op (c.mem.finalVal l) with
        | none => c.mem
        | some new => (c.mem.append { loc := l, val := new, tid }).1) ∧
      ∀ r, r ∈ runTree A tid iv c' (ret (c.mem.finalVal l)) → r ∈ runTree A tid iv c (.rmw k noRet l op ret) := by
  obtain ⟨hb1, hm1⟩ := fenceOpt_bnd hc A.rmwFence .sy
  have hp1 : (if A.rmwFence then fenceStep c .sy else c).prom = [] := by
    rw [RunnerSim.ite_fence_prom]; exact hp
  rw [← hm1]
  generalize hc1 : (if A.rmwFence then fenceStep c .sy else c) = c1 at hb1 hm1 hp1 ⊢
  have hiv1 : iv.Le c1.mem.last := by rw [hm1]; exact hiv
  generalize hK : (if noRet then LoadKind.plain else (A.rmwKind k).loadKind) = K
  have hx := readSuccs_lastWrite A iv hp1 K false l noRet
  have hb2 := (readSuccs_bnd A iv hb1 hiv1 hx).1
  have hm2 : (readNext A iv c1 K false l noRet (c1.mem.lastWrite l) (c1.mem.finalVal l)).mem = c1.mem := rfl
  have hp2 : (readNext A iv c1 K false l noRet (c1.mem.lastWrite l) (c1.mem.finalVal l)).prom = [] := hp1
  cases hop : op (c1.mem.finalVal l) with
  | none =>
    obtain ⟨hb3, hm3⟩ := fenceOpt_bnd hb2 A.rmwFence .sy
    refine ⟨_, hb3, by rw [RunnerSim.ite_fence_prom]; exact hp2, by rw [hm3, hm2]; exact hiv1,
      by rw [hm3, hm2], fun r hr => ?_⟩
    simp only [runTree, List.mem_flatMap]
    rw [hc1, hK]
    refine ⟨_, hx, ?_⟩
    simp only [hop]
    exact hr
  | some new =>
    have hextra := getLastD_le hb2.loadViews 0 (Nat.zero_le _)
    obtain ⟨c3, hc3, hb3, hp3, -⟩ := writeSuccs_now A tid iv hb2 hp2 (by rw [hm2]; exact hiv1)
      (A.rmwKind k).storeKind true l new (some (c1.mem.lastWrite l)) hextra (fun a ha => by
        cases ha; rw [hm2]
        exact ⟨c1.mem.lastWrite_le l, fun t' w hlt hw hl => absurd hl (c1.mem.not_write_of_lastWrite_lt l hlt hw)⟩)
    have hm3 : c3.mem = (c1.mem.append { loc := l, val := new, tid }).1 := by
      rw [← hm2]; exact (TicketStep.writeSuccs_nil A tid iv hp2 (.inl hc3)).1
    obtain ⟨hb4, hm4⟩ := rmwPost_bnd A hb3 k noRet l
    obtain ⟨hb5, hm5⟩ := fenceOpt_bnd hb4 A.rmwFence .sy
    refine ⟨_, hb5, ?_, ?_, ?_, fun r hr => ?_⟩
    · rw [RunnerSim.ite_fence_prom]
      show (rmwPost A k noRet l c3).prom = []
      unfold rmwPost; split <;> exact hp3
    · rw [hm5, hm4, hm3, Memory.last_append]; exact hiv1.mono (Nat.le_succ _)
    · rw [hm5, hm4, hm3]
    · simp only [runTree, List.mem_flatMap]
      rw [hc1, hK]
      refine ⟨_, hx, ?_⟩
      simp only [hop, List.mem_flatMap]
      exact ⟨c3, hc3, hr⟩

/-- A run of one branch of a choice is a run of the choice. -/
theorem EvTree.exists_run_choose {σ : Type} {n : Nat} {k : Fin n → EvTree σ} {c : Ctx} (i : Fin n)
    (h : ∃ r, r ∈ runTree A tid iv c (k i)) : ∃ r, r ∈ runTree A tid iv c (.choose n k) :=
  h.imp fun _ hr => List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hr⟩

/-- `EvTree.rmw_run` in continuation form: an RMW has a run if its continuation
at the value read has one from every bounded promise-free context with the
memory an RMW leaves. -/
theorem EvTree.exists_run_rmw {σ : Type} {k : RmwKind} {noRet : Bool} {l : Loc} {op : Val → Option Val}
    {ret : Val → EvTree σ} {c : Ctx} (hc : c.Bnd) (hp : c.prom = []) (hiv : iv.Le c.mem.last)
    (h : ∀ c', c'.Bnd → c'.prom = [] → iv.Le c'.mem.last →
      c'.mem = (match op (c.mem.finalVal l) with
        | none => c.mem
        | some new => (c.mem.append { loc := l, val := new, tid }).1) →
      ∃ r, r ∈ runTree A tid iv c' (ret (c.mem.finalVal l))) :
    ∃ r, r ∈ runTree A tid iv c (.rmw k noRet l op ret) := by
  obtain ⟨c', hb', hp', hiv', hm', hrun⟩ :=
    EvTree.rmw_run (k := k) (noRet := noRet) (l := l) (op := op) (ret := ret) hc hp hiv
  exact (h c' hb' hp' hiv' hm').imp fun r hr => hrun r hr

namespace EvTree.Total

variable {σ : Type}

theorem done (s : σ) : (EvTree.done s).Total A tid iv :=
  fun _ _ _ _ => ⟨_, List.mem_singleton.mpr rfl⟩

theorem fault (m : String) : (EvTree.fault m : EvTree σ).Total A tid iv :=
  fun _ _ _ _ => ⟨_, List.mem_singleton.mpr rfl⟩

/-- A non-empty choice (`choose 0` is the dead branch; see `LiveOkStepsA64.lean`). -/
theorem choose {n : Nat} {k : Fin n → EvTree σ} (hn : n ≠ 0) (h : ∀ i, (k i).Total A tid iv) :
    (EvTree.choose n k).Total A tid iv := by
  intro c hc hp hiv
  obtain ⟨r, hr⟩ := h ⟨0, Nat.pos_of_ne_zero hn⟩ c hc hp hiv
  exact ⟨r, List.mem_flatMap.mpr ⟨_, List.mem_finRange _, hr⟩⟩

theorem load {k : LoadKind} {xcl : Bool} {l : Loc} {ret : Val → EvTree σ} (h : ∀ v, (ret v).Total A tid iv) :
    (EvTree.load k xcl l ret).Total A tid iv := by
  intro c hc hp hiv
  have hx := readSuccs_lastWrite A iv hp k xcl l false
  obtain ⟨r, hr⟩ := h _ _ (readSuccs_bnd A iv hc hiv hx).1 hp hiv
  exact ⟨r, List.mem_flatMap.mpr ⟨_, hx, hr⟩⟩

theorem store {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {ret : Bool → EvTree σ}
    (h : ∀ b, (ret b).Total A tid iv) : (EvTree.store k xcl l v ret).Total A tid iv := by
  intro c hc hp hiv
  cases xcl with
  | true =>
    have hb : Ctx.Bnd { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
      ⟨hc.views.xclbNone, hc.loadViews, Nat.zero_le _⟩
    obtain ⟨r, hr⟩ := h false _ hb hp hiv
    exact ⟨r, List.mem_append_right _ (by simpa [runTree] using hr)⟩
  | false =>
    obtain ⟨c', hc', hb', hp', hl⟩ := writeSuccs_now A tid (iv.forStore c.stores) hc hp (hiv.forStore _) k false l v
      none (Nat.zero_le _) (fun _ h => by cases h)
    obtain ⟨r, hr⟩ := h true c' hb' hp' (hiv.mono hl)
    refine ⟨r, List.mem_append_left _ ?_⟩
    simpa [runTree] using List.mem_flatMap.mpr ⟨c', hc', hr⟩

theorem fence {k : FenceKind} {ret : Unit → EvTree σ} (h : (ret ()).Total A tid iv) :
    (EvTree.fence k ret).Total A tid iv := fun c hc hp hiv =>
  h (fenceStep c k) (fenceStep_bnd hc k) (by rw [RunnerSim.fenceStep_prom]; exact hp)
    (by rw [fenceStep_mem]; exact hiv)

theorem rmw {k : RmwKind} {noRet : Bool} {l : Loc} {op : Val → Option Val} {ret : Val → EvTree σ}
    (h : ∀ v, (ret v).Total A tid iv) : (EvTree.rmw k noRet l op ret).Total A tid iv := by
  intro c hc hp hiv
  obtain ⟨c', hb', hp', hiv', -, hrun⟩ := EvTree.rmw_run (k := k) (noRet := noRet) (l := l) (op := op) (ret := ret) hc hp hiv
  obtain ⟨r, hr⟩ := h _ c' hb' hp' hiv'
  exact ⟨r, hrun r hr⟩

/-- An access: the location reached, or a mixed-size fault. -/
theorem access {ds : Decls} {addr : BitVec 64} {n : Nat} {k : Loc → EvTree σ} (h : ∀ l, (k l).Total A tid iv) :
    (EvTree.access ds addr n k).Total A tid iv := by
  unfold EvTree.access
  split
  · exact h _
  · exact fault _

theorem map {τ : Type} (f : σ → τ) {tree : EvTree σ} (h : tree.Total A tid iv) : (tree.map f).Total A tid iv := by
  intro c hc hp hiv
  obtain ⟨r, hr⟩ := h c hc hp hiv
  exact ⟨_, by rw [RunnerSim.runTree_map]; exact List.mem_map.mpr ⟨r, hr, rfl⟩⟩

end EvTree.Total

end Rules

/-! ## Instructions -/

/-- **Every instruction tree of the ISA is total**: from every bounded,
promise-free context it has an outcome (a run or a fault). -/
class ISA.ExecTotal (I : ISA) : Prop where
  total : ∀ (A : Arch) (tid : Nat) (iv : InstrViews) (s : I.State) (tree : EvTree I.State),
    I.exec s = some tree → tree.Total A tid iv

theorem finishInstr_exists (t : Thread I) (d : InstrDeps I.RegId) (iv : InstrViews) (st : I.State) (c : Ctx) :
    ∃ th, th ∈ finishInstr t d iv st c := by
  simp only [finishInstr]
  split
  · exact ⟨_, List.mem_cons_self⟩
  · exact ⟨_, List.mem_singleton.mpr rfl⟩

/-- **A bounded promise-free thread's instruction has an outcome list that is
not empty** (it may be all faults). -/
theorem stepOne_ne_nil [I.ExecTotal] (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} (hb : t.Bnd mem.last)
    (hp : t.prom = []) {outs : List (Except String (Outcome I))} (hs : stepOne A t tid mem = some outs) :
    outs ≠ [] := by
  unfold stepOne at hs
  cases hex : I.exec t.st with
  | none => rw [hex] at hs; cases hs
  | some tree =>
    rw [hex] at hs
    have hs' : _ = outs := Option.some.inj hs
    subst hs'
    have hc : Ctx.Bnd { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } :=
      ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
    obtain ⟨r, hr⟩ := ISA.ExecTotal.total A tid (instrViews t (I.deps t.st)) t.st tree hex _ hc hp
      (instrViews_le hb.regs _)
    cases r with
    | error m => exact List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨_, hr, List.mem_singleton.mpr rfl⟩)
    | ok p =>
      obtain ⟨th, hth⟩ := finishInstr_exists t (I.deps t.st) (instrViews t (I.deps t.st)) p.1 p.2
      exact List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨_, hr, List.mem_map.mpr ⟨th, hth, rfl⟩⟩)

namespace Live.NoStuck

/-- N1′'s conclusion: a thread with an outstanding promise that it cannot
fulfil alone within `fuel`. -/
abbrev DeadPromiseIn (A : Arch) (fuel : Nat) (c : Config I) : Prop :=
  ∃ tid t, c.threads[tid]? = some t ∧ t.prom ≠ [] ∧ ¬ CertOkN A tid t c.mem fuel

/-- **`OkStepsPF` from fault freedom**: in a bounded configuration with no
faulting step, every running promise-free thread has a successful outcome. -/
theorem okStepsPF_of_noFault [I.ExecTotal] {A : Arch} {c : Config I} (hb : c.Bnd)
    (hnf : ∀ tid m, ¬ c.FaultStep A tid m) : OkStepsPF A c := by
  intro tid t ht hh hp
  cases hs : stepOne A t tid c.mem with
  | none => rw [halted_of_stepOne_none hs] at hh; cases hh
  | some outs =>
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil outs (stepOne_ne_nil A (hb tid t ht) hp hs)
    cases r with
    | error m => exact absurd ⟨outs, by show (c.threads[tid]?.bind fun t => stepOne A t tid c.mem) = some outs; rw [ht]; exact hs, hr⟩ (hnf tid m)
    | ok o => exact ⟨outs, o, rfl, hr⟩

/-- **`OkStepsPF` along every semantic run** from a bounded start under
`Config.FaultFreeSem`. -/
theorem okStepsPF_of_faultFreeSem [I.ExecTotal] {A : Arch} {fuel : Nat} {init c : Config I} (hb : init.Bnd)
    (hff : Config.FaultFreeSem A fuel init) (hr : ReachableSem A fuel init c) : OkStepsPF A c :=
  okStepsPF_of_noFault (Config.Bnd.reachable hb (ReachableK.of_reachableSem' hb hr)) (hff c hr)

/-- **N1′ from fault freedom**: a stuck configuration reachable on the
semantic machine from a bounded fault-free start has a thread with an
outstanding promise that it cannot fulfil alone within `fuel`. -/
theorem stuckHasDeadPromise_of_faultFreeSem [I.ExecTotal] {A : Arch} {fuel : Nat} {init c : Config I}
    (hb : init.Bnd) (hff : Config.FaultFreeSem A fuel init) (hr : ReachableSem A fuel init c)
    (hst : StuckSem A fuel c) :
    ∃ tid t, c.threads[tid]? = some t ∧ t.prom ≠ [] ∧ ¬ CertOkN A tid t c.mem fuel :=
  stuckHasDeadPromise A I fuel c hst (okStepsPF_of_faultFreeSem hb hff hr)

/-- `stuckHasDeadPromise_of_faultFreeSem` from `Config.init`. -/
theorem stuckHasDeadPromise_init [I.ExecTotal] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} (hff : Config.FaultFreeSem A fuel (Config.init states initMem)) {c : Config I}
    (hr : ReachableSem A fuel (Config.init states initMem) c) (hst : StuckSem A fuel c) :
    ∃ tid t, c.threads[tid]? = some t ∧ t.prom ≠ [] ∧ ¬ CertOkN A tid t c.mem fuel :=
  stuckHasDeadPromise_of_faultFreeSem (Config.init_bnd _ _) hff hr hst

/-- **No stuck configuration from fault freedom and consistency.** -/
theorem noStuckFrom_of_faultFreeSem [I.ExecTotal] {A : Arch} {fuel : Nat} {init : Config I} (hb : init.Bnd)
    (hff : Config.FaultFreeSem A fuel init) (hcons : ∀ c, ReachableSem A fuel init c → ConsistentSem A fuel c) :
    NoStuckFrom A fuel init :=
  noStuckFrom_of_consistent hcons fun _ hr => okStepsPF_of_faultFreeSem hb hff hr

end Live.NoStuck

end Kraken.Promising
