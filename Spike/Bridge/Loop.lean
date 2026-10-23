/-
The bridge spike, spinning-reader variant: the reader loops on an acquire
load of the flag until it reads a non-zero value, then halts. On the target
the loop is a load followed by register-only instructions (a test and a
branch); on the source it is the code block `spin`
(`Spike/Bridge/LoopSrc.lean`).

**The stutter form of the simulation step** (`reach_stutter`): every Kraken
step from a related pair is matched by a source run with the empty trace,
of zero or more steps, to a related pair. In the variant:

* the load at the loop head is one source load (`head_read`);
* a register-only instruction that does not leave the test (x64's `test`)
  is zero source steps;
* the branch back to the head is two source steps, the test and the tail
  call (`mid_test`, `tail_enter`);
* the branch to the exit is one source step, the test;
* the writer's steps are as in the straight-line program (`writer_sim`,
  `writer_prom`, certified by lockstep).

**What the loop adds to the relation** (`RelL`, `RPhaseL`): the reader's
second and later loads are made with non-initial views, on both sides. The
source may read a message only if its read bound does not hide it, so the
relation bounds the source reader's read-bound views by the Kraken
reader's coherence view of the flag (`VBound`): `coh flagA`, `vPreBase` and
`vRd` (read on TSO) are at most `getCoh ⟨F, 8⟩`. A Kraken read at `ts` has
no flag write in `(ts, getCoh]`, hence the source has none in `(ts, bound]`
(`hidden_false`). After the read both sides' views rise to at most `ts` on
the source (message views are `0`, `MV0`; the reader has no own writes,
`vs.mine = []`; no pair accesses, `pairs = []`) and to at least `ts` on
Kraken (the reader has no forwarding entry, `fwdb = []`). This is the
"source views below target views" relation that a longer program needs in
general, here for one location and one thread.

The reader never promises (`loop_cert`: its steps keep its promise set, so
it certifies only with none).
-/
import Spike.Bridge.LoopSrc
import Spike.Bridge.Sim

namespace Spike.Bridge

open Kraken.Promising Kraken.Promising.Lower Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep
open Scc.Sem (SrcSem ExtMachine Target obs)

/-! ## The stutter form of the simulation step -/

section Stutter

variable {I : ISA} (A : Arch) {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch}
  {init : TermRun.Cfg → Prop}

/-- One source step is a run with the empty trace. -/
theorem run_one {tid : Nat} {s s' : TermRun.Cfg} (h : SrcSem.StepBy p k arch tid s s') :
    (SrcSem.ofStep p k arch init).Run s [] s' :=
  Scc.Sem.LRun.step (es := []) (tr := []) ⟨tid, .inl h, rfl⟩ (.refl _)

/-- Two runs with the empty trace compose. -/
theorem run_trans {s s1 s' : TermRun.Cfg} (h1 : (SrcSem.ofStep p k arch init).Run s [] s1)
    (h2 : (SrcSem.ofStep p k arch init).Run s1 [] s') : (SrcSem.ofStep p k arch init).Run s [] s' :=
  Scc.Sem.LRun.trans (tr := []) (tr' := []) h1 h2

/-- **Reachability, stutter form.** If every Kraken step from an `R`-related
pair is matched by a source run with the empty trace (zero, one or more
source steps) to an `R`-related pair, so is every Kraken run. -/
theorem reach_stutter (R : Config I → TermRun.Cfg → Prop)
    (hstep : ∀ tid c c' s, R c s → StepSemInf A tid c c' →
      ∃ s', (SrcSem.ofStep p k arch init).Run s [] s' ∧ R c' s')
    {c c' : Config I} (h : ReachableSemInf A c c') :
    ∀ s, R c s → ∃ s', (SrcSem.ofStep p k arch init).Run s [] s' ∧ R c' s' := by
  induction h with
  | refl => intro s hs; exact ⟨s, .refl s, hs⟩
  | step tid hst _ ih =>
    intro s hs
    obtain ⟨s1, h1, hr1⟩ := hstep tid _ _ s hs hst
    obtain ⟨s', h2, hr'⟩ := ih s1 hr1
    exact ⟨s', run_trans h1 h2, hr'⟩

/-- **The `Sim.sim` clause in stutter form, with trace equality**, for the
existing machine as a target, loading `asmOf st0 st1 F`, from a source
start configuration `s0` related to the loaded one. -/
theorem sim_clause_stutter (R : Config I → TermRun.Cfg → Prop)
    (hstep : ∀ tid c c' s, R c s → StepSemInf A tid c c' →
      ∃ s', (SrcSem.ofStep p k arch init).Run s [] s' ∧ R c' s')
    {st0 st1 : I.State} {F : BitVec 64} {s0 : TermRun.Cfg} (hinit : init = (· = s0))
    (h0 : R (Config.init [st0, st1] [(⟨F, 8⟩, 0)]) s0)
    (rv : I.State → I.RegId → BitVec 64) (pl : I.State → BitVec 64 → Option (BitVec 64)) (Λ : Scc.Sem.Layout) (μ : Scc.Sem.Marks) :
    ∀ t0 tr t, (Target.ofBase I A rv pl).load (asmOf st0 st1 F) Λ = some t0 →
      (Target.ofBase I A rv pl).M.Run μ t0 tr t →
      ∃ tr' s, (SrcSem.ofStep p k arch init).Reach tr' s ∧ R t.1 s ∧ obs tr = tr' := by
  subst hinit
  intro t0 tr t ht0 hr
  cases ht0
  obtain ⟨rfl, hreach⟩ := ExtMachine.ofBase_run_inv hr
  obtain ⟨s, hrun, hs⟩ := reach_stutter A R hstep hreach s0 h0
  exact ⟨[], s, ⟨s0, rfl, hrun⟩, hs, rfl⟩

end Stutter

/-! ## The spinning reader's event trees -/

/-- **The spinning reader's event trees.** At a loop head (`Head`) one
non-exclusive load of `⟨F, 8⟩`, after which the thread is at the test with
the value read (`Mid v`); at the test, register-only instructions (event
tree `.done`) that stay at the test, return to a loop head (only if the
value read is `0` in its low 64 bits, the width of a register) or reach the
exit (only if it is not); at the exit
(`Exit v`) no next instruction. -/
structure LoopShape (I : ISA) (F : BitVec 64) (Head : I.State → Prop) (Mid Exit : Val → I.State → Prop) :
    Prop where
  hd : ∀ h, Head h → ∃ kl, ∃ g : Val → I.State, I.exec h = some (.load kl false ⟨F, 8⟩ fun v => .done (g v)) ∧ ∀ v, Mid v (g v)
  md : ∀ v s, Mid v s → ∃ s', I.exec s = some (.done s') ∧
    (Mid v s' ∨ (v.setWidth 64 = 0 ∧ Head s') ∨ (v.setWidth 64 ≠ 0 ∧ Exit v s'))
  ex : ∀ v s, Exit v s → I.exec s = none

/-- The reader's phases. -/
def LPhase {I : ISA} (Head : I.State → Prop) (Mid Exit : Val → I.State → Prop) (s : I.State) : Prop :=
  Head s ∨ (∃ v, Mid v s) ∨ (∃ v, Exit v s)

/-! ## The reader's steps on the Kraken side -/

section KSteps

variable {I : ISA} (A : Arch) {F : BitVec 64} {Head : I.State → Prop} {Mid Exit : Val → I.State → Prop}
  (hL : LoopShape I F Head Mid Exit)
include hL

omit hL in
/-- The coherence view of the flag after a read at `ts` without a
forwarding entry: at least the old one and `ts`. -/
theorem getCoh_readNext {iv : InstrViews} {c : Ctx} {kl : Kraken.LoadKind} {l : Loc} {ts : Nat} {v : Val}
    (hf : c.views.getFwd l = none) :
    max (c.views.getCoh l) ts ≤ (readNext A iv c kl false l false ts v).views.getCoh l := by
  show max (c.views.getCoh l) ts ≤ (c.views.setCoh l _).getCoh l
  rw [Views.getCoh_setCoh]
  simp only [↓reduceIte, readView, hf]
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)⟩

/-- **The reader's load** (Kraken side): memory, promises and forwarding
bank unchanged; the thread at the test with the value `v` read at some
timestamp `ts` that no flag write hides below the thread's coherence view;
without a forwarding entry, the coherence view rises to at least `ts`. -/
theorem loop_head_out {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory} (hh : Head t.st)
    (h : ThreadStep A tid (t, mem) q) :
    q.2 = mem ∧ q.1.prom = t.prom ∧ q.1.views.fwdb = t.views.fwdb ∧
      ∃ ts v, Mid v q.1.st ∧ mem.read? ⟨F, 8⟩ ts = some v ∧
        mem.writeIn ⟨F, 8⟩ ts (t.views.getCoh ⟨F, 8⟩) = false ∧
        (t.views.fwdb = [] → max (t.views.getCoh ⟨F, 8⟩) ts ≤ q.1.views.getCoh ⟨F, 8⟩) := by
  obtain ⟨kl, g, hex, hmid⟩ := hL.hd _ hh
  obtain ⟨outs, o, hs, ho, rfl⟩ := h
  obtain ⟨st, c', hrun, hth, hm⟩ := (stepOne_ok_iff A tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩
  rw [run_load_iff] at hrun
  obtain ⟨ts, v, hx, rfl⟩ := hrun
  have hp := readSuccs_prom A _ hx
  obtain ⟨ts', v', he, -, hv, hwi, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hk := (finishInstr_relKey hth).2
  have hcoh : o.thread.views.coh = (readNext A (instrViews t (I.deps t.st)) (ctx0 tid t mem) kl false ⟨F, 8⟩ false ts
      v).views.coh := by have := congrArg Views.coh hk; exact this
  have hfw : o.thread.views.fwdb = t.views.fwdb := by have := congrArg Views.fwdb hk; exact this
  refine ⟨hm, (finishInstr_relKey hth).1.trans hp, hfw, ts, v, ?_, hv, ?_, fun hf => ?_⟩
  · rw [finishInstr_st hth]; exact hmid v
  · unfold Memory.writeIn at hwi ⊢
    rw [List.any_eq_false] at hwi ⊢
    intro i hi
    exact hwi i (List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi)
      (Nat.sub_le_sub_right (Nat.le_max_right _ _) _)))
  · have hgf : (ctx0 tid t mem).views.getFwd ⟨F, 8⟩ = none := by
      show (t.views.fwdb.find? _).map _ = none
      rw [hf]; rfl
    have := getCoh_readNext A (iv := instrViews t (I.deps t.st)) (kl := kl) (v := v) (ts := ts) hgf
    have hg : o.thread.views.getCoh ⟨F, 8⟩ = (readNext A (instrViews t (I.deps t.st)) (ctx0 tid t mem) kl false
        ⟨F, 8⟩ false ts v).views.getCoh ⟨F, 8⟩ := by
      unfold Views.getCoh; rw [hcoh]
    rw [hg]
    exact this

/-- **A register-only instruction at the test** (Kraken side): memory,
promises, forwarding bank and coherence views unchanged; the thread stays
at the test, returns to a loop head (value `0`), or reaches the exit. -/
theorem loop_mid_out {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory} {v : Val}
    (hm : Mid v t.st) (h : ThreadStep A tid (t, mem) q) :
    q.2 = mem ∧ q.1.prom = t.prom ∧ q.1.views.fwdb = t.views.fwdb ∧
      q.1.views.getCoh ⟨F, 8⟩ = t.views.getCoh ⟨F, 8⟩ ∧
      (Mid v q.1.st ∨ (v.setWidth 64 = 0 ∧ Head q.1.st) ∨ (v.setWidth 64 ≠ 0 ∧ Exit v q.1.st)) := by
  obtain ⟨s', hex, hnext⟩ := hL.md v _ hm
  obtain ⟨outs, o, hs, ho, rfl⟩ := h
  obtain ⟨st, c', hrun, hth, hmem⟩ := (stepOne_ok_iff A tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := (run_done_iff A tid _).mp hrun
  have hk := (finishInstr_relKey hth).2
  have hcoh : o.thread.views.coh = t.views.coh := by have := congrArg Views.coh hk; exact this
  have hfw : o.thread.views.fwdb = t.views.fwdb := by have := congrArg Views.fwdb hk; exact this
  refine ⟨hmem, (finishInstr_relKey hth).1, hfw, by unfold Views.getCoh; rw [hcoh], ?_⟩
  rw [finishInstr_st hth]
  exact hnext

/-- **Every promise-free solo step of the reader keeps its promise set and
its phase.** -/
theorem loop_step_prom {tid : Nat} {q r : Thread I × Memory} (hph : LPhase Head Mid Exit q.1.st)
    (h : ThreadStep A tid q r) : r.1.prom = q.1.prom ∧ LPhase Head Mid Exit r.1.st := by
  obtain ⟨t, mem⟩ := q
  rcases hph with hh | ⟨v, hm⟩ | ⟨v, he⟩
  · obtain ⟨-, hp, -, ts, v, hm', -⟩ := loop_head_out A hL hh h
    exact ⟨hp, .inr (.inl ⟨v, hm'⟩)⟩
  · obtain ⟨-, hp, -, -, hn⟩ := loop_mid_out A hL hm h
    refine ⟨hp, ?_⟩
    rcases hn with hn | ⟨-, hn⟩ | ⟨-, hn⟩
    · exact .inr (.inl ⟨v, hn⟩)
    · exact .inl hn
    · exact .inr (.inr ⟨v, hn⟩)
  · exact absurd h (no_threadStep A (hL.ex v _ he))

/-- **The reader certifies only with no promise.** -/
theorem loop_cert {tid : Nat} {t : Thread I} {mem : Memory} (hph : LPhase Head Mid Exit t.st)
    (hc : CertOk A tid t mem) : t.prom = [] := by
  obtain ⟨t', mem', hrun, hp⟩ := hc
  suffices H : ∀ q r, ThreadNP A tid q r → LPhase Head Mid Exit q.1.st → r.1.prom = q.1.prom by
    exact (H _ _ hrun hph).symm.trans hp
  intro q r hr
  induction hr with
  | refl => intro _; rfl
  | step hs _ ih =>
    intro hph
    obtain ⟨hp1, hph1⟩ := loop_step_prom A hL hph hs
    exact (ih hph1).trans hp1

end KSteps

/-! ## The relation -/

section Rel

variable {I : ISA} {F : BitVec 64} {v1 : Val}

/-- Every source message has message view `0`. -/
def MV0 (sm : WeakMem.Memory) : Prop := ∀ (i : Nat) (m : WeakMem.Msg), sm[i]? = some m → m.view = 0

theorem MV0.push {sm : WeakMem.Memory} (h : MV0 sm) : MV0 (sm.push ⟨flagA, .num 1, 0⟩) := by
  intro i m hm
  rw [Array.getElem?_push] at hm
  split at hm
  · cases hm; rfl
  · exact h i m hm

/-- **The source reader's read-bound views are below the Kraken reader's
coherence view of the flag**, and the source reader has no own writes. -/
structure VBound (vs : WeakMem.VState) (K : Nat) : Prop where
  coh : vs.coh flagA ≤ K
  pre : vs.vPreBase ≤ K
  rd : vs.vRd ≤ K
  mine : vs.mine = []

/-- **The spinning reader's phase**: no promise, no forwarding entry, the
source views bounded (`VBound`); at a loop head (source `readerHead`), at
the test (source `readerMid`, `r` bound to the value read, `0` or `v1`), or
at the exit (source `readerExit`, the value `v1`). -/
def RPhaseL (F : BitVec 64) (v1 : Val) (Head : I.State → Prop) (Mid Exit : Val → I.State → Prop) (t : Thread I)
    (th : TermRun.TTh) : Prop :=
  t.prom = [] ∧ t.views.fwdb = [] ∧ VBound th.vs (t.views.getCoh ⟨F, 8⟩) ∧
    ((Head t.st ∧ ∃ vs u, th = readerHead vs u) ∨
     (∃ v w vs u, Mid v t.st ∧ th = readerMid vs w u ∧ w.val = .num v.toNat ∧ (v = 0 ∨ v = v1)) ∨
     (∃ v w vs u, Exit v t.st ∧ th = readerExit vs w u ∧ w.val = .num v.toNat ∧ v = v1))

theorem RPhaseL.lphase {Head : I.State → Prop} {Mid Exit : Val → I.State → Prop} {t : Thread I}
    {th : TermRun.TTh} (h : RPhaseL F v1 Head Mid Exit t th) : LPhase Head Mid Exit t.st := by
  obtain ⟨-, -, -, ⟨hh, -⟩ | ⟨v, -, -, -, hm, -⟩ | ⟨v, -, -, -, he, -⟩⟩ := h
  · exact .inl hh
  · exact .inr (.inl ⟨v, hm⟩)
  · exact .inr (.inr ⟨v, he⟩)

/-- **The relation of the variant**: as `Rel`, with the spinning reader's
phase, and the source facts the reader's later loads need (no pair
accesses, message views `0`). -/
def RelL (F : BitVec 64) (v1 : Val) (st0 sW : I.State) (Head : I.State → Prop) (Mid Exit : Val → I.State → Prop)
    (c : Config I) (s : TermRun.Cfg) : Prop :=
  ∃ t0 t1 th0 th1, c.threads = #[t0, t1] ∧ s.ths = #[th0, th1] ∧ WPhase st0 sW t0 th0 ∧ PromOK t0 c.mem ∧
    RPhaseL F v1 Head Mid Exit t1 th1 ∧ MemRel F (· = v1) c.mem s.mem ∧ s.pairs = [] ∧ MV0 s.mem

/-- **No hidden message on the source side**: if no flag write of Kraken
memory lies in `(ts, K]`, no flag message of the related source memory lies
in `(ts, b]` for `b ≤ K`. -/
theorem hidden_false {km : Memory} {sm : WeakMem.Memory} {V : Val → Prop} (hM : MemRel F V km sm) {ts b K : Nat}
    (hw : km.writeIn ⟨F, 8⟩ ts K = false) (hb : b ≤ K) : WeakMem.hiddenFrom sm flagA ts b = false := by
  unfold WeakMem.hiddenFrom
  rw [List.any_eq_false]
  intro (t' : Nat) ht'
  have ht'b : t' ≤ b := Nat.lt_succ_iff.mp (List.mem_range.mp ht')
  cases hm : sm[t']? with
  | none => simp
  | some m =>
    simp only [Option.elim, Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro (hlt : ts < t') _
    have hsz : t' < sm.size := (Array.getElem?_eq_some_iff.mp hm).1
    have hj : t' - 1 < km.msgs.size := by have := hM.size; omega
    have : km.writeIn ⟨F, 8⟩ ts K = true := by
      unfold Memory.writeIn
      rw [List.any_eq_true]
      refine ⟨t' - ts - 1, List.mem_range.mpr (by omega), ?_⟩
      have he : ts + (t' - ts - 1) + 1 = t' := by omega
      rw [he]
      have h0 : t' ≠ 0 := by omega
      simp [Memory.get?, h0, Array.getElem?_eq_getElem hj, (hM.msg _ hj).1]
    rw [hw] at this
    cases this

end Rel

/-! ## The simulation step, stutter form -/

section Sim

variable {I : ISA} (A : Arch) {F : BitVec 64} {v1 : Val} {st0 sW : I.State} {Head : I.State → Prop}
  {Mid Exit : Val → I.State → Prop} {k : Promises.Knobs} {arch : WeakMem.Arch} {init : TermRun.Cfg → Prop}

/-- A source thread with no promise is certified (the empty `Solo` run). -/
theorem certified_nil {p : CoreTerm.Prog} {s : TermRun.Cfg} {i : Nat} {th : TermRun.TTh} (h : s.ths[i]? = some th)
    (hp : th.promises = []) : TermRun.Certified p k arch s i :=
  ⟨s, .refl s, by simp [TermRun.noPromises, h, hp]⟩

/-- **The source views after a load stay below the Kraken coherence view**:
a load of `ts` with message view `0`, no pair accesses and no own writes
raises `coh flagA`, `vRd` and `vPreBase` to at most `ts`. -/
theorem VBound.load {vs : WeakMem.VState} {K K' ts : Nat} (h : VBound vs K) (hK : max K ts ≤ K') :
    VBound (loadVS vs [] ts 0) K' := by
  have hKK : K ≤ K' := Nat.le_trans (Nat.le_max_left _ _) hK
  have hts : ts ≤ K' := Nat.le_trans (Nat.le_max_right _ _) hK
  refine ⟨?_, ?_, ?_, h.mine⟩
  · simp only [loadVS, ↓reduceIte]
    exact Nat.max_le.mpr ⟨Nat.le_trans h.coh hKK, hts⟩
  · simp only [loadVS, Promises.acqV, WeakMem.ownFwd, WeakMem.extTs, h.mine, List.contains_nil,
      Bool.false_eq_true, ↓reduceIte, Option.getD_none]
    exact Nat.max_le.mpr ⟨Nat.le_trans h.pre hKK, Nat.max_le.mpr ⟨Nat.zero_le _, hts⟩⟩
  · simp only [loadVS, Promises.rdV, WeakMem.ownFwd, h.mine, List.contains_nil, Bool.false_eq_true, ↓reduceIte,
      Option.getD_none, Promises.pairTop]
    exact Nat.max_le.mpr ⟨Nat.le_trans h.rd hKK, Nat.max_le.mpr ⟨hts, Nat.zero_le _⟩⟩

/-- The source read bound of a bounded reader is below the bound. -/
theorem VBound.readBound {vs : WeakMem.VState} {K : Nat} (h : VBound vs K) :
    Promises.readBoundOf arch vs 0 flagA ≤ K := by
  unfold Promises.readBoundOf
  refine Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨h.pre, Nat.zero_le _⟩, h.coh⟩, ?_⟩
  split
  · exact h.rd
  · exact Nat.zero_le _

variable (hWS : WShape I F v1 st0 sW) (hL : LoopShape I F Head Mid Exit)
include hWS hL

/-- **The simulation step of the variant, stutter form.** Every fuel-free
step of Kraken thread `tid` from a related pair is matched by a source run
with the empty trace to a related pair: the writer's steps by one source
step each (certified by lockstep); the reader's load by one source load;
its register-only instructions by none (staying at the test), the test and
the tail call (back to the head), or the test (to the exit). The reader
never promises (`loop_cert`). -/
theorem sim_step_loop {c c' : Config I} {s : TermRun.Cfg} {tid : Nat} (hR : RelL F v1 st0 sW Head Mid Exit c s)
    (h : StepSemInf A tid c c') :
    ∃ s', (SrcSem.ofStep progL k arch init).Run s [] s' ∧ RelL F v1 st0 sW Head Mid Exit c' s' := by
  obtain ⟨t0, t1, th0, th1, hc, hs, hW, hP, hRd, hM, hpairs, hmv⟩ := hR
  have h0 : s.ths[0]? = some th0 := by rw [hs]; rfl
  have h1 : s.ths[1]? = some th1 := by rw [hs]; rfl
  rcases h with ⟨t, outs, o, ht, hst, ho, hcert, rfl⟩ | ⟨t, w, ht, hw, hcert, rfl⟩
  · rw [hc] at ht
    have hts : ThreadStep A tid (t, c.mem) (o.thread, o.mem) := ⟨outs, o, hst, ho, rfl⟩
    match tid, ht, hts, hcert with
    | 0, ht, hts, hcert =>
      change some t0 = some t at ht
      cases ht
      obtain ⟨sm, th', hstep, hW', hP', hM', hsm⟩ :=
        writer_sim A hWS (pr := progL) (k := k) (arch := arch) h0 hW hP hM hts
      refine ⟨_, run_one (.inl ⟨hstep, certW A hWS ⟨th', getElem?_set!_self h0 th', hW', hP', hM'⟩ hcert⟩), ?_⟩
      refine ⟨o.thread, t1, th', th1, ?_, ?_, hW', hP', hRd, hM', hpairs, ?_⟩
      · show c.threads.set! 0 o.thread = _
        rw [hc]; rfl
      · show s.ths.set! 0 th' = _
        rw [hs]; rfl
      · show MV0 sm
        rcases hsm with rfl | rfl
        · exact hmv
        · exact hmv.push
    | 1, ht, hts, hcert =>
      change some t1 = some t at ht
      cases ht
      obtain ⟨hp1, hfw1, hvb, hph⟩ := hRd
      have hthr : ∀ t' : Thread I, c.threads.set! 1 t' = #[t0, t'] := by intro t'; rw [hc]; rfl
      have hths : ∀ th' : TermRun.TTh, s.ths.set! 1 th' = #[th0, th'] := by intro th'; rw [hs]; rfl
      rcases hph with ⟨hh, vs, u, rfl⟩ | ⟨v, w, vs, u, hm, rfl, hwv, hv⟩ | ⟨v, w, vs, u, hex, rfl, -, -⟩
      · -- the load: one source load
        obtain ⟨hmem, hpr, hfw, ts, v, hmid, hrd, hwi, hcoh⟩ := loop_head_out A hL hh hts
        obtain ⟨m, hsm, hl, hval⟩ := hM.read hrd
        obtain ⟨u', hstep⟩ := head_read (k := k) (arch := arch) s h1 hsm hl (hidden_false hM hwi hvb.readBound)
        have hmv0 : m.view = 0 := hmv _ _ hsm
        have hm' : o.mem = c.mem := hmem
        refine ⟨_, run_one (.inl ⟨hstep, certified_nil (getElem?_set!_self h1 _) rfl⟩), ?_⟩
        refine ⟨t0, o.thread, th0, _, hthr _, hths _, hW, ?_,
          ⟨hpr.trans hp1, hfw.trans hfw1, ?_, .inr (.inl ⟨v, _, _, u', hmid, rfl, hval, hM.read_val hrd⟩)⟩,
          ?_, hpairs, hmv⟩
        · show PromOK t0 o.mem
          rw [hm']; exact hP
        · show VBound (loadVS vs s.pairs ts m.view) _
          rw [hpairs, hmv0]
          exact hvb.load (hcoh hfw1)
        · show MemRel F (· = v1) o.mem s.mem
          rw [hm']; exact hM
      · -- a register-only instruction at the test
        obtain ⟨hmem, hpr, hfw, hcoh, hn⟩ := loop_mid_out A hL hm hts
        have hm' : o.mem = c.mem := hmem
        have hP' : PromOK t0 o.mem := by rw [hm']; exact hP
        have hM' : MemRel F (· = v1) o.mem s.mem := by rw [hm']; exact hM
        have hvb' : VBound vs (o.thread.views.getCoh ⟨F, 8⟩) := by rw [hcoh]; exact hvb
        have hv1z : v1.setWidth 64 ≠ 0 := by
          intro h0
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_setWidth, hWS.one] at this
          simp at this
        rcases hn with hn | ⟨hz, hn⟩ | ⟨hne, hn⟩
        · -- staying at the test: no source step
          refine ⟨s, .refl s, t0, o.thread, th0, _, hthr _, hs, hW, hP',
            ⟨hpr.trans hp1, hfw.trans hfw1, hvb', .inr (.inl ⟨v, w, vs, u, hn, rfl, hwv, hv⟩)⟩, hM', hpairs, hmv⟩
        · -- back to the head: the test, then the tail call
          obtain rfl : v = 0 := hv.resolve_right (by rintro rfl; exact hv1z hz)
          have h0v : (0 : Val).toNat = 0 := by simp
          have hstep1 := mid_test (k := k) (arch := arch) s h1 hwv
          simp only [h0v, ↓reduceIte] at hstep1
          have h1' := getElem?_set!_self h1 (readerTail vs w u)
          have hstep2 := tail_enter (k := k) (arch := arch) { s with ths := s.ths.set! 1 (readerTail vs w u) } h1'
          refine ⟨_, run_trans (run_one (.inl ⟨hstep1, certified_nil h1' rfl⟩))
            (run_one (.inl ⟨hstep2, certified_nil (getElem?_set!_self h1' _) rfl⟩)), ?_⟩
          refine ⟨t0, o.thread, th0, readerHead vs u, hthr _, ?_, hW, hP',
            ⟨hpr.trans hp1, hfw.trans hfw1, hvb', .inl ⟨hn, vs, u, rfl⟩⟩, hM', hpairs, hmv⟩
          show (s.ths.set! 1 (readerTail vs w u)).set! 1 (readerHead vs u) = _
          rw [hs]; rfl
        · -- to the exit: the test
          have hv1 : v = v1 := hv.resolve_left (by rintro rfl; exact hne rfl)
          have hn0 : ¬ v.toNat = 0 := by rw [hv1, hWS.one]; decide
          have hstep1 := mid_test (k := k) (arch := arch) s h1 hwv
          simp only [hn0, ↓reduceIte] at hstep1
          refine ⟨_, run_one (.inl ⟨hstep1, certified_nil (getElem?_set!_self h1 _) rfl⟩), ?_⟩
          refine ⟨t0, o.thread, th0, readerExit vs w u, hthr _, hths _, hW, hP',
            ⟨hpr.trans hp1, hfw.trans hfw1, hvb', .inr (.inr ⟨v, w, vs, u, hn, rfl, hwv, hv1⟩)⟩, hM', hpairs, hmv⟩
      · exact absurd hts (no_threadStep A (hL.ex v _ hex))
    | n + 2, ht, _, _ => simp at ht
  · rw [hc] at ht
    match tid, ht, hw, hcert with
    | 0, ht, hw, hcert =>
      change some t0 = some t at ht
      cases ht
      obtain ⟨-, th0', hb, hpe, hW', hP', hM'⟩ := writer_prom A hWS (pr := progL) (k := k) (arch := arch) h0 hW hM hcert
      refine ⟨_, run_one hb, ?_⟩
      rw [hpe]
      refine ⟨promThread t0 c.mem w, t1, th0', th1, ?_, ?_, hW', hP', hRd, hM', hpairs, hmv.push⟩
      · show c.threads.set! 0 _ = _
        rw [hc]; rfl
      · show s.ths.set! 0 _ = _
        rw [hs]; rfl
    | 1, ht, hw, hcert =>
      change some t1 = some t at ht
      cases ht
      have := loop_cert A hL (t := promThread t1 c.mem w) hRd.lphase hcert
      simp at this
    | n + 2, ht, _, _ => simp at ht

omit hWS hL in
/-- The start configurations are related: Kraken's `Config.init` of the two
start states (the reader's at a loop head) and the flag's initial write, and
`srcInitL`. -/
theorem rel_initL {st1 : I.State} (hh : Head st1) :
    RelL F v1 st0 sW Head Mid Exit (Config.init [st0, st1] [(⟨F, 8⟩, 0)]) srcInitL := by
  refine ⟨Thread.init st0, Thread.init st1, writerAt [], readerL0, rfl, rfl, .inl ⟨rfl, rfl⟩,
    fun _ h => by simp [Thread.init] at h, ⟨rfl, rfl, ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩,
      .inl ⟨hh, _, _, readerL0_eq⟩⟩, MemRel.start, rfl, ?_⟩
  intro i m hm
  match i, hm with
  | 0, hm => cases hm; rfl
  | n + 1, hm => simp [srcInitL] at hm

/-- **The `Sim.sim` clause of the variant, with trace equality**: every
reachable target configuration is related to a reachable source
configuration of the spinning program from `srcInitL`. -/
theorem sim_clause_loop {st1 : I.State} (hh : Head st1) (rv : I.State → I.RegId → BitVec 64)
    (pl : I.State → BitVec 64 → Option (BitVec 64)) (Λ : Scc.Sem.Layout) (μ : Scc.Sem.Marks) :
    ∀ t0 tr t, (Target.ofBase I A rv pl).load (asmOf st0 st1 F) Λ = some t0 →
      (Target.ofBase I A rv pl).M.Run μ t0 tr t →
      ∃ tr' s, (SrcSem.ofStep progL k arch (· = srcInitL)).Reach tr' s ∧ RelL F v1 st0 sW Head Mid Exit t.1 s ∧
        obs tr = tr' :=
  sim_clause_stutter A (RelL F v1 st0 sW Head Mid Exit) (fun _ _ _ _ hR h => sim_step_loop A hWS hL hR h) rfl
    (rel_initL hh) rv pl Λ μ

end Sim

end Spike.Bridge
