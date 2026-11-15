/-
**Forward segments of a `Solo` thread with the shared memory and the
extension state stated exactly** (`ExtMachine.ofHooks`, any ISA): the
composition layer over `Spike/Lib/X64Fwd.lean` and
`Spike/Lib/X64FwdSys.lean`.

`SegP μ tid P M X P' M' X'`: from every configuration where thread `tid`
runs alone (`Solo`) at a state satisfying `P`, with shared memory exactly
`M` and extension state exactly `X`, some run with no events reaches a
configuration where it runs alone at a state satisfying `P'`, with shared
memory exactly `M'`, extension state exactly `X'` and every other thread
unchanged.

- `SegP.trans`, `SegP.refl`: segments compose.
- One segment per step shape: `segP_done`, `segP_silent`, `segP_choose`
  (a fixed leaf of a choice), `segP_load`
  (reads `M.finalVal l`), `segP_store` (`M' = (M.append ⟨l, v, tid⟩).1`),
  `segP_rmw` (under `A.rmwFence`), and for the kernel hooks
  `segP_rtSigaction`, `segP_archSetFs`, `segP_take` (`X'` holds the range,
  `pmem` erased there).
- `Memory.finalVal` over `append`: `finalVal_append_same`,
  `finalVal_append_ne`.

Nothing here is specific to an ISA or a program.
-/
import Spike.Lib.X64FwdSys

namespace Spike.Lib.Fwd

open Scc.Sem Kraken Kraken.Promising

section Seg

variable {I : ISA} {A : Arch} {H : Hooks I} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat}

variable (I A H rv pl pcf) in
/-- **A forward segment of thread `tid`** from the states `P` at shared
memory `M` and extension state `X` to the states `P'` at `M'` and `X'`:
no events, the other threads unchanged. -/
def SegP (μ : Marks) (tid : Nat) (P : I.State → Prop) (M : Memory) (X : H.X) (P' : I.State → Prop)
    (M' : Memory) (X' : H.X) : Prop :=
  ∀ (c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg) (s : I.State), P s → Solo c tid s → c.1.mem = M → c.2 = X →
    ∃ s' d, P' s' ∧ (ExtMachine.ofHooks I A H rv pl pcf).Run μ c [] d ∧ Solo d tid s' ∧ d.1.mem = M' ∧
      d.2 = X' ∧ ∀ i, i ≠ tid → d.1.threads[i]? = c.1.threads[i]?

variable {μ : Marks} {tid : Nat} {P P1 P2 : I.State → Prop} {M M1 M2 : Memory} {X X1 X2 : H.X}

theorem SegP.refl : SegP I A H rv pl pcf μ tid P M X P M X :=
  fun c s hP h hm hx => ⟨s, c, hP, .refl _, h, hm, hx, fun _ _ => rfl⟩

theorem SegP.trans (h1 : SegP I A H rv pl pcf μ tid P M X P1 M1 X1)
    (h2 : SegP I A H rv pl pcf μ tid P1 M1 X1 P2 M2 X2) : SegP I A H rv pl pcf μ tid P M X P2 M2 X2 := by
  intro c s hP h hm hx
  obtain ⟨s1, d1, hP1, r1, h1', m1, x1, o1⟩ := h1 c s hP h hm hx
  obtain ⟨s2, d2, hP2, r2, h2', m2, x2, o2⟩ := h2 d1 s1 hP1 h1' m1 x1
  exact ⟨s2, d2, hP2, LRun.trans r1 r2, h2', m2, x2, fun i hi => (o2 i hi).trans (o1 i hi)⟩

/-- Weaken the target states. -/
theorem SegP.mono {P2 : I.State → Prop} (h1 : SegP I A H rv pl pcf μ tid P M X P1 M1 X1)
    (h : ∀ s, P1 s → P2 s) : SegP I A H rv pl pcf μ tid P M X P2 M1 X1 := by
  intro c s hP hs hm hx
  obtain ⟨s1, d1, hP1, r1, h1', m1, x1, o1⟩ := h1 c s hP hs hm hx
  exact ⟨s1, d1, h s1 hP1, r1, h1', m1, x1, o1⟩

/-- The run of a segment from a configuration. -/
theorem SegP.run (h : SegP I A H rv pl pcf μ tid P M X P1 M1 X1) {c : (ExtMachine.ofHooks I A H rv pl pcf).Cfg}
    {s : I.State} (hP : P s) (hs : Solo c tid s) (hm : c.1.mem = M) (hx : c.2 = X) :
    ∃ s' d, P1 s' ∧ (ExtMachine.ofHooks I A H rv pl pcf).Run μ c [] d ∧ Solo d tid s' ∧ d.1.mem = M1 ∧
      d.2 = X1 ∧ ∀ i, i ≠ tid → d.1.threads[i]? = c.1.threads[i]? :=
  h c s hP hs hm hx

/-! ## One step per shape -/

/-- A no-event instruction. -/
theorem segP_done
    (h : ∀ s, P s → H.atSys s = false ∧ (∀ k a, μ.site k = some a → pcf s ≠ a) ∧
      ∃ s', P1 s' ∧ I.exec s = some (.done s')) : SegP I A H rv pl pcf μ tid P M X P1 M X := by
  intro c s hP hs hm hx
  obtain ⟨hsys, hsite, s', hP1, hex⟩ := h s hP
  obtain ⟨d, hst, h', hm', hk⟩ := fwd_done hs hsys hsite hex
  exact ⟨s', d, hP1, run_of_step hst, h', hm'.trans hm, hk.1.trans hx, hk.2⟩

/-- A silent instruction (a finite choice of `done` leaves). -/
theorem segP_silent
    (h : ∀ s, P s → H.atSys s = false ∧ (∀ k a, μ.site k = some a → pcf s ≠ a) ∧
      ∃ tree, I.exec s = some tree ∧ Lower.SilentTree P1 tree) : SegP I A H rv pl pcf μ tid P M X P1 M X := by
  intro c s hP hs hm hx
  obtain ⟨hsys, hsite, tree, hex, hsil⟩ := h s hP
  obtain ⟨s', d, hP1, hst, h', hm', hk⟩ := fwd_silent hs hsys hsite hex hsil
  exact ⟨s', d, hP1, run_of_step hst, h', hm'.trans hm, hk.1.trans hx, hk.2⟩

/-- A finite choice of `done` leaves: leaf `i` is taken (so the next state can
be stated exactly, e.g. x64's undefined `AF` fixed). -/
theorem segP_choose
    (h : ∀ s, P s → H.atSys s = false ∧ (∀ k a, μ.site k = some a → pcf s ≠ a) ∧
      ∃ (m : Nat) (k : Fin m → EvTree I.State) (i : Fin m) (s' : I.State),
        I.exec s = some (.choose m k) ∧ k i = .done s' ∧ P1 s') : SegP I A H rv pl pcf μ tid P M X P1 M X := by
  intro c s hP hs hm hx
  obtain ⟨hsys, hsite, m, k, i, s', hex, hk, hP1⟩ := h s hP
  obtain ⟨s'', d, hP1', hst, h', hm', hk'⟩ := fwd_treeP (P := fun x => x = s') hs hsys hsite hex fun t _ hp _ =>
    ⟨s', Live.TicketStep.ctx0 tid t c.1.mem, rfl, (Lower.run_choose_iff A tid _).mpr ⟨i, by rw [hk]; exact Live.TicketStep.run_done_exists A tid _ _ s'⟩, rfl, hp⟩
  subst hP1'
  exact ⟨_, d, hP1, run_of_step hst, h', hm'.trans hm, hk'.1.trans hx, hk'.2⟩

/-- A load of `l`: it reads `M.finalVal l`. -/
theorem segP_load (l : Loc)
    (h : ∀ s, P s → H.atSys s = false ∧ (∀ k a, μ.site k = some a → pcf s ≠ a) ∧
      ∃ (k : LoadKind) (f : Val → I.State), I.exec s = some (.load k false l fun v => .done (f v)) ∧
        P1 (f (M.finalVal l))) : SegP I A H rv pl pcf μ tid P M X P1 M X := by
  intro c s hP hs hm hx
  obtain ⟨hsys, hsite, k, f, hex, hP1⟩ := h s hP
  obtain ⟨d, hst, h', hm', hk⟩ := fwd_load hs hsys hsite hex
  exact ⟨_, d, hm ▸ hP1, run_of_step hst, h', hm'.trans hm, hk.1.trans hx, hk.2⟩

/-- A plain store of `v` to `l`: the message is appended. -/
theorem segP_store (l : Loc) (v : Val)
    (h : ∀ s, P s → H.atSys s = false ∧ (∀ k a, μ.site k = some a → pcf s ≠ a) ∧
      ∃ (k : StoreKind) (s' : I.State), I.exec s = some (.store k false l v fun _ => .done s') ∧ P1 s') :
    SegP I A H rv pl pcf μ tid P M X P1 (M.append { loc := l, val := v, tid }).1 X := by
  intro c s hP hs hm hx
  obtain ⟨hsys, hsite, k, s', hex, hP1⟩ := h s hP
  obtain ⟨d, hst, h', hm', hk⟩ := fwd_store hs hsys hsite hex
  exact ⟨s', d, hP1, run_of_step hst, h', by rw [hm', hm], hk.1.trans hx, hk.2⟩

/-- An always-writing RMW of `l` under `rmwFence`: it reads `M.finalVal l` and
appends `g` of it. -/
theorem segP_rmw (hA : A.rmwFence = true) (l : Loc) (g : Val → Val)
    (h : ∀ s, P s → H.atSys s = false ∧ (∀ k a, μ.site k = some a → pcf s ≠ a) ∧
      ∃ (k : RmwKind) (f : Val → I.State),
        I.exec s = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v)) ∧ P1 (f (M.finalVal l))) :
    SegP I A H rv pl pcf μ tid P M X P1 (M.append { loc := l, val := g (M.finalVal l), tid }).1 X := by
  intro c s hP hs hm hx
  obtain ⟨hsys, hsite, k, f, hex, hP1⟩ := h s hP
  obtain ⟨d, hst, h', hm', hk⟩ := fwd_rmw hA hs hsys hsite hex
  refine ⟨_, d, hm ▸ hP1, run_of_step hst, h', by rw [hm', hm], hk.1.trans hx, hk.2⟩

end Seg

/-! ## Kernel steps -/

section Kern

variable {I : ISA} {A : Arch} {K : Kernel.Abi I} {n : Nat} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat} {μ : Marks} {tid : Nat}
  {P P1 : I.State → Prop} {M : Memory} {X : Kernel.KState}

/-- `rt_sigaction` returns 0. -/
theorem segP_rtSigaction
    (h : ∀ s, P s → K.atSys s = true ∧ Kernel.decode K.nrs (K.nr s) (K.arg s) = some .rtSigaction ∧
      P1 (K.ret s 0)) : SegP I A (Kernel.hooks K A n) rv pl pcf μ tid P M X P1 M X := by
  intro c s hP hs hm hx
  obtain ⟨hsys, hc, hP1⟩ := h s hP
  obtain ⟨d, hst, h', hm', hk⟩ := fwd_rtSigaction hs hsys hc
  exact ⟨_, d, hP1, run_of_step hst, h', hm'.trans hm, hk.1.trans hx, hk.2⟩

/-- `arch_prctl(ARCH_SET_FS, a)` sets the thread pointer and returns 0. -/
theorem segP_archSetFs (a : Nat)
    (h : ∀ s, P s → K.atSys s = true ∧ Kernel.decode K.nrs (K.nr s) (K.arg s) = some (.archSetFs a) ∧
      P1 (K.ret (K.setTp s a) 0)) : SegP I A (Kernel.hooks K A n) rv pl pcf μ tid P M X P1 M X := by
  intro c s hP hs hm hx
  obtain ⟨hsys, hc, hP1⟩ := h s hP
  obtain ⟨d, hst, h', hm', hk⟩ := fwd_archSetFs hs hsys hc
  exact ⟨_, d, hP1, run_of_step hst, h', hm'.trans hm, hk.1.trans hx, hk.2⟩

/-- **The take** of the range `r` at the take site: `r` is fresh at `M`,
`X`; the thread's private memory gets `X.pmem`'s bytes on `r`, `r` becomes
held by `tid` and leaves the pool. -/
theorem segP_take (r : Range)
    (hf : ∀ c : Config I × Kernel.KState, c.1.mem = M → c.2 = X → Kernel.fresh c r = true)
    (h : ∀ s, P s → μ.site .take = some (pcf s) ∧ K.atNop s = true ∧ Kernel.siteRange K s = r ∧
      P1 (K.skip (K.setDmem s (Kernel.copyRange X.pmem (K.dmem s) r)))) :
    SegP I A (Kernel.hooks K A n) rv pl pcf μ tid P M X P1 M
      { X with held := (tid, r) :: X.held, pmem := Kernel.eraseRange X.pmem r } := by
  intro c s hP hs hm hx
  obtain ⟨hsite, hn, hr, hP1⟩ := h s hP
  obtain ⟨d, hst, h', hm', hx', ho⟩ := fwd_take hs hsite hn (hr ▸ hf c hm hx)
  refine ⟨_, d, ?_, run_of_step hst, h', hm'.trans hm, ?_, ho⟩
  · rw [hr, hx]; exact hP1
  · rw [hx', hr, hx]

end Kern

/-! ## `finalVal` over appends -/

theorem finalVal_append_same (M : Memory) (l : Loc) (v : Val) (tid : Nat) :
    (M.append { loc := l, val := v, tid }).1.finalVal l = v := by
  simp [Memory.append, Memory.finalVal, Array.findRev?, Array.reverse_push]

theorem finalVal_append_ne (M : Memory) {l l' : Loc} (v : Val) (tid : Nat) (h : (l' == l) = false) :
    (M.append { loc := l', val := v, tid }).1.finalVal l = M.finalVal l := by
  simp [Memory.append, Memory.finalVal, Memory.initVal, Array.findRev?, Array.reverse_push, h]

end Spike.Lib.Fwd


/-- info: 'Spike.Lib.Fwd.SegP.refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.SegP.refl

/-- info: 'Spike.Lib.Fwd.SegP.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.SegP.trans

/-- info: 'Spike.Lib.Fwd.SegP.mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.SegP.mono

/-- info: 'Spike.Lib.Fwd.SegP.run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.SegP.run

/-- info: 'Spike.Lib.Fwd.segP_done' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.segP_done

/-- info: 'Spike.Lib.Fwd.segP_silent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.segP_silent

/-- info: 'Spike.Lib.Fwd.segP_choose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.segP_choose

/-- info: 'Spike.Lib.Fwd.segP_load' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.segP_load

/-- info: 'Spike.Lib.Fwd.segP_store' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.segP_store

/-- info: 'Spike.Lib.Fwd.segP_rmw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.segP_rmw

/-- info: 'Spike.Lib.Fwd.segP_rtSigaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.segP_rtSigaction

/-- info: 'Spike.Lib.Fwd.segP_archSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.segP_archSetFs

/-- info: 'Spike.Lib.Fwd.segP_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.segP_take

/-- info: 'Spike.Lib.Fwd.finalVal_append_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.finalVal_append_same

/-- info: 'Spike.Lib.Fwd.finalVal_append_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.finalVal_append_ne
