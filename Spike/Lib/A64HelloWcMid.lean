/-
**hello.w's `wc_main` from the box's store to its `clone`'s `svc`** (AArch64), inside `W`, in
any valid layout of `helloProg`: the twin of `Spike/Lib/A64WakeWcMid.lean` at hello's `wc_main` (frame 144), the
segments past the box's store composed,

    .sp0+16 .. .sp3     hello_wc_res_segW        (publish, the reserve; A64HelloWcSp0)
    .sp3 .. .sp6        hello_wc_sp3_sp6_segW    (the second TCB, the tid word, thread_init; A64HelloWcSp3)
    .sp6 .. svc         hello_wc_sp6_segW        (the packet, the clone's arguments; A64HelloWcSp6Seg)

at one memory side `ms` and labels `lbl` (those after the box's `new`: the segment before, `hello_wc_sp0_segW`,
ends at the store's `Out.newStore`). At `.sp3` the frame's words (the slice's registers `sl`, main's word `me`, the
cell `cA`, the caller's saved `x29`, `x30` `fr`) and the source `c0` become the later segments' ghosts
(`rXH_wcN3H`); the exit keeps what the source's `S l A c0` and the cell's word `cA = A` say (wake's `MidG`), and that
`fr`, `sl` and `me` are one entry state's `x29`, `x30`, `x0 .. x4` (`FrMGH`, hello's `FrMG`: `wc_main` spills five
arguments where wake's spills one).

Carried premises: `hhdr`, `htcb` (`scc_rt_alloc_tcb` at `tcb2QH g c0`, `n0 = 80`), `htid`
(the second TCB's tid word) and `hti` (`scc_rt_thread_init` at `tiQ (tH lab) c0 g`, `k0 = 16384`). Unlike wake's,
`hti` is asked only at the ghosts the exit keeps (`MidG`, `FrMGH`), which is weaker.

- `FrMGH`: the saved pair, the slice and main's word are one entry's `x29`, `x30`, `x0 .. x4`;
- `rXH_wcN3H`: `.sp3`'s exit of the reserve is `wcN3H` at the frame's words;
- `WcMidWH`: the segments' states inside `W`, at every ghost;
- `hello_wc_mid_segW`: the composite.
-/
import Spike.Lib.A64HelloWcSp3
import Spike.Lib.A64HelloWcSp6Seg
import Spike.Lib.A64WakeWcMid

namespace Spike.Lib.A64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (tiN tiX)
open Spike.Lib.A64.HelloPh.WcSp6 (oWH FrWH wcNSH WcSp6W hello_wc_sp6_segW)
open Spike.Lib.A64.Flow.WakeWc (AGB MidG kOf tiQ)
open Spike.Lib.A64.Rt (TcbOkGA hdrA)
open Spike.Lib.A64.Rt.Reserve (ResOkA)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- **The saved pair, the slice and main's word are the caller's**: `fr`, `sl` and `me` are the `x29`, `x30` and
`x0 .. x4` of one entry state of `J1` (the prologue's saves and spills, `wcJH`). -/
def FrMGH (J1 : AS → Ctl → Prop) (fr : BitVec 64 × BitVec 64) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (me : BitVec 64) : Prop :=
  ∃ σe c, J1 σe c ∧ fr = (σe.regs.X29.toBitVec, σe.regs.X30.toBitVec) ∧
    sl = (σe.regs.X0.toBitVec, σe.regs.X1.toBitVec, σe.regs.X2.toBitVec, σe.regs.X3.toBitVec) ∧
    me = σe.regs.X4.toBitVec

/-- **`wc_main`'s states past the box's store inside `W`**: the reserve's segment's (the fence's at the source facts
`Q`), and at every ghost (`c0`, `sl`, `me`, `cA`, `fr`) with `MidG S c0 cA` and `FrMGH J1 fr sl me` (as
`rXH_wcN3H` exits) the second TCB's, `.sp4`'s and `.sp6`'s (the last at the frame condition `F₂`). -/
structure WcMidWH (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F F₂ : MachineData → Prop) (ms : MemSide isaLSE2) (J1 : AS → Ctl → Prop)
    (S Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  res : WcResWH W K exe endPc R F ms J1 S Q
  sp3 : ∀ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me → WcSp3WH W K exe endPc R F c0 sl me cA fr
  sp4 : ∀ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me →
    WcSp4WH W K exe endPc R F c0 (tH (_root_.Executable.labels exe).label) sl me cA fr
  sp6 : ∀ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me →
    WcSp6W W K exe endPc R F₂ c0 (tH (_root_.Executable.labels exe).label) (kOf (_root_.Executable.labels exe).label)
      sl me cA fr

/-- From the box's store to the `svc` inside the trivial predicate, with no outside moves. -/
theorem WcMidWH.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop}
    {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcMidWH (fun _ _ => True) (fun _ _ => False) exe endPc R F F₂ ms J1 S Q :=
  ⟨WcResWH.triv, fun _ _ _ _ _ _ => ⟨BlkW.triv, fun _ _ i => by
    cases i <;> dsimp only [Spike.Lib.A64.Rt.TcbWG] <;>
      first | exact BlkW.triv | exact fun _ _ _ => ⟨trivial, fun _ h => h⟩⟩,
    fun _ _ _ _ _ _ => WcSp4WH.triv, fun _ _ _ _ _ _ => WcSp6W.triv⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The reserve's exit at `.sp3` is `wcN3H`** at the frame's words (the slice `sl` at `[sp, #0 .. #24]`, main's
word `me` at `[sp, #32]`, the cell `cA` at `[sp, #40]`, the caller's saved pair `fr`), the source `c` its ghost,
`MidG` and `FrMGH` holding. -/
theorem rXH_wcN3H {J1 : AS → Ctl → Prop} {S : WeakMem.AllocLabel → Nat → Ctl → Prop} {s : State} {c : Ctl}
    {x : Unit} (h : At exe endPc R F (rXH ms (_root_.Executable.labels exe).label J1 S x) s c) :
    ∃ (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64),
      MidG S c cA ∧ FrMGH J1 fr sl me ∧
      At exe endPc R F (wcN3H (_root_.Executable.labels exe).label c sl me cA fr) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, l, A, hS, ⟨q, ⟨σe, hJ1, h16, h8, h0, h1, h2, h3, h4⟩, h104⟩, hx0⟩ := h
  refine ⟨(σ.slot (-144), σ.slot (-136), σ.slot (-128), σ.slot (-120)), σ.slot (-112), σ.slot (-104),
    (σ.slot (-16), σ.slot (-8)), ⟨l, A, hS, h104⟩, ⟨σe, _, hJ1, ?_, ?_, ?_⟩, he, hn, hdc, hpc, σ, hA, hD, rfl,
    j3H_self hx0⟩
  · rw [h16, h8]
  · rw [h0, h1, h2, h3]
  · exact h4

/-- **`wc_main` from the box's store to its `clone`'s `svc` is one segment inside `W`** in any valid layout of
`helloProg`: from the landing past the box's store (`bXH l A`, some fresh label `l`, the source at `Q l A`) to the
`svc` (`wcNSH` at the second TCB `tH lab`, the child's stack top `kOf lab`, the frame's words), the source at some
`c0` with `MidG`, the frame's words the caller's with `FrMGH`. The premises are the three segments'
(`hello_wc_res_segW`, `hello_wc_sp3_sp6_segW`, `hello_wc_sp6_segW`) at every ghost the exit keeps; `K` keeps the
caller's cells outside `scc_rt_alloc_tcb`'s region (`hKR`), hence outside `scc_rt_thread_init`'s. -/
theorem hello_wc_mid_segW {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -400) (hhi : 0 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hW : WcMidWH W K exe endPc R F F₂ ms J1 S Q)
    (hfr : ∀ (q : AGB ms (_root_.Executable.labels exe).label) (l : WeakMem.AllocLabel) (A : Nat),
      Q l A ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ →
      ∃ c', FenceRun p ms.pub .st
        ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ c' ∧ S l A c')
    (hres : ∀ g : Flow.Reserve.G × Ctl, ResOkA ms F exe endPc (rARH R) F ⟨g.1, 0#64, g.2⟩)
    (hhdr : ∀ c0 g, Ret0.StOk ms F exe endPc (hdrA (_root_.Executable.labels exe).label (tcb2QH g c0))
      ((tcb2QH g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ c0 g, TcbOkGA ms F exe endPc (R.callee (-144) (-192) 0) F (tcb2QH g c0))
    (htid : let t := tH (_root_.Executable.labels exe).label
      ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-144) (-192) 0).Off (k - -144) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me →
      let t := tH (_root_.Executable.labels exe).label
      ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-144) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -144) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oWH mC σC ∧
          (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -144) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms (At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e))
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms
      (fun s c => ∃ l A, At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c ∧ Q l A c)
      (fun s c => ∃ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me ∧
        At exe endPc R F₂ (wcNSH (_root_.Executable.labels exe).label c0 (tH (_root_.Executable.labels exe).label)
          (kOf (_root_.Executable.labels exe).label) sl me cA fr) s c) := by
  let lab := (_root_.Executable.labels exe).label
  have hKR4 : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-144) (-256) 0).Off (k - -144) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8 :=
    fun s s' hk hD k hk' hn => hKR s s' hk hD k hk' fun ⟨h1, h2, h3⟩ =>
      hn ⟨h1, by simp only [Region.callee] at h2 ⊢; omega, by simp only [Region.callee] at h3 ⊢; omega⟩
  -- one ghost: `.sp3` to the `svc`
  have hG : ∀ (c0 : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64)
      (fr : BitVec 64 × BitVec 64),
      SegW W K p lbl ms
        (fun s c => At exe endPc R F (wcN3H lab c0 sl me cA fr) s c ∧ (MidG S c0 cA ∧ FrMGH J1 fr sl me))
        (fun s c => ∃ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me ∧
          At exe endPc R F₂ (wcNSH lab c0 (tH lab) (kOf lab) sl me cA fr) s c) :=
    fun c0 sl me cA fr => SegW.of_imp fun hM =>
      ((hello_wc_sp3_sp6_segW hp hend hF hR hal hlo hhi hF₂ (hW.sp3 c0 sl me cA fr hM) (hW.sp4 c0 sl me cA fr hM)
        (hhdr c0) (htcb c0) htid hFK hKR hKR4 (hti c0 sl me cA fr hM)).seq
        (hello_wc_sp6_segW hp hend hF₂s hR hal (by omega) hhi (hW.sp6 c0 sl me cA fr hM))).mono_post
        fun _ _ h => ⟨c0, sl, me, cA, fr, hM.1, hM.2, h⟩
  refine (hello_wc_res_segW hp hend hF hR hal (by omega) hhi hW.res hfr hres).seq ?_
  refine (SegW.exists_pre (P := fun (g : Ctl × (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) × BitVec 64 ×
      BitVec 64 × (BitVec 64 × BitVec 64)) s c =>
    At exe endPc R F (wcN3H lab g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2) s c ∧
      (MidG S g.1 g.2.2.2.1 ∧ FrMGH J1 g.2.2.2.2 g.2.1 g.2.2.1))
    fun g => hG g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).mono_pre ?_
  rintro s c ⟨x, h⟩
  obtain ⟨sl, me, cA, fr, hM, hGm, h⟩ := rXH_wcN3H h
  exact ⟨(c, sl, me, cA, fr), h, hM, hGm⟩

end Seg

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.rXH_wcN3H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.rXH_wcN3H

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_mid_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_mid_segW
