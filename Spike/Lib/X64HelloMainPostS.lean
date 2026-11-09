/-
**`hello.w`'s `scc_rt_main` from `wc_rodata`'s return, frameless** (x86-64; twin of
`Spike/Lib/A64HelloMainPostS.lean`'s live part): `scc_rt_main` from `.x2` (`wc_rodata`'s return of invariant
`Jr`, left its region) into `wc_main`'s segment, and the split by frames of `scc_rt_main`'s states from
`wc_rodata`'s `.x15`: `wc_rodata`'s under the frame `fr` its source call pushed (`HelloRdCf.frH env`), the `.x2`
block's with none.

- `MainPostSWH`: `wc_rodata`'s states from `.x15` at `[fr]`, the `.x2` block's at `[]`.
- `hello_main_sp0_segW`: `scc_rt_main` from `.x2` (of `wc_rodata`'s return invariant `Jr`, left its region)
  into `wc_main`'s segment, frameless.

## Differences from the AArch64 version

- `wc_rodata`'s return lands at `.Lscc_rt_main.x0` (AArch64's `.L1_scc_rt_main.sp0`); the names
  `hello_main_sp0_segW`, `MainPostSWH.sp0` are kept for the twin. `call wc_main` pushes `.Lscc_rt_main.x1`
  (`.x2 + 41`, `label_labelGapB`) at `-80`; `wc_main`'s region `wcR R D` reaches the return address's cell
  (`hi' = 8`), with no 16-alignment (`hD8 : D % 8 = 0`, no `hal`), and the bounds are `R.lo ≤ -288`,
  `8 ≤ R.hi`.
- `RdPostW` has no fence node (scc's `# fence st` emits no code), so `MainPostSWH` has no `J5`.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `hello_main_post_segWS`.
-/
import Spike.Lib.X64HelloMain
import Spike.Lib.X64HelloRdCf

namespace Spike.Lib.X64.Flow.HelloM

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (seg_oneW)
open Spike.Lib.X64.Flow.Hello1 (mB1 mB1_ok mB1_run mainIn mR mF mS0 mWC)
open Spike.Lib.X64.Flow.HelloRd (RdPostW)
open Scc.Cert.Rt.X64 (Lays endOf code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_main` from `.x2`, frameless -/

section MainSp0

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from `.x2` into `wc_main` is one segment inside `W`** in any valid layout of `helloCells`,
for a caller's state `σC` at `wc_rodata`'s call: from `.x2` (`wc_rodata`'s return of invariant `Jr`, left its
region), the `.x2` block (`hsp0`), the call of `wc_main` into its region at the call (`D` deep, `at_enter`),
then `wc_main`'s segment there (`hWc`). -/
theorem hello_main_sp0_segW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {D : Int} (hD : 0 ≤ D) (hD8 : D % 8 = 0)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 8 ≤ R.hi) {σC : AS} {Jr : AS → Ctl → Prop}
    (hsp0 : BlkW W K exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr) mB1)
    {Q : MachineData → AS → Frag isa}
    (hWc : ∀ m1 σ1, (wcR R D).OK → FStable (wcR R D) (wcF R D F m1 σ1) →
      SegW W K p lbl ms (At exe endPc (wcR R D) (wcF R D F m1 σ1)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1⟩) (Q m1 σ1)) :
    SegW W K p lbl ms (At exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr))
      (fun s c => ∃ m1 σ1, Q m1 σ1 s c) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := hello_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, hb1⟩, -⟩, hg2⟩ := hin
  have e41 : (_root_.Executable.labels exe).label ".Lscc_rt_main.x1" =
      (_root_.Executable.labels exe).label ".Lscc_rt_main.x0" + Int64.ofNat 41 := label_labelGapB hp hg2
  refine SegW.seq (Q := At exe endPc R F (mWC lab σC Jr))
    (seg_oneW (seg_ndW (by simp [mB1]) mB1_ok hF hR hlo hhi
      (code_field hp hend hb1 (ofNat_zero' _)) hsp0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)) ?_
  · simp only [mS0, mWC]; rw [mB1_run]
  · simp only [mS0, mWC]; rw [mB1_run]; rfl
  · simp only [mS0, mWC] at hJ ⊢
    obtain ⟨σx, hJr, rfl⟩ := hJ
    rw [mB1_run]
    refine ⟨σx, hJr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp only [Reg64s.set64]
      show (leave (mR R) (-80) σC σx).slot (-16) = _
      simp only [leave]
      exact ite_eq_right (by simp only [Region.Off, Region.callee]; omega)
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp only [lab]
      rw [e41]
      simp only [upd_apply, ↓reduceIte, Int64.toBitVec_add]
      rfl
  · -- `wc_main` in its region
    refine SegW.mono_pre (P := fun s c => ∃ G : MachineData × AS, At exe endPc (wcR R D) (wcF R D F G.1 G.2)
      ⟨lab "wc_main", ⟨0, []⟩, wcJ0 (mWC lab σC Jr).J G.2⟩ s c) (SegW.exists_pre fun G => ?_) ?_
    · obtain ⟨hR'', hF''⟩ := wcR_ok hD hD8 hR hF hloD (by omega) G.1 G.2
      exact (hWc G.1 G.2 hR'' hF'').mono_post fun s c h => ⟨G.1, G.2, h⟩
    · intro s c h
      obtain ⟨m1, σ1, he, hn, hdc, hpc, σ, hA, hD', hc, hσ, hJ⟩ := at_enter (e0 := 0) (lo' := -D) (hi' := 8)
        (by show R.lo ≤ -80 - 0 + -D; omega) (by show (-80 : Int) - 0 + 8 ≤ R.hi; omega)
        (by show ((-80 : Int) - 0) % 8 = 0; decide) h
      exact ⟨(m1, σ1), he, hn, hdc, hpc, σ, hA, hD', hσ, hc ▸ hJ⟩

end MainSp0

/-! ## `scc_rt_main`'s states from `wc_rodata`'s `.x15`, by frames -/

/-- **`scc_rt_main`'s states from `wc_rodata`'s `.x15` with frames**: `wc_rodata`'s under the frame `fr` its
source call pushed, the `.x2` block's with none. -/
structure MainPostSWH (W : FragS isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fr : TermRun.Frame) (m0 : MachineData) (σC : AS)
    (Jp Jp' J1 J2 J2' J3 J4 Jr : AS → Ctl → Prop) : Prop where
  rd : RdPostW (fun s c => W s c [fr]) K exe endPc (mR R) (mF R F m0 σC) Jp Jp' J1 J2 J2' J3 J4
  sp0 : BlkW (fun s c => W s c []) K exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr) mB1

end Spike.Lib.X64.Flow.HelloM

/--
info: 'Spike.Lib.X64.Flow.HelloM.hello_main_sp0_segW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloM.hello_main_sp0_segW
