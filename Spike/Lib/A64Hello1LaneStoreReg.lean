/-
**`wc_rodata`'s first lane store through the generic rule** (a regression
check of `Spike/Lib/A64LaneStore.lean`): from `.sp0` (`sJp`) past the store
of `"Hello, w"` into element 0, `lane_storeW` with `hello1Prog`'s blocks
`rpB0` and `rpB1`.

- `hello1_store1_laneW`: the instance, the source at `rdC2` after it.
-/
import Spike.Lib.A64LaneStore
import Spike.Lib.A64Hello1RodataSetup

namespace Spike.Lib.A64.Flow

namespace Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow.Ret0 (WcG)
open Spike.Lib.A64.Flow.LaneStore (lane_storeW lsNL lsNH lsNS)
open Spike.Lib.Hello1RodataSrc (rdCA rdC2 eW1 τ8 rdK1 rdK1_lt bufElem_b)

set_option linter.unusedSimpArgs false

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata`'s first lane store is `lane_storeW`'s instance**: from
`.sp0` with `sJp` to the node after the store, the source at `rdC2`, given
the buffer's first word unmapped under `F` (`hbuf`) and the states in `W`. -/
theorem hello1_store1_laneW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (g : WcG)
    (hbuf : ∀ σ0 l, RdF lbl ms g σ0 l → ∀ m, F m → Mem.loadInt m.dmem σ0.regs.X0.toBitVec 8 = none)
    (hW1 : BlkW W K exe endPc R F
      ⟨(_root_.Executable.labels exe).label ".L18_wc_rodata.sp0", ⟨-48, []⟩, sJp lbl ms g⟩ rpB0)
    (hWL : NodeW W K exe endPc R F (lsNL (_root_.Executable.labels exe).label rpB0
      ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0")
      ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 2)) ⟨-48, []⟩ ⟨-48, []⟩
      "w0" "o0" "b" false .w8 rdK1 0 eW1 (sJp lbl ms g)))
    (hW2 : BlkW W K exe endPc R F (lsNH (_root_.Executable.labels exe).label rpB0
      ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0")
      ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 2)) ⟨-48, []⟩ ⟨-48, []⟩
      .X9 .X10 0 "w0" "o0" "b" false .w8 rdK1 0 eW1 (sJp lbl ms g)) rpB1)
    (hWS : NodeW W K exe endPc R F (lsNS (_root_.Executable.labels exe).label rpB0 rpB1
      ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0")
      ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 2))
      ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 9)) ⟨-48, []⟩ ⟨-48, []⟩
      ⟨-48, []⟩ .X9 .X10 0 "w0" "o0" "b" false .w8 rdK1 0 eW1 (sJp lbl ms g))) :
    SegW W K p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L18_wc_rodata.sp0", ⟨-48, []⟩, sJp lbl ms g⟩)
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 9) +
        Int64.ofNat 4, ⟨-48, []⟩, fun _ c => ∃ l ini wo0, c = rdC2 l ini wo0⟩) := by
  have hin := hello1_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have hk : ∀ σ : AS, (Spike.Lib.upd σ.slot (-48) σ.regs.X0.toBitVec) (-48) = σ.regs.X0.toBitVec := fun σ => by
    simp [Spike.Lib.upd_apply]
  refine lane_storeW (B1 := rpB0) (B2 := rpB1) (o := ⟨-48, []⟩) (oL := ⟨-48, []⟩) (oS := ⟨-48, []⟩)
    (t := .X9) (b := .X10) (t' := .X9) (i := 0) (lo := -48) (hi := 0)
    (pcL := lab ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 2))
    (pcS := lab ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 9))
    (by simp [rpB0]) (by simp [rpB1]) rpB0_ok rpB1_ok hF hR hal hlo hhi
    (code_of hp hend c0 (ofNat4_zero _)) (code_of hp hend c1 rfl)
    (code_of hp hend c2 (by rw [Int64.add_assoc]; rfl)) (code_of hp hend c3 rfl)
    (fun σ => by rw [rpB0_run]; exact ⟨by simp only [Int64.add_assoc]; rfl, rfl⟩)
    (fun σ => by
      show (arun lab rpB1 ⟨_, ⟨-48, []⟩, σ⟩).pc = _ ∧ (arun lab rpB1 ⟨_, ⟨-48, []⟩, σ⟩).so = _
      rw [rpB1_run]; exact ⟨by simp only [Int64.add_assoc]; rfl, rfl⟩)
    ⟨rfl, rfl, rfl⟩ (by decide) rdK1_lt ?ht ?hsrc hW1 hWL hW2 hWS
  case ht =>
    rintro σ c ⟨l, ini, -, rfl⟩
    rfl
  case hsrc =>
    rintro σ c ⟨l, ini, hRF, rfl⟩
    obtain ⟨A, old, hl, hx0, -⟩ := id hRF
    have h10 : rAddr (arun lab rpB0 ⟨lab ".L18_wc_rodata.sp0", ⟨-48, []⟩, σ⟩).σ.regs .X10 0 =
        σ.regs.X0.toBitVec := by
      rw [rpB0_run]; simp [rAddr, Reg64s.getXReg]
    refine ⟨_, _, .own, l, A, rfl, rfl, bufElem_b ini, hl, ?_, ?_, fun r => ⟨?_, ?_, fun wold => ⟨l, ini, wold, rfl⟩⟩⟩
    · rw [h10, show σ.regs.X0.toBitVec.toNat = σ.regs.X0.toNat from rfl, hx0]; omega
    · intro m hm; rw [h10]; exact hbuf σ l hRF m hm
    · show rAddr (arun lab rpB1 ⟨_, ⟨-48, []⟩, _⟩).σ.regs .X10 0 = _
      rw [rpB1_run, h10, rpB0_run]
      simp [rAddr, Reg64s.getXReg, ldStep, Spike.Lib.upd_apply]
    · show (((arun lab rpB1 ⟨_, ⟨-48, []⟩, _⟩).σ.regs.getRegOrZr (.low (.reg .X9) .W64)).setWidth 128).toNat = _
      rw [rpB1_run, Ret0.getRegOrZr_x9]
      rfl

end Hello1

end Spike.Lib.A64.Flow
