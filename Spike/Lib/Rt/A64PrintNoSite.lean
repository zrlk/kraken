/-
**`scc_rt_print`'s write tail is off the transfer sites** (AArch64), at any
layout: the `hns` premise of `printIn_steps` (`Spike/Lib/Rt/A64PrintDt.lean`)
from the runtime routines' phase check (`printPhOk`, part of A7's
`tailOffC`, `Spike/Lib/A64TailPh.lean`): every pc of a piece is checked off
the sites (`okPc`), and a pc off the sites is neither transfer site.

- `siteAt_of_okPc`: at a pc off the record's sites (`PhRec.okPc`), no
  transfer site of its marks (`PhRec.μ`);
- `okPc_of_blkPh`, `blkSt_okPc`: a block's phase check puts every pc of the
  block, so every `BlkSt` state's pc, off the sites;
- `printIn_noSite`: from `tailPhOk`'s `scc_rt_print` parts at the record
  (the barrier's `phOne` at `writeL`, `printPhOk` at `fenceLab`), `PrintIn`
  (any region, ghosts and frame condition) is off the transfer sites;
- `tailPhOk_ofPlaceOK`: `tailPhOk` at the record of an output passing
  `placeOK`, from A7's `tailOffC` (`tailOff_of_placeOKAt`);
  `printIn_noSite_ofPlaceOK`: `printIn_noSite` there; `allocPhOk_ofPlaceOK`,
  `allocAbOk_ofPlaceOK`: `scc_rt_alloc`'s parts of `tailPhOk` there (the
  targets' check, read at `fenceLab`, at the labels by `allocAbOk_fenceLab`).
-/
import Spike.Lib.Rt.A64PrintDt
import Spike.Lib.A64TailPh
import Spike.Lib.A64PhRec

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem
open Scc.Sem.A64 (abi)
open Spike.Lib.A64.Flow
open Spike.Lib.A64
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.A64.PhRec (okPc ph μ ne_of_okPcOf)
open Scc.Cert.Rt.A64.Print (add0)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-! ## Off the sites -/

/-- **A pc off the record's sites** is neither transfer site of its marks. -/
theorem siteAt_of_okPc (L : RuntimeLayout) {s : State} (h : okPc L s.st.2.toBitVec.toNat = true) :
    Kernel.siteAt abi (μ L) s = none := by
  refine Kernel.siteAt_eq_none_iff.mpr ⟨fun he => ?_, fun he => ?_⟩
  · exact ne_of_okPcOf (l := "scc_rt_take_site") h (by simp [Scc.Cert.Rt.A64.siteLabels]) he rfl
  · exact ne_of_okPcOf (l := "scc_rt_release_site") h (by simp [Scc.Cert.Rt.A64.siteLabels]) he rfl

/-- **A block's phase check puts its pcs off the sites.** -/
theorem okPc_of_blkPh {okP : Nat → Bool} {phf : Nat → Nat} {dead : Nat → Bool} {lab : Label → Int64}
    {pc ra : Int64} {blk : List Directive} (h : blkPh okP phf dead lab pc ra blk = true) {k : Nat}
    (hk : k < blk.length) : okP (pc + Int64.ofNat (4 * k)).toBitVec.toNat = true := by
  unfold blkPh at h
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true] at this
  exact this.1.1

/-- **A `BlkSt` state's pc is off the sites** if its block's phase check
holds (at the block's pc, `hpc`). -/
theorem blkSt_okPc {okP : Nat → Bool} {phf : Nat → Nat} {dead : Nat → Bool} {lab : Label → Int64}
    {pc pc' ra : Int64} {blk : List Directive} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {C : MachineData → Prop} {o : SO} {J : Flow.AS → Prop} {s : State}
    (h : blkPh okP phf dead lab pc' ra blk = true) (hpc : pc = pc') (hs : BlkSt exe endPc R C pc o J blk s) :
    okP s.st.2.toBitVec.toNat = true := by
  obtain ⟨-, -, -, σ0, -, k, hk, hp, -⟩ := hs
  rw [hp, hpc]
  exact okPc_of_blkPh h hk

/-! ## `scc_rt_print`'s pieces -/

/-- **`scc_rt_print`'s write tail is off the transfer sites**, from its
phase checks at the record (any region, ghosts and frame condition): the
barrier's (`hf`, at `writeL`) and the body's at `fenceLab` (`h`, the write
block one instruction on). -/
theorem printIn_noSite (L : RuntimeLayout) {Rp : Region} {x29 ra : BitVec 64} {C : MachineData → Prop}
    (hf : StubW.phOne (okPc L) (ph L) (L.lab StubW.writeL) = true)
    (h : StubW.printPhOk (okPc L) (ph L) (StubW.fenceLab L.lab) = true) :
    ∀ s, PrintIn L.exe L.endPc Rp x29 ra C s → Kernel.siteAt abi (μ L) s = none := by
  have hw : StubW.fenceLab L.lab ".L9_scc_rt_print.2_write" = L.lab ".L9_scc_rt_print.2_write" + 4 :=
    ite_eq_left_iff.mpr fun h => absurd rfl h
  have hn : ∀ l, l ≠ ".L9_scc_rt_print.2_write" → StubW.fenceLab L.lab l = L.lab l :=
    fun _ hl => ite_eq_right_iff.mpr fun h => absurd h hl
  simp only [StubW.printPhOk, Bool.and_eq_true, and_assoc, hw, hn ".L9_scc_rt_print.1_loop" (by decide),
    hn ".L9_scc_rt_print.3_chk2" (by decide), hn ".L9_scc_rt_print.4_chk3" (by decide),
    hn ".L9_scc_rt_print.5_adv" (by decide), hn ".L9_scc_rt_print.6_fail" (by decide),
    hn ".L9_scc_rt_print.7_done" (by decide)] at h
  obtain ⟨-, -, p2, p3, p4, ps, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p16, pr⟩ := h
  rintro s ⟨i, hs⟩
  apply siteAt_of_okPc
  cases i
  case loop => exact blkSt_okPc p2 (add0 _).symm hs
  case n3 => exact blkSt_okPc p3 (by simp only [ppc, Int64.add_assoc]; rfl) hs
  case fence =>
    obtain ⟨-, -, -, hpc, -⟩ := hs
    rw [hpc]
    simp only [StubW.phOne, Bool.and_eq_true] at hf
    exact hf.1
  case write => exact blkSt_okPc p4 (add0 _).symm hs
  case svc =>
    obtain ⟨-, -, -, hpc, -⟩ := hs
    rw [hpc]
    simp only [StubW.phOne, Bool.and_eq_true] at ps
    have he : ppc L.exe .svc = L.lab ".L9_scc_rt_print.2_write" + 4 + Int64.ofNat (4 * 4) := by
      simp only [ppc, PrintD.pcSvc, Int64.add_assoc]; rfl
    rw [he]
    exact ps.1
  case n5 => exact blkSt_okPc p5 (by simp only [ppc, PrintD.pcSvc, Int64.add_assoc]; rfl) hs
  case n6 => exact blkSt_okPc p6 (by simp only [ppc, PrintD.pcSvc, Int64.add_assoc]; rfl) hs
  case n7 => exact blkSt_okPc p7 (by simp only [ppc, PrintD.pcSvc, Int64.add_assoc]; rfl) hs
  case chk2 => exact blkSt_okPc p8 (add0 _).symm hs
  case n9 => exact blkSt_okPc p9 (by simp only [ppc, Int64.add_assoc]; rfl) hs
  case n10 => exact blkSt_okPc p10 (by simp only [ppc, Int64.add_assoc]; rfl) hs
  case chk3 => exact blkSt_okPc p11 (add0 _).symm hs
  case n12 => exact blkSt_okPc p12 (by simp only [ppc, Int64.add_assoc]; rfl) hs
  case adv => exact blkSt_okPc p13 (add0 _).symm hs
  case fail => exact blkSt_okPc p14 (add0 _).symm hs
  case done =>
    -- the epilogue's first three instructions by the check of `b16.take 3`, the `ret` by `pr`
    obtain ⟨-, -, -, σ0, -, k, hk, hp, -⟩ := hs
    rw [hp]
    have hpc : ppc L.exe .done = L.lab ".L9_scc_rt_print.7_done" + Int64.ofNat (4 * 0) := (add0 _).symm
    rw [hpc, add0]
    have hl : Print.b16.length = 4 := by decide
    by_cases h3 : k < 3
    · have := okPc_of_blkPh p16 (k := k) (by simp [List.length_take, hl]; omega)
      rwa [add0] at this
    · have : k = 3 := by rw [hl] at hk; omega
      subst this
      exact pr

/-- **A7's `scc_rt_alloc` target check at `fenceLab` is `allocAbOkR` at
the labels**: `unfenceLab` undoes `fenceLab`. -/
theorem allocAbOk_fenceLab {lab : Label → Int64} :
    AllocG.allocAbOk (StubW.fenceLab lab) = AllocG.allocAbOkR lab := by
  unfold AllocG.allocAbOk
  congr 1
  funext l
  by_cases hl : l = ".L9_scc_rt_print.2_write"
  · simp [AllocG.unfenceLab, StubW.fenceLab, StubW.writeL, hl]
  · simp [AllocG.unfenceLab, StubW.fenceLab, StubW.writeL, hl]

/-! ## From the placement check -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- **The runtime routines' phase check** at the record's `okPc`/`ph` and
labels of an output passing `placeOK`, from A7's `tailOffC` (every label
it reads at its `codeOf` address in the loaded thread). -/
theorem tailPhOk_ofPlaceOK :
    StubW.tailPhOk (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab = true :=
  StubW.tailPhOk_of_tailOffC (Scc.Cert.PlaceOK.A64.tailOff_of_placeOKAt h) fun _ _ ha =>
    Scc.Cert.Rt.A64.label_threadAt_of_codeOf_below (E := Scc.Sem.Entry.linux)
      (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
      (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK_below h i ha) ha

/-- **`scc_rt_print`'s write tail is off the transfer sites** at the record
of an output passing `placeOK`, from A7's `tailOffC`. -/
theorem printIn_noSite_ofPlaceOK {Rp : Region}
    {x29 ra : BitVec 64} {C : MachineData → Prop} :
    ∀ s, PrintIn (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc Rp x29 ra C s →
      Kernel.siteAt abi (μ (RuntimeLayout.ofPlaceOK h i)) s = none :=
  printIn_noSite _ (StubW.fencePh_of_tailPhOk (tailPhOk_ofPlaceOK h i))
    (StubW.printPhOk_of_tailPhOk (tailPhOk_ofPlaceOK h i))

/-- **`scc_rt_alloc`'s phase check** at the record of an output passing
`placeOK`, from A7's `tailOffC`. -/
theorem allocPhOk_ofPlaceOK :
    AllocG.allocPhOk (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab = true :=
  StubW.allocPhOk_of_tailPhOk (tailPhOk_ofPlaceOK h i)

/-- **`scc_rt_alloc`'s targets off the write abort's pcs** at the record's
labels of an output passing `placeOK`, from A7's `tailOffC` (its check at
`fenceLab`, `allocAbOk_fenceLab`). -/
theorem allocAbOk_ofPlaceOK : AllocG.allocAbOkR (RuntimeLayout.ofPlaceOK h i).lab = true :=
  allocAbOk_fenceLab ▸ StubW.allocAbOk_of_tailPhOk (tailPhOk_ofPlaceOK h i)

end Place

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Rt.printIn_noSite_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms printIn_noSite_ofPlaceOK

/-- info: 'Spike.Lib.A64.Rt.allocAbOk_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allocAbOk_ofPlaceOK

end Spike.Lib.A64.Rt
