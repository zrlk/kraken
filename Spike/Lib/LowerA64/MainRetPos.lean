/-
**`scc_rt_main`'s return point is off the write abort** (AArch64; the twin
of `Spike/Lib/LowerX64/MainRetPos.lean`): the label right after `bl fn`
(`sp1` after a setup block, `sp0` without) heads the `exit_group` tail, and
it is `scc_rt_main`'s (function index 1), none of `abLabs`. So it is a
`PosOff` position: the `ra` of `blkW_abSt_posR` / `blkW_abSt_subCdLR` at
`main`'s return block.

- `posOff_mainRetS`, `mainRetS_eq`: after a setup block (`mainSIn`), the
  return point `sp1` and its address after the marshalling block;
- `posOff_mainRetU`, `mainRetU_eq`: without one (`mainUIn`, `bareMC`).
-/
import Spike.Lib.LowerA64.UserAb
import Spike.Lib.Rt.A64MainS

namespace Spike.Lib.LowerA64

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (SetupCode setupMC mainSIn MainCode mainUIn bareMC)
open Spike.Lib.A64.AllocG (abLabs)
open Scc.Cert.Rt.A64 (blockAt labelGap Lays label_labelGap)

/-- **After a setup block, `scc_rt_main`'s return point `sp1` is off the
write abort.** -/
theorem posOff_mainRetS {prog : List Directive} {lab : Label → Int64} {sw : Nat}
    (hin : mainSIn prog (setupMC sw) = true) : PosOff prog lab (lab (setupMC sw).sp1) := by
  simp only [mainSIn, exitIn, Bool.and_eq_true] at hin
  have h := posOff_of_blockAt (lab := lab) hin.2.1 (by simp only [setupMC]; decide) (i := 0)
    (by simp [exitTail])
  rwa [Nat.add_zero, ofNat4_zero] at h

/-- **`sp1` is the return address of `bl fn`**: right after the marshalling
block of `2 * sw + 2` instructions at `sp0`. -/
theorem mainRetS_eq {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) {sc : SetupCode} (hin : mainSIn prog sc = true) :
    (_root_.Executable.labels exe).label sc.sp1 =
      (_root_.Executable.labels exe).label sc.sp0 + Int64.ofNat (4 * (2 * sc.sw + 2)) := by
  simp only [mainSIn, Bool.and_eq_true] at hin
  exact label_labelGap hp hin.1.2

/-- **Without a setup block, `scc_rt_main`'s return point `sp0` is off the
write abort.** -/
theorem posOff_mainRetU {prog : List Directive} {lab : Label → Int64} (hin : mainUIn prog bareMC = true) :
    PosOff prog lab (lab bareMC.sp0) := by
  simp only [mainUIn, exitIn, Bool.and_eq_true] at hin
  have h := posOff_of_blockAt (lab := lab) hin.2.1 (by decide) (i := 0) (by simp [exitTail])
  rwa [Nat.add_zero, ofNat4_zero] at h

/-- **`sp0` is the return address of `bl fn`** at the body's entry. -/
theorem mainRetU_eq {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) {mc : MainCode} (hin : mainUIn prog mc = true) :
    (_root_.Executable.labels exe).label mc.sp0 =
      (_root_.Executable.labels exe).label mc.e0 + Int64.ofNat (4 * 1) := by
  simp only [mainUIn, Bool.and_eq_true] at hin
  exact label_labelGap hp hin.1.2

/-- info: 'Spike.Lib.LowerA64.posOff_mainRetS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms posOff_mainRetS

/-- info: 'Spike.Lib.LowerA64.posOff_mainRetU' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms posOff_mainRetU

end Spike.Lib.LowerA64
