/-
**`scc_rt_main`'s return point is off the write abort** (x86-64; the twin
of `Spike/Lib/LowerA64/MainRetPos.lean`): the label right after `call fn`
(`sp1` after a setup block, `sp0` without) heads the `exit_group` tail, and
it is `scc_rt_main`'s, none of `abLabs`. So it is a `PosOff` position: the
`ra` of `blkW_abSt_posR` / `blkW_abSt_subCdLR` at `main`'s return block.

- `posOff_mainRetS`, `mainRetS_eq`: after a setup block (`mainSIn`), the
  return point `sp1` and its address after the marshalling block;
- `posOff_mainRetU`, `mainRetU_eq`: without one (`mainUIn`, `bareMC`).
-/
import Spike.Lib.LowerX64.RtStartXOf
import Spike.Lib.Rt.X64MainS

namespace Spike.Lib.LowerX64

open Spike.Lib.X64.Flow (exitIn xExit)
open Spike.Lib.X64.Rt (SetupCode setupMC mainSIn marshalSz MainCode mainUIn bareMC)
open Scc.Cert.Rt.X64 (blockAtB labelGapB Lays label_labelGapB)

/-- **After a setup block, `scc_rt_main`'s return point `sp1` is off the
write abort.** -/
theorem posOff_mainRetS {cells : List (Directive × Nat)} {lab : Label → Int64} {sw : Nat}
    (hin : mainSIn cells (setupMC sw) = true) : PosOff cells lab (lab (setupMC sw).sp1) := by
  simp only [mainSIn, exitIn, Bool.and_eq_true] at hin
  have h := posOff_of_blockAtB (lab := lab) hin.2.1 (by simp only [setupMC]; decide) (by simp [xExit])
  rwa [Spike.Lib.X64.Flow.ofNat_zero'] at h

/-- **`sp1` is the return address of `call fn`**: right after the
marshalling block at `sp0`. -/
theorem mainRetS_eq {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) {sc : SetupCode}
    (hin : mainSIn cells sc = true) :
    (_root_.Executable.labels exe).label sc.sp1 =
      (_root_.Executable.labels exe).label sc.sp0 + Int64.ofNat (marshalSz sc.sw) := by
  simp only [mainSIn, Bool.and_eq_true] at hin
  exact label_labelGapB hp hin.1.2

/-- **Without a setup block, `scc_rt_main`'s return point `sp0` is off the
write abort.** -/
theorem posOff_mainRetU {cells : List (Directive × Nat)} {lab : Label → Int64}
    (hin : mainUIn cells bareMC = true) : PosOff cells lab (lab bareMC.sp0) := by
  simp only [mainUIn, exitIn, Bool.and_eq_true] at hin
  have h := posOff_of_blockAtB (lab := lab) hin.2.1 (by decide) (by simp [xExit])
  rwa [Spike.Lib.X64.Flow.ofNat_zero'] at h

/-- **`sp0` is the return address of `call fn`** at the body's entry. -/
theorem mainRetU_eq {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) {mc : MainCode}
    (hin : mainUIn cells mc = true) :
    (_root_.Executable.labels exe).label mc.sp0 = (_root_.Executable.labels exe).label mc.e0 + Int64.ofNat 5 := by
  simp only [mainUIn, Bool.and_eq_true] at hin
  exact label_labelGapB hp hin.1.2

/-- info: 'Spike.Lib.LowerX64.posOff_mainRetS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms posOff_mainRetS

/-- info: 'Spike.Lib.LowerX64.posOff_mainRetU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms posOff_mainRetU

end Spike.Lib.LowerX64
