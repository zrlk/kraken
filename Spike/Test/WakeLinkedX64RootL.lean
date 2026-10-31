import Spike.Test.WakeLinkedX64RootU
import Spike.Lib.X64WakeLandU
import Spike.Lib.X64WakeStartH0B
import Spike.Lib.X64WakeImmsC0
import Spike.Lib.X64WakeHB1
import Spike.Lib.X64WakeRefOblW
import Spike.Lib.X64WakeHabLft
import Spike.Lib.X64WakeTiA

/-!
# `wake.w` on x86-64 at `Λe`: the root, every leaf closed

`wake_linkedXL` is the body of `WakeLinkedXGoal ie`, as
`WakeLinkedX64RootU.wake_linkedXU`, with the three per-entry rows closed:

- `hland`, `hland1` by `LandU.wake_finalX_land` (`LandU.hland_RU`,
  `LandU.hland1_RU` at `c0W`);
- `hst` by `StartH0B.hst0_W`, its placement and code facts at `i := ie`
  (`= X64.WakeImms.iW Λe`) by `X64WakeImmsC0.placedSE_c0WW` (`hpl0`),
  `cfacts_c0WW` (`hC0`) and `placedSE_startW` (`hplS`), `hctrD` by
  `WakeLinkedX64Le.hctrD_e`;
- the rows' `h1` clause `hB1` by `WakeHB1.hB1_W` (at `inv0 := ⊥`, the frame
  `F0 := RootU.wFU`), its `hobl` by `WakeRefOblW.refObl_WF` (which closes
  `RefLft` and `RefBlk` itself); `hF0` by `RootU.hF0_U`;
- `StartH0C.HabLft` at `Le` (shared by `hst0_W` and the landing rows) by
  `WakeHabLft.habLft_W`;
- `hB1_W`'s `hti` (the callee's `WakeH1GOf.TiG` per entry and box ghost) by
  `WakeTiA.tiA_of`;
- `hlo` (`Λe.code.lo = WakePh.lo`, both the linked `.text` base `0x401000`)
  by `WakeLinkedX64.hlo` (`decide +kernel`).

The premises left are the trust boundary `hP` and the budget `hB`, with `ls0`
and `frM` general (`WakeLinkedX64Root.wake_linkedX` fixes them).

Unlike AArch64 (`Spike/Test/WakeLinkedA64Root.lean`, `wake_linkedU`), `hst` enters through
`hst0_W`'s `Box ⊆ inv1W` clause `hB1` at `msBotX` (AArch64 the whole
`WakeRoot.H1R`); the same `hB1` serves the start and both landing rows.
-/

namespace Spike.Test.WakeLinkedX64RootL

open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib
open Spike.Test.WakeLinkedX64 Spike.Test.WakeLinkedX64Br
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64WakeParse (certAsm)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64.WakeHMid (BoxPure)
open Spike.Lib.X64 (AS)
open SccCertificate (asm sizes labelOffs outLit)

set_option hygiene false in
/-- The root's context at `c0W`. -/
local notation "CtxL" => fun E : Entry =>
  Spike.Lib.X64.WakePh.Land.CtxR Le Spike.Lib.X64.WakeC0.c0W
    (Spike.Lib.X64.WakePh.Land.refW certAsm placeWX_e ie ls0 E)

/-- The arena of the root. -/
local notation "arL" => Spike.Lib.X64.WakeOD.arW placeWX_e ie

/-- **wake.w's x86-64 statement at `Λe`**, `ls0` and `frM` general (see the module
doc). -/
theorem wake_linkedXL {arch : WeakMem.Arch} {B : Budget} (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame)
    /- the loader's check (the trust boundary; `#guard`-checked in `WakeLinkedX64`) -/
    (hP : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ outLit.prog outLit.secs = true)
    /- the budget: the caller's choice -/
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.X64.CorrectE 2 (wakeSX arch) { Λe with imms := ie } B ⟨asm, sizes, labelOffs⟩ := by
  have hlo : Λe.code.lo = Spike.Lib.X64.WakePh.lo := Spike.Test.WakeLinkedX64.hlo
  have hpa := (Spike.Lib.X64WakeParse.parsed_outLit hP).1
  have hwp := (Spike.Lib.X64WakeParse.parsed_outLit hP).2.1
  have hti := Spike.Lib.X64.WakeTiA.tiA_of certAsm placeWX_e ie (Spike.Lib.X64WakeHG.cTW placeWX_e ie) DtW CtxL ls0
    hpa hwp hlo hstat hA13_e hpin2 X64WakeFinalCAO.ctrZ_cert hctrD_e
  have hB1 := fun (E : Entry) (hE : E.Ok Le.Λ) =>
    Spike.Lib.X64.WakeHB1.hB1_W certAsm placeWX_e ie E (Spike.Lib.X64WakeHG.cTW placeWX_e ie) DtW ((CtxL) E)
      (ls0 E) (fun _ _ _ => False) hpa hwp hlo hstat hA13_e hpin2 X64WakeFinalCAO.ctrZ_cert (hti E hE)
      (Spike.Lib.X64.WakeRefOblW.refObl_WF certAsm placeWX_e ie E (Spike.Lib.X64WakeHG.cTW placeWX_e ie)
        ((CtxL) E) (ls0 E) hpa hwp hlo hA13_e)
  have hlft : Spike.Lib.X64.WakePh.StartH0C.HabLft Le :=
    Spike.Lib.X64.WakeHabLft.habLft_W placeWX_e ie hpa hwp hlo hA13_e
  rw [← wakeS_eq, ← Le_Λ]
  exact Spike.Lib.X64.WakePh.LandU.wake_finalX_land placeWX_e ie ls0 frM hP hB hlo hstat hA13_e hpin2 hinit2_W
    hsub1_W X64WakeFinalCAO.ctrZ_cert hnz_W (Spike.Lib.X64.WakeImmsC0.placedSE_c0WW placeWX_e) hlft
    (F0 := Spike.Lib.X64.WakePh.RootU.wFU placeWX_e ie) hB1 (Spike.Lib.X64.WakePh.RootU.hF0_U placeWX_e ie)
    (fun E hE => Spike.Lib.X64.WakePh.StartH0B.hst0_W placeWX_e ie ls0 frM E hE hpa hlo hstat hA13_e hpin2
      hctrD_e X64WakeFinalCAO.ctrZ_cert (Spike.Lib.X64.WakeImmsC0.placedSE_c0WW placeWX_e)
      (Spike.Lib.X64.WakeImmsC0.cfacts_c0WW placeWX_e) (Spike.Lib.X64.WakeImmsC0.placedSE_startW placeWX_e)
      hlft (hB1 E hE) (Spike.Lib.X64.WakePh.RootU.hF0_U placeWX_e ie))

end Spike.Test.WakeLinkedX64RootL

/-- info: 'Spike.Test.WakeLinkedX64RootL.wake_linkedXL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64RootL.wake_linkedXL
