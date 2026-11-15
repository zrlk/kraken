/-
**`main`'s segment at its callee frame, for any `Accepted2` program: the
statement** (AArch64): `MainSeg2`, the construct premise `hpre` of
`mainCallWSF_ofPlaceOKHMVCR` (`Spike/Lib/LowerA64/HeldPostAV.lean`) at
`main`'s compiled block, at any callee frame of `main`'s call with the
context facts `MainCx2`, at the assembled theorem's world (`W2At`, `MSAt`,
the take's outside moves) and the trivial base context. Both start paths
consume it: the setup call's (`main` called by `scc_rt_main` after the
setup block, the region below the switch region's top and `Z`) and the bare
start's (`main` called directly).

`main` runs at no suspended frames (`[]`), so it is not a base context
`CxCore2` (`Spike/Lib/LowerA64/G1FnSpec.lean`, which asks `fs ≠ []`):
`MainCx2` is `CxCore2`'s facts at the frames `[]` without the frames'
(placement, environments, ghosts' `FrOk2`, which the ghosts `GM cP` give)
and without the allocations (`newBuf` is the setup block's only).

- `MainCx2`: `main`'s context facts at a callee frame (region, frame
  condition, return address, thread pointer, rows);
- `MainSeg2`: at every such frame and entry control free of `ZBad`, some
  aborts' fragment `Ab` with `CalleePre2R`, the constructs' segments
  (`CallC2R`, `LaneC`, `NewBufC`, `PrintCallC`, `CallC2H`, `PrintCallCH`)
  and `Ab`'s segment.
-/
import Spike.Lib.LowerA64.G1FnSpec
import Spike.Lib.LowerA64.HeldPostAV

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff limA pinA WcG)
open Spike.Lib.A64.Rt (rS0 arOf)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)

section G1Main

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => Spike.Lib.A64.Flow.Ret0.TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- `main`'s code facts at the theorem's immediates. -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- The ghosts at `main`'s frame: the controls a frame run reaches from the
entry control `cP` at no frame. -/
local notation "GM" cP:max => fun c => FrameRunM p (cP, []) (c, [])

/-- **`main`'s context facts at a callee frame** of `main`'s call, at the
region `R`, frame condition `F`, return address `ra` and thread pointer
`tp` (`CxCore2`'s at the frames `[]`, see the module docstring): the
region's alignment and bounds, `F` stable and off the first stack's other
words, the private memory loading no runtime word, the return address off
the write abort, the thread pointer the first TCB's with its limit word
unmapped, the stack need table's room (slack `256`) and limit rows of
`main`, the return address at the phase of the anchor after the bare
start's `bl main` (`bareMC.e0 + 4`, the code facts' return address
condition). -/
structure MainCx2 (R : Region) (F : MachineData → Prop) (ra : BitVec 64) (tp : UInt64) : Prop where
  hR : R.OK
  hal : R.base.toNat % 16 = 0
  hl : R.lo % 8 = 0
  hh : R.hi % 8 = 0
  hhi : 0 ≤ R.hi
  hFS : FStable R F
  hFO : ∀ m, F m → StackOff (rS0 (Ly)) R m
  hwn : ∀ m, F m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem
  hraP : PosOff OP (Ly).lab (Int64.ofBitVec ra)
  hraK : Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
    Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat
  htp : tp = TP0
  hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none
  room : NeedRoomA (OUT).place.need (Scc.Lower.Names.user "main") 256 R.lo
  lim : ∀ m, F m → ∀ J : InvS,
    LimRoomA (OUT).place.need (Scc.Lower.Names.user "main") (((MSS J) []).G ⟨limA tp, 8⟩) R.base.toNat

set_option linter.unusedVariables false in
/-- **`main`'s segment at its callee frames** (G1.4's statement; see the
module docstring): at `main`'s compiled block `j`, every callee frame of
`main`'s call with `MainCx2` (frame condition `F'`, the call's ghost `g`)
and entry control `cP` free of `ZBad`, some aborts' fragment `Ab` with
`mainCallWSF_ofPlaceOKHMVCR`'s `hpre` conjuncts (the plain call's
segment `CallC2R`: at the frames `[]` only for non-`ret` bodies) at the ghosts `GM cP` and
the trivial base context. -/
def MainSeg2 (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS) : Prop :=
  ∀ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d), d.name = "main" →
    ∀ (R : Region) (F' : MachineData → Prop) (g : WcG) (cP : Ctl), MainCx2 h R F' g.ra g.tp → FrOk2 cP [] →
    ∃ Ab : FragS isaLSE2,
      CalleePre2R (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J) (fun _ _ _ _ _ _ _ _ => True) (FC)
        (rS0 (Ly)) R F' [] g.fp g.ra g.tp (GM cP) Ab cP ∧
      CallC2R p (fun _ => none) (fun _ => 0) (FC).lcx (FC).cx (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        R F' (W2S J) (KT) (MSS J) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab (RetLk d.retTy) ∧
      LaneC p (fun _ => none) (fun _ => 0) (FC).lcx (FC).cx (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        R F' (W2S J) (KT) (MSS J) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab ∧
      NewBufC p (fun _ => none) (fun _ => 0) (FC).lcx (FC).cx (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        R F' (W2S J) (KT) (MSS J) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab (RetLk d.retTy) ∧
      PrintCallC p (fun _ => none) (fun _ => 0) (FC).lcx (FC).cx (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        R F' (W2S J) (KT) (MSS J) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab ∧
      CallC2H p (fun _ => none) (fun _ => 0) (FC).lcx (FC).cx (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        R F' (W2S J) (KT) (MSS J) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab (RetLk d.retTy) ∧
      PrintCallCH p (fun _ => none) (fun _ => 0) (FC).lcx (FC).cx (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        R F' (W2S J) (KT) (MSS J) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab ∧
      SegWS (W2S J) (KT) p (fun _ => none) (MSS J) Ab (fun _ _ _ => False)

end G1Main

end Spike.Lib.LowerA64
