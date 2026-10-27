/-
**The setup frame's contexts' `CxLB` at a landing's extended placement**
(x86-64): a landings' context's `CxLB` (`Spike/Test/X64Hello1CxLBOfH.lean`'s
`cxLB_ofCxOkH`, at the start's placement) moved to a landing's extended
placement at any walk, for the landing's route `ResumeCx2T`
(`Spike/Lib/LowerX64/ResumeCx2T.lean`; why the full `ResumeCx2` at the
extended placement is unsatisfiable: `Spike/Lib/LowerX64/H1InLandWT.lean`).

- `cxLB_updT`: `CxLB` at the start's placement at a walk `T₁` moved to an
  extended placement at a walk `T₂`, the walk-reading fields given.
-/
import Spike.Test.X64Hello1CxLBOfH
import Spike.Lib.LowerX64.ResumeCxLB
import Spike.Lib.LowerX64.H1InLandW
import Spike.Lib.LowerX64.UserTgt
import Spike.Lib.LowerX64.HeapWOf
import Spike.Lib.LowerX64.LevelMono2
import Spike.Lib.AllocReachRoom
import Spike.Lib.LblRangeReach
import Spike.Lib.Rt.X64CtrZOfEmitted

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable At BlkW ND okBlk)
open Spike.Lib.X64Consumer (noRetBlk)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Rt (setupMC rS0 arOf swFSL)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2 compiled2 TailAt2 imms2Me addFreeT tailOf_addFree)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.X64.Flow.NewBuf (nbX)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.X64.PhRec.μ (Ly)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (`H1OpenXW`'s). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly))
    (Spike.Lib.X64.Rt.rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Spike.Lib.X64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (`H1OpenXW`'s). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- **`CxLB` at the record** at a placement `L0`, `ls0` (memory side
`MSR J L0 ls0`) for the `j`th compiled block's code facts at the return
address `ra` (`SetupCxLB`'s at `L0`, `ls0`). -/
local notation "CXL" J:max Dt:max L0:max ls0:max hd:max =>
  CxLB (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly))
    (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt (Ly).lab (KT) (Ly).exe
    (Ly).endPc (MSR J L0 ls0) L0 ls0 (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
    (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
    ((fnCode2OfPMe hp h Λ j d hd).Bl ra) (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP
  (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`
(`HSBVF`'s). -/
local notation "FS" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The ghosts at the setup frame. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The setup call's segment's premises at the callee's frame condition
`F'`, ghost `g` and frame `fr` (`SetupPreF`'s `PREF`). -/
local notation "PREF" F':max g:max fr:max => (RC).OK ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option hygiene false in
/-- The stack records' bottom keys at the setup frame (`SetupBot` at `FS`
with `WordsNone`; `X64Hello1SetupOpenOfF`'s). -/
local notation "SB" J:max v:max D1:max fS:max => fun k fs =>
  SetupBot p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
    ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec k fs

set_option hygiene false in
/-- **`CXL` at any walk predicate `T`**. -/
local notation "CXT" J:max Dt:max L0:max ls0:max hd:max T:max =>
  CxLB (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly))
    (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt (Ly).lab (KT) (Ly).exe
    (Ly).endPc (MSR J L0 ls0) L0 ls0 (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
    (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
    ((fnCode2OfPMe hp h Λ j d hd).Bl ra) (imms2Me Λ p) T (RetLk d.retTy)

set_option hygiene false in
/-- **`SetupCxLB` at any walk predicate `T`** (the start's placement). -/
local notation "SXT" J:max Dt:max hd:max T:max =>
  CxLB (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (Spike.Lib.X64.PhRec.GOf Ly M0)
    (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
    (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ly).lab (KT) (Ly).exe (Ly).endPc (MSS J)
    (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
    (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
    ((fnCode2OfPMe hp h Λ j d hd).Bl ra) (imms2Me Λ p) T (RetLk d.retTy)

/-! ## The placement transport at any walk predicate -/

/-- **`CxLB` at the start's placement moved to an extended placement**, at
any walk predicates `T₁`, `T₂` (a field copy): at a reachable
placement `L`, `ls` with a fresh label `l` the arena hands out at `b` with
`n` words, a `CxLB` at no label at `T₁` is one at `upd L l b`, `updN ls l n`
at `T₂`, given the fields reading the walk or the extended placement's
allocations at `T₂` (`hAW`, `hAb`): the frames stay placed at more labels
(`FramesPlacedInI.mono_lbl`); the labels' room, range and heap words at the
reachable extended placement (`Reach.lblRoom`, `lblRange_upd`,
`heapW_ofReach`); the rest the given `CxLB`'s. -/
theorem cxLB_updT (hp : Scc.Lower.Accepted2 p = true) {Dt : State → Prop} (J : InvS) {T₁ T₂ : Expr → Prop}
    {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat} (hL : Reach (Ar) (fun _ => none) (fun _ => 0) L ls)
    (hl : L l = none) (hAL : Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab' : FragS isa}
    (H : (SXT J Dt hd T₁) R F fs fp ra tp G0 Ab')
    (hAW : AllocW2At p (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)
      (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
      (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl ra)
      (fun lbl lsize s c => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly))
        (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
        (Ab (Ly).lab) lbl lsize s c fs)
      (KT) (Ly).exe (Ly).endPc R F
      ((MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) fs) fp ra tp G0 (imms2Me Λ p)
      T₂ (RetLk d.retTy))
    (hAb : ∀ (Jc : Spike.Lib.X64.AS → Ctl → Prop) (pcR : Int64) s c,
      NbJcOf (imms2Me Λ p) (Spike.Lib.AllocReach.upd L l b) (fnCode2OfPMe hp h Λ j d hd).fr Jc →
      (∀ σ c', Jc σ c' → T₂ c'.term) →
      At (Ly).exe (Ly).endPc R F
        (nbX ((MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) fs)
          (_root_.Executable.labels (Ly).exe).label (Spike.Lib.AllocReach.upd L l b) R
          (fnCode2OfPMe hp h Λ j d hd).fr.size pcR Jc .abort) s c → Ab' s c fs) :
    (CXT J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n) hd T₂) R F fs fp ra tp G0 Ab' := by
  have hR' := hL.step hl hAL
  have hsub := Spike.Lib.X64.Rt.arOf_sub h
  exact {
    hR := H.hR
    hR8 := H.hR8
    hl := H.hl
    hh := H.hh
    hlo := H.hlo
    hhi := H.hhi
    hFS := H.hFS
    hFO := H.hFO
    hrs := H.hrs
    hfp := fun s hs => (H.hfp s hs).imp fun _ hB =>
      FramesPlacedInI.mono_lbl (fun _ _ h0 => by cases h0) hB
    hrd := by
      intro w
      generalize ab2 p _ = ab
      cases ab <;> exact fun hw => hw
    hroom := hR'.lblRoom Spike.Lib.AllocReach.lblRoom_none hsub (Scc.Cert.PlaceOK.X64.below32_of_placeOKAt h)
    hrg := Spike.Lib.lblRange_upd hsub (fun _ => rfl) hL hAL
    hwn := H.hwn
    hHW := heapW_ofReach h (Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h) H.hwn (fun _ => rfl) hR'
    hG0F := H.hG0F
    hG0 := H.hG0
    hK := msOfAX_K_abi
    hAW := hAW
    hAb := hAb }

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.cxLB_updT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cxLB_updT

end Spike.Lib.LowerX64
