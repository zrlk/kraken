/-
**The landings' segments for any `Accepted2` program with a setup block:
the statement** (AArch64): `H1InAW` (`Spike/Lib/LowerA64/Closed2AtWA.lean`)
at the landings `ElH` (`Spike/Test/A64Hello1CxOkH.lean`) and the write tail
`fun _ => True`, at every instance with a setup block, from the two
segments a landing needs at its extended placement and that are not given
at the empty placement:

- `CallLUStmt`: the plain calls of the allocating block (`rodata`) at a
  landing context `CxOkH`, at the extended placement `upd L l b`,
  `updN ls l n` of a reachable placement: `CallC2` there, with some aborts'
  fragment ending nowhere. After an allocation the block's frame holds a
  locative, so its callees run at the extended placement (the shape the
  callees' segments at a reachable placement give);
- `MainLUStmt`: `main`'s call after the setup block returns, at a reachable
  placement (`MainCallWSF` at `W2` there, `exitStk_ofBotHRL`'s `hU`): the
  setup result may hold locatives placed by the allocations.

- `CallLUStmt`, `MainLUStmt`: the two segment statements;
- `H1SetupStmtL`: `H1InAW` at `ElH` from them, at every instance with a
  setup block, the branch-target check and the header bound.
-/
import Spike.Test.A64Hello1BotRes
import Spike.Lib.LowerA64.Closed2AtWA
import Spike.Lib.LowerA64.UserTgt

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 swFSL)
open Spike.Lib.LowerNode (setupWords2 compiled2 imms2Me TailAt2)
open Spike.Lib.AllocReach (Reach IN)

section Stmt

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s code facts'). -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB's address. -/
local notation "X0" => pinA (Ly).lab + 0#64 + 8#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (X0)

set_option hygiene false in
/-- The switch region's frame condition at the private memory's `WordsNone`, below the top `v`. -/
local notation "FS" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J`, at the write tail `fun _ => True`. -/
local notation "W2T" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2`. -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J)
    (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- A context's code at the saved return address (`fnCode2OfPMe`'s). -/
local notation "CD" ra:max =>
  CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra)

set_option hygiene false in
/-- The `j`th block's code facts (`ElH`'s). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The extended placement's labels. -/
local notation "LU" => Spike.Lib.AllocReach.upd L l b

set_option hygiene false in
/-- The extended placement's sizes. -/
local notation "LN" => Spike.Lib.AllocReach.updN ls l n

set_option hygiene false in
/-- **The start's frame condition**: the runtime's words unloaded and no
heap or image word loaded (`Closed2AtWA`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
  Spike.Lib.A64.Rt.rtF (Ly) m

/-- **The allocating block's plain calls at a landing's extended
placement**: at every invariant `J` holding at the starts of the landings
`ElH` (`H1InAW.h1`'s hypothesis at the write tail `fun _ => True`), every
extension `upd L l b`, `updN ls l n` of a reachable placement by a fresh
label the arena hands out (`AllocLand`), and every landing context `CxOkH`
of the `j`th compiled block with its bottom key `BotH` (the landing's
records, none above the setup frame) whose return address has the phase
anchor's phase (`fnCode2OfPMe`'s `RaOk`), some aborts' fragment `AbC` with
the block's plain calls `CallC2`, lane stores `LaneC`, buffers `NewBufC`
and output calls `PrintCallC` at the extended placement on its whole walk
and `AbC` ending nowhere. -/
def CallLUStmt (hp : Scc.Lower.Accepted2 p = true) (E : Entry) : Prop :=
  ∀ (J : InvS), (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h E (WNF) (ElH h hp) (fun _ => True) (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ (L : Lbl) (ls : Lsize) (l : WeakMem.AllocLabel) (b n : Nat),
    Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
    Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (R : Region) (F : MachineData → Prop)
      (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
      CxOkH h hp j R F fs fp ra tp G0 Ab → BotH h ⟨j, R, F, fp, ra, tp, G0⟩ fs →
      Spike.Lib.A64.PhRec.ph (LY0) (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.A64.PhRec.ph (LY0)
          (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat →
      ∃ AbC : FragS isaLSE2,
        CallC2 p (LU) (LN) (FC).lcx (FC).cx (CD ra) ((FC).Bl ra) (Ly).exe (Ly).endPc R F (W2T J (LU) (LN)) (KT)
          (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) AbC (RetLk d.retTy) ∧
        LaneC p (LU) (LN) (FC).lcx (FC).cx (CD ra) ((FC).Bl ra) (Ly).exe (Ly).endPc R F (W2T J (LU) (LN)) (KT)
          (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) AbC ∧
        NewBufC p (LU) (LN) (FC).lcx (FC).cx (CD ra) ((FC).Bl ra) (Ly).exe (Ly).endPc R F (W2T J (LU) (LN)) (KT)
          (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) AbC (RetLk d.retTy) ∧
        PrintCallC p (LU) (LN) (FC).lcx (FC).cx (CD ra) ((FC).Bl ra) (Ly).exe (Ly).endPc R F (W2T J (LU) (LN))
          (KT) (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) AbC ∧
        SegWS (W2T J (LU) (LN)) (KT) p (LU) (MSR J (LU) (LN)) AbC fun _ _ _ => False

/-- **`main`'s call after the setup block at a reachable placement**
(`exitStk_ofBotHRL`'s `hU` at the write tail `fun _ => True`): at every
invariant `J`, reachable placement `L0`, `ls` and bounds `Bounds2A`,
`MainCallWSF` inside `W2` at `L0`, `ls` from the setup result of type `ty`. -/
def MainLUStmt (ty : Ty) : Prop :=
  ∀ (J : InvS) (L0 : Lbl) (ls : Lsize), Reach (Ar) (fun _ => none) (fun _ => 0) L0 ls →
    ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat), Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
      Spike.Lib.A64.Rt.MainCallWSF (W2T J L0 ls) (KT) p L0 (MSR J L0 ls) (Ly).exe (Ly).endPc
        (swR (TOP) (-L) 0) (FS (TOP)) (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2
        (Int64.ofInt (fM : Int)) (Spike.Lib.A64.Rt.SetupArgs (SPostC p L0 ty C0) (setupMC (setupWords2 p)).sw (X0))
        (fun c fs v => UPostRF p L0 c fs v ∧ MainCtlV (lay2 Λ p) L0 c fs v)
        ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec (TP0)

/-- **A landing context's aborts at a placement**: at some landing
context `CxOkH` of the `j`th compiled block, its abort node's states and
its buffer allocations' heap abort exits (`AbU2`) at the placement `L`,
`ls` (the rows' memory side and the labels there). -/
def AbLU (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (L : Lbl) (ls : Lsize) : FragS isaLSE2 := fun s c fs' =>
  ∃ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (R : Region) (F : MachineData → Prop)
    (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
    CxOkH h hp j R F fs fp ra tp G0 Ab ∧ AbU2 p (MSR J L ls) L (FC) R F fs fp ra G0 s c fs'

/-- **The landing contexts' aborts at a reachable placement end nowhere**
(the generalisation of `cxOkH_hAbQA` to the aborts at the placement and to
blocks with additions): at every invariant `J` and reachable placement `L`,
`ls`, `AbLU` is a segment to the empty fragment inside `W2` there. -/
def AbLUStmt (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (J : InvS) (L : Lbl) (ls : Lsize), Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
    SegWS (W2T J L ls) (KT) p L (MSR J L ls) (AbLU h hp J L ls) fun _ _ _ => False

end Stmt

/-- **The landings' segments with a setup block from the segments at the
extended placements** (`H1InAW` at the landings `ElH` and the write tail
`fun _ => True`): at every instance of `Closed2InAW` with a setup block, the
branch-target check `tgOkB` and the header bound `hobj`, from the
allocating block's plain calls (`CallLUStmt`) and `main`'s call
(`MainLUStmt`) at the reachable placements. -/
def H1SetupStmtL : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (Λ : Scc.Sem.Layout)
    (hp : Scc.Lower.Accepted2 p = true) (ty : Ty), Scc.Lower.setupOf p = some ty →
    Scc.Lower.mainRetOk p = true → CfgNeedOkA pcfg = true → Scc.Obj.nShift cfg.layout.obj < 22 →
    ∀ E : Entry, E.Ok (lay2 Λ p) →
    ∀ h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true,
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true →
    CallLUStmt h hp E → MainLUStmt h ty →
    H1InAW h E (ElH h hp) (fun _ => True)

end Spike.Lib.LowerA64
