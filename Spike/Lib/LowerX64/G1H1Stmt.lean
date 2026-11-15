/-
**The landings' segments for any `Accepted2` program with a setup block:
the statement** (x86-64; the twin of `Spike/Lib/LowerA64/G1H1Stmt.lean`):
`H1InW` (`Spike/Lib/LowerX64/Closed2AtW.lean`) at the landings `ElG`
(`Spike/Lib/LowerX64/G1AllocOpen.lean`) and the write tail `fun _ => True`,
at every instance with a setup block, from the two segments a landing needs
at its extended placement and that are not given at the empty placement:

- `CallLUStmt`: the constructs of the allocating block (`rodata`) at a
  landing context `CxOkH` with its bottom key `BotH`, at the extended
  placement `upd L l b`, `updN ls l n` of a reachable placement, at every
  frame invariant holding at the landings' starts: `CallC2`, `LaneC`,
  `NewBufC` and `PrintCallC` there (in the context's rebased region
  `rbR R`), with some aborts' fragment ending nowhere. After an allocation the block's frame holds a locative, so its
  callees run at the extended placement (the shape the callees' segments at
  a reachable placement give);
- `MainLUStmt`: `main`'s call after the setup block returns, at a reachable
  placement (`MainCallWSF` at `W2` there, `mainS0_segL`'s `hU`): the setup
  result may hold locatives placed by the allocations.

The landing contexts' aborts at a placement (`AbLU`) and their statement
(`AbLUStmt`) are stated here too; `Spike/Lib/LowerX64/G1AbLU.lean` proves
the latter.

- `CallLUStmt`, `MainLUStmt`: the two segment statements;
- `AbLU`, `AbLUStmt`: the landing contexts' aborts at a placement, ending
  nowhere at a reachable one;
- `H1SetupStmtL`: `H1InW` at `ElG` from them, at every instance with a
  setup block, the branch-target check and the header bound.
-/
import Spike.Lib.LowerX64.G1AllocOpen
import Spike.Lib.LowerX64.Closed2AtW
import Spike.Lib.LowerX64.UserTgt
import Spike.Lib.LowerX64.SetupCall2
import Spike.Lib.LowerX64.MainExitF
import Spike.Lib.LowerX64.RtMainXV
import Spike.Lib.Rt.X64MainSSF

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (CallerCells limA)
open Spike.Lib.X64.Rt (setupMC rS0 rtF swFSL)
open Spike.Lib.LowerNode (setupWords2 compiled2 imms2Me TailAt2)
open Spike.Lib.AllocReach (Reach IN)

section Stmt

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfPMe`'s code facts'). -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

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
/-- The setup code's record. -/
local notation "SC" => setupMC (setupWords2 p)

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`
(`mainS0_segL`'s). -/
local notation "FW" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- **The start's frame condition**: the runtime's words unloaded and no
heap or image word loaded (`Closed2AtW`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J`, at the write tail `fun _ => True`. -/
local notation "W2T" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.X64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2`. -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J)
    (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- A context's code at the saved return address (`fnCode2OfPMe`'s). -/
local notation "CD" ra:max =>
  CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra)

set_option hygiene false in
/-- The code facts' return address condition (`fnCode2OfPMe`'s `RaOk`). -/
local notation "RAOK" ra:max => Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
  Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat

set_option hygiene false in
/-- The `j`th block's code facts (`ElG`'s). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The extended placement's labels. -/
local notation "LU" => Spike.Lib.AllocReach.upd L l b

set_option hygiene false in
/-- The extended placement's sizes. -/
local notation "LN" => Spike.Lib.AllocReach.updN ls l n

/-- **The allocating block's plain calls at a landing's extended
placement**: at every invariant `J` holding at the starts of the landings
`ElG` (`H1InW.h1`'s hypothesis at the write tail `fun _ => True`), every
extension `upd L l b`, `updN ls l n` of a reachable placement by a fresh
label the arena hands out (`AllocLand`), and every landing context `CxOkH`
of the `j`th compiled block with its bottom key `BotH` (the landing's
records, none above the setup frame) whose return address has the phase
anchor's phase (`fnCode2OfPMe`'s `RaOk`), some aborts' fragment `AbC` with
the block's plain calls `CallC2`, lane stores `LaneC`, buffers `NewBufC`
and output calls `PrintCallC` at the extended placement on its whole walk,
in the context's rebased region `rbR R`, and `AbC` ending nowhere. -/
def CallLUStmt (hp : Scc.Lower.Accepted2 p = true) (E : Entry) : Prop :=
  ∀ (J : InvS), (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElG h hp) (fun _ => True) (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ (L : Lbl) (ls : Lsize) (l : WeakMem.AllocLabel) (b n : Nat),
    Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
    Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (R : Region) (F : MachineData → Prop)
      (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isa),
      CxOkH h hp j R F fs fp ra tp G0 Ab → BotH h ⟨j, R, F, fp, ra, tp, G0⟩ fs → RAOK ra →
      ∃ AbC : FragS isa,
        CallC2 p (LU) (LN) (FC).lcx (FC).fr (CD ra) ((FC).Bl ra) (LY0).exe (LY0).endPc (rbR R) F
          (W2T J (LU) (LN)) (KT) (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) AbC
          (RetLk d.retTy) ∧
        LaneC p (LU) (LN) (FC).lcx (FC).fr (CD ra) ((FC).Bl ra) (LY0).exe (LY0).endPc (rbR R) F
          (W2T J (LU) (LN)) (KT) (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) AbC ∧
        NewBufC p (LU) (LN) (FC).lcx (FC).fr (CD ra) ((FC).Bl ra) (LY0).exe (LY0).endPc (rbR R) F
          (W2T J (LU) (LN)) (KT) (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) AbC
          (RetLk d.retTy) ∧
        PrintCallC p (LU) (LN) (FC).lcx (FC).fr (CD ra) ((FC).Bl ra) (LY0).exe (LY0).endPc (rbR R) F
          (W2T J (LU) (LN)) (KT) (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) AbC ∧
        SegWS (W2T J (LU) (LN)) (KT) p (LU) (MSR J (LU) (LN)) AbC fun _ _ _ => False

/-- **`main`'s call after the setup block at a reachable placement**
(`mainS0_segL`'s `hU` at the write tail `fun _ => True`): at every
invariant `J`, reachable placement `L0`, `ls` and bounds `Bounds2`,
`MainCallWSF` inside `W2` at `L0`, `ls` from the setup result of type `ty`,
at the switch region's frame condition with `WordsNone`. -/
def MainLUStmt (ty : Ty) : Prop :=
  ∀ (J : InvS) (L0 : Lbl) (ls : Lsize), Reach (Ar) (fun _ => none) (fun _ => 0) L0 ls →
    ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
      Spike.Lib.X64.Rt.MainCallWSF (W2T J L0 ls) (KT) p L0 (MSR J L0 ls) (Ly).exe (Ly).endPc
        (RS (TOP)) (FW (TOP)) (SC).fn (SC).Z D2 (Int64.ofInt (fM : Int))
        (Spike.Lib.X64.Rt.SetupArgs (SPostC p L0 ty C0) (SC).sw (TP0).toBitVec)
        (fun c fs v => UPostRF p L0 c fs v ∧ MainCtlV (lay2 Λ p) L0 c fs v)
        ((Ly).lab (SC).sp1).toBitVec (TP0)

/-- **A landing context's aborts at a placement**: at some landing
context `CxOkH` of the `j`th compiled block, its abort node's states and
its buffer allocations' heap abort exits (`AbU2`, in the context's rebased
region `rbR R`) at the placement `L`, `ls` (the rows' memory side and the
labels there). -/
def AbLU (hp : Scc.Lower.Accepted2 p = true) (J : InvS) (L : Lbl) (ls : Lsize) : FragS isa := fun s c fs' =>
  ∃ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (R : Region) (F : MachineData → Prop)
    (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isa),
    CxOkH h hp j R F fs fp ra tp G0 Ab ∧ AbU2 p (MSR J L ls) L (FC) (rbR R) F fs fp ra G0 s c fs'

/-- **The landing contexts' aborts at a reachable placement end nowhere**
(the generalisation of `hello1_hAbQ` to the aborts at the placement and to
blocks with additions): at every invariant `J` and reachable placement `L`,
`ls`, `AbLU` is a segment to the empty fragment inside `W2` there. -/
def AbLUStmt (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (J : InvS) (L : Lbl) (ls : Lsize), Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
    SegWS (W2T J L ls) (KT) p L (MSR J L ls) (AbLU h hp J L ls) fun _ _ _ => False

end Stmt

/-- **The landings' segments with a setup block from the segments at the
extended placements** (`H1InW` at the landings `ElG` and the write tail
`fun _ => True`): at every instance of `Closed2InW` with a setup block, the
branch-target check `tgOkB` and the header bound `hobj`, from the
allocating block's plain calls (`CallLUStmt`) and `main`'s call
(`MainLUStmt`) at the reachable placements. -/
def H1SetupStmtL : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout)
    (hp : Scc.Lower.Accepted2 p = true) (ty : Ty), Scc.Lower.setupOf p = some ty →
    Scc.Lower.mainRetOk p = true → CfgNeedOk pcfg = true → Scc.Obj.nShift cfg.layout.obj < 22 →
    ∀ E : Entry, E.Ok (lay2 Λ p) →
    ∀ h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true →
    CallLUStmt h hp E → MainLUStmt h ty →
    H1InW h E (ElG h hp) (fun _ => True)

end Spike.Lib.LowerX64
