/-
**Every compiled block of an `Accepted2` program is one segment inside
`W2`, at a generic base context** (x86-64; the twin of
`Spike/Lib/LowerA64/G1FnSpec.lean`): the statement of the program-wide
function segment `FnSpecC2` (`Spike/Lib/LowerX64/ProgC2.lean`) at the world
of the assembled theorem (`W2At`, `MSAt` at the placement check's record,
the theorem's immediates `imms2Me Λ p`, no label placed), for the placement
check's code facts `fnCode2OfPMe`, at the contexts with their stack records
(`CxOkS`) over one base context `CxG2` closed under plain calls.

The base context's region is the rebased one (`rbR`: its base the entry
`%rsp` less the saved `%rbp`'s cell), so the entry `%rsp` is
`R.base + 8` and the region's lowest offset below the entry is `R.lo - 8`;
the stack need table's rows (`NeedRoomX`, `LimRoomX`) are read there.

- `CxCore2`: a base context's facts at a compiled block `j`: the region,
  its frame condition and the stack (as `CxLB`; the allocations only for a
  block with a buffer allocation), the frames placed, the ghosts, the stack
  need table's room (slack `256`: the stack check's path and the deepest
  runtime routine, `rtMaxX`) and limit rows at the region's entry, the
  thread pointer the first TCB's;
- `AbG2`: the aborts of every such context (its abort node's states, its
  buffer allocations' heap abort exits, its output calls' abort states);
- `CxG2M`: `CxCore2` at the rebased region of the context's (`CxOkS`'s key
  region, its base the entry `%rsp`), its aborts' fragment containing
  `AbG2` (the shape of `main`'s context, at no frames);
- `CxG2`: `CxG2M` with some frame suspended;
- `FnSpecC2At`, `FnSpecC2Stmt`: every compiled block's `FnSpecC2` at
  `CxOkS … CxG2 Bot`, for any bottom keys `Bot`, at an output whose user
  code's direct branches pass `tgOkB` and a write tail holding at the
  output call's system call;
- `Room2OwnStmt`, `Room2CalleeStmt`, `Lim2CalleeStmt`, `LimOk2Stmt`,
  `LaneBuf2Stmt`, `Print2Stmt`: the steps' statements.
-/
import Spike.Lib.LowerX64.CxLBP
import Spike.Lib.LowerX64.Stk2
import Spike.Lib.LowerX64.Closed2At
import Spike.Lib.LowerX64.UserTgt
import Spike.Lib.LowerX64.CalleeRoom
import Spike.Lib.LowerX64.LimRoom
import Spike.Lib.LowerX64.LimOk0
import Spike.Lib.LowerX64.MainNeed
import Spike.Lib.LowerX64.PrintCallInstAI
import Spike.Lib.LowerX64.Start2W2

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (FStable AS)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA tpOf)
open Spike.Lib.X64.Flow.NewBuf (nbX)
open Spike.Lib.X64.Rt (rS0 arOf)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)
open Spike.Lib.AllocReach (IN)

section G1

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP
  (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => Spike.Lib.X64.Flow.Ret0.TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

/-- **The `j`th compiled block allocates a buffer** at a point of its
lowering walk. -/
def HasNewBuf2 (p : Prog) (j : Nat) : Prop :=
  ∃ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e)

/-- **A base context's facts at the `j`th compiled block** (`CxLB`'s,
without its aborts and its room below the frame, the allocations only at a
block allocating a buffer, `HasNewBuf2`), at the rebased region `R`, frame
condition `F`, frames `fs`, saved pair `fp`/`ra`, thread pointer `tp` and
ghosts `G0`; with the stack need table's room (`NeedRoomX`, at the
region's lowest offset below the entry `%rsp`, `R.lo - 8`) and limit
(`LimRoomX`, at the entry `%rsp`, `R.base + 8`, at the memories of `F`,
where the limit value is pinned) rows of the block, the region's base
16-aligned (the entry `%rsp` is `8` past a 16-aligned address), the thread
pointer the first TCB's and the TCB's limit word unmapped in `F`;
the suspended frames' environments small (`EnvSmall`, the overflow abort's
source side), some frame suspended at a block allocating a buffer (the heap
abort exit's frames; a block at no frames is `main`). The room's slack `256` is the stack
check's path (`48`) and the deepest runtime routine (`rtMaxX`, `208`):
`needOk1` does not count a call of a runtime routine in a row's need
(`Spike/Lib/LowerX64/StackBounds2.lean`). -/
structure CxCore2 (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS) (j : Nat) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) :
    Prop where
  hR : R.OK
  hR8 : R.base.toNat % 8 = 0
  hal : R.base.toNat % 16 = 0
  hl : R.lo % 8 = 0
  hh : R.hi % 8 = 0
  hhi : 16 ≤ R.hi
  hFS : FStable R F
  hFO : ∀ m, F m → StackOff (rS0 (Ly)) R m
  hrs : ∀ d (hd : (compiled2 p)[j]? = some d) r k, rsOf (FC j d hd).fr r = some k → R.Off k
  hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI (Ly).Λ (fun _ => none) s fs B
  hes : ∀ m, F m → ∀ f ∈ fs, EnvSmall f.env
  hfs : HasNewBuf2 p j → fs ≠ []
  hrd : ∀ w', ((MSS J) fs).rd w' → IsNum w'
  hwn : ∀ m, F m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem
  hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs
  hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c'
  hK : ((MSS J) fs).K = some Scc.Sem.X64.abi
  hAW : ∀ d (hd : (compiled2 p)[j]? = some d), HasNewBuf2 p j →
    AllocW2At p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p IsNum (Spike.Lib.X64.PhRec.GOf Ly M0)
        (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
        (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Spike.Lib.X64.WriteAb.Ab (Ly).lab) lbl lsize s c fs)
      (KT) (Ly).exe (Ly).endPc R F ((MSS J) fs) fp ra tp G0 (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy)
  room : ∀ d, (compiled2 p)[j]? = some d →
    NeedRoomX (OUT).place.need (Scc.Lower.Names.user d.name) 256 (R.lo - 8)
  lim : ∀ m, F m → ∀ d, (compiled2 p)[j]? = some d →
    LimRoomX (OUT).place.need (Scc.Lower.Names.user d.name) (((MSS J) []).G ⟨limA tp, 8⟩) (R.base.toNat + 8)
  htp : tp = TP0
  hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none

/-- **The aborts of every base context**: at a context with `CxCore2` at
the `j`th compiled block (a ghost `c0` in `G0`), the abort node's states
(`abortN2`), the buffer allocations' heap abort exits (`nbX … .abort` from
a call node placing its controls, `NbJcOf`) at its frames `fs`, and its
output calls' abort states (`printNAS`) at the output call's frame on
`fs`. -/
def AbG2 (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS) : FragS isa := fun s c fs' =>
  ∃ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (R : Region) (F : MachineData → Prop)
    (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop),
    CxCore2 h hp Dt J j R F fs fp ra tp G0 ∧
    ((fs' = fs ∧ ∃ c0, G0 c0 ∧ Spike.Lib.X64.At (Ly).exe (Ly).endPc R F
        (abortN2 (imms2Me Λ p) (TailAt2 p j) p (fun _ => none) (FC j d hd).fr
          (_root_.Executable.labels (Ly).exe).label fp ra c0) s c) ∨
     (fs' = fs ∧ ∃ (Jc : AS → Ctl → Prop) (pcR : Int64), NbJcOf (imms2Me Λ p) (fun _ => none) (FC j d hd).fr Jc ∧
        (∀ σ c', Jc σ c' → TailAt2 p j c'.term) ∧
        Spike.Lib.X64.At (Ly).exe (Ly).endPc R F (nbX ((MSS J) fs) (_root_.Executable.labels (Ly).exe).label
          (fun _ => none) R (FC j d hd).fr.size pcR Jc .abort) s c) ∨
     (∃ c0 x is a e c1, G0 c0 ∧ TailAt2 p j (.let_ x (.call "print" is a []) e) ∧
        fs' = Spike.Lib.LowerNode.printFrame x e c1 :: fs ∧
        Spike.Lib.X64.At (Ly).exe (Ly).endPc R F (printNAS (_root_.Executable.labels (Ly).exe).label (FC j d hd).fr
          (fun _ => none) (imms2Me Λ p) x e c1) s c))

/-- **A base context at any frames** at the `j`th compiled block and the
context's region `R` (its base the entry `%rsp`): `CxCore2` at the rebased
region `rbR R` (the block's, as `fnSpecC2_ofCxLB`'s `CxLB`), the aborts'
fragment `Ab` containing every base context's aborts (`AbG2`). The shape of
`main`'s context (at no frames). -/
def CxG2M (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS) (j : Nat) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab : FragS isa) : Prop :=
  CxCore2 h hp Dt J j (rbR R) F fs fp ra tp G0 ∧ ∀ s c fs', AbG2 h hp Dt J s c fs' → Ab s c fs'

/-- **The generic base context** at the `j`th compiled block: `CxG2M`, some
frame suspended (a called block's). -/
def CxG2 (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS) (j : Nat) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab : FragS isa) : Prop :=
  CxG2M h hp Dt J j R F fs fp ra tp G0 Ab ∧ fs ≠ []

/-- **Every compiled block's segment at one instance** (`FnSpecC2` at the
assembled theorem's world, the placement check's code facts at the
theorem's immediates, the contexts `CxOkS … (CxG2 …) Bot`). -/
def FnSpecC2At (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS)
    (Bot : StkKey → List TermRun.Frame → Prop) : Prop :=
  ∀ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d),
    FnSpecC2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J)
      (CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (fnCode2OfPMe hp h Λ) (CxG2 h hp Dt J) Bot j)
      (FC j d hd)

/-! ## The steps' statements -/

/-- **A compiled block's room covers its frame, its saved `%rbp` and the
slack** (the `Accepted2` twin of `ownRoom_of_placeOK`, the room read below
the entry `%rsp`). -/
def Room2OwnStmt (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (s : Nat) (lo : Int),
    NeedRoomX (OUT).place.need (Scc.Lower.Names.user d.name) s lo →
      lo ≤ -(((FC j d hd).fr.size : Int) + 8 + s)

/-- **A plain call's callee room** (the `Accepted2` twin of
`calleeRoom_of_placeOK`): at a plain call of `g` (a callee of the block's
lowering context) at a point of the `j`th compiled block's walk, the callee
is an earlier compiled block `dg` named `g`, and the caller's room at `lo`
below its entry `%rsp` leaves the callee's room at `lo` raised by the
caller's frame, its saved `%rbp` and the return address (the callee's entry
`%rsp` that far below the caller's). -/
def Room2CalleeStmt (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (x g : String) (a : At) (e : Expr) (s : Nat)
    (lo : Int),
    TailAt2 p j (.let_ x (.call g [] a []) e) → Spike.Lib.LowerCall.Callee (FC j d hd).lcx g →
    NeedRoomX (OUT).place.need (Scc.Lower.Names.user d.name) s lo →
    ∃ (j' : Nat) (dg : Decl) (_ : (compiled2 p)[j']? = some dg), j' < j ∧ dg.name = g ∧
      NeedRoomX (OUT).place.need (Scc.Lower.Names.user g) s (lo + ((FC j d hd).fr.size : Int) + 16)

/-- **A plain call's callee limit room** (the `Accepted2` twin of
`calleeLim_of_placeOK`): at the same call, the caller's limit room at its
entry `%rsp` `sp` gives the callee's at its entry `sp'`, below the caller's
frame, saved `%rbp` and the return address. -/
def Lim2CalleeStmt (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (x g : String) (a : At) (e : Expr)
    (G : Val → Prop) (sp sp' : Nat),
    TailAt2 p j (.let_ x (.call g [] a []) e) → Spike.Lib.LowerCall.Callee (FC j d hd).lcx g →
    sp' + (FC j d hd).fr.size + 16 = sp →
    LimRoomX (OUT).place.need (Scc.Lower.Names.user d.name) G sp →
    LimRoomX (OUT).place.need (Scc.Lower.Names.user g) G sp'

/-- **The prologue's limit facts inside `MSAt`** (the `W2` twin of
`limOk_callee_ofPlaceOK`): at any frames `fs`, a state whose `%fs` base is
the first TCB's, a frame condition leaving the TCB's limit word unmapped,
and every limit value at most the new frame's `%rsp`. -/
def LimOk2Stmt (_hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (J : InvS) (F : MachineData → Prop) (fs : List TermRun.Frame) (σ : AS) (fsz : Int),
    σ.regs.fsBase = TP0 →
    (∀ m, F m → Mem.loadInt m.dmem (limA (TP0)) 8 = none) →
    (∀ v, ((MSS J) []).G ⟨limA (TP0), 8⟩ v →
      (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fsz).toBitVec).toNat) →
    Spike.Lib.X64.Flow.Ret0.LimOk ((MSS J) fs) F
      (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fsz).toBitVec)

/-- **The lane stores and buffers at a base context** (`bodySpecC2_of`'s
`hcon`, its `LaneC` and `NewBufC` conjuncts in the rebased region, at
`CxG2M`). -/
def LaneBuf2Stmt (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (Dt : State → Prop) (J : InvS) (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab : FragS isa),
    CxG2M h hp Dt J j R F fs fp ra tp G0 Ab →
    Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat →
    LaneC p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc (rbR R) F (W2S J) (KT) (MSS J) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab ∧
    NewBufC p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc (rbR R) F (W2S J) (KT) (MSS J) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab (RetLk d.retTy)

/-- **The output calls at a base context** (`bodySpecC2_of`'s `hcon`, its
`PrintCallC` conjunct in the rebased region, at `CxG2M`), the write tail `Dt` holding at the
output call's system call. -/
def Print2Stmt (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (Dt : State → Prop),
    (∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F'
        (Spike.Lib.X64.PrintCall.pN (_root_.Executable.labels (Ly).exe).label Pc Qc ko σC .sys) s c' → Dt s) →
    ∀ (J : InvS) (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab : FragS isa),
    CxG2M h hp Dt J j R F fs fp ra tp G0 Ab →
    Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat →
    PrintCallC p (fun _ => none) (fun _ => 0) (FC j d hd).lcx (FC j d hd).fr (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc (rbR R) F (W2S J) (KT) (MSS J) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab

end G1

/-- **The program-wide function segment of an `Accepted2` program**
(the statement G1.1 proves): at every instance of `Closed2In` whose
output's user code passes the branch-target check `tgOkB` and whose write
tail `Dt` holds at the output call's system call, every invariant `J` and
bottom keys `Bot`, `FnSpecC2At`. -/
def FnSpecC2Stmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted2 p = true),
    CfgNeedOk pcfg = true →
    ∀ (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true),
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true →
    ∀ (Dt : State → Prop),
    (∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      Spike.Lib.X64.At (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe
        (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).endPc R' F'
        (Spike.Lib.X64.PrintCall.pN
          (_root_.Executable.labels (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)).exe).label
          Pc Qc ko σC .sys) s c' → Dt s) →
    ∀ (J : InvS) (Bot : StkKey → List TermRun.Frame → Prop), FnSpecC2At h hp Dt J Bot

end Spike.Lib.LowerX64
