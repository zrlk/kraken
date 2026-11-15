/-
**`main`'s segment at its callee frames at every reachable placement: the
statement** (x86-64; the twin of `Spike/Lib/LowerA64/G1MainStmtL.lean`):
`MainSeg2` (`Spike/Lib/LowerX64/G1MainStmt.lean`) with the current
placement `L`, `ls` (`lbl`, `lsize`) a parameter reachable from the
start's, at the world `W2AtL`/`MSAtL` (`Spike/Lib/LowerX64/RtMainXRL.lean`),
as `Spike/Lib/LowerX64/G1FnSpecL.lean` threads `L`, `ls` through
`G1FnSpec`'s statements. At the start's placement it is `MainSeg2`.

- `MainCx2L`: `MainCx2`'s facts with the limit row's word read in the
  memory side `MSAtL` at `L`, `ls`;
- `MainSeg2L`: `MainSeg2`'s conjuncts at every reachable `L`, `ls`;
- `MainCx2L.toNone`, `MainCx2.toL`: at the start's placement `MainCx2L` is
  `MainCx2`; `MainCx2.toLAt`: `MainCx2` gives `MainCx2L` at any placement
  (the limit word's row is the placement's own);
- `mainSeg2_ofL`: `MainSeg2` from `MainSeg2L` (the start's placement is
  reachable, `W2AtL`/`MSAtL` there are `W2At`/`MSAt`).
-/
import Spike.Lib.LowerX64.G1MainStmt
import Spike.Lib.LowerX64.G1FnSpecL

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (FStable AS)
open Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA tpOf WcG)
open Spike.Lib.X64.Rt (rS0 arOf)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)
open Spike.Lib.AllocReach (Reach)

section G1MainL

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
/-- `W2AtL` at `Closed2At`'s instance, placement `L`, `ls`. -/
local notation "W2L" J:max L:max ls:max => W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0) L ls

set_option hygiene false in
/-- `MSAtL` at `Closed2At`'s instance (the nodes' abort `ab2`), placement
`L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

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
/-- `main`'s code facts at the theorem's immediates. -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- The ghosts at `main`'s frame: the controls a frame run reaches from the
entry control `cP` at no frame. -/
local notation "GM" cP:max => fun c => FrameRunM p (cP, []) (c, [])

/-- **`main`'s context facts at a callee frame at a placement** `L`, `ls`
(`MainCx2`'s at the rebased region `R`, the limit row's word read in the
memory side `MSAtL` at `L`, `ls`). -/
structure MainCx2L (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat) (R : Region)
    (F : MachineData → Prop) (ra : BitVec 64) (tp : UInt64) : Prop where
  hR : R.OK
  hR8 : R.base.toNat % 8 = 0
  hal : R.base.toNat % 16 = 0
  hl : R.lo % 8 = 0
  hh : R.hi % 8 = 0
  hhi : 16 ≤ R.hi
  hFS : FStable R F
  hFO : ∀ m, F m → StackOff (rS0 (Ly)) R m
  hwn : ∀ m, F m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem
  hraP : PosOff OP (Ly).lab (Int64.ofBitVec ra)
  hraK : Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
    Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat
  htp : tp = TP0
  hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none
  room : NeedRoomX (OUT).place.need (Scc.Lower.Names.user "main") 256 (R.lo - 8)
  lim : ∀ m, F m → ∀ J : InvS,
    LimRoomX (OUT).place.need (Scc.Lower.Names.user "main") (((MSL J L ls) []).G ⟨limA tp, 8⟩) (R.base.toNat + 8)

set_option linter.unusedVariables false in
/-- **`main`'s segment at its callee frames at every reachable placement**
(`MainSeg2`'s at `L`, `ls`; see the module docstring): at `main`'s
compiled block `j`, every placement `L`, `ls` reachable from the start's,
every callee frame of `main`'s call in the prologue's region `R` with
`MainCx2L` at its rebased region `rbR R` (frame condition `F'`, the call's
ghost `g`) and entry control `cP` free of `ZBad`, some aborts' fragment
`Ab` with `CalleePre2R` at every entry invariant `JE` whose prologue edge
holds at `cP`, the constructs' segments in `rbR R` at the ghosts `GM cP`
and the trivial base context, and `Ab`'s segment, in `W2AtL`, `MSAtL` at
`L`, `ls`. -/
def MainSeg2L (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS) : Prop :=
  ∀ (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat),
    Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls →
  ∀ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d), d.name = "main" →
    ∀ (R : Region) (F' : MachineData → Prop) (g : WcG) (cP : Ctl), MainCx2L h L ls (rbR R) F' g.ra g.tp →
    FrOk2 cP [] →
    ∃ Ab : FragS isa,
      (∀ JE : AS → Ctl → Prop, ProEdge2 p L ls ((MSL J L ls) []) F' (FC) g.fp g.ra g.tp cP JE →
        CalleePre2R (W2L J L ls) (KT) p L ls (MSL J L ls) (fun _ _ _ _ _ _ _ _ => True) (FC)
          (rS0 (Ly)) R F' [] g.fp g.ra g.tp (GM cP) Ab JE cP) ∧
      CallC2R p L ls (FC).lcx (FC).fr (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        (rbR R) F' (W2L J L ls) (KT) (MSL J L ls) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab
        (RetLk d.retTy) ∧
      LaneC p L ls (FC).lcx (FC).fr (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        (rbR R) F' (W2L J L ls) (KT) (MSL J L ls) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab ∧
      NewBufC p L ls (FC).lcx (FC).fr (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        (rbR R) F' (W2L J L ls) (KT) (MSL J L ls) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab
        (RetLk d.retTy) ∧
      PrintCallC p L ls (FC).lcx (FC).fr (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        (rbR R) F' (W2L J L ls) (KT) (MSL J L ls) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab ∧
      CallC2H p L ls (FC).lcx (FC).fr (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        (rbR R) F' (W2L J L ls) (KT) (MSL J L ls) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab
        (RetLk d.retTy) ∧
      PrintCallCH p L ls (FC).lcx (FC).fr (CD g.ra) ((FC).Bl g.ra) (LY0).exe (LY0).endPc
        (rbR R) F' (W2L J L ls) (KT) (MSL J L ls) g.fp g.ra g.tp [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab ∧
      SegWS (W2L J L ls) (KT) p L (MSL J L ls) Ab (fun _ _ _ => False)

/-- `MainCx2` is `MainCx2L` at the start's placement. -/
theorem MainCx2.toL {R : Region} {F : MachineData → Prop} {ra : BitVec 64} {tp : UInt64}
    (H : MainCx2 h R F ra tp) : MainCx2L h (fun _ => none) (fun _ => 0) R F ra tp :=
  { H with }

/-- `MainCx2L` at the start's placement is `MainCx2`. -/
theorem MainCx2L.toNone {R : Region} {F : MachineData → Prop} {ra : BitVec 64} {tp : UInt64}
    (H : MainCx2L h (fun _ => none) (fun _ => 0) R F ra tp) : MainCx2 h R F ra tp :=
  { H with }

/-- **`MainCx2` gives `MainCx2L` at any placement** `L0`, `ls`: the limit
row's word `G` of the memory side is the placement's own (`msOfAX`'s rows
at either abort). -/
theorem MainCx2.toLAt {R : Region} {F : MachineData → Prop} {ra : BitVec 64} {tp : UInt64}
    (H : MainCx2 h R F ra tp) (L0 : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat) :
    MainCx2L h L0 ls R F ra tp :=
  { H with
    lim := fun m hm J => by
      have hl := H.lim m hm J
      revert hl
      dsimp only [MSAt, MSAtL]
      generalize ab2 p _ = ab
      cases ab <;> exact id }

/-- **`MainSeg2` from `MainSeg2L`** (at the start's placement, reachable by
`Reach.base`, where `W2AtL`, `MSAtL` are `W2At`, `MSAt`). -/
theorem mainSeg2_ofL {hp : Scc.Lower.Accepted2 p = true} {Dt : State → Prop} {J : InvS}
    (H : MainSeg2L h hp Dt J) : MainSeg2 h hp Dt J :=
  fun j d hd hn R F' g cP hc hE => H (fun _ => none) (fun _ => 0) .base j d hd hn R F' g cP (hc.toL h) hE

end G1MainL

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.MainCx2.toL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.MainCx2.toL

/-- info: 'Spike.Lib.LowerX64.MainCx2L.toNone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.MainCx2L.toNone

/-- info: 'Spike.Lib.LowerX64.MainCx2.toLAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.MainCx2.toLAt

/-- info: 'Spike.Lib.LowerX64.mainSeg2_ofL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainSeg2_ofL
