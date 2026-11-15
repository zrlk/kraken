/-
**Every compiled block's segment at a reachable placement** (AArch64): the
statements of `Spike/Lib/LowerA64/G1FnSpec.lean` with the current placement
`L`, `ls` (`lbl`, `lsize`) a parameter, reachable by allocations from the
start's (no label placed, `ls0 = fun _ => 0`; `Reach` at the output's arena
`arOf`), at the world `W2AtL`/`MSAtL` (`Spike/Lib/LowerA64/RtMainXRL.lean`)
in place of `W2At`/`MSAt`.

Each definition threads `L`, `ls` through its namesake's, field for field:
the frames placed at `L`, the reads, kernel and limit rows at `MSAtL … L
ls`, the allocations' `AllocW2At` at `L`, `ls` inside `W2` at the
allocation's own placement, the aborts' nodes at `L`; `CxCore2L` adds the
placement's `Reach`. At the start's placement each is its namesake
(`CxCore2.toL`, `CxCore2L.toNone`, `abG2_toL`, `CxG2ML.toNone`).

- `CxCore2L`, `AbG2L`, `CxG2ML`, `CxG2L`, `FnSpecC2AtL`;
- `LaneBuf2StmtL`, `Print2StmtL`: the lane stores and buffers, the output
  calls, at `CxG2ML`.
-/
import Spike.Lib.LowerA64.G1FnSpec
import Spike.Lib.LowerA64.RtMainXRL

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.A64.Flow.NewBuf (nbX)
open Spike.Lib.A64.Rt (rS0 arOf)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)
open Spike.Lib.AllocReach (IN Reach)

section G1L

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
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- `W2AtL` at `Closed2AtA`'s instance and the placement `L`, `ls`. -/
local notation "W2L" J:max L:max ls:max => W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0) L ls

set_option hygiene false in
/-- `MSAtL` at `Closed2AtA`'s instance (the nodes' abort `ab2`) and the
placement `L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => Spike.Lib.A64.Flow.Ret0.TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

/-- **A base context's facts at the `j`th compiled block and a reachable
placement** `L`, `ls`: `CxCore2`'s, the placement reachable from the
start's (`hre`), the frames placed at `L`, the memory side `MSAtL … L ls`,
the allocations' `AllocW2At` at `L`, `ls`. -/
structure CxCore2L (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS)
    (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat) (j : Nat) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) :
    Prop where
  hre : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls
  hR : R.OK
  hal : R.base.toNat % 16 = 0
  hl : R.lo % 8 = 0
  hh : R.hi % 8 = 0
  hhi : 0 ≤ R.hi
  hFS : FStable R F
  hFO : ∀ m, F m → StackOff (rS0 (Ly)) R m
  hrs : ∀ d (hd : (compiled2 p)[j]? = some d) r k, rsOf (FC j d hd).cx r = some k → R.Off k
  hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI (Ly).Λ L s fs B
  hes : ∀ m, F m → ∀ f ∈ fs, EnvSmall f.env
  hfs : HasNewBuf2 p j → fs ≠ []
  hrd : ∀ w', ((MSL J L ls) fs).rd w' → IsNum w'
  hwn : ∀ m, F m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem
  hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs
  hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c'
  hK : ((MSL J L ls) fs).K = some Scc.Sem.A64.abi
  hAW : ∀ d (hd : (compiled2 p)[j]? = some d), HasNewBuf2 p j →
    AllocW2At p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p IsNum (Spike.Lib.A64.PhRec.GOf Ly M0)
        (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
        (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Spike.Lib.A64.WriteAb.Ab (Ly).lab) lbl lsize s c fs)
      (KT) (Ly).exe (Ly).endPc R F ((MSL J L ls) fs) fp ra tp G0 (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy)
  room : ∀ d, (compiled2 p)[j]? = some d → NeedRoomA (OUT).place.need (Scc.Lower.Names.user d.name) 256 R.lo
  lim : ∀ m, F m → ∀ d, (compiled2 p)[j]? = some d →
    LimRoomA (OUT).place.need (Scc.Lower.Names.user d.name) (((MSL J L ls) []).G ⟨limA tp, 8⟩) R.base.toNat
  htp : tp = TP0
  hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none

/-- **The aborts of every base context at a placement** `L`, `ls`
(`AbG2`'s at a context with `CxCore2L` at `L`, `ls`, the nodes at `L`; a
segment runs at one placement). -/
def AbG2L (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS)
    (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat) : FragS isaLSE2 := fun s c fs' =>
  ∃ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (R : Region) (F : MachineData → Prop)
    (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop),
    CxCore2L h hp Dt J L ls j R F fs fp ra tp G0 ∧
    ((fs' = fs ∧ ∃ c0, G0 c0 ∧ Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R F
        (abortN2 (imms2Me Λ p) (TailAt2 p j) p L (FC j d hd).cx
          (_root_.Executable.labels (Ly).exe).label fp ra c0) s c) ∨
     (fs' = fs ∧ ∃ (Jc : AS → Ctl → Prop) (pcR : Int64), NbJcOf (imms2Me Λ p) L (FC j d hd).cx Jc ∧
        (∀ σ c', Jc σ c' → TailAt2 p j c'.term) ∧
        Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R F (nbX ((MSL J L ls) fs)
          (_root_.Executable.labels (Ly).exe).label L R (FC j d hd).cx.frame pcR Jc .abort) s c) ∨
     (∃ c0 x is a e c1, G0 c0 ∧ TailAt2 p j (.let_ x (.call "print" is a []) e) ∧
        fs' = Spike.Lib.LowerNode.printFrame x e c1 :: fs ∧
        Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R F (printNAS (_root_.Executable.labels (Ly).exe).label
          (FC j d hd).cx L (imms2Me Λ p) x e c1) s c))

/-- **A base context at any frames and a reachable placement**
(`CxG2M`'s at `L`, `ls`). -/
def CxG2ML (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS)
    (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat) (j : Nat) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab : FragS isaLSE2) : Prop :=
  CxCore2L h hp Dt J L ls j R F fs fp ra tp G0 ∧ ∀ s c fs', AbG2L h hp Dt J L ls s c fs' → Ab s c fs'

/-- **The generic base context at a reachable placement** (`CxG2`'s at
`L`, `ls`). -/
def CxG2L (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS)
    (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat) (j : Nat) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab : FragS isaLSE2) : Prop :=
  CxG2ML h hp Dt J L ls j R F fs fp ra tp G0 Ab ∧ fs ≠ []

/-- **Every compiled block's segment at every reachable placement**
(`FnSpecC2At`'s at `L`, `ls`: the world `W2AtL`, the memory side `MSAtL`,
the contexts `CxOkS … (CxG2L … L ls) Bot` at `L`, `ls`). -/
def FnSpecC2AtL (hp : Scc.Lower.Accepted2 p = true) (Dt : State → Prop) (J : InvS)
    (Bot : StkKey → List TermRun.Frame → Prop) : Prop :=
  ∀ (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat),
    Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls →
    ∀ (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d),
      FnSpecC2 (W2L J L ls) (KT) p L ls (MSL J L ls)
        (CxOkS (p := p) (lbl := L) (lsize := ls) (fnCode2OfPMe hp h Λ) (CxG2L h hp Dt J L ls) Bot j)
        (FC j d hd)

/-! ## At the start's placement -/

/-- `CxCore2` is `CxCore2L` at the start's placement. -/
theorem CxCore2.toL {hp : Scc.Lower.Accepted2 p = true} {Dt : State → Prop} {J : InvS} {j : Nat} {R : Region}
    {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    (H : CxCore2 h hp Dt J j R F fs fp ra tp G0) :
    CxCore2L h hp Dt J (fun _ => none) (fun _ => 0) j R F fs fp ra tp G0 :=
  { H with hre := .base }

/-- `CxCore2L` at the start's placement is `CxCore2`. -/
theorem CxCore2L.toNone {hp : Scc.Lower.Accepted2 p = true} {Dt : State → Prop} {J : InvS} {j : Nat}
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} (H : CxCore2L h hp Dt J (fun _ => none) (fun _ => 0) j R F fs fp ra tp G0) :
    CxCore2 h hp Dt J j R F fs fp ra tp G0 :=
  { H with }

/-- `AbG2`'s aborts are `AbG2L`'s (at the start's placement). -/
theorem abG2_toL {hp : Scc.Lower.Accepted2 p = true} {Dt : State → Prop} {J : InvS} {s : State} {c : Ctl}
    {fs' : List TermRun.Frame} (hA : AbG2 h hp Dt J s c fs') : AbG2L h hp Dt J (fun _ => none) (fun _ => 0) s c fs' := by
  obtain ⟨j, d, hd, R, F, fs, fp, ra, tp, G0, H, hX⟩ := hA
  exact ⟨j, d, hd, R, F, fs, fp, ra, tp, G0, H.toL h, hX⟩

/-- `CxG2ML` at the start's placement gives `CxG2M`. -/
theorem CxG2ML.toNone {hp : Scc.Lower.Accepted2 p = true} {Dt : State → Prop} {J : InvS} {j : Nat}
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (H : CxG2ML h hp Dt J (fun _ => none) (fun _ => 0) j R F fs fp ra tp G0 Ab) :
    CxG2M h hp Dt J j R F fs fp ra tp G0 Ab :=
  ⟨H.1.toNone h, fun s c fs' hA => H.2 s c fs' (abG2_toL h hA)⟩

/-! ## The steps' statements at a reachable placement -/

/-- **The lane stores and buffers at a base context at a reachable
placement** (`LaneBuf2Stmt`'s at `CxG2ML … L ls`, `lbl := L`,
`lsize := ls`). -/
def LaneBuf2StmtL (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (Dt : State → Prop) (J : InvS) (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat)
    (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab : FragS isaLSE2),
    CxG2ML h hp Dt J L ls j R F fs fp ra tp G0 Ab →
    Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat →
    LaneC p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc R F (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab ∧
    NewBufC p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc R F (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab
      (RetLk d.retTy)

/-- **The output calls at a base context at a reachable placement**
(`Print2Stmt`'s at `CxG2ML … L ls`, `lbl := L`, `lsize := ls`). -/
def Print2StmtL (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (Dt : State → Prop),
    (∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R' F'
        (Spike.Lib.A64.Flow.PrintCall.pN (_root_.Executable.labels (Ly).exe).label Pc Qc σC .svc) s c' → Dt s) →
    ∀ (J : InvS) (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat)
    (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab : FragS isaLSE2),
    CxG2ML h hp Dt J L ls j R F fs fp ra tp G0 Ab →
    Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat →
    PrintCallC p L ls (FC j d hd).lcx (FC j d hd).cx (CD ra) ((FC j d hd).Bl ra) (LY0).exe
      (LY0).endPc R F (W2L J L ls) (KT) (MSL J L ls) fp ra tp fs G0 (imms2Me Λ p) (TailAt2 p j) Ab

end G1L

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.CxCore2.toL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.CxCore2.toL

/-- info: 'Spike.Lib.LowerA64.CxCore2L.toNone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.CxCore2L.toNone

/-- info: 'Spike.Lib.LowerA64.abG2_toL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.abG2_toL

/-- info: 'Spike.Lib.LowerA64.CxG2ML.toNone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.CxG2ML.toNone
