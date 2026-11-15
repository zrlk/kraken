/-
**The plain calls at a base context at a reachable placement** (x86-64;
the twin of `Spike/Lib/LowerA64/G1CallG2L.lean`): the statements of
`Spike/Lib/LowerX64/G1CallG2.lean` (`ProCallG2L` is in
`Spike/Lib/LowerX64/G1ProCallG2L.lean`) and `LimOk2Stmt`
(`Spike/Lib/LowerX64/G1FnSpec.lean`) at the placement `L`, `ls`, at the
contexts `CxG2ML` (`Spike/Lib/LowerX64/G1FnSpecL.lean`).

- `LimOk2StmtL`: the prologue's limit facts inside `MSAtL`;
- `WCallG2L`: the call's blocks inside `W2AtL`.
-/
import Spike.Lib.LowerX64.G1CallG2
import Spike.Lib.LowerX64.G1CallCxL

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (i64 rel)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA tpOf)
open Spike.Lib.X64.Rt (rS0)
open Spike.Lib.AllocReach (Reach)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum SlotRepAt)

section G1CallG2L

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
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- `W2AtL` at `Closed2At`'s instance and the placement `L`, `ls`. -/
local notation "W2L" J:max L:max ls:max => W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0) L ls

set_option hygiene false in
/-- `MSAtL` at `Closed2At`'s instance (the nodes' abort `ab2`) and the
placement `L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

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

set_option hygiene false in
/-- The code facts' return address condition. -/
local notation "RAOK" ra:max => Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
  Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat

/-- **The prologue's limit facts inside `MSAtL`** at a placement `L`, `ls`
reachable from the start's (`LimOk2Stmt`'s): at any frames `fs`, a state whose `%fs` base is the
first TCB's, a frame condition leaving the TCB's limit word unmapped, and
every limit value at most the new frame's `%rsp`. -/
def LimOk2StmtL (_hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (J : InvS) (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat),
    Reach (Spike.Lib.X64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls →
    ∀ (F : MachineData → Prop) (fs : List TermRun.Frame) (σ : AS) (fsz : Int),
    σ.regs.fsBase = TP0 →
    (∀ m, F m → Mem.loadInt m.dmem (limA (TP0)) 8 = none) →
    (∀ v, ((MSL J L ls) []).G ⟨limA (TP0), 8⟩ v →
      (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fsz).toBitVec).toNat) →
    Spike.Lib.X64.Flow.Ret0.LimOk ((MSL J L ls) fs) F
      (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fsz).toBitVec)

set_option linter.unusedVariables false in
/-- **A plain call's blocks inside `W2` at a base context at a reachable
placement** (`WCallG2` at `CxG2ML … L ls`, `lbl := L`, `lsize := ls`;
`CallC2FW`'s `hWB`, `hWR`, `hWBl`, `hWC` at the `j`th compiled block's code
facts, in the rebased region `rbR R`): the argument's load, the result's
store, the `callq` and the callee's entry, at nodes whose controls are in
`G0` with the saved pair and placed in the slot file. -/
def WCallG2L (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (Dt : State → Prop) (J : InvS) (L : WeakMem.AllocLabel → Option Nat)
    (ls : WeakMem.AllocLabel → Nat) (j : Nat) (d : Decl)
    (hd : (compiled2 p)[j]? = some d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isa),
    CxG2ML h hp Dt J L ls j R F fs fp ra tp G0 Ab → RAOK ra →
    (∀ (n : ND) blk, SubCd (CD ra) n.pc blk → n.o = oB (FC j d hd).fr →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) L (rsOf (FC j d hd).fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk (FC j d hd).fr blk → BlkW (fun s c => (W2L J L ls) s c fs) (KT) (LY0).exe (LY0).endPc (rbR R) F n blk) ∧
    (∀ (n : ND) blk (k0 : Int), SubCd (CD ra) n.pc blk → n.o = oB (FC j d hd).fr → blk.length ≤ 1 →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) L (rsOf (FC j d hd).fr)
          (Spike.Lib.upd σ.slot k0 (σ.regs.get64 .rax)) c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk (FC j d hd).fr blk → BlkW (fun s c => (W2L J L ls) s c fs) (KT) (LY0).exe (LY0).endPc (rbR R) F n blk) ∧
    (∀ (n : ND) zc (g : String) k, (FC j d hd).Bl ra n.pc zc (Scc.Lower.Names.user g) k →
      Spike.Lib.LowerCall.Callee (FC j d hd).lcx g → (∃ x a e, TailAt2 p j (.let_ x (.call g [] a []) e)) →
      n.o = oB (FC j d hd).fr →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) L (rsOf (FC j d hd).fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      BlkW (fun s c => (W2L J L ls) s c fs) (KT) (LY0).exe (LY0).endPc (rbR R) F n
        [(i64 (.call (rel (Scc.Lower.Names.user g))), zc)]) ∧
    (∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → Spike.Lib.LowerCall.Callee (FC j d hd).lcx g →
      (∃ x a e, TailAt2 p j (.let_ x (.call g [] a []) e)) → ∀ (n : ND),
      n.pc = (_root_.Executable.labels (LY0).exe).label (Scc.Lower.Names.user g) →
      n.o = { oB (FC j d hd).fr with sp := (oB (FC j d hd).fr).sp - 8 } →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) L (rsOf (FC j d hd).fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      ∀ s c, Spike.Lib.X64.At (LY0).exe (LY0).endPc (rbR R) F n s c → (W2L J L ls) s c fs)

end G1CallG2L

end Spike.Lib.LowerX64
