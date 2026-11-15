/-
**The plain calls at a base context at a reachable placement** (AArch64):
the statements of `Spike/Lib/LowerA64/G1CallG2.lean` (`ProCallG2L` is in
`Spike/Lib/LowerA64/G1ProCallG2L.lean`) and `LimOk2Stmt`
(`Spike/Lib/LowerA64/G1FnSpec.lean`) at the placement `L`, `ls`, at the
contexts `CxG2ML` (`Spike/Lib/LowerA64/G1FnSpecL.lean`).

- `LimOk2StmtL`: the prologue's limit facts inside `MSAtL`;
- `WCallG2L`: the call's blocks inside `W2AtL`.
-/
import Spike.Lib.LowerA64.G1CallG2
import Spike.Lib.LowerA64.G1CallCxL

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.A64.Rt (rS0)
open Spike.Lib.AllocReach (Reach)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum SlotRepAt)

section G1CallG2L

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

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
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- The code facts' return address condition. -/
local notation "RAOK" ra:max => Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
  Spike.Lib.A64.PhRec.ph LY0 (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat

/-- **The prologue's limit facts inside `MSAtL`** at a placement `L`, `ls`
reachable from the start's (`LimOk2Stmt`'s): at any frames `fs`, a state whose `TPIDR_EL0`
is the first TCB's, a frame condition leaving the TCB's limit word
unmapped, and every limit value at most the new frame's `sp`. -/
def LimOk2StmtL (_hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (J : InvS) (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat),
    Reach (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls →
    ∀ (F : MachineData → Prop) (fs : List TermRun.Frame) (σ : AS) (fsz : Int),
    σ.regs.TPIDR_EL0 = UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64) →
    (∀ m, F m → Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) 8 = none) →
    (∀ v, ((MSL J L ls) []).G ⟨limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt fsz).toBitVec).toNat) →
    Spike.Lib.A64.Flow.Ret0.LimOk ((MSL J L ls) fs) F (LY0).exe (LY0).endPc
      (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) (σ.regs.SP.toBitVec - (Int64.ofInt fsz).toBitVec)

set_option linter.unusedVariables false in
/-- **A plain call's blocks inside `W2` at a base context at a reachable
placement** (`WCallG2` at `CxG2ML … L ls`, `lbl := L`, `lsize := ls`;
`CallC2FW`'s `hWB`, `hWR`, `hWBl`, `hWC` at the `j`th compiled block's code
facts): the argument's load, the result's store,
the `bl` and the callee's entry, at nodes whose controls are in `G0` with
the saved pair and placed in the slot file. -/
def WCallG2L (hp : Scc.Lower.Accepted2 p = true) : Prop :=
  ∀ (Dt : State → Prop) (J : InvS) (L : WeakMem.AllocLabel → Option Nat)
    (ls : WeakMem.AllocLabel → Nat) (j : Nat) (d : Decl)
    (hd : (compiled2 p)[j]? = some d) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
    CxG2ML h hp Dt J L ls j R F fs fp ra tp G0 Ab → RAOK ra →
    (∀ (n : ND) blk, SubCd (CD ra) n.pc blk → n.o = oF (FC j d hd).cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) L (rsOf (FC j d hd).cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk (FC j d hd).cx blk → BlkW (fun s c => (W2L J L ls) s c fs) (KT) (LY0).exe (LY0).endPc R F n blk) ∧
    (∀ (n : ND) blk (k0 : Int), SubCd (CD ra) n.pc blk → n.o = oF (FC j d hd).cx → blk.length ≤ 1 →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) L (rsOf (FC j d hd).cx) (Spike.Lib.upd σ.slot k0 σ.regs.X0.toBitVec) c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk (FC j d hd).cx blk → BlkW (fun s c => (W2L J L ls) s c fs) (KT) (LY0).exe (LY0).endPc R F n blk) ∧
    (∀ (n : ND) (g : String) k, (FC j d hd).Bl ra n.pc (Scc.Lower.Names.user g) k →
      Spike.Lib.LowerCall.Callee (FC j d hd).lcx g → (∃ x a e, TailAt2 p j (.let_ x (.call g [] a []) e)) →
      n.o = oF (FC j d hd).cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) L (rsOf (FC j d hd).cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      BlkW (fun s c => (W2L J L ls) s c fs) (KT) (LY0).exe (LY0).endPc R F n [blD (Scc.Lower.Names.user g)]) ∧
    (∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → Spike.Lib.LowerCall.Callee (FC j d hd).lcx g →
      (∃ x a e, TailAt2 p j (.let_ x (.call g [] a []) e)) → ∀ (n : ND),
      n.pc = (_root_.Executable.labels (LY0).exe).label (Scc.Lower.Names.user g) → n.o = oF (FC j d hd).cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt (imms2Me Λ p) L (rsOf (FC j d hd).cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      ∀ s c, Spike.Lib.A64.Flow.At (LY0).exe (LY0).endPc R F n s c → (W2L J L ls) s c fs)

end G1CallG2L

end Spike.Lib.LowerA64
