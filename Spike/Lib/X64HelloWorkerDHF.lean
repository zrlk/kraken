/-
**The assembly's worker side at the placed instance on x86-64, at the spawned child's segment inside `XHF ∧ AbX`**
(the twin of `Spike/Lib/HelloWorkerDHF.lean`): `X64HelloAssemblyI.DH` at `X64HelloWorkerRRXF.helloDRF`'s fragments
placed at the records (`SRH`'s labels, `X64HelloOwnLift.msWHX` at `GH`, flag `w.1.cS`). The root's switch
instantiates `DH hp i G0 (PF hp i G0) (ZF hp i μ) (XF hp i μ) (hsegFH …)`; this `DH` is `helloDRFY` at the
placement and the node-only fragment `OwnW (tcbWH)` definitionally, so `helloDRFY`'s projections are its rows.

- `PF`, `XF`, `ZF`: the entry fragment `childPX`, the landing fragment `XHF ∧ AbX μ lab`, the segment fact
  `ZHR ∧ OwnW (tcbWH) ∧ XF` (no write at the worker's own self word, `X64OwnWNodes.OwnW`).
- `lays_F`: the placed executable lays out hello's cells (from the loader's parses).
- `hYH`: `OwnW (tcbWH)` at every node of the child's run (`OwnZH.zObl_own`, its premises from `ChildPrem` at
  `msWHX` and the record's `GhOK`/`SelfOK`, `X64HelloOwnSep.own_of_childPrem`).
- `hsegFH`: the segment (`helloDRFY`'s `hsegFY` at the placement).
- `DHF_hplW`, `DHF_hcall`, `DHF_flag`, `DHF_ab`, `DHF_zhr`: the rows `hplW`, `hcall`, the flag, the abort facts and
  the invariant inside `NNH ∧ WideX ∧ Pend ZHR`.
- `DHF_hZW`: at a store-phase state of the segment fact, no write at the worker's own self word.

## Differences from the AArch64 version

- The loader's parses are `cellsOf asm = some …` (AArch64 `textProgram asm = .ok …`), the program the cells
  `SccCode.helloCells` (AArch64 `helloProg`); the labels' check is `Scc.Sem.X64.codeLabel` (AArch64
  `Link.A64.codeOf`).
- Over `PlaceWX`, `X64HelloAssemblyI`'s instance data and `X64HelloOwnLift.msWHX`
  (the worker side owning its TCB self word).
-/
import Spike.Lib.X64HelloWorkerRRXF
import Spike.Lib.X64HelloAssemblyI
import Spike.Lib.X64HelloOwnObl
import Spike.Lib.X64HelloOwnSep

namespace Spike.Lib.X64HelloWorkerDHF

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64.Flow.Worker (NNH)
open Spike.Lib.X64.WideKeep (WideX)
open Spike.Lib.X64HelloSplit (workerCallH workerRestH)
open Spike.Lib.X64.Flow.Worker.Hello.Z (ZHR)
open Spike.Lib.X64.Flow.Worker.Hello.SegRP (childPX)
open Spike.Lib.X64.Flow.Worker.Hello.AbObl (AbX MarksL)
open Spike.Lib.X64.Flow.Worker.Hello.FlagZ (FlagF)
open Spike.Lib.X64.HelloPh.XH (XHF)
open Spike.Lib.X64HelloAssemblyI (ιH LH endH SRH GH DH)
open Spike.Lib.X64HelloWorkerRRXF (helloDRFY helloDRFY_hplW helloDRFY_hcall helloDRFY_flag helloDRFY_ab
  helloDRFY_zhr)
open Spike.Lib.X64.Flow.Worker.Wake.OwnW (OwnW)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)

/-- **The entry fragment**: `childPX` at the record's placement, memory side and flag. -/
abbrev PF : ιH hp i → FragS isa := fun w =>
  childPX (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
    (fun _ => Spike.Lib.X64HelloOwnLift.msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) w.1.cS

/-- **The landing fragment**: `XHF` at the record's placement and flag, and the abort facts `AbX μ lab`. -/
abbrev XF (μ : Marks) : ιH hp i → FragS isa := fun w s c fs =>
  XHF (LH hp i).Λ (SRH hp i w).lbl w.1.cS s c fs ∧ AbX μ (_root_.Executable.labels (LH hp i).exe).label s c fs

/-- **The node-only fragment**: no write at the worker's own self word `tcbWH`. -/
abbrev YF : ιH hp i → FragS isa := fun _ s c _ => OwnW (X64HelloOwnLift.tcbWH (LH hp i)) s c

/-- **The segment fact**: `ZHR ∧ OwnW (tcbWH) ∧ XF`. -/
abbrev ZF (μ : Marks) : ιH hp i → FragS isa := fun w s c fs =>
  ZHR (LH hp i).exe (LH hp i).pfx s c fs ∧ YF hp i w s c fs ∧ XF hp i μ w s c fs

variable (hI : Spike.Lib.X64.HelloPh.XHFSeg.ImmsKid (LH hp i).Λ) {asm : Asm}
  (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells) {μ : Marks}
  (hlab : ∀ l x, Scc.Sem.X64.codeLabel Spike.Lib.X64.HelloPh.lo SccCode.helloCells l = some x →
    (_root_.Executable.labels (LH hp i).exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels (LH hp i).exe).label)

include hpa hhp in
/-- The placed executable lays out hello's cells (from the loader's parses). -/
theorem lays_F : Scc.Cert.Rt.X64.Lays (LH hp i).exe SccCode.helloCells (LH hp i).pfx := by
  have ho : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  rw [← ho]; exact (LH hp i).lays

include hpa hhp in
/-- **`OwnW (tcbWH)` at every node of the child's run** (`OwnZH.zObl_own`): the flag's word, the park word and
the exit word are not `tcbWH` (`X64HelloOwnSep.own_of_childPrem`, from `ChildPrem` at `msWHX`, the flag's offset
in its label from the record's `GhOK` and `tcbWH` outside every placed label from its `SelfOK`). -/
theorem hYH : ∀ w (d : Spike.Lib.X64.Flow.Worker.Hello.SegR.ChildD), d.ok →
    Spike.Lib.X64.Flow.Worker.Hello.SegR.ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
      (fun _ => Spike.Lib.X64HelloOwnLift.msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) d.F d.w d.tp d.sp0 d.w0 d.w1
      d.w2 d.w3 d.w4 d.n d.m → d.w3.val = .loc w.1.cS 0 →
    Spike.Lib.X64.Flow.Worker.Hello.SegRP.ZObl (YF hp i w) (LH hp i).exe (endH hp i)
      (fun _ => Spike.Lib.X64HelloOwnLift.msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) d.R d.F d.w d.tp d.sp0 d.T
      d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m := by
  intro w d ho hc hcS
  haveI := (LH hp i).valid
  obtain ⟨-, -, -, ⟨_, _, hoff, _⟩, -⟩ := w.2.1
  obtain ⟨hA, hB, htp⟩ := X64HelloOwnSep.own_of_childPrem hc hcS hoff w.2.2.2.2.2.1
  obtain ⟨-, hR, hlo, hhi⟩ := ho
  exact Spike.Lib.X64.Flow.Worker.Hello.OwnZH.zObl_own (lays_F hp i hpa hhp) rfl hR (by omega) hhi hA hB htp

include hI hpa hhp hlab hμ in
/-- **The segment at the placement** (`X64HelloWorkerRRXF.hsegFY` at `YF`). -/
theorem hsegFH : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ ZF hp i μ w s c fs) (XF hp i μ w)
    helloSrc (SRH hp i w).lbl (fun _ => Spike.Lib.X64HelloOwnLift.msWHX (LH hp i) (GH hp i G0) (SRH hp i) w)
    (PF hp i G0 w) (fun _ _ _ => False) := by
  haveI := (LH hp i).valid
  exact Spike.Lib.X64HelloWorkerRRXF.hsegFY hI (LH hp i).exe (endH hp i) (LH hp i).pfx (fun w => (SRH hp i w).lbl)
    (fun w _ => Spike.Lib.X64HelloOwnLift.msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) (fun w => w.1.cS)
    (lays_F hp i hpa hhp) rfl hlab hμ (fun _ _ => rfl) (YF hp i) (hYH hp i G0 hpa hhp)

set_option hygiene false in
local notation "DF" => DH hp i G0 (PF hp i G0) (ZF hp i μ) (XF hp i μ) (hsegFH hp i G0 hI hpa hhp hlab hμ)

include hI hpa hhp hlab hμ

/-- **The row `hplW`** at the instance (`helloDRFY_hplW`). -/
theorem DHF_hplW : ∀ w s c fs, (DF).Wi w s c fs → PlacedSE (LH hp i).Λ (SRH hp i w).lbl s c fs := by
  haveI := (LH hp i).valid
  exact helloDRFY_hplW hI _ _ _ (SRH hp i) _ _ _ (lays_F hp i hpa hhp) rfl hlab hμ _ (fun w => w.1.cwW)
    (fun _ => Spike.Lib.X64HelloOkW.lBH) (fun _ => 13) (fun _ => 2) _ (hYH hp i G0 hpa hhp)

/-- **The row `hcall`** at the instance (`helloDRFY_hcall`). -/
theorem DHF_hcall : ∀ w st c, (DF).Wi w st c [] → ∀ c', LocalRunS helloSrc c c' → c'.term = workerCallH →
    FramesPlaced (LH hp i).Λ (SRH hp i w).lbl st [⟨"u", workerRestH, c'.env, [], .unit⟩] := by
  haveI := (LH hp i).valid
  exact helloDRFY_hcall hI _ _ _ (SRH hp i) _ _ _ (lays_F hp i hpa hhp) rfl hlab hμ _ (fun w => w.1.cwW)
    (fun _ => Spike.Lib.X64HelloOkW.lBH) (fun _ => 13) (fun _ => 2) _ (hYH hp i G0 hpa hhp)

/-- **The flag** at the instance (`helloDRFY_flag`). -/
theorem DHF_flag : ∀ w s c fs, (DF).Wi w s c fs → FlagF w.1.cS s c fs := by
  haveI := (LH hp i).valid
  exact helloDRFY_flag hI _ _ _ (SRH hp i) _ _ (fun w => w.1.cS) (lays_F hp i hpa hhp) rfl hlab hμ _
    (fun w => w.1.cwW) (fun _ => Spike.Lib.X64HelloOkW.lBH) (fun _ => 13) (fun _ => 2) _
    (hYH hp i G0 hpa hhp)

/-- **The abort facts** at the instance (`helloDRFY_ab`; the root's `hab1W` at `μ`). -/
theorem DHF_ab : ∀ w s c fs, (DF).Wi w s c fs →
    X64HelloPostAb.AbFacts μ (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels (LH hp i).exe).label) s := by
  haveI := (LH hp i).valid
  exact helloDRFY_ab hI _ _ _ (SRH hp i) _ _ _ (lays_F hp i hpa hhp) rfl hlab hμ _ (fun w => w.1.cwW)
    (fun _ => Spike.Lib.X64HelloOkW.lBH) (fun _ => 13) (fun _ => 2) _ (hYH hp i G0 hpa hhp)

/-- **The invariant inside `NNH ∧ WideX ∧ Pend ZHR`** at the instance (`helloDRFY_zhr`). -/
theorem DHF_zhr : ∀ w s c fs, (DF).Wi w s c fs →
    NNH (LH hp i).exe (endH hp i) s ∧ WideX (LH hp i).exe s ∧
      Pend helloSrc (ZHR (LH hp i).exe (LH hp i).pfx) s c fs := by
  haveI := (LH hp i).valid
  exact helloDRFY_zhr hI _ _ _ (SRH hp i) _ _ _ (lays_F hp i hpa hhp) rfl hlab hμ _ (fun w => w.1.cwW)
    (fun _ => Spike.Lib.X64HelloOkW.lBH) (fun _ => 13) (fun _ => 2) _ (hYH hp i G0 hpa hhp)

omit hI hpa hhp hlab hμ in
/-- **No write at the worker's own self word at a store-phase state of the segment fact** (`ZF`'s `OwnW`
conjunct; the flip's `hZW`). -/
theorem DHF_hZW : ∀ w s c, ZF hp i μ w s c [] → c.hold = none → X64HelloW1Store.StoreT c.term →
    OwnW (X64HelloOwnLift.tcbWH (LH hp i)) s c :=
  fun _ _ _ h _ _ => h.2.1

end Inst

end Spike.Lib.X64HelloWorkerDHF

/-- info: 'Spike.Lib.X64HelloWorkerDHF.hsegFH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerDHF.hsegFH

/-- info: 'Spike.Lib.X64HelloWorkerDHF.DHF_hplW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerDHF.DHF_hplW

/-- info: 'Spike.Lib.X64HelloWorkerDHF.DHF_hcall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerDHF.DHF_hcall

/-- info: 'Spike.Lib.X64HelloWorkerDHF.DHF_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerDHF.DHF_flag

/-- info: 'Spike.Lib.X64HelloWorkerDHF.DHF_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerDHF.DHF_ab

/-- info: 'Spike.Lib.X64HelloWorkerDHF.DHF_zhr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerDHF.DHF_zhr

/-- info: 'Spike.Lib.X64HelloWorkerDHF.hYH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerDHF.hYH
