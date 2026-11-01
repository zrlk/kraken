/-
**The assembly's worker side at the placed instance, at the spawned child's segment inside `XHF ∧ AbX`** (hello.w,
rows 5j-wit-W, 5j-wit-E-call, 5i-hab1, B8-genP-hmapW-flag; AArch64): `HelloAssemblyI.DH` at
`HelloWorkerRRXF.helloDRF`'s fragments placed at the records (`SRH`'s labels, `msWH` at `GH`, flag `w.1.cS`). The
root's switch instantiates `DH hp i G0 (PF hp i G0) (ZF hp i μ) (XF hp i μ) (hsegFH …)`; this `DH` is `helloDRF` at
the placement definitionally, so `helloDRF`'s projections are its rows.

- `PF`, `XF`, `ZF`: the entry fragment `childPX`, the landing fragment `XHF ∧ AbX μ lab`, the segment fact
  `ZHR ∧ XF`.
- `hsegFH`: the segment (`helloDRF`'s `hsegF` at the placement; `hp`, `hend` from the loader's parses).
- `DHF_hplW`, `DHF_hcall`, `DHF_flag`, `DHF_ab`, `DHF_zhr`: the rows `hplW`, `hcall`, the flag, the abort facts and
  the invariant inside `NNH ∧ WideX ∧ Pend ZHR` (for `hhalt1`, `hRW1`, `pass` by `Z` monotonicity).
-/
import Spike.Lib.HelloWorkerRRXF
import Spike.Lib.HelloAssemblyI

namespace Spike.Lib.HelloWorkerDHF

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.A64.WideKeep (WideX)
open Spike.Lib.HelloSplit (workerCallH workerRestH)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZHR)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (childPX)
open Spike.Lib.A64.Flow.Worker.Hello.AbObl (AbX MarksL)
open Spike.Lib.A64.Flow.Worker.Hello.FlagZ (FlagF)
open Spike.Lib.A64.HelloPh.XH (XHF)
open Spike.Lib.HelloAssemblyI (ιH LH endH SRH GH DH)
open Spike.Lib.HelloWorkerRRXF (helloDRF helloDRF_hplW helloDRF_hcall helloDRF_flag helloDRF_ab helloDRF_zhr)
open Scc.Cert.Link.A64 (codeOf)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)

/-- **The entry fragment**: `childPX` at the record's placement, memory side and flag. -/
abbrev PF : ιH hp i → FragS isaLSE2 := fun w =>
  childPX (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
    (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) w.1.cS

/-- **The landing fragment**: `XHF` at the record's placement and flag, and the abort facts `AbX μ lab`. -/
abbrev XF (μ : Marks) : ιH hp i → FragS isaLSE2 := fun w s c fs =>
  XHF (LH hp i).Λ (SRH hp i w).lbl w.1.cS s c fs ∧ AbX μ (_root_.Executable.labels (LH hp i).exe).label s c fs

/-- **The segment fact**: `ZHR ∧ XF`. -/
abbrev ZF (μ : Marks) : ιH hp i → FragS isaLSE2 := fun w s c fs =>
  ZHR (LH hp i).exe (LH hp i).pfx s c fs ∧ XF hp i μ w s c fs

variable (hI : Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid (LH hp i).Λ) {asm : String}
  (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg) {μ : Marks}
  (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
    (_root_.Executable.labels (LH hp i).exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels (LH hp i).exe).label)

include hpa hhp in
/-- The placed executable lays out hello's program (from the loader's parses). -/
theorem lays_F : Scc.Cert.Rt.A64.Lays (LH hp i).exe helloProg (LH hp i).pfx := by
  have ho : o.prog = helloProg := Except.ok.inj (hpa.symm.trans hhp)
  rw [← ho]; exact (LH hp i).lays

include hI hpa hhp hlab hμ in
/-- **The segment at the placement** (`HelloWorkerRRXF.hsegF`). -/
theorem hsegFH : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ ZF hp i μ w s c fs) (XF hp i μ w)
    helloSrc (SRH hp i w).lbl (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (PF hp i G0 w)
    (fun _ _ _ => False) := by
  haveI := (LH hp i).valid
  exact Spike.Lib.HelloWorkerRRXF.hsegF hI (LH hp i).exe (endH hp i) (LH hp i).pfx (fun w => (SRH hp i w).lbl)
    (fun w _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (fun w => w.1.cS)
    (lays_F hp i hpa hhp) rfl hlab hμ (fun _ _ => rfl)

set_option hygiene false in
local notation "DF" => DH hp i G0 (PF hp i G0) (ZF hp i μ) (XF hp i μ) (hsegFH hp i G0 hI hpa hhp hlab hμ)

include hI hpa hhp hlab hμ

/-- **The row `hplW`** at the instance (`helloDRF_hplW`). -/
theorem DHF_hplW : ∀ w s c fs, (DF).Wi w s c fs → PlacedSE (LH hp i).Λ (SRH hp i w).lbl s c fs := by
  haveI := (LH hp i).valid
  exact helloDRF_hplW hI _ _ _ (SRH hp i) _ _ _ (lays_F hp i hpa hhp) rfl hlab hμ _ (fun w => w.1.cwW)
    (fun _ => Spike.Lib.HelloOkW.lBH) (fun _ => 13) (fun _ => 2)

/-- **The row `hcall`** at the instance (`helloDRF_hcall`). -/
theorem DHF_hcall : ∀ w st c, (DF).Wi w st c [] → ∀ c', LocalRunS helloSrc c c' → c'.term = workerCallH →
    FramesPlaced (LH hp i).Λ (SRH hp i w).lbl st [⟨"u", workerRestH, c'.env, [], .unit⟩] := by
  haveI := (LH hp i).valid
  exact helloDRF_hcall hI _ _ _ (SRH hp i) _ _ _ (lays_F hp i hpa hhp) rfl hlab hμ _ (fun w => w.1.cwW)
    (fun _ => Spike.Lib.HelloOkW.lBH) (fun _ => 13) (fun _ => 2)

/-- **The flag** at the instance (`helloDRF_flag`; `HelloMapWF.hmapW_flagH`'s `hflag`). -/
theorem DHF_flag : ∀ w s c fs, (DF).Wi w s c fs → FlagF w.1.cS s c fs := by
  haveI := (LH hp i).valid
  exact helloDRF_flag hI _ _ _ (SRH hp i) _ _ (fun w => w.1.cS) (lays_F hp i hpa hhp) rfl hlab hμ _
    (fun w => w.1.cwW) (fun _ => Spike.Lib.HelloOkW.lBH) (fun _ => 13) (fun _ => 2)

/-- **The abort facts** at the instance (`helloDRF_ab`; the root's `hab1W` at `μ`). -/
theorem DHF_ab : ∀ w s c fs, (DF).Wi w s c fs →
    HelloPostAb.AbFacts μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels (LH hp i).exe).label) s := by
  haveI := (LH hp i).valid
  exact helloDRF_ab hI _ _ _ (SRH hp i) _ _ _ (lays_F hp i hpa hhp) rfl hlab hμ _ (fun w => w.1.cwW)
    (fun _ => Spike.Lib.HelloOkW.lBH) (fun _ => 13) (fun _ => 2)

/-- **The invariant inside `NNH ∧ WideX ∧ Pend ZHR`** at the instance (`helloDRF_zhr`). -/
theorem DHF_zhr : ∀ w s c fs, (DF).Wi w s c fs →
    NNH (LH hp i).exe (endH hp i) s ∧ WideX (LH hp i).exe s ∧
      Pend helloSrc (ZHR (LH hp i).exe (LH hp i).pfx) s c fs := by
  haveI := (LH hp i).valid
  exact helloDRF_zhr hI _ _ _ (SRH hp i) _ _ _ (lays_F hp i hpa hhp) rfl hlab hμ _ (fun w => w.1.cwW)
    (fun _ => Spike.Lib.HelloOkW.lBH) (fun _ => 13) (fun _ => 2)

end Inst

end Spike.Lib.HelloWorkerDHF

/-- info: 'Spike.Lib.HelloWorkerDHF.hsegFH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerDHF.hsegFH

/-- info: 'Spike.Lib.HelloWorkerDHF.DHF_hplW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerDHF.DHF_hplW

/-- info: 'Spike.Lib.HelloWorkerDHF.DHF_hcall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerDHF.DHF_hcall

/-- info: 'Spike.Lib.HelloWorkerDHF.DHF_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerDHF.DHF_flag

/-- info: 'Spike.Lib.HelloWorkerDHF.DHF_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerDHF.DHF_ab

/-- info: 'Spike.Lib.HelloWorkerDHF.DHF_zhr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerDHF.DHF_zhr
