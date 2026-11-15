/-
**`hello1` as an instance of the generic `Accepted2` route** (AArch64; the
oracle check of `Spike/Lib/LowerA64/G1Closed2.lean`):

- `hello1_finalCA_g1`: `hello1_finalCA_gen`'s statement from the generic
  route's per-instance step `in2AW_of_setupG1`, its hello1-specific
  premises discharged from `hello1`'s facts (the landings' segments by
  `h1InAW_ofLandT` at `hello1_landAWTW`, the branch-target check
  `hello1_tgOkBA`, the header bound by decision), the function segment and
  `main`'s segment from the generic statements `FnSpecC2Stmt` and
  `MainSeg2Stmt`;
- `hello1_finalCA_ofClosed2StmtA`: the same statement as an instance of the
  generic theorem `Closed2StmtA`'s body at `hello1`'s configuration
  (`closed2StmtA_at`'s conclusion);
- `hello1_finalCA_g1Fin`: `hello1_finalCA`'s statement as a corollary of the
  unconditional generic theorem `closed2StmtA_g1`
  (`Spike/Lib/LowerA64/G1Closed2Fin.lean`) at `hello1`'s configuration and
  linked layout.
-/
import Spike.Lib.LowerA64.G1Closed2
import Spike.Lib.LowerA64.G1Closed2Fin
import Spike.Test.A64Hello1FinalCA
import Spike.Test.A64Hello1FinalT

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.LowerNode (hello1o_accepted2)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- The compiler's output for the program. -/
local notation "OA" => Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)

/-- **`hello1`'s AArch64 statement through the generic route**
(`hello1_finalCA_gen`'s conclusion, at any layout passing the placement
check): `a64_scc_correctE_text_closedAt2_atW` at `in2AW_of_setupG1`, the
landings' segments from `hello1`'s (`h1InAW_ofLandT` at `hello1_landAWTW`,
as `hello1_finalAW_ofT`), the function segment and `main`'s segment from
the generic statements `FnSpecC2Stmt` and `MainSeg2Stmt`. -/
theorem hello1_finalCA_g1 (HFS : FnSpecC2Stmt) (HM : MainSeg2Stmt) (Λ : Scc.Sem.Layout)
    (hΛ : placeOKAt SccCertificate.placeCfg Λ OA = true)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
      SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 Λ P1A) B
      SccCertificate.asm :=
  a64_scc_correctE_text_closedAt2_atW hello1o_accepted2 (by decide) hΛ (by decide)
    (fun E hE h' => in2AW_of_setupG1 h' hello1o_accepted2 hello1_htyA.choose_spec (by decide) (by decide) hE
      hello1_tgOkBA (by decide)
      (HFS _ _ _ _ hello1o_accepted2 (by decide) h' hello1_tgOkBA _ fun _ _ _ _ _ _ _ _ => trivial)
      (HM _ _ _ _ hello1o_accepted2 (by decide) h' hello1_tgOkBA)
      (h1InAW_ofLandT h' (hello1_landAWTW h') hello1_hTnA
        (fun J _ _ _ _ _ _ _ _ _ => hello1_hAbQA h' rfl hello1o_accepted2 hello1_htyA.choose_spec
          (fun _ _ _ _ _ _ => trivial) J _ _)))
    (hello1_out_eqA ▸ SccCertificate.out_eq ▸ hpa) hB

/-- **`hello1`'s AArch64 statement as an instance of the generic theorem**
(`hello1_finalCA_gen`'s conclusion from `Closed2StmtA`'s body at `hello1`'s
configuration, e.g. `closed2StmtA_at`'s conclusion there). -/
theorem hello1_finalCA_ofClosed2StmtA
    (H : ∀ (pcfg : Scc.Cert.PlaceOK.Config) (p : CoreTerm.Prog) (Λ : Scc.Sem.Layout),
      Scc.Lower.Accepted2 p = true → Scc.Lower.mainRetOk p = true →
      placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config p)) = true →
      CfgNeedOkA pcfg = true →
      ∀ {asm : String}, Scc.Cert.Link.A64.parsesTo asm
        (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config p)).prog
        (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config p)).secs = true →
      ∀ {B : Scc.Sem.Budget}, B.cells = Scc.Cert.PlaceOK.allocCells → ∀ {arch : WeakMem.Arch},
      Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
        { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B asm)
    (Λ : Scc.Sem.Layout) (hΛ : placeOKAt SccCertificate.placeCfg Λ OA = true)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
      SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 Λ P1A) B
      SccCertificate.asm :=
  H _ P1A Λ hello1o_accepted2 (by decide) hΛ (by decide) (hello1_out_eqA ▸ SccCertificate.out_eq ▸ hpa) hB

/-- **The header bound at `hello1`'s configuration** (the premise `hobj`
of `closed2StmtA_at` there). -/
theorem hello1_hobjA : Scc.Obj.nShift SccCertificate.config.layout.obj < 22 := by decide

/-- **`hello1`'s AArch64 statement from the generic theorem**
(`hello1_finalCA`'s conclusion, `hello1_finalCA_ofClosed2StmtA` at
`closed2StmtA_g1` at `hello1`'s configuration, the header bound
`hello1_hobjA`, the linked layout passing the placement check). -/
theorem hello1_finalCA_g1Fin
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
      SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A)
      (lay2 Spike.Test.Hello1LinkedA64.Λe P1A) B SccCertificate.asm :=
  hello1_finalCA_ofClosed2StmtA
    (fun pcfg p Λ' => closed2StmtA_g1 SccCertificate.config hello1_hobjA pcfg p Λ')
    _ (hello1_out_eqA ▸ Spike.Test.Hello1LinkedA64.hello1_placeOKAt) hpa hB

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_finalCA_g1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_finalCA_g1

/--
info: 'Spike.Lib.LowerA64.hello1_finalCA_ofClosed2StmtA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_finalCA_ofClosed2StmtA

/-- info: 'Spike.Lib.LowerA64.hello1_hobjA' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_hobjA

/-- info: 'Spike.Lib.LowerA64.hello1_finalCA_g1Fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_finalCA_g1Fin
