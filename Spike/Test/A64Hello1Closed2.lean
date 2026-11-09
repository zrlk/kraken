/-
**`hello1` from `Closed2StmtA`** (AArch64): the statement of
`Spike/Lib/LowerA64/Closed2StmtA.lean` at `hello1o` (`hello1.w` with `print`
linked), at `ld`'s layout of the linked executable
(`Spike/Test/Hello1LinkedA64.lean`).

- `hello1_out_eqA`: `hello1o`'s output (four declarations) is `hello1.w`'s
  (three, `print` a stub), the certificate's `out`: `print` and `printL` are
  externs and not compiled.
- `hello1_of_closed2A`: the statement at `hello1o`, from the certificate's
  facts; the parse check `hpa` (its compiled `#guard`) a premise.
-/
import Spike.Lib.LowerA64.Closed2StmtA
import Spike.Lib.Src.SrcSafe2
import Spike.Test.Hello1LinkedA64

namespace Spike.Lib.LowerA64

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- **`hello1o`'s output is `hello1.w`'s** (the certificate's `out`): the
lowering of `print`'s model (`printL`, `print`) adds no code, `print` being
an extern; one kernel run of each lowering. -/
theorem hello1_out_eqA :
    Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o) =
      SccCertificate.out := by
  -- `hello1o` lowers, at the certificate's `configW` (`config` with the ranked
  -- witness `gwLit`), to the certificate's literals: one kernel run of each stage.
  have hL : lowered1 SccCertificate.configW Spike.Test.Hello1MainSrc.hello1o =
      some (SccCertificate.loweredLit.1, SccCertificate.loweredLit.2) :=
    lowered1_of_stages (fr := SccCertificate.framesLit) (by kernel_rfl) (by kernel_rfl)
  -- scc's run at `config` is the run at `configW` (the tables' stage at the witness succeeds).
  have hW := Scc.Cert.OutStageWA64.lowerAll_eq_of_tables (cfg := SccCertificate.config) rfl
    Spike.Test.Hello1MainSrc.hello1o SccCertificate.gwLit
    (tables_of_stages hL SccCertificate.emitted_eq SccCertificate.tables_eq)
  -- Both runs at `configW` give the same stage (the certificate's literals).
  exact (congrArg Out.ofEmitted hW).trans
    ((ofEmitted_of_stages hL SccCertificate.emitted_eq SccCertificate.tables_eq).trans
    ((ofEmitted_of_stages (ir := SccCertificate.loweredLit.1) (setup := SccCertificate.loweredLit.2)
      SccCertificate.lowered_eq SccCertificate.emitted_eq SccCertificate.tables_eq).symm.trans
      SccCertificate.out_eqW.symm))

/-- **`hello1` from the statement**: `hello1o` is `Accepted2`
(`hello1o_accepted2`), its output is the certificate's (`hello1_out_eqA`),
which passes the placement check at `ld`'s layout `Λe` of the linked
executable (`hello1_placeOKAt`); the configuration has `CfgNeedOkA`
(`decide`); the text is the certificate's `asm`, its parse the premise
`hpa` (the certificate's compiled `#guard`, the trust boundary). -/
theorem hello1_of_closed2A (H : Closed2StmtA)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch Spike.Test.Hello1MainSrc.hello1o)
        Spike.Test.Hello1MainSrc.hello1o)
      { Spike.Test.Hello1LinkedA64.Λe with
        static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me
          Spike.Test.Hello1LinkedA64.Λe Spike.Test.Hello1MainSrc.hello1o } B
      SccCertificate.asm :=
  H SccCertificate.config SccCertificate.placeCfg Spike.Test.Hello1MainSrc.hello1o
    Spike.Test.Hello1LinkedA64.Λe Spike.Lib.LowerNode.hello1o_accepted2 (by decide)
    (hello1_out_eqA ▸ Spike.Test.Hello1LinkedA64.hello1_placeOKAt) (by decide) (hello1_out_eqA ▸ hpa) hB

/--
info: 'Spike.Lib.LowerA64.hello1_of_closed2A' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_of_closed2A

end Spike.Lib.LowerA64
