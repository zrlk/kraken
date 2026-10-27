/-
**`hello1` from `Closed2Stmt`** (x86-64): the statement of
`Spike/Lib/LowerX64/Closed2Stmt.lean` at `hello1o` (`hello1.w` with `print`
linked), at `ld`'s layout of the linked executable
(`Spike/Test/Hello1LinkedX64.lean`).

- `hello1_out_eq`: `hello1o`'s output (four declarations) is `hello1.w`'s
  (three, `print` a stub), the certificate's `out`: `print` and `printL` are
  externs and not compiled.
- `hello1_of_closed2`: the statement at `hello1o`, from the certificate's
  facts; the parse check `hpa` (its compiled `#guard`) a premise.
-/
import Spike.Lib.LowerX64.Closed2Stmt
import Spike.Lib.Src.SrcSafe2
import Spike.Test.Hello1LinkedX64

namespace Spike.Lib.LowerX64

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **`hello1o`'s output is `hello1.w`'s** (the certificate's `out`): the
lowering of `print`'s model (`printL`, `print`) adds no code, `print` being
an extern; one kernel run of each lowering. -/
theorem hello1_out_eq :
    Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)
      SccCertificate.sizes SccCertificate.labelOffs = SccCertificate.out := by
  rw [show SccCertificate.out = _ from SccCertificate.out_eq]
  rw [show Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)
      SccCertificate.sizes SccCertificate.labelOffs = _ from
    ofEmitted_of_stages SccCertificate.sizes SccCertificate.labelOffs
      (lowered1_of_stages (fr := SccCertificate.framesLit) (r := SccCertificate.loweredLit) (by kernel_rfl)
        (by kernel_rfl))
      SccCertificate.emitted_eq]
  kernel_rfl

/-- **`hello1` from the statement**: `hello1o` is `Accepted2`
(`hello1o_accepted2`), its output is the certificate's (`hello1_out_eq`),
which passes the placement check at `ld`'s layout `Λe` of the linked
executable (`hello1_placeOKAt`); the configuration has `CfgNeedOk`
(`decide`); the text is the certificate's `asm`, its parse the premise
`hpa` (the certificate's compiled `#guard`, the trust boundary). -/
theorem hello1_of_closed2 (H : Closed2Stmt)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch Spike.Test.Hello1MainSrc.hello1o)
        Spike.Test.Hello1MainSrc.hello1o)
      { Spike.Test.Hello1LinkedX64.Λe with
        static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me
          Spike.Test.Hello1LinkedX64.Λe Spike.Test.Hello1MainSrc.hello1o } B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  H SccCertificate.config SccCertificate.placeCfg Spike.Test.Hello1MainSrc.hello1o SccCertificate.sizes
    SccCertificate.labelOffs Spike.Test.Hello1LinkedX64.Λe Spike.Lib.LowerNode.hello1o_accepted2 (by decide)
    (hello1_out_eq ▸ Spike.Test.Hello1LinkedX64.hello1_placeOKAt) (by decide) (hello1_out_eq ▸ hpa) hB

/--
info: 'Spike.Lib.LowerX64.hello1_of_closed2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_of_closed2

end Spike.Lib.LowerX64
