/-
**`hello1` as a corollary of the generic `Accepted2` theorem** (x86-64; the
twin of `Spike/Test/A64Hello1G1.lean`):

- `hello1_hobj`: the header bound at `hello1`'s configuration (the
  configuration premise of `Closed2StmtH`);
- `hello1_finalC_g1Fin`: `hello1_finalC`'s statement
  (`Spike/Test/X64Hello1FinalC.lean`) as a corollary of the unconditional
  generic theorem `closed2Stmt_x64_final`
  (`Spike/Lib/LowerX64/G1Closed2X64.lean`) at `hello1`'s configuration and
  `ld`'s layout of the linked executable.
-/
import Spike.Lib.LowerX64.G1Closed2X64
import Spike.Test.X64Hello1Closed2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- **The header bound at `hello1`'s configuration** (the premise `hobj`
of `Closed2StmtH` there). -/
theorem hello1_hobj : Scc.Obj.nShift SccCertificate.config.layout.obj < 22 := by decide

/-- **`hello1`'s x86-64 statement from the generic theorem**
(`hello1_finalC`'s conclusion and parse hypothesis `hpa`):
`closed2Stmt_x64_final` at `hello1`'s configuration and the header bound
`hello1_hobj`. `hello1o` is `Accepted2` (`hello1o_accepted2`), its output is
the certificate's (`hello1_out_eq`, `out_eq`), which passes the placement
check at `ld`'s layout (`hello1_placeOKAt`); `mainRetOk` and `CfgNeedOk` by
decision. -/
theorem hello1_finalC_g1Fin
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Le P1) B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  closed2Stmt_x64_final SccCertificate.config hello1_hobj SccCertificate.placeCfg P1 SccCertificate.sizes
    SccCertificate.labelOffs Le Spike.Lib.LowerNode.hello1o_accepted2 (by decide)
    (hello1_out_eq ▸ Spike.Test.Hello1LinkedX64.hello1_placeOKAt) (by decide)
    (hello1_out_eq ▸ SccCertificate.out_eq ▸ hpa) hB

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_hobj' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_hobj

/-- info: 'Spike.Lib.LowerX64.hello1_finalC_g1Fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_finalC_g1Fin
