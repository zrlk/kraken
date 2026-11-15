/-
**The x86-64 open premises `Rest2X` for every `Accepted2` program**, with no
premises beyond the instance's (the level below `closed2Stmt_x64_final`'s
`CorrectE`): `rest2X_ofInW` at `closed2InW_at` with the producers
`closed2Stmt_x64_tg` passes at `tgOkBStmt`. For a consumer that moves
`Rest2X` to another output before `correct2_of` (a post-pass output,
`Spike/Lib/X64Correct2Tail.lean`).
-/
import Spike.Lib.LowerX64.G1Closed2X64

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **`Rest2X` at the compiler's output for every `Accepted2` program** at a
configuration with the header bound, every admissible entry state and
placement check at the theorem's layout. -/
theorem rest2X_x64_final (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22)
    (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat) (labelOffs : List (String × Nat))
    (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted2 p = true) (hR : Scc.Lower.mainRetOk p = true)
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hcfg : CfgNeedOk pcfg = true) (arch : WeakMem.Arch) (E : Entry) (hE : E.Ok (lay2 Λ p))
    (h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    Rest2X (lay2 Λ p) p h' arch E :=
  rest2X_ofInW h' hE (closed2InW_at fnSpecC2Stmt tgOkBStmt (mainSeg2Stmt_ofL mainSeg2LStmt_of)
    (huSetupStmt_of (mainSeg2Stmt_ofL mainSeg2LStmt_of)) (h1SetupStmt_ofMainSeg2L mainSeg2LStmt_of)
    h0NoSetupStmt cfg hobj pcfg p sizes labelOffs Λ hp hR h hcfg E hE h')

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.rest2X_x64_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.rest2X_x64_final
