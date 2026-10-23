import Scc.Cert.PlaceOK

/-!
# A value as a literal (`scc --cert`)

A certificate decides `placeOK` of `out`, scc's output computed from the
source term by `lowerAll` and the placement data. Each decision that
mentions `out` makes the kernel run the lowering again, which costs more
than the check itself. So the certificate states the value once as a literal,
`outLit := scc_lit% out`, checks `out = outLit` once in the kernel, and
decides the components of `placeOK` on the literal.

`scc_lit% c`, for a constant `c` whose type has a `Lean.ToExpr` instance,
evaluates `c` at elaboration time (compiled code: untrusted) and returns
`toExpr` of its value. The equation the certificate proves is what makes
the literal trusted. The `ToExpr` instances here are the ISA-generic ones
the outputs need: the data sections and `PlaceOK.Out`. The ISAs' are in
`Scc/Cert/OutLitA64.lean` and `OutLitX64.lean`. The certificate checks
`out = outLit` in three steps on literals (`Scc/Cert/OutStageA64.lean`,
`OutStageX64.lean`), each a smaller kernel check.
-/

deriving instance Lean.ToExpr for Kraken.DataImage.Item
deriving instance Lean.ToExpr for Scc.Sem.DataSecs
deriving instance Lean.ToExpr for Scc.Cert.PlaceOK.Out

namespace Scc.Cert.OutLit

open Lean Elab Term Meta in
/-- `scc_lit% c`, `c` a constant whose type has a `Lean.ToExpr` instance:
evaluate `c` at elaboration time and return its value as a literal
(`toExpr`). -/
elab "scc_lit% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let e ← elabTerm (← `(Lean.toExpr $(mkIdent n))) (some (mkConst ``Lean.Expr))
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "scc_lit%: no `Lean.ToExpr` instance for the type of {n}"
  unsafe evalExpr Expr (mkConst ``Lean.Expr) e

/-- A small example: a list of data items, as a literal, equal to its
definition. -/
private def items : List Kraken.DataImage.Item := [.label "a", .quad (-1), .zero 3]

private def itemsLit : List Kraken.DataImage.Item := scc_lit% items

example : items = itemsLit := rfl

end Scc.Cert.OutLit
