import Scc.Frontend

/-!
# A WeakCore program as a Lean term (`scc --cert`)

A certificate decides properties of `lowerAll cfg p` by the kernel, so it
needs the source program `p` as a term: the frontend's parser is `partial`,
and the kernel does not reduce `Frontend.run`. `progTerm p` is the text of a
Lean term for `p` (the derived `Repr` forms of its parts, fully qualified),
which `scc --cert` writes into the certificate; `reads src p` checks, by
evaluation, that the frontend reads the source text `src` as `p`, by
comparing the printed forms (`Decl` has no equality instance). The term is
an input of the certificate checked by that `#guard`, like the parse of the
assembler text.
-/

namespace Scc.Cert.SrcTerm

open CoreTerm

/-- The text of a Lean term for a block: one field per line, each at
column 4 (a structure instance's fields must start in one column), the
lines of a field's value nested deeper (column 6 on), so that they continue
the field. -/
def declTerm (d : Decl) : String :=
  let f (s : Std.Format) : String := (s.nest 6).pretty 100
  "{\n    name := " ++ f (repr d.name) ++ ",\n    tparams := " ++ f (repr d.tparams) ++
    ",\n    idx := " ++ f (repr d.idx) ++ ",\n    arg := " ++ f (repr d.arg) ++
    ",\n    argTy := " ++ f (repr d.argTy) ++ ",\n    retTy := " ++ f (repr d.retTy) ++
    ",\n    body := " ++ f (repr d.body) ++ " }"

/-- **The text of a Lean term for a program**: a list literal of its
blocks (`declTerm`). -/
def progTerm (p : Prog) : String :=
  "[" ++ ",\n  ".intercalate (p.map declTerm) ++ "]"

/-- **The frontend reads `src` as `p`** (`Frontend.run`, compared by
`progTerm`). -/
def reads (src : String) (p : Prog) : Bool :=
  match Frontend.run src with
  | .ok c => progTerm c.prog == progTerm p
  | .error _ => false

end Scc.Cert.SrcTerm
