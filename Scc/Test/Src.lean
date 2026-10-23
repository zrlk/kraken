import Lean

/-!
# Source files at elaboration time

`w_src% "path.w"` is the contents of a file (path relative to the package
root), read when the term is elaborated, as a string literal: the tests that
compile the `Scc/Test/*.w` programs use it.
-/

open Lean Elab Term in
/-- `w_src% "path.w"`: the contents of a file (path relative to the package
root), read at elaboration time, as a string literal. -/
elab "w_src% " path:str : term => do
  return mkStrLit (← IO.FS.readFile path.getString)
