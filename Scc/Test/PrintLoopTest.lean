import Scc.Frontend
import Scc.Test.Src

/-!
# The output extern's loop in the frontend

`hello1L.w` writes the output extern with its WeakCore model: `print`
(`printExtD`) and its `emit` loop `printL` (`printLoopD`). The frontend takes
the loop, written textually, as part of the extern: it is neither checked
nor compiled, and no compiled block may reach it. A loop that differs from
`printLoopD` in any way is an ordinary block and is checked (its `emit` is
refused).
-/

namespace Scc.Test.PrintLoop
open CoreTerm Scc.Frontend

def hello1L : String := w_src% "Scc/Test/hello1L.w"

/-- The frontend's verdict: the externs it found, or its diagnostics. -/
def verdict (src : String) : String :=
  match run src with
  | .ok c => s!"accepted; externs {c.externs.map (·.1)}"
  | .error ds => "; ".intercalate (ds.map (·.render "t.w"))

#guard isPrintLoop printLoopD
#guard declIs printExtD printExtD
#guard externOf printLoopD == some .print
#guard externOf printExtD == some .print

/-- info: "accepted; externs [printL, print]" -/
#guard_msgs in #eval verdict hello1L

-- A loop that is not textually `printLoopD` is an ordinary block: refused.
/-- info: "t.w:39:7: error: an extern call is not in the accepted fragment (in 'printL', binding 'r')" -/
#guard_msgs in #eval verdict (hello1L.replace "let c1 = c + 1" "let c1 = c + 2")

/-- The number of `modelDiags` of `hello1L` with `main`'s body rewritten by
`f` (`none` if it does not parse). -/
def reachDiags (f : Expr → Expr) : Option Nat :=
  match Scc.Frontend.parse hello1L with
  | .ok p =>
    some (modelDiags hello1L (p.map fun d => if d.name == "main" then { d with body := f d.body } else d)).length
  | .error _ => none

-- A compiled block may not reach the loop: not as written,
#guard reachDiags id == some 0
-- by a call,
#guard reachDiags (.let_ "v" (.call "printL" [] (.lit 0) [])) == some 1
-- by a code value (`fnptr`, later called with `callc`),
#guard reachDiags (.let_ "fp" (.fnptr "printL")) == some 1
-- by a tail call in an `if` arm,
#guard reachDiags (fun e => .ifeq (.lit 0) (.lit 1) e (.tail "printL" ["q", "q"] (.var "sl") [])) == some 1
-- or in a `case` arm, under a `region`.
#guard reachDiags (fun e => .region (.unit) "r" "p" "t"
  (.case (.var "x") "l" e "rt" (.tail "printL" [] (.var "rt") []))) == some 1

end Scc.Test.PrintLoop
