import Scc.Frontend
import Scc.Sem.PubFree
import Scc.Test.Src

/-!
# Publish-free programs

`Scc.Sem.PubFree.ProgPubFree` (no `let _ = publish _` in any code block)
lets M1 take its typing facts from WeakCore's token soundness theorems with
no run fact left. `hello1.w`, the single-thread hello, is publish-free;
`hello.w` (which publishes its slice and its flag) is not.
-/

namespace Scc.Test.PubFree
open Scc.Sem.PubFree

/-- The frontend's program for a source text, and whether it is
publish-free (`ProgPubFree`, decided). -/
def pubFreeOf (src : String) : Except String Bool :=
  match Frontend.run src with
  | .ok c => .ok (decide (ProgPubFree c.prog))
  | .error ds => .error (String.intercalate "\n" (ds.map (·.render "input")))

/-- info: Except.ok true -/
#guard_msgs in #eval pubFreeOf (w_src% "Scc/Test/hello1.w")

/-- info: Except.ok false -/
#guard_msgs in #eval pubFreeOf (w_src% "Scc/Test/hello.w")

end Scc.Test.PubFree
