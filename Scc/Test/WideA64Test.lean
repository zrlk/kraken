import Scc.Cert.Rt.WideA64
import Scc.Test.AllocOrderA64

/-!
# The one-word AArch64 fragment on scc's listings

`Scc/Cert/Rt/WideA64.lean`: `wideIn` holds of the parsed AArch64 listing of
`Scc/Test/hello1.w` and `Scc/Test/hello.w` (every store is `str x`/`stur x`/`stlr x`, every
read-modify-write is `swp x`/`ld<op> x`/`cas x`), so the certification
semantics of its canonical thread writes words only (`wideSt_threadAt`,
`certExec_w8`). Narrow, pair and exclusive stores are refused.
-/

namespace Scc.Test.WideA64

open Scc.Cert.WideA64 Scc.Sem.A64

/-- `wideIn` of the parsed listing; `none` if it does not parse. -/
def wideOf (asm : String) : Option Bool := (textProgram asm).toOption.map wideIn

-- `hello1.w` (1450 directives) and `hello.w`.
#guard Scc.Test.AllocOrderA64.hello1 != "" && Scc.Test.AllocOrderA64.hello != ""
#guard wideOf Scc.Test.AllocOrderA64.hello1 = some true
#guard wideOf Scc.Test.AllocOrderA64.hello = some true

-- The fragment's stores and read-modify-writes.
#guard wideOf "str x0, [x1]\nstr x0, [sp, #8]\nstur x0, [x1, #-8]\nstr x0, [x1, x2, lsl #3]\n\
stlr x0, [x1]\nswpal x0, x2, [x1]\nldaddal x0, x2, [x1]\ncasal x0, x2, [x1]\nldr w0, [x1]\nldrb w0, [x1]" =
  some true

-- Everything else that writes memory is refused, one at a time.
#guard ["str w0, [x1]", "stur w0, [x1]", "strb w0, [x1]", "strh w0, [x1]", "sturb w0, [x1]",
  "sturh w0, [x1]", "stp x0, x1, [sp]", "stlr w0, [x1]", "stlrb w0, [x1]", "swpal w0, w2, [x1]",
  "casal w0, w2, [x1]", "ldaddal w0, w2, [x1]", "stxr w3, x0, [x1]", "stxp w3, x0, x1, [x2]",
  "casp x0, x1, x2, x3, [x4]"].all fun l => wideOf l = some false

end Scc.Test.WideA64
