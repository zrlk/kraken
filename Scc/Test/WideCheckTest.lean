import Scc.Cert.WideCheckA64
import Scc.Sem.TargetA64
import Scc.Cert.Blocks

/-!
# `scc --code`'s fragment check reads the program the loader reads

`Scc.Cert.WideCheckA64.progOf` restates the canonical loader's parser
(`scc-arm` cannot import the loader's modules); the equations hold by `rfl`.
`Scc.Cert.Blocks.code` with the check refuses a listing outside the
fragment.
-/

namespace Scc.Test.WideCheck

example : Scc.Cert.WideCheckA64.textOf = Scc.Sem.textSection := rfl

example : Scc.Cert.WideCheckA64.progOf = Scc.Sem.A64.textProgram := rfl

/-- `scc --code` refuses a listing with a store outside the fragment, before
reading its blocks. -/
def refusal (asm : String) : String :=
  match Scc.Cert.Blocks.code .arm "t.w" asm (some Scc.Cert.WideCheckA64.check) with
  | .ok _ => "ok"
  | .error m => m

/--
info: "1 store(s) outside the certified one-word fragment (str/stur/stlr w, strb/strh/sturb/sturh, stp, stxr/stxp, casp, and sub-word swp/cas/ld<op>), which the code check does not cover yet: line 4: strb w9, [x10]"
-/
#guard_msgs in
#eval refusal ".text\n.globl f\nf:\n  strb w9, [x10]\n  ret\n"

end Scc.Test.WideCheck
