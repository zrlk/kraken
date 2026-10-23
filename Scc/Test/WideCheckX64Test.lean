import Scc.Cert.WideCheckX64
import Scc.Sem.TargetX64
import Scc.Cert.Blocks

/-!
# `scc --arch x64 --code`'s fragment check reads the program the loader reads

`Scc.Cert.WideCheckX64.progOf` restates the canonical x64 loader's parser
(`scc-x64` cannot import the loader's modules); the equations hold by `rfl`.
`Scc.Cert.Blocks.code` with the check refuses a listing outside the
fragment.
-/

namespace Scc.Test.WideCheckX64

example : Scc.Cert.WideCheckX64.textOf = Scc.Sem.textSection := rfl

example : Scc.Cert.WideCheckX64.progOf = Scc.Sem.X64.textProgram := rfl

/-- `scc --arch x64 --code` refuses a listing with a memory write outside the
fragment, before reading its blocks. -/
def refusal (asm : String) : String :=
  match Scc.Cert.Blocks.code .x64 "t.w" asm (some Scc.Cert.WideCheckX64.check) (some ([], [])) with
  | .ok _ => "ok"
  | .error m => m

/--
info: "1 instruction(s) outside the certified one-word fragment (every memory write 8 bytes: movb/movw/movl or another 1/2/4-byte memory destination (setcc to memory, pushw, narrow lock/xchg/xadd/cmpxchg/movnti), vector stores (movups/movaps/movdqa/movdqu/... to memory) and cmpxchg16b are refused), which the code check does not cover yet: line 4: movw %ax, (%rdi)"
-/
#guard_msgs in
#eval refusal ".text\n.globl f\nf:\n\tmovw %ax, (%rdi)\n\tret\n"

end Scc.Test.WideCheckX64
