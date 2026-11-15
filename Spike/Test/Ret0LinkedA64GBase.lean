import Spike.Test.Ret0LinkedA64
import Spike.Lib.LowerA64.Correct1Tail

/-!
# `ret0.w` on AArch64 after the granule pass: the text, its parse and the linked layout

`Scc/Test/elf/ret0a64g/ret0` is `scc --granule`'s text for `ret0.w`
(`ret0.s` next to it), linked as `Ret0LinkedA64`'s. The text is the
certificate's `asm` with the pass's tail before `scc_text_end` (a `.zero`
filler, `.Lgw0:` and the descriptor word) and the `.text.scc_galign` section
after it (`asmG`, checked below). Its parse is the certificate's cells with
the end label replaced by the tail `tailG` (checked below), and the same
data sections: the output `outF := withTail outLit tailG`.

At the executable's layout `ΛG`, each component of `placeOKAt` of `outF`
holds by `decide +kernel` (`ret0G_placeOKAt`), so `ret0_linked_correctG`
is `a64_scc_correctE_text_closedAt_tail` at `ΛG`: `Ret0LinkedA64`'s statement
at the post-pass text and layout, its only premise the parse check `hpa`.
The lowering's success is `Ret0LinkedA64.ret0_placeOKAt`'s (the pre-pass
output at the pre-pass layout); no post-pass certificate is used.
-/

namespace Spike.Test.Ret0LinkedA64G

open Scc.Cert.PlaceOK
open SccCertificate (asm out outLit out_eq placeCfg)
open Spike.Lib.LowerA64 (withTail)

-- The executable is the one linked (evaluation, not a proof).
/-- info: 106c44531a613275d94c0dc9dcb932fbd0d8bf1c3ea7e4795bc9e9e1352b515a -/
#guard_msgs in
#eval do IO.println (Scc.Cert.Sha256.ofBytes (← IO.FS.readBinFile "Scc/Test/elf/ret0a64g/ret0"))

/-- The granule pass's tail as cells: the filler, `.Lgw0`, the descriptor
word (a text `.quad` reads as 8 zero bytes, `Scc/Sem/TextA64.lean`) and the
end label. -/
def tailG : List Directive :=
  [.zeros 60732, .label ".Lgw0", .byteArray ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩, .label "scc_text_end"]

/-- The post-pass text: the certificate's with the tail before the end
label and the alignment section after it. -/
def asmG : String :=
  asm.replace "scc_text_end:\n"
    ("\t.zero 60732\n.Lgw0:\n\t.quad scc_gc_desc - .\nscc_text_end:\n" ++
      "\t.section .text.scc_galign,\"ax\",%progbits\n\t.p2align 16\n\t.text\n")

-- The text linked is `asmG`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile "Scc/Test/elf/ret0a64g/ret0.s") == asmG)

-- The reader accepts the executable.
/-- info: accepted -/
#guard_msgs in
#eval Scc.Test.Elf.verdict "Scc/Test/elf/ret0a64g/ret0" pure

/-- The output with the tail. -/
abbrev outF : A64.Out := withTail outLit tailG

-- The parse of the linked text is the certificate's cells before the end label, then `tailG`
-- (evaluation; `hpa` below is the same fact).
#guard outLit.prog.getLast? == some (.label "scc_text_end")
#guard match Scc.Sem.A64.textProgram asmG with
  | .ok p => p == outF.prog
  | .error _ => false

/-! ### The placement check at the executable's layout -/

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/ret0a64g/ret0"

/-- The linked executable's layout. -/
abbrev ΛG : Scc.Sem.Layout := elf.1

-- The code base moved to a granule, `.text` is one granule, and the code fills it.
#guard ΛG.code.lo % 0x10000 == 0 && ΛG.code.size == 0x10000
#guard Scc.Sem.A64.codeEnd ΛG.code.lo outF.prog == ΛG.code.lo + ΛG.code.size

end Spike.Test.Ret0LinkedA64G
