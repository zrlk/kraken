import Scc.Cert.ElfBytes
import Scc.Cert.LinkA64

/-!
# The byte check on AArch64

`Scc.Cert.ElfBytes.bytesCheck` with the canonical AArch64 loader's resolution of the `.rodata` quads
(`Scc.Cert.Link.A64.quadCode` of the text's program), and `check`, its `IO` wrapper on a file: the call a
certificate's post-link file makes (an `#eval` that throws on a mismatch). The x86-64 twin is
`Scc/Cert/ElfBytesX64.lean` (the two ISAs' link modules cannot be imported together). Untrusted until
`Scc/Test/certify.sh` imports it.
-/

namespace Scc.Cert.ElfBytes.A64

/-- The byte check of the AArch64 executable `b` against a text's program and data sections. -/
def bytesOk (b : ByteArray) (prog : Program) (secs : Scc.Sem.DataSecs) : Except String Unit :=
  bytesCheck b secs.rodata fun Λ => Scc.Cert.Link.A64.quadCode Λ prog

/-- **The byte check of the file at `path`**: throws `byte check: …` on a mismatch. -/
def check (path : String) (prog : Program) (secs : Scc.Sem.DataSecs) : IO Unit := do
  match bytesOk (← IO.FS.readBinFile path) prog secs with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"byte check: {e}")

end Scc.Cert.ElfBytes.A64
