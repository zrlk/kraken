import Scc.Cert.ElfBytes
import Scc.Cert.LinkX64

/-!
# The byte check on x86-64

`Scc.Cert.ElfBytes.bytesCheck` with the canonical x86-64 loader's resolution of the `.rodata` quads
(`Scc.Cert.Link.X64.quadCode` of the text's cells), and `check`, its `IO` wrapper on a file: the call a
certificate's post-link file makes (an `#eval` that throws on a mismatch). The AArch64 twin is
`Scc/Cert/ElfBytesA64.lean` (the two ISAs' link modules cannot be imported together). Untrusted until
`Scc/Test/certify.sh` imports it.
-/

namespace Scc.Cert.ElfBytes.X64

/-- The byte check of the x86-64 executable `b` against a text's cells and data sections. -/
def bytesOk (b : ByteArray) (cells : List (Directive × Nat)) (secs : Scc.Sem.DataSecs) : Except String Unit :=
  bytesCheck b secs.rodata fun Λ => Scc.Cert.Link.X64.quadCode Λ cells

/-- **The byte check of the file at `path`**: throws `byte check: …` on a mismatch. -/
def check (path : String) (cells : List (Directive × Nat)) (secs : Scc.Sem.DataSecs) : IO Unit := do
  match bytesOk (← IO.FS.readBinFile path) cells secs with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"byte check: {e}")

end Scc.Cert.ElfBytes.X64
