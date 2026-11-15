import Scc.Test.ElfBytesTest
import Scc.Cert.ElfBytesX64
import Spike.Lib.X64HelloCode
import Spike.Lib.X64WakeCode

/-!
# The byte check on the x86-64 executables (P6, phase 1: `.rodata`)

`Scc.Cert.ElfBytes.bytesCheck` on the checked-in x86-64 `hello` and `wake` executables
(`Scc/Test/elf/hellox64/hello`, `Scc/Test/elf/wakex64/wake`) against their texts' `.rodata` items
(`SccCode.helloSecs`, `SccCode.wakeSecs`), the code labels resolved as the canonical loader resolves them
(`Scc.Cert.Link.X64.quadCode` with the texts' cells): the executables' `.rodata` bytes are the image the
loader lays out. Then the check's refusals, on patched copies of `hello`. The AArch64 twin is
`Spike/Test/ElfBytesTestA64.lean` (the two ISAs' modules cannot be imported together).
-/

namespace Spike.Test.ElfBytesX64

open Scc.Test.Elf Scc.Test.ElfBytes Scc.Cert.Elf Scc.Cert.ElfBytes

/-- The verdict on hello's executable patched by `p`. -/
def helloVerdict (p : ByteArray → Except String ByteArray := pure) : IO Unit :=
  bytesVerdict "Scc/Test/elf/hellox64/hello" SccCode.helloSecs.rodata
    (fun Λ => Scc.Cert.Link.X64.quadCode Λ SccCode.helloCells) p

/-- info: bytes ok -/
#guard_msgs in
#eval helloVerdict

/-- info: bytes ok -/
#guard_msgs in
#eval bytesVerdict "Scc/Test/elf/wakex64/wake" SccCode.wakeSecs.rodata
  (fun Λ => Scc.Cert.Link.X64.quadCode Λ SccCode.wakeCells)

-- The post-link call (`Scc.Cert.ElfBytes.X64.check`): silent on a match, throws on a mismatch.
#guard_msgs in
#eval Scc.Cert.ElfBytes.X64.check "Scc/Test/elf/hellox64/hello" SccCode.helloCells SccCode.helloSecs

#guard_msgs in
#eval Scc.Cert.ElfBytes.X64.check "Scc/Test/elf/wakex64/wake" SccCode.wakeCells SccCode.wakeSecs

/-- error: byte check: .rodata: 13728 bytes, the text's image needs 14856 -/
#guard_msgs in
#eval Scc.Cert.ElfBytes.X64.check "Scc/Test/elf/wakex64/wake" SccCode.helloCells SccCode.helloSecs

-- Against the other program's text (hello's, the larger stack map): refused.
/-- info: .rodata: 13728 bytes, the text's image needs 14856 -/
#guard_msgs in
#eval bytesVerdict "Scc/Test/elf/wakex64/wake" SccCode.helloSecs.rodata
  (fun Λ => Scc.Cert.Link.X64.quadCode Λ SccCode.helloCells)

/-- The file offset and size of hello's `.rodata`. -/
def roOf (b : ByteArray) : Except String (Nat × Nat) := do
  let (_, s) ← secNamed (← sections b (← header b)) ".rodata"
  return (s.offset, s.size)

-- One byte flipped: the stack map's count.
/-- info: .rodata byte 0 (address 4206592): file 255, text 28 -/
#guard_msgs in
#eval helloVerdict fun b => do return b.set! (← roOf b).1 0xff

-- A stack-map entry's code label moved by 4 (the low byte of the first entry's label).
/-- info: .rodata byte 8 (address 4206600): file 91, text 87 -/
#guard_msgs in
#eval helloVerdict fun b => do let o := (← roOf b).1; return b.set! (o + 8) ((b.get! (o + 8)) + 4)

-- The section's last byte (the image fills the section exactly: no slack today).
/-- info: .rodata byte 14855 (address 4221447): file 1, text 255 -/
#guard_msgs in
#eval helloVerdict fun b => do let (o, n) ← roOf b; return b.set! (o + n - 1) 1

-- The section grown by 8 bytes past the image (its `sh_size`), to cover bytes the text does not account
-- for: already refused by the reader, before the byte check (`.rodata` leaves its `PT_LOAD`).
/-- info: .rodata is not inside a PT_LOAD -/
#guard_msgs in
#eval helloVerdict fun b => do
  let (_, n) ← roOf b
  return put64 b ((← shdrOf b (← secIdx b ".rodata")) + 32) (n + 8)

end Spike.Test.ElfBytesX64
