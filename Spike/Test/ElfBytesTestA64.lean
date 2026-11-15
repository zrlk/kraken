import Scc.Test.ElfBytesTest
import Scc.Cert.ElfBytesA64
import Spike.Lib.A64HelloCode
import Spike.Lib.A64WakeCode

/-!
# The byte check on the AArch64 executables (P6, phase 1: `.rodata`)

`Scc.Cert.ElfBytes.bytesCheck` on the checked-in AArch64 `hello` and `wake` executables
(`Scc/Test/elf/helloa64/hello`, `Scc/Test/elf/wakea64/wake`) against their texts' `.rodata` items
(`SccCode.helloSecs`, `SccCode.wakeSecs`), the code labels resolved as the canonical loader resolves them
(`Scc.Cert.Link.A64.quadCode` with the texts' programs): the executables' `.rodata` bytes are the image the
loader lays out. Then the check's refusals, on patched copies of `hello`. The x86-64 twin is
`Spike/Test/ElfBytesTestX64.lean` (the two ISAs' modules cannot be imported together).
-/

namespace Spike.Test.ElfBytesA64

open Scc.Test.Elf Scc.Test.ElfBytes Scc.Cert.Elf Scc.Cert.ElfBytes

/-- The verdict on hello's executable patched by `p`. -/
def helloVerdict (p : ByteArray → Except String ByteArray := pure) : IO Unit :=
  bytesVerdict "Scc/Test/elf/helloa64/hello" SccCode.helloSecs.rodata
    (fun Λ => Scc.Cert.Link.A64.quadCode Λ SccCode.helloProg) p

/-- info: bytes ok -/
#guard_msgs in
#eval helloVerdict

/-- info: bytes ok -/
#guard_msgs in
#eval bytesVerdict "Scc/Test/elf/wakea64/wake" SccCode.wakeSecs.rodata
  (fun Λ => Scc.Cert.Link.A64.quadCode Λ SccCode.wakeProg)

-- The post-link call (`Scc.Cert.ElfBytes.A64.check`): silent on a match, throws on a mismatch.
#guard_msgs in
#eval Scc.Cert.ElfBytes.A64.check "Scc/Test/elf/helloa64/hello" SccCode.helloProg SccCode.helloSecs

#guard_msgs in
#eval Scc.Cert.ElfBytes.A64.check "Scc/Test/elf/wakea64/wake" SccCode.wakeProg SccCode.wakeSecs

/-- error: byte check: .rodata: 14008 bytes, the text's image needs 15040 -/
#guard_msgs in
#eval Scc.Cert.ElfBytes.A64.check "Scc/Test/elf/wakea64/wake" SccCode.helloProg SccCode.helloSecs

-- Against the other program's text (hello's, the larger stack map): refused.
/-- info: .rodata: 14008 bytes, the text's image needs 15040 -/
#guard_msgs in
#eval bytesVerdict "Scc/Test/elf/wakea64/wake" SccCode.helloSecs.rodata
  (fun Λ => Scc.Cert.Link.A64.quadCode Λ SccCode.helloProg)

/-- The file offset and size of hello's `.rodata`. -/
def roOf (b : ByteArray) : Except String (Nat × Nat) := do
  let (_, s) ← secNamed (← sections b (← header b)) ".rodata"
  return (s.offset, s.size)

-- One byte flipped: the stack map's count.
/-- info: .rodata byte 0 (address 2097592): file 255, text 28 -/
#guard_msgs in
#eval helloVerdict fun b => do return b.set! (← roOf b).1 0xff

-- A stack-map entry's code label moved by 4 (the low byte of the first entry's label).
/-- info: .rodata byte 8 (address 2097600): file 76, text 72 -/
#guard_msgs in
#eval helloVerdict fun b => do let o := (← roOf b).1; return b.set! (o + 8) ((b.get! (o + 8)) + 4)

-- The section's last byte (the image fills the section exactly: no slack today).
/-- info: .rodata byte 15039 (address 2112631): file 1, text 0 -/
#guard_msgs in
#eval helloVerdict fun b => do let (o, n) ← roOf b; return b.set! (o + n - 1) 1

-- The section grown by 8 bytes past the image (its `sh_size`), to cover bytes the text does not account
-- for: already refused by the reader, before the byte check (`.rodata` leaves its `PT_LOAD`).
/-- info: .rodata is not inside a PT_LOAD -/
#guard_msgs in
#eval helloVerdict fun b => do
  let (_, n) ← roOf b
  return put64 b ((← shdrOf b (← secIdx b ".rodata")) + 32) (n + 8)

end Spike.Test.ElfBytesA64
