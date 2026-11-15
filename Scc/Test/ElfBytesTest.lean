import Scc.Cert.ElfBytes
import Scc.Test.ElfTest

/-!
# Tests of the byte check (`Scc.Cert.ElfBytes`) that need no Spike literal

`bytesVerdict` (the check's verdict on a patched file) and refusals on the fixture `x` (`Scc/Test/elf/x`,
its text `x.s` read by the loader's `dataSections`), and the granule words' pieces on synthetic bytes. The
positive tests, against the hello and wake listings, are in `Spike/Test/ElfBytesTestX64.lean` and `Spike/Test/ElfBytesTestA64.lean`.
-/

namespace Scc.Test.ElfBytes

open Scc.Sem Scc.Cert.Elf Scc.Cert.ElfBytes Scc.Test.Elf

/-- The byte check's verdict on file `f` patched by `p`, with the items and resolver given. -/
def bytesVerdict (f : String) (items : List Kraken.DataImage.Item) (code : Layout → String → Option Nat)
    (p : ByteArray → Except String ByteArray := pure) : IO Unit := do
  match p (← IO.FS.readBinFile f) >>= fun b => bytesCheck b items code with
  | .ok () => IO.println "bytes ok"
  | .error e => IO.println e

/-- The `.rodata` items of the fixture `x` (its listing `x.s`, read by the loader's `dataSections`). -/
def xItems : IO (List Kraken.DataImage.Item) := do
  let some d := dataSections (← IO.FS.readFile "Scc/Test/elf/x.s") | throw (IO.userError "x.s: no data sections")
  return d.rodata

-- Code labels unresolved (every `.quad` of a code label 0, as no loader lays it out): the first stack-map
-- entry's label differs (byte 8, the low byte of `.Lscc_rt_start.x0`'s address `0x401057`).
/-- info: .rodata byte 8 (address 4206600): file 87, text 0 -/
#guard_msgs in
#eval do bytesVerdict "Scc/Test/elf/x" (← xItems) fun _ _ => none

-- `.rodata` shrunk by 16 bytes (its `sh_size`): the text's image no longer fits.
/-- info: .rodata: 424 bytes, the text's image needs 440 -/
#guard_msgs in
#eval do bytesVerdict "Scc/Test/elf/x" (← xItems) (fun _ _ => none) fun b => do
  return put64 b ((← shdrOf b (← secIdx b ".rodata")) + 32) (0x1b8 - 16)

/-! ## The granule words -/

-- The word of granule `k` is its last 8 bytes; `.quad scc_gc_desc - .` is the difference modulo `2 ^ 64`.
#guard wordAddr 0x400000 0 == 0x40fff8 && wordAddr 0x400000 2 == 0x42fff8
#guard wordVal 0x410008 0x40fff8 == 16 && wordVal 0x40fff0 0x40fff8 == 2 ^ 64 - 8

/-- One granule of zeros at `lo` with the word `.quad scc_gc_desc - .` for the descriptor at `d`. -/
def oneGranule (lo d : Nat) : ByteArray :=
  put64 (ByteArray.mk (Array.replicate granule 0)) (granule - 8) (wordVal d (wordAddr lo 0))

#guard badWords (oneGranule 0x400000 0x410040) 0x400000 0x410040 1 == []
-- Another descriptor address: the word differs (its granule, address and file value).
#guard badWords (oneGranule 0x400000 0x410040) 0x400000 0x410048 1 == [(0, 0x40fff8, some 72)]
-- A second granule the bytes do not have: no file value.
#guard badWords (oneGranule 0x400000 0x410040) 0x400000 0x410040 2 == [(1, 0x41fff8, none)]

end Scc.Test.ElfBytes
