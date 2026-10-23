import Scc.Cert.Elf

/-!
# Tests of the ELF layout reader

`Scc/Test/elf/` holds the runtime-only program `ret0` emitted for both ISAs,
with the regions of their own last in `.bss` (`x.s`, `a.s`), and linked
statically: `x` for x86-64 (GNU `as`, `ld -static`), `a` for AArch64
(`clang -c`, `ld.lld -static` with `ins.ld`, which places `.rodata` after
`.text`), and `a_def`, `a.s` linked by `ld.lld` with its default script,
which places `.rodata` below `.text`. `x.s` and `a.s` are scc's listings of
`ret0` with the three regions' blocks moved to the end of `.bss`, each with
`.type` and `.size`, and `.data` 16-aligned, as the reader expects of the
emitter. `Scc/Test/elf.sh` rebuilds the executables and checks the reader
against `readelf`.

The positive tests embed each layout with `scc_elf_layout%` and check it
field by field; the negative ones patch bytes of a good file and check the
reader's refusal.
-/

namespace Scc.Test.Elf

open Scc.Sem Scc.Cert Scc.Cert.Elf

/-- The x86-64 executable's layout and digest. -/
def x64 : Layout × String := scc_elf_layout% "Scc/Test/elf/x"

/-- The AArch64 executable's layout and digest. -/
def a64 : Layout × String := scc_elf_layout% "Scc/Test/elf/a"

#guard x64.2 == "7db9ce573ee918cae04f6004bf334ba09930d7b945f6bac9cfd531efccc3ba09"
#guard x64.1.code == ⟨0x401000, 0x1238⟩
#guard x64.1.rodata == ⟨0x403000, 0x1b8⟩
#guard x64.1.data == ⟨0x4041c0, 0x4842e0 - 0x4041c0⟩
#guard x64.1.heap == ⟨0x4842e0, 0x4000000⟩
#guard x64.1.pinned == ⟨0x44842e0, 0x20000⟩
#guard x64.1.stackPool == ⟨0x44a42e0, 0x20000000⟩
#guard x64.1.image.length == 23 && x64.1.image.head? == some (0x4041c0, 1)
#guard x64.1.symbols.lookup "scc_rt_heap_use" == some 0x404290
#guard x64.1.symbols.lookup "scc_rt_nthreads" == some 0x4842d8
#guard x64.1.symbols.lookup "scc_rt_msg5" == some 0x40426a
#guard x64.1.symbols.lookup "scc_stackmap" == none
#guard x64.1.symbols.lookup "_edata" == none
#guard x64.1.symbols.length == 16
#guard Link.wfB x64.1

#guard a64.2 == "979a11dc3c58457c5ea8b6055888f6cc76911855f242296860faf0b08d124fc6"
#guard a64.1.code == ⟨0x210190, 0x1298⟩
#guard a64.1.rodata == ⟨0x221428, 0x1b8⟩
#guard a64.1.data == ⟨0x2315e0, 0x2b1700 - 0x2315e0⟩
#guard a64.1.heap == ⟨0x2b1700, 0x4000000⟩
#guard a64.1.pinned == ⟨0x42b1700, 0x20000⟩
#guard a64.1.stackPool == ⟨0x42d1700, 0x20000000⟩
#guard a64.1.image.length == 23 && a64.1.image.head? == some (0x2315e0, 1)
#guard a64.1.symbols.lookup "scc_rt_stack_free" == some 0x231738
#guard a64.1.symbols.lookup "scc_rt_abort_heap_exit" == none
#guard a64.1.symbols.length == 16
#guard Link.wfB a64.1

-- The two ISAs' images agree: the same `.data` bytes, at different bases.
#guard x64.1.image.map (·.2) == a64.1.image.map (·.2)

/-! ## Refusals -/

/-- Write the 64-bit little-endian `v` at `off`. -/
def put64 (b : ByteArray) (off v : Nat) : ByteArray :=
  (List.range 8).foldl (fun b j => b.set! (off + j) (UInt8.ofNat (v / 2 ^ (8 * j) % 256))) b

/-- The entry offset of symbol `n`. -/
def entryOf (b : ByteArray) (n : String) : Except String Nat := do
  let secs ← sections b (← header b)
  let some s := (← symTable b secs).find? (·.name == n) | throw s!"no {n}"
  return s.entry

/-- The reader's verdict on file `f` patched by `p`. -/
def verdict (f : String) (p : ByteArray → Except String ByteArray) : IO Unit := do
  let b ← IO.FS.readBinFile f
  match p b >>= elfParts with
  | .ok _ => IO.println "accepted"
  | .error e => IO.println e

-- `ld.lld`'s default script puts `.rodata` below the code: refused while the loaders place data
-- symbols after it (`refuseBelowCode`).
/-- info: data symbol scc_stackmap below the code -/
#guard_msgs in
#eval verdict "Scc/Test/elf/a_def" pure

/-- info: accepted -/
#guard_msgs in
#eval verdict "Scc/Test/elf/x" pure

-- The entry point (`e_entry`, offset 24) one instruction past the start of `.text`: Linux would not
-- enter at `_start`.
/-- info: the entry point 4198404 is not the start of .text (4198400) -/
#guard_msgs in
#eval verdict "Scc/Test/elf/x" fun b => pure (put64 b 24 0x401004)

/-- info: truncated: no bytes [12288, 12728) -/
#guard_msgs in
#eval verdict "Scc/Test/elf/x" fun b => pure (b.extract 0 0x3000)

/-- info: truncated: no byte at offset 63 -/
#guard_msgs in
#eval verdict "Scc/Test/elf/x" fun b => pure (b.extract 0 63)

/-- info: unknown machine 40 -/
#guard_msgs in
#eval verdict "Scc/Test/elf/x" fun b => pure (b.set! 18 40)

-- The code's `PT_LOAD` (the second) without `PF_X`.
/-- info: .text: its PT_LOAD has flags 4, not 5 -/
#guard_msgs in
#eval verdict "Scc/Test/elf/x" fun b => pure (b.set! (64 + 56 + 4) 4)

-- The pinned region moved onto the heap arena.
/-- info: overlapping regions -/
#guard_msgs in
#eval verdict "Scc/Test/elf/a" fun b => do return put64 b ((← entryOf b "scc_rt_pinned") + 8) 0x2b1700

-- A region of size 0.
/-- info: scc_rt_stacks has size 0 -/
#guard_msgs in
#eval verdict "Scc/Test/elf/x" fun b => do return put64 b ((← entryOf b "scc_rt_stacks") + 16) 0

-- No heap arena: its symbol renamed (to `scc_rt_heap_use`, by its name's string table offset).
/-- info: no symbol scc_rt_heap -/
#guard_msgs in
#eval verdict "Scc/Test/elf/x" fun b => do
  let e ← entryOf b "scc_rt_heap_use"
  let h ← entryOf b "scc_rt_heap"
  return (List.range 4).foldl (fun c j => c.set! (h + j) (b.get! (e + j))) b

-- A region outside the zero-filled tail (on `.data`).
/-- info: scc_rt_heap is not in the zero-filled tail of the writable PT_LOAD -/
#guard_msgs in
#eval verdict "Scc/Test/elf/x" fun b => do return put64 b ((← entryOf b "scc_rt_heap") + 8) 0x4041c0

-- A data symbol inside the code.
/-- info: data symbol scc_rt_msg1 inside the code -/
#guard_msgs in
#eval verdict "Scc/Test/elf/x" fun b => do return put64 b ((← entryOf b "scc_rt_msg1") + 8) 0x401004

-- A data symbol below the code.
/-- info: data symbol scc_rt_msg1 below the code -/
#guard_msgs in
#eval verdict "Scc/Test/elf/a" fun b => do return put64 b ((← entryOf b "scc_rt_msg1") + 8) 0x200000

-- A data symbol above the heap arena's start that is not a region.
/-- info: data symbol scc_rt_msg1 at or above the heap arena -/
#guard_msgs in
#eval verdict "Scc/Test/elf/x" fun b => do return put64 b ((← entryOf b "scc_rt_msg1") + 8) 0x4842e8

end Scc.Test.Elf
