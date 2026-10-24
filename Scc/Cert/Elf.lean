import Scc.Cert.Link
import Scc.Cert.Sha256

/-!
# The layout of a linked executable, read from its ELF file

Certification after the link: `elfLayout bytes` reads the layout `Λ`
(`Scc.Sem.Layout`) the static linker gave an emitted text from the
executable it wrote, an ELF64 little-endian `ET_EXEC` file for x86-64
(`EM_X86_64`) or AArch64 (`EM_AARCH64`), and fails closed: any part of the
file it does not expect is an error, never a guess.

The reader is total: every field is read with a bounds check (`u8`, …,
`u64`), and a truncated or inconsistent file is an `Except.error`. It reads
the file header (`Header`), the program headers (`Phdr`), the section headers
(`Shdr`, named from `.shstrtab`) and the symbol table (`Sym`, named from its
string table).

The layout (`ElfLayout`, then `ElfLayout.toLayout`):

- `code` is the `.text` section, inside a `PT_LOAD` mapped `R+X` (not `W`),
  and the entry point (`e_entry`) is its start, where A1 puts `_start`;
- `rodata` is the `.rodata` section (empty if there is none), inside a
  `PT_LOAD` mapped `R` only, 8-aligned (`rodataFits`), clear of the regions;
- the **heap arena**, the **pinned region** and the **stack pool** are the
  symbols `scc_rt_heap`, `scc_rt_pinned` and `scc_rt_stacks`
  (`Link.heapSym`, …): `[st_value, st_value + st_size)`, each a non-empty
  `OBJECT` of `.bss`, which the emitter places last in `.bss`, so that they
  lie in the zero-filled tail (`p_memsz > p_filesz`) of the writable
  `PT_LOAD`;
- `data` is `[.data, heap)`: `.data` and the runtime's words in `.bss` before
  the regions; the writable `PT_LOAD` (`R+W`, not `X`) starts at `.data`, its
  file part is exactly `.data`, and `.bss` is its zero-filled tail;
- `image` is the non-zero 8-byte words of the bytes the loader maps at
  `.data` (`Link.addBytes`), read through the program header;
- `symbols` is the `LOCAL` `NOTYPE`/`OBJECT` symbols of `.data` and `.bss`,
  the regions' among them. Not symbols: the mapping symbols (`$x`, `$d`),
  `FILE`, `SECTION` and `FUNC` symbols, absolute and undefined ones, the
  linker's `__bss_start`, `_edata` and `_end`, and the labels of `.text` and
  `.rodata` (the loader resolves those in the text it loads);
- `static` places nothing (the fallback), the abort labels are
  `Link.abortName`, and the other fields have their defaults.

The one other mapped section the reader accepts is the linker's build-id
note, `.note.gnu.build-id` (`ld.lld`'s default, `--build-id`): it is no part
of the layout, and is accepted only as an `SHT_NOTE` section mapped
read-only (`SHF_ALLOC`, neither `SHF_WRITE` nor `SHF_EXECINSTR`), inside a
`PT_LOAD` mapped `R` only, from its file bytes, disjoint from the code,
`.rodata`, `.data`, `.bss` and the regions, and with no symbol in it or
defined in it (`buildIdNote`).

Fail closed: the reader refuses a file whose entry point is not the start
of `.text`, a file with a section it does not know that
is mapped (`SHF_ALLOC`), a build-id note that is not as above, a dynamic or
relocation section, a program header other than `PT_LOAD`, `PT_PHDR`, `PT_NOTE`, `PT_GNU_STACK` and
`PT_GNU_PROPERTY`, an executable stack, overlapping `PT_LOAD`s, a `PT_LOAD`
both writable and executable, more than one writable `PT_LOAD`; a data symbol
(of `.data`, `.bss` or `.rodata`) inside the code, or, while
`refuseBelowCode` holds, below it (`symsAbove`, `Scc/Sem/Target.lean`); a
data symbol that is not `LOCAL`, or of `.data`/`.bss` at or above the heap
arena but for the regions; and a layout that is not well-formed (`wfB`).

`scc_elf_layout% "path"` reads a file (path relative to the package root) at
elaboration time and is the pair of its layout, as a literal, and the
SHA-256 of the file (`Sha256.ofBytes`): the trust is that of `#guard`, the
evaluation of `elfLayout` by the elaborator. `Scc/Test/ElfTest.lean` tests
it on linked executables of both ISAs, and `Scc/Test/elf.sh` checks them
against `readelf`.
-/

namespace Scc.Cert.Elf

open Scc.Sem

/-- Whether a data symbol below the code is refused. Off: the loaders
place data symbols on both sides of the code (`placeBelow`,
`cellsAround`), and the placement check's loader check accepts them
(`Link.A64.loadOk`'s and `Link.X64.loadOk`'s `symsAround` and `noClash`);
one inside the code is still refused (`Link.containsB code`, `symsAbove`). -/
def refuseBelowCode : Bool := false

/-! ## Little-endian fields -/

/-- The byte at `i`. -/
def u8 (b : ByteArray) (i : Nat) : Except String Nat :=
  match b[i]? with
  | some x => .ok x.toNat
  | none => .error s!"truncated: no byte at offset {i}"

/-- The 16-bit little-endian field at `i`. -/
def u16 (b : ByteArray) (i : Nat) : Except String Nat := do
  return (← u8 b i) + 256 * (← u8 b (i + 1))

/-- The 32-bit little-endian field at `i`. -/
def u32 (b : ByteArray) (i : Nat) : Except String Nat := do
  return (← u16 b i) + 2 ^ 16 * (← u16 b (i + 2))

/-- The 64-bit little-endian field at `i`. -/
def u64 (b : ByteArray) (i : Nat) : Except String Nat := do
  return (← u32 b i) + 2 ^ 32 * (← u32 b (i + 4))

/-- The bytes `[off, off + n)`, which must be in the file. -/
def bytesAt (b : ByteArray) (off n : Nat) : Except String ByteArray :=
  if off + n ≤ b.size then .ok (b.extract off (off + n))
  else .error s!"truncated: no bytes [{off}, {off + n})"

/-- The NUL-terminated string at `off` of a string table. -/
def cstr (t : ByteArray) (off : Nat) : Except String String := do
  let rec stop (i : Nat) : Nat → Except String Nat
    | 0 => .error s!"string at {off}: no terminator"
    | f + 1 => match t[i]? with
      | none => .error s!"string at {off}: no terminator"
      | some 0 => .ok i
      | some _ => stop (i + 1) f
  let e ← stop off (t.size + 1)
  match String.fromUTF8? (t.extract off e) with
  | some s => return s
  | none => throw s!"string at {off}: not UTF-8"

/-! ## Headers -/

/-- `EM_X86_64`. -/
def emX8664 : Nat := 62
/-- `EM_AARCH64`. -/
def emAArch64 : Nat := 183

/-- The fields of the file header the reader uses. -/
structure Header where
  machine : Nat
  /-- `e_entry`: where the kernel starts the program. -/
  entry : Nat
  phoff : Nat
  phnum : Nat
  shoff : Nat
  shnum : Nat
  shstrndx : Nat
  deriving Repr, DecidableEq

/-- The file header: ELF64, little-endian, version 1, `ET_EXEC`, for x86-64
or AArch64, with the standard header and entry sizes. -/
def header (b : ByteArray) : Except String Header := do
  unless (← bytesAt b 0 4).data.toList == [0x7f, 0x45, 0x4c, 0x46] do throw "not an ELF file"
  unless (← u8 b 4) = 2 do throw "not ELF64"
  unless (← u8 b 5) = 1 do throw "not little-endian"
  unless (← u8 b 6) = 1 ∧ (← u32 b 20) = 1 do throw "not ELF version 1"
  unless (← u16 b 16) = 2 do throw "not an executable (ET_EXEC)"
  let machine ← u16 b 18
  unless machine = emX8664 ∨ machine = emAArch64 do throw s!"unknown machine {machine}"
  unless (← u16 b 52) = 64 ∧ (← u16 b 54) = 56 ∧ (← u16 b 58) = 64 do
    throw "unexpected header or entry size"
  let shnum ← u16 b 60
  let shstrndx ← u16 b 62
  unless 0 < shnum ∧ shstrndx < shnum do throw "no section headers or no section name table"
  return { machine, entry := ← u64 b 24, phoff := ← u64 b 32, phnum := ← u16 b 56, shoff := ← u64 b 40, shnum, shstrndx }

/-- A program header. -/
structure Phdr where
  type : Nat
  flags : Nat
  offset : Nat
  vaddr : Nat
  filesz : Nat
  memsz : Nat
  deriving Repr, DecidableEq

/-- `PT_LOAD`. -/
def ptLoad : Nat := 1
/-- `PF_X`, `PF_W`, `PF_R`. -/
def pfX : Nat := 1
def pfW : Nat := 2
def pfR : Nat := 4

/-- The program header at `off`. -/
def phdr (b : ByteArray) (off : Nat) : Except String Phdr := do
  return { type := ← u32 b off, flags := ← u32 b (off + 4), offset := ← u64 b (off + 8),
           vaddr := ← u64 b (off + 16), filesz := ← u64 b (off + 32), memsz := ← u64 b (off + 40) }

/-- The program header's mapped addresses. -/
def Phdr.mem (p : Phdr) : Range := ⟨p.vaddr, p.memsz⟩

/-- Its zero-filled tail, after the bytes from the file. -/
def Phdr.tail (p : Phdr) : Range := ⟨p.vaddr + p.filesz, p.memsz - p.filesz⟩

/-- A section header, with its name. -/
structure Shdr where
  name : String
  type : Nat
  flags : Nat
  addr : Nat
  offset : Nat
  size : Nat
  link : Nat
  entsize : Nat
  deriving Repr, DecidableEq

/-- `SHT_PROGBITS`, `SHT_SYMTAB`, `SHT_STRTAB`, `SHT_NOTE`, `SHT_NOBITS`. -/
def shtProgbits : Nat := 1
def shtSymtab : Nat := 2
def shtStrtab : Nat := 3
def shtNote : Nat := 7
def shtNobits : Nat := 8

/-- `SHF_WRITE`, `SHF_ALLOC`, `SHF_EXECINSTR`. -/
def shfWrite : Nat := 1
def shfAlloc : Nat := 2
def shfExec : Nat := 4

/-- The section header at `off`, its name not yet read. -/
def shdrRaw (b : ByteArray) (off : Nat) : Except String (Nat × Shdr) := do
  return (← u32 b off,
    { name := "", type := ← u32 b (off + 4), flags := ← u64 b (off + 8), addr := ← u64 b (off + 16),
      offset := ← u64 b (off + 24), size := ← u64 b (off + 32), link := ← u32 b (off + 40),
      entsize := ← u64 b (off + 56) })

/-- A section's bytes in the file (none for `SHT_NOBITS`). -/
def Shdr.bytes (b : ByteArray) (s : Shdr) : Except String ByteArray :=
  if s.type = shtNobits then .ok .empty else bytesAt b s.offset s.size

/-- A section's addresses. -/
def Shdr.range (s : Shdr) : Range := ⟨s.addr, s.size⟩

/-- The section headers, named. -/
def sections (b : ByteArray) (h : Header) : Except String (Array Shdr) := do
  let raw ← (List.range h.shnum).mapM fun i => shdrRaw b (h.shoff + 64 * i)
  let some (_, strs) := raw[h.shstrndx]? | throw "no section name table"
  unless strs.type = shtStrtab do throw "the section name table is not a string table"
  let t ← strs.bytes b
  return (← raw.mapM fun (n, s) => do return { s with name := ← cstr t n }).toArray

/-- A symbol. -/
structure Sym where
  name : String
  /-- `STB_*`: 0 `LOCAL`, 1 `GLOBAL`, 2 `WEAK`. -/
  bind : Nat
  /-- `STT_*`: 0 `NOTYPE`, 1 `OBJECT`, 2 `FUNC`, 3 `SECTION`, 4 `FILE`. -/
  type : Nat
  shndx : Nat
  value : Nat
  size : Nat
  /-- The offset of its entry in the file. -/
  entry : Nat
  deriving Repr, DecidableEq

/-- The symbols of the (only) symbol table, but the null one. -/
def symTable (b : ByteArray) (secs : Array Shdr) : Except String (List Sym) := do
  let tabs := secs.toList.filter (·.type = shtSymtab)
  let [tab] := tabs | throw s!"{tabs.length} symbol tables"
  unless tab.entsize = 24 ∧ tab.size % 24 = 0 do throw "unexpected symbol entry size"
  let some strs := secs[tab.link]? | throw "no symbol string table"
  unless strs.type = shtStrtab do throw "the symbol string table is not a string table"
  let t ← strs.bytes b
  let _ ← tab.bytes b
  ((List.range (tab.size / 24)).drop 1).mapM fun i => do
    let o := tab.offset + 24 * i
    let info ← u8 b (o + 4)
    return { name := ← cstr t (← u32 b o), bind := info / 16, type := info % 16, shndx := ← u16 b (o + 6),
             value := ← u64 b (o + 8), size := ← u64 b (o + 16), entry := o }

/-! ## The layout -/

/-- The parts of a layout that the file determines. -/
structure ElfLayout where
  code : Range
  data : Range
  rodata : Range
  heap : Range
  stackPool : Range
  pinned : Range
  image : List (Nat × Nat)
  symbols : List (String × Nat)
  deriving Repr, DecidableEq

/-- The layout: no static placement, the runtime's abort labels, the other
fields their defaults. -/
def ElfLayout.toLayout (e : ElfLayout) : Layout where
  code := e.code
  data := e.data
  rodata := e.rodata
  heap := e.heap
  stackPool := e.stackPool
  pinned := e.pinned
  static := fun _ => none
  image := e.image
  symbols := e.symbols
  abortLbl := Link.abortName

/-- `r` is within `s`. -/
def within (r s : Range) : Bool := decide (s.lo ≤ r.lo) && decide (r.lo + r.size ≤ s.lo + s.size)

/-- The one section named `n`, if any. -/
def secNamed? (secs : Array Shdr) (n : String) : Except String (Option (Nat × Shdr)) :=
  match secs.toList.zipIdx.filter (·.1.name == n) with
  | [] => .ok none
  | [(s, i)] => .ok (some (i, s))
  | _ => .error s!"more than one section {n}"

/-- The one section named `n`. -/
def secNamed (secs : Array Shdr) (n : String) : Except String (Nat × Shdr) := do
  let some s ← secNamed? secs n | throw s!"no section {n}"
  return s

/-- The sections the reader knows: the four mapped ones and the unmapped
tables and notes a static link writes. -/
def knownAlloc : List String := [".text", ".rodata", ".data", ".bss"]

/-- The linker's build-id note, the one other mapped section accepted. -/
def buildIdName : String := ".note.gnu.build-id"

/-- The program header types the reader accepts: `PT_NULL`, `PT_LOAD`,
`PT_NOTE`, `PT_PHDR`, `PT_GNU_STACK`, `PT_GNU_PROPERTY`. -/
def knownPt : List Nat := [0, 1, 4, 6, 0x6474e551, 0x6474e553]

/-- The `PT_LOAD` whose mapped addresses contain `r`, with exactly the
permissions `flags`. -/
def loadOf (loads : List Phdr) (what : String) (r : Range) (flags : Nat) : Except String Phdr :=
  match loads.find? (fun p => within r p.mem) with
  | none => .error s!"{what} is not inside a PT_LOAD"
  | some p => if p.flags = flags then .ok p else .error s!"{what}: its PT_LOAD has flags {p.flags}, not {flags}"

/-- A region of its own: the symbol `n`, a non-empty object of `.bss`
(section `bss`) inside the zero-filled tail `tail`. -/
def region (syms : List Sym) (bss : Nat) (tail : Range) (n : String) : Except String Range := do
  let s ← match syms.filter (·.name == n) with
    | [s] => pure s
    | [] => throw s!"no symbol {n}"
    | _ => throw s!"more than one symbol {n}"
  unless s.size ≠ 0 do throw s!"{n} has size 0"
  unless s.shndx = bss do throw s!"{n} is not in .bss"
  unless s.type = 1 ∧ s.bind = 0 do throw s!"{n} is not a local object"
  let r : Range := ⟨s.value, s.size⟩
  unless within r tail do throw s!"{n} is not in the zero-filled tail of the writable PT_LOAD"
  return r

/-- The build-id note `s` (section `i`), if any, checked: an `SHT_NOTE`
section mapped read-only, inside a `PT_LOAD` mapped `R` only from its file
bytes, disjoint from each of `others` (the code, `.rodata`, `.data`, `.bss`
and the regions), with no symbol of `syms` in its section or at an address
in it. It is no part of the layout. -/
def buildIdNote (loads : List Phdr) (others : List Range) (syms : List Sym) :
    Option (Nat × Shdr) → Except String Unit
  | none => pure ()
  | some (i, s) => do
    unless s.type = shtNote ∧ s.flags % 8 = shfAlloc do throw s!"{buildIdName}: unexpected type or flags"
    let p ← loadOf loads buildIdName s.range pfR
    unless s.offset + p.vaddr = p.offset + s.addr do throw s!"{buildIdName} is not mapped from its file bytes"
    unless others.all (Link.disjB s.range) do throw s!"{buildIdName} overlaps the code, the data or a region"
    for y in syms do
      if y.shndx = i ∨ (y.shndx ≠ 0 ∧ Link.containsB s.range y.value) then
        throw s!"symbol {y.name} in {buildIdName}"

/-- The linker's symbols, not data symbols. -/
def linkerSyms : List String := ["__bss_start", "_edata", "_end"]

/-- **The parts of the layout of an executable**, checked (see the module
doc). -/
def elfParts (b : ByteArray) : Except String ElfLayout := do
  let h ← header b
  let phdrs ← (List.range h.phnum).mapM fun i => phdr b (h.phoff + 56 * i)
  for p in phdrs do
    unless knownPt.contains p.type do throw s!"unexpected program header type {p.type}"
    if p.type = 0x6474e551 ∧ p.flags % 2 = 1 then throw "executable stack"
  let loads := phdrs.filter (·.type = ptLoad)
  for p in loads do
    unless p.filesz ≤ p.memsz do throw "a PT_LOAD with more file bytes than memory"
    let _ ← bytesAt b p.offset p.filesz
    if p.flags / 2 % 2 = 1 ∧ p.flags % 2 = 1 then throw "a writable and executable PT_LOAD"
  for (p, i) in loads.zipIdx do
    for q in loads.drop (i + 1) do
      unless Link.disjB p.mem q.mem do throw "overlapping PT_LOADs"
  let secs ← sections b h
  for s in secs do
    if s.flags / shfAlloc % 2 = 1 ∧ !knownAlloc.contains s.name ∧ s.name != buildIdName then
      throw s!"unexpected mapped section {s.name}"
    if [4, 5, 6, 9, 11].contains s.type then throw s!"unexpected dynamic or relocation section {s.name}"
  -- the code
  let (iText, text) ← secNamed secs ".text"
  unless text.type = shtProgbits ∧ text.flags % 8 = shfAlloc + shfExec do throw ".text: unexpected type or flags"
  let code := text.range
  unless h.entry = code.lo do throw s!"the entry point {h.entry} is not the start of .text ({code.lo})"
  let pc ← loadOf loads ".text" code (pfR + pfX)
  unless text.offset + pc.vaddr = pc.offset + text.addr do throw ".text is not mapped from its file bytes"
  -- the read-only image
  let ro ← secNamed? secs ".rodata"
  let (iRo, rodata) ← match ro with
    | none => pure (none, (⟨0, 0⟩ : Range))
    | some (i, s) => do
      unless s.type = shtProgbits ∧ s.flags % 8 = shfAlloc do throw ".rodata: unexpected type or flags"
      let pr ← loadOf loads ".rodata" s.range pfR
      unless s.offset + pr.vaddr = pr.offset + s.addr do throw ".rodata is not mapped from its file bytes"
      unless s.addr % 8 = 0 do throw ".rodata is not 8-aligned"
      pure (some i, s.range)
  -- the writable image and the regions
  let (iData, dsec) ← secNamed secs ".data"
  let (iBss, bss) ← secNamed secs ".bss"
  unless dsec.type = shtProgbits ∧ dsec.flags % 8 = shfAlloc + shfWrite do throw ".data: unexpected type or flags"
  unless bss.type = shtNobits ∧ bss.flags % 8 = shfAlloc + shfWrite do throw ".bss: unexpected type or flags"
  let pd ← loadOf loads ".data" dsec.range (pfR + pfW)
  unless (loads.filter fun p => p.flags / 2 % 2 = 1).length = 1 do throw "more than one writable PT_LOAD"
  unless pd.vaddr = dsec.addr ∧ pd.filesz = dsec.size ∧ pd.offset = dsec.offset do
    throw "the writable PT_LOAD's file part is not exactly .data"
  unless within bss.range pd.tail do throw ".bss is not in the zero-filled tail of the writable PT_LOAD"
  let syms ← symTable b secs
  let heap ← region syms iBss pd.tail Link.heapSym
  let pinned ← region syms iBss pd.tail Link.pinnedSym
  let pool ← region syms iBss pd.tail Link.poolSym
  unless Link.disjB heap pinned ∧ Link.disjB heap pool ∧ Link.disjB pinned pool do throw "overlapping regions"
  unless dsec.addr ≤ heap.lo do throw "the heap arena is below .data"
  let data : Range := ⟨dsec.addr, heap.lo - dsec.addr⟩
  unless Link.disjB rodata data ∧ Link.disjB rodata heap ∧ Link.disjB rodata pinned ∧
      Link.disjB rodata pool ∧ Link.disjB rodata code do throw ".rodata overlaps a region"
  buildIdNote loads [code, rodata, dsec.range, bss.range, data, heap, pinned, pool] syms
    (← secNamed? secs buildIdName)
  let image := (Link.addBytes [] dsec.addr ((← dsec.bytes b).data.toList.map (·.toNat))).filter (·.2 ≠ 0)
  -- the symbols
  let regionSyms := [Link.heapSym, Link.pinnedSym, Link.poolSym]
  let mut out : List (String × Nat) := []
  for s in syms do
    if s.name.startsWith "$" ∨ s.type = 2 ∨ s.type = 3 ∨ s.type = 4 ∨ s.shndx = 0 ∨ s.shndx ≥ 0xff00 ∨
        linkerSyms.contains s.name ∨ s.shndx = iText then
      continue
    unless s.shndx = iData ∨ s.shndx = iBss ∨ some s.shndx = iRo do
      throw s!"symbol {s.name} in an unexpected section"
    if Link.containsB code s.value then throw s!"data symbol {s.name} inside the code"
    if refuseBelowCode ∧ s.value < code.lo then throw s!"data symbol {s.name} below the code"
    unless s.bind = 0 do throw s!"data symbol {s.name} is not local"
    if some s.shndx = iRo then continue
    unless s.type = 0 ∨ s.type = 1 do throw s!"data symbol {s.name} of unexpected type {s.type}"
    unless regionSyms.contains s.name ∨ s.value < heap.lo do
      throw s!"data symbol {s.name} at or above the heap arena"
    out := out ++ [(s.name, s.value)]
  let e : ElfLayout := { code, data, rodata, heap, stackPool := pool, pinned, image, symbols := out }
  unless Link.wfB e.toLayout do throw "the layout is not well-formed (wfB)"
  return e

/-- **The layout of an executable** (see the module doc). -/
def elfLayout (b : ByteArray) : Except String Layout := (elfParts b).map ElfLayout.toLayout

/-! ## At elaboration time -/

deriving instance Lean.ToExpr for Range
deriving instance Lean.ToExpr for ElfLayout

open Lean Elab Term in
/-- `scc_elf_layout% "path"`: the layout of the executable at `path`
(relative to the package root), read at elaboration time (`elfLayout`), as a
literal, and the SHA-256 of the file: a `Layout × String`. -/
elab "scc_elf_layout% " path:str : term => do
  let b ← IO.FS.readBinFile path.getString
  match elfParts b with
  | .error e => throwError "{path.getString}: {e}"
  | .ok l => return mkAppN (mkConst ``Prod.mk [.zero, .zero]) #[mkConst ``Layout, mkConst ``String,
      mkApp (mkConst ``ElfLayout.toLayout) (toExpr l), mkStrLit (Sha256.ofBytes b)]

end Scc.Cert.Elf
