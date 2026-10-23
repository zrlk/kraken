/-
The canonical x64 target.

Kraken's x64 thread states (`Kraken.Promising.X64.State`), its instruction
semantics `X64.isa` under `Arch.tso`, and its assembly parser
(`Kraken.X64.Parser.parse`, AT&T syntax), with the extension hooks of
`Scc/Sem/Target.lean`:

- `regVal`: the sixteen general registers, `RFLAGS` (`CF` bit 0, `PF` 2,
  `AF` 4, `ZF` 6, `SF` 7, `OF` 11), and the low 64 bits of each vector
  register.
- `privLoad`: an 8-byte little-endian load from the thread's private memory
  (`dmem`), if all 8 bytes are mapped.
- `Asm`: what the target loads, the assembly text with the byte size of each
  instruction of its `.text` sections (`sizes`, from GNU `as`, see
  `Scc/Cert/Sizes.lean`) and the offsets of its labels (`labelOffs`);
  `cellsOf` lays the parsed text out at the sizes (`sizedCells`; an
  alignment directive is a `nopalign` cell, `textProgram`).
- `threadAt E base cells syms`: the thread state of the code cells `cells`
  laid out from `base` (each cell as long as its size, labels empty),
  halting after the last one, with label cells for the data symbols `syms`
  at their addresses (`X64.mkState`'s `syms`), those below `base` before
  the code (`placeBelow`, the executable starting at the lowest,
  `exeStart`) and the others after it (`placeSyms`), so that
  `leaq sym(%rip)` gives the symbol's address; the entry state `E` (`%rsp`
  at the top of the zero-filled initial stack in private memory, every other
  register zero, the pc at `base`).
- `loadProg H E Λ cells syms mem`: `H.slots` thread slots: slot 0
  `threadAt` at `Λ.code.lo` (the first instruction is the entry point) with
  the data symbols `syms`, the others dormant (`dormantAt`: halted, no
  private memory); `mem` as the initial memory (8-byte words), the hooks'
  initial extension state under `Λ`.
- `target H E`: the `.text` sections of the assembly text parsed by
  Kraken's parser and laid out at the sizes (`cellsOf`), then `loadProg`
  with `Λ.symbols` and the `.rodata` symbols (`loadSyms`) and the initial
  memory `Λ.image` and the `.rodata` image (`rodataWords`, at
  `Λ.rodata.lo`, its code labels resolved to their addresses); refused
  unless the sizes pass `SizeCheck` at `Λ.code.lo`, the `.rodata` image
  fits `Λ.rodata` and agrees with `Λ.symbols` and its code labels resolve,
  no data symbol lies inside the code (`symsAbove`), and the initial stack is
  clear of the layout (`Entry.clear`). `resolve` gives a label of the
  program its address in the same layout (`codeLabel`), the address of the
  cell after it.
- `abi`: the kernel's view of a thread state (K1, `Scc/Sem/Kernel.lean`):
  `syscall`, the number in `%rax`, arguments `%rdi`, `%rsi`, `%rdx`,
  `%r10`, `%r8`, `%r9`, the result in `%rax`, `%rcx` := the next pc and
  `%r11` := `RFLAGS`, the pc past the `syscall`; at `clone` the child gets
  `%rax = 0`, `%rsp` and the `%fs` base from the arguments; the thread
  pointer is the `%fs` base (`Reg64s.fsBase`); the private memory is
  `dmem`.
- `kernel n`: the kernel model's hooks (`Kernel.hooks abi`, `Arch.tso`,
  `n` thread slots); `canonical n := target (kernel n) Entry.linux`.
- `Scc.Correct cfg asm p`: the statement a certificate states, at
  `canonical cfg.slots` and `SrcSem.source (cfg.src .tso) p`.

Not modelled yet (`Scc/DESIGN.md` §7.1): the kernel's initial stack and
registers beyond `Entry`; the contents of `.data` from the text (the
writable image comes from `Λ`; `.rodata` is read from the text); a load of an image word
narrower than 8 bytes, or not 8-aligned, reads 0 (Kraken's memory has no
mixed-size accesses).

Sanity: `step_of_done` and `run_of_seqRun` (Kraken's single-thread step on
straight-line code is a step / run of the target without hooks), and an
executable check on `mov $5, %rax; add $1, %rax` that the loaded
configuration's Kraken steps compute what `X64.isa.exec` computes;
`unsupported_fault` (a system-call number the kernel model does not know
is a fault of `canonical`'s machine), and executable checks that
`write(1, buf, 1); exit_group(0)` runs to the trace `[out b, exit 0]` and
that an unknown number faults, that `clone` may be refused and activates a
dormant slot (with the child's stack range if the parent took it), and
that a range taken, released and taken again at the transfer sites keeps
its contents; `take_forced` (at the take site the only step is the take of
the range the registers name); `unmapped_fault` and checks of which
accesses fall outside the mapped regions (K11); `load_clear` (a loaded
layout is clear of the initial stack) and a check of the refusal.
-/
import Scc.Sem.Kernel
import Kraken.Promising.X64
import Kraken.Promising.X64Sized
import Kraken.X64.Parser

namespace Scc.Sem.X64

open Kraken.Promising Kraken.Promising.X64

/-- `RFLAGS` from the flags: `CF` bit 0, `PF` 2, `AF` 4, `ZF` 6, `SF` 7,
`OF` 11. -/
def rflags (f : StatusFlags) : BitVec 64 :=
  (BitVec.ofBool f.cf).zeroExtend 64 ||| (BitVec.ofBool f.pf).zeroExtend 64 <<< 2 |||
    (BitVec.ofBool f.af).zeroExtend 64 <<< 4 ||| (BitVec.ofBool f.zf).zeroExtend 64 <<< 6 |||
    (BitVec.ofBool f.sf).zeroExtend 64 <<< 7 ||| (BitVec.ofBool f.of).zeroExtend 64 <<< 11

/-- The 64-bit value of a register (the low 64 bits of a vector register). -/
def regVal (s : State) : RegId → BitVec 64
  | .r r => s.st.1.regs.get64 r
  | .rflags => rflags s.st.1.status
  | .v r => (s.st.1.zmms.get512 r).setWidth 64

/-- An 8-byte load from the private memory, if all 8 bytes are mapped. -/
def privLoad (s : State) (a : BitVec 64) : Option (BitVec 64) :=
  (s.st.1.dmem.loadInt a 8).map (BitVec.ofInt 64)

/-- The cell size of a directive in Kraken's unit x64 layout: one byte per
instruction, none per label (`X64.mkState`). The canonical loader takes the
sizes from the text's size table instead (`Asm.sizes`); `unitAsm` gives a
text this table, for checks that do not depend on sizes. -/
def cellSize : Directive → Nat
  | .label _ => 0
  | _ => 1

/-- **An x64 text with its instruction sizes**: the assembly text, the byte
size of each instruction of its `.text` sections in text order (one entry
per non-label directive of `textProgram`, an alignment directive's entry
being its padding), and the byte offsets from the start of the text of
labels the object file lists (checked by `SizeCheck`). `scc --cert` reads
both from GNU `as`'s output for the emitted text (`Scc/Cert/Sizes.lean`). -/
structure Asm where
  text : String
  sizes : List Nat
  labelOffs : List (String × Nat) := []
  deriving Repr, Inhabited

/-- **The program of a text's `.text` sections**: Kraken's parser on the
lines of `textSection`, directive lines dropped (`stripDirectives`), except
that an alignment directive (`.p2align k`, `.balign n`) becomes Kraken's
`nopalign` cell (`.align n`), whose size is the padding. -/
def textProgram (asm : String) : Except String Program := do
  let parseChunk (ls : List String) : Except String Program :=
    Kraken.X64.Parser.parse (Kraken.X64.Parser.stripDirectives ("\n".intercalate ls.reverse))
  let alignOf (t : String) : Option Nat :=
    let ops := ((t.splitOn " ").filter (· ≠ "")).drop 1
    if t.startsWith ".p2align" then (ops.headD "").toNat?.map (2 ^ ·)
    else if t.startsWith ".balign" then (ops.headD "").toNat?
    else none
  let mut out : Program := []
  let mut cur : List String := []
  for l in (textSection asm).splitOn "\n" do
    let t := " ".intercalate ((l.trimAscii.toString.splitOn "\t").map (·.trimAscii.toString))
    match alignOf t with
    | some n =>
        out := out ++ (← parseChunk cur) ++ (← Kraken.X64.Parser.parse s!".align {n}")
        cur := []
    | none => cur := l :: cur
  return out ++ (← parseChunk cur)

/-- A text with one byte per instruction (Kraken's `unitTable`) and no
label offsets: Kraken's unit layout, for the checks below. -/
def unitAsm (text : String) : Asm :=
  { text, sizes := match textProgram text with | .ok p => unitTable p | .error _ => [] }

/-- The end of code cells laid out from `base`. -/
def codeEnd (base : Nat) (cells : List (Directive × Nat)) : Nat := base + (cells.map (·.2)).sum

/-- The thread state of the code `cells` laid out from `base` (each cell its
size), halting after the last one, with label cells for the data symbols
`syms`: those below `base` before the code (`placeBelow`, the executable
starting at `exeStart base syms`), the others after it (`placeSyms`); entry
state `E`: `%rsp` at the top of the initial stack, which is zero-filled
private memory, every other register zero, the pc at `base`; no
declarations. -/
def threadAt (E : Entry) (base : Nat) (cells : List (Directive × Nat)) (syms : List (String × Nat)) : State where
  exe := (Int64.ofNat (exeStart base syms), placeBelow (.byteArray (.mk #[])) .label base syms ++
    cells ++ placeSyms (.byteArray (.mk #[])) .label (codeEnd base cells) (symsFrom base syms))
  endPc := Int64.ofNat (codeEnd base cells)
  st := ({ regs := { rsp := UInt64.ofNat E.sp }, dmem := E.stackMem }, Int64.ofNat base)

/-- 8-byte words `(address, value)` as initial shared memory. -/
def wordsMem (ws : List (Nat × Nat)) : List (Loc × Val) :=
  ws.map fun p => (⟨BitVec.ofNat 64 p.1, 8⟩, BitVec.ofNat 128 p.2)

/-- The initial memory of a layout: its static image, as 8-byte words. -/
def imageMem (Λ : Scc.Sem.Layout) : List (Loc × Val) := wordsMem Λ.image

/-- The program counter of a thread state. -/
def pcOf (s : State) : Nat := s.st.2.toBitVec.toNat

/-- The machine of the canonical target with hooks `H`. -/
abbrev machine (H : Hooks isa) : ExtMachine := ExtMachine.ofHooks isa Arch.tso H regVal privLoad pcOf

/-- A dormant thread slot (§2.1): `threadAt`'s program, halted (the pc at
the end address), zero registers, no private memory. A `clone` replaces its
state. -/
def dormantAt (E : Entry) (base : Nat) (cells : List (Directive × Nat)) (syms : List (String × Nat)) : State :=
  let s := threadAt E base cells syms
  { s with st := ({}, s.endPc) }

/-- Load laid-out code: `H.slots` thread slots, slot 0 the code `cells` at
`Λ.code.lo` with the data symbols `syms` and entry state `E`, the others
dormant; `mem` as the initial memory. -/
def loadProg (H : Hooks isa) (E : Entry) (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat))
    (syms : List (String × Nat)) (mem : List (Loc × Val)) : (machine H).Cfg :=
  (Config.init (threadAt E Λ.code.lo cells syms ::
    List.replicate (H.slots - 1) (dormantAt E Λ.code.lo cells syms)) mem, H.init E Λ)

/-- The name of a label cell. -/
def labelName : Directive → Option String
  | .label l => some l
  | _ => none

/-- The address of a code label in `cells` laid out from `base`. -/
def codeLabel (base : Nat) (cells : List (Directive × Nat)) (l : String) : Option Nat :=
  labelAddr (fun c : Directive × Nat => labelName c.1) (·.2) base l cells

/-- The code cells of a text at its sizes (`textProgram`, `sizedCells`). -/
def cellsOf (a : Asm) : Option (List (Directive × Nat)) :=
  match textProgram a.text with
  | .ok prog => sizedCells prog a.sizes
  | .error _ => none

/-- **The x64 target with hooks `H` and entry state `E`**: the text's
`.text` sections (`textProgram`) laid out at the text's sizes
(`sizedCells`, checked by `SizeCheck`), its `.rodata`
image at `Λ.rodata.lo` in shared memory beside `Λ.image` (`rodataWords`,
`.quad`s of code labels at their addresses in this layout), loaded by
`loadProg` with the data symbols `loadSyms`; refused if the size table does
not fit, a data section has a line the loader
does not read, the `.rodata` image does not fit `Λ.rodata`
(`rodataFits`), `Λ.symbols` disagrees with it (`symsAgree`), a `.quad`
label is unknown (`quadsResolve`), a data symbol lies inside the code
(`symsAbove`), or the initial stack is not clear of the layout (`Entry.clear`). -/
def target (H : Hooks isa) (E : Entry) : Target where
  M := machine H
  Asm := Asm
  load a Λ := do
    let cells ← cellsOf a
    let secs ← dataSections a.text
    let ro := secs.rodata
    let code (l : String) : Option Nat := (codeLabel Λ.code.lo cells l).orElse fun _ => Λ.symbols.lookup l
    let syms := loadSyms Λ ro
    let fin := codeEnd Λ.code.lo cells
    if SizeCheck (Int64.ofNat Λ.code.lo) cells a.labelOffs && rodataFits Λ ro &&
        symsAgree Λ ro && quadsResolve Λ ro code && symsAbove Λ.code.lo fin syms && E.clear Λ then
      some (loadProg H E Λ cells syms (imageMem Λ ++ wordsMem (rodataWords Λ ro code)))
    else none
  resolve a Λ l := (cellsOf a).bind fun cells => codeLabel Λ.code.lo cells l

/-! ## The kernel's view of a thread -/

/-- The thread is at a `syscall`. -/
def atSyscall (s : State) : Bool :=
  match s.directive with
  | some (.instr (.regular _ _ .syscall)) => true
  | _ => false

/-- The thread is at a `nop` (a transfer site's instruction). -/
def atNop (s : State) : Bool :=
  match s.directive with
  | some (.instr (.regular _ _ (.nop _))) => true
  | _ => false

/-- The pc of the instruction after the one at the pc. -/
def nextPc (s : State) : Int64 :=
  s.st.2 + Int64.ofNat ((s.exe.directivesAtAddress s.st.2).map (·.2)).sum

/-- The registers after a return of `r` from `syscall` at `s`: `%rax := r`,
`%rcx :=` the next pc, `%r11 := RFLAGS`. -/
def retRegs64 (s : State) (r : BitVec 64) : Reg64s :=
  let regs := s.st.1.regs
  { regs with
    rax := UInt64.ofNat r.toNat
    rcx := UInt64.ofNat (nextPc s).toBitVec.toNat
    r11 := UInt64.ofNat (rflags s.st.1.status).toNat }

/-- **The x86-64 Linux system-call convention** (K1): `syscall`, number in
`%rax`, arguments in `%rdi`, `%rsi`, `%rdx`, `%r10`, `%r8`, `%r9`, result in
`%rax`, `%rcx :=` the next pc and `%r11 := RFLAGS` (every other register
preserved), the pc past the `syscall`; at `clone` the child has the
parent's registers but `%rax = 0`, `%rsp = stack`, `fsBase = tls` (and
`%rcx`, `%r11` as for the parent); the thread pointer is the `%fs` base;
the stack pointer is `%rsp`; a transfer site is a `nop`, stepped over. -/
def abi : Kernel.Abi isa where
  nrs := Kernel.Nrs.x64
  atSys := atSyscall
  nr s := s.st.1.regs.rax.toNat
  arg s i :=
    let r := s.st.1.regs
    ([r.rdi, r.rsi, r.rdx, r.r10, r.r8, r.r9].getD i.val 0).toNat
  ret s r := { s with st := ({ s.st.1 with regs := retRegs64 s r }, nextPc s) }
  retRegs := [.r .rax, .r .rcx, .r .r11]
  child s stack tls :=
    { s with st := ({ s.st.1 with
        regs := { retRegs64 s 0 with rsp := UInt64.ofNat stack, fsBase := UInt64.ofNat tls },
        dmem := ∅ }, nextPc s) }
  setTp s a := { s with st := ({ s.st.1 with regs := { s.st.1.regs with fsBase := UInt64.ofNat a } }, s.st.2) }
  tp s := s.st.1.regs.fsBase.toBitVec
  dmem s := s.st.1.dmem
  setDmem s m := { s with st := ({ s.st.1 with dmem := m }, s.st.2) }
  sp s := s.st.1.regs.rsp.toNat
  pc := pcOf
  atNop := atNop
  skip s := { s with st := (s.st.1, nextPc s) }
  dmem_setDmem _ _ := rfl
  dmem_skip _ := rfl

/-- **The kernel model's hooks** for x64 (`Scc/Sem/Kernel.lean`): under
`Arch.tso`, with `n` thread slots. -/
abbrev kernel (n : Nat) : Hooks isa := Kernel.hooks abi Arch.tso n

/-- **The canonical x64 target with `n` thread slots**: the kernel model's
hooks, the Linux entry state `Entry.linux`: the oracle's fixed entry state,
not the certified statement (that is `CorrectE`, every admissible entry
state, `Scc/Sem/CorrectEX64.lean`). A certificate states `Correct` at
`canonical cfg.slots` (`Scc.Correct`), with `cfg.slots = B.threads + 1`
(`CertCfg.WF`). -/
def canonical (n : Nat) : Target := target (kernel n) Entry.linux

/-! ## Sanity -/

/-- **Kraken's single-thread step at a no-event instruction is a step of the
canonical target**, with no events, to the thread in the state Kraken's
step gives. -/
theorem step_of_done {μ : Marks} (hμ : ∀ k, μ.site k = none) {c : (machine (Hooks.none isa)).Cfg} {tid : Nat}
    {t : Thread isa} {s : State} (ht : c.1.threads[tid]? = some t) (hp : t.prom = [])
    (hex : isa.exec t.st = some (.done s)) :
    ∃ th, (machine (Hooks.none isa)).Step μ tid c [] (c.1.withThread tid th c.1.mem, c.2) ∧ th.st = s ∧
      th.prom = [] :=
  ExtMachine.ofHooks_step_of_done ht rfl (fun k a h => by simp [hμ k] at h) rfl id hp hex

/-- **A straight-line run of Kraken's single-thread step from a loaded
program is a run of the canonical target**: thread 0 of `loadProg` reaches
the state Kraken's step reaches, with the image memory unchanged. -/
theorem run_of_seqRun (μ : Marks) (hμ : ∀ k, μ.site k = none) (E : Entry) (Λ : Scc.Sem.Layout)
    (cells : List (Directive × Nat)) (syms : List (String × Nat)) (mem : List (Loc × Val)) {s : State}
    (hr : SeqRun isa (threadAt E Λ.code.lo cells syms) s) :
    ∃ c' th, (machine (Hooks.none isa)).Run μ (loadProg (Hooks.none isa) E Λ cells syms mem) [] c' ∧
      c'.1.threads[0]? = some th ∧ th.st = s ∧ th.prom = [] ∧ c'.1.mem = { init := mem, msgs := #[] } :=
  let ⟨c', th, h1, h2, h3, h4, h5, _⟩ :=
    ExtMachine.ofHooks_run_of_seqRun hr (c := loadProg (Hooks.none isa) E Λ cells syms mem)
    (t := Thread.init _) rfl rfl rfl rfl id (fun _ _ => rfl) (fun _ _ k a h => by simp [hμ k] at h)
  ⟨c', th, h1, h2, h3, h4, h5⟩

/-- A small entry state for the checks: a 64-byte initial stack at 0x1000. -/
private def Et : Entry := ⟨⟨0x1000, 64⟩⟩

/-- The trivial layout, its text at 16, with one data symbol `val` at 48
holding 42. -/
private def Λt : Scc.Sem.Layout := { trivLayout with symbols := [("val", 48)], image := [(48, 42)] }

/-- Kraken's single-thread step, iterated on thread 0's state while each
instruction is a no-event step: `%rax` and the pc after each. -/
private def seqTrace : Nat → State → List String
  | 0, _ => []
  | n + 1, s =>
    match isa.exec s with
    | some (.done s') => s!"rax={(s'.st.1.regs.get64 .rax).toNat} pc={s'.st.2}" :: seqTrace n s'
    | none => ["halt"]
    | some _ => ["event"]

/-- The machine's steps of thread 0 (the first successful outcome of
Kraken's `stepThread`), from the loaded configuration: `%rax`, `%rcx`,
`%rsp`, the pc and the number of shared messages after each. -/
private def machTrace : Nat → Config isa → List String
  | 0, _ => []
  | n + 1, c =>
    match stepThread Arch.tso c 0 with
    | some (.ok o :: _) =>
      let r := o.thread.st.st.1.regs
      s!"rax={(r.get64 .rax).toNat} rcx={(r.get64 .rcx).toNat} rsp={(r.get64 .rsp).toNat} pc={o.thread.st.st.2} msgs={o.mem.msgs.size}" ::
        machTrace n (c.withThread 0 o.thread o.mem)
    | none => ["halt"]
    | _ => ["error"]

/-- The target's run on `asm` under `Λt` and `Et`. -/
private def run (asm : String) : Option (List String) :=
  ((target (Hooks.none isa) Et).load (unitAsm asm) Λt).map fun (c : (machine (Hooks.none isa)).Cfg) => machTrace 8 c.1

private def straight : String := "mov $5, %rax\nadd $1, %rax"

/-- info: some (["rax=5 pc=17", "rax=6 pc=18", "halt"], ["rax=5 pc=17", "rax=6 pc=18", "halt"]) -/
#guard_msgs in
#eval ((target (Hooks.none isa) Et).load (unitAsm straight) Λt).map fun (c : (machine (Hooks.none isa)).Cfg) =>
  ((machTrace 5 c.1).map fun l => " ".intercalate ((l.splitOn " ").filter fun w =>
      w.startsWith "rax=" || w.startsWith "pc=" || w == "halt"),
    (c.1.threads[0]?.map fun t => seqTrace 5 t.st).getD [])

/-- **A data symbol resolves**: `leaq val(%rip)` (scc's `la`) gives its
address 48, and an 8-byte load from it reads the image word 42. The data
section's own label and bytes are ignored (`textSection`). -/
private def dataRef : String :=
  "\t.text\n_start:\n\tleaq val(%rip), %rcx\n\tmovq (%rcx), %rax\n" ++
  "\t.data\n\t.balign 8\nval:\n\t.byte 42, 0, 0, 0, 0, 0, 0, 0\n"

/-- info: some ["rax=0 rcx=48 rsp=4160 pc=17 msgs=0", "rax=42 rcx=48 rsp=4160 pc=18 msgs=0", "halt"] -/
#guard_msgs in
#eval run dataRef

/-- **The entry stack is private**: `%rsp` starts at the top of `Et`'s
stack (0x1040 = 4160); `_start`'s alignment and a push and pop use private
memory (no shared message). -/
private def entryStack : String :=
  "\t.text\n_start:\n\txorl %ebp, %ebp\n\tandq $-16, %rsp\n\tmovq $7, %rax\n\tpushq %rax\n\tmovq $0, %rax\n\tpopq %rax\n"

/--
info: some
  ["rax=0 rcx=0 rsp=4160 pc=17 msgs=0", "rax=0 rcx=0 rsp=4160 pc=18 msgs=0", "rax=7 rcx=0 rsp=4160 pc=19 msgs=0",
    "rax=7 rcx=0 rsp=4152 pc=20 msgs=0", "rax=0 rcx=0 rsp=4152 pc=21 msgs=0", "rax=7 rcx=0 rsp=4160 pc=22 msgs=0",
    "halt"]
-/
#guard_msgs in
#eval run entryStack

/-- Thread 0's pc after `n` machine steps from the loaded configuration. -/
private def pcAfter (asm : String) (n : Nat) : Option Nat :=
  ((target (Hooks.none isa) Et).load (unitAsm asm) Λt).bind fun (c : (machine (Hooks.none isa)).Cfg) => go n c.1
where
  go : Nat → Config isa → Option Nat
    | 0, c => c.threads[0]?.map (pcOf ·.st)
    | n + 1, c =>
      match stepThread Arch.tso c 0 with
      | some (.ok o :: _) => go n (c.withThread 0 o.thread o.mem)
      | _ => none

private def labelled : String := "mov $5, %rax\nfoo:\nadd $1, %rax"

-- `resolve` gives a `.text` label the model pc of the instruction after it
-- (the pc after the first step), and nothing for a label the text lacks.
#guard (target (Hooks.none isa) Et).resolve (unitAsm labelled) Λt "foo" == some 17 &&
  pcAfter labelled 1 == some 17 && (target (Hooks.none isa) Et).resolve (unitAsm labelled) Λt "bar" == none

-- Without hooks the loaded program has one thread slot; with the kernel
-- model, the slot count it is given.
#guard (target (Hooks.none isa) Et).threadSlots (unitAsm straight) Λt == 1 &&
  (target (kernel 7) Et).threadSlots (unitAsm straight) Λt == 7 && (canonical 3).threadSlots (unitAsm straight) Λt == 3

-- A data symbol inside the code (`[16, 18)`) is refused, at its start or
-- its last byte; one at its end is not.
#guard ((target (Hooks.none isa) Et).load (unitAsm dataRef) { Λt with symbols := [("val", 16)] }).isNone &&
  ((target (Hooks.none isa) Et).load (unitAsm dataRef) { Λt with symbols := [("val", 17)] }).isNone &&
  ((target (Hooks.none isa) Et).load (unitAsm dataRef) { Λt with symbols := [("val", 18)] }).isSome

/-- **A data symbol below the code resolves**: with `val` at 8, below the
text at 16, the executable starts at 8 with `val`'s label cell, padded to
the code; `leaq val(%rip)` gives 8 and the load reads the word there. -/
private def Λlow : Scc.Sem.Layout := { Λt with symbols := [("val", 8)], image := [(8, 42)] }

/-- info: some ["rax=0 rcx=8 rsp=4160 pc=17 msgs=0", "rax=42 rcx=8 rsp=4160 pc=18 msgs=0", "halt"] -/
#guard_msgs in
#eval ((target (Hooks.none isa) Et).load (unitAsm dataRef) Λlow).map fun (c : (machine (Hooks.none isa)).Cfg) =>
  machTrace 8 c.1

-- The cells around the code (one 1-byte `nop` at 16): symbols below it
-- from the lowest (`a` at 4), no padding between two at one address (`b`,
-- `c` at 8), padding to the code at 16; above it likewise (`placeSyms`:
-- none for `e` at the end of the code, 17). Without low symbols the
-- executable starts at the code.
private def cellsAround (syms : List (String × Nat)) : Option (Int64 × List (String × Nat)) :=
  (cellsOf (unitAsm "nop")).map fun cells =>
    ((threadAt Et 16 cells syms).exe.1,
      (threadAt Et 16 cells syms).exe.2.map fun (d, z) => (match d with | .label l => l | _ => "_", z))

#guard cellsAround [("d", 40), ("b", 8), ("a", 4), ("c", 8)] ==
    some (4, [("a", 0), ("_", 4), ("b", 0), ("c", 0), ("_", 8), ("_", 1), ("_", 23), ("d", 0)]) &&
  cellsAround [("d", 40)] == some (16, [("_", 1), ("_", 23), ("d", 0)]) &&
  cellsAround [("d", 40), ("e", 17)] == some (16, [("_", 1), ("e", 0), ("_", 23), ("d", 0)])

/-! ## Sanity of the kernel model -/

/-- **An unknown system-call number is a fault** of the canonical target's
machine: a running thread at `syscall` with a number in `%rax` that is none
of `Kernel.Nrs.x64`'s. -/
theorem unsupported_fault {n : Nat} {c : (machine (kernel n)).Cfg} {tid : Nat} {t : Thread isa}
    (ht : c.1.threads[tid]? = some t) (hr : c.2.runs tid = true) (hx : c.2.exited = none)
    (hs : atSyscall t.st = true) (hn : t.st.st.1.regs.rax.toNat ∉ [1, 60, 231, 202, 13, 56, 158]) :
    (machine (kernel n)).fault c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hn
  exact .inr (Kernel.fault_of_unsupported (K := abi) _ _ ht hr hx hs
    (Kernel.decode_none _ h1 h2 h3 h4 h5 h6 (by simpa [abi, Kernel.Nrs.x64, eq_comm] using h7)))

/-- **A transfer site's `nop` has no register dependency**, so a
certification step there keeps the thread's register views
(`Kernel.certSem_step_of_take`, `Kernel.certSem_step_of_release`). -/
theorem deps_of_atNop {s : State} (h : atNop s = true) : isa.deps s = {} := by
  unfold atNop at h
  split at h
  · rename_i hd
    show deps s = {}
    rename_i _ w _
    simp only [deps, hd, _root_.Directive.deps, Instr.deps]
    cases w <;> with_unfolding_all rfl
  · cases h

/-- A `nop` is not a system call. -/
theorem not_atSys_of_atNop {s : State} (h : atNop s = true) : atSyscall s = false := by
  unfold atNop at h
  unfold atSyscall
  split at h <;> simp_all

/-- **The transfer is forced** on the canonical x64 target: a thread at the
take site's `nop` (and at no release site) takes no instruction step,
spawn or system call; its only step is the take of the range `%rdi`,
`%rsi` name (`Kernel.step_at_take`). -/
theorem take_forced {n : Nat} {μ : Marks} {c c' : (machine (kernel n)).Cfg} {tid : Nat} {es : List Ev}
    {t : Thread isa} (ht : c.1.threads[tid]? = some t) (hn : atNop t.st = true)
    (hs : (machine (kernel n)).AtSite μ .take c tid) (hnr : ¬ (machine (kernel n)).AtSite μ .release c tid)
    (h : (machine (kernel n)).Step μ tid c es c') : es = [] ∧ Kernel.takeStep abi tid c = some c' := by
  refine Kernel.step_at_take ht ?_ hs hnr h
  show atSyscall t.st = false
  unfold atNop at hn
  unfold atSyscall
  split at hn <;> simp_all

/-- **A loaded layout is clear of the initial stack**: the loader refuses
any other (`Entry.clear`), so `Correct`'s start clause, which needs a loaded
configuration, implies it. -/
theorem load_clear {H : Hooks isa} {E : Entry} {a : Asm} {Λ : Scc.Sem.Layout} {c : (machine H).Cfg}
    (h : (target H E).load a Λ = some c) : E.clear Λ = true := by
  simp only [target, Option.bind_eq_bind] at h
  obtain ⟨cells, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨secs, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact hc.2
  · cases h

/-- **An access outside the mapped regions is a fault** of the canonical
target's machine (K11), here when it is the instruction's first access
(`Kernel.rootUnmapped`, which the checks below evaluate). -/
theorem unmapped_fault {n : Nat} {c : (machine (kernel n)).Cfg} {tid : Nat}
    (h : Kernel.rootUnmapped abi c tid = true) : (machine (kernel n)).fault c :=
  .inr (Kernel.fault_of_unmapped _ _ (Kernel.unmappedAt_of_root _ h))

/-- Kernel hooks for the checks: two thread slots. -/
private abbrev Kt : Hooks isa := Kernel.hooks abi Arch.tso 2

/-- Thread 0 of a configuration of the kernel model, run for at most `n`
steps: at a system call the kernel's step (`Kernel.sysStep`) with the next
choice of `ps`, printing its events; elsewhere Kraken's step (its first
outcome); a kernel fault (`Kernel.faultAt`) or the process's exit ends the
run. -/
private def kRun : Nat → List Kernel.Pick → Config isa × Kernel.KState → List String
  | 0, _, _ => ["out of fuel"]
  | n + 1, ps, c =>
    match c.2.exited with
    | some o => [s!"exited: {repr o}"]
    | none =>
      if Kernel.faultAt abi c 0 then ["fault"] else
      match c.1.threads[0]? with
      | none => ["no thread"]
      | some t =>
        if abi.atSys t.st then
          match ps with
          | [] => ["no choice left"]
          | p :: ps =>
            match Kernel.sysStep abi Arch.tso 0 c p with
            | some (es, c') => es.map (fun e => s!"{repr e}") ++ kRun n ps c'
            | none => ["no kernel step"]
        else
          match stepThread Arch.tso c.1 0 with
          | some (.ok o :: _) => kRun n ps (c.1.withThread 0 o.thread o.mem, c.2)
          | _ => ["stuck"]

/-- `Λt` with `val` (holding 42) at 256, above the checks' code, and the
stack pool `[0x1f00, 0x2000)`. -/
private def Λk : Scc.Sem.Layout :=
  { Λt with symbols := [("val", 256)], image := [(256, 42)], stackPool := ⟨0x1f00, 0x100⟩ }

/-- The kernel model's run of `asm` under `Λk` and `Et`, with the choices
`ps`. -/
private def krun (asm : String) (ps : List Kernel.Pick) : Option (List String) :=
  ((target Kt Et).load (unitAsm asm) Λk).map fun (c : (machine Kt).Cfg) => kRun 32 ps c

/-- `write(1, val, 1)` then `exit_group(0)`: `val` holds 42 (`Λk`). -/
private def writeExit : String :=
  "\t.text\n_start:\n\tleaq val(%rip), %rsi\n\tmovq $1, %rdi\n\tmovq $1, %rdx\n\tmovq $1, %rax\n" ++
  "\tsyscall\n\tmovq $0, %rdi\n\tmovq $231, %rax\n\tsyscall\n"

/- **`write(1, buf, 1); exit_group(0)` runs to the trace `[out 42, exit 0]`**:
the kernel transfers the byte (reading the image word at `val`, the only
write visible), `write` returns 1, `exit_group(0)` ends the process. -/
/-- info: some ["Scc.Sem.Ev.out 42", "Scc.Sem.Ev.exit 0", "exited: Scc.Sem.Outcome.exit 0"] -/
#guard_msgs in
#eval krun writeExit [.byte 0, .ret 1, .ret 0]

/- **The kernel's other answers**: `write` may be interrupted before any
byte (`-EINTR`, no event; the program has no retry loop, so it goes on to
`exit_group`) or refused (`writeErr`); after one byte, a result other than
1 is no step. -/
/--
info: (some ["Scc.Sem.Ev.exit 0", "exited: Scc.Sem.Outcome.exit 0"],
  some ["Scc.Sem.Ev.writeErr", "Scc.Sem.Ev.exit 0", "exited: Scc.Sem.Outcome.exit 0"],
  some ["Scc.Sem.Ev.out 42", "no kernel step"])
-/
#guard_msgs in
#eval (krun writeExit [.ret (Kernel.neg Kernel.eintr), .ret 0],
  krun writeExit [.ret (Kernel.neg 32), .ret 0], krun writeExit [.byte 0, .ret 2])

/-- Thread 0 run by Kraken's step until it is at a system call (at most `n`
steps). -/
private def toSys : Nat → Config isa × Kernel.KState → Option (Config isa × Kernel.KState)
  | 0, _ => none
  | n + 1, c =>
    match c.1.threads[0]? with
    | none => none
    | some t =>
      if abi.atSys t.st then some c else
      match stepThread Arch.tso c.1 0 with
      | some (.ok o :: _) => toSys n (c.1.withThread 0 o.thread o.mem, c.2)
      | _ => none

/-- `clone(cloneFlags, 0x2000, 0, tls = 0x77, 0)`, arguments in `%rdi`, `%rsi`, `%rdx`, `%r10`, `%r8`. -/
private def cloneProg : String := "movq $0xd0f00, %rdi\nmovq $0x2000, %rsi\nmovq $0, %rdx\nmovq $0, %r10\nmovq $0x77, %r8\nmovq $56, %rax\nsyscall"

/-- The threads of a configuration: `%rax`, `%rsp`, the `%fs` base, the pc,
and whether the word below `%rsp` is private (`privLoad`). -/
private def slotsOf (c : Config isa) : List String :=
  c.threads.toList.zipIdx.map fun (t, i) =>
    let r := t.st.st.1.regs
    s!"slot {i}: rax={r.rax} rsp={r.rsp} fs={r.fsBase} pc={t.st.st.2} " ++
      s!"priv={(privLoad t.st (BitVec.ofNat 64 (r.rsp.toNat - 8))).isSome}"

/- **`clone` activates the dormant slot 1** (`Kernel.spawnStep`, child id
5): the parent gets 5 and moves past the system call; the child starts
there with result 0, the stack pointer 0x2000 = 8192 and thread pointer
0x77 = 119 from the arguments (`%rax`, `%rsp`, the `%fs` base); the slots
are then both running. The parent holds no range ending at 0x2000, so the
child's stack is shared memory and it has no stack range. -/
/--
info: some (["slot 0: rax=5 rsp=4160 fs=0 pc=23 priv=true", "slot 1: rax=0 rsp=8192 fs=119 pc=23 priv=false"],
 #[Scc.Sem.Kernel.Slot.run 0, Scc.Sem.Kernel.Slot.run 0],
 none)
-/
#guard_msgs in
#eval ((target Kt Et).load (unitAsm cloneProg) Λk).bind fun (c : (machine Kt).Cfg) =>
  (toSys 16 c).bind fun c => (Kernel.spawnStep abi 0 c 1 5).map fun c' =>
    (slotsOf c'.1, c'.2.slots, Kt.stackRange c' 1)

/-- A range as text. -/
private def showR (r : Range) : String := s!"[{r.lo}+{r.size}]"

/-- Thread 0 run for at most `n` steps: at the take or release site
(addresses `ts`, `rs`) the kernel's transfer (`Kernel.takeStep`,
`Kernel.releaseStep`), printed with the thread's stack range after it; at a
system call it stops; elsewhere Kraken's step. The log and the final
configuration. -/
private def xRun (ts rs : Option Nat) : Nat → Config isa × Kernel.KState → List String × (Config isa × Kernel.KState)
  | 0, c => (["out of fuel"], c)
  | n + 1, c =>
    match c.1.threads[0]? with
    | none => (["no thread"], c)
    | some t =>
      let r := Kernel.siteRange abi t.st
      let site (nm : String) (st : Option (Config isa × Kernel.KState)) :=
        match st with
        | some c' =>
          let (l, c'') := xRun ts rs n c'
          (s!"{nm} {showR r} stack={((Kernel.stackRangeOf abi c' 0).map showR).getD "none"}" :: l, c'')
        | none => ([s!"stuck at {nm} {showR r}"], c)
      if ts = some (pcOf t.st) then site "take" (Kernel.takeStep abi 0 c)
      else if rs = some (pcOf t.st) then site "release" (Kernel.releaseStep abi 0 c)
      else if abi.atSys t.st then (["at syscall"], c)
      else
        match stepThread Arch.tso c.1 0 with
        | some (.ok o :: _) => xRun ts rs n (c.1.withThread 0 o.thread o.mem, c.2)
        | none => (["halt"], c)
        | _ => (["stuck"], c)

/-- The transfer sites of `asm` (`XferKind.label`) and `xRun` on it under
`Λk`, `Et`, with two slots. -/
private def xrun (asm : String) (n : Nat) : Option (List String × (Config isa × Kernel.KState)) :=
  ((target Kt Et).load (unitAsm asm) Λk).map fun (c : (machine Kt).Cfg) =>
    xRun ((target Kt Et).resolve (unitAsm asm) Λk XferKind.take.label)
      ((target Kt Et).resolve (unitAsm asm) Λk XferKind.release.label) n c

/-- The runtime's transfer routines, reduced to their sites. -/
private def sites : String :=
  "\tjmp end\ntake:\nscc_rt_take_site:\n\tnop\n\tret\nrelease:\nscc_rt_release_site:\n\tnop\n\tret\nend:\n"

/-- Take `[0x1fc0, 0x2000)` (the child's stack, as `scc_rt_thread_init`
does), then `clone` with stack pointer 0x2000. -/
private def cloneTake : String :=
  "\tmovq $0x1fc0, %rdi\n\tmovq $0x40, %rsi\n\tcall take\n" ++
  "\tmovq $0xd0f00, %rdi\n\tmovq $0x2000, %rsi\n\tmovq $0, %rdx\n\tmovq $0, %r10\n\tmovq $0x77, %r8\n" ++
  "\tmovq $56, %rax\n\tsyscall\n" ++ sites

/- **`clone` hands the child its stack range**: the parent takes
`[0x1fc0, 0x2000)` at the take site (its stack pointer is elsewhere, so it
is not the parent's stack range); `clone` with stack pointer 0x2000 moves
it to the child, whose stack is then private and whose stack range it is. -/
/--
info: some (["take [8128+64] stack=none", "at syscall"],
 some (["slot 0: rax=5 rsp=4160 fs=0 pc=26 priv=true", "slot 1: rax=0 rsp=8192 fs=119 pc=26 priv=true"],
  [(1, { lo := 8128, size := 64 })],
  none,
  some { lo := 8128, size := 64 }))
-/
#guard_msgs in
#eval (xrun cloneTake 32).map fun (p : List String × (Config isa × Kernel.KState)) =>
  (p.1, (Kernel.spawnStep abi 0 p.2 1 5).map fun (c' : Config isa × Kernel.KState) =>
    (slotsOf c'.1, c'.2.held, Kt.stackRange c' 0, Kt.stackRange c' 1))

/-- Grow and reuse: take `r1 = [0x1f00, 0x1f40)`, switch `%rsp` into it and
store 7 at 0x1f00; take `r2 = [0x1f80, 0x2000)` (the grow routine's new
range) and switch `%rsp` to its top; release `r1` (the thread has left
it); take `r1` again and load 0x1f00. The calls push their return
addresses on the current stack. -/
private def growReuse : String :=
  "\tmovq $0x1f00, %rdi\n\tmovq $0x40, %rsi\n\tcall take\n\tmovq $0x1f40, %rsp\n" ++
  "\tmovq $7, %rax\n\tmovq $0x1f00, %rcx\n\tmovq %rax, (%rcx)\n" ++
  "\tmovq $0x1f80, %rdi\n\tmovq $0x80, %rsi\n\tcall take\n\tmovq $0x2000, %rsp\n" ++
  "\tmovq $0x1f00, %rdi\n\tmovq $0x40, %rsi\n\tcall release\n" ++
  "\tmovq $0x1f00, %rdi\n\tmovq $0x40, %rsi\n\tcall take\n\tmovq (%rcx), %rdx\n" ++ sites

/- **A range released and taken again keeps its contents**
(`Kernel.release_take_handoff`): the stack range follows the stack
pointer (`r1`, then `r2` after the switch); after the release `r1` is
unmapped and the pool holds its bytes; the second take maps them back, so
the load reads the 7 stored before the growth, from private memory (no
shared message). -/
/--
info: some (["take [7936+64] stack=none", "take [8064+128] stack=[7936+64]", "release [7936+64] stack=[8064+128]",
  "take [7936+64] stack=[8064+128]", "halt"],
 7,
 0,
 [(0, { lo := 7936, size := 64 }), (0, { lo := 8064, size := 128 })])
-/
#guard_msgs in
#eval (xrun growReuse 64).map fun (p : List String × (Config isa × Kernel.KState)) =>
  (p.1, (p.2.1.threads[0]?.map fun (t : Thread isa) => t.st.st.1.regs.rdx).getD 0, p.2.1.mem.msgs.size,
    p.2.2.held)

/- **No release of the range a thread is on**: with `%rsp` in `r1`, the
release of `r1` has no step (the thread is stuck, which progress
excludes). -/
/-- info: some ["take [7936+64] stack=none", "stuck at release [7936+64]"] -/
#guard_msgs in
#eval (xrun ("\tmovq $0x1f00, %rdi\n\tmovq $0x40, %rsi\n\tcall take\n\tmovq $0x1f40, %rsp\n" ++
  "\tcall release\n" ++ sites) 32).map (·.1)

/- **A range is not taken twice**: the second take of `r1` while held is
stuck. -/
/-- info: some ["take [7936+64] stack=none", "stuck at take [7936+64]"] -/
#guard_msgs in
#eval (xrun ("\tmovq $0x1f00, %rdi\n\tmovq $0x40, %rsi\n\tcall take\n\tcall take\n" ++ sites) 32).map (·.1)

/- **`clone` with every slot used is a fault** (one slot: the entry
thread's). -/
/-- info: some true -/
#guard_msgs in
#eval ((target (Kernel.hooks abi Arch.tso 1) Et).load (unitAsm cloneProg) Λk).bind
  fun (c : (machine (Kernel.hooks abi Arch.tso 1)).Cfg) => (toSys 16 c).map fun c => Kernel.faultAt abi c 0

/- **An unknown system-call number faults.** -/
/-- info: some ["fault"] -/
#guard_msgs in
#eval krun "movq $999, %rax\nsyscall" []

/- **Linux may refuse a `clone`**: `-EAGAIN` or `-ENOMEM` with the event
`cloneErr` (here the program then runs off its code, a fault); any other
error is no step. -/
/--
info: (some ["Scc.Sem.Ev.cloneErr", "fault"], some ["Scc.Sem.Ev.cloneErr", "fault"], some ["no kernel step"])
-/
#guard_msgs in
#eval (krun cloneProg [.ret (Kernel.neg Kernel.eagain)], krun cloneProg [.ret (Kernel.neg Kernel.enomem)],
  krun cloneProg [.ret (Kernel.neg 1)])

/-- Thread 0 of `asm` (under `Λk`, `Et`) after `n` of Kraken's steps:
whether its next instruction's first access is unmapped
(`Kernel.rootUnmapped`, a fault by `unmapped_fault`). -/
private def unmappedAfter (asm : String) (n : Nat) : Option Bool :=
  ((target Kt Et).load (unitAsm asm) Λk).bind fun (c : (machine Kt).Cfg) => (go n c).map (Kernel.rootUnmapped abi · 0)
where
  go : Nat → Config isa × Kernel.KState → Option (Config isa × Kernel.KState)
    | 0, c => some c
    | n + 1, c =>
      match stepThread Arch.tso c.1 0 with
      | some (.ok o :: _) => go n (c.1.withThread 0 o.thread o.mem, c.2)
      | _ => none

/- **Accesses outside the mapped regions are faults** (K11): under `Λk`
(code `[16, 48)`, data `[48, 64)`, heap `[64, 80)`, pool
`[0x1f00, 0x2000)`) and `Et` (initial stack `[0x1000, 0x1040)`), a load
from the data, the code, the pool, a store to the heap, and a load from the
initial stack (private, no shared access) are not; a load from 0x9000, a
store to the code and a store just past the heap are. -/
/-- info: [some false, some false, some false, some false, some false, some true, some true, some true] -/
#guard_msgs in
#eval [unmappedAfter "movq $48, %r9\nmovq (%r9), %rax" 1, unmappedAfter "movq $16, %r9\nmovq (%r9), %rax" 1,
  unmappedAfter "movq $0x1f00, %r9\nmovq (%r9), %rax" 1, unmappedAfter "movq $64, %r9\nmovq %rax, (%r9)" 1,
  unmappedAfter "movq -8(%rsp), %rax" 0, unmappedAfter "movq $0x9000, %r9\nmovq (%r9), %rax" 1,
  unmappedAfter "movq $16, %r9\nmovq %rax, (%r9)" 1, unmappedAfter "movq $76, %r9\nmovq %rax, (%r9)" 1]

-- The loader refuses an initial stack that meets the layout (here `Λt`'s
-- code), and the Linux entry state is clear of the trivial layout.
#guard ((target (Hooks.none isa) ⟨⟨40, 64⟩⟩).load (unitAsm straight) Λt).isNone &&
  ((target (Hooks.none isa) Et).load (unitAsm straight) Λt).isSome && Entry.linux.clear trivLayout

/-- `asm` (under `Λk`, `Et`) followed by `movq %rax, (%r9)` with
`r9 = 48`: the values thread 0 may promise to 48 now, certified under
`Kernel.certExec` (`cert = true`) or under the ISA's `exec`
(`cert = false`). -/
private def certPromised (asm : String) (cert : Bool) : Option (List Nat) :=
  ((target Kt Et).load (unitAsm ("movq $48, %r9\n" ++ asm ++ "\nmovq %rax, (%r9)")) Λk).map
    fun (c : (machine Kt).Cfg) =>
      let ps := if cert then (certifiedPromisesWith Arch.tso (Kernel.certExec abi) {} c.1 0 16).1
        else (certifiedPromises Arch.tso {} c.1 0 16).1
      ps.filterMap fun (c', _) => c'.mem.msgs.back?.map (·.val.toNat)

/- **Certification runs through system calls** (`Kernel.certExec`): a store
of the result of `futex` wake (count 2) may be promised with each count the
kernel model may return, `0`, `1`, `2`; of `rt_sigaction`, `0`; nothing
after `exit_group`, which does not return. The ISA's `exec` alone certifies
no store after a system call. -/
/-- info: (some [2, 1, 0], some [0], some [], some []) -/
#guard_msgs in
#eval (certPromised "movq $0, %rdi\nmovq $129, %rsi\nmovq $2, %rdx\nmovq $202, %rax\nsyscall" true,
  certPromised "movq $13, %rdi\nmovq $0, %rsi\nmovq $0, %rdx\nmovq $8, %r10\nmovq $13, %rax\nsyscall" true,
  certPromised "movq $0, %rdi\nmovq $231, %rax\nsyscall" true,
  certPromised "movq $0, %rdi\nmovq $129, %rsi\nmovq $2, %rdx\nmovq $202, %rax\nsyscall" false)

end Scc.Sem.X64

/-- **`scc` correctness on x64**: `asm` is a correct lowering of the
WeakCore program `p` under the certificate's configuration `cfg`, i.e.
`Scc.Sem.Correct` for the canonical x64 target with the certificate's
thread slots and the source instance
of `p` under the `tso` memory model, with `cfg` well formed for the
canonical target and `asm` (`CertCfg.WF`, part of what a certificate
proves). The name a certificate states. -/
def Scc.Correct (cfg : Scc.Sem.CertCfg) (asm : Scc.Sem.X64.Asm) (p : CoreTerm.Prog) : Prop :=
  cfg.WF (Scc.Sem.X64.canonical cfg.slots) asm ∧
  Scc.Sem.Correct (Scc.Sem.X64.canonical cfg.slots) (Scc.Sem.SrcSem.source (cfg.src .tso) p) cfg.Λ cfg.B asm
