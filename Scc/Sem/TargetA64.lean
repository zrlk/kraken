/-
The canonical AArch64 target.

Kraken's AArch64 thread states (`Kraken.Promising.AArch64.State`), its
FEAT_LSE2 instruction semantics `isaLSE2` under `Arch.armv8`, and its
assembly parser (`Kraken.AArch64.Parser.parse`), with the extension hooks of
`Scc/Sem/Target.lean`:

- `regVal`: `X0`–`X30`, `SP`, and `NZCV` at its architectural bits 31–28.
- `privLoad`: an 8-byte little-endian load from the thread's private memory
  (`dmem`), if all 8 bytes are mapped.
- `threadAt E base prog syms`: the thread state of `prog` laid out from
  `base`, 4 bytes per instruction (`Directive.fakeSize`, as
  `AArch64.mkState`), halting after the last one, with label cells for the
  data symbols `syms` at their addresses, those below `base` before the
  code (`placeBelow`, the executable starting at the lowest, `exeStart`)
  and the others after it (`placeSyms`), so that `adrp` + `add :lo12:` of a
  data symbol gives its address; the entry state `E` (`sp` at the top of
  the zero-filled initial stack in private memory, every other register
  zero, the pc at `base`).
- `loadProg H E Λ prog syms mem`: `H.slots` thread slots: slot 0
  `threadAt` at `Λ.code.lo` (the first instruction is the entry point)
  with the data symbols `syms`, the others dormant (`dormantAt`: halted, no
  private memory); `mem` as the initial memory (8-byte words), the hooks'
  initial extension state under `Λ`.
- `target H E`: the `.text` sections of the assembly text (`textProgram`:
  `textSection`, then Kraken's `stripDirectives`), parsed by Kraken's
  parser, then `loadProg` with `Λ.symbols` and the `.rodata` symbols
  (`loadSyms`) and the initial memory `Λ.image` and the `.rodata` image
  (`rodataWords`, at `Λ.rodata.lo`, its code labels resolved to their
  addresses); refused unless the `.rodata` image fits `Λ.rodata` and agrees
  with `Λ.symbols` and its code labels resolve, no data symbol lies inside
  the code (`symsAbove`), and the initial stack is clear of the layout
  (`Entry.clear`).
  `resolve` parses the same way and gives a label of the program its
  address in `threadAt`'s layout (`labelAddr`), the pc of the instruction
  after it.
- `abi`: the kernel's view of a thread state (K1, `Scc/Sem/Kernel.lean`):
  `svc` (any immediate: Linux ignores it), the number in `x8`, arguments
  `x0`–`x5`, the result in `x0`, the pc past the `svc`; at `clone` the
  child gets `x0 = 0`, `sp` and `TPIDR_EL0` from the arguments; the thread
  pointer is `TPIDR_EL0`; the private memory is `dmem`.
- `kernel n`: the kernel model's hooks (`Kernel.hooks abi`, `Arch.armv8`,
  `n` thread slots); `canonical n := target (kernel n) Entry.linux`.
- `Scc.Correct cfg asm p`: the statement a certificate states, at
  `canonical cfg.slots` and `SrcSem.source (cfg.src .arm) p`.

Not modelled yet (`Scc/DESIGN.md` §7.1): the kernel's initial stack and
registers beyond `Entry` (arguments, environment, auxiliary vector); the
contents of `.data` from the text (the writable image comes from `Λ`;
`.rodata` is read from the text); a load of an
image word narrower than 8 bytes, or not 8-aligned, reads 0 (Kraken's
memory has no mixed-size accesses).

Sanity: `step_of_done` and `run_of_seqRun` (Kraken's single-thread step on
straight-line code is a step / run of the target without hooks), and an
executable check on `mov x0, #5; add x0, x0, #1` that the loaded
configuration's Kraken steps compute what `isaLSE2.exec` computes;
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
import Kraken.Promising.AArch64
import Kraken.AArch64.Parser

namespace Scc.Sem.A64

open Kraken.Promising Kraken.Promising.AArch64

/-- The 31 general registers, `X0` first. -/
def xRegs (r : Reg64s) : List UInt64 :=
  [r.X0, r.X1, r.X2, r.X3, r.X4, r.X5, r.X6, r.X7, r.X8, r.X9, r.X10, r.X11, r.X12, r.X13, r.X14, r.X15,
   r.X16, r.X17, r.X18, r.X19, r.X20, r.X21, r.X22, r.X23, r.X24, r.X25, r.X26, r.X27, r.X28, r.X29, r.X30]

/-- The flags as `NZCV` holds them: `N` at bit 31, `Z` 30, `C` 29, `V` 28. -/
def nzcv (f : StatusFlags) : BitVec 64 :=
  (BitVec.ofBool f.n).zeroExtend 64 <<< 31 ||| (BitVec.ofBool f.z).zeroExtend 64 <<< 30 |||
    (BitVec.ofBool f.c).zeroExtend 64 <<< 29 ||| (BitVec.ofBool f.v).zeroExtend 64 <<< 28

/-- The 64-bit value of a register. -/
def regVal (s : State) : RegId → BitVec 64
  | .x n => ((xRegs s.st.1.regs).getD n.val 0).toBitVec
  | .sp => s.st.1.regs.SP.toBitVec
  | .nzcv => nzcv s.st.1.status

/-- An 8-byte load from the private memory, if all 8 bytes are mapped. -/
def privLoad (s : State) (a : BitVec 64) : Option (BitVec 64) :=
  (s.st.1.dmem.loadInt a 8).map (BitVec.ofInt 64)

/-- The end of `prog`'s code laid out from `base`. -/
def codeEnd (base : Nat) (prog : Program) : Nat := base + (prog.map Directive.fakeSize).sum

/-- The thread state of `prog` laid out from `base`, 4 bytes per
instruction (`Directive.fakeSize`), halting after the last one, with label
cells for the data symbols `syms`: those below `base` before the code
(`placeBelow`, the executable starting at `exeStart base syms`), the others
after it (`placeSyms`); entry state `E`: `sp` at the top of the initial
stack, which is zero-filled private memory, every other register zero, the
pc at `base`; no declarations. -/
def threadAt (E : Entry) (base : Nat) (prog : Program) (syms : List (String × Nat)) : State where
  exe := (Int64.ofNat (exeStart base syms),
    placeBelow (.byteArray (.mk #[])) .label base syms ++
    prog.map (fun d => (d, Directive.fakeSize d)) ++
    placeSyms (.byteArray (.mk #[])) .label (codeEnd base prog) (symsFrom base syms))
  endPc := Int64.ofNat (codeEnd base prog)
  st := ({ regs := { SP := UInt64.ofNat E.sp }, dmem := E.stackMem }, Int64.ofNat base)

/-- 8-byte words `(address, value)` as initial shared memory. -/
def wordsMem (ws : List (Nat × Nat)) : List (Loc × Val) :=
  ws.map fun p => (⟨BitVec.ofNat 64 p.1, 8⟩, BitVec.ofNat 128 p.2)

/-- The initial memory of a layout: its static image, as 8-byte words. -/
def imageMem (Λ : Scc.Sem.Layout) : List (Loc × Val) := wordsMem Λ.image

/-- The program counter of a thread state. -/
def pcOf (s : State) : Nat := s.st.2.toBitVec.toNat

/-- The machine of the canonical target with hooks `H`. -/
abbrev machine (H : Hooks isaLSE2) : ExtMachine := ExtMachine.ofHooks isaLSE2 Arch.armv8 H regVal privLoad pcOf

/-- A dormant thread slot of `prog` (§2.1): `threadAt`'s program, halted
(the pc at the end address), zero registers, no private memory. A `clone`
replaces its state. -/
def dormantAt (E : Entry) (base : Nat) (prog : Program) (syms : List (String × Nat)) : State :=
  let s := threadAt E base prog syms
  { s with st := ({}, s.endPc) }

/-- Load a parsed program: `H.slots` thread slots, slot 0 at `Λ.code.lo` with
the data symbols `syms` and entry state `E`, the others dormant; `mem` as
the initial memory. -/
def loadProg (H : Hooks isaLSE2) (E : Entry) (Λ : Scc.Sem.Layout) (prog : Program)
    (syms : List (String × Nat)) (mem : List (Loc × Val)) : (machine H).Cfg :=
  (Config.init (threadAt E Λ.code.lo prog syms ::
    List.replicate (H.slots - 1) (dormantAt E Λ.code.lo prog syms)) mem, H.init E Λ)

/-- The name of a label cell. -/
def labelName : Directive → Option String
  | .label l => some l
  | _ => none

/-- The program of a text's `.text` sections (Kraken's parser, directive
lines dropped; AArch64 instructions are 4 bytes, so `.p2align 2` pads
nothing). -/
def textProgram (asm : String) : Except String Program :=
  Kraken.AArch64.Parser.parse (Kraken.AArch64.Parser.stripDirectives (textSection asm))

/-- **The AArch64 target with hooks `H` and entry state `E`**: the text's
`.text` sections, parsed by Kraken's parser, its `.rodata` image at
`Λ.rodata.lo` in shared memory beside `Λ.image` (`rodataWords`, `.quad`s of
code labels at their model addresses), loaded by `loadProg` with the data
symbols `loadSyms`; refused if a data section has a line the loader does not read, the `.rodata` image does not fit
`Λ.rodata` (`rodataFits`), `Λ.symbols` disagrees with it (`symsAgree`), a
`.quad` label is unknown (`quadsResolve`), a data symbol lies inside the
code (`symsAbove`), or the initial stack is not clear of the layout
(`Entry.clear`). -/
def target (H : Hooks isaLSE2) (E : Entry) : Target where
  M := machine H
  Asm := String
  load asm Λ := do
    let prog ← (textProgram asm).toOption
    let secs ← dataSections asm
    let ro := secs.rodata
    let code (l : String) : Option Nat :=
      (labelAddr labelName Directive.fakeSize Λ.code.lo l prog).orElse fun _ => Λ.symbols.lookup l
    let syms := loadSyms Λ ro
    let fin := codeEnd Λ.code.lo prog
    if rodataFits Λ ro && symsAgree Λ ro && quadsResolve Λ ro code &&
        symsAbove Λ.code.lo fin syms && E.clear Λ then
      some (loadProg H E Λ prog syms (imageMem Λ ++ wordsMem (rodataWords Λ ro code)))
    else none
  resolve asm Λ l :=
    match textProgram asm with
    | .ok prog => labelAddr labelName Directive.fakeSize Λ.code.lo l prog
    | .error _ => none

/-! ## The kernel's view of a thread -/

/-- The thread is at a supervisor call (`svc #imm`; Linux ignores `imm`). -/
def atSvc (s : State) : Bool :=
  match s.directive with
  | some (.instr ⟨_, .SVC _⟩) => true
  | _ => false

/-- The thread is at a `nop` (a transfer site's instruction). -/
def atNop (s : State) : Bool :=
  match s.directive with
  | some (.instr ⟨_, .NOP⟩) => true
  | _ => false

/-- The pc of the instruction after the one at the pc. -/
def nextPc (s : State) : Int64 :=
  s.st.2 + Int64.ofNat ((s.exe.directivesAtAddress s.st.2).map (·.2)).sum

/-- **The AArch64 Linux system-call convention** (K1): `svc`, number in
`x8`, arguments in `x0`–`x5`, result in `x0` (every other register
preserved), the pc past the `svc`; at `clone` the child has the parent's
registers but `x0 = 0`, `sp = stack`, `TPIDR_EL0 = tls`; the thread pointer
is `TPIDR_EL0`; the stack pointer is `sp`; a transfer site is a `nop`,
stepped over. -/
def abi : Kernel.Abi isaLSE2 where
  nrs := Kernel.Nrs.a64
  atSys := atSvc
  nr s := s.st.1.regs.X8.toNat
  arg s i := ((xRegs s.st.1.regs).getD i.val 0).toNat
  ret s r := { s with st := ({ s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat r.toNat } }, nextPc s) }
  retRegs := [.x 0]
  child s stack tls :=
    { s with st := ({ s.st.1 with
        regs := { s.st.1.regs with X0 := 0, SP := UInt64.ofNat stack, TPIDR_EL0 := UInt64.ofNat tls },
        dmem := ∅ }, nextPc s) }
  setTp s a := { s with st := ({ s.st.1 with regs := { s.st.1.regs with TPIDR_EL0 := UInt64.ofNat a } }, s.st.2) }
  tp s := s.st.1.regs.TPIDR_EL0.toBitVec
  dmem s := s.st.1.dmem
  setDmem s m := { s with st := ({ s.st.1 with dmem := m }, s.st.2) }
  sp s := s.st.1.regs.SP.toNat
  pc := pcOf
  atNop := atNop
  skip s := { s with st := (s.st.1, nextPc s) }
  dmem_setDmem _ _ := rfl
  dmem_skip _ := rfl

/-- **The kernel model's hooks** for AArch64 (`Scc/Sem/Kernel.lean`): under
`Arch.armv8`, with `n` thread slots. -/
abbrev kernel (n : Nat) : Hooks isaLSE2 := Kernel.hooks abi Arch.armv8 n

/-- **The canonical AArch64 target with `n` thread slots**: the kernel
model's hooks, the Linux entry state `Entry.linux`: the oracle's fixed entry
state, not the certified statement (that is `CorrectE`, every admissible
entry state, `Scc/Sem/CorrectEA64.lean`). A certificate states `Correct` at
`canonical cfg.slots` (`Scc.Correct`), with `cfg.slots = B.threads + 1`
(`CertCfg.WF`). -/
def canonical (n : Nat) : Target := target (kernel n) Entry.linux

/-! ## Sanity -/

/-- **Kraken's single-thread step at a no-event instruction is a step of the
canonical target**, with no events, to the thread in the state Kraken's
step gives. -/
theorem step_of_done {μ : Marks} (hμ : ∀ k, μ.site k = none) {c : (machine (Hooks.none isaLSE2)).Cfg} {tid : Nat}
    {t : Thread isaLSE2} {s : State} (ht : c.1.threads[tid]? = some t) (hp : t.prom = [])
    (hex : isaLSE2.exec t.st = some (.done s)) :
    ∃ th, (machine (Hooks.none isaLSE2)).Step μ tid c [] (c.1.withThread tid th c.1.mem, c.2) ∧ th.st = s ∧
      th.prom = [] :=
  ExtMachine.ofHooks_step_of_done ht rfl (fun k a h => by simp [hμ k] at h) rfl id hp hex

/-- **A straight-line run of Kraken's single-thread step from a loaded
program is a run of the canonical target**: thread 0 of `loadProg` reaches
the state Kraken's step reaches, with the image memory unchanged. -/
theorem run_of_seqRun (μ : Marks) (hμ : ∀ k, μ.site k = none) (E : Entry) (Λ : Scc.Sem.Layout) (prog : Program)
    (syms : List (String × Nat)) (mem : List (Loc × Val)) {s : State}
    (hr : SeqRun isaLSE2 (threadAt E Λ.code.lo prog syms) s) :
    ∃ c' th, (machine (Hooks.none isaLSE2)).Run μ (loadProg (Hooks.none isaLSE2) E Λ prog syms mem) [] c' ∧
      c'.1.threads[0]? = some th ∧ th.st = s ∧ th.prom = [] ∧ c'.1.mem = { init := mem, msgs := #[] } :=
  let ⟨c', th, h1, h2, h3, h4, h5, _⟩ :=
    ExtMachine.ofHooks_run_of_seqRun hr (c := loadProg (Hooks.none isaLSE2) E Λ prog syms mem)
    (t := Thread.init _) rfl rfl rfl rfl id (fun _ _ => rfl) (fun _ _ k a h => by simp [hμ k] at h)
  ⟨c', th, h1, h2, h3, h4, h5⟩

/-- A small entry state for the checks: a 64-byte initial stack at 0x1000. -/
private def Et : Entry := ⟨⟨0x1000, 64⟩⟩

/-- The trivial layout, its text at 16, with one data symbol `val` at 48
holding 42. -/
private def Λt : Scc.Sem.Layout := { trivLayout with symbols := [("val", 48)], image := [(48, 42)] }

/-- Kraken's single-thread step, iterated on thread 0's state while each
instruction is a no-event step: the register `X0` and the pc after each. -/
private def seqTrace : Nat → State → List String
  | 0, _ => []
  | n + 1, s =>
    match isaLSE2.exec s with
    | some (.done s') => s!"x0={s'.st.1.regs.X0} pc={s'.st.2}" :: seqTrace n s'
    | none => ["halt"]
    | some _ => ["event"]

/-- The machine's steps of thread 0 (the first successful outcome of
Kraken's `stepThread`), from the loaded configuration: `X0`, `X9`, `SP`, the
pc and the number of shared messages after each. -/
private def machTrace : Nat → Config isaLSE2 → List String
  | 0, _ => []
  | n + 1, c =>
    match stepThread Arch.armv8 c 0 with
    | some (.ok o :: _) =>
      let r := o.thread.st.st.1.regs
      s!"x0={r.X0} x9={r.X9} sp={r.SP} pc={o.thread.st.st.2} msgs={o.mem.msgs.size}" ::
        machTrace n (c.withThread 0 o.thread o.mem)
    | none => ["halt"]
    | _ => ["error"]

/-- The target's run on `asm` under `Λt` and `Et`. -/
private def run (asm : String) : Option (List String) :=
  ((target (Hooks.none isaLSE2) Et).load asm Λt).map fun (c : (machine (Hooks.none isaLSE2)).Cfg) => machTrace 8 c.1

private def straight : String := "mov x0, #5\nadd x0, x0, #1"

/-- info: some (["x0=5 pc=20", "x0=6 pc=24", "halt"], ["x0=5 pc=20", "x0=6 pc=24", "halt"]) -/
#guard_msgs in
#eval ((target (Hooks.none isaLSE2) Et).load straight Λt).map fun (c : (machine (Hooks.none isaLSE2)).Cfg) =>
  ((machTrace 5 c.1).map fun l => " ".intercalate ((l.splitOn " ").filter fun w =>
      w.startsWith "x0=" || w.startsWith "pc=" || w == "halt"),
    (c.1.threads[0]?.map fun t => seqTrace 5 t.st).getD [])

/-- **A data symbol resolves**: `adrp` + `add :lo12:` of `val` (scc's `la`)
gives its address 48, and an 8-byte load from it reads the image word 42.
The data section's own label and bytes are ignored (`textSection`). -/
private def dataRef : String :=
  "\t.text\n_start:\n\tadrp x9, val\n\tadd x9, x9, :lo12:val\n\tldr x0, [x9]\n" ++
  "\t.data\n\t.balign 8\nval:\n\t.byte 42, 0, 0, 0, 0, 0, 0, 0\n"

/-- info: some ["x0=0 x9=0 sp=4160 pc=20 msgs=0", "x0=0 x9=48 sp=4160 pc=24 msgs=0", "x0=42 x9=48 sp=4160 pc=28 msgs=0", "halt"] -/
#guard_msgs in
#eval run dataRef

/-- **The entry stack is private**: `sp` starts at the top of `Et`'s stack
(0x1040 = 4160); a store below it is to private memory (no shared message)
and reads back. -/
private def entryStack : String := "mov x0, #7\nsub sp, sp, #16\nstr x0, [sp]\nmov x0, #0\nldr x0, [sp]"

/-- info: some
  ["x0=7 x9=0 sp=4160 pc=20 msgs=0", "x0=7 x9=0 sp=4144 pc=24 msgs=0", "x0=7 x9=0 sp=4144 pc=28 msgs=0",
    "x0=0 x9=0 sp=4144 pc=32 msgs=0", "x0=7 x9=0 sp=4144 pc=36 msgs=0", "halt"] -/
#guard_msgs in
#eval run entryStack

/-- Thread 0's pc after `n` machine steps from the loaded configuration. -/
private def pcAfter (asm : String) (n : Nat) : Option Nat :=
  ((target (Hooks.none isaLSE2) Et).load asm Λt).bind fun (c : (machine (Hooks.none isaLSE2)).Cfg) => go n c.1
where
  go : Nat → Config isaLSE2 → Option Nat
    | 0, c => c.threads[0]?.map (pcOf ·.st)
    | n + 1, c =>
      match stepThread Arch.armv8 c 0 with
      | some (.ok o :: _) => go n (c.withThread 0 o.thread o.mem)
      | _ => none

private def labelled : String := "mov x0, #5\nfoo:\nadd x0, x0, #1"

-- `resolve` gives a `.text` label the model pc of the instruction after it
-- (the pc after the first step), and nothing for a label the text lacks.
#guard (target (Hooks.none isaLSE2) Et).resolve labelled Λt "foo" == some 20 &&
  pcAfter labelled 1 == some 20 && (target (Hooks.none isaLSE2) Et).resolve labelled Λt "bar" == none

-- Without hooks the loaded program has one thread slot; with the kernel
-- model, the slot count it is given.
#guard (target (Hooks.none isaLSE2) Et).threadSlots straight Λt == 1 &&
  (target (kernel 7) Et).threadSlots straight Λt == 7 && (canonical 3).threadSlots straight Λt == 3

-- A data symbol inside the code (`[16, 28)`) is refused, at its start or
-- its last byte; one at its end is not.
#guard ((target (Hooks.none isaLSE2) Et).load dataRef { Λt with symbols := [("val", 16)] }).isNone &&
  ((target (Hooks.none isaLSE2) Et).load dataRef { Λt with symbols := [("val", 27)] }).isNone &&
  ((target (Hooks.none isaLSE2) Et).load dataRef { Λt with symbols := [("val", 28)] }).isSome

/-- **A data symbol below the code resolves**: with `val` at 8, below the
text at 16, the executable starts at 8 with `val`'s label cell, padded to
the code; `adrp` + `add :lo12:` gives 8 and the load reads the word there. -/
private def Λlow : Scc.Sem.Layout := { Λt with symbols := [("val", 8)], image := [(8, 42)] }

/-- info: some ["x0=0 x9=0 sp=4160 pc=20 msgs=0", "x0=0 x9=8 sp=4160 pc=24 msgs=0", "x0=42 x9=8 sp=4160 pc=28 msgs=0", "halt"] -/
#guard_msgs in
#eval ((target (Hooks.none isaLSE2) Et).load dataRef Λlow).map fun (c : (machine (Hooks.none isaLSE2)).Cfg) =>
  machTrace 8 c.1

-- The cells around the code (one `nop` at 16): symbols below it from the
-- lowest (`a` at 4), no padding between two at one address (`b`, `c` at 8),
-- padding to the code at 16; above it likewise (`placeSyms`: none for `e`
-- at the end of the code, 20). Without low symbols the executable starts at
-- the code.
private def cellsAround (syms : List (String × Nat)) : Option (Int64 × List (String × Nat)) :=
  match textProgram "nop" with
  | .ok p => some ((threadAt Et 16 p syms).exe.1,
      (threadAt Et 16 p syms).exe.2.map fun (d, z) => (match d with | .label l => l | _ => "_", z))
  | .error _ => none

#guard cellsAround [("d", 40), ("b", 8), ("a", 4), ("c", 8)] ==
    some (4, [("a", 0), ("_", 4), ("b", 0), ("c", 0), ("_", 8), ("_", 4), ("_", 20), ("d", 0)]) &&
  cellsAround [("d", 40)] == some (16, [("_", 4), ("_", 20), ("d", 0)]) &&
  cellsAround [("d", 40), ("e", 20)] == some (16, [("_", 4), ("e", 0), ("_", 20), ("d", 0)])

/-! ## Sanity of the kernel model -/

/-- **An unknown system-call number is a fault** of the canonical target's
machine: a running thread at `svc` with a number in `x8` that is none of
`Kernel.Nrs.a64`'s. -/
theorem unsupported_fault {n : Nat} {c : (machine (kernel n)).Cfg} {tid : Nat} {t : Thread isaLSE2}
    (ht : c.1.threads[tid]? = some t) (hr : c.2.runs tid = true) (hx : c.2.exited = none)
    (hs : atSvc t.st = true) (hn : t.st.st.1.regs.X8.toNat ∉ [64, 93, 94, 98, 134, 220]) :
    (machine (kernel n)).fault c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hn
  exact .inr (Kernel.fault_of_unsupported (K := abi) _ _ ht hr hx hs
    (Kernel.decode_none _ h1 h2 h3 h4 h5 h6 (by simp [abi, Kernel.Nrs.a64])))

/-- **A transfer site's `nop` has no register dependency**, so a
certification step there keeps the thread's register views
(`Kernel.certSem_step_of_take`, `Kernel.certSem_step_of_release`). -/
theorem deps_of_atNop {s : State} (h : atNop s = true) : isaLSE2.deps s = {} := by
  unfold atNop at h
  split at h
  · rename_i i hd
    show depsLSE2 s = {}
    simp [depsLSE2, deps, hd, _root_.Directive.deps]
    rfl
  · cases h

/-- A `nop` is not a system call. -/
theorem not_atSys_of_atNop {s : State} (h : atNop s = true) : atSvc s = false := by
  unfold atNop at h
  unfold atSvc
  split at h <;> simp_all

/-- **The transfer is forced** on the canonical AArch64 target: a thread at
the take site's `nop` (and at no release site) takes no instruction step,
spawn or system call; its only step is the take of the range `x0`, `x1`
name (`Kernel.step_at_take`). -/
theorem take_forced {n : Nat} {μ : Marks} {c c' : (machine (kernel n)).Cfg} {tid : Nat} {es : List Ev}
    {t : Thread isaLSE2} (ht : c.1.threads[tid]? = some t) (hn : atNop t.st = true)
    (hs : (machine (kernel n)).AtSite μ .take c tid) (hnr : ¬ (machine (kernel n)).AtSite μ .release c tid)
    (h : (machine (kernel n)).Step μ tid c es c') : es = [] ∧ Kernel.takeStep abi tid c = some c' := by
  refine Kernel.step_at_take ht ?_ hs hnr h
  show atSvc t.st = false
  unfold atNop at hn
  unfold atSvc
  split at hn <;> simp_all

/-- **A loaded layout is clear of the initial stack**: the loader refuses
any other (`Entry.clear`), so `Correct`'s start clause, which needs a loaded
configuration, implies it. -/
theorem load_clear {H : Hooks isaLSE2} {E : Entry} {asm : String} {Λ : Scc.Sem.Layout} {c : (machine H).Cfg}
    (h : (target H E).load asm Λ = some c) : E.clear Λ = true := by
  simp only [target, Option.bind_eq_bind] at h
  obtain ⟨prog, -, h⟩ := Option.bind_eq_some_iff.mp h
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
private abbrev Kt : Hooks isaLSE2 := Kernel.hooks abi Arch.armv8 2

/-- Thread 0 of a configuration of the kernel model, run for at most `n`
steps: at a system call the kernel's step (`Kernel.sysStep`) with the next
choice of `ps`, printing its events; elsewhere Kraken's step (its first
outcome); a kernel fault (`Kernel.faultAt`) or the process's exit ends the
run. -/
private def kRun : Nat → List Kernel.Pick → Config isaLSE2 × Kernel.KState → List String
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
            match Kernel.sysStep abi Arch.armv8 0 c p with
            | some (es, c') => es.map (fun e => s!"{repr e}") ++ kRun n ps c'
            | none => ["no kernel step"]
        else
          match stepThread Arch.armv8 c.1 0 with
          | some (.ok o :: _) => kRun n ps (c.1.withThread 0 o.thread o.mem, c.2)
          | _ => ["stuck"]

/-- `Λt` with `val` (holding 42) at 256, above the checks' code, and the
stack pool `[0x1f00, 0x2000)`. -/
private def Λk : Scc.Sem.Layout :=
  { Λt with symbols := [("val", 256)], image := [(256, 42)], stackPool := ⟨0x1f00, 0x100⟩ }

/-- The kernel model's run of `asm` under `Λk` and `Et`, with the choices
`ps`. -/
private def krun (asm : String) (ps : List Kernel.Pick) : Option (List String) :=
  ((target Kt Et).load asm Λk).map fun (c : (machine Kt).Cfg) => kRun 32 ps c

/-- `write(1, val, 1)` then `exit_group(0)`: `val` holds 42 (`Λk`). -/
private def writeExit : String :=
  "\t.text\n_start:\n\tadrp x1, val\n\tadd x1, x1, :lo12:val\n\tmov x0, #1\n\tmov x2, #1\n" ++
  "\tmov x8, #64\n\tsvc #0\n\tmov x0, #0\n\tmov x8, #94\n\tsvc #0\n"

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
private def toSys : Nat → Config isaLSE2 × Kernel.KState → Option (Config isaLSE2 × Kernel.KState)
  | 0, _ => none
  | n + 1, c =>
    match c.1.threads[0]? with
    | none => none
    | some t =>
      if abi.atSys t.st then some c else
      match stepThread Arch.armv8 c.1 0 with
      | some (.ok o :: _) => toSys n (c.1.withThread 0 o.thread o.mem, c.2)
      | _ => none

/-- `clone(cloneFlags, 0x2000, 0, tls = 0x77, 0)`, arguments in `x0`–`x4`. -/
private def cloneProg : String := "movz x0, #0x0f00\nmovk x0, #0xd, lsl #16\nmov x1, #0x2000\nmov x2, #0\nmov x3, #0x77\nmov x4, #0\nmov x8, #220\nsvc #0"

/-- The threads of a configuration: `x0`, `sp`, `TPIDR_EL0`, the pc, and
whether the word below `sp` is private (`privLoad`). -/
private def slotsOf (c : Config isaLSE2) : List String :=
  c.threads.toList.zipIdx.map fun (t, i) =>
    let r := t.st.st.1.regs
    s!"slot {i}: x0={r.X0} sp={r.SP} tp={r.TPIDR_EL0} pc={t.st.st.2} " ++
      s!"priv={(privLoad t.st (BitVec.ofNat 64 (r.SP.toNat - 8))).isSome}"

/- **`clone` activates the dormant slot 1** (`Kernel.spawnStep`, child id
5): the parent gets 5 and moves past the system call; the child starts
there with result 0, the stack pointer 0x2000 = 8192 and thread pointer
0x77 = 119 from the arguments (`x0`, `sp`, `TPIDR_EL0`); the slots are then
both running. The parent holds no range ending at 0x2000, so the child's
stack is shared memory and it has no stack range. -/
/--
info: some (["slot 0: x0=5 sp=4160 tp=0 pc=48 priv=true", "slot 1: x0=0 sp=8192 tp=119 pc=48 priv=false"],
 #[Scc.Sem.Kernel.Slot.run 0, Scc.Sem.Kernel.Slot.run 0],
 none)
-/
#guard_msgs in
#eval ((target Kt Et).load cloneProg Λk).bind fun (c : (machine Kt).Cfg) =>
  (toSys 16 c).bind fun c => (Kernel.spawnStep abi 0 c 1 5).map fun c' =>
    (slotsOf c'.1, c'.2.slots, Kt.stackRange c' 1)

/-- A range as text. -/
private def showR (r : Range) : String := s!"[{r.lo}+{r.size}]"

/-- Thread 0 run for at most `n` steps: at the take or release site
(addresses `ts`, `rs`) the kernel's transfer (`Kernel.takeStep`,
`Kernel.releaseStep`), printed with the thread's stack range after it; at a
system call it stops; elsewhere Kraken's step. The log and the final
configuration. -/
private def xRun (ts rs : Option Nat) : Nat → Config isaLSE2 × Kernel.KState →
    List String × (Config isaLSE2 × Kernel.KState)
  | 0, c => (["out of fuel"], c)
  | n + 1, c =>
    match c.1.threads[0]? with
    | none => (["no thread"], c)
    | some t =>
      let r := Kernel.siteRange abi t.st
      let site (nm : String) (st : Option (Config isaLSE2 × Kernel.KState)) :=
        match st with
        | some c' =>
          let (l, c'') := xRun ts rs n c'
          (s!"{nm} {showR r} stack={((Kernel.stackRangeOf abi c' 0).map showR).getD "none"}" :: l, c'')
        | none => ([s!"stuck at {nm} {showR r}"], c)
      if ts = some (pcOf t.st) then site "take" (Kernel.takeStep abi 0 c)
      else if rs = some (pcOf t.st) then site "release" (Kernel.releaseStep abi 0 c)
      else if abi.atSys t.st then (["at svc"], c)
      else
        match stepThread Arch.armv8 c.1 0 with
        | some (.ok o :: _) => xRun ts rs n (c.1.withThread 0 o.thread o.mem, c.2)
        | none => (["halt"], c)
        | _ => (["stuck"], c)

/-- The transfer sites of `asm` (`XferKind.label`) and `xRun` on it under
`Λk`, `Et`, with two slots. -/
private def xrun (asm : String) (n : Nat) : Option (List String × (Config isaLSE2 × Kernel.KState)) :=
  ((target Kt Et).load asm Λk).map fun (c : (machine Kt).Cfg) =>
    xRun ((target Kt Et).resolve asm Λk XferKind.take.label)
      ((target Kt Et).resolve asm Λk XferKind.release.label) n c

/-- The runtime's transfer routines, reduced to their sites. -/
private def sites : String :=
  "\tb end\ntake:\nscc_rt_take_site:\n\tnop\n\tret\nrelease:\nscc_rt_release_site:\n\tnop\n\tret\nend:\n"

/-- Take `[0x1fc0, 0x2000)` (the child's stack, as `scc_rt_thread_init`
does), then `clone` with stack pointer 0x2000. -/
private def cloneTake : String :=
  "\tmov x0, #0x1fc0\n\tmov x1, #0x40\n\tbl take\n" ++
  "\tmovz x0, #0x0f00\n\tmovk x0, #0xd, lsl #16\n\tmov x1, #0x2000\n\tmov x2, #0\n\tmov x3, #0x77\n" ++
  "\tmov x4, #0\n\tmov x8, #220\n\tsvc #0\n" ++ sites

/- **`clone` hands the child its stack range**: the parent takes
`[0x1fc0, 0x2000)` at the take site (its stack pointer is elsewhere, so it
is not the parent's stack range); `clone` with stack pointer 0x2000 moves
it to the child, whose stack is then private and whose stack range it is. -/
/--
info: some (["take [8128+64] stack=none", "at svc"],
 some (["slot 0: x0=5 sp=4160 tp=0 pc=60 priv=true", "slot 1: x0=0 sp=8192 tp=119 pc=60 priv=true"],
  [(1, { lo := 8128, size := 64 })],
  none,
  some { lo := 8128, size := 64 }))
-/
#guard_msgs in
#eval (xrun cloneTake 32).map fun (p : List String × (Config isaLSE2 × Kernel.KState)) =>
  (p.1, (Kernel.spawnStep abi 0 p.2 1 5).map fun (c' : Config isaLSE2 × Kernel.KState) =>
    (slotsOf c'.1, c'.2.held, Kt.stackRange c' 0, Kt.stackRange c' 1))

/-- Grow and reuse: take `r1 = [0x1f00, 0x1f40)`, switch `sp` into it and
store 7 at 0x1f00; take `r2 = [0x1f80, 0x2000)` (the grow routine's new
range) and switch `sp` to its top; release `r1` (the thread has left it);
take `r1` again and load 0x1f00. -/
private def growReuse : String :=
  "\tmov x0, #0x1f00\n\tmov x1, #0x40\n\tbl take\n\tmov x11, #0x1f40\n\tadd sp, x11, #0\n" ++
  "\tmov x9, #7\n\tmov x10, #0x1f00\n\tstr x9, [x10]\n" ++
  "\tmov x0, #0x1f80\n\tmov x1, #0x80\n\tbl take\n\tmov x11, #0x2000\n\tadd sp, x11, #0\n" ++
  "\tmov x0, #0x1f00\n\tmov x1, #0x40\n\tbl release\n" ++
  "\tmov x0, #0x1f00\n\tmov x1, #0x40\n\tbl take\n\tldr x2, [x10]\n" ++ sites

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
#eval (xrun growReuse 64).map fun (p : List String × (Config isaLSE2 × Kernel.KState)) =>
  (p.1, (p.2.1.threads[0]?.map fun (t : Thread isaLSE2) => t.st.st.1.regs.X2).getD 0, p.2.1.mem.msgs.size,
    p.2.2.held)

/- **No release of the range a thread is on**: with `sp` in `r1`, the
release of `r1` has no step (the thread is stuck, which progress
excludes). -/
/-- info: some ["take [7936+64] stack=none", "stuck at release [7936+64]"] -/
#guard_msgs in
#eval (xrun ("\tmov x0, #0x1f00\n\tmov x1, #0x40\n\tbl take\n\tmov x11, #0x1f40\n\tadd sp, x11, #0\n" ++
  "\tbl release\n" ++ sites) 32).map (·.1)

/- **A range is not taken twice**: the second take of `r1` while held is
stuck. -/
/-- info: some ["take [7936+64] stack=none", "stuck at take [7936+64]"] -/
#guard_msgs in
#eval (xrun ("\tmov x0, #0x1f00\n\tmov x1, #0x40\n\tbl take\n\tbl take\n" ++ sites) 32).map (·.1)

/- **`clone` with every slot used is a fault** (one slot: the entry
thread's). -/
/-- info: some true -/
#guard_msgs in
#eval ((target (Kernel.hooks abi Arch.armv8 1) Et).load cloneProg Λk).bind
  fun (c : (machine (Kernel.hooks abi Arch.armv8 1)).Cfg) => (toSys 16 c).map fun c => Kernel.faultAt abi c 0

/- **An unknown system-call number faults.** -/
/-- info: some ["fault"] -/
#guard_msgs in
#eval krun "mov x8, #999\nsvc #0" []

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
  ((target Kt Et).load asm Λk).bind fun (c : (machine Kt).Cfg) => (go n c).map (Kernel.rootUnmapped abi · 0)
where
  go : Nat → Config isaLSE2 × Kernel.KState → Option (Config isaLSE2 × Kernel.KState)
    | 0, c => some c
    | n + 1, c =>
      match stepThread Arch.armv8 c.1 0 with
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
#eval [unmappedAfter "mov x9, #48\nldr x0, [x9]" 1, unmappedAfter "mov x9, #16\nldr x0, [x9]" 1,
  unmappedAfter "mov x9, #0x1f00\nldr x0, [x9]" 1, unmappedAfter "mov x9, #64\nstr x0, [x9]" 1,
  unmappedAfter "ldr x0, [sp, #-8]" 0, unmappedAfter "mov x9, #0x9000\nldr x0, [x9]" 1,
  unmappedAfter "mov x9, #16\nstr x0, [x9]" 1, unmappedAfter "mov x9, #76\nstr x0, [x9]" 1]

-- The loader refuses an initial stack that meets the layout (here `Λt`'s
-- code), and the Linux entry state is clear of the trivial layout.
#guard ((target (Hooks.none isaLSE2) ⟨⟨40, 64⟩⟩).load straight Λt).isNone &&
  ((target (Hooks.none isaLSE2) Et).load straight Λt).isSome && Entry.linux.clear trivLayout

/-- `asm` (under `Λk`, `Et`) followed by `str x0, [x9]` with `x9 = 48`:
the values thread 0 may promise to 48 now, certified under `Kernel.certExec`
(`cert = true`) or under the ISA's `exec` (`cert = false`). -/
private def certPromised (asm : String) (cert : Bool) : Option (List Nat) :=
  ((target Kt Et).load ("mov x9, #48\n" ++ asm ++ "\nstr x0, [x9]") Λk).map fun (c : (machine Kt).Cfg) =>
    let ps := if cert then (certifiedPromisesWith Arch.armv8 (Kernel.certExec abi) {} c.1 0 16).1
      else (certifiedPromises Arch.armv8 {} c.1 0 16).1
    ps.filterMap fun (c', _) => c'.mem.msgs.back?.map (·.val.toNat)

/- **Certification runs through system calls** (`Kernel.certExec`): a store
of the result of `futex` wake (count 2) may be promised with each count the
kernel model may return, `0`, `1`, `2`; of `rt_sigaction`, `0`; nothing
after `exit_group`, which does not return. The ISA's `exec` alone certifies
no store after a system call. -/
/-- info: (some [2, 1, 0], some [0], some [], some []) -/
#guard_msgs in
#eval (certPromised "mov x0, #0\nmov x1, #129\nmov x2, #2\nmov x8, #98\nsvc #0" true,
  certPromised "mov x0, #13\nmov x1, #0\nmov x2, #0\nmov x3, #8\nmov x8, #134\nsvc #0" true,
  certPromised "mov x0, #0\nmov x8, #94\nsvc #0" true,
  certPromised "mov x0, #0\nmov x1, #129\nmov x2, #2\nmov x8, #98\nsvc #0" false)

end Scc.Sem.A64

/-- **`scc` correctness on AArch64**: `asm` is a correct lowering of the
WeakCore program `p` under the certificate's configuration `cfg`, i.e.
`Scc.Sem.Correct` for the canonical AArch64 target with the certificate's
thread slots and the source instance
of `p` under the `arm` memory model, with `cfg` well formed for the
canonical target and `asm` (`CertCfg.WF`, part of what a certificate
proves). The name a certificate states. -/
def Scc.Correct (cfg : Scc.Sem.CertCfg) (asm : String) (p : CoreTerm.Prog) : Prop :=
  cfg.WF (Scc.Sem.A64.canonical cfg.slots) asm ∧
  Scc.Sem.Correct (Scc.Sem.A64.canonical cfg.slots) (Scc.Sem.SrcSem.source (cfg.src .arm) p) cfg.Λ cfg.B asm
