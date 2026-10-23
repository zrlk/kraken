/-
The canonical targets, ISA-independent part.

`Scc/Sem/TargetA64.lean` and `Scc/Sem/TargetX64.lean` (one file each, as
Kraken's AArch64 and x64 modules cannot be imported together) build the
canonical `Target` of each ISA from Kraken's thread states, instruction
semantics (`isaLSE2` / `X64.isa`, under `Arch.armv8` / `Arch.tso`) and
assembly parsers. This file has what they share:

- `Hooks I`: the parts of the extended machine (`Scc/DESIGN.md` §2) that
  Kraken's machine does not have: the system-call instruction and its steps,
  the thread-creation and range-transfer steps (at the transfer sites,
  `XferKind`), the process and thread exit
  records, the thread slots, the stack ranges, the thread pointer. Each is
  an explicit field; nothing here gives it a meaning. `Hooks.none` is the
  instance with none of them (no extension step, no extension state, one
  thread slot); the kernel model (`Scc/Sem/Kernel.lean`, `Kernel.hooks`)
  is the canonical targets' instance.
- `ExtMachine.ofHooks I A H regVal privLoad`: the extended machine with
  Kraken's instruction steps and the hooks `H`.
- Sanity lemmas: with `Hooks.none` and no transfer site a step is exactly a
  step of Kraken's existing machine (`ofHooks_none_step_iff`); at a no-event instruction
  (Kraken's single-thread step `I.exec st = some (.done s)`) the instance has
  a step to `s` (`ofHooks_step_of_done`), and every instruction step of that
  thread goes to `s` (`ofHooks_instr_done`); a straight-line run of Kraken's
  single-thread step is a run of the instance (`ofHooks_run_of_seqRun`).

Loader pieces shared by both ISAs:

- `textSection`: the lines of the text's `.text` sections (the `.data` and
  `.bss` contents come from the layout's image, their labels from the
  layout's symbols).
- `dataSections`, `rodataWords`, `loadSyms` and the checks `rodataFits`,
  `symsAgree`, `quadsResolve`: the text's data sections as
  `Kraken.DataImage` items, and its `.rodata` laid out at `Λ.rodata.lo` as
  the loaders' read-only image (`Scc/DESIGN.md` §7.2, *`.rodata`*).
- `labelAddr`: the address of a code label in the model layout, which the
  targets' `resolve` gives.
- `placeSyms`, `placeBelow`: label cells for the layout's data symbols
  after and before the code, at their addresses (the executable then starts
  at `exeStart`, the lowest symbol below the code), so that a text reference
  to a data symbol (x64 `leaq sym(%rip)`, AArch64 `adrp` + `add :lo12:`)
  resolves to it; `symsAbove`: no data symbol lies inside the code.
- `Entry`: the process entry state the loader assumes (part of the trusted
  base, `Scc/DESIGN.md` §4); `Entry.clear`: its initial stack is clear of
  the layout, which the loaders check.
- `CertCfg`: a certificate's layout, budget, thread slots and source
  parameters, from which each ISA file defines `Scc.Correct` (the canonical
  target with `CertCfg.slots` thread slots); `CertCfg.WF` (the slots are
  `B.threads + 1`, the capacity covers `Target.threadSlots` and exceeds
  `B.threads`; `threads_abort_unjustified` shows why the last is needed).

`Scc/DESIGN.md` §7 lists each hook with the Kraken change it needs.
-/
import Scc.Sem.Correct
import Kraken.Promising.Lower.Events
import Kraken.Mem
import Kraken.DataImageWords

namespace Scc.Sem

open Kraken.Promising

/-! ## Loader pieces -/

/-- The lines of the `.text` sections of an assembly text: a line starting
`.text` opens one, a line starting `.data`, `.bss`, `.section` or
`.rodata` opens a data section, and the text starts in `.text`. Section
directives themselves are dropped. -/
def textSection (asm : String) : String :=
  let step (acc : Bool × List String) (l : String) : Bool × List String :=
    let t := l.trimAscii.toString
    if t.startsWith ".text" then (true, acc.2)
    else if t.startsWith ".data" || t.startsWith ".bss" || t.startsWith ".section" ||
        t.startsWith ".rodata" then (false, acc.2)
    else if acc.1 then (true, l :: acc.2) else acc
  "\n".intercalate ((asm.splitOn "\n").foldl step (true, [])).2.reverse

/-! ## Data sections

The loaders read the text's data sections into `Kraken.DataImage.Item`s
(`dataSections`) and lay `.rodata` out at `Λ.rodata.lo` as a read-only image
in shared memory (`rodataWords`), its labels resolved from the image
(`DataImage.dataLabel`). The `.data` contents still come from `Λ.image` and
the `.data` / `.bss` labels from `Λ.symbols`. -/

/-- The data sections of a text, each in text order. -/
structure DataSecs where
  data : List Kraken.DataImage.Item := []
  bss : List Kraken.DataImage.Item := []
  rodata : List Kraken.DataImage.Item := []
  deriving Repr, DecidableEq, Inhabited

/-- A section of a text: code, one of the three data sections, or another
(say `.note.GNU-stack`), whose contents are ignored. -/
inductive Sec
  | text | data | bss | rodata | other
  deriving DecidableEq

/-- The section a section directive opens (`none`: not a section directive). -/
def secOf (t : String) : Option Sec :=
  if t.startsWith ".text" then some .text
  else if t.startsWith ".data" then some .data
  else if t.startsWith ".bss" then some .bss
  else if t.startsWith ".rodata" then some .rodata
  else if t.startsWith ".section" then
    let name := ((t.drop 8).trimAscii.toString.splitOn ",").headD ""
    if name.trimAscii.toString == ".rodata" then some .rodata
    else if name.trimAscii.toString == ".data" then some .data
    else if name.trimAscii.toString == ".bss" then some .bss
    else if name.trimAscii.toString == ".text" then some .text
    else some .other
  else none

/-- A decimal or `0x` hexadecimal integer, with an optional `-`. -/
def parseInt? (s : String) : Option Int :=
  let s := s.trimAscii.toString
  let (neg, body) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let n? : Option Nat :=
    if body.startsWith "0x" || body.startsWith "0X" then
      let ds := (body.drop 2).toString.toList
      if ds.isEmpty then none else
      ds.foldl (fun acc c => acc.bind fun a =>
        if c.isDigit then some (16 * a + (c.toNat - '0'.toNat))
        else if 'a' ≤ c && c ≤ 'f' then some (16 * a + (c.toNat - 'a'.toNat + 10))
        else if 'A' ≤ c && c ≤ 'F' then some (16 * a + (c.toNat - 'A'.toNat + 10))
        else none) (some 0)
    else body.toNat?
  n?.map fun n => if neg then -(n : Int) else n

/-- A label name (`[A-Za-z_.$][A-Za-z0-9_.$]*`). -/
def isSym (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_' || c == '.' || c == '$') &&
      cs.all fun c => c.isAlphanum || c == '_' || c == '.' || c == '$'

/-- The operands of a directive line, comma-separated. -/
def operands (t : String) (dir : String) : List String :=
  ((t.drop dir.length).toString.splitOn ",").map (·.trimAscii.toString)

/-- The items of one line of a data section: a label, `.balign n`,
`.p2align k`, `.zero n` / `.skip n`, `.byte`, `.quad` (numbers or labels);
symbol directives (`.globl`, `.type`, `.size`) and blank or comment lines
have none. `none`: a line the loader does not read (it refuses the text). -/
def dataLine (t : String) : Option (List Kraken.DataImage.Item) :=
  let word := (t.splitOn " ").headD "" |>.splitOn "\t" |>.headD ""
  if t.isEmpty || t.startsWith "#" || t.startsWith "//" then some []
  else if t.endsWith ":" && isSym (t.dropEnd 1).toString then some [.label (t.dropEnd 1).toString]
  else if word == ".globl" || word == ".type" || word == ".size" || word == ".local" then some []
  else if word == ".balign" then
    match operands t ".balign" with
    | [n] => (parseInt? n).bind fun n => if 0 ≤ n then some [.align n.toNat] else none
    | _ => none
  else if word == ".p2align" then
    match operands t ".p2align" with
    | [k] => (parseInt? k).bind fun k => if 0 ≤ k ∧ k < 64 then some [.align (2 ^ k.toNat)] else none
    | _ => none
  else if word == ".zero" || word == ".skip" then
    match operands t word with
    | [n] => (parseInt? n).bind fun n => if 0 ≤ n then some [.zero n.toNat] else none
    | _ => none
  else if word == ".byte" then
    (operands t ".byte").mapM (fun b => (parseInt? b).bind fun v =>
      if 0 ≤ v ∧ v < 256 then some (UInt8.ofNat v.toNat) else none) |>.map fun bs => [.bytes bs]
  else if word == ".quad" then
    (operands t ".quad").mapM fun x =>
      match parseInt? x with
      | some v => some (.quad v)
      | none => if isSym x then some (.quadLabel x) else none
  else none

/-- **The data sections of a text**: the lines of its `.data`, `.bss` and
`.rodata` sections (`secOf`; the text starts in `.text`) as data items, each
section's lines in text order (`dataLine`); `none` if a line of a data
section is not one the loader reads. -/
def dataSections (asm : String) : Option DataSecs :=
  let step (acc : Option (Sec × DataSecs)) (l : String) : Option (Sec × DataSecs) :=
    acc.bind fun (sec, d) =>
      let t := (l.trimAscii.toString.splitOn "\t").map (·.trimAscii.toString) |> " ".intercalate
      match secOf t with
      | some s => some (s, d)
      | none =>
        match sec with
        | .text | .other => some (sec, d)
        | .data => (dataLine t).map fun is => (sec, { d with data := d.data ++ is })
        | .bss => (dataLine t).map fun is => (sec, { d with bss := d.bss ++ is })
        | .rodata => (dataLine t).map fun is => (sec, { d with rodata := d.rodata ++ is })
  ((asm.splitOn "\n").foldl step (some (.text, {}))).map (·.2)

/-- The `.rodata` image fits `Λ.rodata` (8-aligned, below its end), and a
non-empty one lies in the address space, clear of `Λ`'s regions. -/
def rodataFits (Λ : Layout) (items : List Kraken.DataImage.Item) : Bool :=
  decide (Λ.rodata.lo % 8 = 0) &&
  decide (Kraken.DataImage.endAddr Λ.rodata.lo items ≤ Λ.rodata.lo + Λ.rodata.size) &&
  (items.isEmpty ||
    (decide (0 < Λ.rodata.lo) && decide (Λ.rodata.lo + Λ.rodata.size ≤ 2 ^ 64) &&
      Λ.regions.all fun r => decide (r.lo + r.size ≤ Λ.rodata.lo) || decide (Λ.rodata.lo + Λ.rodata.size ≤ r.lo)))

/-- The labels of the `.rodata` image at their addresses. -/
def rodataSyms (Λ : Layout) (items : List Kraken.DataImage.Item) : List (String × Nat) :=
  Kraken.DataImage.labelsFrom Λ.rodata.lo items

/-- `Λ.symbols` agrees with the image on every `.rodata` label it lists. -/
def symsAgree (Λ : Layout) (items : List Kraken.DataImage.Item) : Bool :=
  Λ.symbols.all fun (l, a) => match Kraken.DataImage.dataLabel Λ.rodata.lo items l with
    | some b => a == b
    | none => true

/-- The data symbols the loader places: `Λ.symbols` (the `.data` and `.bss`
labels) without the `.rodata` labels, then the `.rodata` labels at their
image addresses. -/
def loadSyms (Λ : Layout) (items : List Kraken.DataImage.Item) : List (String × Nat) :=
  Λ.symbols.filter (fun p => (Kraken.DataImage.dataLabel Λ.rodata.lo items p.1).isNone) ++
    rodataSyms Λ items

/-- Every `.quad` label of the image is a `.rodata` label or one `code`
resolves (a code label of the loaded program, or a data symbol). -/
def quadsResolve (Λ : Layout) (items : List Kraken.DataImage.Item) (code : String → Option Nat) : Bool :=
  (Kraken.DataImage.quadLabels items).all fun l =>
    (Kraken.DataImage.dataLabel Λ.rodata.lo items l).isSome || (code l).isSome

/-- **The `.rodata` image as shared 8-byte words** `(address, value)`
(`DataImage.words`): the items laid out from `Λ.rodata.lo`, a `.quad` of a
label holding the label's address (`DataImage.resolve`: a `.rodata` label
from the image, any other through `code`, 0 if unknown, which
`quadsResolve` excludes). -/
def rodataWords (Λ : Layout) (items : List Kraken.DataImage.Item) (code : String → Option Nat) :
    List (Nat × Nat) :=
  let res := Kraken.DataImage.resolve (fun l => BitVec.ofNat 64 ((code l).getD 0)) Λ.rodata.lo items
  Kraken.DataImage.words Λ.rodata.lo (Kraken.DataImage.image res Λ.rodata.lo items)

/-- A padding cell from `c` up to `a`, none if `a ≤ c` (a padding cell is
not a label, so it must not be empty). -/
def padTo {D : Type} (pad : D) (c a : Nat) : List (D × Nat) :=
  if c < a then [(pad, a - c)] else []

/-- Label cells for the data symbols `syms`, after code that ends at `cur`:
for each symbol in address order, padding up to its address (`padTo`, none
for a symbol at the end of the code or at the previous one's address) and a
label cell there. A symbol below the end of the code, or below the previous
one, would be misplaced; the targets pass only the symbols at or above the
start of the code (`symsFrom`), and `symsAbove` checks none of them is
inside the code. -/
def placeSyms {D : Type} (pad : D) (lbl : String → D) (cur : Nat) (syms : List (String × Nat)) :
    List (D × Nat) :=
  ((syms.mergeSort fun a b => a.2 ≤ b.2).foldl (init := ([], cur)) fun (cells, c) (x, a) =>
    (cells ++ padTo pad c a ++ [(lbl x, 0)], max a c)).1

/-- No data symbol lies inside the code `[lo, fin)`: each is below its start
or at or above its end. -/
def symsAbove (lo fin : Nat) (syms : List (String × Nat)) : Bool :=
  syms.all fun p => decide (p.2 < lo) || decide (fin ≤ p.2)

/-- The data symbols below `lo`, the start of the code. -/
def symsBelow (lo : Nat) (syms : List (String × Nat)) : List (String × Nat) :=
  syms.filter fun p => p.2 < lo

/-- The data symbols at or above `lo`, the start of the code. -/
def symsFrom (lo : Nat) (syms : List (String × Nat)) : List (String × Nat) :=
  syms.filter fun p => lo ≤ p.2

/-- The start of the executable for code at `lo` and the data symbols
`syms`: the lowest symbol below `lo`, or `lo` if there is none. -/
def exeStart (lo : Nat) (syms : List (String × Nat)) : Nat :=
  ((symsBelow lo syms).map (·.2)).foldl min lo

/-- Label cells for the data symbols of `syms` below `lo`, the start of the
code, laid out from `exeStart lo syms`: for each such symbol in address
order, padding up to its address (`padTo`, none for the first or one at the
previous address) and a label cell there, then padding up to `lo`. Empty if
no symbol is below `lo`. -/
def placeBelow {D : Type} (pad : D) (lbl : String → D) (lo : Nat) (syms : List (String × Nat)) :
    List (D × Nat) :=
  let r := ((symsBelow lo syms).mergeSort fun a b => a.2 ≤ b.2).foldl
    (init := ([], exeStart lo syms)) fun (cells, c) (x, a) =>
      (cells ++ padTo pad c a ++ [(lbl x, 0)], max a c)
  r.1 ++ padTo pad r.2 lo

/-- The address of the first label cell named `l` in `prog` laid out from
`base`, each cell `d` taking `size d` bytes (a label's address is that of
the cell after it); `none` if `prog` has no such label. -/
def labelAddr {D : Type} (lbl : D → Option String) (size : D → Nat) (base : Nat) (l : String) :
    List D → Option Nat
  | [] => none
  | d :: ds => if lbl d = some l then some base else labelAddr lbl size (base + size d) l ds

/-- **The process entry state** the canonical loaders assume, as Linux
gives it to a static executable: the stack pointer at the top of an initial
stack, `stack`, mapped in the main thread's private memory (zero-filled:
`argc`, `argv`, `envp` and the auxiliary vector are not modelled, and `scc`
reads none of them), every other register zero. `scc`'s entry reads only
the stack pointer: x64 `_start` aligns `%rsp` and calls the runtime's start
function; AArch64 `_start` branches to it; that function's frame (and those
of the calls it makes before switching to a pool stack) live on this stack.
Trusted (`Scc/DESIGN.md` §4). -/
structure Entry where
  /-- The initial stack: the stack pointer starts at its top. -/
  stack : Range

/-- The entry stack pointer: the top of the initial stack. -/
def Entry.sp (E : Entry) : Nat := E.stack.lo + E.stack.size

/-- The Linux entry state modelled: a 64 KiB initial stack just below
`2^47 - 4096` (the top of the user address space, less a guard page). Linux
maps more (up to the stack limit) and puts the arguments and environment at
the top; `scc` needs only what its start-up frames use. -/
def Entry.linux : Entry := ⟨⟨2 ^ 47 - 4096 - 65536, 65536⟩⟩

/-- The initial stack as private memory: zero bytes. -/
def Entry.stackMem (E : Entry) : _root_.Mem 64 :=
  Mem.storeBytes ∅ (BitVec.ofNat 64 E.stack.lo) (List.replicate E.stack.size 0)

/-- **The initial stack is clear of the layout**: it lies in the address
space and shares no address with any region of `Λ` (code, data, heap,
stack pool) or with `Λ.rodata`. The loaders refuse a layout that fails
this, so a certificate's layout must pass it (checked by evaluation); with
it the entry thread's private stack never hides an address of `Λ`. -/
def Entry.clear (E : Entry) (Λ : Layout) : Bool :=
  decide (E.stack.lo + E.stack.size ≤ 2 ^ 64) &&
    (Λ.rodata :: Λ.regions).all fun r =>
      decide (r.lo + r.size ≤ E.stack.lo) || decide (E.stack.lo + E.stack.size ≤ r.lo)

theorem Entry.clear_disjoint {E : Entry} {Λ : Layout} (h : E.clear Λ = true) :
    E.stack.lo + E.stack.size ≤ 2 ^ 64 ∧ ∀ r ∈ Λ.regions, r.Disjoint E.stack := by
  simp only [Entry.clear, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at h
  exact ⟨h.1, fun r hr => h.2 r (List.mem_cons_of_mem _ hr)⟩

theorem Entry.clear_rodata {E : Entry} {Λ : Layout} (h : E.clear Λ = true) :
    Λ.rodata.Disjoint E.stack := by
  simp only [Entry.clear, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at h
  exact h.2 _ List.mem_cons_self

/-- **The extension hooks**: what the extended machine needs beyond Kraken's
instruction steps (`Scc/DESIGN.md` §2, §7). The canonical targets use the
kernel model `Kernel.hooks` (`Scc/Sem/Kernel.lean`); `Hooks.none` is the
instance without any. -/
structure Hooks (I : ISA) where
  /-- The extension state (process exit record, thread exit records, futex
  and stack-pool state, thread pointers). -/
  X : Type
  /-- The extension state at load time, under the entry state and the
  layout (the kernel model takes its stack pool and its mapped regions
  from them). -/
  init : Entry → Layout → X
  /-- The thread state is at a system-call instruction (`svc` /
  `syscall`), where it takes no instruction step (only `sys`/`spawn`):
  Kraken's step halts there (`MachineData.pendingSyscall`). -/
  atSys : I.State → Bool
  /-- A system call other than `clone`, with its events (§2.3). -/
  sys : Marks → Nat → Config I × X → List Ev → Config I × X → Prop
  /-- `clone`: activate a thread (§2.1). -/
  spawn : Marks → Nat → Config I × X → Config I × X → Prop
  /-- At the transfer site of kind `k`, move the stack-pool range the
  thread's registers give into (`take`) or out of (`release`) its private
  memory, and move past the site (§2.6). -/
  xfer : XferKind → Nat → Config I × X → Config I × X → Prop
  /-- The process has exited (`exit_group`), and how. -/
  exited : X → Option Outcome
  /-- Thread `tid` does not run: it has called `exit`, or its slot is
  dormant (§2.1). -/
  threadDone : X → Nat → Prop
  /-- Faults of the extension (an unsupported system call or argument, a
  thread halted off its exit path). -/
  fault : Config I × X → Prop
  /-- The current stack range of a thread (§2.6). -/
  stackRange : Config I × X → Nat → Option Range
  /-- The thread pointer of a thread (`TPIDR_EL0` / `%fs` base, §2.4). -/
  threadPtr : Config I × X → Nat → BitVec 64
  /-- The thread slots the loader lays out (§2.1): slot 0 the entry thread,
  the others dormant until a `spawn` activates them. -/
  slots : Nat
  /-- The semantics a promise of thread `tid` is certified with under the
  code marks and the extension state of the step (`ExtMachine.cexec`): the
  ISA's own by default (no certification passes a system call); the kernel
  model's solo projection `Kernel.certSem` on the canonical targets. -/
  cexec : Marks → X → Nat → CertSem I := fun _ _ _ => CertSem.ofExec I.exec

/-- **No hooks**: no extension state, no system-call instruction, no
extension step, no exit record, no blocking, no extension fault, no stack
range, thread pointer 0, one thread slot. -/
def Hooks.none (I : ISA) : Hooks I where
  X := Unit
  init _ _ := ()
  atSys _ := false
  sys _ _ _ _ _ := False
  spawn _ _ _ _ := False
  xfer _ _ _ _ := False
  exited _ := Option.none
  threadDone _ _ := False
  fault _ := False
  stackRange _ _ := Option.none
  threadPtr _ _ := 0
  slots := 1

/-- **The extended machine with Kraken's instruction steps and the hooks
`H`.**

* A thread runs (takes steps) if it exists, has not called `exit`, and the
  process has not exited; it is at a system call (and takes no instruction
  step) if the hooks say its state is (`Hooks.atSys`).
* It is live if the process has not exited, it has not called `exit`, and it
  has not halted with an empty promise set.
* The configuration has exited as the hooks record, else (as the existing
  machine) `halted` when `Config.final`.
* A fault is a faulting instruction step (`Config.FaultStep`) of a running
  thread not at a system call (Kraken's step halts with a fault at a system
  call, where the hooks step instead; a thread that does not run takes no
  step), or a fault of the hooks. -/
def ExtMachine.ofHooks (I : ISA) (A : Arch) (H : Hooks I) (regVal : I.State → I.RegId → BitVec 64)
    (privLoad : I.State → BitVec 64 → Option (BitVec 64)) (pc : I.State → Nat) : ExtMachine where
  I := I
  A := A
  cexec := H.cexec
  X := H.X
  runs c tid := (∃ t, c.1.threads[tid]? = some t) ∧ H.exited c.2 = none ∧ ¬ H.threadDone c.2 tid
  atSys c tid := ∃ t, c.1.threads[tid]? = some t ∧ H.atSys t.st = true
  spawn := H.spawn
  sys := H.sys
  xfer := H.xfer
  live c tid := H.exited c.2 = none ∧ ¬ H.threadDone c.2 tid ∧
    ∃ t, c.1.threads[tid]? = some t ∧ ¬ (t.halted = true ∧ t.prom = [])
  exited c := match H.exited c.2 with
    | some o => some o
    | none => if c.1.final then some .halted else none
  fault c := (∃ tid m, ((∃ t, c.1.threads[tid]? = some t) ∧ H.exited c.2 = none ∧ ¬ H.threadDone c.2 tid) ∧
    ¬ (∃ t, c.1.threads[tid]? = some t ∧ H.atSys t.st = true) ∧ c.1.FaultStep A tid m) ∨ H.fault c
  regVal := regVal
  privLoad := privLoad
  stackRange := H.stackRange
  pc := pc

namespace ExtMachine

variable {I : ISA} {A : Arch} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat} {μ : Marks}

/-- The thread of a step of the existing machine exists. -/
theorem stepSemInf_thread {tid : Nat} {c c' : Config I} (h : Live.Inf.StepSemInf A tid c c') :
    ∃ t, c.threads[tid]? = some t := by
  rcases h with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩

/-- **An instruction step certified under `cexec` at a no-event
instruction** (`I.exec = some (.done s)`): the outcome is `finishInstr` at
the thread's own context, certified under `cexec`; memory unchanged
(Kraken's `instrSemInf_done_iff`, with `CertOkC`). -/
theorem instrSemC_done_iff {cexec : CertSem I} {tid : Nat} {c c' : Config I}
    {t : Thread I} {s : I.State} (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some (.done s)) :
    InstrSemC A cexec tid c c' ↔ ∃ th, th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s
        (Live.TicketStep.ctx0 tid t c.mem) ∧ CertOkC A cexec tid th c.mem ∧ c' = c.withThread tid th c.mem := by
  constructor
  · rintro ⟨t', outs, o, ht', hs, ho, hc, rfl⟩
    obtain rfl : t' = t := Option.some.inj (ht'.symm.trans ht)
    obtain ⟨st, c1, hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := (Lower.run_done_iff A tid _).mp hr
    have hm' : o.mem = c.mem := hm
    exact ⟨o.thread, hth, hm' ▸ hc, by rw [hm']⟩
  · rintro ⟨th, hth, hc, rfl⟩
    obtain ⟨outs, o, hs, ho, h1, h2⟩ := (Lower.stepOne_ok_iff A tid hex).mpr
      ⟨s, _, (Lower.run_done_iff A tid _).mpr ⟨rfl, rfl⟩, hth, rfl⟩
    have h2' : o.mem = c.mem := h2
    subst h1
    exact ⟨t, outs, o, ht, hs, ho, h2' ▸ hc, by rw [h2']⟩

/-- **With no hooks, a step is a step of the existing machine**, with no
events (under marks with no transfer site). -/
theorem ofHooks_none_step_iff (hμ : ∀ k, μ.site k = none) {tid : Nat}
    {c c' : (ofHooks I A (Hooks.none I) rv pl pcf).Cfg} {es : List Ev} :
    (ofHooks I A (Hooks.none I) rv pl pcf).Step μ tid c es c' ↔ es = [] ∧ Live.Inf.StepSemInf A tid c.1 c'.1 := by
  constructor
  · intro h
    cases h with
    | instr _ _ _ hs => exact ⟨rfl, stepSemC_exec.mp hs⟩
    | spawn _ h => exact h.elim
    | sys _ h _ _ _ => exact h.elim
    | xfer _ _ _ h => exact h.elim
  · rintro ⟨rfl, hs⟩
    obtain ⟨t, ht⟩ := stepSemInf_thread hs
    have : c' = (c'.1, c.2) := rfl
    rw [this]
    exact .instr ⟨⟨t, ht⟩, rfl, id⟩ (fun ⟨_, _, h⟩ => Bool.false_ne_true h)
      (fun k ⟨a, ha, _⟩ => by simp [hμ k] at ha) (stepSemC_exec.mpr hs)

/-- **With no hooks, a fault is a faulting step of the existing machine**
(`Config.FaultStep`): the gating of `ofHooks`'s `fault` by `runs` and
`atSys` excludes nothing there. -/
theorem ofHooks_none_fault_iff {c : (ofHooks I A (Hooks.none I) rv pl pcf).Cfg} :
    (ofHooks I A (Hooks.none I) rv pl pcf).fault c ↔ ∃ tid m, c.1.FaultStep A tid m := by
  constructor
  · rintro (⟨tid, m, -, -, h⟩ | h)
    · exact ⟨tid, m, h⟩
    · exact h.elim
  · rintro ⟨tid, m, h⟩
    refine .inl ⟨tid, m, ⟨?_, rfl, id⟩, fun ⟨_, _, h⟩ => Bool.false_ne_true h, h⟩
    obtain ⟨outs, hs, -⟩ := h
    cases ht : c.1.threads[tid]? with
    | none => simp [stepThread, ht] at hs
    | some t => exact ⟨t, ht⟩

/-- **Every instruction step at a no-event instruction agrees with Kraken's
single-thread step**: if thread `tid`'s next instruction is `.done s` in
Kraken's semantics (`I.exec`), an instruction step of `tid` replaces the
thread by one in state `s` with the same promise set, leaves memory and the
extension state alone, and changes the views as Kraken's
`instrSemInf_done_stutter` says. -/
theorem ofHooks_instr_done {H : Hooks I} {tid : Nat} {c : (ofHooks I A H rv pl pcf).Cfg} {c' : Config I}
    {t : Thread I} {s : I.State} (ht : c.1.threads[tid]? = some t) (hex : I.exec t.st = some (.done s))
    (h : InstrSemC A (H.cexec μ c.2 tid) tid c.1 c') :
    ∃ th, c' = c.1.withThread tid th c.1.mem ∧ th.st = s ∧ th.prom = t.prom := by
  obtain ⟨th, hth, -, rfl⟩ := (instrSemC_done_iff ht hex).mp h
  exact ⟨th, rfl, finishInstr_st hth, (finishInstr_relKey hth).1⟩

/-- **The instance takes Kraken's single-thread step at a no-event
instruction** off the transfer sites: a running thread with no outstanding
promise whose next
instruction is `.done s` (`I.exec`) has a step, with no events, to the
configuration where it is in state `s`, still with no promise; memory and
extension state are unchanged. -/
theorem ofHooks_step_of_done {H : Hooks I} {tid : Nat} {c : (ofHooks I A H rv pl pcf).Cfg} {t : Thread I}
    {s : I.State} (ht : c.1.threads[tid]? = some t) (hsys : H.atSys t.st = false)
    (hsite : ∀ k a, μ.site k = some a → pcf t.st ≠ a) (hx : H.exited c.2 = none)
    (hd : ¬ H.threadDone c.2 tid) (hp : t.prom = []) (hex : I.exec t.st = some (.done s)) :
    ∃ th, (ofHooks I A H rv pl pcf).Step μ tid c [] (c.1.withThread tid th c.1.mem, c.2) ∧ th.st = s ∧
      th.prom = [] := by
  obtain ⟨th, hth⟩ := List.exists_mem_of_ne_nil _
    (Live.TicketStep.finishInstr_ne_nil t (I.deps t.st) (instrViews t (I.deps t.st)) s
      (Live.TicketStep.ctx0 tid t c.1.mem))
  have hst : th.st = s := finishInstr_st hth
  have hpr : th.prom = [] := (finishInstr_relKey hth).1.trans hp
  have hi : InstrSemC A (H.cexec μ c.2 tid) tid c.1 (c.1.withThread tid th c.1.mem) :=
    (instrSemC_done_iff ht hex).mpr ⟨th, hth, certOkC_of_prom_nil hpr, rfl⟩
  have hns : ¬ (ofHooks I A H rv pl pcf).atSys c tid := fun ⟨t', ht', h⟩ => by
    have e : t = t' := Option.some.inj (ht.symm.trans ht')
    subst e
    rw [hsys] at h
    exact Bool.false_ne_true h
  have hnsite : ∀ k, ¬ (ofHooks I A H rv pl pcf).AtSite μ k c tid := fun k ⟨a, ha, t', ht', hpc⟩ => by
    have e : t = t' := Option.some.inj (ht.symm.trans ht')
    subst e
    exact hsite k a ha hpc
  exact ⟨th, .instr ⟨⟨t, ht⟩, hx, hd⟩ hns hnsite (.inl hi), hst, hpr⟩

end ExtMachine

/-- **A straight-line run of Kraken's single-thread step**: a sequence of
no-event instructions (`I.exec st = some (.done st')`), e.g. register moves
and arithmetic. -/
inductive SeqRun (I : ISA) : I.State → I.State → Prop
  | refl (s : I.State) : SeqRun I s s
  | step {s s' s'' : I.State} : I.exec s = some (.done s') → SeqRun I s' s'' → SeqRun I s s''

namespace ExtMachine

variable {I : ISA} {A : Arch} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat} {μ : Marks}

theorem withThread_self {c : Config I} {tid : Nat} {t th : Thread I} {mem : Memory}
    (ht : c.threads[tid]? = some t) : (c.withThread tid th mem).threads[tid]? = some th := by
  have hlt : tid < c.threads.size := by
    rcases Nat.lt_or_ge tid c.threads.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at ht
  simp [Config.withThread, hlt]

/-- **A straight-line run of Kraken's single-thread step is a run of the
instance**, with the empty trace: from a configuration where thread `tid`
runs with no outstanding promise, if Kraken's single-thread step takes its
state from `t.st` to `s` through no-event instructions (none at a
system-call instruction or a transfer site), the instance reaches a configuration where the
thread is in state `s` with no promise, with the same memory and extension
state. -/
theorem ofHooks_run_of_seqRun {H : Hooks I} {tid : Nat} {s0 s : I.State} (hr : SeqRun I s0 s) :
    ∀ {c : (ofHooks I A H rv pl pcf).Cfg} {t : Thread I}, c.1.threads[tid]? = some t → t.st = s0 → t.prom = [] →
    H.exited c.2 = none → ¬ H.threadDone c.2 tid → (∀ u, SeqRun I s0 u → H.atSys u = false) →
    (∀ u, SeqRun I s0 u → ∀ k a, μ.site k = some a → pcf u ≠ a) →
    ∃ c' th, (ofHooks I A H rv pl pcf).Run μ c [] c' ∧ c'.1.threads[tid]? = some th ∧ th.st = s ∧ th.prom = [] ∧
      c'.1.mem = c.1.mem ∧ c'.2 = c.2 := by
  induction hr with
  | refl => intro c t ht hu hp _ _ _ _; exact ⟨c, t, .refl _, ht, hu, hp, rfl, rfl⟩
  | @step u u' u'' hex _ ih =>
    intro c t ht hu hp hx hd hsys hsite
    subst hu
    obtain ⟨th, hstep, hst, hpr⟩ := ofHooks_step_of_done ht (hsys _ (.refl _)) (hsite _ (.refl _)) hx hd hp hex
    obtain ⟨c', th', hrun, ht', hst', hpr', hm, hX⟩ :=
      ih (c := (c.1.withThread tid th c.1.mem, c.2)) (withThread_self ht) hst hpr hx hd
        (fun v hv => hsys v (.step hex hv)) (fun v hv => hsite v (.step hex hv))
    refine ⟨c', th', ?_, ht', hst', hpr', hm, hX⟩
    unfold ExtMachine.Run at hrun ⊢
    exact LRun.step (es := []) (tr := []) ⟨tid, hstep⟩ hrun

end ExtMachine

/-! ## The certificate's statement -/

/-- **A certificate's configuration**: the layout `Λ` and the budget `B`
the statement is published with, the target's thread slots `slots` (the
canonical target of each ISA is a function of it: the kernel model lets the
process have that many threads, `Scc/DESIGN.md` §3.1), the source's thread
capacity (`SrcSem.SrcParams.cap`: at least the target's thread slots, above
`B.threads`), and the source's start configurations (by default the empty
setup block, `SrcSem.mainInit`, as the heap-bytes fallback has an empty
image). -/
structure CertCfg where
  Λ : Layout
  B : Budget
  slots : Nat
  cap : Nat
  init : TermRun.Cfg → Prop := SrcSem.mainInit cap

/-- The source parameters of a certificate's configuration under the memory
model `arch`: all knobs on, no extern step. -/
def CertCfg.src (cfg : CertCfg) (arch : WeakMem.Arch) : SrcSem.SrcParams :=
  { arch, cap := cfg.cap, init := cfg.init }

/-- **The target's thread slots** for `asm` under `Λ`: the size of the
loaded configuration's thread array (0 if the loader refuses). With dormant
slots (`Scc/DESIGN.md` §2.1) the loader lays out one slot per thread the
target can ever run, and no step changes the array's size, so this is the
number of threads the target can have; it is read off the target's own
loader, not stated beside it. -/
def Target.threadSlots (T : Target) (asm : T.Asm) (Λ : Layout) : Nat :=
  match T.load asm Λ with
  | some t => t.1.threads.size
  | none => 0

/-- **A well-formed certificate configuration** for target `T` and text
`asm`: the thread slots are fixed by the budget, one more than `B.threads`
(the slot count is not a free parameter of the statement: a certificate
cannot pick a target with fewer threads than its budget allows); the
source's thread capacity covers the target's thread slots (each target
thread creation needs a source spawn), and exceeds the thread budget (the
spawn that crosses `B.threads` must exist for a `threads` abort to be
justified, `threads_abort_unjustified`). -/
structure CertCfg.WF (cfg : CertCfg) (T : Target) (asm : T.Asm) : Prop where
  slotsEq : cfg.slots = cfg.B.threads + 1
  capSlots : T.threadSlots asm cfg.Λ ≤ cfg.cap
  capBudget : cfg.B.threads < cfg.cap

/-- **With a capacity at most the thread budget, no `threads` abort is
justified**: no source step (thread step, promise or spawn below the
capacity) takes the thread count above the budget, so a target that runs
out of thread slots could never abort justifiably (unless the kernel
refused a `clone`, `Ev.cloneErr`). This is why `CertCfg.WF` asks for
`B.threads < cap`. -/
theorem threads_abort_unjustified {P : SrcSem.SrcParams} (hP : P.hooks = SrcSem.SrcHooks.none) {B : Budget}
    (hcap : P.cap ≤ B.threads) {p : CoreTerm.Prog} {tr : List Ev} (hc : Ev.cloneErr ∉ tr) {s : TermRun.Cfg}
    {i : Nat} : ¬ AbortJustified B (SrcSem.source P p) tr s i .threads := by
  rintro (h | ⟨es, s', ⟨-, hs, -⟩, hle, hgt⟩)
  · exact hc h
  apply hgt
  show s'.ths.size ≤ B.threads
  rcases hs with hs | hs | hs
  · rw [SrcSem.stepBy_size hs]
    exact hle
  · have := SrcSem.spawnBy_size hs
    omega
  · rw [hP] at hs
    exact hs.elim

end Scc.Sem
