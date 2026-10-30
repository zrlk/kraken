/-
AArch64 emitter for `scc`.

Instruction selection for the `isaLSE2` target (FEAT_LSE2, `Arch.armv8`): the
helpers below produce Kraken AArch64 `Directive`s (as `Item`s of
`Scc/Emit/A64Print.lean`) in the canonical forms that round-trip through
Kraken's parser, and only in forms that `Program.WCLowerable`
(`Kraken/Promising/Lower/Lowerable.lean`) allows:

* acquire load = `ldar` (never `ldapr`, clause 4); release store = `stlr`;
* read-modify-write only as `casal`/`swpal`/`ld<op>al` with a real result
  register (clauses 2 and 3), at word or doubleword size (clause 6);
* no 64-bit `ldp`/`stp` anywhere (clause 1): frames are saved with single
  `str`/`ldr`;
* no sub-word store (clause 6): a byte or halfword write is a word load, a
  bitfield insert and a word store (`subWordStore`);
* no pair atomics (clause 5).

Register use is AAPCS64-like: arguments and results in `x0`–`x7`, `x8` the
system-call number, `x9`–`x15` caller-saved temporaries, `x16`/`x17` the
emitter's scratch registers, `x18` unused (platform register), `x19`–`x28`
callee-saved, `x29` frame pointer, `x30` link register. No register holds the
thread control block: the thread pointer is `TPIDR_EL0`, read with `mrs` and
set by `clone(CLONE_SETTLS)` or `msr` at start-up.

Obligations where WeakCore's `TermRun` is stricter than herd (keep them when
extending the table):

* a thread that re-reads the value its own RMW wrote and dereferences it needs
  the RMW in an `-al` form (`swpal`/`ldaddal`/`casal`), or a release write
  followed by an `ldar` re-read; never `ldapr` (the IR's `rmw` is always
  `swpal`/`ldaddal`);
* `spawn` is a full barrier on the parent: the lowering puts an IR
  `fence full` (`dmb ish`) before every `clone`;
* not in the fragment yet: a pair store needs `dmb ish` before the `stp` (and
  64-bit `stp` is excluded by clause 1 anyway), and `casPair` would be
  `caspal` (excluded by clause 5 until the pair findings are resolved).

System calls use `svc #0` with the number in `x8`; the thread pointer is
`TPIDR_EL0`, read with `mrs` and set with `msr`. All three are Kraken
instructions (`Operation.SVC`, `MRS`, `MSR`; `Kraken/SYSCALL.md`), so every
instruction of the emitted text is in the re-parsed program and the only raw
lines are assembler directives.

The emitter is not trusted: a certificate re-parses its text.
-/
import Scc.Emit.A64Print
import Scc.IR.StackMap
import Scc.Emit.Data

namespace Scc.Emit.A64

/-! ## Operand shorthands -/

/-- `X<r>` as a source/destination where index 31 is `XZR`. -/
def xz (r : XReg) : RegOrZr .W64 := .low (.reg r) .W64
/-- `X<r>` where index 31 is `SP`. -/
def xs (r : XReg) : RegOrSp .W64 := .low (.reg r) .W64
/-- `W<r>` where index 31 is `WZR`. -/
def wz (r : XReg) : RegOrZr .W32 := .low (.reg r) .W32
/-- A register of either width, index 31 = zero register. -/
def rz (w : RegWidth) (r : XReg) : RegOrZr w := .low (.reg r) w
def rsp (w : RegWidth) (r : XReg) : RegOrSp w := .low (.reg r) w
def zr (w : RegWidth) : RegOrZr w := .low .XZR w
def spW64 : RegOrSp .W64 := RegOrSp.SP

/-- An integer constant. -/
def i64 (n : Int) : ConstExpr := .int64 (Int64.ofInt n)

/-- One instruction item. -/
def ins {w : RegWidth} (op : Operation w) : Item := .d (.instr ⟨w, op⟩)

/-- A label item. -/
def lbl (l : Label) : Item := .d (.label l)

/-- The emitter's scratch registers (intra-procedure-call registers). -/
def scratch0 : XReg := .X16
def scratch1 : XReg := .X17

/-- The register numbers `x0`..`x30` in order. -/
def xregs : List XReg :=
  [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7, .X8, .X9, .X10, .X11, .X12, .X13, .X14, .X15,
   .X16, .X17, .X18, .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29, .X30]

/-- Argument registers `x0`–`x7`. -/
def argRegs : List XReg := xregs.take 8

/-- Callee-saved registers `x19`–`x28`. -/
def calleeSaved : List XReg := (xregs.drop 19).take 10

/-- Caller-saved temporaries `x9`–`x15`. -/
def tempRegs : List XReg := (xregs.drop 9).take 7

/-! ## Moves and constants -/

/-- `mov xd, xs` (`orr xd, xzr, xs`). -/
def movReg (w : RegWidth) (d s : XReg) : Item :=
  ins (.ORR_s (rz w d) (zr w) ⟨rz w s, 0, .LSL⟩)

/-- `mov` between `sp` and a register (`add d, s, #0`). -/
def movSp (d s : RegOrSp .W64) : Item := ins (.ADD_e d s (.imm ⟨i64 0, .S0⟩))

/-- The 16-bit halfwords of a 64-bit value, low first. -/
def halfwords (v : Nat) : List Nat := (List.range 4).map fun k => (v >>> (16 * k)) % 65536

def movShiftOf : Nat → MovShift .W64
  | 1 => .LSL16 | 2 => .LSL32 | 3 => .LSL48 | _ => .LSL0

/-- Materialise a 64-bit constant (`n` taken modulo `2^64`) in `xd`: one `movz`
of the lowest non-zero halfword (or `#0`), then a `movk` per other non-zero
halfword. -/
def movImm (d : XReg) (n : Int) : List Item :=
  let v := (n % 18446744073709551616).toNat
  let hs := (halfwords v).zipIdx.filter (fun (h, _) => h != 0)
  match hs with
  | [] => [ins (.MOVZ (xz d) (i64 0) .LSL0)]
  | (h, k) :: rest =>
    ins (.MOVZ (xz d) (i64 h) (movShiftOf k)) ::
      rest.map fun (h, k) => ins (.MOVK (xz d) (i64 h) (movShiftOf k))

/-- The address of a label: `adrp xd, l` + `add xd, xd, :lo12:l`. -/
def addrOf (d : XReg) (l : Label) : List Item :=
  [ins (.ADRP (xz d) (.label l)), ins (.ADD_e (xs d) (xs d) (.imm ⟨.lo12 (.label l), .S0⟩))]

/-! ## Arithmetic -/

/-- An unsigned 12-bit arithmetic immediate (optionally shifted by 12). -/
def arithImm? (n : Int) : Option ImmExpr :=
  if 0 ≤ n ∧ n ≤ 4095 then some ⟨i64 n, .S0⟩
  else if 0 ≤ n ∧ n % 4096 = 0 ∧ n / 4096 ≤ 4095 then some ⟨i64 (n / 4096), .S12⟩
  else none

/-- `d := s + n` for registers that may be `sp`; a constant outside the
immediate range goes through `scratch0` (which must differ from `d` and `s`). -/
def addImm (d s : RegOrSp .W64) (n : Int) : List Item :=
  match arithImm? n, arithImm? (-n) with
  | some i, _ => [ins (.ADD_e d s (.imm i))]
  | none, some i => [ins (.SUB_e d s (.imm i))]
  | none, none =>
    movImm scratch0 n ++ [ins (.ADD_e d s (.ext ⟨⟨.W64, xz scratch0⟩, ⟨.UXTX, .E0⟩⟩))]

/-- `d := a + b` (64-bit, wrapping). -/
def addReg (w : RegWidth) (d a b : XReg) : Item := ins (.ADD_s (rz w d) (rz w a) ⟨rz w b, 0, .LSL⟩)
/-- `d := a - b` (wrapping). -/
def subReg (w : RegWidth) (d a b : XReg) : Item := ins (.SUB_s (rz w d) (rz w a) ⟨rz w b, 0, .LSL⟩)

/-- Unbounded-`Int` addition with an overflow trap: `adds` then `b.hs abort`
(carry set = the unsigned sum does not fit in 64 bits). -/
def addChecked (d a b : XReg) (abort : Label) : List Item :=
  [ins (.ADDS_s (xz d) (xz a) ⟨xz b, 0, .LSL⟩), ins (.B_cond .CS (.label abort))]

/-- Unbounded-`Int` subtraction, floored at zero: `subs` then
`csel d, d, xzr, hs`. -/
def subSat (d a b : XReg) : List Item :=
  [ins (.SUBS_s (xz d) (xz a) ⟨xz b, 0, .LSL⟩), ins (.CSEL (xz d) (xz d) (zr .W64) .CS)]

/-- `cmp a, b`. -/
def cmpReg (w : RegWidth) (a b : XReg) : Item := ins (.SUBS_s (zr w) (rz w a) ⟨rz w b, 0, .LSL⟩)

/-- `cmp a, #n` for `0 ≤ n ≤ 4095`, otherwise through `scratch0`. -/
def cmpImm (w : RegWidth) (a : XReg) (n : Int) : List Item :=
  match arithImm? n with
  | some i => [ins (.SUBS_e (zr w) (rsp w a) (.imm i))]
  | none => movImm scratch0 n ++ [cmpReg w a scratch0]

/-- `cset d, c` (`csinc d, zr, zr, !c`). -/
def cset (w : RegWidth) (d : XReg) (c : CondCode) : Item :=
  ins (.CSINC (rz w d) (zr w) (zr w) c.invert)

/-! ## Plain loads and stores

Word or doubleword only; `w` is the access width. Offsets that fit neither the
scaled unsigned nor the 9-bit signed form go through `scratch0`. The choice
between `ldr` and `ldur` is the one Kraken's parser makes, so the forms
round-trip. -/

/-- The scaled unsigned offset form applies (`0 ≤ off ≤ 4095·size`, aligned). -/
def scaledOk (size : Nat) (off : Int) : Bool :=
  0 ≤ off && off ≤ 4095 * size && off % size == 0

def unscaledOk (off : Int) : Bool := -256 ≤ off && off ≤ 255

/-- `rt := [base + off]`, `w`-sized. -/
def ldrOff (w : RegWidth) (rt : XReg) (base : RegOrSp .W64) (off : Int) : List Item :=
  if scaledOk w.bytes off then [ins (.LDR (rz w rt) (.addr ⟨base, .imm ⟨i64 off, none⟩⟩))]
  else if unscaledOk off then [ins (.LDUR (rz w rt) ⟨base, i64 off⟩)]
  else movImm scratch0 off ++
    [ins (.LDR (rz w rt) (.addr ⟨base, .reg ⟨⟨.W64, xz scratch0⟩, ⟨.UXTX, .E0⟩⟩⟩))]

/-- `[base + off] := rt`, `w`-sized. -/
def strOff (w : RegWidth) (rt : XReg) (base : RegOrSp .W64) (off : Int) : List Item :=
  if scaledOk w.bytes off then [ins (.STR (rz w rt) ⟨base, .imm ⟨i64 off, none⟩⟩)]
  else if unscaledOk off then [ins (.STUR (rz w rt) ⟨base, i64 off⟩)]
  else movImm scratch0 off ++
    [ins (.STR (rz w rt) ⟨base, .reg ⟨⟨.W64, xz scratch0⟩, ⟨.UXTX, .E0⟩⟩⟩)]

/-- Store the zero register (`str xzr/wzr`). -/
def strZeroOff (w : RegWidth) (base : RegOrSp .W64) (off : Int) : List Item :=
  if scaledOk w.bytes off then [ins (.STR (zr w) ⟨base, .imm ⟨i64 off, none⟩⟩)]
  else if unscaledOk off then [ins (.STUR (zr w) ⟨base, i64 off⟩)]
  else movImm scratch0 off ++
    [ins (.STR (zr w) ⟨base, .reg ⟨⟨.W64, xz scratch0⟩, ⟨.UXTX, .E0⟩⟩⟩)]

/-- `rt := [base + idx·8]` (doubleword array element). -/
def ldrIdx (rt base idx : XReg) : Item :=
  ins (.LDR (xz rt) (.addr ⟨xs base, .reg ⟨⟨.W64, xz idx⟩, ⟨.UXTX, .E3⟩⟩⟩))

/-- `[base + idx·8] := rt`. -/
def strIdx (rt base idx : XReg) : Item :=
  ins (.STR (xz rt) ⟨xs base, .reg ⟨⟨.W64, xz idx⟩, ⟨.UXTX, .E3⟩⟩⟩)

/-- Zero-extending byte load `ldrb` (loads of any width are lowerable). -/
def ldrbOff (rt : XReg) (base : RegOrSp .W64) (off : Int) : List Item :=
  if scaledOk 1 off then [ins (.LDRB (wz rt) ⟨base, .imm ⟨i64 off, none⟩⟩)]
  else if unscaledOk off then [ins (.LDURB (wz rt) ⟨base, i64 off⟩)]
  else movImm scratch0 off ++ [ins (.LDRB (wz rt) ⟨base, .reg ⟨⟨.W64, xz scratch0⟩, ⟨.UXTX, .E0⟩⟩⟩)]

/-- A sub-word write without a sub-word store (clause 6): the aligned 32-bit
word at `[base]` is loaded into `tmp`, bits `[8·byteOff, 8·byteOff + 8·size)`
are replaced by the low bits of `v` (`bfi` = `bfm`), and the word is stored
back. `size` is 1 or 2 bytes, `byteOff + size ≤ 4`. Not atomic: only for
locations no other thread writes concurrently. -/
def subWordStore (size byteOff : Nat) (v base tmp : XReg) : List Item :=
  let lsb := 8 * byteOff
  [ins (.LDR (wz tmp) (.addr ⟨xs base, .imm ⟨i64 0, none⟩⟩)),
   ins (.BFM (wz tmp) (wz v) ((32 - lsb) % 32) (8 * size - 1)),
   ins (.STR (wz tmp) ⟨xs base, .imm ⟨i64 0, none⟩⟩)]

/-! ## Ordered and atomic accesses (base register only) -/

/-- Acquire load `ldar` (clause 4: never `ldapr`). -/
def loadAcq (w : RegWidth) (rt base : XReg) : Item :=
  ins (.LDAR .acq false (w : MemWidth) (rz w rt) (xs base))

/-- Release store `stlr`. -/
def storeRel (w : RegWidth) (rt base : XReg) : Item :=
  ins (.STLR (w : MemWidth) (rz w rt) (xs base))

/-- Compare-and-swap `casal rs, rt, [base]` (clause 2: `casal`; clause 3: `rs`
must be a real register): if `[base] = rs` then `[base] := rt`; `rs` receives
the old value. -/
def casAL (w : RegWidth) (rs rt base : XReg) : Item :=
  ins (.CAS .acqRel (w : MemWidth) (rz w rs) (rz w rt) (xs base))

/-- Exchange `swpal rs, rt, [base]`: `[base] := rs`, `rt` receives the old value
(must be a real register, clause 3). -/
def swpAL (w : RegWidth) (rs rt base : XReg) : Item :=
  ins (.SWP .acqRel (w : MemWidth) (rz w rs) (rz w rt) (xs base))

/-- Atomic fetch-and-op `ld<op>al rs, rt, [base]` (`rt` a real register). -/
def ldopAL (op : AtomicOp) (w : RegWidth) (rs rt base : XReg) : Item :=
  ins (.LDOP op .acqRel (w : MemWidth) (rz w rs) (rz w rt) (xs base))

/-- Full barrier `dmb ish`. -/
def fullFence : Item := ins (.DMB .sy)

/-! ## Control flow -/

def jmp (l : Label) : Item := ins (.B (.label l))
def jcc (c : CondCode) (l : Label) : Item := ins (.B_cond c (.label l))
def call (l : Label) : Item := ins (.BL (.label l))
def callReg (r : XReg) : Item := ins (.BLR (xz r))
def tailReg (r : XReg) : Item := ins (.BR (xz r))
def ret : Item := ins (.RET RegOrZr.X30)
def cbz (w : RegWidth) (r : XReg) (l : Label) : Item := ins (.CBZ (rz w r) (.label l))
def cbnz (w : RegWidth) (r : XReg) (l : Label) : Item := ins (.CBNZ (rz w r) (.label l))

/-! ## Frames

A frame of `size` bytes (a multiple of 16) keeps the caller's `x29`/`x30` in
its top 16 bytes; they are saved with two `str` (no 64-bit `stp`, clause 1).
After the prologue `x29` points at the saved pair. -/

/-- Round up to a multiple of 16. -/
def align16 (n : Nat) : Nat := (n + 15) / 16 * 16

def prologue (size : Nat) : List Item :=
  let f := align16 (max size 16)
  addImm spW64 spW64 (-(f : Int)) ++
  strOff .W64 .X29 spW64 (f - 16) ++ strOff .W64 .X30 spW64 (f - 8) ++
  addImm (xs .X29) spW64 (f - 16)

def epilogue (size : Nat) : List Item :=
  let f := align16 (max size 16)
  ldrOff .W64 .X29 spW64 (f - 16) ++ ldrOff .W64 .X30 spW64 (f - 8) ++
  addImm spW64 spW64 f ++ [ret]

/-! ## System calls -/

/-- Linux AArch64 system-call numbers used by the runtime. -/
def sysWrite : Nat := 64
def sysExit : Nat := 93
def sysExitGroup : Nat := 94
def sysFutex : Nat := 98
def sysRtSigaction : Nat := 134
def sysClone : Nat := 220

/-- `x8 := nr; svc #0` (arguments already in `x0`–`x5`, result in `x0`). -/
def syscall (nr : Nat) : List Item := movImm .X8 nr ++ [ins (.SVC 0)]

/-- Read the thread pointer (`mrs xd, tpidr_el0`). -/
def readTp (d : XReg) : Item := ins (.MRS (xz d) .TPIDR_EL0)

/-- Set the thread pointer (`msr tpidr_el0, xs`). -/
def writeTp (s : XReg) : Item := ins (.MSR .TPIDR_EL0 (xz s))

/-! ## From the IR

Register allocation is spill-all: every IR register of a function has an
8-byte slot in the function's frame, at `[sp, #8·(o + i)]` in order of first
occurrence, above the outgoing argument area of `o` words (`outWords`, even)
at the bottom of the frame; the caller's `x29`/`x30` sit in the frame's top
16 bytes. Each IR instruction loads its operands into the temporaries
`x9`–`x15`, computes, and stores the result back to its slot, so every IR
register keeps its value across a call (the callee only touches its own frame
and its incoming argument words). Call arguments go in `x0`–`x7`, then on the
stack (AAPCS64): argument `8 + j` at `[sp, #8·j]` at the call, which is
`[x29, #16 + 8·j]` in the callee, copied to its slot in the prologue. Results
go in `x0`–`x5`. The outgoing area is as large as the argument area of any
callee (`IR.StackMap.argAreas`), and a tail call writes its stack arguments
over the function's own incoming area, which the argument areas make large
enough, so every tail call runs in constant stack.

Growable stacks (`Scc.IR.StackMap`): `x29` is the frame-record pointer
(`[x29]` the caller's `x29`, `[x29, #8]` the return address), so the slot of
register `i` is at `8·i - (frame - 16)` from it. The grow stub of a function
(when the program has `IR.Program.growth`) allocates an 80-byte save area,
stores `x0`–`x7` at `[sp, #8·i]` and `x29`/`x30` at `[sp, #64]`/`[sp, #72]`
(single `str`, clause 1), points `x29` at that pair (so register parameter
`i` is at `8·i - 64` from it, and stack parameter `8 + j` at `16 + 8·j`),
passes the frame size in `x0` to `scc_rt_morestack`,
reloads everything, frees the area and repeats the check. Every call is
followed by a local label `sp<k>`, its safepoint. Frame slots are addressed
from `sp`, which the moved frame records restore on return, and no other
machine register holds a stack address across a call. The thread entry and
the start-up stack switch zero `x29` so that the frame-record chain ends.

Labels: block `b` (index `bi`) of function `f` (index `fi`) is
`.L<fi>_<f>.<bi>_<b>` with every character other than a letter, a digit or
`_` replaced by `_` in `<f>` and `<b>`; the index prefixes make labels unique.
The per-function abort stubs, the child stubs and the clone continuation
labels use suffixes that do not start with a digit.

Threads: a `clone` passes its argument in `x9` and the `spawnReg`s in
`x10`–`x14` (the kernel keeps every register but `x0` in the child), and
the child branches (`cbz x0`) to the function's child stub of that `clone`
(`FnCtx.childStub`, after the function's code), which moves them into
`x0`–`x5`, zeroes `x29` and calls the entry. -/

section FromIR

/-- Letters, digits and `_` kept; anything else becomes `_`. -/
def sanitize (s : String) : String :=
  s.map fun c => if c.isAlphanum || c == '_' then c else '_'

/-- Per-function emission context. -/
structure FnCtx where
  /-- Function index (for unique labels). -/
  fi : Nat
  name : String
  /-- IR register slots, in order. -/
  slots : List IR.Reg
  /-- Block labels, in order. -/
  blocks : List IR.Label
  /-- Frame size in bytes (multiple of 16). -/
  frame : Nat
  /-- Words of the outgoing argument area at the bottom of the frame. -/
  out : Nat := 0
  /-- Words of the function's incoming argument area
  (`IR.StackMap.argAreas`): its tail calls write at most this many. -/
  inArea : Nat := 0
  /-- The program's abort routine. -/
  abortFn : String
  /-- Place safepoint labels after calls (the program has `IR.Program.growth`). -/
  maps : Bool := false

def FnCtx.prefix (c : FnCtx) : String := s!".L{c.fi}_{sanitize c.name}."

/-- The assembler label of an IR block label. -/
def FnCtx.blockLabel (c : FnCtx) (l : IR.Label) : Except String Label :=
  match c.blocks.idxOf? l with
  | some bi => .ok s!"{c.prefix}{bi}_{sanitize l}"
  | none => .error s!"scc (arm): unknown label {l} in function {c.name}"

def FnCtx.local (c : FnCtx) (suffix : String) : Label := c.prefix ++ suffix

def FnCtx.slotOff (c : FnCtx) (r : IR.Reg) : Except String Int :=
  match c.slots.idxOf? r with
  | some i => .ok (8 * (c.out + i))
  | none => .error s!"scc (arm): unknown register {r} in function {c.name}"

/-- `t := ` the IR register `r`. -/
def FnCtx.getReg (c : FnCtx) (t : XReg) (r : IR.Reg) : Except String (List Item) := do
  return ldrOff .W64 t spW64 (← c.slotOff r)

/-- IR register `r := t`. -/
def FnCtx.setReg (c : FnCtx) (r : IR.Reg) (t : XReg) : Except String (List Item) := do
  return strOff .W64 t spW64 (← c.slotOff r)

/-- `t := ` an operand. -/
def FnCtx.getOp (c : FnCtx) (t : XReg) : IR.Operand → Except String (List Item)
  | .reg r => c.getReg t r
  | .imm v => .ok (movImm t v.toNat)

/-- `t := ` the address `a` (base plus displacement). -/
def FnCtx.getAddr (c : FnCtx) (t : XReg) (a : IR.Addr) : Except String (List Item) := do
  let base ← c.getReg t a.base
  return base ++ (if a.disp == 0 then [] else addImm (xs t) (xs t) a.disp)

/-- The condition code of an IR comparison (after `cmp a, b`). -/
def condCode : IR.Cond → CondCode
  | .eq => .EQ | .ne => .NE
  | .ult => .CC | .ule => .LS | .ugt => .HI | .uge => .CS
  | .slt => .LT | .sle => .LE | .sgt => .GT | .sge => .GE

/-- `x9 := x9 op x10` (64-bit). Uses `x11` for the remainders. -/
def binOp : IR.BinOp → List Item
  | .add => [addReg .W64 .X9 .X9 .X10]
  | .sub => [subReg .W64 .X9 .X9 .X10]
  | .mul => [ins (.MADD (xz .X9) (xz .X9) (xz .X10) (zr .W64))]
  | .umulh => [ins (.UMULH (xz .X9) (xz .X9) (xz .X10))]
  | .udiv => [ins (.UDIV (xz .X9) (xz .X9) (xz .X10))]
  | .sdiv => [ins (.SDIV (xz .X9) (xz .X9) (xz .X10))]
  | .urem => [ins (.UDIV (xz .X11) (xz .X9) (xz .X10)),
              ins (.MSUB (xz .X9) (xz .X11) (xz .X10) (xz .X9))]
  | .srem => [ins (.SDIV (xz .X11) (xz .X9) (xz .X10)),
              ins (.MSUB (xz .X9) (xz .X11) (xz .X10) (xz .X9))]
  | .and => [ins (.AND_s (xz .X9) (xz .X9) ⟨xz .X10, 0, .LSL⟩)]
  | .or => [ins (.ORR_s (xz .X9) (xz .X9) ⟨xz .X10, 0, .LSL⟩)]
  | .xor => [ins (.EOR_s (xz .X9) (xz .X9) ⟨xz .X10, 0, .LSL⟩)]
  | .shl => [ins (.LSLV (xz .X9) (xz .X9) (xz .X10))]
  | .lshr => [ins (.LSRV (xz .X9) (xz .X9) (xz .X10))]
  | .ashr => [ins (.ASRV (xz .X9) (xz .X9) (xz .X10))]

/-- `lsr d, s, #k` (`ubfm d, s, #k, #63`). -/
def lsrImm (d s : XReg) (k : Nat) : Item := ins (.UBFM (xz d) (xz s) k 63)

/-- `x9 := op x9`. Population count has no scalar instruction in the base
ISA; it is the usual SWAR sequence (temporaries `x10`, `x11`). -/
def unOp : IR.UnOp → List Item
  | .not => [ins (.ORN_s (xz .X9) (zr .W64) ⟨xz .X9, 0, .LSL⟩)]
  | .neg => [ins (.SUB_s (xz .X9) (zr .W64) ⟨xz .X9, 0, .LSL⟩)]
  | .ctz => [ins (.RBIT (xz .X9) (xz .X9)), ins (.CLZ (xz .X9) (xz .X9))]
  | .popcnt =>
    [lsrImm .X10 .X9 1,
     ins (.AND_i (xs .X10) (xz .X10) (i64 0x5555555555555555)),
     subReg .W64 .X9 .X9 .X10,
     ins (.AND_i (xs .X10) (xz .X9) (i64 0x3333333333333333)),
     lsrImm .X9 .X9 2,
     ins (.AND_i (xs .X9) (xz .X9) (i64 0x3333333333333333)),
     addReg .W64 .X9 .X9 .X10,
     lsrImm .X10 .X9 4,
     addReg .W64 .X9 .X9 .X10,
     ins (.AND_i (xs .X9) (xz .X9) (i64 0x0f0f0f0f0f0f0f0f))] ++
    movImm .X11 0x0101010101010101 ++
    [ins (.MADD (xz .X9) (xz .X9) (xz .X11) (zr .W64)),
     lsrImm .X9 .X9 56]

/-- `x9 := ` the low `w` bits of `x9`, zero- or sign-extended. -/
def extOp (signed : Bool) : IR.Width → List Item
  | .w64 => []
  | w => [if signed then ins (.SBFM (xz .X9) (xz .X9) 0 (w.bits - 1))
          else ins (.UBFM (xz .X9) (xz .X9) 0 (w.bits - 1))]

/-- The Kraken access width of a word or doubleword IR width. -/
def regWidthOf : IR.Width → RegWidth
  | .w64 => .W64
  | _ => .W32

def memWidthOf : IR.Width → MemWidth
  | .w8 => .W8 | .w16 => .W16 | .w32 => .W32 | .w64 => .W64

/-- `x9 := ` the `w`-bit value at `[x10 + disp]`, zero-extended. -/
def plainLoad (w : IR.Width) (disp : Int) : List Item :=
  match w with
  | .w64 => ldrOff .W64 .X9 (xs .X10) disp
  | .w32 => ldrOff .W32 .X9 (xs .X10) disp
  | .w8 => ldrbOff .X9 (xs .X10) disp
  | .w16 =>
    if scaledOk 2 disp then [ins (.LDRH (wz .X9) ⟨xs .X10, .imm ⟨i64 disp, none⟩⟩)]
    else if unscaledOk disp then [ins (.LDURH (wz .X9) ⟨xs .X10, i64 disp⟩)]
    else movImm scratch0 disp ++
      [ins (.LDRH (wz .X9) ⟨xs .X10, .reg ⟨⟨.W64, xz scratch0⟩, ⟨.UXTX, .E0⟩⟩⟩)]

/-- A byte or halfword store of `x9` at the address in `x10`, without a
sub-word store (clause 6): the containing 8-byte-aligned doubleword is read,
the lane replaced, and the doubleword written back (with `stlr` for a release
store). WeakCore's only sub-word store is a lane store into the writer's own
buffer (`WeakCore/SubWord.lean`), and buffers are made of whole 64-bit words,
so no other thread writes that doubleword concurrently and no access of a
different size to it is introduced. The lowering is valid only because the
fragment never emits a sub-word store to a cell another thread can write; if a
later fragment admits sub-word stores to shared cells, the IR needs an
ownership marker on stores so that the emitter can tell the cases apart. Temporaries `x11`–`x14`. -/
def subWordStoreDyn (w : IR.Width) (release : Bool) : List Item :=
  [ins (.AND_i (xs .X11) (xz .X10) (i64 (-8))),            -- doubleword address
   ins (.UBFM (xz .X12) (xz .X10) 61 2),                    -- (addr & 7) * 8
   ins (.LDR (xz .X13) (.addr ⟨xs .X11, .imm ⟨i64 0, none⟩⟩))] ++
  movImm .X14 (if w == .w8 then 0xff else 0xffff) ++
  [ins (.LSLV (xz .X14) (xz .X14) (xz .X12)),
   ins (.BIC_s (xz .X13) (xz .X13) ⟨xz .X14, 0, .LSL⟩),
   ins (.UBFM (xz .X9) (xz .X9) 0 (w.bits - 1)),
   ins (.LSLV (xz .X9) (xz .X9) (xz .X12)),
   ins (.ORR_s (xz .X13) (xz .X13) ⟨xz .X9, 0, .LSL⟩),
   if release then storeRel .W64 .X13 .X11
   else ins (.STR (xz .X13) ⟨xs .X11, .imm ⟨i64 0, none⟩⟩)]

/-- Load register arguments into `x0`, `x1`, ... (at most eight). -/
def FnCtx.getArgs (c : FnCtx) (args : List IR.Operand) : Except String (List Item) := do
  if args.length > argRegs.length then
    throw s!"scc (arm): more than {argRegs.length} register arguments in function {c.name}"
  let mut out : List Item := []
  for (a, r) in args.zip argRegs do
    out := out ++ (← c.getOp r a)
  return out

/-- Call arguments: those past `x0`–`x7` stored at `[sp + base + 8·j]`
(`base` 0: the outgoing area; `base = frame`: the function's own incoming
area, for a tail call), then the register ones. -/
def FnCtx.callArgs (c : FnCtx) (args : List IR.Operand) (base : Nat := 0) :
    Except String (List Item) := do
  if args.length > IR.maxArgs then
    throw s!"scc (arm): more than {IR.maxArgs} arguments in function {c.name}"
  let mut out : List Item := []
  for (a, j) in (args.drop argRegs.length).zipIdx do
    out := out ++ (← c.getOp .X9 a) ++ strOff .W64 .X9 spW64 (base + 8 * j)
  return out ++ (← c.getArgs (args.take argRegs.length))

/-- Store results `x0`, `x1`, ... into IR registers. -/
def FnCtx.setResults (c : FnCtx) (ds : List IR.Reg) : Except String (List Item) := do
  if ds.length > IR.maxRets then
    throw s!"scc (arm): more than {IR.maxRets} results in function {c.name}"
  let mut out : List Item := []
  for (d, r) in ds.zip argRegs do
    out := out ++ (← c.setReg d r)
  return out

/-- An endless self-branch, after code that never returns. -/
def halt (l : Label) : List Item := [lbl l, jmp l]

/-- The `spawnReg` registers the function has, each with the register a
`clone` passes it in (`x10`–`x14`, `Inst.clone`). -/
def FnCtx.spawnArgs (c : FnCtx) : List (IR.Reg × XReg) :=
  (IR.spawnRegs.zip [.X10, .X11, .X12, .X13, .X14]).filter fun (r, _) => c.slots.contains r

/-- Emit one IR instruction (`k` is its index in the function, for labels). -/
def FnCtx.inst (c : FnCtx) (k : Nat) : IR.Inst → Except String (List Item)
  | .mov d s => do return (← c.getOp .X9 s) ++ (← c.setReg d .X9)
  | .bin op d a b => do return (← c.getOp .X9 a) ++ (← c.getOp .X10 b) ++ binOp op ++ (← c.setReg d .X9)
  | .un op d a => do return (← c.getOp .X9 a) ++ unOp op ++ (← c.setReg d .X9)
  | .ext s w d a => do return (← c.getOp .X9 a) ++ extOp s w ++ (← c.setReg d .X9)
  | .setc cc d a b => do
    return (← c.getOp .X9 a) ++ (← c.getOp .X10 b) ++
      [cmpReg .W64 .X9 .X10, cset .W64 .X9 (condCode cc)] ++ (← c.setReg d .X9)
  | .select cc d a b t f => do
    return (← c.getOp .X9 a) ++ (← c.getOp .X10 b) ++ [cmpReg .W64 .X9 .X10] ++
      (← c.getOp .X11 t) ++ (← c.getOp .X12 f) ++
      [ins (.CSEL (xz .X9) (xz .X11) (xz .X12) (condCode cc))] ++ (← c.setReg d .X9)
  | .addChk d a b => do
    return (← c.getOp .X9 a) ++ (← c.getOp .X10 b) ++
      addChecked .X9 .X9 .X10 (c.local "abort_overflow") ++ (← c.setReg d .X9)
  | .subSat d a b => do
    return (← c.getOp .X9 a) ++ (← c.getOp .X10 b) ++ subSat .X9 .X9 .X10 ++ (← c.setReg d .X9)
  | .la d s => do
    if labelOk s then return addrOf .X9 s ++ (← c.setReg d .X9)
    else throw s!"scc (arm): invalid symbol {s}"
  | .getTp d => do return [readTp .X9] ++ (← c.setReg d .X9)
  | .load o w d a => do
    let base ← c.getReg .X10 a.base
    let body ← match o with
      | .plain => pure (plainLoad w a.disp)
      | .acq =>
        pure ((if a.disp == 0 then [] else addImm (xs .X10) (xs .X10) a.disp) ++
          [ins (.LDAR .acq false (memWidthOf w) (rz (regWidthOf w) .X9) (xs .X10))])
      | .rel => throw s!"scc (arm): release load in function {c.name}"
    return base ++ body ++ (← c.setReg d .X9)
  | .store o w a v => do
    let val ← c.getOp .X9 v
    let rel ← match o with
      | .plain => pure false
      | .rel => pure true
      | .acq => throw s!"scc (arm): acquire store in function {c.name}"
    match w, rel with
    | .w64, false | .w32, false => do
      return val ++ (← c.getReg .X10 a.base) ++ strOff (regWidthOf w) .X9 (xs .X10) a.disp
    | .w64, true | .w32, true => do
      return val ++ (← c.getAddr .X10 a) ++ [storeRel (regWidthOf w) .X9 .X10]
    | _, _ => do return val ++ (← c.getAddr .X10 a) ++ subWordStoreDyn w rel
  | .rmw op d a v => do
    let body := match op with
      | .xchg => swpAL .W64 .X9 .X11 .X10
      | .add => ldopAL .ADD .W64 .X9 .X11 .X10
    return (← c.getOp .X9 v) ++ (← c.getAddr .X10 a) ++ [body] ++ (← c.setReg d .X11)
  | .fence f => do return [ins (.DMB (match f with | .ld => .ld | .st => .st | .full => .sy))]
  | .call ds f args => do
    if labelOk f then
      return (← c.callArgs args) ++ [call f] ++
        (if c.maps then [lbl (c.local s!"sp{k}")] else []) ++ (← c.setResults ds)
    else throw s!"scc (arm): invalid symbol {f}"
  | .syscall d nr args l => do
    let here ← match l with
      | some l => if labelOk l then pure [lbl l] else throw s!"scc (arm): invalid symbol {l}"
      | none => pure []
    return (← c.getArgs args) ++ movImm .X8 nr.nrA64 ++ here ++ [ins (.SVC 0)] ++ (← c.setReg d .X0)
  | .clone d stack tls entry arg => do
    unless labelOk entry do throw s!"scc (arm): invalid symbol {entry}"
    -- clone(flags, newsp, parent_tid = 0, tls, child_tid = 0): the AArch64
    -- argument order puts `tls` in x3. The child keeps x9 (the argument)
    -- and x10–x14 (the `spawnReg`s) and branches to its stub (`childStub`).
    let parent := c.local s!"clone{k}"
    let mut spawn : List Item := []
    for (r, t) in c.spawnArgs do
      spawn := spawn ++ (← c.getReg t r)
    return (← c.getOp .X1 stack) ++ (← c.getOp .X3 tls) ++ (← c.getOp .X9 arg) ++ spawn ++
      movImm .X0 IR.cloneFlags ++ movImm .X2 0 ++ movImm .X4 0 ++ syscall sysClone ++
      [cbz .W64 .X0 (c.local s!"child{k}"), lbl parent] ++ (← c.setReg d .X0)
  | .slotAddr d s => do return addImm (xs .X9) spW64 (← c.slotOff s) ++ (← c.setReg d .X9)
  | .site s args => do
    unless labelOk s do throw s!"scc (arm): invalid symbol {s}"
    return (← c.getArgs args) ++ [lbl s, ins (w := .W64) .NOP]
  | .comment s => do return [.comment s]

/-- The child's stub of the `clone` with index `k` into `entry`, placed
after the function's code: frameless, it moves the argument (`x9`) and the
`spawnReg`s (`x10`–`x14`) into the argument registers, ends the frame-record
chain and calls `entry`, which never returns. -/
def FnCtx.childStub (c : FnCtx) (k : Nat) (entry : IR.Sym) : List Item :=
  [lbl (c.local s!"child{k}"), movReg .W64 .X0 .X9] ++
    (([XReg.X10, .X11, .X12, .X13, .X14].zip (argRegs.drop 1)).filterMap fun (t, a) =>
      if c.spawnArgs.any (·.2 == t) then some (movReg .W64 a t) else none) ++
    (if c.maps then movImm .X29 0 else []) ++ [call entry] ++
    halt (c.local s!"child{k}_halt")

/-- The `clone`s of a function with their instruction indices (the `k` of
`FnCtx.inst`: instructions and terminators numbered in order) and entries. -/
def cloneSites (f : IR.Func) : List (Nat × IR.Sym) :=
  (f.blocks.foldl (fun (acc : Nat × List (Nat × IR.Sym)) b =>
    let r := b.insts.foldl (fun (acc : Nat × List (Nat × IR.Sym)) i =>
      (acc.1 + 1, match i with
        | .clone _ _ _ e _ => acc.2 ++ [(acc.1, e)]
        | _ => acc.2)) acc
    (r.1 + 1, r.2)) (0, [])).2

/-- Restore `x29`/`x30` and pop the frame (no return). -/
def FnCtx.leave (c : FnCtx) : List Item :=
  ldrOff .W64 .X29 spW64 (c.frame - 16) ++ ldrOff .W64 .X30 spW64 (c.frame - 8) ++
  addImm spW64 spW64 c.frame

/-- Emit a block terminator (`k` a unique index for labels). -/
def FnCtx.term (c : FnCtx) (k : Nat) : IR.Term → Except String (List Item)
  | .ret vs => do
    if vs.length > IR.maxRets then
      throw s!"scc (arm): more than {IR.maxRets} results in function {c.name}"
    let mut out : List Item := []
    for (v, r) in vs.zip argRegs do
      out := out ++ (← c.getOp r v)
    return out ++ c.leave ++ [ret]
  | .jmp l => do return [jmp (← c.blockLabel l)]
  | .br cc a b t f => do
    return (← c.getOp .X9 a) ++ (← c.getOp .X10 b) ++
      [cmpReg .W64 .X9 .X10, jcc (condCode cc) (← c.blockLabel t), jmp (← c.blockLabel f)]
  | .tail f args => do
    unless labelOk f do throw s!"scc (arm): invalid symbol {f}"
    if IR.StackMap.stackWords argRegs.length args.length > c.inArea then
      throw s!"scc (arm): tail call of {f} with {args.length} arguments in function {c.name} (argument area of {c.inArea} words)"
    return (← c.callArgs args c.frame) ++ c.leave ++ [jmp f]
  | .switchTo stack tls f arg => do
    unless labelOk f do throw s!"scc (arm): invalid symbol {f}"
    return (← c.getOp .X9 stack) ++ (← c.getOp .X10 tls) ++ (← c.getOp .X0 arg) ++
      [writeTp .X10, movSp spW64 (xs .X9)] ++ (if c.maps then movImm .X29 0 else []) ++ [call f] ++
      halt (c.local s!"halt{k}")
  | .unreachable => do return halt (c.local s!"halt{k}")

/-- The IR registers of a function, in order of first occurrence. -/
def funcRegs (f : IR.Func) : List IR.Reg :=
  let op : IR.Operand → List IR.Reg := fun | .reg r => [r] | .imm _ => []
  let inst : IR.Inst → List IR.Reg
    | .mov d s => d :: op s
    | .bin _ d a b => d :: op a ++ op b
    | .un _ d a => d :: op a
    | .ext _ _ d a => d :: op a
    | .setc _ d a b => d :: op a ++ op b
    | .select _ d a b t e => d :: op a ++ op b ++ op t ++ op e
    | .addChk d a b => d :: op a ++ op b
    | .subSat d a b => d :: op a ++ op b
    | .la d _ => [d]
    | .getTp d => [d]
    | .load _ _ d a => [d, a.base]
    | .store _ _ a v => a.base :: op v
    | .rmw _ d a v => d :: a.base :: op v
    | .fence _ => []
    | .call ds _ args => ds ++ args.flatMap op
    | .syscall d _ args _ => d :: args.flatMap op
    | .clone d s t _ a => d :: op s ++ op t ++ op a
    | .slotAddr d s => [d, s]
    | .site _ args => args.flatMap op
    | .comment _ => []
  let term : IR.Term → List IR.Reg
    | .ret vs => vs.flatMap op
    | .jmp _ => []
    | .br _ a b _ _ => op a ++ op b
    | .tail _ args => args.flatMap op
    | .switchTo s t _ a => op s ++ op t ++ op a
    | .unreachable => []
  let all := f.params ++ f.blocks.flatMap (fun b => b.insts.flatMap inst ++ term b.term)
  all.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) []

/-- Words of a function's outgoing argument area: the most any of its calls
reserves (`IR.StackMap.callWords`: the callee's argument area, past
`x0`–`x7`), rounded up to an even number. -/
def outWords (areas : List (IR.Sym × Nat)) (f : IR.Func) : Nat :=
  let n := f.blocks.foldl (fun n b => b.insts.foldl (fun n i => match i with
    | .call _ g args => max n (IR.StackMap.callWords areas argRegs.length g args.length)
    | _ => n) n) 0
  (n + 1) / 2 * 2

/-- A safepoint: its label and the offsets of its stack and heap slots from
the frame record. -/
abbrev Safepoint := Label × List Int × List Int

/-- The context of function `f`, the `fi`th of the program: its slots,
frame and labels. -/
def fnCtx (abortFn : String) (growth : Option IR.Growth) (areas : List (IR.Sym × Nat))
    (fi : Nat) (f : IR.Func) : FnCtx :=
  let slots := funcRegs f
  let out := outWords areas f
  { fi, name := f.name, slots, blocks := f.blocks.map (·.label),
    frame := 8 * out + align16 (8 * slots.length + 16), out,
    inArea := ((areas.find? (·.1 == f.name)).map (·.2)).getD 0, abortFn,
    maps := growth.isSome }

/-- Emit one function; also return its safepoints in code order. -/
def emitFunc (abortFn : String) (growth : Option IR.Growth) (areas : List (IR.Sym × Nat))
    (fi : Nat) (f : IR.Func) : Except String (List Item × List Safepoint) := do
  unless labelOk f.name do throw s!"scc (arm): invalid function name {f.name}"
  if f.params.length > IR.maxArgs then
    throw s!"scc (arm): more than {IR.maxArgs} parameters in function {f.name}"
  let c := fnCtx abortFn growth areas fi f
  let fpOff (r : IR.Reg) : Except String Int := do
    return (← c.slotOff r) - ((c.frame : Int) - 16)
  -- Prologue: allocate the frame (checking the stack limit if asked), save
  -- x29/x30, store the parameters.
  let alloc :=
    if f.checkStack then
      (if c.maps then [lbl (c.local "stack_check")] else []) ++
      addImm (xs .X9) spW64 (-(c.frame : Int)) ++
      [readTp .X10] ++ ldrOff .W64 .X10 (xs .X10) IR.Tcb.stackLimit ++
      [cmpReg .W64 .X9 .X10, jcc .CC (c.local (if c.maps then "stack_grow" else "abort_stack")),
       movSp spW64 (xs .X9)]
    else addImm spW64 spW64 (-(c.frame : Int))
  let save := strOff .W64 .X29 spW64 (c.frame - 16) ++ strOff .W64 .X30 spW64 (c.frame - 8) ++
    addImm (xs .X29) spW64 (c.frame - 16)
  let mut params : List Item := []
  for (p, r) in f.params.zip argRegs do
    params := params ++ (← c.setReg p r)
  for (p, j) in (f.params.drop argRegs.length).zipIdx do
    params := params ++ ldrOff .W64 .X9 spW64 (c.frame + 8 * j) ++ (← c.setReg p .X9)
  let mut body : List Item := []
  let mut sps : List Safepoint := []
  let mut k := 0
  for (b, ms) in f.blocks.zip (IR.StackMap.callMaps f) do
    let mut code := [lbl (← c.blockLabel b.label)]
    for (i, sm) in b.insts.zip ms do
      code := code ++ (← c.inst k i)
      if c.maps then
        if let some e := sm then
          sps := sps ++ [(c.local s!"sp{k}", ← e.stack.mapM fpOff, ← e.heap.mapM fpOff)]
      k := k + 1
    code := code ++ (← c.term k b.term)
    k := k + 1
    body := body ++ code
  let abortStub (suffix : String) (kind : IR.AbortKind) : List Item :=
    [lbl (c.local suffix)] ++ movImm .X0 kind.code ++ [call abortFn] ++
      halt (c.local (suffix ++ "_halt"))
  let hasAddChk := f.blocks.any fun b => b.insts.any fun | .addChk .. => true | _ => false
  -- The grow stub (see the section docstring): save area of 80 bytes.
  let saveOff (r : IR.Reg) : Int := match f.params.idxOf? r with
    | some i => if i < argRegs.length then 8 * (i : Int) - 64
                else 16 + 8 * ((i - argRegs.length : Nat) : Int)
    | none => 0
  let growStub : List Item :=
    [lbl (c.local "stack_grow")] ++ addImm spW64 spW64 (-80) ++
    (argRegs.zipIdx.flatMap fun (r, i) => strOff .W64 r spW64 (8 * i)) ++
    strOff .W64 .X29 spW64 64 ++ strOff .W64 .X30 spW64 72 ++ addImm (xs .X29) spW64 64 ++
    movImm .X0 c.frame ++ [call IR.StackMap.morestackSym, lbl (c.local "sp_check")] ++
    (argRegs.zipIdx.flatMap fun (r, i) => ldrOff .W64 r spW64 (8 * i)) ++
    ldrOff .W64 .X29 spW64 64 ++ ldrOff .W64 .X30 spW64 72 ++ addImm spW64 spW64 80 ++
    [jmp (c.local "stack_check")]
  let checkSp : List Safepoint :=
    if f.checkStack && growth.isSome then
      let e := IR.StackMap.checkMap f
      [(c.local "sp_check", e.stack.map saveOff, e.heap.map saveOff)]
    else []
  let childStubs := (cloneSites f).flatMap fun (k, e) => c.childStub k e
  let stubs :=
    (if f.checkStack then
      (if growth.isSome then growStub else abortStub "abort_stack" .stack) else []) ++
    ((if hasAddChk then abortStub "abort_overflow" .overflow else []) ++ childStubs)
  return ([.raw ".p2align 2", .raw s!".type {f.name}, %function", lbl f.name] ++
    alloc ++ save ++ params ++ body ++ stubs, sps ++ checkSp)

/-- `.byte` lines for a data item, 16 bytes per line. -/
def byteLines (bs : List UInt8) : List Item :=
  let rec go (fuel : Nat) (bs : List UInt8) : List Item :=
    match fuel, bs with
    | 0, _ | _, [] => []
    | fuel + 1, bs =>
      .raw (".byte " ++ ", ".intercalate ((bs.take 16).map (toString ·.toNat))) ::
        go fuel (bs.drop 16)
  go bs.length bs

def emitData (d : IR.Data) : Except String (List Item) := do
  unless labelOk d.name do throw s!"scc (arm): invalid data name {d.name}"
  match d.init with
  | .zero n => do
    return [.raw ".bss", .raw s!".balign {d.align}", .raw s!".type {d.name}, %object", lbl d.name,
      .raw s!".zero {max n 1}", .raw s!".size {d.name}, {max n 1}"]
  | .bytes bs => do
    return [.raw ".data", .raw s!".balign {d.align}", lbl d.name] ++
      (if bs.isEmpty then [.raw ".zero 1"] else byteLines bs)

/-- The trampoline between a grow stub and `Growth.grow` (the protocol is in
`Scc.IR.StackMap`): `x0` = the frame size that did not fit. -/
def morestack (g : IR.Growth) : List Item :=
  [.raw ".p2align 2", .raw s!".type {IR.StackMap.morestackSym}, %function",
   lbl IR.StackMap.morestackSym] ++
  addImm spW64 spW64 (-16) ++ strOff .W64 .X29 spW64 0 ++ strOff .W64 .X30 spW64 8 ++
  addImm (xs .X29) spW64 0 ++
  [movReg .W64 .X1 .X0, movReg .W64 .X0 .X29, call g.grow,
   -- (x0, x1, x2) = (delta, old base, old size); move onto the new range.
   addReg .W64 .X29 .X29 .X0, movSp spW64 (xs .X29),
   movReg .W64 .X0 .X1, movReg .W64 .X1 .X2, call g.release] ++
  ldrOff .W64 .X29 spW64 0 ++ ldrOff .W64 .X30 spW64 8 ++ addImm spW64 spW64 16 ++ [ret]

/-- The stack-map table (format in `Scc.IR.StackMap`). -/
def mapItems (sps : List Safepoint) : List Item :=
  let entries := (sps.foldl (fun (acc, first) (l, st, hp) =>
      (acc ++ [Item.raw s!".quad {l}, {st.length}, {hp.length}, {first}"],
       first + st.length + hp.length)) ([], 0)).1
  [.raw ".section .rodata", .raw ".balign 8", lbl IR.StackMap.tableSym,
   .raw s!".quad {sps.length}"] ++ entries ++
  sps.flatMap fun (_, st, hp) => (st ++ hp).map fun o => Item.raw s!".quad {o}"

/-- The whole-program checks before the functions are emitted (the start
and abort symbols, the stack maps, no stack argument area where a function
is entered without a caller), and the stack argument areas the functions are
emitted with (`emitItemsMaps`). -/
def emitPre (p : IR.Program) : Except String (List (IR.Sym × Nat)) := do
  unless labelOk p.start && labelOk p.abortFn do
    throw "scc (arm): invalid start or abort symbol"
  IR.StackMap.check p
  let areas := IR.StackMap.argAreas p argRegs.length
  -- Entered with no caller's outgoing area (`_start`, `clone`, `switchTo`):
  -- such functions must need no argument area.
  for e in [p.start] ++ p.funcs.flatMap (fun f => f.blocks.flatMap fun b =>
      (b.insts.filterMap fun | .clone _ _ _ g _ => some g | _ => none) ++
      (match b.term with | .switchTo _ _ g _ => [g] | _ => [])) do
    if IR.StackMap.callWords areas argRegs.length e 0 > 0 then
      throw s!"scc (arm): {e} is entered without a caller but has a stack argument area"
  return areas

/-- Emit the function `f`, the `fi`th of `p`, with the argument areas
`areas` (`emitItemsMaps`). -/
def emitFuncAt (p : IR.Program) (areas : List (IR.Sym × Nat)) (x : IR.Func × Nat) :
    Except String (List Item × List Safepoint) :=
  emitFunc p.abortFn p.growth areas x.2 x.1

/-- The items of a whole program from its functions' items and safepoints
`rs`, in order (`emitItemsMaps`): header, `_start` (a jump to
`Program.start`), the functions, then the data (and, with
`IR.Program.growth`, the trampoline and the stack-map table), and the
safepoints in code order. -/
def emitPost (p : IR.Program) (rs : List (List Item × List Safepoint)) :
    Except String (List Item × List Safepoint) := do
  let fs := rs.flatMap (·.1)
  let sps := rs.flatMap (·.2)
  -- `.data` and `.bss` start 16-aligned (`Data.Secs.ofProgram`).
  let mut ds : List Item := [.raw ".data", .raw ".balign 16", .raw ".bss", .raw ".balign 16"]
  for d in p.data do
    ds := ds ++ (← emitData d)
  let (ms, tab) := match p.growth with
    | some g => (morestack g, mapItems sps)
    | none => ([], [])
  -- `.p2align 4` first in `.text`: it pads nothing (offset 0) but makes the
  -- section 16-aligned, so a linker places the code on a 16-byte boundary
  -- whatever precedes it (the placement check requires one).
  return ([.comment "generated by scc (arm: AArch64 FEAT_LSE2, Linux)",
          .raw ".arch armv8.4-a", .raw ".text", .raw ".globl _start", .raw ".p2align 4",
          lbl "_start", jmp p.start] ++ fs ++ ms ++ ds ++ tab, sps)

/-- The items of a whole program and its safepoints in code order: the
checks (`emitPre`), each function (`emitFuncAt`), then the rest
(`emitPost`). A certificate checks the three parts separately
(`emitItemsMaps_of_stages`). -/
def emitItemsMaps (p : IR.Program) : Except String (List Item × List Safepoint) := do
  let areas ← emitPre p
  let rs ← p.funcs.zipIdx.mapM (emitFuncAt p areas)
  emitPost p rs

/-- **`emitItemsMaps` from its stages**: the checks give the argument areas
`areas`, the functions their items and safepoints `rs`, and the rest the
result. A certificate checks the checks, each function and the rest in
their own kernel runs, and chains the functions
(`Scc.Cert.OutLit.mapM_ok_cons`). -/
theorem emitItemsMaps_of_stages {p : IR.Program} {areas : List (IR.Sym × Nat)}
    {rs : List (List Item × List Safepoint)} {r : List Item × List Safepoint}
    (h1 : emitPre p = .ok areas) (h2 : p.funcs.zipIdx.mapM (emitFuncAt p areas) = .ok rs)
    (h3 : emitPost p rs = .ok r) : emitItemsMaps p = .ok r := by
  unfold emitItemsMaps
  rw [h1]
  show (p.funcs.zipIdx.mapM (emitFuncAt p areas) >>= emitPost p) = _
  rw [h2]
  exact h3

/-- The items of a whole program (`emitItemsMaps`). -/
def emitItems (p : IR.Program) : Except String (List Item) :=
  (·.1) <$> emitItemsMaps p

/-- The data sections of a program's assembler text as data images
(`Scc.Emit.Data`): what `emitData` and `mapItems` write. -/
def dataSecs (p : IR.Program) : Except String Data.Secs := do
  let (_, sps) ← emitItemsMaps p
  pure (Data.Secs.ofProgram p.data (if p.growth.isSome then some sps else none))

/-- The assembler text of a whole program. -/
def emitProgram (p : IR.Program) : Except String String := do
  render (← emitItems p)

end FromIR

end Scc.Emit.A64
