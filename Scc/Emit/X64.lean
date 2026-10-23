import Scc.IR.StackMap
import Scc.Emit.X64Print
import Scc.Emit.Data

/-!
# The x64 emitter

IR → GNU assembler, AT&T syntax, for a static Linux binary with no libc.

**Output.** The emitter builds a list of `Item`s (`Scc.Emit.X64Print`):
Kraken x64 `Directive`s for every instruction and label Kraken's syntax has,
and assembler directive lines for sections, symbols and data.  There are no
raw instruction lines: `syscall`, `ud2`, the `%fs:` moves of `getTp` and the
stack check (`Kraken/SYSCALL.md`), `divq`/`cqto`/`idivq` and `popcntq` are
Kraken directives.  `render` prints the list; `Scc/Emit/X64Test.lean` checks that
every item reads back as itself with Kraken's parser.

**Register allocation.**  Every IR register lives in its own 8-byte frame slot
below `%rbp`; each instruction loads its operands into scratch registers
(`%rax`, `%rcx`, `%rdx`, `%rsi`), computes, and stores the result back.  So no
IR register survives in a machine register across instructions, and calls
need no save/restore.

**Calling convention** (SysV-like, scc-internal): arguments in `%rdi`, `%rsi`,
`%rdx`, `%rcx`, `%r8`, `%r9`, then on the stack: argument `6 + j` at
`8j(%rsp)` at the call, so at `16+8j(%rbp)` in the callee, which copies it to
its slot in the prologue; results in `%rax`, `%rdx`, `%rcx`, `%rsi`,
`%rdi`, `%r8`.  The frame is `push %rbp; mov %rsp, %rbp; sub $F, %rsp` with
`F` a multiple of 16, so `%rsp` is 16-byte aligned at every call; its bottom
`8·outWords` bytes are the outgoing argument area, as large as the argument
area of any callee (`StackMap.argAreas`).  A tail call writes its stack
arguments over the function's own incoming area, which the argument areas
make large enough, so every tail call runs in constant stack.  The
prologue's stack check (when `Func.checkStack`) compares `%rsp - F` with the
TCB's stack limit at `%fs:8`, loaded into `%r11` first (Kraken's `%fs:`
operand is `mov` only; `%r11` is free there: it is neither an argument
register nor used anywhere else by the emitter); below it, the abort routine,
or (with `Program.growth`) the grow stub.

**Growable stacks** (`Scc.IR.StackMap`).  `%rbp` is the frame-record pointer
(`[%rbp]` the caller's `%rbp`, `[%rbp+8]` the return address).  The grow
stub of a function pushes the six argument registers (`%rdi` at
`-8(%rbp)` … `%r9` at `-48(%rbp)`; stack parameters are still at
`16+8j(%rbp)`, where the check's map designates them), passes `F` in `%rdi` to
`scc_rt_morestack`, pops the registers and repeats the check.  Every call is
followed by a local label, its safepoint, and the stack-map table lists the
slots `-8(k+1)(%rbp)` of the registers the map designates.  Frame slots are
addressed from `%rbp` only, and no other machine register holds a stack
address across a call, so a moved frame works once `%rbp` and the saved
`%rbp` values are rewritten.

**Thread pointer.**  `%fs` base = the TCB address; the TCB's first word is its
own address, so `getTp` is `mov %fs:0, %reg`.  `switchTo` sets it with
`arch_prctl(ARCH_SET_FS)`, and `clone` with `CLONE_SETTLS`.

**Division.**  `div`/`idiv` fault on a zero divisor and on `-2^63 / -1`; the
emitter branches around both to produce the IR's results (`x / 0 = 0`,
`x % 0 = x`, `-2^63 / -1 = -2^63`, `-2^63 % -1 = 0`).

**Bit counts.**  `ctz` is `tzcntq` (BMI1, which Kraken assumes; it gives 64
on a zero source); `popcnt` is `popcntq`.

**Sub-word loads.**  An 8- or 16-bit load is a narrow `mov` into `%al`/`%ax`
followed by a register `movzbl`/`movzwl` (one memory access, the same as a
`movz*` with a memory source, which Kraken's parser does not read).

**Fences.**  Under TSO, `Fence.ld` and `Fence.st` need no code; `Fence.full`
is `mfence`.  Acquire loads and release stores are plain `mov`s.

This emitter is not verified; the certificates re-parse its output.
-/

namespace Scc.Emit.X64
open Scc.IR

/-- Emitter state: output items and a counter for local labels. The two
lists are kept in reverse order (the last item first): adding to the front
is constant time also when the kernel evaluates the emitter, where an
`Array.push` copies the whole array. -/
structure S where
  /-- The items so far, the last first. -/
  out : List Item := []
  next : Nat := 0
  /-- Safepoints so far, the last first: label, stack offsets, heap offsets
  (from the frame record). -/
  maps : List (String × List Int × List Int) := []

abbrev E := StateT S (Except String)

def item (it : Item) : E Unit := modify fun st => { st with out := it :: st.out }
/-- An instruction Kraken's syntax has. -/
def ins (d : Directive) : E Unit := item (.d d)
/-- A label. -/
def lbl (l : String) : E Unit := item (.d (.label l))
/-- An assembler directive line. -/
def dir (s : String) : E Unit := item (.dir s)
/-- `syscall`. -/
def sysc : E Unit := ins (i64 .syscall)
/-- `ud2`. -/
def ud2 : E Unit := ins (i64 .ud2)
/-- `movq %fs:off, %r`. -/
def movFs (r : Reg64) (off : Nat) : E Unit :=
  ins (i64 (.movfs (xr r) (om { base := none, idx := none, disp := .int64 (Int64.ofNat off) })))

def freshL (fn : String) : E String := do
  let st ← get
  set { st with next := st.next + 1 }
  pure s!".L{fn}.x{st.next}"

/-- Registers by position. -/
def argRegs : List Reg64 := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]
def retRegs : List Reg64 := [.rax, .rdx, .rcx, .rsi, .rdi, .r8]
def sysRegs : List Reg64 := [.rdi, .rsi, .rdx, .r10, .r8, .r9]

/-- Frame slots of a function's registers. -/
structure Frame where
  fn : String
  slots : List (IR.Reg × Nat)
  size : Nat
  /-- Words of the function's incoming argument area
(`StackMap.argAreas`): its tail calls write at most this many. -/
  inArea : Nat := 0
  /-- Record safepoints (the program has `Program.growth`). -/
  maps : Bool := false

/-- The offset of a register's slot from the frame record. -/
def Frame.slotOff (f : Frame) (r : IR.Reg) : E Int :=
  match f.slots.find? (·.1 == r) with
  | some (_, k) => pure (-(8 * ((k : Int) + 1)))
  | none => throw s!"{f.fn}: no slot for register {r}"

/-- A register's slot, `-8(k+1)(%rbp)`. -/
def Frame.slot (f : Frame) (r : IR.Reg) : E AddrExpr := do
  pure (mem .rbp (← f.slotOff r))

/-- Record a safepoint at local label `l`. -/
def recordMap (l : String) (stack heap : List Int) : E Unit :=
  modify fun st => { st with maps := (l, stack, heap) :: st.maps }

/-- Place a safepoint label after a call and record its map. -/
def safepoint (fr : Frame) (sm : Option StackMap.Entry) : E Unit := do
  if fr.maps then
    let l ← freshL fr.fn
    lbl l
    let e := sm.getD {stack := [], heap := []}
    recordMap l (← e.stack.mapM fr.slotOff) (← e.heap.mapM fr.slotOff)

def opRegs : IR.Operand → List IR.Reg
  | .reg r => [r]
  | .imm _ => []

def instRegs : Inst → List IR.Reg
  | .mov d s => d :: opRegs s
  | .bin _ d a b => d :: opRegs a ++ opRegs b
  | .un _ d a => d :: opRegs a
  | .ext _ _ d a => d :: opRegs a
  | .setc _ d a b => d :: opRegs a ++ opRegs b
  | .select _ d a b t f => d :: opRegs a ++ opRegs b ++ opRegs t ++ opRegs f
  | .addChk d a b => d :: opRegs a ++ opRegs b
  | .subSat d a b => d :: opRegs a ++ opRegs b
  | .la d _ => [d]
  | .getTp d => [d]
  | .load _ _ d a => [d, a.base]
  | .store _ _ a v => a.base :: opRegs v
  | .rmw _ d a v => [d, a.base] ++ opRegs v
  | .fence _ => []
  | .call ds _ args => ds ++ args.flatMap opRegs
  | .syscall d _ args _ => d :: args.flatMap opRegs
  | .clone d s t _ a => d :: opRegs s ++ opRegs t ++ opRegs a
  | .slotAddr d s => [d, s]
  | .site _ args => args.flatMap opRegs
  | .comment _ => []

def termRegs : Term → List IR.Reg
  | .ret vs => vs.flatMap opRegs
  | .jmp _ => []
  | .br _ a b _ _ => opRegs a ++ opRegs b
  | .tail _ args => args.flatMap opRegs
  | .switchTo s t _ a => opRegs s ++ opRegs t ++ opRegs a
  | .unreachable => []

/-- Words of a function's outgoing argument area: the most any of its calls
reserves (`StackMap.callWords`: the callee's argument area), rounded up to
an even number (16 bytes). -/
def outWords (areas : List (Sym × Nat)) (f : Func) : Nat :=
  let n := f.blocks.foldl (fun n b => b.insts.foldl (fun n i => match i with
    | .call _ g args => max n (StackMap.callWords areas 6 g args.length)
    | _ => n) n) 0
  (n + 1) / 2 * 2

/-- The frame: the register slots below `%rbp`, then the outgoing area at
`[%rsp, %rsp + 8·outWords)`. -/
def frameOf (areas : List (Sym × Nat)) (f : Func) : Frame :=
  let all := f.params ++ f.blocks.flatMap fun b => b.insts.flatMap instRegs ++ termRegs b.term
  let regs := all.eraseDups
  let n := regs.length
  { fn := f.name, slots := regs.zipIdx, size := (8 * n + 15) / 16 * 16 + 8 * outWords areas f,
    inArea := ((areas.find? (·.1 == f.name)).map (·.2)).getD 0 }

/-- `movq r, s` (64-bit register to register). -/
def movRR (d s : Reg64) : E Unit := ins (i64 (.mov (xr d) (or_ s)))

/-- `movl $n, %r32` (zero-extends into the 64-bit register). -/
def movl (r : Reg64) (n : Nat) : E Unit := ins (i32 (.mov (xr r) (oi n)))

/-- `xorl %r32, %r32` (clears the 64-bit register). -/
def zero32 (r : Reg64) : E Unit := ins (i32 (.xor (xr r) (or_ r)))

/-- `call f` or `jmp f`, `f` a symbol or a label. -/
def callSym (f : String) : E Unit := ins (i64 (.call (rel f)))
def jmpTo (l : String) : E Unit := ins (i64 (.jmp (rel l)))

/-- Load an operand into machine register `r`.  An immediate is a `movq`
when it is a sign-extended 32-bit value, a `movabsq` otherwise (the printer
chooses). -/
def ld (fr : Frame) (o : IR.Operand) (r : Reg64) : E Unit :=
  match o with
  | .reg x => do ins (i64 (.mov (xr r) (om (← fr.slot x))))
  | .imm v => ins (i64 (.mov (xr r) (.imm (.int64 v.toInt64))))

/-- Store machine register `r` into IR register `d`. -/
def st (fr : Frame) (r : Reg64) (d : IR.Reg) : E Unit := do
  ins (i64 (.mov (xm (← fr.slot d)) (or_ r)))

def cc : Cond → CondCode
  | .eq => .z | .ne => .nz | .ult => .c | .ule => .be | .ugt => .a | .uge => .nc
  | .slt => .l | .sle => .le | .sgt => .g | .sge => .ge

/-- `cmp b, a` (flags of `a - b`), with `a` in `%rax` and `b` in `%rcx`. -/
def cmpAB (fr : Frame) (a b : IR.Operand) : E Unit := do
  ld fr a .rax; ld fr b .rcx; ins (i64 (.cmp (xr .rax) (or_ .rcx)))

def labelOf (fn : String) (l : IR.Label) : String := s!".L{fn}.{l}"

def sysNr : Sys → Nat := Sys.nrX64

/-- `ARCH_SET_FS` and the `arch_prctl` system call number. -/
def archSetFs : Nat := 0x1002
def nrArchPrctl : Nat := 158
def nrClone : Nat := 56

def loadArgs (fr : Frame) (regs : List Reg64) (args : List IR.Operand) (what : String) : E Unit := do
  if args.length > regs.length then throw s!"{fr.fn}: {what} with {args.length} arguments"
  for (a, r) in args.zip regs do ld fr a r

/-- The byte offset from `%rbp` of incoming stack argument `j` (argument
`6 + j`): above the frame record. -/
def inArgOff (j : Nat) : Int := 16 + 8 * (j : Int)

/-- Call arguments: those past the six registers to the outgoing area
`8·j(%rsp)`, then the register ones. -/
def callArgs (fr : Frame) (args : List IR.Operand) (what : String) : E Unit := do
  if args.length > maxArgs then throw s!"{fr.fn}: {what} with {args.length} arguments"
  for (a, j) in (args.drop argRegs.length).zipIdx do
    ld fr a .rax
    ins (i64 (.mov (xm (mem .rsp (8 * (j : Int)))) (or_ .rax)))
  loadArgs fr argRegs (args.take argRegs.length) what

/-- `%rax`, the 64-bit accumulator as a destination register. -/
def rax64 : _root_.Reg .W64 := lw .rax .W64

def emitInst (fr : Frame) (sm : Option StackMap.Entry) : Inst → E Unit
  | .mov d s => do ld fr s .rax; st fr .rax d
  | .bin op d a b => do
      ld fr a .rax; ld fr b .rcx
      match op with
      | .add => ins (i64 (.add (xr .rax) (or_ .rcx)))
      | .sub => ins (i64 (.sub (xr .rax) (or_ .rcx)))
      | .mul => ins (i64 (.imul none (xr .rax) (or_ .rcx)))
      | .umulh => do ins (i64 (.mul (xr .rcx))); movRR .rax .rdx
      | .and => ins (i64 (.and (xr .rax) (or_ .rcx)))
      | .or => ins (i64 (.or (xr .rax) (or_ .rcx)))
      | .xor => ins (i64 (.xor (xr .rax) (or_ .rcx)))
      | .shl => ins (i64 (.shl (xr .rax) .cl))
      | .lshr => ins (i64 (.shr (xr .rax) .cl))
      | .ashr => ins (i64 (.sar (xr .rax) .cl))
      | .udiv | .urem => do
          let zero ← freshL fr.fn
          let done ← freshL fr.fn
          ins (i64 (.test (xr .rcx) (or_ .rcx)))
          ins (i64 (.jcc .z zero))
          zero32 .rdx
          ins (i64 (.div (xr .rcx)))
          if op == .urem then movRR .rax .rdx
          jmpTo done
          lbl zero
          -- x / 0 = 0; x % 0 = x (already in %rax)
          if op == .udiv then zero32 .rax
          lbl done
      | .sdiv | .srem => do
          let zero ← freshL fr.fn
          let m1 ← freshL fr.fn
          let done ← freshL fr.fn
          ins (i64 (.test (xr .rcx) (or_ .rcx)))
          ins (i64 (.jcc .z zero))
          ins (i64 (.cmp (xr .rcx) (oi (-1))))
          ins (i64 (.jcc .z m1))
          ins (i64 .cqo)
          ins (i64 (.idiv (xr .rcx)))
          if op == .srem then movRR .rax .rdx
          jmpTo done
          lbl m1
          -- x / -1 = -x (wrapping at -2^63); x % -1 = 0
          if op == .sdiv then ins (i64 (.neg (xr .rax))) else zero32 .rax
          jmpTo done
          lbl zero
          if op == .sdiv then zero32 .rax
          lbl done
      st fr .rax d
  | .un op d a => do
      ld fr a .rax
      match op with
      | .not => ins (i64 (.not (xr .rax)))
      | .neg => ins (i64 (.neg (xr .rax)))
      | .ctz => ins (i64 (.tzcnt rax64 (xr .rax)))
      | .popcnt => ins (i64 (.popcnt (lw .rax .W64) (xr .rax)))
      st fr .rax d
  | .ext sg w d a => do
      ld fr a .rax
      match sg, w with
      | true, .w8 => ins (i64 (.movsx (xr .rax) (xr (w := .W8) .rax)))
      | true, .w16 => ins (i64 (.movsx (xr .rax) (xr (w := .W16) .rax)))
      | true, .w32 => ins (i64 (.movsx (xr .rax) (xr (w := .W32) .rax)))
      | false, .w8 => ins (i32 (.movzx (xr .rax) (xr (w := .W8) .rax)))
      | false, .w16 => ins (i32 (.movzx (xr .rax) (xr (w := .W16) .rax)))
      | false, .w32 => ins (i32 (.mov (xr .rax) (or_ .rax)))
      | _, .w64 => pure ()
      st fr .rax d
  | .setc c d a b => do
      cmpAB fr a b
      ins (i8 (.setcc (cc c) (xr .rax)))
      ins (i32 (.movzx (xr .rax) (xr (w := .W8) .rax)))
      st fr .rax d
  | .select c d a b t f => do
      ld fr t .rdx; ld fr f .rsi
      cmpAB fr a b
      movRR .rax .rsi
      ins (i64 (.cmovcc (cc c) rax64 (xr .rdx)))
      st fr .rax d
  | .addChk d a b => do
      ld fr a .rax; ld fr b .rcx
      ins (i64 (.add (xr .rax) (or_ .rcx)))
      ins (i64 (.jcc .c (labelOf fr.fn "ovf")))
      st fr .rax d
  | .subSat d a b => do
      ld fr a .rax; ld fr b .rcx
      ins (i64 (.sub (xr .rax) (or_ .rcx)))
      movl .rdx 0
      ins (i64 (.cmovcc .c rax64 (xr .rdx)))
      st fr .rax d
  | .la d s => do ins (i64 (.lea rax64 (ripSym s))); st fr .rax d
  | .getTp d => do movFs .rax Tcb.self; st fr .rax d
  | .load _ w d a => do
      ld fr (.reg a.base) .rcx
      let m := mem .rcx a.disp
      match w with
      | .w64 => ins (i64 (.mov (xr .rax) (om m)))
      | .w32 => ins (i32 (.mov (xr .rax) (om m)))
      | .w16 => do
          ins (i16 (.mov (xr .rax) (om m)))
          ins (i32 (.movzx (xr .rax) (xr (w := .W16) .rax)))
      | .w8 => do
          ins (i8 (.mov (xr .rax) (om m)))
          ins (i32 (.movzx (xr .rax) (xr (w := .W8) .rax)))
      st fr .rax d
  | .store _ w a v => do
      ld fr (.reg a.base) .rcx
      ld fr v .rax
      let m := mem .rcx a.disp
      match w with
      | .w64 => ins (i64 (.mov (xm m) (or_ .rax)))
      | .w32 => ins (i32 (.mov (xm m) (or_ .rax)))
      | .w16 => ins (i16 (.mov (xm m) (or_ .rax)))
      | .w8 => ins (i8 (.mov (xm m) (or_ .rax)))
  | .rmw op d a v => do
      ld fr (.reg a.base) .rcx
      ld fr v .rax
      let m := mem .rcx a.disp
      match op with
      | .xchg => ins (i64 (.xchg rax64 (xm m)))
      | .add => ins (i64 (.xadd true (xm m) rax64))
      st fr .rax d
  | .fence f =>
      match f with
      | .full => ins (i64 .mfence)
      | .ld => item (.comment "fence ld: no code under TSO")
      | .st => item (.comment "fence st: no code under TSO")
  | .call ds f args => do
      if ds.length > retRegs.length then throw s!"{fr.fn}: call of {f} with {ds.length} results"
      callArgs fr args s!"call of {f}"
      callSym f
      safepoint fr sm
      for (d, r) in ds.zip retRegs do st fr r d
  | .syscall d nr args l => do
      loadArgs fr sysRegs args "syscall"
      movl .rax (sysNr nr)
      if let some l := l then lbl l
      sysc
      st fr .rax d
  | .clone d stack tls entry arg => do
      let parent ← freshL fr.fn
      ld fr arg .r12
      ld fr stack .rsi
      ld fr tls .r8
      movl .rdi cloneFlags
      zero32 .rdx
      zero32 .r10
      movl .rax nrClone
      sysc
      ins (i64 (.test (xr .rax) (or_ .rax)))
      ins (i64 (.jcc .nz parent))
      -- the child: on its own stack, with %fs = tls
      zero32 .rbp
      movRR .rdi .r12
      callSym entry
      ud2
      lbl parent
      st fr .rax d
  | .slotAddr d s => do ins (i64 (.lea rax64 (← fr.slot s))); st fr .rax d
  | .site s args => do
      loadArgs fr argRegs args s!"site {s}"
      lbl s
      ins (i64 (.nop 1))
  | .comment s => item (.comment s)

def epilogue : E Unit := do
  movRR .rsp .rbp
  ins (i64 (.pop (xr .rbp)))

def emitTerm (fr : Frame) : Term → E Unit
  | .ret vs => do
      loadArgs fr retRegs vs "ret"
      epilogue
      ins (i64 .ret)
  | .jmp l => jmpTo (labelOf fr.fn l)
  | .br c a b t f => do
      cmpAB fr a b
      ins (i64 (.jcc (cc c) (labelOf fr.fn t)))
      jmpTo (labelOf fr.fn f)
  | .tail f args => do
      -- Stack arguments overwrite this function's own incoming area (its
      -- parameters were copied to their slots in the prologue), which
      -- `StackMap.argAreas` sized for every tail call of its component.
      let k := argRegs.length
      if StackMap.stackWords k args.length > fr.inArea then
        throw s!"{fr.fn}: tail call of {f} with {args.length} arguments (argument area of {fr.inArea} words)"
      for (a, j) in (args.drop k).zipIdx do
        ld fr a .rax
        ins (i64 (.mov (xm (mem .rbp (inArgOff j))) (or_ .rax)))
      loadArgs fr argRegs (args.take k) s!"tail call of {f}"
      epilogue
      jmpTo f
  | .switchTo stack tls f arg => do
      ld fr tls .rsi
      movl .rdi archSetFs
      movl .rax nrArchPrctl
      sysc
      ld fr stack .rax
      ld fr arg .rdi
      movRR .rsp .rax
      zero32 .rbp
      callSym f
      ud2
  | .unreachable => ud2

def emitFunc (abortFn : Sym) (growth : Option Growth) (areas : List (Sym × Nat)) (f : Func) :
    E Unit := do
  let fr := { frameOf areas f with maps := growth.isSome }
  if f.params.length > maxArgs then throw s!"{f.name}: {f.params.length} parameters"
  item .blank
  dir s!".globl {f.name}"
  dir s!".type {f.name}, @function"
  lbl f.name
  ins (i64 (.push (or_ .rbp)))
  movRR .rbp .rsp
  if f.checkStack then
    if growth.isSome then lbl (labelOf f.name "chk")
    ins (i64 (.lea rax64 (mem .rsp (-(fr.size : Int)))))
    movFs .r11 Tcb.stackLimit
    ins (i64 (.cmp (xr .rax) (or_ .r11)))
    ins (i64 (.jcc .c (labelOf f.name "stk")))
  if fr.size > 0 then ins (i64 (.sub (xr .rsp) (oi fr.size)))
  for (p, r) in f.params.zip argRegs do st fr r p
  for (p, j) in (f.params.drop argRegs.length).zipIdx do
    ins (i64 (.mov (xr .rax) (om (mem .rbp (inArgOff j)))))
    st fr .rax p
  for (b, ms) in f.blocks.zip (StackMap.callMaps f) do
    lbl (labelOf f.name b.label)
    for (i, sm) in b.insts.zip ms do emitInst fr sm i
    emitTerm fr b.term
  -- the abort edges
  if f.blocks.any (·.insts.any fun | .addChk .. => true | _ => false) then
    lbl (labelOf f.name "ovf")
    movl .rdi AbortKind.overflow.code
    callSym abortFn
    ud2
  if f.checkStack then
    lbl (labelOf f.name "stk")
    match growth with
    | none =>
        movl .rdi AbortKind.stack.code
        callSym abortFn
        ud2
    | some _ =>
        -- The grow stub: save the argument registers at -8(%rbp) … -48(%rbp);
        -- stack parameters stay in the caller's outgoing area, `inArgOff`.
        for r in argRegs do ins (i64 (.push (or_ r)))
        movl .rdi fr.size
        callSym StackMap.morestackSym
        let l ← freshL f.name
        lbl l
        let e := StackMap.checkMap f
        let saveOff (r : IR.Reg) : Int := match f.params.idxOf? r with
          | some i => if i < argRegs.length then -(8 * ((i : Int) + 1))
                      else inArgOff (i - argRegs.length)
          | none => 0
        recordMap l (e.stack.map saveOff) (e.heap.map saveOff)
        for r in argRegs.reverse do ins (i64 (.pop (xr r)))
        jmpTo (labelOf f.name "chk")
  dir s!".size {f.name}, .-{f.name}"

/-- `l` in pieces of at most 16. -/
def chunks16 {α : Type} (l : List α) : List (List α) :=
  (List.range ((l.length + 15) / 16)).map fun i => (l.drop (16 * i)).take 16

def emitData (d : Data) : E Unit := do
  match d.init with
  | .zero n => do
      dir ".bss"
      dir s!".balign {d.align}"
      dir s!".type {d.name}, @object"
      lbl d.name
      dir s!".zero {max n 1}"
      dir s!".size {d.name}, {max n 1}"
  | .bytes bs => do
      dir ".data"
      dir s!".balign {d.align}"
      lbl d.name
      if bs.isEmpty then dir ".zero 1"
      for chunk in chunks16 bs do
        dir (".byte " ++ ", ".intercalate (chunk.map fun b => toString b.toNat))

/-- The trampoline between a grow stub and `Growth.grow` (the protocol is in
`Scc.IR.StackMap`): `%rdi` = the frame size that did not fit. -/
def emitMorestack (g : Growth) : E Unit := do
  item .blank
  dir s!".type {StackMap.morestackSym}, @function"
  lbl StackMap.morestackSym
  ins (i64 (.push (or_ .rbp)))
  movRR .rbp .rsp
  movRR .rsi .rdi
  movRR .rdi .rbp
  callSym g.grow
  -- (%rax, %rdx, %rcx) = (delta, old base, old size); move onto the new range.
  ins (i64 (.add (xr .rbp) (or_ .rax)))
  movRR .rsp .rbp
  movRR .rdi .rdx
  movRR .rsi .rcx
  callSym g.release
  ins (i64 (.pop (xr .rbp)))
  ins (i64 .ret)
  dir s!".size {StackMap.morestackSym}, .-{StackMap.morestackSym}"

/-- The stack-map table (format in `Scc.IR.StackMap`). -/
def emitMaps : E Unit := do
  let ms := (← get).maps.reverse
  dir ".section .rodata"
  dir ".balign 8"
  lbl StackMap.tableSym
  dir s!".quad {ms.length}"
  let mut first := 0
  for (l, st, hp) in ms do
    dir s!".quad {l}, {st.length}, {hp.length}, {first}"
    first := first + st.length + hp.length
  for (_, st, hp) in ms do
    for o in st ++ hp do dir s!".quad {o}"

/-- The items of a program's assembly file, and the safepoints recorded
(label, stack offsets, heap offsets, in emission order). -/
def emitItemsMaps (p : IR.Program) : Except String (List Item × List (String × List Int × List Int)) := do
  StackMap.check p
  let areas := StackMap.argAreas p argRegs.length
  -- Entered with no caller's outgoing area (`_start`, `clone`, `switchTo`):
  -- such functions must need no argument area.
  for e in [p.start] ++ p.funcs.flatMap (fun f => f.blocks.flatMap fun b =>
      (b.insts.filterMap fun | .clone _ _ _ g _ => some g | _ => none) ++
      (match b.term with | .switchTo _ _ g _ => [g] | _ => [])) do
    if StackMap.callWords areas argRegs.length e 0 > 0 then
      throw s!"{e}: entered without a caller but has a stack argument area"
  let body : E Unit := do
    item (.comment "Generated by scc (x86-64, AT&T syntax, Linux, no libc).")
    dir ".text"
    dir ".globl _start"
    dir ".type _start, @function"
    lbl "_start"
    zero32 .rbp
    ins (i64 (.and (xr .rsp) (oi (-16))))
    callSym p.start
    ud2
    for f in p.funcs do emitFunc p.abortFn p.growth areas f
    if let some g := p.growth then emitMorestack g
    item .blank
    -- `.data` and `.bss` start 16-aligned (`Data.Secs.ofProgram`).
    dir ".data"
    dir ".balign 16"
    dir ".bss"
    dir ".balign 16"
    for d in p.data do emitData d
    if p.growth.isSome then emitMaps
    item .blank
    dir ".section .note.GNU-stack,\"\",@progbits"
  let ((), s) ← body.run {}
  pure (s.out.reverse, s.maps.reverse)

/-- The items of a program's assembly file. -/
def emitItems (p : IR.Program) : Except String (List Item) :=
  (·.1) <$> emitItemsMaps p

/-- The data sections of a program's assembly file as data images
(`Scc.Emit.Data`): what `emitData` and `emitMaps` write. -/
def dataSecs (p : IR.Program) : Except String Data.Secs := do
  let (_, ms) ← emitItemsMaps p
  pure (Data.Secs.ofProgram p.data (if p.growth.isSome then some ms else none))

/-- The assembly text of a program. -/
def emit (p : IR.Program) : Except String String := do
  render (← emitItems p)

end Scc.Emit.X64
