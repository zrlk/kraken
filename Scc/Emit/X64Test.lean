/-
Re-parsing the x64 output of `scc` with Kraken's x64 parser.

Certificates of later stages re-parse the emitted text with Kraken's own
parser, so every emitted instruction line must be representable in Kraken's
x64 syntax (`Kraken/X64/Syntax.lean`). The x64 emitter (`Scc/Emit/X64.lean`)
builds Kraken `Directive`s for every instruction; raw instruction lines
(`Item.raw`, `Scc/Emit/X64Print.lean`) are no longer needed, and this file
checks that none is emitted.

* **Round trip.** For every program below, every item the emitter produces
  that is not a raw line reads back as itself: a Kraken directive `d` prints
  to a line that Kraken's parser reads as `[d]`, and an assembler directive
  line, comment or blank line reads back as nothing (`Item.roundTrips`). The
  whole file without its raw lines re-parses to the emitter's Kraken program
  (`roundTripsWithoutRaw`).
* **Raw lines.** The summaries list, per program, the number of raw lines
  (none) and, if there were any, each mnemonic with the parser's message.
* **Programs.** The `Scc/Test/*.w` programs that `scc` accepts are compiled
  for x64 (`compileW`), and so are the IR test programs `helloIR` and
  `allOpsIR` (every IR instruction and terminator and every branch of the
  emitter).
* **Lowerability.** Each program, re-parsed as a certificate does
  (`Scc.Cert.X64.reparse`: directive lines dropped), satisfies
  `ProgramWCLowerable` (`Scc/Emit/X64Lowerable.lean`), by `decide +kernel`.
* **Meaning.** `stepsToDone` runs a directive once under Kraken's x64
  semantics, translated to events by the Promising adapter, and checks that it
  does not fault; it holds for every Kraken directive of every program except
  `syscall` and `ud2`, which halt by design (`Kraken/SYSCALL.md`: a pending
  system call and a trap, both `Effects.unimplemented`); `haltsAsDesigned`
  checks that they fault with exactly those messages.

## Gap table

Every instruction form `Scc/Emit/X64.lean` can emit (`allOpsIR` reaches each
of them), by IR construct. "Item" is how the emitter produces it: a Kraken
directive (which round-trips) or a raw line (which Kraken's parser rejects).
"Sem." is whether `Kraken/X64/Semantics.lean` gives it a meaning that
`Kraken/Promising/X64.lean` translates without a fault (`stepsToDone`; the
only undefined values these forms produce are flag bits, which the adapter
turns into a two-way choice). "Class" is what is missing: (b) Kraken needs
the form, (c) out of scope for the fragment.

| Emitted form (IR construct) | Item | Sem. | Class |
|---|---|---|---|
| `movq d(%rbp), %r`, `movq %r, d(%rbp)` (frame slots) | Kraken | yes | – |
| `movq $i, %r`, `$i` a sign-extended 32-bit value | Kraken | yes | – |
| `movabsq $n, %r` (other 64-bit constants) | Kraken (`mov` at `W64`) | yes | – |
| `addq`/`subq`/`andq`/`orq`/`xorq`/`imulq %rcx, %rax`, `mulq %rcx` (`bin`) | Kraken | yes | – |
| `shlq`/`shrq`/`sarq %cl, %rax` (`bin` shifts) | Kraken | yes | – |
| `testq %rcx, %rcx`, `je` (`udiv`/`urem`/`sdiv`/`srem` guards) | Kraken | yes | – |
| `xorl %edx, %edx; divq %rcx` (`udiv`/`urem`) | Kraken | yes (`%rcx ≠ 0`; #DE on 0, guarded) | – |
| `cqto; idivq %rcx` (`sdiv`/`srem`) | Kraken | yes (`%rcx ∉ {0, -1}`, guarded) | – |
| `negq`/`notq %rax` (`un`) | Kraken | yes | – |
| `tzcntq %rax, %rax` (`ctz`) | Kraken | yes | – |
| `popcntq %rax, %rax` (`popcnt`) | Kraken | yes | – |
| `movsbq %al, %rax`, `movswq %ax, %rax`, `movslq %eax, %rax`, `movzbl %al, %eax`, `movzwl %ax, %eax`, `movl %eax, %eax` (`ext`) | Kraken | yes | – |
| `cmpq %rcx, %rax; set<cc> %al; movzbl %al, %eax` (`setc`) | Kraken | yes | – |
| `cmov<cc> %rdx, %rax` (`select`), `cmovb %rdx, %rax` (`subSat`) | Kraken | yes | – |
| `addq %rcx, %rax; jb .L<f>.ovf` (`addChk`) | Kraken | yes | – |
| `leaq sym(%rip), %rax` (`la`) | Kraken | yes | – |
| `movq %fs:0, %rax` (`getTp`), `movq %fs:8, %r11; cmpq %r11, %rax` (stack check) | Kraken (`movfs`, `cmp`) | yes | – |
| `movq`/`movl d(%rcx), %r` (`load` 64/32), `movq`/`movl`/`movw`/`movb %r, d(%rcx)` (`store`) | Kraken | yes | – |
| `movw d(%rcx), %ax; movzwl %ax, %eax`, `movb d(%rcx), %al; movzbl %al, %eax` (`load` 16/8) | Kraken | yes | – |
| `xchgq %rax, d(%rcx)` (`rmw xchg`) | Kraken | yes | – |
| `lock xaddq %rax, d(%rcx)` (`rmw add`) | Kraken | yes | – |
| `mfence` (`fence full`) | Kraken | yes | – |
| `# fence ld: …` (`fence ld`/`st`), `# …` (`comment`) | comment | – | – |
| `call f`, `jmp f`, `ret`, `pushq`/`popq %r`, `movq %rbp, %rsp` | Kraken | yes | – |
| `syscall` (`syscall`, `clone`, `switchTo`) | Kraken | halt (pending system call) | – |
| `ud2` (`unreachable`, after `clone`'s child call, `switchTo`, the abort edges, `_start`) | Kraken | halt (trap) | – |
| `leaq -F(%rsp), %rax`, `subq $F, %rsp`, `andq $-16, %rsp`, `xorl %ebp, %ebp`, `xorl %r10d, %r10d`, `movl $n, %e..` | Kraken | yes | – |
| local labels `.L<f>.<block>:`, `.L<f>.x<n>:`, `.L<f>.ovf:`, `.L<f>.stk:`, `.L<f>.chk:`; symbol labels `f:` | Kraken | yes | – |
| `.text`, `.data`, `.bss`, `.globl`, `.type`, `.size`, `.section`, `.balign`, `.quad` (stack maps) | directive line | – | (c) |
| `.byte …`, `.zero n` (data contents) | directive line | – | (c) here; a certificate that reads initial data needs them (Kraken's parser reads `.byte`, but `stripDirectives` removes it) |

Notes on the table:

* The printer writes one spelling per Kraken form (`Scc/Emit/X64Print.lean`):
  the condition codes `e`/`ne`/`b`/`ae`/… (so `je`, `jne`, `jb`, never `jz`,
  `jnz`, `jc`) and unsuffixed `cmov<cc>` (Kraken's parser reads the condition
  code from everything after `cmov`, so a width suffix makes it an unknown
  condition code; accepting the suffix would be a one-line parser change).
* A narrow load followed by a register `movz*` makes the same single access
  as a `movz*` with a memory source. `Operation.movzx` already takes a
  register-or-memory source and its semantics reads memory; only the parser
  (`movzbl`/`movzwl`/… take registers) refuses the memory form.
* `tzcnt` needs BMI1 (Kraken assumes it); on a processor without BMI1 it
  executes as `bsf`, which leaves the destination unchanged on a zero source.
* `popcntSwar` is a 19-instruction replacement for `popcnt` from
  instructions Kraken had before `popcnt`; kept as a test of those forms.
* `div`/`idiv` fault on a zero divisor and on `-2^63 / -1`; the emitter
  branches around both, so a model of them may treat those cases as a fault.
* Kraken's `%fs:` operand is `mov` only (`Operation.movfs`), so the stack
  check loads the limit into `%r11` and compares registers; `%r11` is free
  there (not an argument register, and not used elsewhere by the emitter).
* Kraken's parser now reads the `movz*` memory source and the suffixed
  `cmov`; the emitter does not use them yet.

## Lowerability

Kraken has no x64 counterpart of AArch64's `Program.WCLowerable`
(`Kraken/Promising/Lower/Lowerable.lean`, whose docstring explains why: no x64
form needs clauses 1–5, and clause 6, no sub-word stores, is not encoded for
x64). `Scc/Emit/X64Lowerable.lean` states the x64 conventions (every memory
RMW locked, no `movnti`) as `ProgramWCLowerable`, proved below of every
program. The emitter's 8- and 16-bit stores (`movb`/`movw %r, d(%rcx)`)
rely on the obligation `SubWordOwned` named there, the same ownership
invariant as the AArch64 emitter's lane stores (a sub-word store goes only to
a cell no other thread writes).
-/
import Scc.Emit.X64
import Scc.Cert.X64
import Scc.Frontend
import Scc.Lower.Program
import Kraken.X64.Parser
import Kraken.Promising.X64
import Scc.Test.Src

namespace Scc.Emit.X64.Test

open Scc.IR
open Kraken.X64.Parser (parse stripDirectives)

/-! ## The printer -/

/-- Print each directive, read the text back with Kraken's parser, and
compare. -/
def roundTrips (ds : List Directive) : Bool := ds.all fun d => (Item.d d).roundTrips

-- A form outside the printer's range does not round-trip, nor does a raw line.
#guard !roundTrips [i64 (.nop 2)]
#guard !(Item.raw "divq %rcx").roundTrips
-- Directive lines, comments and blank lines read back as nothing.
#guard [Item.dir ".globl f", .dir ".quad .Lf.x0, 1, 0, 0", .comment "a comment: with a colon",
  .blank].all Item.roundTrips
-- An item that is not printable is refused.
#guard (render [.dir "f:"]).toOption.isNone && (render [.raw ".text"]).toOption.isNone &&
  (render [.d (i64 (.nop 2))]).toOption.isNone

/-- `syscall`, `ud2`, `%fs:` moves (the absolute load the emitter uses, and
the based and indexed store forms), division and `popcnt`. -/
def fsForms : List Directive :=
  [i64 .syscall, i64 .ud2,
   i64 (.movfs (xr .r11) (om { base := none, idx := none, disp := .int64 8 })),
   i64 (.movfs (xm (mem .rax 16)) (or_ .rdi)),
   i32 (.movfs (xm { base := some (.reg .rbx), idx := some ⟨.rcx, .W32⟩, disp := .int64 8 })
     (oi 7)),
   i64 (.div (xr .rcx)), i64 .cqo, i64 (.idiv (xr .rcx)), i32 .cqo,
   i64 (.popcnt (lw .rax .W64) (xr .rax))]

#guard roundTrips fsForms

-- The printed text of a few forms.
/--
info: movq -8(%rbp), %rax
movq $-5, %rdi
movabsq $2147483648, %rax
movabsq $9223372036854775808, %rax
imulq %rcx, %rax
shlq %cl, %rax
leaq some_symbol(%rip), %rax
movq (%rcx), %rax
movb %al, 1(%rcx)
xchgq %rax, 16(%rcx)
lock xaddq %rax, 8(%rcx)
call callee
cmovb %rdx, %rax
tzcntq %rax, %rax
movzbl %al, %eax
je .Lf.x0
syscall
ud2
movq %fs:8, %r11
movq %rdi, %fs:16(%rax)
movl $7, %fs:8(%rbx,%rcx,4)
divq %rcx
cqto
idivq %rcx
cltd
popcntq %rax, %rax
-/
#guard_msgs in
#eval for d in [i64 (.mov (xr .rax) (om (mem .rbp (-8)))), i64 (.mov (xr .rdi) (oi (-5))),
    i64 (.mov (xr .rax) (oi (2 ^ 31))), i64 (.mov (xr .rax) (oi (-2 ^ 63))),
    i64 (.imul none (xr .rax) (or_ .rcx)), i64 (.shl (xr .rax) .cl),
    i64 (.lea (lw .rax .W64) (ripSym "some_symbol")), i64 (.mov (xr .rax) (om (mem .rcx))),
    i8 (.mov (xm (mem .rcx 1)) (or_ .rax)), i64 (.xchg (lw .rax .W64) (xm (mem .rcx 16))),
    i64 (.xadd true (xm (mem .rcx 8)) (lw .rax .W64)), i64 (.call (rel "callee")),
    i64 (.cmovcc .c (lw .rax .W64) (xr .rdx)), i64 (.tzcnt (lw .rax .W64) (xr .rax)),
    i32 (.movzx (xr .rax) (xr (w := .W8) .rax)), i64 (.jcc .z ".Lf.x0")] ++ fsForms do
  IO.println ((ppDirective d).getD "?")

/-! ## Meaning of the directives -/

section
open Kraken.Promising.X64 (showRun toEv)

/-- Labels resolve to a fixed address in the semantic check below. -/
local instance : Labels := ⟨fun _ => 0x1000⟩

/-- The last line of one execution of `d` from state `s` at address `0x2000`
(see `stepsToDone`). -/
def lastStep (s : MachineData) (d : Directive) : Option String :=
  let eff := d.interp s ⟨0x2000, 0x2001⟩ (fun s => .done (s, 0x2001)) (fun pc s => .done (s, pc))
  (showRun [] (toEv {} eff)).getLast?

/-- One execution of `d` under Kraken's x64 semantics (`Directive.interp`),
translated to events by the Promising adapter (`toEv`), from the zero state
at address `0x2000`: every load reads 0, every store succeeds, every choice
takes its first branch. `true` when it ends in `done` (falls through or
jumps), `false` on a fault (`unimplemented`, an undefined register value, an
unaligned access, …). -/
def stepsToDone (d : Directive) : Bool := lastStep {} d == some "done"

/-- One execution of `d` from `s` ends in a fault whose message contains `m`. -/
def faultsWith (s : MachineData) (m : String) (d : Directive) : Bool :=
  match lastStep s d with
  | some l => l != "done" && (l.splitOn m).length > 1
  | none => false

/-- `syscall` and `ud2` halt by design (`Kraken/SYSCALL.md`): one execution
ends in a fault whose message is `pendingSyscallMsg` or `ud2Msg`. -/
def haltsAsDesigned (d : Directive) : Bool :=
  let msg := match d with
    | .instr (.regular _ _ .syscall) => some pendingSyscallMsg
    | .instr (.regular _ _ .ud2) => some ud2Msg
    | _ => none
  match msg with
  | none => false
  | some m => faultsWith {} m d

/-- The meaning check of one directive: `stepsToDone`; for `syscall` and
`ud2` the designed halt; for `div`/`idiv`, whose divisor the emitter keeps in
`%rcx` and guards against zero (and `idiv` against `-1`), a step to `done`
with `%rcx = 1` and the divide error (#DE, `divErrorMsg`) with `%rcx = 0`. -/
def meaningOk (d : Directive) : Bool :=
  match d with
  | .instr (.regular _ _ .syscall) | .instr (.regular _ _ .ud2) => haltsAsDesigned d
  | .instr (.regular _ _ (.div _)) | .instr (.regular _ _ (.idiv _)) =>
      lastStep { regs := { rcx := 1 } } d == some "done" && faultsWith {} divErrorMsg d
  | _ => stepsToDone d

end

#guard haltsAsDesigned (i64 .syscall) && haltsAsDesigned (i64 .ud2)
#guard meaningOk (i64 (.div (xr .rcx))) && meaningOk (i64 (.idiv (xr .rcx))) &&
  meaningOk (i64 .cqo) && meaningOk (i64 (.popcnt (lw .rax .W64) (xr .rax)))
#guard !stepsToDone (i64 .syscall) && !haltsAsDesigned (i64 .ret)

-- A data cell has no meaning as code: the check can fail.
#guard !stepsToDone (.byteArray ⟨#[1]⟩)

/-- `popcntq %rax, %rax` from instructions Kraken has (the classic SWAR
population count; clobbers `%rcx` and `%rdx`, which the emitter's `un`
lowering leaves free). -/
def popcntSwar : List Directive :=
  [i64 (.mov (xr .rcx) (or_ .rax)), i64 (.shr (xr .rcx) (.imm8 (.int64 1))),
   i64 (.mov (xr .rdx) (oi 6148914691236517205)), i64 (.and (xr .rcx) (or_ .rdx)),
   i64 (.sub (xr .rax) (or_ .rcx)), i64 (.mov (xr .rdx) (oi 3689348814741910323)),
   i64 (.mov (xr .rcx) (or_ .rax)), i64 (.and (xr .rax) (or_ .rdx)),
   i64 (.shr (xr .rcx) (.imm8 (.int64 2))), i64 (.and (xr .rcx) (or_ .rdx)),
   i64 (.add (xr .rax) (or_ .rcx)), i64 (.mov (xr .rcx) (or_ .rax)),
   i64 (.shr (xr .rcx) (.imm8 (.int64 4))), i64 (.add (xr .rax) (or_ .rcx)),
   i64 (.mov (xr .rdx) (oi 1085102592571150095)), i64 (.and (xr .rax) (or_ .rdx)),
   i64 (.mov (xr .rdx) (oi 72340172838076673)), i64 (.imul none (xr .rax) (or_ .rdx)),
   i64 (.shr (xr .rax) (.imm8 (.int64 56)))]

#guard roundTrips popcntSwar && popcntSwar.all stepsToDone

/-! ## Summaries of emitted programs -/

/-- The mnemonic of a line (its first word), or the whole line. -/
def mnemonic (l : String) : String :=
  (l.trimAscii.toString.takeWhile (fun c => c != ' ' && c != '\t')).toString

/-- Counts of `xs`, in order of first occurrence. -/
def tally (xs : List String) : List (String × Nat) :=
  xs.foldl (init := []) fun acc x =>
    if acc.any (·.1 == x) then acc.map fun (y, n) => if y == x then (y, n + 1) else (y, n)
    else acc ++ [(x, 1)]

/-- The parser's message on a raw line, or `parses` if it reads it. -/
def rawVerdict (l : String) : String :=
  match parse l with
  | .error msg => (msg.dropPrefix "line 1: ").toString
  | .ok _ => "parses"

/-- A summary of an emitted item list: the number of items of each kind,
the round trip (`ok`, or the first item that fails), the meaning check, and
each raw mnemonic with the parser's message and its number of lines. -/
def summary (r : Except String (List Item)) : String := Id.run do
  let items ← match r with
    | .ok items => pure items
    | .error e => return s!"error: {e}"
  let count (p : Item → Bool) := (items.filter p).length
  let ni := count fun | .d (.instr _) => true | _ => false
  let nl := count fun | .d (.label _) => true | _ => false
  let nd := count fun | .dir _ => true | _ => false
  let nc := count fun | .comment _ => true | _ => false
  let nb := count fun | .blank => true | _ => false
  let raws := rawLines items
  let mut out := s!"items {items.length}: instr {ni}, label {nl}, directive {nd}, comment {nc}, blank {nb}, raw {raws.length}"
  let bad := items.find? fun it => match it with | .raw _ => false | _ => !it.roundTrips
  out := out ++ "\n  round trip: " ++ match bad with
    | none => if roundTripsWithoutRaw items then "ok" else "whole file fails"
    | some it => s!"fails on {(it.line?).getD "?"}"
  let sem := (directives items).filter (!meaningOk ·)
  out := out ++ "\n  meaning: " ++ match sem with
    | [] => "ok"
    | d :: _ => s!"fails on {(ppDirective d).getD "?"}"
  for (k, n) in tally (raws.map fun l => mnemonic l ++ " (" ++ rawVerdict l ++ ")") do
    out := out ++ s!"\n  raw ×{n}: {k}"
  return out

/-! ## The emitted programs -/

/-- Compile a WeakCore source text for x64: frontend, lowering, x64 emitter
items. -/
def compileW (src : String) : Except String (List Item) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let ir ← Lower.lowerProgram { arch := .x64 } c
  emitItems ir

def arithItems := compileW (w_src% "Scc/Test/arith.w")
def helloItems := compileW (w_src% "Scc/Test/hello.w")
def handoffItems := compileW (w_src% "Scc/Test/handoff.w")
def overflowItems := compileW (w_src% "Scc/Test/overflow.w")
def tailloopItems := compileW (w_src% "Scc/Test/tailloop.w")

/-! ### IR test programs -/

def r (s : String) : IR.Operand := .reg s
def k (n : Nat) : IR.Operand := .imm (UInt64.ofNat n)
def u64 (n : Int) : IR.Operand := .imm (UInt64.ofInt n)

/-- Hello world in the IR: the start routine builds the main thread's TCB and
moves onto its own stack, `main` writes the message once and exits, `abort`
writes its message to fd 2 and exits with 101. -/
def helloIR : IR.Program where
  start := "scc_start"
  abortFn := "scc_abort"
  data := [
    { name := "scc_msg", align := 1, init := .bytes "Hello, world\n".toUTF8.toList },
    { name := "scc_abort_msg", align := 1, init := .bytes "scc abort\n".toUTF8.toList },
    { name := "scc_tcb0", init := .zero Tcb.size },
    { name := "scc_stack0", align := 16, init := .zero 16384 }]
  funcs := [
    { name := "scc_start", params := [], checkStack := false, blocks := [
      { label := "entry", insts := [
          .la "t" "scc_tcb0", .store .plain .w64 ⟨"t", Tcb.self⟩ (r "t"),
          .la "s" "scc_stack0", .bin .add "lim" (r "s") (k Tcb.headroom),
          .store .plain .w64 ⟨"t", Tcb.stackLimit⟩ (r "lim"),
          .bin .add "top" (r "s") (k 16384)],
        term := .switchTo (r "top") (r "t") "main" (k 0) }] },
    { name := "main", params := ["arg"], blocks := [
      { label := "entry", insts := [
          .la "p" "scc_msg",
          .syscall "n" .write [k 1, r "p", k 13]],
        term := .br .slt (r "n") (k 0) "fail" "done" },
      { label := "fail", insts := [.call [] "scc_abort" [k AbortKind.write.code]],
        term := .unreachable },
      { label := "done", insts := [.syscall "z" .exitGroup [k 0]], term := .unreachable }] },
    { name := "scc_abort", params := ["code"], checkStack := false, blocks := [
      { label := "entry", insts := [
          .la "p" "scc_abort_msg",
          .syscall "n" .write [k 2, r "p", k 10],
          .syscall "z" .exitGroup [k abortExitCode]],
        term := .unreachable }] }]

/-- Every IR instruction and terminator, reaching every branch of the x64
emitter: immediates on both sides of the sign-extended 32-bit range (`movq`
or `movabsq`), every operation, condition, width and order, displacements
zero (no displacement printed), positive and negative, calls and system calls
with six arguments and six results, functions with and without the stack
check and with an empty frame, and data items that are empty, zero-filled or
longer than one `.byte` line. -/
def allOpsIR : IR.Program where
  start := "t_start"
  abortFn := "t_abort"
  data := [{ name := "t_data", init := .zero 64 }, { name := "t_none", init := .zero 0 },
    { name := "t_bytes", init := .bytes [1, 2, 3] }, { name := "t_empty", align := 1, init := .bytes [] },
    { name := "t_long", align := 16, init := .bytes ((List.range 40).map UInt8.ofNat) }]
  funcs := [
    { name := "t_start", params := [], checkStack := false, blocks := [
      { label := "entry", insts := [.la "t" "t_data", .la "s" "t_data"],
        term := .switchTo (r "s") (r "t") "t_ops" (k 7) }] },
    { name := "t_ops", params := ["a", "b", "c", "d", "e", "f"], blocks := [
      { label := "entry", insts := [
          .comment "immediates",
          .mov "x" (r "a"), .mov "y" (k 0xffffffffffffffff),
          .mov "x" (k (2 ^ 31 - 1)), .mov "x" (k (2 ^ 31)), .mov "x" (u64 (-2 ^ 31)),
          .mov "x" (u64 (-2 ^ 31 - 1)), .mov "x" (k 0x123456789abcdef0), .mov "x" (u64 (-5)),
          .comment "arithmetic",
          .bin .add "z" (r "x") (r "y"), .bin .sub "z" (r "x") (k 5),
          .bin .mul "z" (r "x") (r "y"), .bin .umulh "z" (r "x") (r "y"),
          .bin .udiv "z" (r "x") (r "y"), .bin .sdiv "z" (r "x") (r "y"),
          .bin .urem "z" (r "x") (r "y"), .bin .srem "z" (r "x") (r "y"),
          .bin .and "z" (r "x") (r "y"), .bin .or "z" (r "x") (r "y"),
          .bin .xor "z" (r "x") (r "y"), .bin .shl "z" (r "x") (k 3),
          .bin .lshr "z" (r "x") (k 3), .bin .ashr "z" (r "x") (k 3),
          .un .not "z" (r "x"), .un .neg "z" (r "x"), .un .ctz "z" (r "x"), .un .popcnt "z" (r "x"),
          .ext false .w8 "z" (r "x"), .ext false .w16 "z" (r "x"), .ext false .w32 "z" (r "x"),
          .ext true .w8 "z" (r "x"), .ext true .w16 "z" (r "x"), .ext true .w32 "z" (r "x"),
          .ext true .w64 "z" (r "x"), .ext false .w64 "z" (r "x"),
          .setc .eq "z" (r "x") (r "y"), .setc .ne "z" (r "x") (r "y"),
          .setc .ult "z" (r "x") (r "y"), .setc .ule "z" (r "x") (r "y"),
          .setc .ugt "z" (r "x") (r "y"), .setc .uge "z" (r "x") (r "y"),
          .setc .slt "z" (r "x") (r "y"), .setc .sle "z" (r "x") (r "y"),
          .setc .sgt "z" (r "x") (r "y"), .setc .sge "z" (r "x") (r "y"),
          .select .eq "z" (r "x") (r "y") (r "a") (k 9), .select .ne "z" (r "x") (r "y") (r "a") (k 9),
          .select .ult "z" (r "x") (r "y") (r "a") (k 9), .select .ule "z" (r "x") (r "y") (r "a") (k 9),
          .select .ugt "z" (r "x") (r "y") (r "a") (k 9), .select .uge "z" (r "x") (r "y") (r "a") (k 9),
          .select .slt "z" (r "x") (r "y") (r "a") (k 9), .select .sle "z" (r "x") (r "y") (r "a") (k 9),
          .select .sgt "z" (r "x") (r "y") (r "a") (k 9), .select .sge "z" (r "x") (r "y") (r "a") (k 9),
          .addChk "z" (r "x") (r "y"), .subSat "z" (r "x") (r "y"),
          .comment "memory",
          .la "m" "t_data", .getTp "tp",
          .load .plain .w8 "z" ⟨"m", 1⟩, .load .plain .w16 "z" ⟨"m", 2⟩,
          .load .plain .w32 "z" ⟨"m", 4⟩, .load .plain .w64 "z" ⟨"m", 8⟩,
          .load .plain .w64 "z" ⟨"m", 0⟩, .load .plain .w64 "z" ⟨"m", -8⟩,
          .load .plain .w64 "z" ⟨"m", 100000⟩, .load .plain .w16 "z" ⟨"m", 0⟩,
          .load .acq .w8 "z" ⟨"m", 0⟩, .load .acq .w16 "z" ⟨"m", 2⟩,
          .load .acq .w32 "z" ⟨"m", 4⟩, .load .acq .w64 "z" ⟨"m", 8⟩,
          .store .plain .w8 ⟨"m", 1⟩ (r "x"), .store .plain .w16 ⟨"m", 2⟩ (r "x"),
          .store .plain .w32 ⟨"m", 4⟩ (r "x"), .store .plain .w64 ⟨"m", 8⟩ (k 0),
          .store .plain .w64 ⟨"m", 0⟩ (r "x"), .store .plain .w64 ⟨"m", -16⟩ (r "x"),
          .store .plain .w64 ⟨"m", 200000⟩ (k 0x123456789abcdef0),
          .store .rel .w8 ⟨"m", 1⟩ (r "x"), .store .rel .w16 ⟨"m", 2⟩ (r "x"),
          .store .rel .w32 ⟨"m", 4⟩ (r "x"), .store .rel .w64 ⟨"m", 8⟩ (r "x"),
          .rmw .xchg "z" ⟨"m", 0⟩ (r "x"), .rmw .add "z" ⟨"m", 8⟩ (k 1),
          .rmw .xchg "z" ⟨"m", 16⟩ (k 1), .rmw .add "z" ⟨"m", 0⟩ (r "x"),
          .fence .ld, .fence .st, .fence .full,
          .comment "calls",
          .call ["p", "q", "g", "h", "i", "j"] "t_callee" [r "a", r "b", r "c", r "d", r "e", k 6],
          .call [] "t_callee" [],
          .syscall "z" .futex [r "m", k 0, k 1, k 0, k 0, k 0],
          .syscall "z" .rtSigaction [k 13, r "m", k 0, k 8],
          .syscall "z" .write [k 1, r "m", k 1],
          .clone "tid" (r "s") (r "tp") "t_thread" (r "m")],
        term := .br .uge (r "x") (r "y") "left" "right" },
      { label := "left", insts := [], term := .jmp "out" },
      { label := "right", insts := [], term := .tail "t_callee" [r "p", r "q"] },
      { label := "out", insts := [], term := .ret [r "p", r "q", k 3, r "g", r "h", r "i"] }] },
    { name := "t_callee", params := ["u", "v"], blocks := [
      { label := "entry", insts := [], term := .ret [r "v", r "u"] }] },
    { name := "t_leaf", params := [], checkStack := false, blocks := [
      { label := "entry", insts := [], term := .ret [] }] },
    { name := "t_thread", params := ["arg"], blocks := [
      { label := "entry", insts := [.syscall "z" .exit [k 0]], term := .unreachable }] },
    { name := "t_abort", params := ["code"], checkStack := false, blocks := [
      { label := "entry", insts := [.syscall "z" .exitGroup [k abortExitCode]],
        term := .unreachable }] }]

#guard (emitItems helloIR).toOption.isSome
#guard (emitItems allOpsIR).toOption.isSome

/-! ### Summaries

Per program: the items, the round trip of every item, the meaning of every
Kraken directive, and the raw lines (none). -/

/-- The expected summary under each header placement
(`ObjLayout.headerBeforeTrace`, `Scc/LAYOUT.md` §2): `false` adds the
header address computation to the runtime's allocators, so flipping the
default needs no edit here. -/
def byPlacement (before after : String) : String :=
  if ({} : Scc.ObjLayout).headerBeforeTrace then before else after

-- `Scc/Test/arith.w`
#guard summary arithItems == byPlacement
  "items 2130: instr 1729, label 215, directive 163, comment 1, blank 22, raw 0\n  round trip: ok\n  meaning: ok"
  "items 2138: instr 1737, label 215, directive 163, comment 1, blank 22, raw 0\n  round trip: ok\n  meaning: ok"

-- `Scc/Test/hello.w`
#guard summary helloItems == byPlacement
  "items 1782: instr 1349, label 188, directive 216, comment 3, blank 26, raw 0\n  round trip: ok\n  meaning: ok"
  "items 1790: instr 1357, label 188, directive 216, comment 3, blank 26, raw 0\n  round trip: ok\n  meaning: ok"

-- `Scc/Test/handoff.w`
#guard summary handoffItems == byPlacement
  "items 1683: instr 1265, label 181, directive 209, comment 3, blank 25, raw 0\n  round trip: ok\n  meaning: ok"
  "items 1691: instr 1273, label 181, directive 209, comment 3, blank 25, raw 0\n  round trip: ok\n  meaning: ok"

-- `Scc/Test/overflow.w`
#guard summary overflowItems == byPlacement
  "items 1428: instr 1090, label 152, directive 163, comment 1, blank 22, raw 0\n  round trip: ok\n  meaning: ok"
  "items 1436: instr 1098, label 152, directive 163, comment 1, blank 22, raw 0\n  round trip: ok\n  meaning: ok"

-- `Scc/Test/tailloop.w`
#guard summary tailloopItems == byPlacement
  "items 1494: instr 1142, label 160, directive 168, comment 1, blank 23, raw 0\n  round trip: ok\n  meaning: ok"
  "items 1502: instr 1150, label 160, directive 168, comment 1, blank 23, raw 0\n  round trip: ok\n  meaning: ok"

-- `helloIR`
/--
info: items 137: instr 84, label 14, directive 33, comment 1, blank 5, raw 0
  round trip: ok
  meaning: ok
-/
#guard_msgs in
#eval IO.println (summary (emitItems helloIR))

-- `allOpsIR` (one of its functions has a zero-byte frame: its `subq $0, %rsp` is counted)
/--
info: items 639: instr 540, label 37, directive 47, comment 7, blank 8, raw 0
  round trip: ok
  meaning: ok
-/
#guard_msgs in
#eval IO.println (summary (emitItems allOpsIR))

/-- The programs above. -/
def allItems : List (Except String (List Item)) :=
  [arithItems, helloItems, handoffItems, overflowItems, tailloopItems, emitItems helloIR,
   emitItems allOpsIR]

-- Every program is emitted; every item that is not a raw line round-trips, and so
-- does the whole file without its raw lines; every raw line is rejected by the
-- parser; every Kraken directive has a meaning.
#guard allItems.all fun
  | .ok items =>
    items.all (fun it => match it with | .raw _ => true | _ => it.roundTrips) &&
    roundTripsWithoutRaw items &&
    (rawLines items).all (fun l => (parse l).toOption.isNone) &&
    (directives items).all meaningOk
  | .error _ => false

-- The rendered text is the items, line by line.
#guard allItems.all fun
  | .ok items => (render items).toOption ==
      some (String.join (items.map fun it => (it.line?.getD "") ++ "\n"))
  | .error _ => false

-- No program has a raw line: every instruction is a Kraken directive.
#guard allItems.all fun
  | .ok items => (rawLines items).isEmpty
  | .error _ => false

/-- The runtime's site `s` (`Inst.site`) in an emitted program: the label
`s` is placed exactly once, on a `nop`, and the two lines before it load the
base into `%rdi` and the size into `%rsi`. -/
def siteOk (items : List Item) (s : String) : Bool :=
  let ls := (items.map fun it => it.line?.getD "").toArray
  match (List.range ls.size).filter (fun k => ls[k]! == s ++ ":") with
  | [k] => 2 ≤ k && ls[k + 1]? == some "\tnop" &&
      ls[k - 2]!.startsWith "\tmovq " && ls[k - 2]!.endsWith ", %rdi" &&
      ls[k - 1]!.startsWith "\tmovq " && ls[k - 1]!.endsWith ", %rsi"
  | _ => false

-- The take and release sites of the stack pool, in every compiled program.
#guard [arithItems, helloItems, handoffItems, overflowItems, tailloopItems].all fun
  | .ok items => siteOk items Lower.Names.takeSite && siteOk items Lower.Names.releaseSite
  | .error _ => false
-- `nop` round-trips; the IR programs without the runtime have no site.
#guard roundTrips [i64 (.nop 1)]
#guard [emitItems helloIR, emitItems allOpsIR].all fun
  | .ok items => !(siteOk items Lower.Names.takeSite)
  | .error _ => false

/-! ## Lowerability of the emitted programs (as re-parsed) -/

open Lean Elab Term Meta in
/-- `x64_reparsed% p`: emit the IR program `p`, print it, re-parse the text
as a certificate does (`Scc.Cert.X64.reparse`), and return the resulting
`Program` as a literal. -/
elab "x64_reparsed% " t:term : term => do
  let e ← elabTermEnsuringType t (mkConst ``Scc.IR.Program)
  let e ← instantiateMVars e
  let p ← unsafe evalExpr Scc.IR.Program (mkConst ``Scc.IR.Program) e
  match emit p with
  | .error msg => throwError msg
  | .ok text =>
    match Cert.X64.reparse text with
    | .error msg => throwError "re-parse failed: {msg}"
    | .ok prog => return toExpr prog

open Lean Elab Term Meta in
/-- `x64_reparsed_w% "path.w"`: compile the WeakCore file (path relative to the
package root) for x64, re-parse the emitted text as a certificate does, and
return the resulting `Program` as a literal. -/
elab "x64_reparsed_w% " path:str : term => do
  let src ← IO.FS.readFile path.getString
  match Cert.X64.compile { arch := .x64 } src with
  | .error msg => throwError msg
  | .ok text =>
    match Cert.X64.reparse text with
    | .error msg => throwError "re-parse failed: {msg}"
    | .ok prog => return toExpr prog

def arithX64 : _root_.Program := x64_reparsed_w% "Scc/Test/arith.w"
def helloWX64 : _root_.Program := x64_reparsed_w% "Scc/Test/hello.w"
def handoffX64 : _root_.Program := x64_reparsed_w% "Scc/Test/handoff.w"
def overflowX64 : _root_.Program := x64_reparsed_w% "Scc/Test/overflow.w"
def tailloopX64 : _root_.Program := x64_reparsed_w% "Scc/Test/tailloop.w"
def helloX64 : _root_.Program := x64_reparsed% helloIR
def allOpsX64 : _root_.Program := x64_reparsed% allOpsIR

-- The literals are the emitter's Kraken programs (the re-parse drops exactly
-- the directive lines).
#guard [(arithX64, arithItems), (helloWX64, helloItems), (handoffX64, handoffItems),
    (overflowX64, overflowItems), (tailloopX64, tailloopItems),
    (helloX64, emitItems helloIR), (allOpsX64, emitItems allOpsIR)].all fun
  | (p, .ok items) => decide (p = directives items)
  | (_, .error _) => false

/-! Each program, as re-parsed, is WeakCore-lowerable (every memory RMW is
`lock xadd` or `xchg`, no `movnti`). **Scope:** the re-parsed program, which
has every instruction of the text; the directive lines are not covered, and
the sub-word store obligation `SubWordOwned` is not discharged. -/

theorem arithX64_wcLowerable : ProgramWCLowerable arithX64 := by decide +kernel
theorem helloWX64_wcLowerable : ProgramWCLowerable helloWX64 := by decide +kernel
theorem handoffX64_wcLowerable : ProgramWCLowerable handoffX64 := by decide +kernel
theorem overflowX64_wcLowerable : ProgramWCLowerable overflowX64 := by decide +kernel
theorem tailloopX64_wcLowerable : ProgramWCLowerable tailloopX64 := by decide +kernel
theorem helloX64_wcLowerable : ProgramWCLowerable helloX64 := by decide +kernel
theorem allOpsX64_wcLowerable : ProgramWCLowerable allOpsX64 := by decide +kernel

/-! ## The stack depth limit

`Lower.frameBytes` is the stack an x64 frame occupies (`frameOf`'s size, the
saved `%rbp` and the return address), for every function of the test
programs; the depth limit lets `deeprec.w` (100000 frames) and `growmany.w`
(10000 frames per worker) run. -/

/-- Every function's `Lower.frameBytes` is the emitter's frame plus 16. -/
def framesAgree (src : String) : Except String Bool := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error _ => throw "frontend error"
  let ir ← Lower.lowerProgram { arch := .x64 } c
  let areas := StackMap.argAreas ir 6
  pure (ir.funcs.all fun f => Lower.frameBytes .x64 areas f == (frameOf areas f).size + 16)

/-- The depth limit of a WeakCore source for x64. -/
def framesOfW (src : String) : Except String Nat := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error _ => throw "frontend error"
  let b ← Lower.stackBudget { arch := .x64 } c
  unless b.ok do throw "budget does not hold"
  pure b.frames

#guard (framesAgree (w_src% "Scc/Test/arith.w")).toOption == some true
#guard (framesAgree (w_src% "Scc/Test/hello.w")).toOption == some true
#guard (framesAgree (w_src% "Scc/Test/handoff.w")).toOption == some true
#guard (framesAgree (w_src% "Scc/Test/deeprec.w")).toOption == some true
#guard (framesAgree (w_src% "Scc/Test/growmany.w")).toOption == some true
#guard (framesAgree (w_src% "Scc/Test/stackdepth.w")).toOption == some true
#guard (framesOfW (w_src% "Scc/Test/deeprec.w")).toOption.getD 0 > 100000
#guard (framesOfW (w_src% "Scc/Test/growmany.w")).toOption.getD 0 > 10000

end Scc.Emit.X64.Test
