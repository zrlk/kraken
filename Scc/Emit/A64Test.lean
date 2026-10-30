/-
Tests of the AArch64 printer and emitter of `scc`.

* **Round trip.** For every instruction form the emitter produces, Kraken's
  AArch64 parser reads the printed text back to the same `Directive`s
  (`roundTrips`, checked with `#guard` on the helper forms and on whole emitted
  programs).
* **Lowerability.** The re-parsed text of each emitted test program satisfies
  `Program.WCLowerable` (`Kraken/Promising/Lower/Lowerable.lean`), proved by
  `decide` on the program as a literal (the `a64_reparsed%` elaborator runs the
  emitter and Kraken's parser at elaboration time, exactly as a certificate
  re-parses the text).
* **Assembly.** `main` writes the emitted programs as `.s` files into a
  directory; `Scc/Emit/a64_check.sh` assembles them with `llvm-mc`.

The test programs are written directly in the IR: `helloIR` (one `write` and
`exit_group`, with the start-up stack switch and an abort routine) and
`allOpsIR` (every IR instruction and terminator, including the large and
unaligned displacements that take the fallback paths).
-/
import Scc.Emit.A64
import Scc.Frontend
import Scc.Lower.Program
import Kraken.Promising.Lower.Lowerable
import Scc.Test.Src
import Scc.Cert.NeedA64

namespace Scc.Emit.A64.Test

open Scc.IR

/-! ## Helper forms round-trip -/

/-- Every helper of `Scc/Emit/A64.lean`, with arguments that reach each of
its branches. -/
def helperItems : List Item :=
  movImm .X0 0 ++ movImm .X1 5 ++ movImm .X2 0x10000 ++ movImm .X3 0x123456789abcdef0 ++
  movImm .X4 (-1) ++ movImm .X5 (2 ^ 48) ++
  addrOf .X6 "some_symbol" ++
  addImm spW64 spW64 16 ++ addImm spW64 spW64 (-16) ++ addImm (xs .X1) (xs .X2) 0x5000 ++
  addImm (xs .X1) spW64 (-0x7000) ++ addImm (xs .X1) (xs .X2) 123456789 ++
  [addReg .W64 .X1 .X2 .X3, subReg .W64 .X1 .X2 .X3, addReg .W32 .X1 .X2 .X3,
   movReg .W64 .X1 .X2, movReg .W32 .X1 .X2, movSp spW64 (xs .X9), movSp (xs .X9) spW64] ++
  addChecked .X1 .X2 .X3 "abort_label" ++ subSat .X1 .X2 .X3 ++
  [cmpReg .W64 .X1 .X2, cmpReg .W32 .X1 .X2] ++ cmpImm .W64 .X1 7 ++ cmpImm .W64 .X1 100000 ++
  [cset .W64 .X1 .EQ, cset .W64 .X1 .CC, cset .W64 .X1 .GT] ++
  ldrOff .W64 .X1 spW64 0 ++ ldrOff .W64 .X1 spW64 8 ++ ldrOff .W64 .X1 spW64 32760 ++
  ldrOff .W64 .X1 spW64 (-8) ++ ldrOff .W64 .X1 spW64 3 ++ ldrOff .W64 .X1 spW64 100000 ++
  ldrOff .W32 .X1 (xs .X2) 4 ++ ldrOff .W32 .X1 (xs .X2) (-4) ++ ldrOff .W32 .X1 (xs .X2) 16380 ++
  strOff .W64 .X1 spW64 0 ++ strOff .W64 .X1 spW64 16 ++ strOff .W64 .X1 spW64 (-16) ++
  strOff .W64 .X1 spW64 100000 ++ strOff .W32 .X1 (xs .X2) 12 ++ strOff .W32 .X1 (xs .X2) 2 ++
  strZeroOff .W64 spW64 8 ++ strZeroOff .W32 (xs .X3) (-4) ++ strZeroOff .W64 spW64 50000 ++
  [ldrIdx .X1 .X2 .X3, strIdx .X1 .X2 .X3] ++
  ldrbOff .X1 (xs .X2) 0 ++ ldrbOff .X1 (xs .X2) 4095 ++ ldrbOff .X1 (xs .X2) (-1) ++
  ldrbOff .X1 (xs .X2) 5000 ++
  subWordStore 1 0 .X1 .X2 .X3 ++ subWordStore 1 3 .X1 .X2 .X3 ++ subWordStore 2 2 .X1 .X2 .X3 ++
  [loadAcq .W64 .X1 .X2, loadAcq .W32 .X1 .X2, storeRel .W64 .X1 .X2, storeRel .W32 .X1 .X2,
   casAL .W64 .X1 .X2 .X3, casAL .W32 .X1 .X2 .X3, swpAL .W64 .X1 .X2 .X3, swpAL .W32 .X1 .X2 .X3,
   ldopAL .ADD .W64 .X1 .X2 .X3, ldopAL .EOR .W32 .X1 .X2 .X3, fullFence,
   ins (.DMB .ld), ins (.DMB .st),
   ins (.LDAR .acq false .W8 (wz .X1) (xs .X2)), ins (.LDAR .acq false .W16 (wz .X1) (xs .X2)),
   ins (.LDRH (wz .X1) ⟨xs .X2, .imm ⟨i64 6, none⟩⟩), ins (.LDURH (wz .X1) ⟨xs .X2, i64 (-2)⟩),
   lbl "a_label", lbl ".Llocal.1_x", jmp "a_label", jcc .NE "a_label", jcc .CS "a_label",
   call "callee", callReg .X9, tailReg .X9, ret, cbz .W64 .X1 "a_label",
   cbnz .W32 .X1 "a_label"] ++
  prologue 32 ++ epilogue 32 ++ prologue 40000 ++ epilogue 40000 ++
  syscall sysWrite ++ [readTp .X0, writeTp .X0, readTp .X10, writeTp .X30] ++
  [.comment "a comment: with a colon"]

#guard helperItems.all Item.ok
#guard roundTrips helperItems

-- The printed text of a few helper forms.
/--
info: 	movz x3, #57072
	movk x3, #39612, lsl #16
	movk x3, #22136, lsl #32
	movk x3, #4660, lsl #48
	adrp x6, some_symbol
	add x6, x6, :lo12:some_symbol
	sub sp, sp, #16
	ldur x1, [sp, #-8]
	movz x16, #34464
	movk x16, #1, lsl #16
	ldr x1, [sp, x16]
	ldr w3, [x2]
	bfm w3, w1, #8, #7
	str w3, [x2]
	ldar x1, [x2]
	stlr w1, [x2]
	casal x1, x2, [x3]
	swpal w1, w2, [x3]
	ldaddal x1, x2, [x3]
	dmb ish
	b.hs a_label
	ret
	svc #0
	mrs x0, tpidr_el0
	msr tpidr_el0, x30
-/
#guard_msgs in
#eval IO.print <| (render (movImm .X3 0x123456789abcdef0 ++ addrOf .X6 "some_symbol" ++
  addImm spW64 spW64 (-16) ++ ldrOff .W64 .X1 spW64 (-8) ++ ldrOff .W64 .X1 spW64 100000 ++
  subWordStore 1 3 .X1 .X2 .X3 ++
  [loadAcq .W64 .X1 .X2, storeRel .W32 .X1 .X2, casAL .W64 .X1 .X2 .X3, swpAL .W32 .X1 .X2 .X3,
   ldopAL .ADD .W64 .X1 .X2 .X3, fullFence, jcc .CS "a_label", ret, ins (.SVC 0), readTp .X0,
   writeTp .X30])).toOption.getD ""

/-! ## Forms that do not round-trip are refused or detected -/

-- A raw line with a colon would survive `stripDirectives`; `render` refuses it.
#guard !(Item.raw ".ascii \"a:b\"").ok
#guard (render [.raw ".ascii \"a:b\""]).toOption.isNone
-- Register names are not labels.
#guard !labelOk "x1" && !labelOk "sp" && !labelOk "1abc" && labelOk ".L0_f.1_b"
-- An `ADD_e` with an unshifted register operand is printed with an explicit
-- `uxtx`, so it is not read back as `ADD_s`.
#guard roundTrips [ins (.ADD_e (xs .X0) (xs .X1) (.ext ⟨⟨.W64, xz .X2⟩, ⟨.UXTX, .E0⟩⟩))]
-- A `NOP` at width `W32` is read back at `W64`: the emitter never produces it.
#guard !roundTrips [ins (.NOP : Operation .W32)]

/-! ## IR test programs -/

def r (s : String) : Operand := .reg s
def k (n : Nat) : Operand := .imm (UInt64.ofNat n)

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

/-- Every IR instruction and terminator. -/
def allOpsIR : IR.Program where
  start := "t_start"
  abortFn := "t_abort"
  data := [{ name := "t_data", init := .zero 64 }, { name := "t_bytes", init := .bytes [1, 2, 3] }]
  funcs := [
    { name := "t_start", params := [], checkStack := false, blocks := [
      { label := "entry", insts := [.la "t" "t_data", .la "s" "t_data"],
        term := .switchTo (r "s") (r "t") "t_ops" (k 7) }] },
    { name := "t_ops", params := ["a", "b", "c", "d", "e", "f"], blocks := [
      { label := "entry", insts := [
          .comment "arithmetic",
          .mov "x" (r "a"), .mov "y" (k 0xffffffffffffffff),
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
          .ext true .w64 "z" (r "x"),
          .setc .eq "z" (r "x") (r "y"), .setc .ne "z" (r "x") (r "y"),
          .setc .ult "z" (r "x") (r "y"), .setc .ule "z" (r "x") (r "y"),
          .setc .ugt "z" (r "x") (r "y"), .setc .uge "z" (r "x") (r "y"),
          .setc .slt "z" (r "x") (r "y"), .setc .sle "z" (r "x") (r "y"),
          .setc .sgt "z" (r "x") (r "y"), .setc .sge "z" (r "x") (r "y"),
          .select .ult "z" (r "x") (r "y") (r "a") (k 9),
          .addChk "z" (r "x") (r "y"), .subSat "z" (r "x") (r "y"),
          .comment "memory",
          .la "m" "t_data", .getTp "tp",
          .load .plain .w8 "z" ⟨"m", 1⟩, .load .plain .w16 "z" ⟨"m", 2⟩,
          .load .plain .w32 "z" ⟨"m", 4⟩, .load .plain .w64 "z" ⟨"m", 8⟩,
          .load .plain .w64 "z" ⟨"m", -8⟩, .load .plain .w64 "z" ⟨"m", 3⟩,
          .load .plain .w64 "z" ⟨"m", 100000⟩, .load .plain .w16 "z" ⟨"m", 100000⟩,
          .load .acq .w8 "z" ⟨"m", 0⟩, .load .acq .w16 "z" ⟨"m", 2⟩,
          .load .acq .w32 "z" ⟨"m", 4⟩, .load .acq .w64 "z" ⟨"m", 8⟩,
          .store .plain .w8 ⟨"m", 1⟩ (r "x"), .store .plain .w16 ⟨"m", 2⟩ (r "x"),
          .store .plain .w32 ⟨"m", 4⟩ (r "x"), .store .plain .w64 ⟨"m", 8⟩ (k 0),
          .store .plain .w64 ⟨"m", -16⟩ (r "x"), .store .plain .w64 ⟨"m", 200000⟩ (r "x"),
          .store .rel .w8 ⟨"m", 1⟩ (r "x"), .store .rel .w16 ⟨"m", 2⟩ (r "x"),
          .store .rel .w32 ⟨"m", 4⟩ (r "x"), .store .rel .w64 ⟨"m", 8⟩ (r "x"),
          .rmw .xchg "z" ⟨"m", 0⟩ (r "x"), .rmw .add "z" ⟨"m", 8⟩ (k 1),
          .fence .ld, .fence .st, .fence .full,
          .comment "calls",
          .call ["p", "q"] "t_callee" [r "a", r "b", r "c", r "d", r "e", k 6],
          .call [] "t_callee" [],
          .syscall "z" .futex [r "m", k 0, k 1, k 0, k 0, k 0],
          .syscall "z" .rtSigaction [k 13, r "m", k 0, k 8],
          .clone "tid" (r "s") (r "tp") "t_thread" (r "m")],
        term := .br .uge (r "x") (r "y") "left" "right" },
      { label := "left", insts := [], term := .jmp "out" },
      { label := "right", insts := [], term := .tail "t_callee" [r "p", r "q"] },
      { label := "out", insts := [], term := .ret [r "p", r "q", k 3] }] },
    { name := "t_callee", params := ["u", "v"], blocks := [
      { label := "entry", insts := [], term := .ret [r "v", r "u"] }] },
    { name := "t_thread", params := ["arg"], blocks := [
      { label := "entry", insts := [.syscall "z" .exit [k 0]], term := .unreachable }] },
    { name := "t_abort", params := ["code"], checkStack := false, blocks := [
      { label := "entry", insts := [.syscall "z" .exitGroup [k abortExitCode]],
        term := .unreachable }] }]

/-! ### Programs meant to run

`startBlocks` is a start routine that builds the main thread's TCB in
`scc_tcb0` (self pointer, stack limit) and switches to `scc_stack0`. -/

/-- 16 KiB stacks. -/
def stackBytes : Nat := 16384

/-- The data every runnable test needs: TCB and stack of the main thread and
the abort message. -/
def baseData : List Data := [
  { name := "scc_abort_msg", align := 1, init := .bytes "scc abort\n".toUTF8.toList },
  { name := "scc_tcb0", init := .zero Tcb.size },
  { name := "scc_stack0", align := 16, init := .zero stackBytes }]

/-- Instructions that initialise a TCB `tcb` with stack `stk`; leave the top
of the stack in register `top`. -/
def initTcb (tcb stk : Sym) : List Inst :=
  [.la "t" tcb, .store .plain .w64 ⟨"t", Tcb.self⟩ (r "t"),
   .la "s" stk, .bin .add "lim" (r "s") (k Tcb.headroom),
   .store .plain .w64 ⟨"t", Tcb.stackLimit⟩ (r "lim"),
   .bin .add "top" (r "s") (k stackBytes)]

def startFunc (main : Sym) : Func :=
  { name := "scc_start", params := [], checkStack := false, blocks := [
    { label := "entry", insts := initTcb "scc_tcb0" "scc_stack0",
      term := .switchTo (r "top") (r "t") main (k 0) }] }

/-- The abort routine: message to fd 2, `exit_group(101)`. -/
def abortFunc : Func :=
  { name := "scc_abort", params := ["code"], checkStack := false, blocks := [
    { label := "entry", insts := [
        .la "p" "scc_abort_msg",
        .syscall "n" .write [k 2, r "p", k 10],
        .syscall "z" .exitGroup [k abortExitCode]],
      term := .unreachable }] }

/-- `write(1, sym, n)`. -/
def say (sym : Sym) (n : Nat) : List Inst := [.la "p" sym, .syscall "n" .write [k 1, r "p", k n]]

/-- A chain of checks: check `i` runs its instructions, then compares register
`got` with its expected value; on a mismatch the program exits with code
`10 + i`. After the last check, control goes to block `pass`. -/
def checkBlocks (cs : List (List Inst × Operand)) : List Block :=
  (cs.zipIdx.map fun ((insts, expected), i) =>
    [{ label := s!"c{i}", insts,
       term := .br .eq (r "got") expected (if i + 1 = cs.length then "pass" else s!"c{i+1}") s!"f{i}" },
     { label := s!"f{i}", insts := [.syscall "z" .exitGroup [k (10 + i)]], term := .unreachable }]).flatten

def u64 (n : Int) : Operand := .imm (UInt64.ofInt n)

/-- Arithmetic, sub-word stores and calls, checked at run time: prints `ok`
and exits with 0, or exits with `10 + i` at the first failing check `i`. -/
def checksIR : IR.Program where
  start := "scc_start"
  abortFn := "scc_abort"
  data := baseData ++ [
    { name := "t_ok", align := 1, init := .bytes "ok\n".toUTF8.toList },
    { name := "t_buf", init := .zero 16 }]
  funcs := [startFunc "main", abortFunc,
    { name := "t_two", params := ["a", "b", "c", "d", "e", "f"], blocks := [
      { label := "entry", insts := [.bin .add "x" (r "a") (r "b"), .bin .add "x" (r "x") (r "c"),
          .bin .add "y" (r "d") (r "e"), .bin .add "y" (r "y") (r "f")],
        term := .ret [r "x", r "y"] }] },
    { name := "t_tailer", params := ["a"], blocks := [
      { label := "entry", insts := [.bin .add "a" (r "a") (k 1)],
        term := .tail "t_two" [r "a", k 0, k 0, k 1, k 1, k 1] }] },
    { name := "main", params := ["arg"], blocks := checkBlocks [
      ([.un .popcnt "got" (u64 0xF0F0F0F0F0F0F0F1)], k 33),
      ([.un .ctz "got" (k 0x100)], k 8),
      ([.un .ctz "got" (k 0)], k 64),
      ([.un .not "got" (k 0)], u64 (-1)),
      ([.un .neg "got" (k 1)], u64 (-1)),
      ([.bin .urem "got" (k 17) (k 5)], k 2),
      ([.bin .udiv "got" (k 17) (k 0)], k 0),
      ([.bin .urem "got" (k 17) (k 0)], k 17),
      ([.bin .sdiv "got" (u64 (-7)) (k 2)], u64 (-3)),
      ([.bin .srem "got" (u64 (-7)) (k 2)], u64 (-1)),
      ([.bin .sdiv "got" (u64 (-2 ^ 63)) (u64 (-1))], u64 (-2 ^ 63)),
      ([.bin .srem "got" (u64 (-2 ^ 63)) (u64 (-1))], k 0),
      ([.bin .umulh "got" (k (2 ^ 63)) (k 4)], k 2),
      ([.bin .mul "got" (k 6) (k 7)], k 42),
      ([.bin .ashr "got" (u64 (-16)) (k 2)], u64 (-4)),
      ([.bin .lshr "got" (u64 (-16)) (k 60)], k 15),
      ([.bin .shl "got" (k 1) (k 65)], k 2),
      ([.bin .xor "got" (k 0xff) (k 0x0f)], k 0xf0),
      ([.ext true .w8 "got" (k 0x80)], u64 (-128)),
      ([.ext false .w16 "got" (k 0x12345)], k 0x2345),
      ([.ext true .w32 "got" (k 0xffffffff)], u64 (-1)),
      ([.subSat "got" (k 3) (k 5)], k 0),
      ([.subSat "got" (k 5) (k 3)], k 2),
      ([.addChk "got" (u64 (-2)) (k 1)], u64 (-1)),
      ([.setc .slt "got" (u64 (-1)) (k 0)], k 1),
      ([.setc .ult "got" (u64 (-1)) (k 0)], k 0),
      ([.select .sge "got" (k 3) (k 3) (k 7) (k 8)], k 7),
      ([.la "b" "t_buf", .store .plain .w8 ⟨"b", 3⟩ (k 0x1AB), .store .plain .w16 ⟨"b", 6⟩ (k 0xCDEF),
        .store .rel .w8 ⟨"b", 9⟩ (k 0x11), .load .plain .w64 "got" ⟨"b", 0⟩], k 0xCDEF0000AB000000),
      ([.la "b" "t_buf", .load .acq .w64 "got" ⟨"b", 8⟩], k 0x1100),
      ([.la "b" "t_buf", .load .plain .w16 "got" ⟨"b", 6⟩], k 0xCDEF),
      ([.la "b" "t_buf", .store .rel .w32 ⟨"b", 12⟩ (k 0x12345678), .load .acq .w8 "got" ⟨"b", 13⟩],
        k 0x56),
      ([.la "b" "t_buf", .rmw .add "o" ⟨"b", 8⟩ (k 1), .bin .add "got" (r "o") (k 0)],
        k 0x1234567800001100),
      ([.la "b" "t_buf", .rmw .xchg "o" ⟨"b", 8⟩ (k 5), .load .plain .w64 "got" ⟨"b", 8⟩], k 5),
      ([.call ["x", "y"] "t_two" [k 1, k 2, k 3, k 4, k 5, k 6], .bin .sub "got" (r "y") (r "x")], k 9),
      ([.call ["x", "y"] "t_tailer" [k 4], .bin .add "got" (r "x") (r "y")], k 8),
      ([.getTp "t", .load .plain .w64 "got" ⟨"t", Tcb.self⟩, .la "u" "scc_tcb0",
        .bin .sub "got" (r "got") (r "u")], k 0)] ++
      [{ label := "pass", insts := say "t_ok" 3 ++ [.syscall "z" .exitGroup [k 0]],
         term := .unreachable }] }]

/-- A checked addition that overflows: the abort routine exits with 101. -/
def overflowIR : IR.Program where
  start := "scc_start"
  abortFn := "scc_abort"
  data := baseData
  funcs := [startFunc "main", abortFunc,
    { name := "main", params := ["arg"], blocks := [
      { label := "entry", insts := [.addChk "x" (u64 (-1)) (k 1), .syscall "z" .exitGroup [k 0]],
        term := .unreachable }] }]

/-- Unbounded recursion with the stack check: the abort routine exits with 101. -/
def stackIR : IR.Program where
  start := "scc_start"
  abortFn := "scc_abort"
  data := baseData
  funcs := [startFunc "main", abortFunc,
    { name := "main", params := ["arg"], blocks := [
      { label := "entry", insts := [.call ["x"] "main" [r "arg"]], term := .ret [r "x"] }] }]

/-- Two threads: `main` starts a child with `clone(CLONE_SETTLS)` and parks on
its own TCB's permit (futex wait while the permit is 0); the child checks its
thread pointer and its second argument (`77`, passed in `spawnReg 1`,
`Inst.clone`), prints `child`, unparks `main` (exchange the permit to 1, futex
wake), sets its exited flag with a release store and wakes any waiter, then
exits. `main`, after being unparked, waits for the exited flag (acquire load,
futex wait) and prints `main`. Output `child\nmain\n`, exit 0. -/
def threadsIR : IR.Program where
  start := "scc_start"
  abortFn := "scc_abort"
  data := baseData ++ [
    { name := "scc_tcb1", init := .zero Tcb.size },
    { name := "scc_stack1", align := 16, init := .zero stackBytes },
    { name := "t_child", align := 1, init := .bytes "child\n".toUTF8.toList },
    { name := "t_main", align := 1, init := .bytes "main\n".toUTF8.toList }]
  funcs := [startFunc "main", abortFunc,
    { name := "main", params := ["arg"], blocks := [
      { label := "entry", insts := initTcb "scc_tcb1" "scc_stack1" ++
          [.mov (spawnReg 1) (k 77), .clone "tid" (r "top") (r "t") "child" (r "t")],
        term := .br .slt (r "tid") (k 0) "fail" "park" },
      { label := "fail", insts := [.call [] "scc_abort" [k 9]], term := .unreachable },
      { label := "park", insts := [.getTp "me", .rmw .xchg "p" ⟨"me", Tcb.permit⟩ (k 0)],
        term := .br .ne (r "p") (k 0) "join" "wait1" },
      { label := "wait1", insts := [.bin .add "a" (r "me") (k Tcb.permit),
          .syscall "z" .futex [r "a", k 128, k 0, k 0, k 0, k 0]],
        term := .jmp "park" },
      { label := "join", insts := [.la "c" "scc_tcb1", .load .acq .w64 "e" ⟨"c", Tcb.exited⟩],
        term := .br .ne (r "e") (k 0) "done" "wait2" },
      { label := "wait2", insts := [.bin .add "a" (r "c") (k Tcb.exited),
          .syscall "z" .futex [r "a", k 128, k 0, k 0, k 0, k 0]],
        term := .jmp "join" },
      { label := "done", insts := say "t_main" 5 ++ [.syscall "z" .exitGroup [k 0]],
        term := .unreachable }] },
    { name := "child", params := ["self", "v"], blocks := [
      { label := "entry", insts := [.getTp "tp"],
        term := .br .eq (r "tp") (r "self") "arg2" "bad" },
      { label := "arg2", insts := [], term := .br .eq (r "v") (k 77) "run" "bad2" },
      { label := "bad", insts := [.syscall "z" .exitGroup [k 7]], term := .unreachable },
      { label := "bad2", insts := [.syscall "z" .exitGroup [k 8]], term := .unreachable },
      { label := "run", insts := say "t_child" 6 ++
          [.la "m" "scc_tcb0", .rmw .xchg "old" ⟨"m", Tcb.permit⟩ (k 1),
           .bin .add "a" (r "m") (k Tcb.permit),
           .syscall "z" .futex [r "a", k 129, k 1, k 0, k 0, k 0],
           .store .rel .w64 ⟨"tp", Tcb.exited⟩ (k 1),
           .bin .add "a" (r "tp") (k Tcb.exited),
           .syscall "z" .futex [r "a", k 129, k 1, k 0, k 0, k 0],
           .syscall "z" .exit [k 0]],
        term := .unreachable }] }]

/-- The emitted items of a program, or none. -/
def itemsOf (p : IR.Program) : List Item := (emitItems p).toOption.getD []

#guard (emitItems helloIR).toOption.isSome
#guard (emitItems allOpsIR).toOption.isSome
#guard roundTrips (itemsOf helloIR)
#guard roundTrips (itemsOf allOpsIR)
#guard roundTrips (itemsOf checksIR)
#guard roundTrips (itemsOf overflowIR)
#guard roundTrips (itemsOf stackIR)
#guard roundTrips (itemsOf threadsIR)

/-! ## Lowerability of the emitted programs (as re-parsed) -/

open Lean Elab Term Meta in
/-- `a64_reparsed% p`: emit the IR program `p`, print it, re-parse the text
with Kraken's parser (as a certificate does), and return the resulting
`Program` as a literal. -/
elab "a64_reparsed% " t:term : term => do
  let e ← elabTermEnsuringType t (mkConst ``Scc.IR.Program)
  let e ← instantiateMVars e
  let p ← unsafe evalExpr Scc.IR.Program (mkConst ``Scc.IR.Program) e
  match emitProgram p with
  | .error msg => throwError msg
  | .ok text =>
    match reparse text with
    | .error msg => throwError "re-parse failed: {msg}"
    | .ok prog => return toExpr prog

/-- Compile a WeakCore source text for `--arch arm`: frontend, lowering,
AArch64 emitter. -/
def compileW (src : String) : Except String String := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let ir ← Lower.lowerProgram { arch := .arm } c
  emitProgram ir

open Lean Elab Term Meta in
/-- `a64_reparsed_w% "path.w"`: compile the WeakCore file (path relative to the
package root) for `--arch arm`, re-parse the emitted text with Kraken's parser,
and return the resulting `Program` as a literal. -/
elab "a64_reparsed_w% " path:str : term => do
  let src ← IO.FS.readFile path.getString
  match compileW src with
  | .error msg => throwError msg
  | .ok text =>
    match reparse text with
    | .error msg => throwError "re-parse failed: {msg}"
    | .ok prog => return toExpr prog

/-- `Scc/Test/hello.w` compiled for `--arch arm`, as Kraken's parser reads the
emitted text. -/
def helloWA64 : _root_.Program := a64_reparsed_w% "Scc/Test/hello.w"

/-- `helloWA64` (the emitted text of `Scc/Test/hello.w`, as Kraken's parser
reads it) is WeakCore-lowerable.

**Scope.** This is a statement about the *re-parsed* program only. The text
also contains lines that `stripDirectives` drops before parsing, so they are
not covered: the assembler directives (`.arch`, `.text`, `.data`, `.bss`, `.globl`, `.type`,
`.p2align`, `.balign`, `.byte`, `.zero`). -/
theorem helloWA64_wcLowerable : helloWA64.WCLowerable := by decide +kernel

/-- The emitted hello program, as Kraken's parser reads it. -/
def helloA64 : _root_.Program := a64_reparsed% helloIR

/-- The emitted all-operations program, as Kraken's parser reads it. -/
def allOpsA64 : _root_.Program := a64_reparsed% allOpsIR

/-- `helloA64` (the emitted text, as Kraken's parser reads it) is WeakCore-lowerable.

**Scope.** This is a statement about the *re-parsed* program only. The text
also contains lines that `stripDirectives` drops before parsing, so they are
not covered: the assembler directives (`.arch`, `.text`, `.data`, `.bss`, `.globl`, `.type`,
`.p2align`, `.balign`, `.byte`, `.zero`). -/
theorem helloA64_wcLowerable : helloA64.WCLowerable := by decide +kernel

/-- `allOpsA64` (the emitted text, as Kraken's parser reads it) is WeakCore-lowerable.

**Scope.** This is a statement about the *re-parsed* program only. The text
also contains lines that `stripDirectives` drops before parsing, so they are
not covered: the assembler directives (`.arch`, `.text`, `.data`, `.bss`, `.globl`, `.type`,
`.p2align`, `.balign`, `.byte`, `.zero`). -/
theorem allOpsA64_wcLowerable : allOpsA64.WCLowerable := by decide +kernel

/-- The emitted run-time checks program, as Kraken's parser reads it. -/
def checksA64 : _root_.Program := a64_reparsed% checksIR

/-- The emitted two-thread program, as Kraken's parser reads it. -/
def threadsA64 : _root_.Program := a64_reparsed% threadsIR

/-- `checksA64` (the emitted text, as Kraken's parser reads it) is WeakCore-lowerable.

**Scope.** This is a statement about the *re-parsed* program only. The text
also contains lines that `stripDirectives` drops before parsing, so they are
not covered: the assembler directives (`.arch`, `.text`, `.data`, `.bss`, `.globl`, `.type`,
`.p2align`, `.balign`, `.byte`, `.zero`). -/
theorem checksA64_wcLowerable : checksA64.WCLowerable := by decide +kernel

/-- `threadsA64` (the emitted text, as Kraken's parser reads it) is WeakCore-lowerable.

**Scope.** This is a statement about the *re-parsed* program only. The text
also contains lines that `stripDirectives` drops before parsing, so they are
not covered: the assembler directives (`.arch`, `.text`, `.data`, `.bss`, `.globl`, `.type`,
`.p2align`, `.balign`, `.byte`, `.zero`). -/
theorem threadsA64_wcLowerable : threadsA64.WCLowerable := by decide +kernel

-- Every instruction is a Kraken instruction: no raw `.inst` words, and the
-- re-parsed programs contain the system call and thread-pointer forms, so the
-- `WCLowerable` results above cover them.
#guard [helloIR, allOpsIR, checksIR, threadsIR].all fun p =>
  (itemsOf p).all fun | .raw l => !(l.trimAsciiStart.toString.startsWith ".inst") | _ => true
#guard [helloWA64, helloA64, allOpsA64, threadsA64].all fun p =>
  p.any (fun | .instr ⟨_, .SVC 0⟩ => true | _ => false) &&
  p.any (fun | .instr ⟨_, .MRS _ .TPIDR_EL0⟩ => true | _ => false) &&
  p.any (fun | .instr ⟨_, .MSR .TPIDR_EL0 _⟩ => true | _ => false)

/-- The runtime's site `s` (`Inst.site`) in a re-parsed program: the label
`s` is placed exactly once, on a `nop`. -/
def siteOk (p : _root_.Program) (s : String) : Bool :=
  let a : Array Directive := p.toArray
  match (List.range a.size).filter (fun (k : Nat) => match a[k]? with | some (.label l) => l == s | _ => false) with
  | [k] => match a[k + 1]? with
    | some (.instr ⟨.W64, .NOP⟩) => true
    | _ => false
  | _ => false

-- The take and release sites of the stack pool, in the compiled program; the
-- IR programs without the runtime have none.
#guard siteOk helloWA64 Lower.Names.takeSite && siteOk helloWA64 Lower.Names.releaseSite
#guard [helloA64, allOpsA64, checksA64, threadsA64].all fun p =>
  !siteOk p Lower.Names.takeSite && !siteOk p Lower.Names.releaseSite

-- The literals are the emitter's output (not just some parse).
#guard decide (helloA64 = directives (itemsOf helloIR))
#guard decide (allOpsA64 = directives (itemsOf allOpsIR))
#guard decide (checksA64 = directives (itemsOf checksIR))
#guard decide (threadsA64 = directives (itemsOf threadsIR))

/-! ## Writing the test programs for the assembler check -/

/-- The emitted test programs, by file name. -/
def testPrograms : List (String × IR.Program) :=
  [("hello_ir", helloIR), ("allops_ir", allOpsIR), ("checks_ir", checksIR),
   ("overflow_ir", overflowIR), ("stack_ir", stackIR), ("threads_ir", threadsIR)]

/-- Write each test program as `<dir>/<name>.s` (the first argument, default
`.`). `Scc/Emit/a64_check.sh` calls it from a generated driver. -/
def writeAll (args : List String) : IO UInt32 := do
  let dir := args.headD "."
  IO.FS.createDirAll dir
  for (name, p) in testPrograms do
    match emitProgram p with
    | .ok text => IO.FS.writeFile s!"{dir}/{name}.s" text
    | .error e => IO.eprintln e; return 1
  return 0

/-! ## The stack depth limit

`Lower.frameBytes` is the AArch64 frame (`fnCtx`'s `frame`, which holds
`x29`/`x30`), for every function of the test programs; the depth limit lets
`deeprec.w` (100000 frames) and `growmany.w` (10000 frames per worker) run. -/

/-- Every function's `Lower.frameBytes` is the emitter's frame. -/
def framesAgree (src : String) : Except String Bool := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error _ => throw "frontend error"
  let ir ← Lower.lowerProgram { arch := .arm } c
  let areas := StackMap.argAreas ir argRegs.length
  pure (ir.funcs.all fun f =>
    Lower.frameBytes .arm areas f == (fnCtx ir.abortFn ir.growth areas 0 f).frame)

/-- The depth limit of a WeakCore source for AArch64. -/
def framesOfW (src : String) : Except String Nat := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error _ => throw "frontend error"
  let b ← Lower.stackBudget { arch := .arm } c
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

/-! ## The stack need table (G6)

`Lower.stackNeed` on `hello.w` (calls `wc_printL → wc_emit8`, a tail call
`wc_printL → wc_printL`, the trampolines' calls) holds on the emitted text
as Kraken's parser reads it (`Scc.Cert.NeedA64.needOk`); lowering one need breaks
it; a program with non-tail recursion has no table. -/

/-- The stack need table of a WeakCore source for AArch64. -/
def needOfW (src : String) : Except String (List Scc.Cert.NeedA64.Row) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error _ => throw "frontend error"
  let ir ← Lower.lowerProgram { arch := .arm } c
  Lower.stackNeed .arm ir

/-- `needOfW` of `Scc/Test/hello.w`. -/
def helloNeed : List Scc.Cert.NeedA64.Row := (needOfW (w_src% "Scc/Test/hello.w")).toOption.getD []

/-- The thread entries of `Scc/Test/hello.w`. -/
def helloEntries : List String :=
  (do
    let c ← match Frontend.run (w_src% "Scc/Test/hello.w") with
      | .ok c => pure c
      | .error _ => throw "frontend error"
    pure (Lower.threadEntries (← Lower.lowerProgram { arch := .arm } c))).toOption.getD []

#guard helloEntries == ["scc_rt_main", "scc_rt_thr_worker"]
#guard helloNeed.length == 6
#guard Scc.Cert.NeedA64.needOk helloWA64 helloNeed (16384 - 4096) helloEntries
-- `scc_rt_main` calls `wc_main`: its need covers its frame and `wc_main`'s.
#guard (Scc.Cert.NeedA64.row? helloNeed "scc_rt_main").map (·.2.2) ==
  (do let (_, fr, _) ← Scc.Cert.NeedA64.row? helloNeed "scc_rt_main"
      let (_, _, ne) ← Scc.Cert.NeedA64.row? helloNeed "wc_main"
      pure (fr + ne))
#guard !Scc.Cert.NeedA64.needOk helloWA64
  (helloNeed.map fun r => if r.1 == "scc_rt_main" then (r.1, r.2.1, r.2.2 - 8) else r)
  (16384 - 4096) helloEntries
#guard !Scc.Cert.NeedA64.needOk helloWA64 helloNeed 100 helloEntries
#guard (needOfW (w_src% "Scc/Test/deeprec.w")).toOption.isNone

end Scc.Emit.A64.Test
