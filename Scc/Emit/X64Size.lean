import Kraken.X64.Syntax
import Std.Data.HashMap

/-!
# x64 instruction lengths, as GNU `as` encodes them

`sizeOf d wide` is the length in bytes of the encoding GNU `as` (64-bit
mode, no `-O`) picks for the Kraken x64 directive `d`: legacy prefixes
(`0x66` operand size, `0x67` address size, `0xF0` lock, `0x64` for `%fs:`),
REX (REX.W at 64-bit operand size except `push`/`pop`/branches, REX.R/X/B
for `%r8`–`%r15`, a bare REX for `%spl`/`%bpl`/`%sil`/`%dil`), the opcode,
ModRM, SIB (an index, a `%rsp`/`%r12` base, or no base at all),
displacement (none, disp8 or disp32; always disp32 for `%rip` and
symbolic displacements) and immediate (imm8 when it fits a sign-extended
byte and the opcode has an imm8 form, the short accumulator forms, `movabs`
for a 64-bit `mov` immediate that does not fit 32 bits).

Branches: `call` is always rel32 (5 bytes). `jcc`/`jmp` to a label are
rel8 (2 bytes) or rel32 (6 / 5 bytes), as `wide` says; GNU `as` relaxes
them to rel8 exactly when the displacement measured from the end of the
2-byte form fits a signed byte (`branchShort`). Since relaxation is
monotone, a layout is gas's when every branch's `wide` is
`!branchShort (target − (addr + 2))` at the addresses of that layout:
`checkCells` validates a size table that way, and a layout pass computes
the least such fixpoint by iteration.

Labels are 0 bytes and a byte array its length. An alignment directive
(`nopalign n`, from `.p2align`/`.balign`) is `alignPad addr n`, so it is
not a function of the directive alone: `sizeOf` returns `none` for it and
`sizeAt` takes the address. Every form outside the emitter's repertoire
(AVX, `mulx`, `.align n, max`, non-64-bit `push`/`pop`, ...) is `none`, so
a pass built on these functions fails closed.

Untrusted: the statement's loader checks the size table it is given
(`Kraken.Promising.X64.SizeCheck`) and the certificates read their tables
off the assembler (`Scc.Cert.Sizes`); this module is for planning a layout
before assembly (granule placement, the block-length bound) and its tests
compare it, cell by cell, with the assembler's tables of every fixture
(`Spike/Test/X64SizeFixtures.lean`, `X64SizeCall1.lean`,
`X64SizeFrame0.lean`).
-/

namespace Scc.Emit.X64.Size

/-! ## Operand pieces -/

/-- Does `i` fit a sign-extended byte? -/
def fits8 (i : Int) : Bool := decide (-128 ≤ i ∧ i ≤ 127)

/-- Does `i` fit a sign-extended 32-bit immediate? -/
def fits32 (i : Int) : Bool := decide (-2 ^ 31 ≤ i ∧ i < 2 ^ 31)

/-- The value of a literal constant; `none` for symbolic ones. -/
def constInt? : ConstExpr → Option Int
  | .int64 i => some i.toInt
  | _ => none

/-- Is the constant a literal that fits a sign-extended byte? -/
def const8 (c : ConstExpr) : Bool := (constInt? c).any fits8

/-- `%r8`–`%r15`: needs a REX.R/X/B bit. -/
def hi : Reg64 → Bool
  | .r8 | .r9 | .r10 | .r11 | .r12 | .r13 | .r14 | .r15 => true
  | _ => false

/-- Does naming the register force a REX prefix (`%r8`–`%r15`, or
`%spl`/`%bpl`/`%sil`/`%dil` at 8 bits)? -/
def regRex {w : Width} : Reg w → Bool
  | .low r w => hi r || (w == .W8 && match r with | .rsp | .rbp | .rsi | .rdi => true | _ => false)
  | _ => false

/-- The accumulator (`%al`/`%ax`/`%eax`/`%rax`). -/
def isAcc {w : Width} : Reg w → Bool
  | .low .rax _ => true
  | _ => false

/-- The ModRM, SIB and displacement bytes of a memory operand, and whether
its registers need REX. -/
def memLen (a : AddrExpr) : Nat × Bool :=
  let idxRex := a.idx.any (hi ·.reg)
  match a.base with
  | some .rip => (5, idxRex)
  | none => (6, idxRex)
  | some (.reg b) =>
    let sib := if a.idx.isSome || b == .rsp || b == .r12 then 1 else 0
    let disp := match constInt? a.disp with
      | some 0 => if b == .rbp || b == .r13 then 1 else 0
      | some d => if fits8 d then 1 else 4
      | none => 4
    (1 + sib + disp, hi b || idxRex)

/-- The ModRM (and SIB, displacement) bytes of a register-or-memory operand,
and whether it needs REX. -/
def rmLen {w : Width} : RegOrMem w → Nat × Bool
  | .reg r => (1, (regRex r))
  | .mem a => memLen a

/-- Is the operand in memory? -/
def isMem {w : Width} : RegOrMem w → Bool
  | .mem _ => true
  | .reg _ => false

/-- The bytes of a full-width immediate at operand width `w` (imm32 at 64
bits, sign-extended). -/
def immW : Width → Nat
  | .W8 => 1 | .W16 => 2 | _ => 4

/-- An encoding's length: optional `0x67`, `0x66` at 16 bits, REX when
`rexW` (64-bit operand size) or a register needs it, then `body` bytes
(opcode, ModRM/SIB/displacement, immediate). -/
def enc (as w : Width) (mem : Bool) (rexW rex : Bool) (body : Nat) : Nat :=
  (if mem && as == .W32 then 1 else 0) + (if w == .W16 then 1 else 0) +
    (if rexW || rex then 1 else 0) + body

/-! ## Instruction forms -/

/-- `op rm, reg`-shaped forms with an `opc`-byte opcode: `rm` the ModRM
operand, `rex` any REX the other register needs. -/
def rmForm (as w : Width) (opc : Nat) (rm : Nat × Bool) (mem rex : Bool) (imm : Nat := 0) : Nat :=
  enc as w mem (w == .W64) (rm.2 || rex) (opc + rm.1 + imm)

/-- The binary ALU group (`add`, `or`, `adc`, `sbb`, `and`, `sub`, `xor`,
`cmp`) with destination `d` and source `s`. -/
def aluLen (as : Width) {w : Width} (d : RegOrMem w) (s : Operand w) : Option Nat :=
  match d, s with
  | d, .regOrMem (.reg r) => some (rmForm as w 1 (rmLen d) (isMem d) (regRex r))
  | .reg r, .regOrMem (.mem m) => some (rmForm as w 1 (memLen m) true (regRex r))
  | .mem _, .regOrMem (.mem _) => none
  | d, .imm c =>
    if w == .W8 then
      if (match d with | .reg r => (isAcc r) | _ => false) then some 2
      else some (rmForm as w 1 (rmLen d) (isMem d) false 1)
    else if const8 c then some (rmForm as w 1 (rmLen d) (isMem d) false 1)
    else if (match d with | .reg r => (isAcc r) | _ => false) then
      some (enc as w false (w == .W64) false (1 + immW w))
    else some (rmForm as w 1 (rmLen d) (isMem d) false (immW w))

/-- `test`: no imm8 form; the accumulator has a short form. -/
def testLen (as : Width) {w : Width} (a : RegOrMem w) (b : Operand w) : Option Nat :=
  match a, b with
  | a, .regOrMem (.reg r) => some (rmForm as w 1 (rmLen a) (isMem a) (regRex r))
  | .reg r, .regOrMem (.mem m) => some (rmForm as w 1 (memLen m) true (regRex r))
  | .mem _, .regOrMem (.mem _) => none
  | a, .imm _ =>
    if (match a with | .reg r => (isAcc r) | _ => false) then
      some (enc as w false (w == .W64) false (1 + immW w))
    else some (rmForm as w 1 (rmLen a) (isMem a) false (immW w))

/-- `mov` with destination `d` and source `s` (no segment override). -/
def movLen (as : Width) {w : Width} (d : RegOrMem w) (s : Operand w) : Option Nat :=
  match d, s with
  | d, .regOrMem (.reg r) => some (rmForm as w 1 (rmLen d) (isMem d) (regRex r))
  | .reg r, .regOrMem (.mem m) => some (rmForm as w 1 (memLen m) true (regRex r))
  | .mem _, .regOrMem (.mem _) => none
  | .reg r, .imm c =>
    match w with
    | .W64 =>
      -- `C7 /0 imm32` when the value sign-extends from 32 bits (a symbol is
      -- assumed to), `movabs` (`B8+r imm64`) otherwise.
      if (constInt? c).all fits32 then some (enc as w false true (regRex r) 6)
      else some (enc as w false true (regRex r) 9)
    | _ => some (enc as w false false (regRex r) (1 + immW w))
  | .mem m, .imm _ => some (rmForm as w 1 (memLen m) true false (immW w))

/-- A shift or rotate by `c`: `D1` for a literal 1, `C1 ib` for another
immediate, `D3` for `%cl` (`D0`/`C0`/`D2` at 8 bits, same lengths). -/
def shiftLen (as : Width) {w : Width} (d : RegOrMem w) (c : ShiftCountExpr) : Nat :=
  match c with
  | .cl => rmForm as w 1 (rmLen d) (isMem d) false
  | .imm8 v => if constInt? v == some 1 then rmForm as w 1 (rmLen d) (isMem d) false
    else rmForm as w 1 (rmLen d) (isMem d) false 1

/-- `jmp`/`call` through a register or memory (`FF /4`, `FF /2`; no REX.W). -/
def indirLen (as : Width) : RelRegOrMem → Option Nat
  | .reg r => some (enc as .W64 false false (hi (match r with | .low r _ => r | _ => .rax)) 2)
  | .mem m => let l := memLen m; some (enc as .W64 true false l.2 (1 + l.1))
  | .rel _ => none

/-- The target label of a relative branch (`jcc l`, `jmp l`), or `none`. -/
def branchTarget : Directive → Option Label
  | .instr (.regular _ _ (.jcc _ l)) => some l
  | .instr (.regular _ _ (.jmp (.rel (.sub (.label l) .after_current_instruction)))) => some l
  | _ => none

/-- **The length of an operation**, `wide` choosing rel32 for `jcc`/`jmp`
to a label. -/
def opLen (as : Width) (wide : Bool) : {w : Width} → Operation w → Option Nat
  | _, .mov d s => movLen as d s
  | w, @Operation.movsx _ w' d s =>
    match d with
    | .reg r => if w' == .W32 then
        (if w == .W64 then some (rmForm as w 1 (rmLen s) (isMem s) (regRex r)) else none)
      else some (rmForm as w 2 (rmLen s) (isMem s) (regRex r))
    | .mem _ => none
  | w, @Operation.movzx _ w' d s =>
    match d with
    | .reg r => if w' == .W32 then none else some (rmForm as w 2 (rmLen s) (isMem s) (regRex r))
    | .mem _ => none
  | .W64, .push s => match s with
    | .regOrMem (.reg (.low r _)) => some (if hi r then 2 else 1)
    | .regOrMem (.mem m) => let l := memLen m; some (enc as .W64 true false l.2 (1 + l.1))
    | .imm c => some (if const8 c then 2 else 5)
    | _ => none
  | .W64, .pop d => match d with
    | .reg (.low r _) => some (if hi r then 2 else 1)
    | .mem m => let l := memLen m; some (enc as .W64 true false l.2 (1 + l.1))
    | _ => none
  | _, .push _ | _, .pop _ => none
  | w, .setcc _ d => some (enc as w (isMem d) false (rmLen d).2 (2 + (rmLen d).1))
  | w, .cmovcc _ r s => some (rmForm as w 2 (rmLen s) (isMem s) (regRex r))
  | w, .lea r a => some (rmForm as w 1 (memLen a) true (regRex r))
  | _, .add d s | _, .adc d s | _, .sub d s | _, .sbb d s
  | _, .and d s | _, .or d s | _, .xor d s => aluLen as d s
  | _, .cmp a b => aluLen as a b
  | w, .adcx r s | w, .adox r s =>
    some (1 + enc as w (isMem s) (w == .W64) ((rmLen s).2 || (regRex r)) (3 + (rmLen s).1))
  | w, .inc d | w, .dec d | w, .neg d | w, .not d
  | w, .mul d | w, .imul1 d | w, .div d | w, .idiv d => some (rmForm as w 1 (rmLen d) (isMem d) false)
  | _, .mulx .. => none
  | w, .imul none s1 s2 =>
    match s1, s2 with
    | .reg r, .regOrMem rm => some (rmForm as w 2 (rmLen rm) (isMem rm) (regRex r))
    | .reg r, .imm c => some (rmForm as w 1 (1, (regRex r)) false false (if const8 c then 1 else immW w))
    | _, _ => none
  | w, .imul (some (.reg r)) rm (.imm c) =>
    some (rmForm as w 1 (rmLen rm) (isMem rm) (regRex r) (if const8 c then 1 else immW w))
  | _, .imul _ _ _ => none
  | _, .test a b => testLen as a b
  | _, .shl d c | _, .shr d c | _, .sar d c | _, .rol d c
  | _, .ror d c | _, .rcl d c | _, .rcr d c => some (shiftLen as d c)
  | w, .shld d r c | w, .shrd d r c =>
    some (rmForm as w 2 (rmLen d) (isMem d) (regRex r) (match c with | .cl => 0 | .imm8 _ => 1))
  | w, .bswap r => some (enc as w false (w == .W64) (regRex r) 2)
  | w, .tzcnt r s | w, .popcnt r s => some (1 + rmForm as w 2 (rmLen s) (isMem s) (regRex r))
  | _, .jcc _ _ => some (if wide then 6 else 2)
  | _, .jmp t => match t with
    | .rel (.sub (.label _) .after_current_instruction) => some (if wide then 5 else 2)
    | .rel _ => none
    | t => indirLen as t
  | _, .call t => match t with
    | .rel (.sub (.label _) .after_current_instruction) => some 5
    | .rel _ => none
    | t => indirLen as t
  | _, .ret => some 1
  | _, .nop n => if n = 0 then none else some n
  | _, .nopalign _ _ => none
  | w, .lockBin _ m s => (aluLen as (.mem m : RegOrMem w) s).map (· + 1)
  | w, .lockUn _ m => some (1 + rmForm as w 1 (memLen m) true false)
  | w, .xchg r m =>
    match m with
    | .reg r' =>
      if w != .W8 && (isAcc r || isAcc r') then some (enc as w false (w == .W64) (regRex r || regRex r') 1)
      else some (rmForm as w 1 (1, (regRex r')) false (regRex r))
    | .mem a => some (rmForm as w 1 (memLen a) true (regRex r))
  | w, .xadd lock d r | w, .cmpxchg lock d r =>
    some ((if lock then 1 else 0) + rmForm as w 2 (rmLen d) (isMem d) (regRex r))
  | _, .mfence | _, .lfence | _, .sfence => some 3
  | w, .movnti m r => some (rmForm as w 2 (memLen m) true (regRex r))
  | _, .syscall | _, .ud2 => some 2
  | _, .movfs d s => (movLen as d s).map (· + 1)
  | w, .cqo => some (if w == .W8 then 0 else enc as w false (w == .W64) false 1)
  | _, .cmpfs a b => (aluLen as a b).map (· + 1)

/-! ## Directives and layouts -/

/-- **The padding of an alignment directive** to `k` bytes at `addr`. -/
def alignPad (addr k : Nat) : Nat := if k = 0 then 0 else (k - addr % k) % k

/-- **GNU `as`'s branch relaxation rule**: a `jcc`/`jmp` is short (rel8)
iff its displacement from the end of the 2-byte short form fits a signed
byte. -/
def branchShort (disp : Int) : Bool := fits8 disp

/-- **The length of a directive**, `wide` choosing rel32 for `jcc`/`jmp`;
labels are 0, a byte array its length; `none` for an alignment directive
(use `sizeAt`) and every unmodelled form. -/
def sizeOf : Directive → (wide : Bool) → Option Nat
  | .label _, _ => some 0
  | .byteArray bs, _ => some bs.size
  | .instr (.regular as _ op), wide => opLen as wide op
  | .instr (.avx ..), _ => none

/-- The length of a directive at address `addr`: `sizeOf`, and the padding
of an alignment directive without a maximum. -/
def sizeAt (addr : Nat) (d : Directive) (wide : Bool) : Option Nat :=
  match d with
  | .instr (.regular _ _ (.nopalign k none)) => some (alignPad addr k)
  | d => sizeOf d wide

/-- The label offsets of laid-out cells (from offset 0; first occurrence). -/
def labelOffsets (cells : List (Directive × Nat)) : Std.HashMap Label Nat := Id.run do
  let mut m : Std.HashMap Label Nat := {}
  let mut a := 0
  for (d, z) in cells do
    if let .label l := d then
      if !m.contains l then m := m.insert l a
    a := a + z
  return m

/-- **A size table against `sizeAt`**: for laid-out cells (each with the
assembler's length), every cell whose computed length differs, as
`(index, offset, directive, table length, computed length)`. A branch's
`wide` is gas's at this layout (`branchShort` of the distance to its
target; a label not in the cells is wide). Empty iff the table is what
these rules give at its own layout. -/
def checkCells (cells : List (Directive × Nat)) : List (Nat × Nat × Directive × Nat × Option Nat) := Id.run do
  let offs := labelOffsets cells
  let mut out := #[]
  let mut a := 0
  let mut i := 0
  for (d, z) in cells do
    let wide := match branchTarget d with
      | some l => match offs[l]? with
        | some t => !branchShort ((t : Int) - (a + 2 : Nat))
        | none => true
      | none => false
    let s := sizeAt a d wide
    if s != some z then out := out.push (i, a, d, z, s)
    a := a + z
    i := i + 1
  return out.toList

/-! ## Unit tests (lengths from GNU `as` 2.x, `objdump -d`) -/

private def r (x : Reg64) : Reg .W64 := .low x .W64
private def m (b : Reg64) (d : Int := 0) : AddrExpr :=
  { base := some (.reg b), idx := none, disp := .int64 (Int64.ofInt d) }
private def q (o : Operation .W64) : Directive := .instr (.regular .W64 .W64 o)
private def l32 (o : Operation .W32) : Directive := .instr (.regular .W64 .W32 o)
private def imm {w : Width} (n : Int) : Operand w := .imm (.int64 (Int64.ofInt n))

-- `movq %rax, -8(%rbp)`: 48 89 45 f8
#guard sizeOf (q (.mov (.mem (m .rbp (-8))) (.reg (r .rax)))) false == some 4
-- `movq -200(%rbp), %rcx`: 48 8b 8d 38 ff ff ff
#guard sizeOf (q (.mov (.reg (r .rcx)) (.regOrMem (.mem (m .rbp (-200)))))) false == some 7
-- `movq (%rsp), %rax`: 48 8b 04 24 ; `movq (%rbp), %rax`: 48 8b 45 00
#guard sizeOf (q (.mov (.reg (r .rax)) (.regOrMem (.mem (m .rsp))))) false == some 4
#guard sizeOf (q (.mov (.reg (r .rax)) (.regOrMem (.mem (m .rbp))))) false == some 4
-- `movq $5, %rcx`: 48 c7 c1 05 00 00 00 ; `movabsq $2^40, %rax`: 10 bytes
#guard sizeOf (q (.mov (.reg (r .rcx)) (imm 5))) false == some 7
#guard sizeOf (q (.mov (.reg (r .rax)) (imm (2 ^ 40)))) false == some 10
-- `movl $231, %eax`: b8 e7 00 00 00 ; `xorl %r10d, %r10d`: 45 31 d2
#guard sizeOf (l32 (.mov (.reg (.low .rax .W32)) (imm 231))) false == some 5
#guard sizeOf (l32 (.xor (.reg (.low .r10 .W32)) (.regOrMem (.reg (.low .r10 .W32))))) false == some 3
-- `subq $16, %rsp`: 48 83 ec 10 ; `subq $4096, %rsp`: 48 81 ec 00 10 00 00 ;
-- `addq $4096, %rax`: 48 05 00 10 00 00
#guard sizeOf (q (.sub (.reg (r .rsp)) (imm 16))) false == some 4
#guard sizeOf (q (.sub (.reg (r .rsp)) (imm 4096))) false == some 7
#guard sizeOf (q (.add (.reg (r .rax)) (imm 4096))) false == some 6
-- `pushq %rbp`: 55 ; `pushq %r12`: 41 54
#guard sizeOf (q (.push (.regOrMem (.reg (r .rbp))))) false == some 1
#guard sizeOf (q (.push (.regOrMem (.reg (r .r12))))) false == some 2
-- `movq %fs:0, %rax`: 64 48 8b 04 25 00 00 00 00
#guard sizeOf (q (.movfs (.reg (r .rax)) (.regOrMem (.mem { base := none, idx := none, disp := .int64 0 }))))
  false == some 9
-- `leaq sym(%rip), %rax`: 48 8d 05 <rel32>
#guard sizeOf (q (.lea (r .rax) { base := some .rip, idx := none, disp := .label "sym" })) false == some 7
-- `shlq %cl, %rax`: 48 d3 e0 ; `lock xaddq %rax, (%rcx)`: f0 48 0f c1 01
#guard sizeOf (q (.shl (.reg (r .rax)) .cl)) false == some 3
#guard sizeOf (q (.xadd true (.mem (m .rcx)) (r .rax))) false == some 5
-- `xchgq %rax, 16(%rcx)`: 48 87 41 10 ; `imulq %rcx, %rax`: 48 0f af c1
#guard sizeOf (q (.xchg (r .rax) (.mem (m .rcx 16)))) false == some 4
#guard sizeOf (q (.imul none (.reg (r .rax)) (.regOrMem (.reg (r .rcx))))) false == some 4
-- `je l`: 74 xx / 0f 84 <rel32> ; `jmp l`: eb xx / e9 <rel32> ; `call f`: e8 <rel32>
#guard sizeOf (q (.jcc .z "l")) false == some 2 && sizeOf (q (.jcc .z "l")) true == some 6
#guard sizeOf (q (.call (.rel (.sub (.label "f") .after_current_instruction)))) false == some 5
#guard sizeOf (q .ret) false == some 1 && sizeOf (q .syscall) false == some 2 && sizeOf (q .mfence) false == some 3
#guard branchShort 127 && !branchShort 128 && branchShort (-128) && !branchShort (-129)
#guard alignPad 13 16 == 3 && alignPad 16 16 == 0 && alignPad 5 1 == 0

end Scc.Emit.X64.Size
