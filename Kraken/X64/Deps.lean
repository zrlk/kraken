/-
Syntactic register dependencies of x64 instructions, for the weak-memory layer.
`Operation.deps` is total over the regular
operations and classifies every register an instruction reads or writes by
the role it plays, per the field docstrings of `Kraken.InstrDeps`: partial
registers map to their `Reg64`, the flags are the register `.rflags`. The
sequential semantics never consults this file.

Two reads are less than obvious; both are checked by `Kraken/X64/DepsTests.lean`,
which tests `deps` against `Operation.interp` per constructor:
- A write narrower than 32 bits merges into the 64-bit register (`mov %bl, %al`
  keeps the upper 56 bits of `rax`), so under `W8`/`W16` every written general
  register is also a data input (`mergePartial`).
- Shifts and rotates read the flags: a zero count leaves them unchanged, and
  the rotates update only `CF`/`OF`, so the new flags value depends on the old
  one.
-/
import Kraken.MemKinds
import Kraken.X64.Syntax

/-- A register identity for dependency tracking: a 64-bit general register
(partial registers fold into it), the flags, or a vector register (`xmm`/`ymm`
fold into their `zmm`). -/
inductive RegId
  | r (r : Reg64)
  | rflags
  | v (r : RegMm)
  deriving Repr, BEq, DecidableEq, Hashable

namespace RegId

/-- The identity of a (possibly partial) register. -/
def ofReg {w} : Reg w → RegId
  | .low b _ => .r b
  | .ah => .r .rax | .bh => .r .rbx | .ch => .r .rcx | .dh => .r .rdx

/-- The identity of a vector register: its `zmm`. -/
def ofAvx {w} : AvxReg w → RegId
  | .xmm b | .ymm b | .zmm b => .v b

end RegId

open Kraken (InstrDeps)

/-- The registers an address expression reads: base and index. A rip-relative
reference reads no register. -/
def AddrExpr.deps (a : AddrExpr) : List RegId :=
  (match a.base with | some (.reg r) => [RegId.r r] | _ => [])
  ++ (match a.idx with | some ⟨r, _⟩ => [RegId.r r] | none => [])

/-- Address registers of a register-or-memory operand. -/
def RegOrMem.addrRegs {w} : RegOrMem w → List RegId
  | .reg _ => []
  | .mem a => a.deps

/-- The register a register-or-memory operand names, as a data input or an
output; a memory operand names none. -/
def RegOrMem.reg? {w} : RegOrMem w → List RegId
  | .reg r => [RegId.ofReg r]
  | .mem _ => []

/-- Whether the operand is in memory. -/
def RegOrMem.isMem {w} : RegOrMem w → Bool
  | .reg _ => false
  | .mem _ => true

def Operand.addrRegs {w} : Operand w → List RegId
  | .regOrMem rm => rm.addrRegs
  | .imm _ => []

def Operand.reg? {w} : Operand w → List RegId
  | .regOrMem rm => rm.reg?
  | .imm _ => []

def Operand.isMem {w} : Operand w → Bool
  | .regOrMem rm => rm.isMem
  | .imm _ => false

def RelRegOrMem.addrRegs : RelRegOrMem → List RegId
  | .rel _ => []
  | .reg _ => []
  | .mem a => a.deps

def RelRegOrMem.reg? : RelRegOrMem → List RegId
  | .rel _ => []
  | .reg r => [RegId.ofReg r]
  | .mem _ => []

def ShiftCountExpr.deps : ShiftCountExpr → List RegId
  | .cl => [RegId.r .rcx]
  | .imm8 _ => []

namespace Operation

/-- The dependencies of a two-operand ALU instruction `op dst, src` that reads
and writes `dst`, reads `src` and writes the flags (`flags := true`). A
register destination is a data input and an ALU output; a memory destination
is read (the loaded value feeds no register, so it is not a `loadDef`) and
written with data from `src` and the old contents. -/
private def alu2 {w} (dst : RegOrMem w) (src : Operand w) (flags : Bool := true)
    (readsFlags : Bool := false) : InstrDeps RegId :=
  { addrRegs := dst.addrRegs ++ src.addrRegs
    dataRegs := dst.reg? ++ src.reg? ++ (if readsFlags then [.rflags] else [])
    defs := dst.reg? ++ (if flags then [.rflags] else []) }

/-- A one-operand ALU instruction that reads and writes `dst`. -/
private def alu1 {w} (dst : RegOrMem w) (flags : Bool := true) (readsFlags : Bool := false) :
    InstrDeps RegId :=
  { addrRegs := dst.addrRegs
    dataRegs := dst.reg? ++ (if readsFlags then [.rflags] else [])
    defs := dst.reg? ++ (if flags then [.rflags] else []) }

/-- A shift or rotate: `dst` as `alu1`, plus `cl` when it is the count. The
flags are read: a zero count leaves them unchanged, and the rotates write only
`CF`/`OF` (`rcl`/`rcr` also rotate through `CF`). -/
private def shift {w} (dst : RegOrMem w) (cnt : ShiftCountExpr) : InstrDeps RegId :=
  { addrRegs := dst.addrRegs
    dataRegs := dst.reg? ++ cnt.deps ++ [.rflags]
    defs := dst.reg? ++ [.rflags] }

/-- A move of `src` into `dst`: a register destination fed from memory is a
`loadDef`; from a register or an immediate, a `def`. A memory destination is a
store whose data is `src`. -/
private def move {w w'} (dst : RegOrMem w) (src : RegOrMem w') : InstrDeps RegId :=
  { addrRegs := dst.addrRegs ++ src.addrRegs
    dataRegs := src.reg?
    loadDefs := if src.isMem then dst.reg? else []
    defs := if src.isMem then [] else dst.reg? }

/-- A write narrower than 32 bits merges into the 64-bit register, so under
`W8`/`W16` every written general register is also read. -/
private def mergePartial (w : Width) (d : InstrDeps RegId) : InstrDeps RegId :=
  match w with
  | .W8 | .W16 => { d with dataRegs := d.dataRegs ++ (d.loadDefs ++ d.defs).filter (· != .rflags) }
  | .W32 | .W64 => d

/-- The syntactic dependencies of one operation, before `mergePartial`. -/
private def depsCore {w} : Operation w → InstrDeps RegId
  -- Data movement
  | .mov dst src => match src with
    | .regOrMem rm => move dst rm
    | .imm _ => { addrRegs := dst.addrRegs, defs := dst.reg? }
  | .movsx dst src => move dst src
  | .movzx dst src => move dst src
  | .push src =>
    { addrRegs := [.r .rsp] ++ src.addrRegs, dataRegs := src.reg?, defs := [.r .rsp] }
  | .pop dst =>
    { addrRegs := [.r .rsp] ++ dst.addrRegs, loadDefs := dst.reg?, defs := [.r .rsp] }
  | .setcc _ dst => { addrRegs := dst.addrRegs, condRegs := [.rflags], defs := dst.reg?, isPick := true }
  | .cmovcc _ dst src =>
    { addrRegs := src.addrRegs, dataRegs := [RegId.ofReg dst] ++ src.reg?,
      condRegs := [.rflags], loadDefs := if src.isMem then [RegId.ofReg dst] else [],
      defs := if src.isMem then [] else [RegId.ofReg dst], isPick := true }
  -- Arithmetic
  | .lea dst src => { dataRegs := src.deps, defs := [RegId.ofReg dst] }
  | .add dst src => alu2 dst src
  | .adc dst src => alu2 dst src (readsFlags := true)
  | .adcx dst src => alu2 (.reg dst) (.regOrMem src) (readsFlags := true)
  | .adox dst src => alu2 (.reg dst) (.regOrMem src) (readsFlags := true)
  | .inc dst => alu1 dst (readsFlags := true)   -- keeps `CF`
  | .dec dst => alu1 dst (readsFlags := true)
  | .neg dst => alu1 dst
  | .sub dst src => alu2 dst src
  | .sbb dst src => alu2 dst src (readsFlags := true)
  | .cmp a b =>
    { addrRegs := a.addrRegs ++ b.addrRegs, dataRegs := a.reg? ++ b.reg?, defs := [.rflags] }
  | .mul src =>
    { addrRegs := src.addrRegs, dataRegs := [.r .rax] ++ src.reg?,
      defs := [.r .rax, .r .rdx, .rflags] }
  | .mulx hi lo src =>
    { addrRegs := src.addrRegs, dataRegs := [.r .rdx] ++ src.reg?,
      defs := [RegId.ofReg hi, RegId.ofReg lo] }
  | .imul1 src =>
    { addrRegs := src.addrRegs, dataRegs := [.r .rax] ++ src.reg?,
      defs := [.r .rax, .r .rdx, .rflags] }
  | .imul dst src1 src2 =>
    let d := match dst with | some d => d | none => src1
    { addrRegs := d.addrRegs ++ src1.addrRegs ++ src2.addrRegs,
      dataRegs := src1.reg? ++ src2.reg?, defs := d.reg? ++ [.rflags] }
  -- Bitwise
  | .test a b =>
    { addrRegs := a.addrRegs ++ b.addrRegs, dataRegs := a.reg? ++ b.reg?, defs := [.rflags] }
  | .and dst src => alu2 dst src
  | .not dst => alu1 dst (flags := false)
  | .or dst src => alu2 dst src
  | .xor dst src => alu2 dst src
  | .shl dst cnt => shift dst cnt
  | .shr dst cnt => shift dst cnt
  | .sar dst cnt => shift dst cnt
  | .shld dst src cnt =>
    { addrRegs := dst.addrRegs, dataRegs := dst.reg? ++ [RegId.ofReg src] ++ cnt.deps ++ [.rflags],
      defs := dst.reg? ++ [.rflags] }
  | .shrd dst src cnt =>
    { addrRegs := dst.addrRegs, dataRegs := dst.reg? ++ [RegId.ofReg src] ++ cnt.deps ++ [.rflags],
      defs := dst.reg? ++ [.rflags] }
  | .rol dst cnt => shift dst cnt
  | .ror dst cnt => shift dst cnt
  | .rcl dst cnt => shift dst cnt
  | .rcr dst cnt => shift dst cnt
  | .bswap dst => { dataRegs := [RegId.ofReg dst], defs := [RegId.ofReg dst] }
  | .tzcnt dst src =>
    { addrRegs := src.addrRegs, dataRegs := src.reg?, defs := [RegId.ofReg dst, .rflags] }
  -- Control flow
  | .jcc _ _ => { condRegs := [.rflags], isBranch := true }
  | .jmp tgt => { addrRegs := tgt.addrRegs, dataRegs := tgt.reg? }
  | .call tgt =>
    { addrRegs := [.r .rsp] ++ tgt.addrRegs, dataRegs := tgt.reg?, defs := [.r .rsp] }
  | .ret => { addrRegs := [.r .rsp], defs := [.r .rsp] }
  | .nop _ | .nopalign _ _ => {}
  -- Atomics and barriers
  | .lockBin _ dst src =>
    { addrRegs := dst.deps ++ src.addrRegs, dataRegs := src.reg?, defs := [.rflags] }
  | .lockUn op dst =>
    { addrRegs := dst.deps,
      dataRegs := match op with | .inc | .dec => [.rflags] | .neg | .not => [],
      dataRegsPer := [],
      defs := match op with | .not => [] | _ => [.rflags] }
  | .xchg r m =>
    { addrRegs := m.addrRegs, dataRegs := [RegId.ofReg r] ++ m.reg?,
      loadDefs := if m.isMem then [RegId.ofReg r] else [],
      defs := if m.isMem then [] else [RegId.ofReg r] ++ m.reg? }
  | .xadd _ dst src =>
    { addrRegs := dst.addrRegs, dataRegs := [RegId.ofReg src] ++ dst.reg?,
      loadDefs := if dst.isMem then [RegId.ofReg src] else [],
      defs := (if dst.isMem then [] else [RegId.ofReg src] ++ dst.reg?) ++ [.rflags] }
  | .cmpxchg _ dst src =>
    { addrRegs := dst.addrRegs, dataRegs := [.r .rax, RegId.ofReg src] ++ dst.reg?,
      loadDefs := if dst.isMem then [.r .rax] else [],
      defs := (if dst.isMem then [] else [.r .rax] ++ dst.reg?) ++ [.rflags] }
  | .mfence | .lfence | .sfence => {}
  -- as `mov %src, (dst)`
  | .movnti dst src => move (w := w) (.mem dst) (.reg src)
  -- `syscall` halts the thread (`MachineData.pendingSyscall`): no register yet.
  | .syscall => {}
  -- `mov` with a `%fs:` memory operand: the dependencies of `mov`. The segment
  -- base `fsBase` is not a `RegId`, so the address registers are the operand's
  -- base and index only (it is no event's data, and the access is the event).
  | .movfs dst src => match src with
    | .regOrMem rm => move dst rm
    | .imm _ => { addrRegs := dst.addrRegs, defs := dst.reg? }
  -- `ud2` faults before any effect.
  | .ud2 => {}
  -- `div`/`idiv` read the dividend `rdx:rax` and the divisor and write the
  -- quotient, the remainder and the (undefined) flags; whether they fault
  -- depends on the same registers.
  | .div src | .idiv src =>
    { addrRegs := src.addrRegs, dataRegs := [.r .rax, .r .rdx] ++ src.reg?,
      defs := [.r .rax, .r .rdx, .rflags] }
  | .cqo => { dataRegs := [.r .rax], defs := [.r .rdx] }
  | .popcnt dst src =>
    { addrRegs := src.addrRegs, dataRegs := src.reg?, defs := [RegId.ofReg dst, .rflags] }
  -- `cmp` with a `%fs:` memory operand: the dependencies of `cmp` (`fsBase` is
  -- not a `RegId`; see `movfs`).
  | .cmpfs a b =>
    { addrRegs := a.addrRegs ++ b.addrRegs, dataRegs := a.reg? ++ b.reg?, defs := [.rflags] }

/-- The syntactic dependencies of one operation; see the file comment. -/
def deps {w} (op : Operation w) : InstrDeps RegId := mergePartial w (depsCore op)

end Operation

namespace AvxOperation

/-- Address registers of a vector register-or-memory operand. -/
private def addrRegs {w} : AvxRegOrMem w → List RegId
  | .mem a => a.deps
  | .avx _ => []

/-- The vector register an operand names; a memory operand names none. -/
private def reg? {w} : AvxRegOrMem w → List RegId
  | .avx r => [RegId.ofAvx r]
  | .mem _ => []

private def isMem {w} : AvxRegOrMem w → Bool
  | .avx _ => false
  | .mem _ => true

/-- A vector move `dst := src`, shaped like `Operation.move`. A legacy SSE
write to a register keeps the bits above the operation width, so with
`legacy` the destination register is also read (as `mergePartial` has it for
narrow general-register writes). -/
private def move {w} (dst src : AvxRegOrMem w) (legacy : Bool) : InstrDeps RegId :=
  { addrRegs := addrRegs dst ++ addrRegs src
    dataRegs := reg? src ++ (if legacy then reg? dst else [])
    loadDefs := if isMem src then reg? dst else []
    defs := if isMem src then [] else reg? dst }

/-- A legacy two-operand lane operation `dst := dst op src`. -/
private def alu2 {w} (dst src : AvxRegOrMem w) : InstrDeps RegId :=
  { addrRegs := addrRegs dst ++ addrRegs src
    dataRegs := reg? dst ++ reg? src
    defs := reg? dst }

/-- A VEX three-operand operation `dst := src1 op src2`; with `readsDst` the
old destination is a third input (`vfmadd231ps`). -/
private def alu3 {w} (dst src1 : AvxReg w) (src2 : AvxRegOrMem w) (readsDst : Bool := false) :
    InstrDeps RegId :=
  { addrRegs := addrRegs src2
    dataRegs := (if readsDst then [RegId.ofAvx dst] else []) ++ [RegId.ofAvx src1] ++ reg? src2
    defs := [RegId.ofAvx dst] }

/-- `zmm0`–`zmm15`, the registers `vzeroupper` rewrites (keeping their low
128 bits, so it also reads them). -/
private def lowVecs : List RegId :=
  [.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7, .mm8, .mm9, .mm10, .mm11, .mm12, .mm13,
    .mm14, .mm15].map RegId.v

/-- The syntactic dependencies of one vector operation. Vector registers are
`RegId.v` of their `zmm`; `cmpxchg16b` is the 16-byte sibling of
`Operation.cmpxchg`, and it writes only ZF, so it also reads the flags. -/
def deps {w} : AvxOperation w → InstrDeps RegId
  | .movups dst src | .movaps dst src | .movapd dst src | .movdqa dst src | .movdqu dst src =>
    move dst src (legacy := true)
  | .vmovups dst src | .vmovaps dst src | .vmovapd dst src | .vmovdqa dst src
  | .vmovdqu dst src => move dst src (legacy := false)
  | .subps dst src | .addps dst src | .mulps dst src | .xorps dst src => alu2 dst src
  | .vxorps dst src1 src2 | .vaddps dst src1 src2 | .vmulps dst src1 src2
  | .vshufps dst src1 src2 _ => alu3 dst src1 src2
  | .vfmadd231ps dst src1 src2 => alu3 dst src1 src2 (readsDst := true)
  | .vextractf128 dst src _ => { dataRegs := [RegId.ofAvx src], defs := [RegId.ofAvx dst] }
  | .vmovhlps dst src1 src2 | .vmovss dst src1 src2 | .vaddss dst src1 src2 =>
    { dataRegs := [RegId.ofAvx src1, RegId.ofAvx src2], defs := [RegId.ofAvx dst] }
  | .vzeroupper => { dataRegs := lowVecs, defs := lowVecs }
  | .cmpxchg16b _ dst =>
    { addrRegs := dst.deps, dataRegs := [.r .rax, .r .rdx, .r .rbx, .r .rcx, .rflags],
      loadDefs := [.r .rax, .r .rdx], defs := [.rflags] }

end AvxOperation

/-- Dependencies of an instruction. -/
def Instr.deps : Instr → InstrDeps RegId
  | .regular _ _ op => op.deps
  | .avx _ _ op => op.deps

def Directive.deps : Directive → InstrDeps RegId
  | .instr i => i.deps
  | .label _ | .byteArray _ => {}

/-- info: { addrRegs := [RegId.r (Reg64.rdi)],
  dataRegs := [],
  dataRegsPer := [],
  condRegs := [],
  loadDefs := [RegId.r (Reg64.rax)],
  statusDefs := [],
  defs := [],
  isBranch := false,
  isPick := false,
  casLike := false } -/
#guard_msgs in
#eval (Operation.mov (w := .W32) (.reg (.low .rax .W32)) (.mem ⟨some (.reg .rdi), none, .int64 0⟩)).deps

/-- info: { addrRegs := [RegId.r (Reg64.rsi), RegId.r (Reg64.rcx)],
  dataRegs := [RegId.r (Reg64.rbx)],
  dataRegsPer := [],
  condRegs := [],
  loadDefs := [],
  statusDefs := [],
  defs := [],
  isBranch := false,
  isPick := false,
  casLike := false } -/
#guard_msgs in
#eval (Operation.mov (w := .W64) (.mem ⟨some (.reg .rsi), some ⟨.rcx, .W64⟩, .int64 8⟩)
  (.reg (.low .rbx .W64))).deps

/-- info: { addrRegs := [],
  dataRegs := [RegId.r (Reg64.rax), RegId.r (Reg64.rax)],
  dataRegsPer := [],
  condRegs := [],
  loadDefs := [],
  statusDefs := [],
  defs := [RegId.r (Reg64.rax), RegId.rflags],
  isBranch := false,
  isPick := false,
  casLike := false } -/
#guard_msgs in
#eval (Operation.xor (w := .W32) (.reg (.low .rax .W32)) (.reg (.low .rax .W32))).deps

/-- info: { addrRegs := [],
  dataRegs := [],
  dataRegsPer := [],
  condRegs := [RegId.rflags],
  loadDefs := [],
  statusDefs := [],
  defs := [],
  isBranch := true,
  isPick := false,
  casLike := false } -/
#guard_msgs in
#eval (Operation.jcc (w := .W64) .nz "L").deps

/-- info: { addrRegs := [],
  dataRegs := [RegId.r (Reg64.rax), RegId.r (Reg64.rbx)],
  dataRegsPer := [],
  condRegs := [RegId.rflags],
  loadDefs := [],
  statusDefs := [],
  defs := [RegId.r (Reg64.rax)],
  isBranch := false,
  isPick := true,
  casLike := false } -/
#guard_msgs in
#eval (Operation.cmovcc (w := .W64) .z (.low .rax .W64) (.reg (.low .rbx .W64))).deps

/-- info: { addrRegs := [RegId.r (Reg64.rdi)],
  dataRegs := [RegId.r (Reg64.rax)],
  dataRegsPer := [],
  condRegs := [],
  loadDefs := [RegId.r (Reg64.rax)],
  statusDefs := [],
  defs := [RegId.rflags],
  isBranch := false,
  isPick := false,
  casLike := false } -/
#guard_msgs in
#eval (Operation.xadd (w := .W32) true (.mem ⟨some (.reg .rdi), none, .int64 0⟩) (.low .rax .W32)).deps

/-- info: { addrRegs := [RegId.r (Reg64.rdi)],
  dataRegs := [RegId.r (Reg64.rax), RegId.r (Reg64.rbx)],
  dataRegsPer := [],
  condRegs := [],
  loadDefs := [RegId.r (Reg64.rax)],
  statusDefs := [],
  defs := [RegId.rflags],
  isBranch := false,
  isPick := false,
  casLike := false } -/
#guard_msgs in
#eval (Operation.cmpxchg (w := .W32) true (.mem ⟨some (.reg .rdi), none, .int64 0⟩) (.low .rbx .W32)).deps

/-- info: { addrRegs := [RegId.r (Reg64.rdi)],
  dataRegs := [RegId.r (Reg64.rax)],
  dataRegsPer := [],
  condRegs := [],
  loadDefs := [RegId.r (Reg64.rax)],
  statusDefs := [],
  defs := [],
  isBranch := false,
  isPick := false,
  casLike := false } -/
#guard_msgs in
#eval (Operation.xchg (w := .W32) (.low .rax .W32) (.mem ⟨some (.reg .rdi), none, .int64 0⟩)).deps

-- A 16-bit move merges into `rax`, so `rax` is read as well as written; the
-- 32-bit form zero-extends and reads only its source.
/-- info: ([RegId.r (Reg64.rbx), RegId.r (Reg64.rax)], [RegId.r (Reg64.rbx)]) -/
#guard_msgs in
#eval
  let w16 := (Operation.mov (w := .W16) (.reg (.low .rax .W16)) (.reg (.low .rbx .W16))).deps
  let w32 := (Operation.mov (w := .W32) (.reg (.low .rax .W32)) (.reg (.low .rbx .W32))).deps
  (w16.dataRegs, w32.dataRegs)
