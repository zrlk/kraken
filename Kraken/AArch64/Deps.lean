/-
Syntactic register dependencies of AArch64 instructions, for the weak-memory
layer (`Kraken.InstrDeps`, see `Kraken/MemKinds.lean`). `Operation.deps` is total
over `Operation`; keep it in step with `Operation.interp` in `Semantics.lean`.

Conventions (from the `InstrDeps` field docstrings):
- A `W` register maps to its `X`; `XZR`/`WZR` is not a register; `SP` is `.sp`;
  the flags are `.nzcv`.
- Flag-setting operations put `.nzcv` in `defs`; `B.cond`, `CCMP`/`CCMN` and the
  `CSEL` family read it through `condRegs`; `ADC`/`SBC` read the carry as an ALU
  input (`dataRegs`).
- `CBZ`/`CBNZ`/`TBZ`/`TBNZ` put the tested register in `condRegs` with `isBranch`;
  indirect branches (`BR`, `BLR`, `RET`) do the same with their target.
- The `CSEL` family sets `isPick` with both sources in `dataRegs`.
- Loads put destinations in `loadDefs`, address registers in `addrRegs`, and a
  written-back base in `defs`; stores put their data in `dataRegs`. `STP` also
  lists each store's data separately in `dataRegsPer` (per-access data
  dependencies, as herd has them).
- `STXR`'s status register is in `statusDefs`. RMWs: `Rs` in `dataRegs`, `Rt` in
  `loadDefs`. For `CAS` (`casLike`), the comparand `Rs` is in `condRegs` (it
  orders the write without being its data) and in `loadDefs`; `Rt` is the data.
- The `CSEL` family lists both sources here; `Kraken/Promising/AArch64.lean`
  refines that per state to the selected source (`isPick`).

There is no lemma that every register `Operation.interp` reads/writes appears in
`Operation.deps`; `Kraken/AArch64/DepsTests.lean` checks it by testing, per
constructor, and the two functions are kept in the same case order by hand.
-/

import Kraken.AArch64.Syntax
import Kraken.MemKinds

/-- Register identity for dependency tracking: `X0`–`X30`, `SP`, and the flags. -/
inductive RegId
  | x (n : Fin 31)
  | sp
  | nzcv
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

namespace XReg
def idx : XReg → Fin 31
  |  X0 =>  0 |  X1 =>  1 |  X2 =>  2 |  X3 =>  3 |  X4 =>  4 |  X5 =>  5 |  X6 =>  6 |  X7 =>  7
  |  X8 =>  8 |  X9 =>  9 | X10 => 10 | X11 => 11 | X12 => 12 | X13 => 13 | X14 => 14 | X15 => 15
  | X16 => 16 | X17 => 17 | X18 => 18 | X19 => 19 | X20 => 20 | X21 => 21 | X22 => 22 | X23 => 23
  | X24 => 24 | X25 => 25 | X26 => 26 | X27 => 27 | X28 => 28 | X29 => 29 | X30 => 30
end XReg

/-- The registers a `RegOrZr` operand names (none for `XZR`/`WZR`). -/
def RegOrZr.regs {w} : RegOrZr w → List RegId
  | .low (.reg r) _ => [.x r.idx]
  | .low .XZR _ => []

/-- The registers a `RegOrSp` operand names. -/
def RegOrSp.regs {w} : RegOrSp w → List RegId
  | .low (.reg r) _ => [.x r.idx]
  | .low .SP _ => [.sp]

def RegOrZrW.regs (r : RegOrZrW) : List RegId := r.reg.regs

def ExtOrImmReg.regs : ExtOrImmReg → List RegId
  | .ext e => e.reg.regs
  | .imm _ => []

def ShiftRegExpr.regs {w} (e : ShiftRegExpr w) : List RegId := e.reg.regs

/-- Registers feeding the address of a memory operand. -/
def AddrExpr.addrRegs (a : AddrExpr) : List RegId :=
  a.base.regs ++ match a.off with
    | .reg r => r.reg.regs
    | .imm _ => []

/-- The base register if the addressing mode writes it back. -/
def AddrExpr.wbDefs (a : AddrExpr) : List RegId :=
  match a.off with
  | .imm { index := some _, .. } => a.base.regs
  | _ => []

def AddrOrLit.addrRegs : AddrOrLit → List RegId
  | .addr a => a.addrRegs
  | .lit _ => []

def AddrOrLit.wbDefs : AddrOrLit → List RegId
  | .addr a => a.wbDefs
  | .lit _ => []

def UnscaledAddrExpr.addrRegs (a : UnscaledAddrExpr) : List RegId := a.base.regs

namespace Operation
open Kraken (InstrDeps)

private def load {w} (dst : RegOrZr w) (src : AddrOrLit) : InstrDeps RegId :=
  { loadDefs := dst.regs, addrRegs := src.addrRegs, defs := src.wbDefs }
private def loadA {w} (dst : RegOrZr w) (src : AddrExpr) : InstrDeps RegId :=
  { loadDefs := dst.regs, addrRegs := src.addrRegs, defs := src.wbDefs }
private def loadU {w} (dst : RegOrZr w) (src : UnscaledAddrExpr) : InstrDeps RegId :=
  { loadDefs := dst.regs, addrRegs := src.addrRegs }
private def store {w} (src : RegOrZr w) (dst : AddrExpr) : InstrDeps RegId :=
  { dataRegs := src.regs, addrRegs := dst.addrRegs, defs := dst.wbDefs }
private def storeU {w} (src : RegOrZr w) (dst : UnscaledAddrExpr) : InstrDeps RegId :=
  { dataRegs := src.regs, addrRegs := dst.addrRegs }
/-- An ALU operation: `dst := f srcs`, optionally setting the flags. -/
private def alu (dst : List RegId) (srcs : List RegId) (flags : Bool := false) : InstrDeps RegId :=
  { dataRegs := srcs, defs := dst ++ (if flags then [.nzcv] else []) }
private def pick {w} (dst src1 src2 : RegOrZr w) : InstrDeps RegId :=
  { dataRegs := src1.regs ++ src2.regs, condRegs := [.nzcv], defs := dst.regs, isPick := true }
private def ccmp (srcs : List RegId) : InstrDeps RegId :=
  { dataRegs := srcs, condRegs := [.nzcv], defs := [.nzcv] }
private def condBranch (on : List RegId) : InstrDeps RegId :=
  { condRegs := on, isBranch := true }

/-- The syntactic register dependencies of an operation; see the file comment. -/
def deps {w} : Operation w → InstrDeps RegId
  | .LDR dst src => load dst src
  | .STR src dst => store src dst
  | .LDUR dst src => loadU dst src
  | .STUR src dst => storeU src dst
  | .LDP dst1 dst2 src => { loadDefs := dst1.regs ++ dst2.regs, addrRegs := src.addrRegs, defs := src.wbDefs }
  | .STP src1 src2 dst =>
    { dataRegs := src1.regs ++ src2.regs, dataRegsPer := [src1.regs, src2.regs],
      addrRegs := dst.addrRegs, defs := dst.wbDefs }
  | .LDRB dst src => loadA dst src
  | .LDURB dst src => loadU dst src
  | .STRB src dst => store src dst
  | .STURB src dst => storeU src dst
  | .LDRSB dst src => loadA dst src
  | .LDURSB dst src => loadU dst src
  | .LDRH dst src => loadA dst src
  | .LDURH dst src => loadU dst src
  | .STRH src dst => store src dst
  | .STURH src dst => storeU src dst
  | .LDRSH dst src => loadA dst src
  | .LDURSH dst src => loadU dst src
  | .LDRSW dst src => load dst src
  | .LDURSW dst src => loadU dst src
  | .LDPSW dst1 dst2 src => { loadDefs := dst1.regs ++ dst2.regs, addrRegs := src.addrRegs, defs := src.wbDefs }
  | .ADD_e dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .ADD_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .ADDS_e dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs) true
  | .ADDS_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs) true
  | .SUB_e dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .SUB_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .SUBS_e dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs) true
  | .SUBS_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs) true
  | .ADC dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs ++ [.nzcv])
  | .ADCS dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs ++ [.nzcv]) true
  | .SBC dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs ++ [.nzcv])
  | .SBCS dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs ++ [.nzcv]) true
  | .SDIV dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .UDIV dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .MADD dst src1 src2 src3 => alu dst.regs (src1.regs ++ src2.regs ++ src3.regs)
  | .MSUB dst src1 src2 src3 => alu dst.regs (src1.regs ++ src2.regs ++ src3.regs)
  | .SMULH dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .UMULH dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .SMADDL dst src1 src2 src3 => alu dst.regs (src1.regs ++ src2.regs ++ src3.regs)
  | .UMADDL dst src1 src2 src3 => alu dst.regs (src1.regs ++ src2.regs ++ src3.regs)
  | .SMSUBL dst src1 src2 src3 => alu dst.regs (src1.regs ++ src2.regs ++ src3.regs)
  | .UMSUBL dst src1 src2 src3 => alu dst.regs (src1.regs ++ src2.regs ++ src3.regs)
  | .AND_i dst src1 _ => alu dst.regs src1.regs
  | .AND_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .ANDS_i dst src1 _ => alu dst.regs src1.regs true
  | .ANDS_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs) true
  | .ORR_i dst src1 _ => alu dst.regs src1.regs
  | .ORR_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .ORN_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .EOR_i dst src1 _ => alu dst.regs src1.regs
  | .EOR_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .EON_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .BIC_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .BICS_s dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs) true
  | .BFM dst src _ _ => alu dst.regs (dst.regs ++ src.regs) -- BFM reads its destination
  | .SBFM dst src _ _ => alu dst.regs src.regs
  | .UBFM dst src _ _ => alu dst.regs src.regs
  | .CLZ dst src => alu dst.regs src.regs
  | .CLS dst src => alu dst.regs src.regs
  | .RBIT dst src => alu dst.regs src.regs
  | .REV dst src => alu dst.regs src.regs
  | .REV16 dst src => alu dst.regs src.regs
  | .REV32 dst src => alu dst.regs src.regs
  | .EXTR dst src1 src2 _ => alu dst.regs (src1.regs ++ src2.regs)
  | .MOVZ dst _ _ => alu dst.regs []
  | .MOVK dst _ _ => alu dst.regs dst.regs -- MOVK keeps the other halfwords
  | .MOVN dst _ _ => alu dst.regs []
  | .LSLV dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .LSRV dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .ASRV dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .RORV dst src1 src2 => alu dst.regs (src1.regs ++ src2.regs)
  | .CSEL dst src1 src2 _ => pick dst src1 src2
  | .CSINC dst src1 src2 _ => pick dst src1 src2
  | .CSINV dst src1 src2 _ => pick dst src1 src2
  | .CSNEG dst src1 src2 _ => pick dst src1 src2
  | .CCMP_reg src1 src2 _ _ => ccmp (src1.regs ++ src2.regs)
  | .CCMP_imm src1 _ _ _ => ccmp src1.regs
  | .CCMN_reg src1 src2 _ _ => ccmp (src1.regs ++ src2.regs)
  | .CCMN_imm src1 _ _ _ => ccmp src1.regs
  | .ADR dst _ => alu dst.regs []
  | .ADRP dst _ => alu dst.regs []
  | .B _ => {}
  | .B_cond _ _ => condBranch [.nzcv]
  | .BL _ => { defs := [.x XReg.X30.idx] }
  | .BLR target => { condRegs := target.regs, isBranch := true, defs := [.x XReg.X30.idx] }
  | .BR target => condBranch target.regs
  | .RET target => condBranch target.regs
  | .CBZ reg _ => condBranch reg.regs
  | .CBNZ reg _ => condBranch reg.regs
  | .TBZ reg _ _ => condBranch reg.regs
  | .TBNZ reg _ _ => condBranch reg.regs
  | .NOP => {}
  | .LDAR _ _ _ dst base => { loadDefs := dst.regs, addrRegs := base.regs }
  | .STLR _ src base => { dataRegs := src.regs, addrRegs := base.regs }
  -- The registers `STXR` reads; herd reads its data with `read_reg_ord`
  -- (`AArch64Sem.ml`, `stxr`), so `Kraken.Promising.AArch64.deps` drops them
  -- as dependencies.
  | .STXR _ _ status src base => { dataRegs := src.regs, addrRegs := base.regs, statusDefs := status.regs }
  | .CAS _ _ rs rt base => { dataRegs := rt.regs, condRegs := rs.regs, addrRegs := base.regs, loadDefs := rs.regs, casLike := true }
  | .SWP _ _ rs rt base => { dataRegs := rs.regs, addrRegs := base.regs, loadDefs := rt.regs }
  | .LDOP _ _ _ rs rt base => { dataRegs := rs.regs, addrRegs := base.regs, loadDefs := rt.regs }
  | .LDXP _ dst1 dst2 base => { loadDefs := dst1.regs ++ dst2.regs, addrRegs := base.regs }
  -- The registers `STXP` reads; herd reads its data with `read_reg_ord`
  -- (`AArch64Sem.ml`, `stxp`), so `Kraken.Promising.AArch64.deps` drops them
  -- as dependencies.
  | .STXP _ status src1 src2 base =>
    { dataRegs := src1.regs ++ src2.regs, dataRegsPer := [src1.regs, src2.regs], addrRegs := base.regs,
      statusDefs := status.regs }
  | .CASP _ rs1 rs2 rt1 rt2 base =>
    { dataRegs := rt1.regs ++ rt2.regs, condRegs := rs1.regs ++ rs2.regs, addrRegs := base.regs,
      loadDefs := rs1.regs ++ rs2.regs, casLike := true }
  | .DMB _ => {}
  | .DSB _ => {}
  | .ISB => {}
  -- `SVC` halts the thread (`MachineData.pendingSyscall`): it reads and writes no
  -- register yet. The system-call step will read `X8` and `X0`–`X5` and write `X0`.
  | .SVC _ => {}
  -- `TPIDR_EL0` is not a `RegId` (it is never an address or data register of a
  -- memory event): `MRS` defines `Xt` from no tracked register, `MSR` reads `Xt`
  -- and defines no tracked register. A dependency carried through `TPIDR_EL0` is
  -- therefore dropped, which only weakens the memory model's ordering.
  | .MRS dst _ => alu dst.regs []
  | .MSR _ src => alu [] src.regs

end Operation

def Instr.deps (i : Instr) : Kraken.InstrDeps RegId := i.operation.deps

/-- Labels and data blocks have no register dependencies. -/
def Directive.deps : Directive → Kraken.InstrDeps RegId
  | .instr i => i.deps
  | .label _ => {}
  | .byteArray _ => {}

-- Sanity checks.

/--
info: { addrRegs := [RegId.x 1, RegId.x 2],
  dataRegs := [],
  dataRegsPer := [],
  condRegs := [],
  loadDefs := [RegId.x 0],
  statusDefs := [],
  defs := [],
  isBranch := false,
  isPick := false,
  casLike := false }
-/
#guard_msgs in
#eval
  let addr : AddrExpr := { base := .X1, off := .reg { reg := ⟨.W32, .W2⟩, ext := { type := .SXTW, amount := .E0 } } }
  (Operation.LDR .W0 (.addr addr)).deps

-- Pre-indexed store: the base is both an address input and written back.
/--
info: { addrRegs := [RegId.sp],
  dataRegs := [RegId.x 3],
  dataRegsPer := [],
  condRegs := [],
  loadDefs := [],
  statusDefs := [],
  defs := [RegId.sp],
  isBranch := false,
  isPick := false,
  casLike := false }
-/
#guard_msgs in
#eval (Operation.STR .X3 { base := .SP, off := .imm { imm := .int64 (-16), index := some .Pre } }).deps

-- `EOR W2, W0, W0` keeps the dependency on `W0`; `CMP` (SUBS to WZR) defines only the flags.
/-- info: ([RegId.x 0, RegId.x 0], [RegId.x 2], [RegId.x 0], [RegId.nzcv]) -/
#guard_msgs in
#eval
  let eor := (Operation.EOR_s .W2 .W0 (.W0 : RegOrZr .W32)).deps
  let cmp := (Operation.SUBS_e .WZR .W0 (0 : ExtOrImmReg)).deps
  (eor.dataRegs, eor.defs, cmp.dataRegs, cmp.defs)

/-- info: (true, [RegId.nzcv], [RegId.x 1, RegId.x 3], true, [RegId.nzcv], true, [RegId.x 0]) -/
#guard_msgs in
#eval
  let csel := (Operation.CSEL .W1 .W1 .W3 .EQ).deps
  let beq := (Operation.B_cond .EQ (.label "over")).deps
  let cbz := (Operation.CBZ .W0 (.label "over")).deps
  (csel.isPick, csel.condRegs, csel.dataRegs, beq.isBranch, beq.condRegs, cbz.isBranch, cbz.condRegs)

/--
info: { addrRegs := [RegId.x 1],
  dataRegs := [RegId.x 3],
  dataRegsPer := [],
  condRegs := [],
  loadDefs := [],
  statusDefs := [RegId.x 4],
  defs := [],
  isBranch := false,
  isPick := false,
  casLike := false }
-/
#guard_msgs in
#eval (Operation.STXR .rel .W64 .W4 .X3 .X1).deps

-- `STP`: per-store data registers (`XZR` names none), their union in `dataRegs`.
/-- info: ([RegId.x 4, RegId.x 5], [[RegId.x 4], [RegId.x 5]], [], [[], [RegId.x 5]]) -/
#guard_msgs in
#eval
  let stp := (Operation.STP .X4 .X5 { base := .X0, off := .imm { imm := .int64 0, index := none } }).deps
  let stpz := (Operation.STP .WZR .W5 { base := .X0, off := .imm { imm := .int64 0, index := none } }).deps
  (stp.dataRegs, stp.dataRegsPer, (Operation.STR .X3 { base := .X0, off := .imm { imm := .int64 0, index := none } }).deps.dataRegsPer, stpz.dataRegsPer)

/-- info: ([RegId.x 1], [RegId.x 0], [RegId.x 0], [RegId.x 1], [RegId.x 0], []) -/
#guard_msgs in
#eval
  let cas := (Operation.CAS .acqRel .W32 .W0 .W1 .X2).deps
  let swp := (Operation.SWP .plain .W32 .W0 .W1 .X2).deps
  let stadd := (Operation.LDOP .ADD .rel .W32 .W0 .WZR .X2).deps
  (cas.dataRegs, cas.loadDefs, swp.dataRegs, swp.loadDefs, stadd.dataRegs, stadd.loadDefs)
