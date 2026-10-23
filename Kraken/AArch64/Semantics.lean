import Kraken.AArch64.Syntax
import Kraken.Attribute
import Kraken.Mem
import Lean
import Std

-- injective coercions only
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat

@[kstep] def BitVec.unsigned {w} (x : BitVec w) : Int := x.toNat
@[kstep] def BitVec.signed {w} (x : BitVec w) : Int := x.toInt
@[kstep] def BitVec.take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
@[kstep] def BitVec.drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)

attribute [kstep]
  BitVec.ofInt_add
  BitVec.ofInt_toInt
  BitVec.signed
  BitVec.truncate

namespace RegOrSp
@[kstep] def base {w} (r : RegOrSp w) : XRegOrSp := match r with
  | .low r _ => r
end RegOrSp

namespace RegOrZr
@[kstep] def base {w} (r : RegOrZr w) : XRegOrXzr := match r with
  | .low r _ => r
end RegOrZr

structure Reg64s where
  X0 : UInt64 := 0
  X1 : UInt64 := 0
  X2 : UInt64 := 0
  X3 : UInt64 := 0
  X4 : UInt64 := 0
  X5 : UInt64 := 0
  X6 : UInt64 := 0
  X7 : UInt64 := 0
  X8 : UInt64 := 0
  X9 : UInt64 := 0
  X10 : UInt64 := 0
  X11 : UInt64 := 0
  X12 : UInt64 := 0
  X13 : UInt64 := 0
  X14 : UInt64 := 0
  X15 : UInt64 := 0
  X16 : UInt64 := 0
  X17 : UInt64 := 0
  X18 : UInt64 := 0
  X19 : UInt64 := 0
  X20 : UInt64 := 0
  X21 : UInt64 := 0
  X22 : UInt64 := 0
  X23 : UInt64 := 0
  X24 : UInt64 := 0
  X25 : UInt64 := 0
  X26 : UInt64 := 0
  X27 : UInt64 := 0
  X28 : UInt64 := 0
  X29 : UInt64 := 0
  X30 : UInt64 := 0
  SP : UInt64 := 0
  /-- The thread pointer `TPIDR_EL0` (`MRS`/`MSR`): private to the thread like the
  general registers, no memory event, initially 0 (`Kraken/SYSCALL.md`). -/
  TPIDR_EL0 : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

@[kstep] def Reg64s.getXReg (s : Reg64s) (r : XReg) := match r with
  |  .X0 =>  s.X0 |  .X1 =>  s.X1 |  .X2 =>  s.X2 |  .X3 =>  s.X3
  |  .X4 =>  s.X4 |  .X5 =>  s.X5 |  .X6 =>  s.X6 |  .X7 =>  s.X7
  |  .X8 =>  s.X8 |  .X9 =>  s.X9 | .X10 => s.X10 | .X11 => s.X11
  | .X12 => s.X12 | .X13 => s.X13 | .X14 => s.X14 | .X15 => s.X15
  | .X16 => s.X16 | .X17 => s.X17 | .X18 => s.X18 | .X19 => s.X19
  | .X20 => s.X20 | .X21 => s.X21 | .X22 => s.X22 | .X23 => s.X23
  | .X24 => s.X24 | .X25 => s.X25 | .X26 => s.X26 | .X27 => s.X27
  | .X28 => s.X28 | .X29 => s.X29 | .X30 => s.X30

@[kstep] def Reg64s.getRegOrSp64 (s : Reg64s) (r : XRegOrSp) : RegWidth.W64.type := UInt64.toBitVec (match r with
  | .reg r => s.getXReg r
  | .SP => s.SP )

@[kstep] def Reg64s.getRegOrZr64 (s : Reg64s) (r : XRegOrXzr) : RegWidth.W64.type := UInt64.toBitVec (match r with
  | .reg r => s.getXReg r
  | .XZR => 0 ) -- Reads from XZR return constant 0.

@[kstep] def Reg64s.setXReg (regs : Reg64s) (r : XReg) (v : RegWidth.W64.type) : Reg64s :=
  let v := UInt64.ofBitVec v
  match r with
  |  .X0 => { regs with  X0 := v } |  .X1 => { regs with  X1 := v }
  |  .X2 => { regs with  X2 := v } |  .X3 => { regs with  X3 := v }
  |  .X4 => { regs with  X4 := v } |  .X5 => { regs with  X5 := v }
  |  .X6 => { regs with  X6 := v } |  .X7 => { regs with  X7 := v }
  |  .X8 => { regs with  X8 := v } |  .X9 => { regs with  X9 := v }
  | .X10 => { regs with X10 := v } | .X11 => { regs with X11 := v }
  | .X12 => { regs with X12 := v } | .X13 => { regs with X13 := v }
  | .X14 => { regs with X14 := v } | .X15 => { regs with X15 := v }
  | .X16 => { regs with X16 := v } | .X17 => { regs with X17 := v }
  | .X18 => { regs with X18 := v } | .X19 => { regs with X19 := v }
  | .X20 => { regs with X20 := v } | .X21 => { regs with X21 := v }
  | .X22 => { regs with X22 := v } | .X23 => { regs with X23 := v }
  | .X24 => { regs with X24 := v } | .X25 => { regs with X25 := v }
  | .X26 => { regs with X26 := v } | .X27 => { regs with X27 := v }
  | .X28 => { regs with X28 := v } | .X29 => { regs with X29 := v }
  | .X30 => { regs with X30 := v }

@[kstep] def Reg64s.setRegOrSp64 (regs : Reg64s) (r : XRegOrSp) (v : RegWidth.W64.type) : Reg64s :=
  match r with
  | .reg r => regs.setXReg r v
  | .SP => { regs with SP := UInt64.ofBitVec v }

@[kstep] def Reg64s.setRegOrZr64 (regs : Reg64s) (r : XRegOrXzr) (v : RegWidth.W64.type) : Reg64s :=
  match r with
  | .reg r => regs.setXReg r v
  | .XZR => regs -- Writes to XZR are dropped.

@[kstep] def Reg64s.getRegOrSp (s : Reg64s) {w} (r : RegOrSp w) : w.type :=
  (s.getRegOrSp64 r.base).take w.bits

@[kstep] def Reg64s.getRegOrZr (s : Reg64s) {w} (r : RegOrZr w) : w.type :=
  (s.getRegOrZr64 r.base).take w.bits

/-- Is the operand the zero register? (An atomic whose destination is `XZR`/`WZR`
is herd's `NoRet`; see `MachineData.rmwK`.) -/
@[kstep] def RegOrZr.isZr {w} (r : RegOrZr w) : Bool :=
  match r.base with
  | .XZR => true
  | .reg _ => false

@[kstep] def Reg64s.setRegOrSp (s : Reg64s) {w} (r : RegOrSp w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.setRegOrSp64 r v
  | .low r .W32 => s.setRegOrSp64 r (v.zeroExtend _)

@[kstep] def Reg64s.setRegOrZr (s : Reg64s) {w} (r : RegOrZr w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.setRegOrZr64 r v
  | .low r .W32 => s.setRegOrZr64 r (v.zeroExtend _)

structure StatusFlags where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

abbrev DataMem := Mem 64
instance : Repr DataMem where reprPrec _ _ := "<opaque memory>"
structure MachineData where -- does not include code or program position
  regs : Reg64s := {}
  status : StatusFlags := .mk false false false false
  dmem : DataMem := ∅
  deriving Repr, BEq, DecidableEq

-- We only allow nondeterministic choices for a fixed set of types.
class inductive NondetSupportingType : Type -> Type
  | bitvec (w : RegWidth) : NondetSupportingType w.type
  | bool : NondetSupportingType Bool
  | statusFlags : NondetSupportingType StatusFlags

def NondetSupportingType.from_hash {α} [t : NondetSupportingType α] (h : UInt64) : α :=
  match t with
  | .bool => h % 2 != 0
  | .statusFlags => let h := h.toBitVec; (.mk h[0] h[1] h[2] h[3])
  | .bitvec w => h.toBitVec.setWidth w.bits

instance (w : RegWidth) : NondetSupportingType w.type := .bitvec w
instance : NondetSupportingType Bool := .bool
instance : NondetSupportingType StatusFlags := .statusFlags

/-- A system call (`SVC #imm`) as the instruction leaves it to the kernel: the
immediate, the system-call number register `X8` and the argument registers
`X0`–`X5`, in order. Kraken attaches no meaning to them; they are what a kernel
model (a parameter of the certification semantics, see `Kraken/SYSCALL.md`)
consults. -/
structure SyscallInfo where
  imm : Nat
  num : BitVec 64
  args : List (BitVec 64)
  deriving Repr, BEq

inductive Effects
  | done (a : MachineData × Int64)
  | unimplemented (msg : String)
  -- loads and stores *outside* the data memory, eg. MMIO, might still affect the data memory:
  -- for instance, MMIO reads/writes at certain device register addresses might change what
  -- data memory the process logically owns vs what memory is owned by devices
  | nonmem_load (dmem : DataMem) (addr : BitVec 64) (w : MemWidth) (ret : w.type → DataMem → Effects)
  | nonmem_store (dmem : DataMem) (addr : BitVec 64) {w : MemWidth} (v : w.type) (ret: DataMem → Effects)
  | undefined {α : Type} [NondetSupportingType α] (ret : α → Effects)
  | require_read_access (addr : BitVec 64) (w : MemWidth) (ok : Unit → Effects)
  | require_write_access (addr : BitVec 64) (w : MemWidth) (ok : Unit → Effects)
  | require_exec_access (p: Std.Rco Int64) (ok : Unit → Effects)
  | unaligned_sp {w : RegWidth} (sp : w.type)
  -- Memory events of the weak-memory layer (`Kraken/MemKinds.lean`), emitted only for
  -- addresses *outside* the data memory, like `nonmem_load`/`nonmem_store` (which stay
  -- the plain-kind events). On mapped memory the instructions act sequentially; see
  -- `MachineData.loadK`/`storeK`/`rmwK`.
  | sync_load (k : Kraken.LoadKind) (xcl : Bool) (dmem : DataMem) (addr : BitVec 64) (w : MemWidth)
      (ret : w.type → DataMem → Effects)
  -- The `Bool` is store-exclusive success (always `true` for a non-exclusive store).
  | sync_store (k : Kraken.StoreKind) (xcl : Bool) (dmem : DataMem) (addr : BitVec 64) {w : MemWidth} (v : w.type)
      (ret : Bool → DataMem → Effects)
  -- Read-modify-write: `op old = none` means nothing is written (a failed `CAS` compare);
  -- `ret` receives the old value. `noRet`: the old value is discarded (the destination
  -- register is `XZR`/`WZR`: `ST<op>`, `LD<op>`/`SWP` to `XZR`, `CAS` with comparand `XZR`),
  -- herd's `NoRet` read, which `DMB LD`/`DSB LD` do not order and which loses its acquire
  -- annotation (see `MachineData.rmwK`). Only the weak-memory layer reads it.
  | rmw (k : Kraken.RmwKind) (noRet : Bool) (dmem : DataMem) (addr : BitVec 64) (w : MemWidth)
      (op : w.type → Option w.type) (ret : w.type → DataMem → Effects)
  | fence (k : Kraken.FenceKind) (ok : Unit → Effects)
  -- Pair accesses (`LDXP`/`LDAXP`, `STXP`/`STLXP`, `CASP*`) both of whose halves are
  -- outside the data memory: two `w`-sized accesses at `addr` and `addr + w.bytes`, the
  -- first register's half at the lower address. herd performs them as two accesses of one
  -- instruction, unordered with each other, with per-location atomicity; the weak-memory
  -- layer (`Kraken/Promising/AArch64.lean`) translates them so. A pair with one half in
  -- `dmem` uses the single-access effects on the other half (`MachineData.loadPairK`).
  -- Load pair of kind `k` (`xcl`: load-exclusive pair); `ret` receives both halves.
  | sync_load_pair (k : Kraken.LoadKind) (xcl : Bool) (dmem : DataMem) (addr : BitVec 64) (w : MemWidth)
      (ret : w.type → w.type → DataMem → Effects)
  -- Store pair of kind `k`: both halves are written or (a store-exclusive pair, `xcl`,
  -- failing) neither; the `Bool` is the success, always `true` when `xcl = false`.
  | sync_store_pair (k : Kraken.StoreKind) (xcl : Bool) (dmem : DataMem) (addr : BitVec 64) {w : MemWidth}
      (v1 v2 : w.type) (ret : Bool → DataMem → Effects)
  -- Compare-and-swap pair (`CASP`): if the halves hold `cmp1`, `cmp2`, write `new1`, `new2`,
  -- otherwise write nothing; `ret` receives the old halves.
  | rmw_pair (k : Kraken.RmwKind) (dmem : DataMem) (addr : BitVec 64) {w : MemWidth}
      (cmp1 cmp2 new1 new2 : w.type) (ret : w.type → w.type → DataMem → Effects)
  -- A system call (`MachineData.pendingSyscall`): `ret` continues after the
  -- instruction with the kernel's result in `X0`. Every consumer of the
  -- semantics treats it as the fault `unimplemented (pendingSyscallMsg info.imm)`
  -- except the certification adapter (`Kraken.Promising.AArch64.toEvCert`),
  -- which continues with each result a kernel-model parameter allows.
  | syscall (info : SyscallInfo) (ret : BitVec 64 → Effects)
export Effects (unimplemented nonmem_load nonmem_store undefined require_read_access require_write_access require_exec_access
  sync_load sync_store rmw fence sync_load_pair sync_store_pair rmw_pair)

-- the unused `Std.Rco Int64` argument and the unmodified `MachineData` return
-- value are present for uniformity with RegOrMem.interp
def RegOrSp.interp {w} (r : RegOrSp w) (s : MachineData) (_ : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) : Effects :=
  ret (s.regs.getRegOrSp r) s

def RegOrZr.interp {w} (r : RegOrZr w) (s : MachineData) (_ : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) : Effects :=
  ret (s.regs.getRegOrZr r) s

-- Since MMIO can cause devices to do arbitrary actions, a load might actually
-- *modify* memory. For instance:
-- A TEST instruction might load a flag from an MMIO address and bitwise-and it with
-- an immediate, and if the result is non-zero, it might mean that some device has
-- finished processing a buffer and therefore now passes ownership of that buffer
-- to the CPU.
-- Note that `ret` takes a whole `MachineData` instead of only `DataMem`, which
-- provides a bit more flexibility than we need: MachineData.load might change
-- dmem, but will not change the registers or status flags.
-- But this superfluous flexibility helps us simplify the state-threading:
-- Instead of writing `fun v dmem => ... { s with dmem } ...` everywhere, we
-- can just write `fun v s => ...` and the new `s` will shadow the old `s`.
def MachineData.load
  (s : MachineData) (addr : BitVec 64) (w : MemWidth)
  (ret : w.type → MachineData → Effects): Effects :=
  require_read_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some i => ret (.ofInt _ i) s
    | .none => nonmem_load s.dmem addr w (fun v dmem => ret v { s with dmem }))

def MachineData.store (s : MachineData) (addr : BitVec 64) {w : MemWidth} (v : w.type) (ret: MachineData → Effects) : Effects :=
  require_write_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some _ =>
        ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
    | .none => nonmem_store s.dmem addr v (fun dmem' => ret { s with dmem := dmem' }))

-- The kinded variants used by the acquire/release, exclusive and atomic
-- instructions. They follow the same mapped-first discipline as `load`/`store`:
-- a mapped address is served from `dmem` with plain sequential semantics, and
-- only an unmapped address reaches the weak-memory layer as a `sync_load`,
-- `sync_store` or `rmw` effect. Alignment of the access is not checked here.

/-- A load of kind `k` (`xcl`: load-exclusive). On mapped memory this is `load`. -/
def MachineData.loadK
  (s : MachineData) (k : Kraken.LoadKind) (xcl : Bool) (addr : BitVec 64) (w : MemWidth)
  (ret : w.type → MachineData → Effects): Effects :=
  require_read_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some i => ret (.ofInt _ i) s
    | .none => sync_load k xcl s.dmem addr w (fun v dmem => ret v { s with dmem }))

/-- A store of kind `k`; `ret` receives whether the store took place. A plain
(`xcl = false`) store always succeeds. A store-exclusive (`xcl = true`) on mapped
memory **may fail spuriously** (`undefined Bool`), as the architecture permits and
as herd7 and Promising-ARM model it: on `true` the value is written and success
reported, on `false` nothing is written. Unmapped exclusives emit `sync_store`
with `xcl := true` and let the handler decide. -/
def MachineData.storeK
  (s : MachineData) (k : Kraken.StoreKind) (xcl : Bool) (addr : BitVec 64) {w : MemWidth} (v : w.type)
  (ret : Bool → MachineData → Effects) : Effects :=
  require_write_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some _ =>
      let s' := { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
      if xcl then
        undefined (α := Bool) (fun ok => if ok then ret true s' else ret false s)
      else
        ret true s'
    | .none => sync_store k xcl s.dmem addr v (fun ok dmem' => ret ok { s with dmem := dmem' }))

/-- A read-modify-write of kind `k`: `ret` receives the old value; if
`op old = some new` then `new` is written, otherwise nothing is (a failed `CAS`
compare). On mapped memory this is a load followed by a store.

`noRet` marks herd's `NoRet` atomics (`AArch64Sem.ml`: `swp`, `cas`, `ldop`):
the instruction discards the value read, i.e. its destination is the zero
register — `Rt` for `SWP` and `LD<op>` (so every `ST<op>`), the comparand `Rs`
for `CAS` (`CASP` has none). herd then annotates the read `NoRet` in place of
its `A`/`X` annotation, whatever the `A`/`L` suffix: the read is not ordered by
`DMB LD`/`DSB LD` (`[(Exp & R) \ NoRet]` in `bob`/`DSB-ob` of
`aarch64hwreqs.cat`) and is never an acquire; the write keeps its annotation
(release for `L`/`AL`). The flag only reaches the weak-memory layer (`rmw`);
on mapped memory it is ignored. -/
def MachineData.rmwK
  (s : MachineData) (k : Kraken.RmwKind) (noRet : Bool) (addr : BitVec 64) (w : MemWidth)
  (op : w.type → Option w.type) (ret : w.type → MachineData → Effects) : Effects :=
  require_read_access addr w (fun _unit =>
  require_write_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some i =>
      let old : w.type := .ofInt _ i
      match op old with
      | .some new => ret old { s with dmem := Mem.storeInt s.dmem addr w.bytes new.toInt }
      | .none => ret old s
    | .none => rmw k noRet s.dmem addr w op (fun old dmem' => ret old { s with dmem := dmem' })))

-- The pair variants, for `LDXP`/`STXP`/`CASP` (and the LSE2 reading of `LDP`/`STP` in
-- `Kraken/Promising/AArch64.lean`): two `w`-sized halves at `addr` and `addr + w.bytes`,
-- each checked for access. Mapped-first per half: both halves in `dmem` act
-- sequentially; both outside it are one pair effect; one of each is the single-access
-- effect on the outside half, with the inside half served by `dmem` (so that the
-- merged link of `Kraken/Promising/SeqLinkAArch64.lean` holds for a pair that is half
-- private and half shared).

/-- A load pair of kind `k` (`xcl`: load-exclusive pair). On mapped memory this is
two loads. -/
def MachineData.loadPairK
  (s : MachineData) (k : Kraken.LoadKind) (xcl : Bool) (addr : BitVec 64) (w : MemWidth)
  (ret : w.type → w.type → MachineData → Effects) : Effects :=
  require_read_access addr w (fun _unit =>
  require_read_access (addr + w.bytesv) w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes, Mem.loadInt s.dmem (addr + w.bytesv) w.bytes with
    | .some i1, .some i2 => ret (.ofInt _ i1) (.ofInt _ i2) s
    | .none, .none => sync_load_pair k xcl s.dmem addr w (fun v1 v2 dmem => ret v1 v2 { s with dmem })
    | .some i1, .none =>
      sync_load k xcl s.dmem (addr + w.bytesv) w (fun v2 dmem => ret (.ofInt _ i1) v2 { s with dmem })
    | .none, .some i2 =>
      sync_load k xcl s.dmem addr w (fun v1 dmem => ret v1 (.ofInt _ i2) { s with dmem })))

/-- A store pair of kind `k`: both halves are written or neither. A
store-exclusive pair (`xcl`) on mapped memory **may fail spuriously**, as one
(`undefined Bool`), like `storeK`; `ret` receives the success. -/
def MachineData.storePairK
  (s : MachineData) (k : Kraken.StoreKind) (xcl : Bool) (addr : BitVec 64) {w : MemWidth} (v1 v2 : w.type)
  (ret : Bool → MachineData → Effects) : Effects :=
  require_write_access addr w (fun _unit =>
  require_write_access (addr + w.bytesv) w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes, Mem.loadInt s.dmem (addr + w.bytesv) w.bytes with
    | .some _, .some _ =>
      let s' := { s with dmem := Mem.storeInt (Mem.storeInt s.dmem addr w.bytes v1.toInt)
                                   (addr + w.bytesv) w.bytes v2.toInt }
      if xcl then
        undefined (α := Bool) (fun ok => if ok then ret true s' else ret false s)
      else
        ret true s'
    | .none, .none => sync_store_pair k xcl s.dmem addr v1 v2 (fun ok dmem => ret ok { s with dmem })
    | .some _, .none =>
      sync_store k xcl s.dmem (addr + w.bytesv) v2 (fun ok dmem =>
        if ok then ret true { s with dmem := Mem.storeInt dmem addr w.bytes v1.toInt }
        else ret false { s with dmem })
    | .none, .some _ =>
      sync_store k xcl s.dmem addr v1 (fun ok dmem =>
        if ok then ret true { s with dmem := Mem.storeInt dmem (addr + w.bytesv) w.bytes v2.toInt }
        else ret false { s with dmem })))

/-- A compare-and-swap pair of kind `k` (`CASP`): `ret` receives both old
halves; if they are `cmp1`, `cmp2`, then `new1`, `new2` are written, otherwise
nothing is. On mapped memory this is two loads followed by two stores. -/
def MachineData.rmwPairK
  (s : MachineData) (k : Kraken.RmwKind) (addr : BitVec 64) {w : MemWidth}
  (cmp1 cmp2 new1 new2 : w.type) (ret : w.type → w.type → MachineData → Effects) : Effects :=
  require_read_access addr w (fun _unit =>
  require_write_access addr w (fun _unit =>
  require_read_access (addr + w.bytesv) w (fun _unit =>
  require_write_access (addr + w.bytesv) w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes, Mem.loadInt s.dmem (addr + w.bytesv) w.bytes with
    | .some i1, .some i2 =>
      let o1 : w.type := .ofInt _ i1
      let o2 : w.type := .ofInt _ i2
      if o1 == cmp1 && o2 == cmp2 then
        ret o1 o2 { s with dmem := Mem.storeInt (Mem.storeInt s.dmem addr w.bytes new1.toInt)
                                     (addr + w.bytesv) w.bytes new2.toInt }
      else ret o1 o2 s
    | .none, .none => rmw_pair k s.dmem addr cmp1 cmp2 new1 new2 (fun o1 o2 dmem => ret o1 o2 { s with dmem })
    | .some i1, .none =>
      let o1 : w.type := .ofInt _ i1
      rmw k false s.dmem (addr + w.bytesv) w (fun o2 => if o1 == cmp1 && o2 == cmp2 then some new2 else none)
        (fun o2 dmem =>
          if o1 == cmp1 && o2 == cmp2 then ret o1 o2 { s with dmem := Mem.storeInt dmem addr w.bytes new1.toInt }
          else ret o1 o2 { s with dmem })
    | .none, .some i2 =>
      let o2 : w.type := .ofInt _ i2
      rmw k false s.dmem addr w (fun o1 => if o1 == cmp1 && o2 == cmp2 then some new1 else none)
        (fun o1 dmem =>
          if o1 == cmp1 && o2 == cmp2 then
            ret o1 o2 { s with dmem := Mem.storeInt dmem (addr + w.bytesv) w.bytes new2.toInt }
          else ret o1 o2 { s with dmem })))))

class Labels where label : Label → Int64
export Labels (label)

@[kstep] def ConstExpr.interp [Labels] : ConstExpr → Std.Rco Int64 → Int64
  | .label l, _ => Labels.label l
  | .int64 i, _ => i
  | .before_current_instruction, r => r.lower
  | .after_current_instruction, r => r.upper
  | .add e1 e2, p => e1.interp p + e2.interp p
  | .sub e1 e2, p => e1.interp p - e2.interp p
  | .pg_hi21 e, p =>
    let val := BitVec.ofInt 64 (Int64.toInt (e.interp p))
    let page := val &&& ~~~0xFFF#64
    Int64.ofNat page.toNat
  | .lo12 e, p =>
    let val := BitVec.ofInt 64 (Int64.toInt (e.interp p))
    let lo := val &&& 0xFFF#64
    Int64.ofNat lo.toNat

def ConstExpr.evalBranchTarget [Labels] (target : ConstExpr) (p : Std.Rco Int64) : Int64 :=
  match target with
  | .int64 imm => p.lower + imm
  | _ => target.interp p

@[kstep] def BitVec.apply_extend (v : BitVec 64) (ext : Extend) :=
  let extended := match ext.type with
               | .UXTB => (v.take MemWidth.W8.bits).unsigned
               | .SXTB => (v.take MemWidth.W8.bits).signed
               | .UXTH => (v.take MemWidth.W16.bits).unsigned
               | .SXTH => (v.take MemWidth.W16.bits).signed
               | .UXTW => (v.take MemWidth.W32.bits).unsigned
               | .SXTW => (v.take MemWidth.W32.bits).signed
               | .UXTX => v.unsigned
               | .SXTX => v.signed
  let shifted := match ext.amount with
                 | .E0 => extended
                 | .E1 => extended <<< 1
                 | .E2 => extended <<< 2
                 | .E3 => extended <<< 3
                 | .E4 => extended <<< 4
  shifted

@[kstep] def BitVec.apply_mem_extend (v : BitVec 64) (ext : MemExtend) :=
  let extended := match ext.type with
               | .UXTW => (v.take MemWidth.W32.bits).unsigned
               | .SXTW => (v.take MemWidth.W32.bits).signed
               | .UXTX => v.unsigned
               | .SXTX => v.signed
  let shifted := match ext.amount with
                 | .E0 => extended
                 | .E1 => extended <<< 1
                 | .E2 => extended <<< 2
                 | .E3 => extended <<< 3
  shifted

@[kstep] def ExtRegExpr.interp (er : ExtRegExpr) (s : Reg64s) (_ : Std.Rco Int64) :=
  let base := s.getRegOrZr er.reg.reg
  (base.take RegWidth.W64.bits).apply_extend er.ext

@[kstep] def MemExtRegExpr.interp (er : MemExtRegExpr) (s : Reg64s) (_ : Std.Rco Int64) :=
  let base := s.getRegOrZr er.reg.reg
  (base.take RegWidth.W64.bits).apply_mem_extend er.ext

@[kstep] def ExtOrImmReg.interp [Labels] {w : RegWidth} (expr : ExtOrImmReg) (s : Reg64s) (p : Std.Rco Int64) : w.type :=
  match expr with
  | .ext e =>
    BitVec.ofInt w.bits (e.interp s p)
  | .imm i =>
    let imm := Int64.toInt (i.imm.interp p)
    match i.shift with
    | .S0 => BitVec.ofInt w.bits (imm)
    | .S12 => BitVec.ofInt w.bits (imm <<< 12)

@[kstep] def ShiftRegExpr.interp {w} (expr : ShiftRegExpr w) (s : Reg64s) (_ : Std.Rco Int64) : w.type :=
  let base := s.getRegOrZr expr.reg
  let amount := (Int64.toInt expr.amount).toNat
  match expr.shift with
  | .LSL => base <<< amount
  | .LSR => base.ushiftRight amount
  | .ASR => base.sshiftRight amount
  | .ROR => base.rotateRight amount

@[kstep] def AddrExpr.eval [Labels] (mem : AddrExpr) (s : MachineData) (p : Std.Rco Int64) : BitVec 64 × MachineData :=
  let base := (s.regs.getRegOrSp mem.base).signed
  match mem.off with
  | .reg r =>
    let off := r.interp s.regs p
    (BitVec.ofInt 64 (base + off), s)
  | .imm i =>
    let off := Int64.toInt (i.imm.interp p)
    let addr := match i.index with
      | some .Post => BitVec.ofInt 64 base
      | _ => BitVec.ofInt 64 (base + off)
    let s' := match i.index with
      | some _ => { s with regs := s.regs.setRegOrSp mem.base (BitVec.ofInt 64 (base + off)) }
      | none => s
    (addr, s')

-- AArch64 mandates 16-byte alignment when accessing memory through SP.
@[kstep] def AddrExpr.checkSPAlignment (mem : AddrExpr) (s : MachineData) (ok : Unit → Effects) : Effects :=
  match mem.base with
  | .SP =>
    if s.regs.getRegOrSp .SP % 16#64 != 0#64 then
      .unaligned_sp (s.regs.getRegOrSp .SP)
    else
      ok ()
  | _ => ok ()

@[kstep] def AddrExpr.interpLoad [Labels] {w : MemWidth} (mem : AddrExpr) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :=
  mem.checkSPAlignment s (fun _unit =>
    let (addr, s') := mem.eval s p
    s'.load addr w ret)

@[kstep] def AddrExpr.interpStore [Labels] {w : MemWidth} (mem : AddrExpr) (s : MachineData) (p : Std.Rco Int64)
    (val : w.type) (next : MachineData → Effects) : Effects :=
  mem.checkSPAlignment s (fun _unit =>
    let (addr, s') := mem.eval s p
    s'.store addr (w := w) val next)

@[kstep] def UnscaledAddrExpr.eval [Labels] (mem : UnscaledAddrExpr) (s : MachineData) (p : Std.Rco Int64) : BitVec 64 :=
  let base := (s.regs.getRegOrSp mem.base).signed
  let off := Int64.toInt (mem.imm.interp p)
  BitVec.ofInt 64 (base + off)

-- AArch64 mandates 16-byte alignment when accessing memory through SP.
@[kstep] def UnscaledAddrExpr.checkSPAlignment (mem : UnscaledAddrExpr) (s : MachineData) (ok : Unit → Effects) : Effects :=
  match mem.base with
  | .SP =>
    if s.regs.getRegOrSp .SP % 16#64 != 0#64 then
      .unaligned_sp (s.regs.getRegOrSp .SP)
    else
      ok ()
  | _ => ok ()

@[kstep] def UnscaledAddrExpr.interpLoad [Labels] {w : MemWidth} (mem : UnscaledAddrExpr) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :=
  mem.checkSPAlignment s (fun _unit =>
    let addr := mem.eval s p
    s.load addr w ret)

@[kstep] def UnscaledAddrExpr.interpStore [Labels] {w : MemWidth} (mem : UnscaledAddrExpr) (s : MachineData) (p : Std.Rco Int64)
    (val : w.type) (next : MachineData → Effects) : Effects :=
  mem.checkSPAlignment s (fun _unit =>
    let addr := mem.eval s p
    s.store addr (w := w) val next)

@[kstep] def Literal.interpLoad [Labels] {w : MemWidth} (expr : Literal) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) : Effects :=
  match expr with
  | .addr addr_expr => -- Load from address.
    let addr_val := Labels.label addr_expr.label
    let addr := BitVec.ofInt 64 (Int64.toInt addr_val)
    s.load addr w ret
  | .pool litpool_expr => -- Bypass loading and return value directly.
    let val := litpool_expr.expr.interp p
    let val_bv : w.type := BitVec.ofInt w.bits (Int64.toInt val)
    ret val_bv s

@[kstep] def AddrOrLit.interpLoad [Labels] {w : MemWidth} (expr : AddrOrLit) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :=
  match expr with
  | .addr addr_expr => addr_expr.interpLoad s p ret
  | .lit lit_expr => lit_expr.interpLoad s p ret

/-- The address of a base-register-only memory operand `[Xn|SP]`, as used by the
acquire/release, exclusive and atomic instructions. AArch64 mandates 16-byte
alignment when accessing memory through SP. (No `let` for the address, so that
`kstep` leaves it as an expression in the goal, as for `AddrExpr`.) -/
@[kstep] def RegOrSp.interpBase (base : RegOrSp .W64) (s : MachineData) (ok : BitVec 64 → Effects) : Effects :=
  match base with
  | .SP =>
    if s.regs.getRegOrSp .SP % 16#64 != 0#64 then .unaligned_sp (s.regs.getRegOrSp .SP)
    else ok (s.regs.getRegOrSp .SP)
  | _ => ok (s.regs.getRegOrSp base)

/-- The arithmetic of an atomic load-and-op instruction: the new memory value
given the old one and the `Rs` operand. -/
@[kstep] def AtomicOp.apply {n} (op : AtomicOp) (old rs : BitVec n) : BitVec n :=
  match op with
  | .ADD => old + rs
  | .CLR => old &&& ~~~rs
  | .EOR => old ^^^ rs
  | .SET => old ||| rs
  | .SMAX => if old.slt rs then rs else old
  | .SMIN => if old.slt rs then old else rs
  | .UMAX => if old.ult rs then rs else old
  | .UMIN => if old.ult rs then old else rs

@[kstep] def MachineData.setRegOrSp (s : MachineData) {w} (r : RegOrSp w) (v : w.type) (ret : MachineData → Effects) : Effects :=
  ret { s with regs := s.regs.setRegOrSp r v }

@[kstep] def MachineData.setRegOrZr (s : MachineData) {w} (r : RegOrZr w) (v : w.type) (ret : MachineData → Effects) : Effects :=
  ret { s with regs := s.regs.setRegOrZr r v }

@[kstep, simp] def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .EQ => s.z
  | .NE => !s.z
  | .CS => s.c
  | .CC => !s.c
  | .MI => s.n
  | .PL => !s.n
  | .VS => s.v
  | .VC => !s.v
  | .HI => s.c && !s.z
  | .LS => !s.c || s.z
  | .GE => s.n == s.v
  | .LT => s.n != s.v
  | .GT => !s.z && s.n == s.v
  | .LE => s.z || s.n != s.v
  | .AL => true
  | .NV => true -- NV ("never") behaves the same as AL ("always") on AArch64

structure StatusFlags.from_result.Remaining where
  c : Bool
  v : Bool
  deriving Repr, BEq, DecidableEq

@[kstep, simp] def StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags :=
  { n := result.msb
    z := result == BitVec.zero _
    c := f.c
    v := f.v }

@[kstep, simp] def StatusFlags.adds {w} (res val1 val2 : BitVec w) : StatusFlags :=
  StatusFlags.from_result res {
    c := res.unsigned != val1.unsigned + val2.unsigned
    v := res.signed != val1.signed + val2.signed }

@[kstep, simp] def StatusFlags.subs {w} (res val1 val2 : BitVec w) : StatusFlags :=
  StatusFlags.from_result res {
    c := res.unsigned == val1.unsigned - val2.unsigned
    v := res.signed != val1.signed - val2.signed }

def StatusFlags.ofNat (nzcv : Nat) : StatusFlags :=
  { n := (nzcv &&& 8) != 0
    z := (nzcv &&& 4) != 0
    c := (nzcv &&& 2) != 0
    v := (nzcv &&& 1) != 0 }

@[kstep, simp] def maskOfLen {w : RegWidth} (len : Nat) : w.type :=
  if len >= w.bits then
    ~~~(0 : w.type)
  else
    ((1 : w.type) <<< len) - 1

@[kstep, simp] def evalUBFM {w : RegWidth} (src : w.type) (immr imms : Nat) : w.type :=
  let immr := immr % w.bits
  let imms := imms % w.bits
  if imms >= immr then
    let len := imms - immr + 1
    let field := (src >>> immr).take len
    field.zeroExtend w.bits
  else
    let len := imms + 1
    let pos := w.bits - immr
    let field := src.take len
    (field.zeroExtend w.bits) <<< pos

@[kstep, simp] def evalSBFM {w : RegWidth} (src : w.type) (immr imms : Nat) : w.type :=
  let immr := immr % w.bits
  let imms := imms % w.bits
  if imms >= immr then
    let len := imms - immr + 1
    let field := (src >>> immr).take len
    field.signExtend w.bits
  else
    let len := imms + 1
    let pos := w.bits - immr
    let field := src.take len
    (field.signExtend (w.bits - pos)).zeroExtend w.bits <<< pos

@[kstep, simp] def evalBFM {w : RegWidth} (dst src : w.type) (immr imms : Nat) : w.type :=
  let immr := immr % w.bits
  let imms := imms % w.bits
  if imms >= immr then
    let len := imms - immr + 1
    let mask : w.type := maskOfLen (w := w) len
    let field := (src >>> immr) &&& mask
    (dst &&& ~~~mask) ||| field
  else
    let len := imms + 1
    let pos := w.bits - immr
    let mask : w.type := (maskOfLen (w := w) len) <<< pos
    let field : w.type := (src &&& maskOfLen (w := w) len) <<< pos
    (dst &&& ~~~mask) ||| field

/-- The value of a system register (`MRS`). -/
@[kstep] def Reg64s.getSysReg (s : Reg64s) : SysReg → BitVec 64
  | .TPIDR_EL0 => s.TPIDR_EL0.toBitVec

/-- Write a system register (`MSR`). -/
@[kstep] def Reg64s.setSysReg (s : Reg64s) (sr : SysReg) (v : BitVec 64) : Reg64s :=
  match sr with
  | .TPIDR_EL0 => { s with TPIDR_EL0 := UInt64.ofBitVec v }

/-- The message of the halt at a supervisor call (`pendingSyscall`). -/
def pendingSyscallMsg (imm : Nat) : String := s!"pending system call: svc #{imm}"

/-- **The system-call step: the extension point.** `SVC #imm` with the machine
state `s` and the continuation `next` (the state after the instruction).

The step is the effect `Effects.syscall` with the immediate, `X8` and
`X0`–`X5`, continuing with `next` from `s` with the kernel's result in `X0`
(every other register, the flags and the private memory unchanged). There is
no kernel model in Kraken: every consumer but one treats the effect as the
distinguished status `unimplemented (pendingSyscallMsg imm)`, with no memory
effect. The sequential evaluator reports it as that error, the program logics
can prove nothing past it, and the Promising adapter
(`Kraken.Promising.AArch64.toEv`) makes it a fault with that message. The
certification adapter (`toEvCert`) continues with every result a kernel-model
parameter allows. A real step (trace events for `write`/`exit_group`, `clone`,
`futex`) replaces this one definition. See `Kraken/SYSCALL.md`. -/
def MachineData.pendingSyscall (s : MachineData) (imm : Nat) (next : MachineData → Effects) :
    Effects :=
  let x (r : XReg) : BitVec 64 := (s.regs.getXReg r).toBitVec
  .syscall { imm, num := x .X8, args := [x .X0, x .X1, x .X2, x .X3, x .X4, x .X5] }
    (fun r => next { s with regs := s.regs.setXReg .X0 r })

set_option maxHeartbeats 1000000
@[kstep] def Operation.interp [Labels]
  {w} (i : Operation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match (generalizing := false) (motive := Operation w → Effects) i with
  | .LDR dst src => src.interpLoad s p (fun val s => s.setRegOrZr dst val next)
  | .STR src dst => dst.interpStore s p (s.regs.getRegOrZr src) next
  | .LDUR dst src => src.interpLoad s p (fun val s => s.setRegOrZr dst val next)
  | .STUR src dst => dst.interpStore s p (s.regs.getRegOrZr src) next
  -- TODO: Architecturally, the memory access ordering of LDP/STP is UNORDERED and can occur
  -- simultaneously as a 128-bit transaction or in any order on hardware. Here we model a specific
  -- sequential order (lower address first, then higher address), which does not necessarily reflect
  -- physical execution order on device memory. (Note: unpredictable cases like identical transfer
  -- registers in LDP or writeback conflicts are statically rejected during parsing).
  | .LDP dst1 dst2 src =>
    src.checkSPAlignment s (fun _unit =>
      let (addr, s') := src.eval s p
      s'.load addr w (fun val1 s'' =>
        s''.load (addr + w.bytesv) w (fun val2 s''' =>
          s'''.setRegOrZr dst1 val1 (fun s'''' =>
            s''''.setRegOrZr dst2 val2 next))))
  | .STP src1 src2 dst =>
    dst.checkSPAlignment s (fun _unit =>
      let val1 := s.regs.getRegOrZr src1
      let val2 := s.regs.getRegOrZr src2
      let (addr, s') := dst.eval s p
      s'.store addr val1 (fun s'' =>
        s''.store (addr + w.bytesv) val2 next))
  | .LDRB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .LDURB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .STRB src dst =>
    dst.interpStore (w := .W8) s p ((s.regs.getRegOrZr src).take MemWidth.W8.bits) next
  | .STURB src dst =>
    dst.interpStore (w := .W8) s p ((s.regs.getRegOrZr src).take MemWidth.W8.bits) next
  | .LDRSB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDURSB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDRH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .LDURH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .STRH src dst =>
    dst.interpStore (w := .W16) s p ((s.regs.getRegOrZr src).take MemWidth.W16.bits) next
  | .STURH src dst =>
    dst.interpStore (w := .W16) s p ((s.regs.getRegOrZr src).take MemWidth.W16.bits) next
  | .LDRSH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDURSH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDRSW dst src =>
    src.interpLoad (w := .W32) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend RegWidth.W64.bits) next)
  | .LDURSW dst src =>
    src.interpLoad (w := .W32) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend RegWidth.W64.bits) next)
  | .LDPSW dst1 dst2 src =>
    src.checkSPAlignment s (fun _unit =>
      let (addr, s') := src.eval s p
      s'.load addr .W32 (fun val1 s'' =>
        s''.load (addr + MemWidth.W32.bytesv) .W32 (fun val2 s''' =>
          s'''.setRegOrZr dst1 (val1.signExtend RegWidth.W64.bits) (fun s'''' =>
            s''''.setRegOrZr dst2 (val2.signExtend RegWidth.W64.bits) next))))
  | .ADD_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    s.setRegOrSp dst res next
  | .ADD_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    s.setRegOrZr dst res next
  | .ADDS_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    { s with status := StatusFlags.adds res val1 val2 }.setRegOrZr dst res next
  | .ADDS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    { s with status := StatusFlags.adds res val1 val2 }.setRegOrZr dst res next
  | .SUB_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    s.setRegOrSp dst res next
  | .SUB_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    s.setRegOrZr dst res next
  | .SUBS_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    { s with status := StatusFlags.subs res val1 val2 }.setRegOrZr dst res next
  | .SUBS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    { s with status := StatusFlags.subs res val1 val2 }.setRegOrZr dst res next
  | .ADC dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let carry : w.type := s.status.c
    let res := val1 + val2 + carry
    s.setRegOrZr dst res next
  | .ADCS dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let carry : w.type := s.status.c
    let res := val1 + val2 + carry
    let carry_int : Int := if s.status.c then 1 else 0
    let status := StatusFlags.from_result res {
      c := res.unsigned != val1.unsigned + val2.unsigned + carry_int
      v := res.signed != val1.signed + val2.signed + carry_int }
    { s with status }.setRegOrZr dst res next
  | .SBC dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let borrow : w.type := !s.status.c
    let res := val1 - val2 - borrow
    s.setRegOrZr dst res next
  | .SBCS dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let borrow : w.type := !s.status.c
    let res := val1 - val2 - borrow
    let borrow_int : Int := if s.status.c then 0 else 1
    let status := StatusFlags.from_result res {
      c := val1.unsigned >= val2.unsigned + borrow_int
      v := res.signed != val1.signed - val2.signed - borrow_int }
    { s with status }.setRegOrZr dst res next
  | .MADD dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := val1 * val2 + val3
    s.setRegOrZr dst res next
  | .MSUB dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := val3 - val1 * val2
    s.setRegOrZr dst res next
  | .SMULH dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let prod := val1.signed * val2.signed
    let res := (BitVec.ofInt (RegWidth.W64.bits + RegWidth.W64.bits) prod).extractLsb' RegWidth.W64.bits RegWidth.W64.bits
    s.setRegOrZr dst res next
  | .UMULH dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let prod := val1.unsigned * val2.unsigned
    let res := (BitVec.ofInt (RegWidth.W64.bits + RegWidth.W64.bits) prod).extractLsb' RegWidth.W64.bits RegWidth.W64.bits
    s.setRegOrZr dst res next
  | .SDIV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let res := if val2 == 0 then (0 : w.type) else val1.sdiv val2
    s.setRegOrZr dst res next
  | .UDIV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let res := if val2 == 0 then (0 : w.type) else val1 / val2
    s.setRegOrZr dst res next
  | .SMADDL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val1.signed * val2.signed + val3.signed)
    s.setRegOrZr dst res next
  | .UMADDL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val1.unsigned * val2.unsigned + val3.unsigned)
    s.setRegOrZr dst res next
  | .SMSUBL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val3.signed - val1.signed * val2.signed)
    s.setRegOrZr dst res next
  | .UMSUBL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val3.unsigned - val1.unsigned * val2.unsigned)
    s.setRegOrZr dst res next
  | .AND_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 &&& val2
    s.setRegOrSp dst res next
  | .AND_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& val2
    s.setRegOrZr dst res next
  | .ANDS_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 &&& val2
    let flags := StatusFlags.from_result res { c := false, v := false }
    { s with status := flags }.setRegOrZr dst res next
  | .ANDS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& val2
    let flags := StatusFlags.from_result res { c := false, v := false }
    { s with status := flags }.setRegOrZr dst res next
  | .ORR_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 ||| val2
    s.setRegOrSp dst res next
  | .ORR_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ||| val2
    s.setRegOrZr dst res next
  | .ORN_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ||| ~~~val2
    s.setRegOrZr dst res next
  | .EOR_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 ^^^ val2
    s.setRegOrSp dst res next
  | .EOR_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ^^^ val2
    s.setRegOrZr dst res next
  | .BIC_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& ~~~val2
    s.setRegOrZr dst res next
  | .EON_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ^^^ ~~~val2
    s.setRegOrZr dst res next
  | .BICS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& ~~~val2
    let status' := StatusFlags.from_result res { c := false, v := false }
    { s with status := status' }.setRegOrZr dst res next
  | .BFM dst src immr imms =>
    let val_dst := s.regs.getRegOrZr dst
    let val_src := s.regs.getRegOrZr src
    let res := evalBFM val_dst val_src immr imms
    s.setRegOrZr dst res next
  | .SBFM dst src immr imms =>
    let val_src := s.regs.getRegOrZr src
    let res := evalSBFM val_src immr imms
    s.setRegOrZr dst res next
  | .UBFM dst src immr imms =>
    let val_src := s.regs.getRegOrZr src
    let res := evalUBFM val_src immr imms
    s.setRegOrZr dst res next
  | .CLZ dst src =>
    let val := s.regs.getRegOrZr src
    s.setRegOrZr dst val.clz next
  | .CLS dst src =>
    let val := s.regs.getRegOrZr src
    let res := (if val.msb then (~~~val).clz else val.clz) - 1#w.bits
    s.setRegOrZr dst res next
  | .RBIT dst src =>
    let val := s.regs.getRegOrZr src
    s.setRegOrZr dst val.reverse next
  | .REV dst src =>
    let val := s.regs.getRegOrZr src
    let res : w.type := match w, val with
      | .W32, v =>
        let step1 := ((v &&& 0x00FF00FF#32) <<< 8) ||| ((v &&& 0xFF00FF00#32) >>> 8)
        ((step1 &&& 0x0000FFFF#32) <<< 16) ||| ((step1 &&& 0xFFFF0000#32) >>> 16)
      | .W64, v =>
        let step1 := ((v &&& 0x00FF00FF00FF00FF#64) <<< 8) ||| ((v &&& 0xFF00FF00FF00FF00#64) >>> 8)
        let step2 := ((step1 &&& 0x0000FFFF0000FFFF#64) <<< 16) ||| ((step1 &&& 0xFFFF0000FFFF0000#64) >>> 16)
        ((step2 &&& 0x00000000FFFFFFFF#64) <<< 32) ||| ((step2 &&& 0xFFFFFFFF00000000#64) >>> 32)
    s.setRegOrZr dst res next
  | .REV16 dst src =>
    let val := s.regs.getRegOrZr src
    let res := ((val &&& 0x00FF00FF00FF00FF#w.bits) <<< 8) ||| ((val &&& 0xFF00FF00FF00FF00#w.bits) >>> 8)
    s.setRegOrZr dst res next
  | .REV32 dst src =>
    let val := s.regs.getRegOrZr src
    let step1 := ((val &&& 0x00FF00FF00FF00FF#64) <<< 8) ||| ((val &&& 0xFF00FF00FF00FF00#64) >>> 8)
    let res := ((step1 &&& 0x0000FFFF0000FFFF#64) <<< 16) ||| ((step1 &&& 0xFFFF0000FFFF0000#64) >>> 16)
    s.setRegOrZr dst res next
  | .EXTR dst src1 src2 lsb =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let lsb := lsb % w.bits
    let res := if lsb == 0 then val2 else (val1 <<< (w.bits - lsb)) ||| (val2 >>> lsb)
    s.setRegOrZr dst res next
  | .MOVZ dst imm shift =>
    let val16 := (BitVec.ofInt w.bits (Int64.toInt (imm.interp p))) &&& 0xFFFF#w.bits
    let res := val16 <<< shift.toNat
    s.setRegOrZr dst res next
  | .MOVK dst imm shift =>
    let oldVal := s.regs.getRegOrZr dst
    let mask := ~~~(0xFFFF#w.bits <<< shift.toNat)
    let val16 := (BitVec.ofInt w.bits (Int64.toInt (imm.interp p))) &&& 0xFFFF#w.bits
    let res := (oldVal &&& mask) ||| (val16 <<< shift.toNat)
    s.setRegOrZr dst res next
  | .MOVN dst imm shift =>
    let val16 := (BitVec.ofInt w.bits (Int64.toInt (imm.interp p))) &&& 0xFFFF#w.bits
    let res := ~~~(val16 <<< shift.toNat)
    s.setRegOrZr dst res next
  | .LSLV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1 <<< shift
    s.setRegOrZr dst res next
  | .LSRV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1.ushiftRight shift
    s.setRegOrZr dst res next
  | .ASRV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1.sshiftRight shift
    s.setRegOrZr dst res next
  | .RORV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1.rotateRight shift
    s.setRegOrZr dst res next
  | .CSEL dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else s.regs.getRegOrZr src2
    s.setRegOrZr dst val next
  | .CSINC dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else s.regs.getRegOrZr src2 + 1#w.bits
    s.setRegOrZr dst val next
  | .CSINV dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else ~~~(s.regs.getRegOrZr src2)
    s.setRegOrZr dst val next
  | .CSNEG dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else -(s.regs.getRegOrZr src2)
    s.setRegOrZr dst val next
  | .CCMP_reg src1 src2 nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := s.regs.getRegOrZr src2
        let res := val1 - val2
        StatusFlags.subs res val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .CCMP_imm src1 imm nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := BitVec.ofNat w.bits imm
        let res := val1 - val2
        StatusFlags.subs res val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .CCMN_reg src1 src2 nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := s.regs.getRegOrZr src2
        let res := val1 + val2
        StatusFlags.adds res val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .CCMN_imm src1 imm nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := BitVec.ofNat w.bits imm
        let res := val1 + val2
        StatusFlags.adds res val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .ADR dst target =>
    let val := match target with
      | .int64 imm => BitVec.ofInt 64 (Int64.toInt p.lower + Int64.toInt imm)
      | _ => BitVec.ofInt 64 (Int64.toInt (target.interp p))
    s.setRegOrZr dst val next
  | .ADRP dst target =>
    let val := match target with
      | .int64 imm => BitVec.ofInt 64 (Int64.toInt p.lower + Int64.toInt imm)
      | _ => BitVec.ofInt 64 (Int64.toInt (target.interp p))
    s.setRegOrZr dst (val &&& ~~~0xFFF#64) next
  | .B target =>
    jmp (target.evalBranchTarget p) s
  | .B_cond cond target =>
    if cond.interp s.status then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .BL target =>
    let lr_val := BitVec.ofInt 64 (Int64.toInt p.upper)
    s.setRegOrZr RegOrZr.X30 lr_val (fun s' => jmp (target.evalBranchTarget p) s')
  | .BLR target =>
    let lr_val := BitVec.ofInt 64 (Int64.toInt p.upper)
    let target_val := Int64.ofInt (s.regs.getRegOrZr target).signed
    s.setRegOrZr RegOrZr.X30 lr_val (fun s' => jmp target_val s')
  | .BR target =>
    let target_val := Int64.ofInt (s.regs.getRegOrZr target).signed
    jmp target_val s
  | .RET target =>
    let target_val := Int64.ofInt (s.regs.getRegOrZr target).signed
    jmp target_val s
  | .CBZ reg target =>
    let val := s.regs.getRegOrZr reg
    if val == 0 then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .CBNZ reg target =>
    let val := s.regs.getRegOrZr reg
    if val != 0 then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .TBZ reg bit target =>
    let val := s.regs.getRegOrZr reg
    if val.getLsbD bit == false then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .TBNZ reg bit target =>
    let val := s.regs.getRegOrZr reg
    if val.getLsbD bit == true then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .LDAR k xcl sz dst base =>
    base.interpBase s (fun addr =>
      s.loadK k xcl addr sz (fun val s' =>
        s'.setRegOrZr dst (val.zeroExtend w.bits) next))
  | .STLR sz src base =>
    base.interpBase s (fun addr =>
      s.storeK .rel false addr ((s.regs.getRegOrZr src).take sz.bits) (fun _ok s' => next s'))
  | .STXR k sz status src base =>
    base.interpBase s (fun addr =>
      s.storeK k true addr ((s.regs.getRegOrZr src).take sz.bits) (fun ok s' =>
        s'.setRegOrZr status (if ok then 0#32 else 1#32) next))
  | .CAS k sz rs rt base =>
    base.interpBase s (fun addr =>
      let cmp := (s.regs.getRegOrZr rs).take sz.bits
      let new := (s.regs.getRegOrZr rt).take sz.bits
      s.rmwK k rs.isZr addr sz (fun old => if old == cmp then some new else none) (fun old s' =>
        s'.setRegOrZr rs (old.zeroExtend w.bits) next))
  | .SWP k sz rs rt base =>
    base.interpBase s (fun addr =>
      let new := (s.regs.getRegOrZr rs).take sz.bits
      s.rmwK k rt.isZr addr sz (fun _old => some new) (fun old s' =>
        s'.setRegOrZr rt (old.zeroExtend w.bits) next))
  | .LDOP op k sz rs rt base =>
    base.interpBase s (fun addr =>
      let arg := (s.regs.getRegOrZr rs).take sz.bits
      s.rmwK k rt.isZr addr sz (fun old => some (op.apply old arg)) (fun old s' =>
        s'.setRegOrZr rt (old.zeroExtend w.bits) next))
  | .LDXP k dst1 dst2 base =>
    base.interpBase s (fun addr =>
      s.loadPairK k true addr w (fun val1 val2 s' =>
        s'.setRegOrZr dst1 val1 (fun s'' =>
          s''.setRegOrZr dst2 val2 next)))
  | .STXP k status src1 src2 base =>
    base.interpBase s (fun addr =>
      s.storePairK k true addr (s.regs.getRegOrZr src1) (s.regs.getRegOrZr src2) (fun ok s' =>
        s'.setRegOrZr status (if ok then 0#32 else 1#32) next))
  | .CASP k rs1 rs2 rt1 rt2 base =>
    base.interpBase s (fun addr =>
      let cmp1 := s.regs.getRegOrZr rs1
      let cmp2 := s.regs.getRegOrZr rs2
      let new1 := s.regs.getRegOrZr rt1
      let new2 := s.regs.getRegOrZr rt2
      s.rmwPairK k addr (w := (w : MemWidth)) cmp1 cmp2 new1 new2
        (fun old1 old2 s' =>
          s'.setRegOrZr rs1 old1 (fun s'' =>
            s''.setRegOrZr rs2 old2 next)))
  | .DMB k => fence k (fun _unit => next s)
  | .DSB k => fence (if k == .st then .stAll else k) (fun _unit => next s)
  | .ISB => fence .isb (fun _unit => next s)
  | .NOP => next s
  | .SVC imm => s.pendingSyscall imm next
  | .MRS dst sr => s.setRegOrZr dst (s.regs.getSysReg sr) next
  | .MSR sr src => next { s with regs := s.regs.setSysReg sr (s.regs.getRegOrZr src) }

@[kstep] def Instr.interp [Labels]
  (i : Instr) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  require_exec_access p (fun _unit =>
    Operation.interp (w := i.operation_size) i.operation p s next jmp)

@[kstep] def Directive.interp [Labels]
  (d : Directive) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match d with
  | .label _ => next s
  | .instr i => i.interp s p next jmp
  | .byteArray _ => .unimplemented s!"Unimplemented: execution reached data block at {p.1}"

def Directives.interp [Labels]
  (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64)
  (ret : Int64 → MachineData → Effects) : Effects :=
  match ds with
  | [] => ret pc s
  | (d, sz) :: ds =>
    d.interp s (.mk pc (pc+.ofNat sz)) (jmp:=ret) (next := (fun s =>
    interp ds s (pc+.ofNat sz) ret))

abbrev Layout := Kraken.Layout Directive

@[reducible]
def Executable.labels (e : Executable) : Labels :=
  { label l := (e.withAddresses.findSome?
      (fun (p, d, _) => if d = .label l then .some p else .none)).getD (-1) }

def Executable.directivesFromLabel (e : Executable) (l : Label) : List (Directive × Nat) :=
  e.2.dropWhile (·.1 != .label l)

abbrev MachineState := MachineData × Int64

def Executable.step (e : Executable) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  let := Executable.labels e
  Directives.interp (e.directivesAtAddress s.2) s.1 s.2 (fun pc s => ret (s, pc))

def Executable.straightline (e : Executable) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  let := Executable.labels e
  Directives.interp (e.directivesFromAddress s.2) s.1 s.2 (fun pc s => ret (s, pc))

-- -- Concrete evaluators for expedient testing

partial def Executable.eval (e : Executable) (s : MachineState) (until_ : MachineState → Bool) : Except String (MachineState) :=
  if until_ s then .ok s else handleEffects (Executable.straightline e s .done)
where
  handleEffects es :=
    match es with
    | .done s => eval e s until_
    | .unimplemented msg => .error msg
    | .require_read_access _ _ ok => handleEffects (ok ())
    | .require_write_access _ _ ok => handleEffects (ok ())
    | .require_exec_access _ ok => handleEffects (ok ())
    | .nonmem_load _ addr _ _ => .error s!"Load at unmapped address {repr addr}"
    | .nonmem_store _ addr _ _ => .error s!"Store at unmapped address {repr addr}"
    | .sync_load _ _ _ addr _ _ => .error s!"Load at unmapped address {repr addr}"
    | .sync_store _ _ _ addr _ _ => .error s!"Store at unmapped address {repr addr}"
    | .rmw _ _ _ addr _ _ _ => .error s!"Read-modify-write at unmapped address {repr addr}"
    | .sync_load_pair _ _ _ addr _ _ => .error s!"Load pair at unmapped address {repr addr}"
    | .sync_store_pair _ _ _ addr _ _ _ => .error s!"Store pair at unmapped address {repr addr}"
    | .rmw_pair _ _ addr _ _ _ _ _ => .error s!"Read-modify-write pair at unmapped address {repr addr}"
    | .fence _ ok => handleEffects (ok ())
    | .unaligned_sp sp => .error s!"SP={sp} (is not 16-byte aligned)"
    | @Effects.undefined _ t cont => handleEffects (cont (t.from_hash (hash s.1.regs)))
    | .syscall info _ => .error (pendingSyscallMsg info.imm)

def Directive.fakeSize (d : Directive) : Nat :=
  match d with
  | .instr _ => 4
  | .label _ => 0
  | .byteArray bs => bs.size

def Program.fakeLayout (prog : Program) : Executable :=
  let : Inhabited Directive := .mk (.byteArray (.mk #[]))
  let h := hash prog;
  let layout : Layout := { start := h.toInt64<<<16, size i := prog[i]!.fakeSize }
  layout prog

abbrev eval [layout : Layout] (prog : Program) := Executable.eval (layout prog)

/-- info: Except.ok 58 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr ⟨.W64, .LDR .X1 (.addr { base := .SP, off := 0 })⟩,
    .instr ⟨.W64, .ADD_e .X1 .X1 0x10⟩,
    .instr ⟨.W64, .STR .X1 { base := .SP, off := 0 }⟩,
    .instr ⟨.W64, .LDR .X2 (.addr { base := .SP, off := 0 })⟩]
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 42, regs := {SP := 0x100} }
  (Executable.eval exe (data, start) (fun (_, pc) => (exe.directivesFromAddress pc).isEmpty)).bind (fun s => .ok s.1.regs.X2)

/-- info: Except.ok (42, 264) -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr ⟨.W64, .LDR .X1 (.addr { base := .SP, off := .imm { imm := 8, index := some .Pre } })⟩ ]
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x108 8 42, regs := { SP := 0x100 } }
  (Executable.eval exe (data, start) (fun (_, pc) => (exe.directivesFromAddress pc).isEmpty)).bind (fun s => .ok (s.1.regs.X1, s.1.regs.SP))

/-- info: Except.ok (42, 264) -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr ⟨.W64, .STR .X1 { base := .SP, off := .imm { imm := 8, index := some .Post } }⟩ ]
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 0, regs := { SP := 0x100, X1 := 42 } }
  (Executable.eval exe (data, start) (fun (_, pc) => (exe.directivesFromAddress pc).isEmpty)).bind (fun s =>
    match Mem.loadInt s.1.dmem 0x100 8 with
    | some v => .ok (v, s.1.regs.SP)
    | none => .error "Memory store failed"
  )

-- Tests of the acquire/release, exclusive and atomic instructions on mapped
-- memory. Each runs a small program from `main` to its end on a memory holding
-- `42` at `0x100` (`X1 = 0x100`), and reports a register and the final word.

private def runAtomicTest {α} (prog : Program) (f : MachineData → α)
    (regs : Reg64s := { X1 := 0x100 }) : Except String α :=
  let exe := Program.fakeLayout ([.label "main"] ++ prog)
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 42, regs }
  (Executable.eval exe (data, start) (fun (_, pc) => (exe.directivesFromAddress pc).isEmpty)).map (f ·.1)

private def memAt (s : MachineData) (addr : BitVec 64 := 0x100) : Int :=
  (Mem.loadInt s.dmem addr 8).getD (-1)

-- LDAR reads, STLR writes, DMB is a skip: X2 := [X1]; [X1] := X2 + 1.
/-- info: Except.ok (42, 43) -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W64, .LDAR .acq false .W64 .X2 .X1⟩,
    .instr ⟨.W64, .DMB .sy⟩,
    .instr ⟨.W64, .ADD_e .X3 .X2 1⟩,
    .instr ⟨.W64, .STLR .W64 .X3 .X1⟩,
    .instr ⟨.W64, .ISB⟩]
  fun s => (s.regs.X2, memAt s)

-- LDARB zero-extends into a W register; STLRH writes only the low halfword.
/-- info: Except.ok (255, 65535) -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W32, .STLR .W16 .W4 .X1⟩,
    .instr ⟨.W32, .LDAR .acq false .W8 .W2 .X1⟩]
  (fun s => (s.regs.X2, memAt s))
  (regs := { X1 := 0x100, X3 := 0xFFFFFFFF, X4 := 0xFFFF_FFFF_FFFF_FFFF })

-- CAS succeeds: X2 (= 42) matches memory, so X3 (= 7) is written; X2 receives the old value.
/-- info: Except.ok (42, 7) -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W64, .CAS .acqRel .W64 .X2 .X3 .X1⟩]
  (fun s => (s.regs.X2, memAt s))
  (regs := { X1 := 0x100, X2 := 42, X3 := 7 })

-- CAS fails: X2 (= 41) does not match, memory is untouched, X2 still receives the old value.
/-- info: Except.ok (42, 42) -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W64, .CAS .plain .W64 .X2 .X3 .X1⟩]
  (fun s => (s.regs.X2, memAt s))
  (regs := { X1 := 0x100, X2 := 41, X3 := 7 })

-- SWP: X2 is written, X3 receives the old value.
/-- info: Except.ok (42, 7) -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W64, .SWP .acq .W64 .X2 .X3 .X1⟩]
  (fun s => (s.regs.X3, memAt s))
  (regs := { X1 := 0x100, X2 := 7 })

-- LDADD: memory += X2, X3 receives the old value; STADD (Rt = XZR) adds again.
/-- info: Except.ok (42, 62) -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W64, .LDOP .ADD .plain .W64 .X2 .X3 .X1⟩,
    .instr ⟨.W64, .LDOP .ADD .rel .W64 .X2 .XZR .X1⟩]
  (fun s => (s.regs.X3, memAt s))
  (regs := { X1 := 0x100, X2 := 10 })

-- LDSMAX/LDUMAX differ on a negative operand: as a signed 64-bit value -1 < 42, as unsigned it is the max.
/-- info: Except.ok (42, 18446744073709551615) -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W64, .LDOP .SMAX .plain .W64 .X2 .X3 .X1⟩,
    .instr ⟨.W64, .LDOP .UMAX .plain .W64 .X2 .X4 .X1⟩]
  (fun s => (s.regs.X3, memAt s))
  (regs := { X1 := 0x100, X2 := 0xFFFF_FFFF_FFFF_FFFF })

-- LDCLR/LDSET/LDEOR on a halfword: 42 = 0b101010; clear 0b10 -> 40; set 0b101 -> 45; eor 0xFF -> 210.
/-- info: Except.ok 210 -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W32, .LDOP .CLR .plain .W16 .W2 .WZR .X1⟩,
    .instr ⟨.W32, .LDOP .SET .plain .W16 .W3 .WZR .X1⟩,
    .instr ⟨.W32, .LDOP .EOR .plain .W16 .W4 .WZR .X1⟩]
  (fun s => memAt s)
  (regs := { X1 := 0x100, X2 := 2, X3 := 5, X4 := 0xFF })

-- LDXR/STXR: the store exclusive may fail spuriously (resolved from a hash by
-- `Executable.eval`); whichever way it goes, the status register and memory agree.
/-- info: Except.ok true -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W64, .LDAR .plain true .W64 .X2 .X1⟩,
    .instr ⟨.W64, .STXR .plain .W64 .W4 .X3 .X1⟩]
  (fun s => (s.regs.X2 == 42) && (if s.regs.X4 == 0 then memAt s == 7 else s.regs.X4 == 1 && memAt s == 42))
  (regs := { X1 := 0x100, X3 := 7 })

-- An exclusive retry loop terminates under `Executable.eval`'s hash-driven choice
-- (the hash is over the registers, which the loop changes: a counter in X5).
/-- info: Except.ok (0, 7, true) -/
#guard_msgs in
#eval runAtomicTest [
    .label "retry",
    .instr ⟨.W64, .ADD_e .X5 .X5 1⟩,
    .instr ⟨.W64, .LDAR .acq true .W64 .X2 .X1⟩,
    .instr ⟨.W64, .STXR .rel .W64 .W4 .X3 .X1⟩,
    .instr ⟨.W32, .CBNZ .W4 (.label "retry")⟩]
  (fun s => (s.regs.X4, memAt s, decide (s.regs.X5 ≥ 1)))
  (regs := { X1 := 0x100, X3 := 7 })

-- An atomic at an unmapped address stops the sequential evaluator.
/-- info: Except.error "Read-modify-write at unmapped address 0x0000000000000200#64" -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W64, .SWP .plain .W64 .X2 .X3 .X1⟩]
  (fun s => memAt s)
  (regs := { X1 := 0x200, X2 := 7 })

-- Tests of the pair exclusives and `CASP` on mapped memory: `0x100` holds 42 and
-- `0x108` holds 43 (`X1 = 0x100`); each test reports registers and both words.

private def runPairTest {α} (prog : Program) (f : MachineData → α)
    (regs : Reg64s := { X1 := 0x100 }) : Except String α :=
  let exe := Program.fakeLayout ([.label "main"] ++ prog)
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt (Mem.storeInt {} 0x100 8 42) 0x108 8 43, regs }
  (Executable.eval exe (data, start) (fun (_, pc) => (exe.directivesFromAddress pc).isEmpty)).map (f ·.1)

-- LDXP reads both halves, the first register from the lower address.
/-- info: Except.ok (42, 43) -/
#guard_msgs in
#eval runPairTest [
    .instr ⟨.W64, .LDXP .acq .X2 .X3 .X1⟩]
  (fun s => (s.regs.X2, s.regs.X3))

-- LDXP with `W` registers: two 4-byte halves of the word 42 (42 and 0).
/-- info: Except.ok (42, 0) -/
#guard_msgs in
#eval runPairTest [
    .instr ⟨.W32, .LDXP .plain .W2 .W3 .X1⟩]
  (fun s => (s.regs.X2, s.regs.X3))

-- LDXP/STXP: the store exclusive pair may fail spuriously, as one; whichever way
-- it goes, the status register and both words agree.
/-- info: Except.ok true -/
#guard_msgs in
#eval runPairTest [
    .instr ⟨.W64, .LDXP .plain .X2 .X3 .X1⟩,
    .instr ⟨.W64, .STXP .rel .W4 .X5 .X6 .X1⟩]
  (fun s => (s.regs.X2 == 42 && s.regs.X3 == 43) &&
    (if s.regs.X4 == 0 then memAt s == 7 && memAt s 0x108 == 8
     else s.regs.X4 == 1 && memAt s == 42 && memAt s 0x108 == 43))
  (regs := { X1 := 0x100, X5 := 7, X6 := 8 })

-- An exclusive pair retry loop terminates (the counter in X7 changes the hash).
/-- info: Except.ok (0, 7, 8) -/
#guard_msgs in
#eval runPairTest [
    .label "retry",
    .instr ⟨.W64, .ADD_e .X7 .X7 1⟩,
    .instr ⟨.W64, .LDXP .acq .X2 .X3 .X1⟩,
    .instr ⟨.W64, .STXP .plain .W4 .X5 .X6 .X1⟩,
    .instr ⟨.W32, .CBNZ .W4 (.label "retry")⟩]
  (fun s => (s.regs.X4, memAt s, memAt s 0x108))
  (regs := { X1 := 0x100, X5 := 7, X6 := 8 })

-- CASP succeeds: X2:X3 (= 42:43) match, so X4:X5 (= 7:8) are written; X2:X3 receive the old values.
/-- info: Except.ok (42, 43, 7, 8) -/
#guard_msgs in
#eval runPairTest [
    .instr ⟨.W64, .CASP .acqRel .X2 .X3 .X4 .X5 .X1⟩]
  (fun s => (s.regs.X2, s.regs.X3, memAt s, memAt s 0x108))
  (regs := { X1 := 0x100, X2 := 42, X3 := 43, X4 := 7, X5 := 8 })

-- CASP fails when only one half matches: memory is untouched, X2:X3 still receive the old values.
/-- info: Except.ok (42, 43, 42, 43) -/
#guard_msgs in
#eval runPairTest [
    .instr ⟨.W64, .CASP .plain .X2 .X3 .X4 .X5 .X1⟩]
  (fun s => (s.regs.X2, s.regs.X3, memAt s, memAt s 0x108))
  (regs := { X1 := 0x100, X2 := 42, X3 := 0, X4 := 7, X5 := 8 })

-- CASP with `W` registers compares and writes two 4-byte halves: 42:0 becomes 7:8.
/-- info: Except.ok (42, 0, 34359738375) -/
#guard_msgs in
#eval runPairTest [
    .instr ⟨.W32, .CASP .rel .W2 .W3 .W4 .W5 .X1⟩]
  (fun s => (s.regs.X2, s.regs.X3, memAt s))
  (regs := { X1 := 0x100, X2 := 42, X3 := 0, X4 := 7, X5 := 8 })

-- A pair at an unmapped address stops the sequential evaluator; so does a pair
-- with one half unmapped (here the upper half, at 0x110).
/-- info: Except.error "Read-modify-write pair at unmapped address 0x0000000000000200#64" -/
#guard_msgs in
#eval runPairTest [
    .instr ⟨.W64, .CASP .plain .X2 .X3 .X4 .X5 .X1⟩]
  (fun s => memAt s)
  (regs := { X1 := 0x200 })
/-- info: Except.error "Load at unmapped address 0x0000000000000110#64" -/
#guard_msgs in
#eval runPairTest [
    .instr ⟨.W64, .LDXP .plain .X2 .X3 .X1⟩]
  (fun s => memAt s)
  (regs := { X1 := 0x108 })

-- The thread pointer: `TPIDR_EL0` starts at 0; `MSR` sets it from X1 (0x100),
-- `MRS` reads it back into X2, and a load through X2 reads the word 42.
/-- info: Except.ok (0, 256, 256, 42) -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W64, .MRS .X4 .TPIDR_EL0⟩,
    .instr ⟨.W64, .MSR .TPIDR_EL0 .X1⟩,
    .instr ⟨.W64, .MRS .X2 .TPIDR_EL0⟩,
    .instr ⟨.W64, .LDR .X3 (.addr { base := .X2, off := 0 })⟩]
  (fun s => (s.regs.X4, s.regs.X2, s.regs.TPIDR_EL0, s.regs.X3))

-- `MSR` from `XZR` clears it; `MRS` to `XZR` writes nothing.
/-- info: Except.ok (0, 0) -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W64, .MSR .TPIDR_EL0 .X1⟩,
    .instr ⟨.W64, .MRS .XZR .TPIDR_EL0⟩,
    .instr ⟨.W64, .MSR .TPIDR_EL0 .XZR⟩,
    .instr ⟨.W64, .MRS .X2 .TPIDR_EL0⟩]
  (fun s => (s.regs.X2, s.regs.TPIDR_EL0))

-- A supervisor call stops the sequential evaluator with the pending-system-call
-- status (`MachineData.pendingSyscall`); nothing after it runs.
/-- info: Except.error "pending system call: svc #0" -/
#guard_msgs in
#eval runAtomicTest [
    .instr ⟨.W64, .ADD_e .X2 .X2 1⟩,
    .instr ⟨.W64, .SVC 0⟩,
    .instr ⟨.W64, .ADD_e .X2 .X2 1⟩]
  (fun s => s.regs.X2)
