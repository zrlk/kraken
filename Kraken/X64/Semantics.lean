-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html

import Kraken.Attribute
import Kraken.Float32Fma
import Kraken.Layout
import Kraken.Mem
import Kraken.MemKinds
import Kraken.X64.Syntax
import Lean
import Std

-- injective coercions only
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat

namespace BitVec
def unsigned {w} (x : BitVec w) : Int := x.toNat
def signed {w} (x : BitVec w) : Int := x.toInt
@[kstep] def take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
@[kstep] def drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)
end BitVec
attribute [kstep]
  BitVec.extractLsb'
  BitVec.ofInt_add
  BitVec.ofInt_toInt
  BitVec.signed
  BitVec.truncate
def BitVec.replaceLow {w n} (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.drop n) new).setWidth _

namespace Reg
@[kstep] def base {w} (r : Reg w) : Reg64 := match r with
  | .low r _ => r
  | .ah => .rax | .bh => .rbx | .ch => .rcx | .dh => .rdx

@[kstep] def offset {w} (r : Reg w) : Nat := match r with
  | .low _ _ => 0
  | .ah | .bh | .ch | .dh => 8
end Reg

namespace AvxReg
def base {w} (r : AvxReg w) : RegMm := match r with
  | .xmm r => r
  | .ymm r => r
  | .zmm r => r
end AvxReg

structure Reg64s where
  rax : UInt64 := 0
  rbx : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  rsi : UInt64 := 0
  rdi : UInt64 := 0
  rsp : UInt64 := 0
  rbp : UInt64 := 0
  r8  : UInt64 := 0
  r9  : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

/-- The register file's own width is the literal 64: stating it as `BitVec 64`
makes every consumer store the literal as the width index, the one spelling
`grind`'s congruence and `bv_decide` read syntactically. `Width.W64.type` is
definitionally the same type; an index spelled through it depends on which
reduction path the elaborator took (`Width.W64.bits`, a stranded `bits` match,
or `64`), and syntactically distinct spellings of one index split atoms. -/
@[kstep] def Reg64s.get64 (s : Reg64s) (r : Reg64) : BitVec 64 := UInt64.toBitVec (match r with
  | .rax => s.rax | .rbx => s.rbx | .rcx => s.rcx | .rdx => s.rdx
  | .rsi => s.rsi | .rdi => s.rdi | .rsp => s.rsp | .rbp => s.rbp
  | .r8  => s.r8  | .r9  => s.r9  | .r10 => s.r10 | .r11 => s.r11
  | .r12 => s.r12 | .r13 => s.r13 | .r14 => s.r14 | .r15 => s.r15)

@[kstep] def Reg64s.set64 (regs : Reg64s) (r : Reg64) (v : BitVec 64) : Reg64s :=
  let  v := UInt64.ofBitVec v
  match r with
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v }
  | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v }
  | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v }
  | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v }
  | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }

@[kstep] def Reg64s.get (s : Reg64s) {w} (r : Reg w) : w.type :=
  ((s.get64 r.base).drop r.offset).take w.bits
  -- BitVec because it may be signed or unsigned depending on context

@[kstep] def Reg64s.set (s : Reg64s) {w} (r : Reg w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.set64 r v
  | .low r .W32 => s.set64 r (v.zeroExtend _)
  | .low r w => s.set64 r ((s.get64 r).replaceLow v)
  | .ah | .bh | .ch | .dh => let old := s.get64 r.base;
    s.set64 r.base (old.replaceLow (BitVec.append v (s.get (.low r.base .W8))))

def ZmmValue : Type := BitVec 512
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def zmmZero : ZmmValue := 0#512

structure RegZmms where
  zmm0  : ZmmValue := zmmZero
  zmm1  : ZmmValue := zmmZero
  zmm2  : ZmmValue := zmmZero
  zmm3  : ZmmValue := zmmZero
  zmm4  : ZmmValue := zmmZero
  zmm5  : ZmmValue := zmmZero
  zmm6  : ZmmValue := zmmZero
  zmm7  : ZmmValue := zmmZero
  zmm8  : ZmmValue := zmmZero
  zmm9  : ZmmValue := zmmZero
  zmm10 : ZmmValue := zmmZero
  zmm11 : ZmmValue := zmmZero
  zmm12 : ZmmValue := zmmZero
  zmm13 : ZmmValue := zmmZero
  zmm14 : ZmmValue := zmmZero
  zmm15 : ZmmValue := zmmZero
  zmm16 : ZmmValue := zmmZero
  zmm17 : ZmmValue := zmmZero
  zmm18 : ZmmValue := zmmZero
  zmm19 : ZmmValue := zmmZero
  zmm20 : ZmmValue := zmmZero
  zmm21 : ZmmValue := zmmZero
  zmm22 : ZmmValue := zmmZero
  zmm23 : ZmmValue := zmmZero
  zmm24 : ZmmValue := zmmZero
  zmm25 : ZmmValue := zmmZero
  zmm26 : ZmmValue := zmmZero
  zmm27 : ZmmValue := zmmZero
  zmm28 : ZmmValue := zmmZero
  zmm29 : ZmmValue := zmmZero
  zmm30 : ZmmValue := zmmZero
  zmm31 : ZmmValue := zmmZero
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def RegZmms.get512 (s : RegZmms) (r : RegMm) : AvxWidth.W512.type := (match r with
  | .mm0  => s.zmm0  | .mm1  => s.zmm1  | .mm2  => s.zmm2  | .mm3  => s.zmm3
  | .mm4  => s.zmm4  | .mm5  => s.zmm5  | .mm6  => s.zmm6  | .mm7  => s.zmm7
  | .mm8  => s.zmm8  | .mm9  => s.zmm9  | .mm10 => s.zmm10 | .mm11 => s.zmm11
  | .mm12 => s.zmm12 | .mm13 => s.zmm13 | .mm14 => s.zmm14 | .mm15 => s.zmm15
  | .mm16 => s.zmm16 | .mm17 => s.zmm17 | .mm18 => s.zmm18 | .mm19 => s.zmm19
  | .mm20 => s.zmm20 | .mm21 => s.zmm21 | .mm22 => s.zmm22 | .mm23 => s.zmm23
  | .mm24 => s.zmm24 | .mm25 => s.zmm25 | .mm26 => s.zmm26 | .mm27 => s.zmm27
  | .mm28 => s.zmm28 | .mm29 => s.zmm29 | .mm30 => s.zmm30 | .mm31 => s.zmm31)

def RegZmms.set512 (regs : RegZmms) (r : RegMm) (v : AvxWidth.W512.type) : RegZmms :=
  match r with
  | .mm0  => { regs with zmm0  := v } | .mm1  => { regs with zmm1  := v }
  | .mm2  => { regs with zmm2  := v } | .mm3  => { regs with zmm3  := v }
  | .mm4  => { regs with zmm4  := v } | .mm5  => { regs with zmm5  := v }
  | .mm6  => { regs with zmm6  := v } | .mm7  => { regs with zmm7  := v }
  | .mm8  => { regs with zmm8  := v } | .mm9  => { regs with zmm9  := v }
  | .mm10 => { regs with zmm10 := v } | .mm11 => { regs with zmm11 := v }
  | .mm12 => { regs with zmm12 := v } | .mm13 => { regs with zmm13 := v }
  | .mm14 => { regs with zmm14 := v } | .mm15 => { regs with zmm15 := v }
  | .mm16 => { regs with zmm16 := v } | .mm17 => { regs with zmm17 := v }
  | .mm18 => { regs with zmm18 := v } | .mm19 => { regs with zmm19 := v }
  | .mm20 => { regs with zmm20 := v } | .mm21 => { regs with zmm21 := v }
  | .mm22 => { regs with zmm22 := v } | .mm23 => { regs with zmm23 := v }
  | .mm24 => { regs with zmm24 := v } | .mm25 => { regs with zmm25 := v }
  | .mm26 => { regs with zmm26 := v } | .mm27 => { regs with zmm27 := v }
  | .mm28 => { regs with zmm28 := v } | .mm29 => { regs with zmm29 := v }
  | .mm30 => { regs with zmm30 := v } | .mm31 => { regs with zmm31 := v }

def RegZmms.get (s : RegZmms) {w} (r : AvxReg w) : w.type :=
  (s.get512 r.base).take w.bits

def RegZmms.set (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v
  | .ymm r => s.set512 r (v.zeroExtend _)
  | .xmm r => s.set512 r (v.zeroExtend _)

def RegZmms.setLegacy (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v  -- impossible
  | .ymm r => s.set512 r ((s.get512 r).replaceLow v)  -- impossible
  | .xmm r => s.set512 r ((s.get512 r).replaceLow v)

/-- `vzeroupper` in 64-bit mode: bits 511:128 of zmm0–15 are cleared, and
zmm16–31 are left alone. -/
def RegZmms.zeroUpper (s : RegZmms) : RegZmms :=
  let z (v : ZmmValue) : ZmmValue := (BitVec.setWidth 128 v).setWidth 512
  { s with
    zmm0 := z s.zmm0, zmm1 := z s.zmm1, zmm2 := z s.zmm2, zmm3 := z s.zmm3,
    zmm4 := z s.zmm4, zmm5 := z s.zmm5, zmm6 := z s.zmm6, zmm7 := z s.zmm7,
    zmm8 := z s.zmm8, zmm9 := z s.zmm9, zmm10 := z s.zmm10, zmm11 := z s.zmm11,
    zmm12 := z s.zmm12, zmm13 := z s.zmm13, zmm14 := z s.zmm14, zmm15 := z s.zmm15 }

@[kstep]
def BitVec.toAddressSize [address_size: AddressSize] (w: BitVec 64): BitVec address_size.address_size.bits :=
  w.take address_size.address_size.bits

-- TODO: consider adding a `split` helper to switch representations between
-- u128, 4xu32, etc.
def BitVec.packedBinOp {w : Nat} (c : Nat) (op : BitVec c → BitVec c → BitVec c) (a b : BitVec w) : BitVec w :=
  if _ : c = 0 ∨ w < c then
    a -- Fallback/Base case (w = 0 or invalid chunk size)
  else
    -- Extract the lowest chunk
    let a_low := a.take c
    let b_low := b.take c
    let res_low := op a_low b_low

    -- Recursively process the remaining high bits
    let a_high := a.drop c
    let b_high := b.drop c
    let res_high := BitVec.packedBinOp c op a_high b_high

    -- Recombine: res_high is the high part, res_low is the low part
    (BitVec.append res_high res_low).setWidth _
termination_by w
decreasing_by omega

def BitVec.toFloat32 (v : BitVec 32) : Float32 :=
  Float32.ofBits (UInt32.ofBitVec v)

def Float32.toBitVec (f : Float32) : BitVec 32 :=
  UInt32.toBitVec (Float32.toBits f)

/-- The three-operand sibling of `packedBinOp`: `op` on each `c`-bit chunk of
`a`, `b` and `d`. -/
def BitVec.packedTernOp {w : Nat} (c : Nat) (op : BitVec c → BitVec c → BitVec c → BitVec c)
    (a b d : BitVec w) : BitVec w :=
  if _ : c = 0 ∨ w < c then
    a
  else
    let res_low := op (a.take c) (b.take c) (d.take c)
    let res_high := BitVec.packedTernOp c op (a.drop c) (b.drop c) (d.drop c)
    (BitVec.append res_high res_low).setWidth _
termination_by w
decreasing_by omega

/-! Single-precision lane arithmetic, on the bits of a lane. The model rounds
to nearest, ties to even (MXCSR is not modeled). -/

/-- `a + b` on single-precision lanes. -/
def BitVec.f32add (a b : BitVec 32) : BitVec 32 :=
  Float32.toBitVec (BitVec.toFloat32 a + BitVec.toFloat32 b)

/-- `a * b` on single-precision lanes. -/
def BitVec.f32mul (a b : BitVec 32) : BitVec 32 :=
  Float32.toBitVec (BitVec.toFloat32 a * BitVec.toFloat32 b)

/-- `a * b + c` on single-precision lanes, rounded once. -/
def BitVec.f32fma (a b c : BitVec 32) : BitVec 32 :=
  Float32.toBitVec
    (Kraken.Float32.fma (BitVec.toFloat32 a) (BitVec.toFloat32 b) (BitVec.toFloat32 c))

/-- One 128-bit lane of `shufps`: the low two floats of the result come from
`a` and the high two from `b`, each picked by two bits of `imm`. -/
def BitVec.shufps128 (imm : UInt8) (a b : BitVec 128) : BitVec 128 :=
  let pick (x : BitVec 128) (k : Nat) : BitVec 32 :=
    x.extractLsb' (32 * ((imm.toNat >>> k) % 4)) 32
  pick b 6 ++ pick b 4 ++ pick a 2 ++ pick a 0

structure StatusFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

abbrev DataMem := Mem 64
instance : Repr DataMem where reprPrec _ _ := "<opaque memory>"
structure MachineData where -- does not include code or program position
  regs : Reg64s := {}
  zmms : RegZmms := {}
  status : StatusFlags := .mk false false false false false false
  dmem : DataMem := ∅
  deriving Repr, BEq, DecidableEq

-- We only allow nondeterministic choices for a fixed set of types.
class inductive NondetSupportingType : Type -> Type
  | bitvec (w : Width) : NondetSupportingType w.type
  | avx_bitvec (aw : AvxWidth) : NondetSupportingType aw.type
  | bool : NondetSupportingType Bool
  | statusFlags : NondetSupportingType StatusFlags

def NondetSupportingType.from_hash {α} [t : NondetSupportingType α] (h : UInt64) : α :=
  match t with
  | .bool => h % 2 != 0
  | .statusFlags => let h := h.toBitVec; (.mk h[0] h[1] h[2] h[3] h[4] h[5])
  | .bitvec w => h.toBitVec.setWidth w.bits
  | .avx_bitvec w => h.toBitVec.setWidth w.bits

instance (w : Width) : NondetSupportingType w.type := .bitvec w
instance (w : AvxWidth) : NondetSupportingType w.type := .avx_bitvec w
instance : NondetSupportingType Bool := .bool
instance : NondetSupportingType StatusFlags := .statusFlags

inductive Effects
  | done (a : MachineData × Int64)
  | unimplemented (msg : String)
  | gp_unaligned (addr : BitVec 64) (w : Nat)
  -- loads and stores *outside* the data memory, eg. MMIO, might still affect the data memory:
  -- for instance, MMIO reads/writes at certain device register addresses might change what
  -- data memory the process logically owns vs what memory is owned by devices
  | nonmem_load (dmem : DataMem) (addr : BitVec 64) (w : Width) (ret : w.type → DataMem → Effects)
  | nonmem_store (dmem : DataMem) (addr : BitVec 64) {w : Width} (v : w.type) (ret: DataMem → Effects)
  | undefined {α : Type} [NondetSupportingType α] (ret : α → Effects)
  | require_read_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects)
  | require_write_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects)
  | require_exec_access (p: Std.Rco Int64) (ok : Unit → Effects)
  -- Memory events with an ordering kind, for the weak-memory
  -- layer. Like `nonmem_load`/`nonmem_store` they are
  -- emitted only for an address outside `dmem`, so the sequential consumers
  -- treat the access effects as faults and `fence` as a skip. x86 has no
  -- instruction that emits `sync_load`/`sync_store` (its ordering is the TSO
  -- profile of the memory model, not an annotation on the access); they are
  -- here so that the two ISAs' `Effects` are shaped alike.
  | sync_load (k : Kraken.LoadKind) (xcl : Bool) (dmem : DataMem) (addr : BitVec 64) (w : Width)
      (ret : w.type → DataMem → Effects)
  -- `ret`'s `Bool` is the store's success (always `true` on x86).
  | sync_store (k : Kraken.StoreKind) (xcl : Bool) (dmem : DataMem) (addr : BitVec 64) {w : Width}
      (v : w.type) (ret : Bool → DataMem → Effects)
  -- An atomic read-modify-write: `op old` is the value written, or `none` when
  -- a compare failed and nothing is written; `ret` receives the old value.
  | rmw (k : Kraken.RmwKind) (dmem : DataMem) (addr : BitVec 64) (w : Width)
      (op : w.type → Option w.type) (ret : w.type → DataMem → Effects)
  | fence (k : Kraken.FenceKind) (ok : Unit → Effects)
  -- Vector (SSE/AVX) accesses. The access checks
  -- announce the true width of a vector access, so that the
  -- `Width`-indexed checks above and their rules stay as they are.
  -- `atomic` is the access's `atomic` flag below (`true` for `rmw16`); it means
  -- nothing to the sequential semantics, and tells the merged link's access
  -- discipline which footprint the access has.
  | require_read_access_avx (addr : BitVec 64) (w : AvxWidth) (atomic : Bool) (ok : Unit → Effects)
  | require_write_access_avx (addr : BitVec 64) (w : AvxWidth) (atomic : Bool) (ok : Unit → Effects)
  -- A vector access outside `dmem`, the counterpart of `nonmem_load`/`nonmem_store`.
  -- `atomic` holds exactly for the accesses the SDM guarantees to be
  -- single-copy atomic: the aligned 16-byte moves `movaps`/`movapd`/`movdqa`
  -- and their VEX.128 forms.
  | nonmem_load_avx (atomic : Bool) (dmem : DataMem) (addr : BitVec 64) (w : AvxWidth)
      (ret : w.type → DataMem → Effects)
  | nonmem_store_avx (atomic : Bool) (dmem : DataMem) (addr : BitVec 64) {w : AvxWidth}
      (v : w.type) (ret : DataMem → Effects)
  -- `lock cmpxchg16b` outside `dmem`: an atomic 16-byte read-modify-write,
  -- shaped like `rmw` (`Width` has no 16-byte case).
  | rmw16 (k : Kraken.RmwKind) (dmem : DataMem) (addr : BitVec 64)
      (op : BitVec 128 → Option (BitVec 128)) (ret : BitVec 128 → DataMem → Effects)
export Effects (unimplemented nonmem_load nonmem_store undefined require_read_access require_write_access require_exec_access)

-- the unused `Std.Rco Int64` argument and the unmodified `MachineData` return
-- value are present for uniformity with RegOrMem.interp
@[kstep] def Reg.interp {w} (r : Reg w) (s : MachineData) (_ : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) : Effects :=
  ret (s.regs.get r) s

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
  (s : MachineData) (addr : BitVec 64) (w : Width)
  (ret : w.type → MachineData → Effects): Effects :=
  require_read_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some i => ret (.ofInt _ i) s
    | .none => nonmem_load s.dmem addr w (fun v dmem => ret v { s with dmem }))

-- Alternatively, we could define this in terms of BitVecs without %:
-- (addr &&& BitVec.ofNat 64 (bytes - 1)) == 0#64
def isAligned (bytes : Nat) (addr : BitVec 64) : Bool :=
  addr.toNat % bytes == 0

-- Legacy SSE instructions are generally stricter about alignment requirements,
-- while AVX (VEX-encoded) instructions can mostly deal with unaligned
-- addresses (https://discourse.llvm.org/t/memory-alignment-model-on-avx-avx2-and-avx-512-targets/34705).
-- For this reason we default checkAlign to false.
-- The access check is at the true width.
-- Outside `dmem` the access is `nonmem_load_avx`, tagged `atomic` for
-- the moves the SDM guarantees to be single-copy atomic; that flag means
-- nothing to the sequential semantics, so it too defaults to false.
def MachineData.loadAvx
  (s : MachineData) (addr : BitVec 64) (w : AvxWidth)
  (ret : w.type → MachineData → Effects) (checkAlign : Bool := false)
  (atomic : Bool := false) : Effects :=
  if checkAlign && !(isAligned w.bytes addr) then
    .gp_unaligned addr w.bytes
  else
    .require_read_access_avx addr w atomic (fun _unit =>
  match Mem.loadInt s.dmem addr w.bytes with
      | .some i => ret (.ofInt _ i) s
      | .none => .nonmem_load_avx atomic s.dmem addr w (fun v dmem => ret v { s with dmem }))

def MachineData.store (s : MachineData) (addr : BitVec 64) {w : Width} (v : w.type) (ret: MachineData → Effects) : Effects :=
  require_write_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some _ =>
        ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
    | .none => nonmem_store s.dmem addr v (fun dmem' => ret { s with dmem := dmem' }))

/-- The ordering kind of a non-temporal store (`movnti`) for the memory model
(weakly ordered, see `Kraken.Promising.writeSuccs`). Sequentially every kind
is alike. -/
abbrev ntStoreKind : Kraken.StoreKind := .nt

/-- A non-temporal store (`movnti`): `store`, except that outside `dmem` it is
a `sync_store` of kind `ntStoreKind`, so that the memory model can order it
more weakly than an ordinary store. Sequentially the two are the same: inside
`dmem` both write it, outside both are a fault (`Effects.All`). -/
def MachineData.storeNT (s : MachineData) (addr : BitVec 64) {w : Width} (v : w.type) (ret: MachineData → Effects) : Effects :=
  require_write_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some _ =>
        ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
    | .none => .sync_store ntStoreKind false s.dmem addr v (fun _ dmem' => ret { s with dmem := dmem' }))

/-- An atomic read-modify-write of `w` bytes at `addr`: `op old` is the new
value, or `none` to write nothing (a failed compare); `ret` receives the old
value. Mapped-first, like `load`/`store`: inside `dmem` this is the load followed
by the store, and only an unmapped address emits the `rmw` effect, which carries
`op` to the memory model. -/
def MachineData.rmwK (s : MachineData) (k : Kraken.RmwKind) (addr : BitVec 64) (w : Width)
    (op : w.type → Option w.type) (ret : w.type → MachineData → Effects) : Effects :=
  require_read_access addr w (fun _unit =>
  require_write_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some i =>
      let old : w.type := .ofInt _ i
      match op old with
      | .some new => ret old { s with dmem := Mem.storeInt s.dmem addr w.bytes new.toInt }
      | .none => ret old s
    | .none => .rmw k s.dmem addr w op (fun old dmem => ret old { s with dmem })))

/-- The unlocked read-modify-write (`xadd`/`cmpxchg` without `lock`): a plain
load, then a plain store if `op` produces a value. Two accesses, each of which
may be a `nonmem_*` effect. -/
def MachineData.rmwPlain (s : MachineData) (addr : BitVec 64) (w : Width)
    (op : w.type → Option w.type) (ret : w.type → MachineData → Effects) : Effects :=
  s.load addr w (fun old s =>
    match op old with
    | .some new => s.store addr new (ret old)
    | .none => ret old s)

def MachineData.storeAvx (s : MachineData) (addr : BitVec 64) {w : AvxWidth} (v : w.type) (ret: MachineData → Effects) (checkAlign : Bool := false) (atomic : Bool := false) : Effects :=
  if checkAlign && !(isAligned w.bytes addr) then
    .gp_unaligned addr w.bytes
  else
    .require_write_access_avx addr w atomic (fun _unit =>
  match Mem.loadInt s.dmem addr w.bytes with
      | .some _ =>
          ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
      | .none => .nonmem_store_avx atomic s.dmem addr v (fun dmem => ret { s with dmem }))

/-- `lock cmpxchg16b`'s access: an atomic read-modify-write of the 16 bytes at
`addr`, the 16-byte sibling of `rmwK`. Inside `dmem` it is the load followed
by the store; only an unmapped address emits the `rmw16` effect. The caller
checks the alignment. -/
def MachineData.rmw16K (s : MachineData) (k : Kraken.RmwKind) (addr : BitVec 64)
    (op : BitVec 128 → Option (BitVec 128)) (ret : BitVec 128 → MachineData → Effects) : Effects :=
  .require_read_access_avx addr .W128 true (fun _unit =>
  .require_write_access_avx addr .W128 true (fun _unit =>
    match Mem.loadInt s.dmem addr 16 with
    | .some i =>
      let old : BitVec 128 := .ofInt _ i
      match op old with
      | .some new => ret old { s with dmem := Mem.storeInt s.dmem addr 16 new.toInt }
      | .none => ret old s
    | .none => .rmw16 k s.dmem addr op (fun old dmem => ret old { s with dmem })))

/-- `cmpxchg16b` without `lock`: a plain 16-byte load, then a plain 16-byte
store if `op` produces a value, the 16-byte sibling of `rmwPlain`. Neither
access is guaranteed atomic. -/
def MachineData.rmw16Plain (s : MachineData) (addr : BitVec 64)
    (op : BitVec 128 → Option (BitVec 128)) (ret : BitVec 128 → MachineData → Effects) : Effects :=
  s.loadAvx addr .W128 (fun old s =>
    match op old with
    | .some new => s.storeAvx addr (w := .W128) new (ret old)
    | .none => ret old s)

class Labels where label : Label → Int64
export Labels (label)

@[kstep] def ConstExpr.interp [Labels] : ConstExpr → Std.Rco _root_.Int64 → _root_.Int64
  | .label l, _ => Labels.label l
  | .int64 i, _ => i
  | .before_current_instruction, r => r.lower
  | .after_current_instruction, r => r.upper
  | .add e1 e2, p => e1.interp p + e2.interp p
  | .sub e1 e2, p => e1.interp p - e2.interp p

@[kstep] def AddrExpr.interp [Labels] [address_size : AddressSize] (a : AddrExpr) (s : Reg64s) (p : Std.Rco Int64) :=
  let base := match a.base with
              | .some (.reg r) => (s.get64 r).toAddressSize.signed
              | .some .rip => p.upper.toInt
              | .none => 0
  let idx := match a.idx with
             | .some ⟨r, c⟩ => (s.get64 r).toAddressSize.signed * c.bytes
             | .none => 0
  BitVec.ofInt address_size.address_size.bits (base + idx + (a.disp.interp p).toInt)

@[kstep] def RegOrMem.interp {w} [Labels] [AddressSize]
  (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
match o with
  | .reg r => ret (s.regs.get r) s
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) w ret

def AvxRegOrMem.interp {w} [Labels] [AddressSize]
  (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) (checkAlign : Bool := false) (atomic : Bool := false) :=
match o with
  | .avx r => ret (s.zmms.get r) s
  | .mem a => s.loadAvx ((a.interp s.regs p).zeroExtend _) w ret checkAlign atomic

@[kstep]
def MachineData.setReg (s : MachineData) {w} (r : Reg w) (v : w.type) : MachineData :=
  { s with regs := s.regs.set r v }

def MachineData.setAvxReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.set r v }

def MachineData.setAvxLegacyReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.setLegacy r v }

@[kstep]
def MachineData.set {w} [Labels] [AddressSize] (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) : Effects :=
  match d with
  | .reg r => ret (s.setReg r v)
  | .mem a => s.store ((a.interp s.regs p).zeroExtend _) v ret

/-- Read-modify-write of a register-or-memory destination. On a register it is
the register update; on memory it is `rmwK .acqRel` under `lock` and the
two-access `rmwPlain` otherwise. `ret` receives the old value. -/
def RegOrMem.rmw {w} [Labels] [AddressSize] (o : RegOrMem w) (lock : Bool) (s : MachineData)
    (p : Std.Rco Int64) (op : w.type → Option w.type) (ret : w.type → MachineData → Effects) :
    Effects :=
  match o with
  | .reg r =>
    let old := s.regs.get r
    match op old with
    | .some new => ret old (s.setReg r new)
    | .none => ret old s
  | .mem a =>
    if lock then s.rmwK .acqRel ((a.interp s.regs p).zeroExtend _) w op ret
    else s.rmwPlain ((a.interp s.regs p).zeroExtend _) w op ret

def MachineData.setAvx {aw} [Labels] [AddressSize] (s : MachineData) (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64) (ret : MachineData → Effects) (checkAlign : Bool := false) (atomic : Bool := false) : Effects :=
match d with
  | .avx r => ret (s.setAvxReg r v)
  | .mem a => s.storeAvx ((a.interp s.regs p).zeroExtend _) v ret checkAlign atomic

def MachineData.setAvxLegacy {w} [Labels] [AddressSize] (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) (checkAlign : Bool := false) (atomic : Bool := false) : Effects :=
match d with
  | .avx r => ret (s.setAvxLegacyReg r v)
  | .mem a => s.storeAvx ((a.interp s.regs p).zeroExtend _) v ret checkAlign atomic

@[kstep] def Operand.interp {w} [Labels] [AddressSize]
  (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
  match o with
  | regOrMem rm => rm.interp s p ret
  | .imm v => ret ((v.interp p).toBitVec.truncate _) s
  -- we rely on assemblers erroring out on too-large immediates in uniform ops

def AvxOperand.interp {aw} [Labels] [AddressSize]
  (o : AvxOperand aw) (s : MachineData) (p : Std.Rco Int64)
  (ret : aw.type → MachineData → Effects) (checkAlign : Bool := false) :=
match o with
  | regOrMem rm => rm.interp s p ret checkAlign

@[kstep]
def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .z  => s.zf | .nz => !s.zf | .c  => s.cf | .nc => !s.cf
  | .a  => !s.cf && !s.zf | .be => s.cf || s.zf
  | .l => s.sf != s.of | .le => (s.sf != s.of) || s.zf
  | .ge => s.sf == s.of | .g => !s.zf && (s.sf == s.of)

@[kstep] def ShiftCountExpr.interp [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) := match c with
  | .cl => s.regs.rcx.toBitVec.take 8
  | .imm8 v => (v.interp p).toBitVec.take _
@[kstep] def ShiftCountExpr.interpMasked [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) (w : Width) : Nat :=
  (c.interp s p).toNat &&& match w with | .W64 => 0x3f | _ => 0x1f -- "masked to 5 bits (or 6 bits with a 64-bit operand)"

def RelRegOrMem.interp [Labels] [AddressSize]
  (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
  (ret : BitVec 64 → MachineData → Effects) :=
  match o with
  | .rel c => ret (p.upper + c.interp p).toBitVec s
  | .reg r => ret (s.regs.get r) s
  | .mem a => s.load ((a.interp s.regs p).zeroExtend _) .W64 ret

structure StatusFlags.from_result.Remaining where
  cf : Bool
  af : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq

-- TEMPORARY: definitions stolen from Lean 4.28's standard library, but with a
-- different name so that this file builds with both 4.27 and 4.28
namespace BitVec
def cpopNatRec_ {w} (x : BitVec w) (pos acc : Nat) : Nat :=
  match pos with
  | 0 => acc
  | n + 1 => x.cpopNatRec_ n (acc + (x.getLsbD n).toNat)

def cpop_ {w} (x : BitVec w) : BitVec w := BitVec.ofNat w (cpopNatRec_ x w 0)
end BitVec

@[kstep] def StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags :=
  { pf := (result.take 8).cpop_ % 2 == BitVec.zero _
    zf := result == BitVec.zero _
    sf := result.msb, cf := f.cf, af := f.af, of := f.of }

/-- The value a locked binary ALU operation writes: `old op src`. -/
@[kstep] def LockBinOp.eval (op : LockBinOp) {n} (old src : BitVec n) : BitVec n :=
  match op with
  | .add => old + src
  | .sub => old - src
  | .and => old &&& src
  | .or => old ||| src
  | .xor => old ^^^ src

/-- The flags of a locked binary ALU operation, the same formulas as the
unlocked `add`/`sub`/`and`/`or`/`xor`. `af` is the architecturally undefined
value the logic operations leave in `AF`; the arithmetic ones ignore it. -/
@[kstep] def LockBinOp.status (op : LockBinOp) {n} (old src v : BitVec n) (af : Bool) : StatusFlags :=
  match op with
  | .add => .from_result v {
      cf := v.unsigned != src.unsigned + old.unsigned
      af := (v.take 4).unsigned != (src.take 4).unsigned + (old.take 4).unsigned,
      of := v.signed != src.signed + old.signed }
  | .sub => .from_result v {
      cf := v.unsigned != old.unsigned - src.unsigned
      af := (v.take 4).unsigned != (old.take 4).unsigned - (src.take 4).unsigned,
      of := v.signed != old.signed - src.signed }
  | .and | .or | .xor => .from_result v { cf := false, of := false, af }

/-- The value a locked unary ALU operation writes. -/
@[kstep] def LockUnOp.eval (op : LockUnOp) {n} (old : BitVec n) : BitVec n :=
  match op with
  | .inc => old + 1
  | .dec => old - 1
  | .neg => -old
  | .not => ~~~old

/-- The flags of a locked unary ALU operation, the same formulas as the
unlocked `inc`/`dec`/`neg`; `not` leaves the flags alone. -/
@[kstep] def LockUnOp.status (op : LockUnOp) {n} (old v : BitVec n) (prev : StatusFlags) : StatusFlags :=
  match op with
  | .inc => .from_result v {
      cf := prev.cf
      af := (v.take 4).unsigned != (old.take 4).unsigned + 1,
      of := v.signed != old.signed + 1 }
  | .dec => .from_result v {
      cf := prev.cf
      af := (v.take 4).unsigned != (old.take 4).unsigned - 1,
      of := v.signed != old.signed - 1 }
  | .neg => .from_result v {
      cf := old != 0
      af := (old.take 4) != 0,
      of := v.signed != - old.signed }
  | .not => prev



set_option maxHeartbeats 1000000
@[kstep] def Operation.interp [Labels] [address_size : AddressSize]
  {w} (i : Operation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match (generalizing := false) (motive := Operation w → Effects) i with
  | .mov dst src => src.interp s p (fun val s => s.set dst val p next)
  | .movsx dst src => src.interp s p (fun val s => s.set dst (val.signExtend _) p next)
  | .movzx dst src => src.interp s p (fun val s => s.set dst (val.zeroExtend _) p next)
  | .push src =>
    src.interp s p (fun v s =>
    let rsp := s.regs.get64 .rsp - w.bytesv
    -- The store precedes the rsp commit, so a faulting push leaves rsp at its
    -- original value, as a restartable fault requires.
    s.store rsp v (fun s => next { s with regs := s.regs.set64 .rsp rsp }))
  | .pop dst =>
    let rsp := s.regs.get64 .rsp
    s.load rsp w (fun val s =>
    let s := { s with regs := s.regs.set64 .rsp (rsp + w.bytesv) }
    s.set dst val p next)
  | .setcc cc dst =>
    s.set dst (cc.interp s.status) p next
  | .cmovcc cc dst src =>
    src.interp s p (fun src s =>
    let v := if cc.interp s.status then src else s.regs.get dst
    next (s.setReg dst v))
-- Arithmetic
  | .lea dst src => next (s.setReg dst ((src.interp s.regs p).zeroExtend _))
  | .add dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b
    let status := .from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
      of := v.signed != a.signed + b.signed }
    { s with status }.set dst v p next))
  | .adc dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let c := s.status.cf
    let v := a + b + c
    let status := .from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned + c
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
      of := v.signed != a.signed + b.signed + c }
    { s with status }.set dst v p next))
  | .adcx dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b + s.status.cf
    let cf := v.unsigned != a.unsigned + b.unsigned + s.status.cf
    next { s with regs := s.regs.set dst v, status := { s.status with cf := cf }}))
  | .adox dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b + s.status.of
    let of := v.unsigned != a.unsigned + b.unsigned + s.status.of
    next { s with regs := s.regs.set dst v, status := { s.status with of := of }}))
  | .inc dst =>
    dst.interp s p (fun a s =>
    let v := a + 1
    let status := .from_result v {
      cf := s.status.cf
      af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
      of := v.signed != a.signed + 1 }
    { s with status }.set dst v p next)
  | .dec dst =>
    dst.interp s p (fun a s =>
    let v := a - 1
    let status := .from_result v {
      cf := s.status.cf
      af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
      of := v.signed != a.signed - 1 }
    { s with status }.set dst v p next)
  | .neg dst =>
    dst.interp s p (fun b s =>
    let v := -b
    let status := .from_result v {
      cf := b != 0
      af := (b.take 4) != 0,
      of := v.signed != - b.signed }
    { s with status }.set dst v p next)
  | .sub dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := b - a
    let status := .from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
      of := v.signed != b.signed - a.signed }
    { s with status }.set dst v p next))
  | .sbb dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let c := s.status.cf
    let v := b - a - c
    let status := .from_result v {
      cf := v.unsigned != b.unsigned - a.unsigned - c
      af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - c,
      of := v.signed != b.signed - a.signed - c }
    { s with status }.set dst v p next))
  | .cmp a b =>
    a.interp s p (fun a s =>
    b.interp s p (fun b s =>
    let v := a - b
    let status := .from_result v {
      cf := v.unsigned != a.unsigned - b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := v.signed != a.signed - b.signed }
    next { s with status }))
  | .mul src =>
    let a := s.regs.get (Reg.low .rax w)
    src.interp s p (fun b s =>
    let v := a * b
    let vn := a.unsigned * b.unsigned
    let s := if w == .W8
      then s.setReg (.low .rax .W16) (.ofInt _ vn)
      else (s.setReg (.low .rax w) v).setReg (.low .rdx w) (.ofInt _ (vn >>> w.bits))
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := v.unsigned != vn, pf, af, zf, sf, of := v.unsigned != vn }})))))
  | .mulx r_hi r_lo src1 =>
    src1.interp s p (fun a s =>
    let b := s.regs.get (.low .rdx w)
    let v := a.unsigned * b.unsigned
    let s := s.setReg r_lo (.ofInt _ v) -- if r_hi = r_li, hi is written:
    let s := s.setReg r_hi (.ofInt _ (v >>> w.bits))
    next s)
  -- imul1 and imul collectively describe variants of the same
  -- syntax level `imul` instruction, where imul1 is the 1-operand case
  | .imul1 src =>
    let a := s.regs.get (Reg.low .rax w)
    src.interp s p (fun b s =>
    let v := a.toInt * b.toInt
    let s := if w == .W8 then
      s.setReg (.low .rax .W16) (BitVec.ofInt 16 v)
    else
      let result := BitVec.ofInt (w.bits * 2) v
      let low := result.take w.bits
      let high := (result.drop w.bits).setWidth _
      (s.setReg (.low .rax w) low).setReg (.low .rdx w) high
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    let low := BitVec.ofInt w.bits v
    let cf := v != low.toInt
    next { s with status := { cf := cf, pf, af, zf, sf, of := cf }})))))
  | .imul dst src1 src2 =>
    src1.interp s p (fun a s =>
    src2.interp s p (fun b s =>
    let v := a * b
    s.set (match (generalizing := false) (motive := Option (RegOrMem w) → RegOrMem w)
             dst with | .some dst => dst | _ => src1) v p (fun s =>
    let cf := v.signed != a.signed * b.signed
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := cf, pf, af, zf, sf, of := cf }})))))))
-- Bitwise
  | .test a b =>
    a.interp s p (fun a s =>
    b.interp s p (fun b s =>
    let v := a &&& b
    undefined (fun af =>
    let status := .from_result v { cf := false, af, of := false}
    next { s with status})))
  | .and dst src | .or dst src | .xor dst src =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let v := match i with | .and _ _ => a &&& b | .or _ _ => a ||| b | _ => a ^^^ b
    undefined (fun af =>
    let status := .from_result v { cf := false, of := false, af }
    { s with status }.set dst v p next)))
  | .not dst =>
    dst.interp s p (fun a s =>
    let v := ~~~a
    s.set dst v p next)
  | .shl dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a <<< count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a <<< (count-1)).msb else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .shr dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.ushiftRight count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a.getLsbD (count-1)) else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof a.msb else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .sar dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.sshiftRight count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a.getLsbD (count-1)) else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof false else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .shrd dst src count =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := (((b.append a) >>> count).take w.bits).setWidth _
    (λ setstatus => if count >= w.bits then undefined setstatus else
      let cf := a.getLsbD (count-1)
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    { s with status }.set dst v p next)))
  | .shld dst src count =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := (((a.append b) <<< count).drop w.bits).setWidth _
    (λ setstatus => if count >= w.bits then undefined setstatus else
      let cf := (a <<< (count-1)).msb
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    { s with status }.set dst v p next)))
  | .rol dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.rotateLeft count
    let cf := v.getLsbD 0
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .ror dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let v := a.rotateRight count
    let cf := v.msb
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcr dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateRight count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcl dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then next s else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateLeft count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .bswap dst =>
    let a := s.regs.get dst
    match (generalizing := false) (motive := Width → Effects) w with
    | .W32 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24
      next (s.setReg dst (v.setWidth _))
    | .W64 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8
            ++ a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56
      next (s.setReg dst (v.setWidth _))
    | _ => undefined (fun v => next (s.setReg dst v))
  -- `TZCNT` (SDM vol. 2B): `dst` gets the number of trailing zero bits of
  -- `src`, or the operand size when `src` is 0 (`BitVec.ctz`, which is `w` at
  -- 0); `CF` is `src = 0`, `ZF` is `dst = 0`, and `OF`, `SF`, `AF` and `PF` are
  -- undefined. The instruction needs BMI1, which is assumed: Kraken has no
  -- CPUID feature model, and the encoding's meaning on a processor without
  -- BMI1 (where it executes as `BSF`) is not modelled. There is no 8-bit form;
  -- the parser rejects one.
  | .tzcnt dst src =>
    src.interp s p (fun a s =>
    let v := a.ctz
    undefined (λ of => undefined (λ sf => undefined (λ af => undefined (λ pf =>
    next { s with regs := s.regs.set dst v,
                  status := { cf := a == 0, zf := v == 0, of, sf, af, pf } })))))
  | .jcc cc l =>
    if cc.interp s.status
    then jmp (label l) s
    else next s
  | .jmp tgt =>
    tgt.interp s p (fun a s =>
    jmp (.ofBitVec a) s)
  | .call tgt =>
    tgt.interp s p (fun a s =>
    let rsp := s.regs.get64 .rsp - Width.W64.bytesv
    { s with regs := s.regs.set64 .rsp rsp }.store rsp (w:=.W64) p.upper.toBitVec (jmp (.ofBitVec a)))
  | .ret =>
    let rsp := s.regs.get64 .rsp
    s.load rsp .W64 (fun ra s =>
    jmp (.ofBitVec ra) { s with regs := s.regs.set64 .rsp (rsp + 8) })
  | nop _ | nopalign _ _ => next s
-- Atomics and barriers
  | .lockBin op dst src =>
    src.interp s p (fun b s =>
    s.rmwK .acqRel ((dst.interp s.regs p).zeroExtend _) w (fun a => some (op.eval a b)) (fun a s =>
    -- The choice is only consulted by the logic operations (undefined `AF`).
    undefined (fun af =>
    next { s with status := op.status a b (op.eval a b) af })))
  | .lockUn op dst =>
    s.rmwK .acqRel ((dst.interp s.regs p).zeroExtend _) w (fun a => some (op.eval a)) (fun a s =>
    next { s with status := op.status a (op.eval a) s.status })
  | .xchg r m =>
    let v := s.regs.get r
    m.rmw true s p (fun _ => some v) (fun old s => next (s.setReg r old))
  | .xadd lock dst src =>
    let b := s.regs.get src
    match dst with
    | .reg r =>
      -- `src` is written before `dst`, so `xadd %eax, %eax` leaves the sum.
      let a := s.regs.get r
      let v := a + b
      next { (s.setReg src a).setReg r v with status := LockBinOp.add.status a b v false }
    | .mem addr =>
      (RegOrMem.mem addr).rmw lock s p (fun a => some (a + b)) (fun a s =>
      next { s.setReg src a with status := LockBinOp.add.status a b (a + b) false })
  | .cmpxchg lock dst src =>
    let acc := s.regs.get (.low .rax w)
    let v := s.regs.get src
    dst.rmw lock s p (fun a => if a == acc then some v else none) (fun a s =>
    let d := acc - a
    let status := .from_result d {
      cf := d.unsigned != acc.unsigned - a.unsigned
      af := (d.take 4).unsigned != (acc.take 4).unsigned - (a.take 4).unsigned,
      of := d.signed != acc.signed - a.signed }
    let s := if a == acc then s else s.setReg (.low .rax w) a
    next { s with status })
  | .mfence => .fence .sy (fun _ => next s)
  -- `lfence`/`sfence` order no ordinary accesses on write-back memory under
  -- TSO (herd's `x86tso.cat` has no rule for them; neither drains the store
  -- buffer, SDM vol. 3A §8.2.5); they are emitted as `.ld`/`.st` fences so the
  -- memory model sees them. The one effect is `sfence`'s on non-temporal
  -- stores (`movnti`): `.st` orders them before later stores.
  | .lfence => .fence .ld (fun _ => next s)
  | .sfence => .fence .st (fun _ => next s)
  | .movnti dst src =>
    s.storeNT ((dst.interp s.regs p).zeroExtend _) (s.regs.get src) next

-- AVX Operations Interpreter
def AvxOperation.interp [Labels] [address_size : AddressSize]
  {w} (i : AvxOperation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) : Effects :=
match i with
  | .movups dst src => src.interp s p (fun val s => s.setAvxLegacy dst val p next)
  | .vmovups dst src => src.interp s p (fun val s => s.setAvx dst val p next)
  -- The aligned 16-byte moves are the accesses the SDM guarantees atomic.
  | .movaps dst src | .movapd dst src | .movdqa dst src =>
    src.interp s p (checkAlign := true) (atomic := w == .W128)
      (fun val s => s.setAvxLegacy dst val p (checkAlign := true) (atomic := w == .W128) next)
  | .movdqu dst src => src.interp s p (fun val s => s.setAvxLegacy dst val p next)
  -- TODO: MXCSR
  | .subps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      let v := BitVec.packedBinOp 32 (fun dst_chunk src_chunk =>
        let f_dst := BitVec.toFloat32 dst_chunk
        let f_src := BitVec.toFloat32 src_chunk
        Float32.toBitVec (f_dst - f_src)
      ) b a
      s.setAvxLegacy dst v p next))
  | .addps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      let v := BitVec.packedBinOp 32 (fun dst_chunk src_chunk =>
        let f_dst := BitVec.toFloat32 dst_chunk
        let f_src := BitVec.toFloat32 src_chunk
        Float32.toBitVec (f_dst + f_src)
      ) b a
      s.setAvxLegacy dst v p next))
  | .mulps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      s.setAvxLegacy dst (BitVec.packedBinOp 32 BitVec.f32mul b a) p next))
  | .xorps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      s.setAvxLegacy dst (b ^^^ a) p next))
  -- VEX-encoded forms: a register destination is written with the bits above
  -- the operation width cleared, and only `vmovaps` requires an aligned memory
  -- operand.
  | .vmovaps dst src | .vmovapd dst src | .vmovdqa dst src =>
    src.interp s p (checkAlign := true) (atomic := w == .W128)
      (fun val s => s.setAvx dst val p (checkAlign := true) (atomic := w == .W128) next)
  | .vmovdqu dst src => src.interp s p (fun val s => s.setAvx dst val p next)
  | .vxorps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (s.zmms.get src1 ^^^ b)))
  | .vaddps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32 BitVec.f32add (s.zmms.get src1) b)))
  | .vmulps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get src1) b)))
  | .vfmadd231ps dst src1 src2 =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst
        (BitVec.packedTernOp 32 BitVec.f32fma (s.zmms.get src1) b (s.zmms.get dst))))
  | .vshufps dst src1 src2 imm =>
    src2.interp s p (fun b s =>
      next (s.setAvxReg dst (BitVec.packedBinOp 128 (BitVec.shufps128 imm) (s.zmms.get src1) b)))
  | .vextractf128 dst src imm =>
    next (s.setAvxReg dst ((s.zmms.get src).extractLsb' (128 * (imm.toNat % 2)) 128))
  | .vmovhlps dst src1 src2 =>
    next (s.setAvxReg dst
      ((s.zmms.get src1).extractLsb' 64 64 ++ (s.zmms.get src2).extractLsb' 64 64))
  | .vmovss dst src1 src2 =>
    next (s.setAvxReg dst
      ((s.zmms.get src1).extractLsb' 32 96 ++ (s.zmms.get src2).extractLsb' 0 32))
  | .vaddss dst src1 src2 =>
    let a := s.zmms.get src1
    let b := s.zmms.get src2
    next (s.setAvxReg dst
      (a.extractLsb' 32 96 ++ BitVec.f32add (a.extractLsb' 0 32) (b.extractLsb' 0 32)))
  | .vzeroupper => next { s with zmms := s.zmms.zeroUpper }
  | .cmpxchg16b lock dst =>
    let addr : BitVec 64 := (dst.interp s.regs p).zeroExtend _
    let acc : BitVec 128 := s.regs.get64 .rdx ++ s.regs.get64 .rax
    let v : BitVec 128 := s.regs.get64 .rcx ++ s.regs.get64 .rbx
    let op := fun old : BitVec 128 => if old == acc then some v else none
    -- Only ZF changes; on failure `rdx:rax` takes the old value.
    let k := fun (old : BitVec 128) (s : MachineData) =>
      let s := if old == acc then s else
        { s with regs := (s.regs.set64 .rax (old.extractLsb' 0 64)).set64 .rdx (old.extractLsb' 64 64) }
      next { s with status := { s.status with zf := old == acc } }
    if isAligned 16 addr then
      if lock then s.rmw16K .acqRel addr op k else s.rmw16Plain addr op k
    else .gp_unaligned addr 16

@[kstep]
def Instr.interp [Labels]
  (i : Instr) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  require_exec_access p (fun _unit =>
    match i with
      | .regular addr_sz op_sz op =>
          Operation.interp (w := op_sz) (address_size := .mk addr_sz) op p s next jmp
      | .avx addr_sz op_sz op =>
          AvxOperation.interp (w := op_sz) (address_size := .mk addr_sz) op p s next
  )

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
    | .gp_unaligned addr w => .error s!"#GP: Memory op at {repr addr} did not have mandatory alignment of {w}"
    | .require_read_access _ _ ok => handleEffects (ok ())
    | .require_write_access _ _ ok => handleEffects (ok ())
    | .require_exec_access _ ok => handleEffects (ok ())
    | .nonmem_load _ addr _ _ => .error s!"Load at unmapped address {repr addr}"
    | .nonmem_store _ addr _ _ => .error s!"Store at unmapped address {repr addr}"
    | .sync_load _ _ _ addr _ _ => .error s!"Load at unmapped address {repr addr}"
    | .sync_store _ _ _ addr _ _ => .error s!"Store at unmapped address {repr addr}"
    | .rmw _ _ addr _ _ _ => .error s!"Read-modify-write at unmapped address {repr addr}"
    | .fence _ ok => handleEffects (ok ())
    | .require_read_access_avx _ _ _ ok => handleEffects (ok ())
    | .require_write_access_avx _ _ _ ok => handleEffects (ok ())
    | .nonmem_load_avx _ _ addr _ _ => .error s!"Vector load at unmapped address {repr addr}"
    | .nonmem_store_avx _ _ addr _ _ => .error s!"Vector store at unmapped address {repr addr}"
    | .rmw16 _ _ addr _ _ => .error s!"16-byte read-modify-write at unmapped address {repr addr}"
    | @Effects.undefined _ t cont => handleEffects (cont (t.from_hash (hash s.1.regs)))

def Directive.fakeSize (hashOfProgram : UInt64) (d : Directive) : Nat :=
  match d with
  | .label _ => 0
  | .instr (.regular _ _ (.nop sz)) => sz -- may be zero
  | .instr i => (1 + hash (hashOfProgram, i) % 15).toNat
  | .byteArray bs => bs.size

def Program.fakeLayout (prog : Program) : Executable :=
  let : Inhabited Directive := .mk (.byteArray (.mk #[]))
  let h := hash prog;
  let layout : Layout := { start := h.toInt64<<<16, size i := prog[i]!.fakeSize h }
  layout prog

abbrev eval [layout : Layout] (prog : Program) := Executable.eval (layout prog)

/-- info: Except.ok 42 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr (.regular .W64 .W64 (.lea (.low .rax .W64) (.mk .none .none (.int64 41)))),
    .instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64)))),
    .instr (.regular .W64 .W64 .ret) ]
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 0x1337, regs := {rsp := 0x100} }
  (Executable.eval exe (data, start) (fun (_, pc) => pc = 0x1337)).bind (fun s => .ok s.1.regs.rax)

/-! Atomics on mapped memory. The cell at `0x200` is the memory operand, `0x100`
holds the return address. -/

private def atomicsExe (body : List Directive) : Executable :=
  Program.fakeLayout ([.label "main"] ++ body ++ [.instr (.regular .W64 .W64 .ret)])

private def runAtomics (body : List Directive) (rax rbx cell : Int64) :
    Except String (UInt64 × Option Int × Bool × Bool) :=
  let exe := atomicsExe body
  let start := (Executable.labels exe).label "main"
  let data : MachineData := {
    dmem := Mem.storeInt (Mem.storeInt {} 0x100 8 0x1337) 0x200 8 cell.toInt,
    regs := { rsp := 0x100, rax := rax.toUInt64, rbx := rbx.toUInt64 } }
  (Executable.eval exe (data, start) (fun (_, pc) => pc = 0x1337)).map
    (fun s => (s.1.regs.rax, Mem.loadInt s.1.dmem 0x200 8, s.1.status.zf, s.1.status.cf))

private def cell : AddrExpr := ⟨none, none, .int64 0x200⟩

-- `lock addq $30, cell` then `xchgq %rax, cell`: the cell is 12 + 30, then
-- swapped with rax.
/-- info: Except.ok (42, some 5, false, false) -/
#guard_msgs in
#eval runAtomics [
  .instr (.regular .W64 .W64 (.lockBin .add cell (.imm (.int64 30)))),
  .instr (.regular .W64 .W64 (.xchg (.low .rax .W64) (.mem cell))) ] 5 0 12

-- `lock xaddq %rax, cell`: rax gets the old cell, the cell the sum.
/-- info: Except.ok (7, some 12, false, false) -/
#guard_msgs in
#eval runAtomics [ .instr (.regular .W64 .W64 (.xadd true (.mem cell) (.low .rax .W64))) ] 5 0 7

-- `lock cmpxchgq %rbx, cell`, equal: the cell takes rbx, ZF is set.
/-- info: Except.ok (5, some 9, true, false) -/
#guard_msgs in
#eval runAtomics [ .instr (.regular .W64 .W64 (.cmpxchg true (.mem cell) (.low .rbx .W64))) ] 5 9 5

-- `lock cmpxchgq %rbx, cell`, unequal: rax takes the cell, which is unchanged;
-- the flags are those of `6 - 9`.
/-- info: Except.ok (9, some 9, false, true) -/
#guard_msgs in
#eval runAtomics [ .instr (.regular .W64 .W64 (.cmpxchg true (.mem cell) (.low .rbx .W64))) ] 6 11 9

-- `lock subq %rbx, cell` to zero: ZF.
/-- info: Except.ok (1, some 0, true, false) -/
#guard_msgs in
#eval runAtomics [ .instr (.regular .W64 .W64 (.lockBin .sub cell (.reg (.low .rbx .W64)))) ] 1 4 4

-- Fences do nothing on one thread.
/-- info: Except.ok (1, some 2, false, false) -/
#guard_msgs in
#eval runAtomics [
  .instr (.regular .W64 .W64 .mfence),
  .instr (.regular .W64 .W64 .lfence),
  .instr (.regular .W64 .W64 .sfence) ] 1 0 2

/-! `cmpxchg16b` and the 16-byte moves. The 16-byte cell at `0x200` holds
`hi:lo`; the result is `rax`, `rdx`, the cell and ZF. -/

private def run16 (body : List Directive) (rax rdx rbx rcx hi lo : UInt64) :
    Except String (UInt64 × UInt64 × Option Int × Bool) :=
  let exe := atomicsExe body
  let start := (Executable.labels exe).label "main"
  let cell : BitVec 128 := hi.toBitVec ++ lo.toBitVec
  let data : MachineData := {
    dmem := Mem.storeInt (Mem.storeInt (Mem.storeInt {} 0x100 8 0x1337) 0x200 16 cell.toNat)
      0x300 32 0,
    regs := { rsp := 0x100, rax, rdx, rbx, rcx } }
  (Executable.eval exe (data, start) (fun (_, pc) => pc = 0x1337)).map
    (fun s => (s.1.regs.rax, s.1.regs.rdx, Mem.loadInt s.1.dmem 0x200 16, s.1.status.zf))

private def avx128 (op : AvxOperation .W128) : Directive := .instr (.avx .W64 .W128 op)

-- `lock cmpxchg16b cell`, equal: the cell takes `rcx:rbx` (`2^64 * 4 + 3`), ZF is set.
/-- info: Except.ok (1, 2, some 73786976294838206467, true) -/
#guard_msgs in
#eval run16 [avx128 (.cmpxchg16b true cell)] 1 2 3 4 2 1

-- `cmpxchg16b cell`, unequal: `rdx:rax` takes the cell, which is unchanged; ZF clear.
/-- info: Except.ok (7, 9, some 166020696663385964551, false) -/
#guard_msgs in
#eval run16 [avx128 (.cmpxchg16b false cell)] 1 2 3 4 9 7

-- A misaligned `cmpxchg16b` raises `#GP` before any access.
/-- info: Except.error "#GP: Memory op at 0x0000000000000208#64 did not have mandatory alignment of 16" -/
#guard_msgs in
#eval run16 [avx128 (.cmpxchg16b true ⟨none, none, .int64 0x208⟩)] 1 2 3 4 2 1

-- Off `dmem`, the locked form is one `rmw16`, the unlocked form a vector load.
/-- info: Except.error "16-byte read-modify-write at unmapped address 0x0000000000000400#64" -/
#guard_msgs in
#eval run16 [avx128 (.cmpxchg16b true ⟨none, none, .int64 0x400⟩)] 1 2 3 4 2 1

/-- info: Except.error "Vector load at unmapped address 0x0000000000000400#64" -/
#guard_msgs in
#eval run16 [avx128 (.cmpxchg16b false ⟨none, none, .int64 0x400⟩)] 1 2 3 4 2 1

-- The cell goes out through an unaligned `movdqu` store to `0x301`, the cell
-- is overwritten with the zeros at `0x310`, and it comes back through an
-- unaligned `vmovdqu` load.
/-- info: Except.ok (0, 0, some 36893488147419103233, false) -/
#guard_msgs in
#eval run16 [avx128 (.movdqa (.avx (.xmm .mm1)) (.mem cell)),
  avx128 (.movdqu (.mem ⟨none, none, .int64 0x301⟩) (.avx (.xmm .mm1))),
  avx128 (.movdqa (.avx (.xmm .mm3)) (.mem ⟨none, none, .int64 0x310⟩)),
  avx128 (.movdqa (.mem cell) (.avx (.xmm .mm3))),
  avx128 (.vmovdqu (.avx (.xmm .mm2)) (.mem ⟨none, none, .int64 0x301⟩)),
  avx128 (.movdqa (.mem cell) (.avx (.xmm .mm2)))] 0 0 0 0 2 1

-- `movdqa` from a misaligned address raises `#GP`; `vmovdqu` does not.
/-- info: Except.error "#GP: Memory op at 0x0000000000000201#64 did not have mandatory alignment of 16" -/
#guard_msgs in
#eval run16 [avx128 (.movdqa (.avx (.xmm .mm1)) (.mem ⟨none, none, .int64 0x201⟩))] 0 0 0 0 2 1

-- `vmovdqu 0x201, %xmm1` reads 15 bytes of the cell and one unmapped byte.
/-- info: Except.error "Vector load at unmapped address 0x0000000000000201#64" -/
#guard_msgs in
#eval run16 [avx128 (.vmovdqu (.avx (.xmm .mm1)) (.mem ⟨none, none, .int64 0x201⟩))] 0 0 0 0 2 1

-- `vmovdqa cell, %xmm2; vmovapd %xmm2, cell`: the cell round-trips.
/-- info: Except.ok (0, 0, some 36893488147419103233, false) -/
#guard_msgs in
#eval run16 [avx128 (.vmovdqa (.avx (.xmm .mm2)) (.mem cell)),
  avx128 (.vmovapd (.mem cell) (.avx (.xmm .mm2)))] 0 0 0 0 2 1

-- A locked RMW on an unmapped address reaches `handleEffects` as the `rmw`
-- effect, a fault in the sequential evaluator.
/-- info: Except.error "Read-modify-write at unmapped address 0x0000000000000300#64" -/
#guard_msgs in
#eval runAtomics [
  .instr (.regular .W64 .W64 (.lockUn .inc ⟨none, none, .int64 0x300⟩)) ] 1 0 2

/-! `tzcnt`. The result is `rax`; the cell, ZF and CF as above. -/

private def tz {w : Width} (dst : Reg w) (src : RegOrMem w) : List Directive :=
  [.instr (.regular .W64 w (.tzcnt dst src))]

-- `tzcntq %rbx, %rax` with `rbx = 0`: the operand size, CF set, ZF clear.
/-- info: Except.ok (64, some 0, false, true) -/
#guard_msgs in
#eval runAtomics (tz (.low .rax .W64) (.reg (.low .rbx .W64))) 5 0 0

-- Bit 0 set: the count is 0, so ZF is set and CF clear.
/-- info: Except.ok (0, some 0, true, false) -/
#guard_msgs in
#eval runAtomics (tz (.low .rax .W64) (.reg (.low .rbx .W64))) 5 0x2B 0

-- Only the high bit set: 63.
/-- info: Except.ok (63, some 0, false, false) -/
#guard_msgs in
#eval runAtomics (tz (.low .rax .W64) (.reg (.low .rbx .W64))) 5 Int64.minValue 0

-- `tzcntq cell, %rax`, a memory source: `0x80` has 7 trailing zeros.
/-- info: Except.ok (7, some 128, false, false) -/
#guard_msgs in
#eval runAtomics (tz (.low .rax .W64) (.mem cell)) 5 0 0x80

-- `tzcntl %ebx, %eax` with `ebx = 0` (the upper half of `rbx` set): 32, and
-- the upper half of `rax` is cleared.
/-- info: Except.ok (32, some 0, false, true) -/
#guard_msgs in
#eval runAtomics (tz (.low .rax .W32) (.reg (.low .rbx .W32))) (-1) 0x100000000 0

-- `tzcntw %bx, %ax` with `bx = 0`: 16, merged into the low 16 bits of `rax`.
/-- info: Except.ok (18446744073709486096, some 0, false, true) -/
#guard_msgs in
#eval runAtomics (tz (.low .rax .W16) (.reg (.low .rbx .W16))) (-1) 0 0

-- The value is `BitVec.ctz`, the operand size at 0.
#guard (0#64).ctz == 64#64 && (0x80#64).ctz == 7#64 && (0x8000000000000000#64).ctz == 63#64 &&
    (0#16).ctz == 16#16
example : (0#64).ctz = 64#64 ∧ (0x8000000000000000#64).ctz = 63#64 := by decide +kernel
