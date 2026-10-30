/-
**The allocator on x64**: the x64 twin of `Spike/Lib/A64Alloc.lean`. The
runtime's `scc_rt_alloc(h, k, u)` (`Scc/Lower/Runtime.lean`, `allocF`, the
stride-16 allocator; its blocks in `Scc/Sem/HeapCtr.lean`) as one `Seg`
from its entry, called at a source buffer allocation
`let x = newBuf a τ in e` of `n` elements, to its return (the source's
allocation step taken) or its heap abort.

    scc_rt_alloc(h = %rdi, k = %rsi, u = %rdx):
      prologue (frame of 144 bytes below %rbp, h, k, u at -8, -16, -24(%rbp))
      entry: if k ≥ 2^28 goto full
      cnt:   old = lock xadd [scc_rt_heap_use], u
             if old + u > cells goto slow                  -- cells = 2^22
      slow:  if old > cells goto spin; goto full
      spin:  goto spin
      full:  %rdi = 2; call scc_rt_abort
      ok:    m = (h >> 22) & 16383; s = scc_rt_heap + 16·old
             [s + 8·k·m] = h | k << 36                     -- the header
             %rax = s + 8·k·m + 8; epilogue; ret

The text is the same in every program `scc` compiles for x64 (it is the
runtime's); the blocks below are its listing, parsed by Kraken's own
`parse`, with the sizes of the assembler's cells. The region is the frame,
offsets `[-160, 8)` from the `%rsp` at entry: the return address at `0`,
the saved `%rbp` at `-8`, the locals down to `-152`, and the return address
`call scc_rt_abort` pushes at `-160`.

**The specification** (`Call`, `Call.OK`): as on AArch64. The source is at
the allocation, no hold pending, `k = n` and `u` the buffer's units
(`ms.units`), `h` a header whose trace-word field `m` gives the buffer's
base offset (`ms.off n τ = 8·n·m + 8`); the labels `scc_rt_heap_use` and
`scc_rt_heap` are the counter (`ms.ctr`) and the arena (`ms.heap`), the
arena has `ms.cells = 2^22` cells and room for its addresses; the runtime
memory's value invariant `ms.G` allows the counter's add (within the cells)
and each header the code may store (at an old count above the counter's
floor, `ms.lo`), at an address the runtime owns and maps
for writing (`ms.mp`); the element type has its accesses.

- **entry** (`.e`): pc at `scc_rt_alloc`, `%rsp` at offset 0, `%rdi`,
  `%rsi`, `%rdx` the arguments, `%rbp` the caller's (`fp`), the return
  address `ra` at offset 0;
- **return** (`Ea`, through `Out.alloc` at the `ret`, into the allocation's
  continuation `ms.xa`, `hxa`): pc at `ra`, `%rsp` at offset 8, `%rbp`
  restored, the source past its allocation step, `x` bound to a fresh
  label, `%rax` the base `ms.heap + 16·old + ms.off n τ` for the counter's
  old value `old`, with `old + u ≤ cells`. The exit `.ret` is kept in the
  graph but not reached;
- **abort** (exit `.abort`): pc at `scc_rt_abort` with `%rdi = 2`, the
  source at the allocation: either `k ≥ 2^28`, or the counter's add
  happened (the hold records its old value) and crossed the cells
  (`old ≤ cells < old + u`).

The counter's add is `ctr_nd` (`Out.ctrRmw`): with one thread the old value
it reads is within the cells, so `slow` never goes to `spin` and `ok`'s
arithmetic does not wrap. The header store is `rtst_nd` (`Out.rtStore`),
the `ret` is `alloc_nd` (`Out.alloc`), the label addresses are `si_nd`, the
shifts and logical operations (undefined flags) `flag_nd`. The counter and
the headers are outside the frame and outside the thread's private memory
(`hmem`).

`seg_allocW` is the segment inside a predicate `W` (one obligation per
node, `AllocW`) for any frame condition no write inside the frame breaks
(`seg_allocW_at` from any node), in any valid layout of cells holding the code (`allocIn`; `hello1Cells`'s
is `hello1_allocIn`); `seg_alloc` is it inside the trivial predicate at
`DFrame R m0`.
-/
import Spike.Lib.X64AllocNodes
import Scc.Cert.Rt.X64AllocIn
import Spike.Lib.X64Flags
import Spike.Lib.X64CodeSegs
import Spike.Lib.X64Hello1Code

namespace Spike.Lib.X64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add')

set_option linter.unusedSimpArgs false

#guard allocIn SccCode.hello1Cells

/-- The code's check on `hello1Cells`. -/
theorem hello1_allocIn : allocIn SccCode.hello1Cells = true := by decide +kernel

/-! ## Arithmetic -/

/-- **The header's trace-word field** `m`. -/
def mOf (h : BitVec 64) : BitVec 64 := h >>> 22 &&& 16383#64

theorem mOf_lt (h : BitVec 64) : (mOf h).toNat < 2 ^ 14 := by
  simp only [mOf, BitVec.toNat_and, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- **The base the code computes** does not wrap: `heap + 16·old + 8·k·m`,
for `old ≤ 2^22`, `k < 2^28`, `m < 2^14` and room for `2^46` bytes past
the arena's base. -/
theorem base_toNat {H o k m : BitVec 64} (ho : o.toNat ≤ 2 ^ 22) (hk : k.toNat < 2 ^ 28) (hm : m.toNat < 2 ^ 14)
    (hH : H.toNat + 2 ^ 46 ≤ 2 ^ 64) :
    (H + o <<< 4 + (k * m) <<< 3).toNat = H.toNat + 16 * o.toNat + 8 * (k.toNat * m.toNat) := by
  have hkm : k.toNat * m.toNat < 2 ^ 42 :=
    calc k.toNat * m.toNat < 2 ^ 28 * 2 ^ 14 := Nat.mul_lt_mul'' hk hm
      _ = 2 ^ 42 := by rw [← Nat.pow_add]
  have hkm' : (k * m).toNat = k.toNat * m.toNat := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  have h3 : ((k * m) <<< 3).toNat = 8 * (k.toNat * m.toNat) := by
    rw [BitVec.toNat_shiftLeft, hkm', Nat.shiftLeft_eq]; omega
  have h4 : (o <<< 4).toNat = 16 * o.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  rw [BitVec.toNat_add, BitVec.toNat_add, h3, h4]
  omega

/-- The returned base, one word past the header. -/
theorem base8_toNat {H o k m : BitVec 64} (ho : o.toNat ≤ 2 ^ 22) (hk : k.toNat < 2 ^ 28) (hm : m.toNat < 2 ^ 14)
    (hH : H.toNat + 2 ^ 46 ≤ 2 ^ 64) :
    (H + o <<< 4 + (k * m) <<< 3 + 8#64).toNat = H.toNat + 16 * o.toNat + (8 * (k.toNat * m.toNat) + 8) := by
  have hkm : k.toNat * m.toNat < 2 ^ 42 :=
    calc k.toNat * m.toNat < 2 ^ 28 * 2 ^ 14 := Nat.mul_lt_mul'' hk hm
      _ = 2 ^ 42 := by rw [← Nat.pow_add]
  rw [BitVec.toNat_add, base_toNat ho hk hm hH]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The shift counts the code loads into `%rcx`. -/
theorem cl_vals : ((22#64).take 8).toNat &&& 63 = 22 ∧ ((4#64).take 8).toNat &&& 63 = 4 ∧
    ((3#64).take 8).toNat &&& 63 = 3 ∧ ((36#64).take 8).toNat &&& 63 = 36 := by decide

section Vals

variable {σ : AS} {a c : BitVec 64} (ha : σ.regs.rax.toBitVec = a) (hc : σ.regs.rcx.toBitVec = c)
  (fl : StatusFlags)
include ha hc

/-- `%rax` after `shrq %cl, %rax`. -/
theorem shr_rax : ((FI.shr_cl .rax).step σ fl).regs.rax.toBitVec = a.ushiftRight ((c.take 8).toNat &&& 63) := by
  simp [FI.step, FI.regs, clOf, Reg64s.set64, Reg64s.get64, ha, hc]

/-- `%rax` after `shlq %cl, %rax`. -/
theorem shl_rax : ((FI.shl_cl .rax).step σ fl).regs.rax.toBitVec = a <<< ((c.take 8).toNat &&& 63) := by
  simp [FI.step, FI.regs, clOf, Reg64s.set64, Reg64s.get64, ha, hc]

/-- `%rax` after `andq %rcx, %rax`. -/
theorem and_rax : ((FI.and_rr .rax .rcx).step σ fl).regs.rax.toBitVec = a &&& c := by
  simp [FI.step, FI.regs, clOf, Reg64s.set64, Reg64s.get64, ha, hc]

/-- `%rax` after `orq %rcx, %rax`. -/
theorem or_rax : ((FI.or_rr .rax .rcx).step σ fl).regs.rax.toBitVec = a ||| c := by
  simp [FI.step, FI.regs, clOf, Reg64s.set64, Reg64s.get64, ha, hc]

/-- `%rax` after `imulq %rcx, %rax`. -/
theorem imul_rax : ((FI.imul_rr .rax .rcx).step σ fl).regs.rax.toBitVec = a * c := by
  simp [FI.step, FI.regs, clOf, Reg64s.set64, Reg64s.get64, ha, hc]

end Vals

/-! ## The specification -/

/-- **A call of the allocator**: the source's buffer allocation
`let x = newBuf a τ in e` of `n` elements (`a` evaluating to the words
`ws` of type `ta`) from the control `c0`, the header `h`, the caller's
`%rbp` and the return address `ra`. -/
structure Call where
  c0 : Ctl
  x : String
  a : CoreTerm.At
  τ : Ty
  e : Expr
  ta : Ty
  ws : List TermRun.Word
  n : Nat
  h : BitVec 64
  fp : BitVec 64
  ra : BitVec 64

/-- The element count argument. -/
def Call.k (q : Call) : BitVec 64 := BitVec.ofNat 64 q.n
/-- The units argument. -/
def Call.u (ms : MemSide isa) (q : Call) : BitVec 64 := BitVec.ofNat 64 (ms.units q.n q.τ)
/-- The header the allocator stores. -/
def Call.hdr (q : Call) : BitVec 64 := q.h ||| q.k <<< 36
/-- The header's address for the counter's old value `o`. -/
def Call.hdrAt (ms : MemSide isa) (q : Call) (o : Nat) : Nat := ms.heap + 16 * o + 8 * (q.n * (mOf q.h).toNat)

/-- **The call's premises**: see the module docstring. -/
structure Call.OK (ms : MemSide isa) (lab : Label → Int64) (q : Call) : Prop where
  term : q.c0.term = .let_ q.x (.newBuf q.a q.τ) q.e
  ev : TermRun.evalAt q.c0.env q.a = some (q.ta, q.ws)
  num : TermRun.numOf q.ws = some q.n
  hold : q.c0.hold = none
  n_lt : q.n < 2 ^ 64
  ctr : (lab "scc_rt_heap_use").toBitVec = BitVec.ofNat 64 ms.ctr
  heap : (lab "scc_rt_heap").toBitVec.toNat = ms.heap
  room : ms.heap + 2 ^ 46 ≤ 2 ^ 64
  cells : ms.cells = 4194304
  units : ms.units q.n q.τ < 2 ^ 63
  off : ms.off q.n q.τ = 8 * (q.n * (mOf q.h).toNat) + 8
  accs : ∃ us, TermRun.accs (TermRun.close [] q.τ) = some us
  rt : ms.rt (BitVec.ofNat 64 ms.ctr).toNat
  mp : ms.mp (ctrLoc ms) true
  grow : ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells →
    ms.G (ctrLoc ms) ((old.setWidth 64 + q.u ms).setWidth 128)
  hdr : ∀ o, ms.lo o → o + ms.units q.n q.τ ≤ ms.cells →
    ms.rt (q.hdrAt ms o) ∧ ms.mp ⟨BitVec.ofNat 64 (q.hdrAt ms o), 8⟩ true ∧
      ms.G ⟨BitVec.ofNat 64 (q.hdrAt ms o), 8⟩ (q.hdr.setWidth 128)

/-- The internal nodes: the blocks, the single instructions (`f…` with
undefined flags, `cnt`/`s2` the label addresses, `rmw` the counter's add,
`hdr` the header's store, `ret`). -/
inductive AN where
  | e | entry | j1 | cnt | c1 | rmw | c2 | j2 | slow | j3 | full | ok | f1 | o1 | f2 | o2 | s2 | o3 | f3 | o4
  | f4 | o5 | f5 | o6 | f6 | o7 | f7 | o8 | hdr | o9 | ret

/-- The exits. -/
inductive AX where
  | ret | abort

section Spec

variable (lab : Label → Int64) (ms : MemSide isa) (q : Call)

/-- The frame's fixed cells: the return address, the caller's `%rbp`, the
arguments. -/
def Fr (σ : AS) : Prop :=
  σ.slot 0 = q.ra ∧ σ.slot (-8) = q.fp ∧ σ.slot (-16) = q.h ∧ σ.slot (-24) = q.k ∧ σ.slot (-32) = q.u ms

/-- Before the counter's add: the source at the call, the count checked. -/
def Jc (σ : AS) (c : Ctl) : Prop := c = q.c0 ∧ Fr ms q σ ∧ q.n < 2 ^ 28

/-- After the add, within the cells: the hold records the old value `o`,
in its cell, above the counter's floor (`ms.lo`). -/
def Jok (o : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = holdCtr ms q.c0 o ∧ o.toNat + ms.units q.n q.τ ≤ ms.cells ∧ Fr ms q σ ∧ q.n < 2 ^ 28 ∧ σ.slot (-48) = o ∧
    ms.lo o.toNat

/-- After the add, past the cells. -/
def Jslow (o : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = holdCtr ms q.c0 o ∧ o.toNat ≤ ms.cells ∧ ms.cells < o.toNat + ms.units q.n q.τ ∧ Fr ms q σ ∧
    σ.slot (-48) = o

/-- On the way to the heap abort. -/
def Jfull (c : Ctl) : Prop :=
  (c = q.c0 ∧ 2 ^ 28 ≤ q.n) ∨
    ∃ o : BitVec 64, c = holdCtr ms q.c0 o ∧ o.toNat ≤ ms.cells ∧ ms.cells < o.toNat + ms.units q.n q.τ

/-- The arena's base. -/
abbrev H : BitVec 64 := (lab "scc_rt_heap").toBitVec

/-- The object's start and the trace words' bytes, in their cells. -/
def Jbase (o : BitVec 64) (σ : AS) : Prop :=
  σ.slot (-96) = H lab + o <<< 4 ∧ σ.slot (-112) = (q.k * mOf q.h) <<< 3

/-- **The nodes.** -/
def N : AN → ND
  | .e => ⟨lab fnL, oE, fun σ c => c = q.c0 ∧ σ.regs.rbp.toBitVec = q.fp ∧ σ.slot 0 = q.ra ∧
      σ.regs.rdi.toBitVec = q.h ∧ σ.regs.rsi.toBitVec = q.k ∧ σ.regs.rdx.toBitVec = q.u ms⟩
  | .entry => ⟨lab entryL, oI, fun σ c => c = q.c0 ∧ Fr ms q σ⟩
  | .j1 => ⟨lab entryL + Int64.ofNat 16, oI, Jc ms q⟩
  | .cnt => ⟨lab cntL, oI, Jc ms q⟩
  | .c1 => ⟨lab cntL + Int64.ofNat 7, oI, fun σ c => Jc ms q σ c ∧
      σ.regs.rax.toBitVec = (lab "scc_rt_heap_use").toBitVec⟩
  | .rmw => ⟨lab cntL + Int64.ofNat 19, oI, fun σ c => Jc ms q σ c ∧
      σ.regs.rcx.toBitVec = (lab "scc_rt_heap_use").toBitVec ∧ σ.regs.rax.toBitVec = q.u ms⟩
  | .c2 => ⟨lab cntL + Int64.ofNat 24, oI, fun σ c => ∃ o : BitVec 64,
      c = holdCtr ms q.c0 o ∧ o.toNat ≤ ms.cells ∧ Fr ms q σ ∧ q.n < 2 ^ 28 ∧ σ.regs.rax.toBitVec = o ∧
      ms.lo o.toNat⟩
  | .j2 => ⟨lab cntL + Int64.ofNat 59, oI, fun σ c => ∃ o, Jok ms q o σ c⟩
  | .slow => ⟨lab slowL, oI, fun σ c => ∃ o, Jslow ms q o σ c⟩
  | .j3 => ⟨lab slowL + Int64.ofNat 16, oI, fun σ c => ∃ o, Jslow ms q o σ c⟩
  | .full => ⟨lab fullL, oI, fun _ c => Jfull ms q c⟩
  | .ok => ⟨lab okL, oI, fun σ c => ∃ o, Jok ms q o σ c⟩
  | .f1 => ⟨lab okL + Int64.ofNat 11, oI, fun σ c => ∃ o, Jok ms q o σ c ∧
      σ.regs.rax.toBitVec = q.h ∧ σ.regs.rcx.toBitVec = 22#64⟩
  | .o1 => ⟨lab okL + Int64.ofNat 14, oI, fun σ c => ∃ o, Jok ms q o σ c ∧
      σ.regs.rax.toBitVec = q.h.ushiftRight 22⟩
  | .f2 => ⟨lab okL + Int64.ofNat 29, oI, fun σ c => ∃ o, Jok ms q o σ c ∧
      σ.regs.rax.toBitVec = q.h.ushiftRight 22 ∧ σ.regs.rcx.toBitVec = 16383#64⟩
  | .o2 => ⟨lab okL + Int64.ofNat 32, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ σ.regs.rax.toBitVec = mOf q.h⟩
  | .s2 => ⟨lab okL + Int64.ofNat 36, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ σ.slot (-72) = mOf q.h⟩
  | .o3 => ⟨lab okL + Int64.ofNat 43, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ σ.slot (-72) = mOf q.h ∧
      σ.regs.rax.toBitVec = H lab⟩
  | .f3 => ⟨lab okL + Int64.ofNat 58, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ σ.slot (-72) = mOf q.h ∧
      σ.slot (-80) = H lab ∧ σ.regs.rax.toBitVec = o ∧ σ.regs.rcx.toBitVec = 4#64⟩
  | .o4 => ⟨lab okL + Int64.ofNat 61, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ σ.slot (-72) = mOf q.h ∧
      σ.slot (-80) = H lab ∧ σ.regs.rax.toBitVec = o <<< 4⟩
  | .f4 => ⟨lab okL + Int64.ofNat 88, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ σ.slot (-96) = H lab + o <<< 4 ∧
      σ.regs.rax.toBitVec = q.k ∧ σ.regs.rcx.toBitVec = mOf q.h⟩
  | .o5 => ⟨lab okL + Int64.ofNat 92, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ σ.slot (-96) = H lab + o <<< 4 ∧
      σ.regs.rax.toBitVec = q.k * mOf q.h⟩
  | .f5 => ⟨lab okL + Int64.ofNat 107, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ σ.slot (-96) = H lab + o <<< 4 ∧
      σ.regs.rax.toBitVec = q.k * mOf q.h ∧ σ.regs.rcx.toBitVec = 3#64⟩
  | .o6 => ⟨lab okL + Int64.ofNat 110, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ σ.slot (-96) = H lab + o <<< 4 ∧
      σ.regs.rax.toBitVec = (q.k * mOf q.h) <<< 3⟩
  | .f6 => ⟨lab okL + Int64.ofNat 125, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ Jbase lab q o σ ∧
      σ.regs.rax.toBitVec = q.k ∧ σ.regs.rcx.toBitVec = 36#64⟩
  | .o7 => ⟨lab okL + Int64.ofNat 128, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ Jbase lab q o σ ∧
      σ.regs.rax.toBitVec = q.k <<< 36⟩
  | .f7 => ⟨lab okL + Int64.ofNat 140, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ Jbase lab q o σ ∧
      σ.regs.rax.toBitVec = q.h ∧ σ.regs.rcx.toBitVec = q.k <<< 36⟩
  | .o8 => ⟨lab okL + Int64.ofNat 143, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ Jbase lab q o σ ∧
      σ.regs.rax.toBitVec = q.hdr⟩
  | .hdr => ⟨lab okL + Int64.ofNat 170, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ Jbase lab q o σ ∧
      σ.regs.rax.toBitVec = q.hdr ∧ σ.regs.rcx.toBitVec = H lab + o <<< 4 + (q.k * mOf q.h) <<< 3⟩
  | .o9 => ⟨lab okL + Int64.ofNat 173, oI, fun σ c => ∃ o, Jok ms q o σ c ∧ Jbase lab q o σ⟩
  | .ret => ⟨lab okL + Int64.ofNat 226, oE, fun σ c => ∃ o : BitVec 64, c = holdCtr ms q.c0 o ∧
      o.toNat + ms.units q.n q.τ ≤ ms.cells ∧ q.n < 2 ^ 28 ∧
      σ.regs.rax.toBitVec = H lab + o <<< 4 + (q.k * mOf q.h) <<< 3 + 8#64 ∧
      σ.regs.rbp.toBitVec = q.fp ∧ σ.slot 0 = q.ra ∧ ms.lo o.toNat⟩

/-- **The exits**: the return to `ra` past the source's allocation step,
and the heap abort. -/
def E (lbl : WeakMem.AllocLabel → Option Nat) : AX → ND
  | .ret => ⟨Int64.ofBitVec q.ra, oR, fun σ c => ∃ (l : WeakMem.AllocLabel) (ini old : Nat),
      Scc.Sem.ValRep lbl (.loc ⟨l, 0⟩ 0) σ.regs.rax.toNat ∧ c = allocCtl q.c0 q.x q.τ q.e q.n l ini ∧
      σ.regs.rax.toNat = ms.heap + 16 * old + ms.off q.n q.τ ∧ old + ms.units q.n q.τ ≤ ms.cells ∧
      ms.lo old ∧ σ.regs.rbp.toBitVec = q.fp⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-160, [(.rbp, -8)]⟩, fun σ c => σ.regs.rdi.toBitVec = 2#64 ∧ Jfull ms q c⟩

/-- **The allocation's continuation** at the fresh label `l`, base `b`:
the return to `ra` past the source's allocation step, `x` bound to `l`'s
locative, `%rax = b` the base for the counter's old value (`alloc_nd`; the
words `w` are the allocation's, `q.n` elements of the element type's
words). -/
def Ea (l : WeakMem.AllocLabel) (b w : Nat) : ND :=
  ⟨Int64.ofBitVec q.ra, oR, fun σ c => ∃ (ini old : Nat), c = allocCtl q.c0 q.x q.τ q.e q.n l ini ∧
    σ.regs.rax.toNat = b ∧ b = ms.heap + 16 * old + ms.off q.n q.τ ∧ old + ms.units q.n q.τ ≤ ms.cells ∧
    ms.lo old ∧ σ.regs.rbp.toBitVec = q.fp ∧
    ∃ us, TermRun.accs (TermRun.close [] q.τ) = some us ∧ w = q.n * TermRun.nWords us⟩

/-- **The function's states inside `W`**, none moved by `K`: one obligation
per node (a block's `BlkW`, a single instruction's `NodeW`). -/
structure AllocW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) : Prop where
  e : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .e) bPro
  entry : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .entry) bChk
  j1 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .j1) bJ1
  cnt : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .cnt)
  c1 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .c1) bC1
  rmw : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .rmw)
  c2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .c2) bC2
  j2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .j2) bJ2
  slow : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .slow) bSlow
  j3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .j3) bJ3
  full : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .full) bFull
  ok : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ok) bO0
  f1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f1)
  o1 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o1) bO1
  f2 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f2)
  o2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o2) bO2
  s2 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .s2)
  o3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o3) bO3
  f3 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f3)
  o4 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o4) bO4
  f4 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f4)
  o5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o5) bO5
  f5 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f5)
  o6 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o6) bO6
  f6 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f6)
  o7 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o7) bO7
  f7 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .f7)
  o8 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o8) bO8
  hdr : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .hdr)
  o9 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .o9) bO9
  ret : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ret)

/-- The function is inside the trivial predicate, with no outside moves. -/
theorem AllocW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} :
    AllocW ms q (fun _ _ => True) (fun _ _ => False) exe endPc R F :=
  ⟨BlkW.triv, BlkW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv,
    BlkW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv,
    BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv,
    NodeW.triv, BlkW.triv, NodeW.triv⟩

end Spec

/-! ## The proof -/

/-- The count argument's value. -/
theorem Call.k_toNat {q : Call} (h : q.n < 2 ^ 64) : q.k.toNat = q.n := by
  simp only [Call.k, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The units argument's value. -/
theorem Call.u_toNat {ms : MemSide isa} {q : Call} (h : ms.units q.n q.τ < 2 ^ 63) :
    (q.u ms).toNat = ms.units q.n q.τ := by
  simp only [Call.u, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {R : Region} {m0 : MachineData}
  {q : Call} {cells : List (Directive × Nat)}

set_option hygiene false in
/-- A block node at `l + k`: the block, its `okBlk`, its `W` obligation; the
edge is left. -/
local macro "anode " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at an instruction with undefined flags writing `%rax`, at `okL + k`
(`z` bytes), to node `j`; the invariant's facts are left. -/
local macro "fnode " fi:term:max k:term:max z:term:max j:term:max w:term:max : tactic =>
  `(tactic| refine flag_ndW (fi := $fi) rfl hF
    (code_field hp hend (by simp only [hin']) (l := okL) (off := $k) rfl) $w
      fun σ c hJ fl => ⟨c, .refl c, .inl ⟨$j, ofNat_add' _ $k $z, rfl, ?_⟩⟩)

/-- **`scc_rt_alloc` is one segment inside `W` from any of its nodes `i0`**
to its return or its heap abort (`seg_allocW` from its entry). -/
theorem seg_allocW_at {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} {kp : Nat}
    (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi) (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocW ms q W K exe endPc R F) (i0 : AN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label ms q lbl x) s c) := by
  have hin' := hin
  simp only [allocIn, fiAt, iCtr, iHeap, iRmw, iHdr, iRet, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := fnL) (b := entryL) (off := 23) hp (by simp only [hin'])
  have hk := Call.k_toNat hq.n_lt
  have hu := Call.u_toNat hq.units
  have hcl := hq.cells
  have hU := hq.units
  refine fn_segW (N := N _ ms q) (E := E _ ms q lbl) (fun i => ?_) i0
  cases i
  case e =>
    anode bPro bPro_ok fnL 0 hW.e
    dsimp only [N] at hJ ⊢
    rw [bPro_run]
    obtain ⟨rfl, h1, h2, h3, h4, h5⟩ := hJ
    refine .inl ⟨AN.entry, eEntry, rfl, rfl, ?_⟩
    simp [Fr, upd_apply, h1, h2, h3, h4, h5]
  case entry =>
    anode bChk bChk_ok entryL 0 hW.entry
    dsimp only [N] at hJ ⊢
    rw [bChk_run]
    obtain ⟨rfl, hFr⟩ := hJ
    have h24 := hFr.2.2.2.1
    rw [h24]
    split
    · rename_i h
      refine .inl ⟨AN.full, rfl, rfl, .inl ⟨rfl, ?_⟩⟩
      rw [hk] at h; omega
    · rename_i h
      refine .inl ⟨AN.j1, rfl, rfl, rfl, hFr, ?_⟩
      rw [hk] at h; omega
  case j1 =>
    anode bJ1 bJ1_ok entryL 16 hW.j1
    dsimp only [N] at hJ ⊢
    rw [bJ1_run]
    exact .inl ⟨AN.cnt, rfl, rfl, hJ⟩
  case cnt =>
    refine si_ndW (si := .leaRip .rax "scc_rt_heap_use") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := cntL) (off := 0) (ofNat_zero' _)) hW.cnt
      fun σ c hJ => ⟨c, .refl c, .inl ⟨AN.c1, rfl, rfl, hJ, ?_⟩⟩
    simp [SI.step, SI.regs, Reg64s.set64]
  case c1 =>
    anode bC1 bC1_ok cntL 7 hW.c1
    dsimp only [N] at hJ ⊢
    rw [bC1_run]
    obtain ⟨⟨rfl, ⟨h0, h8, h16, h24, h32⟩, hn28⟩, hax⟩ := hJ
    refine .inl ⟨AN.rmw, ofNat_add' _ 7 12, rfl, ⟨rfl, ?_, hn28⟩, ?_, ?_⟩
    · simp [Fr, upd_apply, h0, h8, h16, h24, h32]
    · simp [Reg64s.set64, Reg64s.get64, hax]
    · simp [Reg64s.set64, Reg64s.get64, h32]
  case rmw =>
    refine ctr_ndW (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
      (code_field hp hend (by simp only [hin']) (l := cntL) (off := 19) rfl) hW.rmw fun m σ c _ hD hJ => ?_
    obtain ⟨⟨rfl, hFr, hn28⟩, hcx, hax⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = BitVec.ofNat 64 ms.ctr := by
      rw [← hq.ctr, ← hcx]; simp [bAddr, Reg64s.get64]
    rw [hb]
    refine ⟨rfl, hq.rt, hq.mp, hmem _ (.inl rfl) _ hD, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, hq.term, hq.ev,
      hq.num, hq.hold, by exact hax, fun old hG hle hlo => ⟨hq.grow old hG hle, fun fl =>
        .inl ⟨AN.c2, ofNat_add' _ 19 5, rfl, _, rfl, hle, hFr, hn28, ?_, hlo⟩⟩⟩
    simp [ownStep, Reg64s.set64]
  case c2 =>
    anode bC2 bC2_ok cntL 24 hW.c2
    dsimp only [N] at hJ ⊢
    rw [bC2_run]
    obtain ⟨o, rfl, ho, ⟨h0, h8, h16, h24, h32⟩, hn28, hax, hlo⟩ := hJ
    have hr : (σ.regs.rax.toNat : Int) = o.toNat := by rw [← hax]; rfl
    have hol := o.isLt
    rw [h32, hax, hr, hu]
    split
    · rename_i h
      obtain ⟨h1, h2⟩ := h
      have hlt : ms.cells < o.toNat + ms.units q.n q.τ := by
        rw [hcl]
        by_cases he : ms.units q.n q.τ + o.toNat = 4194304
        · refine absurd (BitVec.eq_of_toNat_eq ?_) h2
          simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits, hu] at he ⊢
          omega
        · omega
      refine .inl ⟨AN.slow, rfl, rfl, o, rfl, ho, hlt, ?_, ?_⟩
      · simp [Fr, upd_apply, h0, h8, h16, h24, h32]
      · simp [upd_apply]
    · rename_i h
      have hle : o.toNat + ms.units q.n q.τ ≤ ms.cells := by
        rw [hcl]
        by_cases he : ms.units q.n q.τ + o.toNat = 4194304
        · omega
        · refine Decidable.byContradiction fun hc => h ⟨by omega, fun h' => he ?_⟩
          have := congrArg BitVec.toNat h'
          simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits, hu] at this
          omega
      refine .inl ⟨AN.j2, ofNat_add' _ 24 35, rfl, o, rfl, hle, ?_, hn28, ?_, hlo⟩
      · simp [Fr, upd_apply, h0, h8, h16, h24, h32]
      · simp [upd_apply]
  case j2 =>
    anode bJ2 bJ2_ok cntL 59 hW.j2
    dsimp only [N] at hJ ⊢
    rw [bJ2_run]
    exact .inl ⟨AN.ok, rfl, rfl, hJ⟩
  case slow =>
    anode bSlow bSlow_ok slowL 0 hW.slow
    dsimp only [N] at hJ ⊢
    rw [bSlow_run]
    obtain ⟨o, hJ⟩ := hJ
    have ⟨_, ho, _, _, h48⟩ := hJ
    rw [h48]
    split
    · rename_i h
      obtain ⟨h1, h2⟩ := h
      refine absurd (BitVec.eq_of_toNat_eq ?_) h2
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Width.bits] at h1 ⊢
      have := o.isLt
      omega
    · exact .inl ⟨AN.j3, rfl, rfl, o, hJ⟩
  case j3 =>
    anode bJ3 bJ3_ok slowL 16 hW.j3
    dsimp only [N] at hJ ⊢
    rw [bJ3_run]
    obtain ⟨o, hc, ho, hx, -⟩ := hJ
    exact .inl ⟨AN.full, rfl, rfl, .inr ⟨o, hc, ho, hx⟩⟩
  case full =>
    anode bFull bFull_ok fullL 0 hW.full
    dsimp only [N] at hJ ⊢
    rw [bFull_run]
    exact .inr ⟨AX.abort, rfl, rfl, by simp [Reg64s.set64, Reg64s.get64], hJ⟩
  case ok =>
    anode bO0 bO0_ok okL 0 hW.ok
    dsimp only [N] at hJ ⊢
    rw [bO0_run]
    obtain ⟨o, rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩ := hJ
    refine .inl ⟨AN.f1, rfl, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo]
  case f1 =>
    fnode (.shr_cl .rax) 11 3 AN.o1 hW.f1
    obtain ⟨o, hJo, ha, hc⟩ := hJ
    exact ⟨o, hJo, (shr_rax ha hc fl).trans (by rw [cl_vals.1])⟩
  case o1 =>
    anode bO1 bO1_ok okL 14 hW.o1
    dsimp only [N] at hJ ⊢
    rw [bO1_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ha⟩ := hJ
    refine .inl ⟨AN.f2, ofNat_add' _ 14 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, ha]
  case f2 =>
    fnode (.and_rr .rax .rcx) 29 3 AN.o2 hW.f2
    obtain ⟨o, hJo, ha, hc⟩ := hJ
    exact ⟨o, hJo, and_rax ha hc fl⟩
  case o2 =>
    anode bO2 bO2_ok okL 32 hW.o2
    dsimp only [N] at hJ ⊢
    rw [bO2_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ha⟩ := hJ
    refine .inl ⟨AN.s2, ofNat_add' _ 32 4, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, ha]
  case s2 =>
    refine si_ndW (si := .leaRip .rax "scc_rt_heap") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := okL) (off := 36) rfl) hW.s2
      fun σ c hJ => ⟨c, .refl c, .inl ⟨AN.o3, ofNat_add' _ 36 7, rfl, ?_⟩⟩
    obtain ⟨o, hJo, h72⟩ := hJ
    exact ⟨o, hJo, h72, by simp [SI.step, SI.regs, Reg64s.set64]⟩
  case o3 =>
    anode bO3 bO3_ok okL 43 hW.o3
    dsimp only [N] at hJ ⊢
    rw [bO3_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h72, ha⟩ := hJ
    refine .inl ⟨AN.f3, ofNat_add' _ 43 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, h72, ha]
  case f3 =>
    fnode (.shl_cl .rax) 58 3 AN.o4 hW.f3
    obtain ⟨o, hJo, h72, h80, ha, hc⟩ := hJ
    exact ⟨o, hJo, h72, h80, (shl_rax ha hc fl).trans (by rw [cl_vals.2.1])⟩
  case o4 =>
    anode bO4 bO4_ok okL 61 hW.o4
    dsimp only [N] at hJ ⊢
    rw [bO4_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h72, h80, ha⟩ := hJ
    refine .inl ⟨AN.f4, ofNat_add' _ 61 27, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo,
      h72, h80, ha, BitVec.add_comm]
  case f4 =>
    fnode (.imul_rr .rax .rcx) 88 4 AN.o5 hW.f4
    obtain ⟨o, hJo, h96, ha, hc⟩ := hJ
    exact ⟨o, hJo, h96, imul_rax ha hc fl⟩
  case o5 =>
    anode bO5 bO5_ok okL 92 hW.o5
    dsimp only [N] at hJ ⊢
    rw [bO5_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h96, ha⟩ := hJ
    refine .inl ⟨AN.f5, ofNat_add' _ 92 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, h96, ha]
  case f5 =>
    fnode (.shl_cl .rax) 107 3 AN.o6 hW.f5
    obtain ⟨o, hJo, h96, ha, hc⟩ := hJ
    exact ⟨o, hJo, h96, (shl_rax ha hc fl).trans (by rw [cl_vals.2.2.1])⟩
  case o6 =>
    anode bO6 bO6_ok okL 110 hW.o6
    dsimp only [N] at hJ ⊢
    rw [bO6_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h96, ha⟩ := hJ
    refine .inl ⟨AN.f6, ofNat_add' _ 110 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, h96, ha]
  case f6 =>
    fnode (.shl_cl .rax) 125 3 AN.o7 hW.f6
    obtain ⟨o, hJo, hb, ha, hc⟩ := hJ
    exact ⟨o, hJo, hb, (shl_rax ha hc fl).trans (by rw [cl_vals.2.2.2])⟩
  case o7 =>
    anode bO7 bO7_ok okL 128 hW.o7
    dsimp only [N] at hJ ⊢
    rw [bO7_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ⟨h96, h112⟩, ha⟩ := hJ
    refine .inl ⟨AN.f7, ofNat_add' _ 128 12, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo,
      h96, h112, ha]
  case f7 =>
    fnode (.or_rr .rax .rcx) 140 3 AN.o8 hW.f7
    obtain ⟨o, hJo, hb, ha, hc⟩ := hJ
    exact ⟨o, hJo, hb, or_rax ha hc fl⟩
  case o8 =>
    anode bO8 bO8_ok okL 143 hW.o8
    dsimp only [N] at hJ ⊢
    rw [bO8_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ⟨h96, h112⟩, ha⟩ := hJ
    refine .inl ⟨AN.hdr, ofNat_add' _ 143 27, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo,
      h96, h112, ha, BitVec.add_comm]
  case hdr =>
    refine rtst_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := okL) (off := 170) rfl) hW.hdr fun m σ c _ hD hJ => ?_
    obtain ⟨o, hJo, hb, ha, hc⟩ := hJ
    have ⟨_, hle, _, hn28, _, hlo⟩ := hJo
    have hra : bAddr σ.regs .rcx 0 = H (_root_.Executable.labels exe).label + o <<< 4 + (q.k * mOf q.h) <<< 3 := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hAeq : (bAddr σ.regs .rcx 0).toNat = q.hdrAt ms o.toNat := by
      rw [hra, base_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.heap]; exact hq.room), hq.heap, hk]
      rfl
    have hofn : BitVec.ofNat 64 (q.hdrAt ms o.toNat) = bAddr σ.regs .rcx 0 := by
      rw [← hAeq]; simp
    obtain ⟨hrt, hmp, hG⟩ := hq.hdr o.toNat hlo hle
    have hv : σ.regs.get64 .rax = q.hdr := ha
    refine ⟨hAeq ▸ hrt, hofn ▸ hmp, ?_, hmem _ (.inr ⟨o.toNat, hle, hAeq⟩) _ hD, c, .refl c,
      .inl ⟨AN.o9, ofNat_add' _ 170 3, rfl, o, hJo, hb⟩⟩
    rw [← hofn, hv]
    exact hG
  case o9 =>
    anode bO9 bO9_ok okL 173 hW.o9
    dsimp only [N] at hJ ⊢
    rw [bO9_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ⟨h96, h112⟩⟩ := hJ
    refine .inl ⟨AN.ret, ofNat_add' _ 173 53, rfl, o, rfl, hle, hn28, ?_, ?_, ?_, hlo⟩
    · simp [Reg64s.set64, Reg64s.get64, h96, h112]
      ac_rfl
    · simp [Reg64s.set64, Reg64s.get64, h8]
    · simp [upd_apply, h0]
  case ret =>
    refine alloc_ndW (Ea ms q) (a := .ret) (z := 1) (lo := -160) (hi := 8) rfl (by rintro w op ⟨⟩) hF
      hR hlo hhi (code_field hp hend (by simp only [hin']) (l := okL) (off := 226) rfl) hxa hW.ret
      fun σ c hJ => ?_
    obtain ⟨o, rfl, hle, hn28, h0, h29, h30, hlo⟩ := hJ
    have hA : σ.regs.rax.toBitVec.toNat = ms.heap + 16 * o.toNat + ms.off q.n q.τ := by
      rw [h0, base8_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.heap]; exact hq.room), hq.heap, hk, hq.off]
    obtain ⟨us, hus⟩ := hq.accs
    refine ⟨σ.regs.rax.toBitVec, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, TermRun.cst (.num o.toNat), o.toNat, us,
      hq.term, hq.ev, hq.num, rfl, rfl, hA, hle, hus, fun l ini _ =>
        ⟨?_, rfl, ini, o.toNat, rfl, ?_, hA, hle, hlo, ?_, us, hus, rfl⟩⟩
    · simp [N, Ea, AI.tgt, h30]
    · simp [iRet, AI.step, Reg64s.set64, Reg64s.get64]
    · simp [iRet, AI.step, Reg64s.set64, Reg64s.get64, h29]

/-- **`scc_rt_alloc` is one segment inside `W`** from its entry to its
return or its heap abort, in any valid layout of cells holding its code
(`allocIn`), for every frame condition `F` no write inside the frame breaks
(`seg_alloc` is the frame condition `DFrame R m0`): the counter and every
header the code may store are unmapped in private memory in every memory of
`F` (`hmem`); its nodes' states lie in `W`, none moved by `K` (`hW`). -/
theorem seg_allocW {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} {kp : Nat}
    (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi) (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocW ms q W K exe endPc R F) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label ms q lbl x) s c) :=
  seg_allocW_at hp hend hin hF hR hlo hhi hq hmem hxa hW .e

/-- **`scc_rt_alloc` is one segment** from its entry to its return (the
source's allocation step taken, `x` bound at the base the code returns) or
its heap abort, in any valid layout of cells holding its code (`allocIn`),
for a call satisfying `Call.OK`, with the counter and every header the code
may store outside the frame and unmapped in private memory (`hmem`). The
return is into the allocation's continuation (`hxa`: every state at `Ea`
for a fresh label is one `ms.xa` continues in). -/
theorem seg_alloc {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi) (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      a.toNat + 8 ≤ 2 ^ 64 ∧ ((a.toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a.toNat) ∧
      Mem.loadInt m0.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R (DFrame R m0) (Ea ms q l b w) s c → ms.xa l b w s c) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label ms q .e))
      (fun s c => ∃ x, At exe endPc R (DFrame R m0) (E (_root_.Executable.labels exe).label ms q lbl x) s c) :=
  (seg_allocW hp hend hin (FStable.dframe R m0) hR hlo hhi hq
    (fun a ha => let ⟨hfit, hout, hnone⟩ := hmem a ha; fun _ hD => (hD _ hfit hout).trans hnone)
    hxa (AllocW.triv ms q)).toSeg

end Proof

end Spike.Lib.X64.Alloc
