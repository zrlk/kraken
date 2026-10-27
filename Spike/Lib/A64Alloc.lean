/-
**The allocator on AArch64**: the runtime's `scc_rt_alloc(h, k, u)`
(`Scc/Lower/Runtime.lean`, `allocF`, the stride-16 allocator; its blocks in
`Scc/Sem/HeapCtr.lean`) as one `Seg` from its entry, called at a source
buffer allocation `let x = newBuf a τ in e` of `n` elements, to its return
(the source's allocation step taken) or its heap abort.

    scc_rt_alloc(h = x0, k = x1, u = x2):
      prologue (frame of 160 bytes, x29/x30 saved at 144/152, h/k/u at 0/8/16)
      entry: if k ≥ 2^28 goto full
      cnt:   old = ldaddal [scc_rt_heap_use], u
             if old + u > cells goto slow                  -- cells = 2^22
      slow:  if old > cells goto spin; goto full
      spin:  goto spin
      full:  x0 = 2; bl scc_rt_abort
      ok:    m = (h >> 22) & 16383; s = scc_rt_heap + 16·old
             str (h | k << 36), [s + 8·k·m]                -- the header
             x0 = s + 8·k·m + 8; epilogue; ret

The text is the same in every program `scc --arch arm` compiles (it is the
runtime's); the blocks below are its listing, parsed by Kraken's own
`parseAArch64`. The region is the frame, offsets `[-160, 0)` from the `sp`
at entry.

**The specification** (`Call`, `Call.OK`): the source is at the
allocation, no hold pending, `k = n` and `u` the buffer's units
(`ms.units`), `h` a header whose trace-word field `m` gives the buffer's
base offset (`ms.off n τ = 8·n·m + 8`); the labels `scc_rt_heap_use` and
`scc_rt_heap` are the counter (`ms.ctr`) and the arena (`ms.heap`), the
arena has `ms.cells = 2^22` cells and room for its addresses; the runtime
memory's value invariant `ms.G` allows the counter's add (within the
cells) and each header the code may store, at an address the runtime owns
and maps for writing (`ms.mp`); the element type has its accesses.

- **entry** (`.e`): pc at `scc_rt_alloc`, `sp` at offset 0, `x0`–`x2` the
  arguments, `x29 = x29`, `x30 = ra`;
- **return** (`Ea`, through `Out.alloc` at the `ret`, into the
  allocation's continuation `ms.xa`, `hxa`): pc at `ra`, `sp` at offset 0,
  `x29` and `x30` restored, the source past its allocation step, `x` bound
  to a fresh label, `x0` the base `ms.heap + 16·old + ms.off n τ` for the
  counter's old value `old`, with `old + u ≤ cells`. The exit `.ret` is
  kept in the graph but no longer reached;
- **abort** (exit `.abort`): pc at `scc_rt_abort` with `x0 = 2`, the
  source at the allocation: either `k ≥ 2^28`, or the counter's add
  happened (the hold records its old value) and crossed the cells
  (`old ≤ cells < old + u`, the premises of `HeapCtr1.abort_justified`).

The counter's add is `ctr_nd` (`Out.ctrRmw`): with one thread the old value
it reads is within the cells (`ms.cells`), so `slow` never goes to `spin`
and `ok`'s arithmetic does not wrap. The header store is `rtst_nd`
(`Out.rtStore`), the `ret` is `alloc_nd` (`Out.alloc`), the label addresses
are `si_nd`. The counter and the headers are outside the frame and outside
the thread's private memory (`hmem`).

`seg_allocW` is the segment inside a predicate `W` (one obligation per
node, `AllocW`) for any frame condition no write inside the frame breaks
(`seg_allocW_at` from any node); `seg_alloc` is it inside the trivial
predicate at `DFrame R m0`.
-/
import Spike.Lib.A64AllocNodes
import Kraken.AArch64.Parser

namespace Spike.Lib.A64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

/-! ## The blocks -/

def b0 : List Directive := parseAArch64("sub sp, sp, #160
str x29, [sp, #144]
str x30, [sp, #152]
add x29, sp, #144
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]")
def b1 : List Directive := parseAArch64("ldr x9, [sp, #8]
movz x10, #4096, lsl #16
subs xzr, x9, x10
b.hs .L2_scc_rt_alloc.4_full")
def b2 : List Directive := parseAArch64("b .L2_scc_rt_alloc.1_cnt")
def b3 : List Directive := parseAArch64("str x9, [sp, #24]
ldr x9, [sp, #16]
ldr x10, [sp, #24]")
def b4 : List Directive := parseAArch64("str x11, [sp, #32]
ldr x9, [sp, #32]
ldr x10, [sp, #16]
add x9, x9, x10
str x9, [sp, #40]
ldr x9, [sp, #40]
movz x10, #64, lsl #16
subs xzr, x9, x10
b.hi .L2_scc_rt_alloc.2_slow")
def b5 : List Directive := parseAArch64("b .L2_scc_rt_alloc.5_ok")
def b6 : List Directive := parseAArch64("ldr x9, [sp, #32]
movz x10, #64, lsl #16
subs xzr, x9, x10
b.hi .L2_scc_rt_alloc.3_spin")
def b7 : List Directive := parseAArch64("b .L2_scc_rt_alloc.4_full")
def b9 : List Directive := parseAArch64("movz x0, #2
bl scc_rt_abort")
def b11 : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #22
lsrv x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #48]
movz x10, #16383
and x9, x9, x10
str x9, [sp, #56]")
def b12 : List Directive := parseAArch64("str x9, [sp, #64]
ldr x9, [sp, #32]
movz x10, #4
lslv x9, x9, x10
str x9, [sp, #72]
ldr x9, [sp, #64]
ldr x10, [sp, #72]
add x9, x9, x10
str x9, [sp, #80]
ldr x9, [sp, #8]
ldr x10, [sp, #56]
madd x9, x9, x10, xzr
str x9, [sp, #88]
ldr x9, [sp, #88]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #96]
ldr x9, [sp, #8]
movz x10, #36
lslv x9, x9, x10
str x9, [sp, #104]
ldr x9, [sp]
ldr x10, [sp, #104]
orr x9, x9, x10
str x9, [sp, #112]
ldr x9, [sp, #80]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #120]
ldr x9, [sp, #112]
ldr x10, [sp, #120]")
def b13 : List Directive := parseAArch64("ldr x9, [sp, #80]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #128]
ldr x9, [sp, #128]
movz x10, #8
add x9, x9, x10
str x9, [sp, #136]
ldr x0, [sp, #136]
ldr x29, [sp, #144]
ldr x30, [sp, #152]
add sp, sp, #160")

/-- The single instructions: the label addresses, the counter's add, the
header store, the `ret`. -/
def iAdrpC : SI := .adrp .X9 "scc_rt_heap_use"
def iAddC : SI := .addLo12 .X9 .X9 "scc_rt_heap_use"
def iAdrpH : SI := .adrp .X9 "scc_rt_heap"
def iAddH : SI := .addLo12 .X9 .X9 "scc_rt_heap"
def iRmw : Directive := ldopDir .ADD .acqRel .X9 .X11 .X10
def iHdr : Directive := strDir .X9 .X10 0
def iRet : AI := .ret (.low (.reg .X30) .W64)

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-160, []⟩
/-- The offsets at entry and return. -/
abbrev oE : SO := ⟨0, []⟩

block_spec b0 (-160) 0 oE b0
block_spec b1 (-160) 0 oI b1
block_spec b2 (-160) 0 oI b2
block_spec b3 (-160) 0 oI b3
block_spec b4 (-160) 0 oI b4
block_spec b5 (-160) 0 oI b5
block_spec b6 (-160) 0 oI b6
block_spec b7 (-160) 0 oI b7
block_spec b9 (-160) 0 oI b9
block_spec b11 (-160) 0 oI b11
block_spec b12 (-160) 0 oI b12
block_spec b13 (-160) 0 oI b13

/-- The listing's text, as the blocks and single instructions in order. -/
example : parseAArch64("adrp x9, scc_rt_heap_use
add x9, x9, :lo12:scc_rt_heap_use
ldaddal x9, x11, [x10]
adrp x9, scc_rt_heap
add x9, x9, :lo12:scc_rt_heap
str x9, [x10]
ret") = [iAdrpC.toDir, iAddC.toDir, iRmw, iAdrpH.toDir, iAddH.toDir, iHdr, iRet.toDir] := by
  decide

/-! ## Arithmetic -/

/-- A label's page plus its low 12 bits is the label. -/
theorem adrp_lo12 (x : BitVec 64) : (x &&& ~~~0xFFF#64) + (x &&& 0xFFF#64) = x := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases x[i] <;> cases (0xFFF#64)[i] <;> rfl
  · ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases x[i] <;> cases (0xFFF#64)[i] <;> rfl

/-- `subs`'s carry: no borrow. -/
theorem subs_c (a b : BitVec 64) : (StatusFlags.subs (a - b) a b).c = decide (b.toNat ≤ a.toNat) := by
  simp only [StatusFlags.subs, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_sub]
  by_cases h : b.toNat ≤ a.toNat
  · simp [h]; omega
  · simp [h]; omega

/-- `subs`'s zero flag: equal operands. -/
theorem subs_z (a b : BitVec 64) : (StatusFlags.subs (a - b) a b).z = decide (a = b) := by
  simp only [StatusFlags.subs, StatusFlags.from_result]
  by_cases h : a = b
  · subst h; simp
  · simp [h, BitVec.zero_eq]; intro h'; exact h (by bv_omega)

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

/-- `subs`'s unsigned higher: `b < a`. -/
theorem subs_hi (a b : BitVec 64) :
    ((StatusFlags.subs (a - b) a b).c = true ∧ (StatusFlags.subs (a - b) a b).z = false) ↔ b.toNat < a.toNat := by
  rw [subs_c, subs_z]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1, h2⟩
    exact Nat.lt_of_le_of_ne h1 fun h => h2 (BitVec.eq_of_toNat_eq h.symm)
  · intro h
    exact ⟨Nat.le_of_lt h, fun he => by rw [he] at h; exact Nat.lt_irrefl _ h⟩

/-- A general register read as a 64-bit operand. -/
theorem getRegOrZr_x (r : Reg64s) (x : XReg) : r.getRegOrZr (.low (.reg x) .W64) = (r.getXReg x).toBitVec := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base]

/-! ## The specification -/

/-- **A call of the allocator**: the source's buffer allocation
`let x = newBuf a τ in e` of `n` elements (`a` evaluating to the words
`ws` of type `ta`) from the control `c0`, the header `h`, the caller's
`x29` and the return address `ra`. -/
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
  x29 : BitVec 64
  ra : BitVec 64

/-- The element count argument. -/
def Call.k (q : Call) : BitVec 64 := BitVec.ofNat 64 q.n
/-- The units argument. -/
def Call.u (ms : MemSide isaLSE2) (q : Call) : BitVec 64 := BitVec.ofNat 64 (ms.units q.n q.τ)
/-- The header the allocator stores. -/
def Call.hdr (q : Call) : BitVec 64 := q.h ||| q.k <<< 36
/-- The header's address for the counter's old value `o`. -/
def Call.hdrAt (ms : MemSide isaLSE2) (q : Call) (o : Nat) : Nat := ms.heap + 16 * o + 8 * (q.n * (mOf q.h).toNat)

/-- **The call's premises**: see the module docstring. -/
structure Call.OK (ms : MemSide isaLSE2) (lab : Label → Int64) (q : Call) : Prop where
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
  hdr : ∀ o, o + ms.units q.n q.τ ≤ ms.cells →
    ms.rt (q.hdrAt ms o) ∧ ms.mp ⟨BitVec.ofNat 64 (q.hdrAt ms o), 8⟩ true ∧
      ms.G ⟨BitVec.ofNat 64 (q.hdrAt ms o), 8⟩ (q.hdr.setWidth 128)

/-- The internal nodes. -/
inductive AN where
  | e | entry | n2 | cnt | cnt1 | cnt2 | rmw | n4 | n5 | slow | n7 | full | ok | ok1 | ok2 | n12 | hdr | n13 | ret

/-- The exits. -/
inductive AX where
  | ret | abort

section Spec

variable (lab : Label → Int64) (ms : MemSide isaLSE2) (q : Call)

/-- The frame's fixed cells: the caller's `x29`, the return address, the
arguments. -/
def Fr (σ : AS) : Prop :=
  σ.slot (-16) = q.x29 ∧ σ.slot (-8) = q.ra ∧ σ.slot (-160) = q.h ∧ σ.slot (-152) = q.k ∧ σ.slot (-144) = q.u ms

/-- Before the counter's add: the source at the call, the count checked. -/
def Jc (σ : AS) (c : Ctl) : Prop := c = q.c0 ∧ Fr ms q σ ∧ q.n < 2 ^ 28

/-- After the add, within the cells: the hold records the old value `o`,
in its cell. -/
def Jok (o : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = holdCtr ms q.c0 o ∧ o.toNat + ms.units q.n q.τ ≤ ms.cells ∧ Fr ms q σ ∧ q.n < 2 ^ 28 ∧ σ.slot (-128) = o

/-- After the add, past the cells. -/
def Jslow (o : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = holdCtr ms q.c0 o ∧ o.toNat ≤ ms.cells ∧ ms.cells < o.toNat + ms.units q.n q.τ ∧ Fr ms q σ ∧
    σ.slot (-128) = o

/-- On the way to the heap abort. -/
def Jfull (c : Ctl) : Prop :=
  (c = q.c0 ∧ 2 ^ 28 ≤ q.n) ∨
    ∃ o : BitVec 64, c = holdCtr ms q.c0 o ∧ o.toNat ≤ ms.cells ∧ ms.cells < o.toNat + ms.units q.n q.τ

/-- The arena's base. -/
abbrev H : BitVec 64 := (lab "scc_rt_heap").toBitVec

/-- The object's start and the trace words' bytes, in their cells. -/
def Jbase (o : BitVec 64) (σ : AS) : Prop :=
  σ.slot (-80) = H lab + o <<< 4 ∧ σ.slot (-64) = (q.k * mOf q.h) <<< 3

/-- **The nodes.** -/
def N : AN → ND
  | .e => ⟨lab "scc_rt_alloc", oE, fun σ c => c = q.c0 ∧ σ.regs.X29.toBitVec = q.x29 ∧
      σ.regs.X30.toBitVec = q.ra ∧ σ.regs.X0.toBitVec = q.h ∧ σ.regs.X1.toBitVec = q.k ∧
      σ.regs.X2.toBitVec = q.u ms⟩
  | .entry => ⟨lab ".L2_scc_rt_alloc.0_entry", oI, fun σ c => c = q.c0 ∧ Fr ms q σ⟩
  | .n2 => ⟨lab ".L2_scc_rt_alloc.0_entry" + 4 + 4 + 4 + 4, oI, Jc ms q⟩
  | .cnt => ⟨lab ".L2_scc_rt_alloc.1_cnt", oI, Jc ms q⟩
  | .cnt1 => ⟨lab ".L2_scc_rt_alloc.1_cnt" + 4, oI, fun σ c => Jc ms q σ c ∧
      σ.regs.X9.toBitVec = (lab "scc_rt_heap_use").toBitVec &&& ~~~0xFFF#64⟩
  | .cnt2 => ⟨lab ".L2_scc_rt_alloc.1_cnt" + 4 + 4, oI, fun σ c => Jc ms q σ c ∧
      σ.regs.X9.toBitVec = BitVec.ofNat 64 ms.ctr⟩
  | .rmw => ⟨lab ".L2_scc_rt_alloc.1_cnt" + 4 + 4 + 4 + 4 + 4, oI, fun σ c => Jc ms q σ c ∧
      σ.regs.X10.toBitVec = BitVec.ofNat 64 ms.ctr ∧ σ.regs.X9.toBitVec = q.u ms⟩
  | .n4 => ⟨lab ".L2_scc_rt_alloc.1_cnt" + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c => ∃ o : BitVec 64,
      c = holdCtr ms q.c0 o ∧ o.toNat ≤ ms.cells ∧ Fr ms q σ ∧ q.n < 2 ^ 28 ∧ σ.regs.X11.toBitVec = o⟩
  | .n5 => ⟨lab ".L2_scc_rt_alloc.1_cnt" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI,
      fun σ c => ∃ o, Jok ms q o σ c⟩
  | .slow => ⟨lab ".L2_scc_rt_alloc.2_slow", oI, fun σ c => ∃ o, Jslow ms q o σ c⟩
  | .n7 => ⟨lab ".L2_scc_rt_alloc.2_slow" + 4 + 4 + 4 + 4, oI, fun σ c => ∃ o, Jslow ms q o σ c⟩
  | .full => ⟨lab ".L2_scc_rt_alloc.4_full", oI, fun _ c => Jfull ms q c⟩
  | .ok => ⟨lab ".L2_scc_rt_alloc.5_ok", oI, fun σ c => ∃ o, Jok ms q o σ c⟩
  | .ok1 => ⟨lab ".L2_scc_rt_alloc.5_ok" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c => ∃ o, Jok ms q o σ c ∧
      σ.slot (-104) = mOf q.h⟩
  | .ok2 => ⟨lab ".L2_scc_rt_alloc.5_ok" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c => ∃ o, Jok ms q o σ c ∧
      σ.slot (-104) = mOf q.h ∧ σ.regs.X9.toBitVec = H lab &&& ~~~0xFFF#64⟩
  | .n12 => ⟨lab ".L2_scc_rt_alloc.5_ok" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c => ∃ o,
      Jok ms q o σ c ∧ σ.slot (-104) = mOf q.h ∧ σ.regs.X9.toBitVec = H lab⟩
  | .hdr => ⟨lab ".L2_scc_rt_alloc.5_ok" +
      4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 +
      4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c => ∃ o,
      Jok ms q o σ c ∧ Jbase lab q o σ ∧ σ.regs.X9.toBitVec = q.hdr ∧
      σ.regs.X10.toBitVec = H lab + o <<< 4 + (q.k * mOf q.h) <<< 3⟩
  | .n13 => ⟨lab ".L2_scc_rt_alloc.5_ok" +
      4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 +
      4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c => ∃ o,
      Jok ms q o σ c ∧ Jbase lab q o σ⟩
  | .ret => ⟨lab ".L2_scc_rt_alloc.5_ok" +
      4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 +
      4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 +
      4 + 4, oE, fun σ c => ∃ o : BitVec 64, c = holdCtr ms q.c0 o ∧
      o.toNat + ms.units q.n q.τ ≤ ms.cells ∧ q.n < 2 ^ 28 ∧
      σ.regs.X0.toBitVec = H lab + o <<< 4 + (q.k * mOf q.h) <<< 3 + 8#64 ∧
      σ.regs.X29.toBitVec = q.x29 ∧ σ.regs.X30.toBitVec = q.ra⟩

/-- **The exits**: the return to `ra` past the source's allocation step,
and the heap abort. -/
def E (lbl : WeakMem.AllocLabel → Option Nat) : AX → ND
  | .ret => ⟨Int64.ofBitVec q.ra, oE, fun σ c => ∃ (l : WeakMem.AllocLabel) (ini old : Nat),
      Scc.Sem.ValRep lbl (.loc ⟨l, 0⟩ 0) σ.regs.X0.toNat ∧ c = allocCtl q.c0 q.x q.τ q.e q.n l ini ∧
      σ.regs.X0.toNat = ms.heap + 16 * old + ms.off q.n q.τ ∧ old + ms.units q.n q.τ ≤ ms.cells ∧
      σ.regs.X29.toBitVec = q.x29 ∧ σ.regs.X30.toBitVec = q.ra⟩
  | .abort => ⟨lab "scc_rt_abort", oI, fun σ c => σ.regs.X0 = 2 ∧ Jfull ms q c⟩

/-- **The allocation's continuation** at the fresh label `l`, base `b`:
the return to `ra` past the source's allocation step, `x` bound to `l`'s
locative, `x0 = b` the base for the counter's old value (`alloc_nd`; the
words `w` are the allocation's, `q.n` elements of the element type's
words). -/
def Ea (l : WeakMem.AllocLabel) (b w : Nat) : ND :=
  ⟨Int64.ofBitVec q.ra, oE, fun σ c => ∃ (ini old : Nat), c = allocCtl q.c0 q.x q.τ q.e q.n l ini ∧
    σ.regs.X0.toNat = b ∧ b = ms.heap + 16 * old + ms.off q.n q.τ ∧ old + ms.units q.n q.τ ≤ ms.cells ∧
    σ.regs.X29.toBitVec = q.x29 ∧ σ.regs.X30.toBitVec = q.ra ∧
    ∃ us, TermRun.accs (TermRun.close [] q.τ) = some us ∧ w = q.n * TermRun.nWords us⟩

/-- **The code**: every block and single instruction at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (N (_root_.Executable.labels exe).label ms q .e).pc b0
  entry : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .entry).pc b1
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (N (_root_.Executable.labels exe).label ms q .n2).pc b2
  cnt : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .cnt).pc [iAdrpC.toDir]
  cnt1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .cnt1).pc [iAddC.toDir]
  cnt2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .cnt2).pc b3
  rmw : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .rmw).pc [iRmw]
  n4 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (N (_root_.Executable.labels exe).label ms q .n4).pc b4
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (N (_root_.Executable.labels exe).label ms q .n5).pc b5
  slow : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .slow).pc b6
  n7 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (N (_root_.Executable.labels exe).label ms q .n7).pc b7
  full : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .full).pc b9
  ok : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (N (_root_.Executable.labels exe).label ms q .ok).pc b11
  ok1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .ok1).pc [iAdrpH.toDir]
  ok2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .ok2).pc [iAddH.toDir]
  n12 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .n12).pc b12
  hdr : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .hdr).pc [iHdr]
  n13 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .n13).pc b13
  ret : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label ms q .ret).pc [iRet.toDir]

/-- **The function's states inside `W`**, none moved by `K`: one obligation
per node (a block's `BlkW`, a single instruction's `NodeW`). -/
structure AllocW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) : Prop where
  e : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .e) b0
  entry : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .entry) b1
  n2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .n2) b2
  cnt : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .cnt)
  cnt1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .cnt1)
  cnt2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .cnt2) b3
  rmw : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .rmw)
  n4 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .n4) b4
  n5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .n5) b5
  slow : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .slow) b6
  n7 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .n7) b7
  full : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .full) b9
  ok : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ok) b11
  ok1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ok1)
  ok2 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ok2)
  n12 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .n12) b12
  hdr : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .hdr)
  n13 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .n13) b13
  ret : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label ms q .ret)

/-- The function is inside the trivial predicate, with no outside moves. -/
theorem AllocW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} :
    AllocW ms q (fun _ _ => True) (fun _ _ => False) exe endPc R F :=
  ⟨BlkW.triv, BlkW.triv, BlkW.triv, NodeW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, BlkW.triv, BlkW.triv,
    BlkW.triv, BlkW.triv, BlkW.triv, NodeW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv⟩

end Spec

/-! ## The proof -/

/-- The count argument's value. -/
theorem Call.k_toNat {q : Call} (h : q.n < 2 ^ 64) : q.k.toNat = q.n := by
  simp only [Call.k, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The units argument's value. -/
theorem Call.u_toNat {ms : MemSide isaLSE2} {q : Call} (h : ms.units q.n q.τ < 2 ^ 63) :
    (q.u ms).toNat = ms.units q.n q.τ := by
  simp only [Call.u, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {q : Call}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code, its `W` obligation; the
edge is left. -/
macro "anode " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) hW.$f fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_alloc` is one segment inside `W` from any of its nodes `i0`**
to its return or its heap abort (`seg_allocW` from its entry). -/
theorem seg_allocW_at {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop} (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OK ms (_root_.Executable.labels exe).label) (hcode : Code ms q exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_alloc" + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocW ms q W K exe endPc R F) (i0 : AN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label ms q lbl x) s c) := by
  refine fn_segW (N := N _ ms q) (E := E _ ms q lbl) (fun i => ?_) i0
  cases i
  case e =>
    anode b0 b0_ok e; rw [N, b0_run]
    refine .inl ⟨AN.entry, ?_, rfl, ?_⟩
    · simp [N, hentry]
    · obtain ⟨rfl, h29, h30, h0, h1, h2⟩ := hJ
      simp [N, Fr, upd_apply, h29, h30, h0, h1, h2]
  case entry =>
    anode b1 b1_ok entry; rw [N, b1_run]
    obtain ⟨rfl, hF⟩ := hJ
    have hk := Call.k_toNat hq.n_lt
    rw [hF.2.2.2.1, subs_c]
    split
    · rename_i h
      refine .inl ⟨AN.full, rfl, rfl, .inl ⟨rfl, ?_⟩⟩
      simp only [decide_eq_true_eq, hk, BitVec.toNat_ofNat] at h; omega
    · rename_i h
      refine .inl ⟨AN.n2, rfl, rfl, rfl, hF, ?_⟩
      simp only [decide_eq_true_eq, hk, BitVec.toNat_ofNat] at h; omega
  case n2 => anode b2 b2_ok n2; rw [N, b2_run]; exact .inl ⟨AN.cnt, rfl, rfl, hJ⟩
  case cnt =>
    refine si_ndW (si := iAdrpC) hF (fun s he hn => hcode.cnt s he hn) hW.cnt
      fun σ c hJ => ⟨c, .refl c, .inl ⟨AN.cnt1, rfl, rfl, hJ, ?_⟩⟩
    simp [SI.step, SI.regs, iAdrpC]
  case cnt1 =>
    refine si_ndW (si := iAddC) hF (fun s he hn => hcode.cnt1 s he hn) hW.cnt1
      fun σ c hJ => ⟨c, .refl c, .inl ⟨AN.cnt2, rfl, rfl, hJ.1, ?_⟩⟩
    simp only [SI.step, SI.regs, iAddC]
    simp [hJ.2, ← hq.ctr]
    exact adrp_lo12 _
  case cnt2 =>
    anode b3 b3_ok cnt2; rw [N, b3_run]
    obtain ⟨⟨rfl, hF, hn28⟩, h9⟩ := hJ
    refine .inl ⟨AN.rmw, rfl, rfl, ⟨rfl, ?_, hn28⟩, h9, hF.2.2.2.2⟩
    simp_all [Fr, upd_apply]
  case rmw =>
    refine ctr_ndW hF (fun s he hn => hcode.rmw s he hn)
      hW.rmw fun m σ c hA hD hJ => ?_
    obtain ⟨⟨rfl, hF, hn28⟩, h10, h9⟩ := hJ
    have hnone := hmem _ (.inl rfl)
    refine ⟨h10, hq.rt, hq.mp, hnone _ hD, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, hq.term, hq.ev,
      hq.num, hq.hold, by rw [getRegOrZr_x]; exact h9, fun old hG hle =>
        ⟨hq.grow old hG hle, .inl ⟨AN.n4, rfl, rfl, _, rfl, hle, hF, hn28, rfl⟩⟩⟩
  case n4 =>
    anode b4 b4_ok n4; rw [N, b4_run]
    obtain ⟨o, rfl, ho, hF, hn28, h11⟩ := hJ
    have hu := Call.u_toNat hq.units
    have hc := hq.cells
    have hU := hq.units
    have hsum : (o + q.u ms).toNat = o.toNat + ms.units q.n q.τ := by
      rw [BitVec.toNat_add, hu]; exact Nat.mod_eq_of_lt (by omega)
    simp only [h11, hF.2.2.2.2, subs_hi, hsum]
    split
    · rename_i h
      refine .inl ⟨AN.slow, rfl, rfl, o, rfl, ho, ?_, ?_, ?_⟩
      · simp only [BitVec.toNat_ofNat] at h; omega
      · simp_all [Fr, upd_apply]
      · simp [upd_apply]
    · rename_i h
      refine .inl ⟨AN.n5, rfl, rfl, o, rfl, ?_, ?_, hn28, ?_⟩
      · simp only [BitVec.toNat_ofNat] at h; omega
      · simp_all [Fr, upd_apply]
      · simp [upd_apply]
  case n5 => anode b5 b5_ok n5; rw [N, b5_run]; exact .inl ⟨AN.ok, rfl, rfl, hJ⟩
  case slow =>
    anode b6 b6_ok slow; rw [N, b6_run]
    obtain ⟨o, hJ⟩ := hJ
    have ⟨_, ho, _, _, h128⟩ := hJ
    have hc := hq.cells
    simp only [h128, subs_hi]
    split
    · rename_i h
      simp only [BitVec.toNat_ofNat] at h; omega
    · exact .inl ⟨AN.n7, rfl, rfl, o, hJ⟩
  case n7 =>
    anode b7 b7_ok n7; rw [N, b7_run]
    obtain ⟨o, hc, ho, hu, -⟩ := hJ
    exact .inl ⟨AN.full, rfl, rfl, .inr ⟨o, hc, ho, hu⟩⟩
  case full => anode b9 b9_ok full; rw [N, b9_run]; exact .inr ⟨AX.abort, rfl, rfl, rfl, hJ⟩
  case ok =>
    anode b11 b11_ok ok; rw [N, b11_run]
    obtain ⟨o, hc, hle, hF, hn28, h128⟩ := hJ
    refine .inl ⟨AN.ok1, rfl, rfl, o, ⟨hc, hle, ?_, hn28, ?_⟩, ?_⟩
    · simp_all [Fr, upd_apply]
    · simp [upd_apply, h128]
    · simp [upd_apply, mOf, hF.2.2.1]
  case ok1 =>
    refine si_ndW (si := iAdrpH) hF (fun s he hn => hcode.ok1 s he hn) hW.ok1
      fun σ c hJ => ⟨c, .refl c, .inl ⟨AN.ok2, rfl, rfl, ?_⟩⟩
    obtain ⟨o, hJ, h104⟩ := hJ
    exact ⟨o, hJ, h104, by simp [SI.step, SI.regs, iAdrpH]⟩
  case ok2 =>
    refine si_ndW (si := iAddH) hF (fun s he hn => hcode.ok2 s he hn) hW.ok2
      fun σ c hJ => ⟨c, .refl c, .inl ⟨AN.n12, rfl, rfl, ?_⟩⟩
    obtain ⟨o, hJ, h104, h9⟩ := hJ
    refine ⟨o, hJ, h104, ?_⟩
    simp only [SI.step, SI.regs, iAddH]
    simp [h9]
    exact adrp_lo12 _
  case n12 =>
    anode b12 b12_ok n12; rw [N, b12_run]
    obtain ⟨o, ⟨hc, hle, hF, hn28, h128⟩, h104, h9⟩ := hJ
    obtain ⟨h16, h8, h160, h152, h144⟩ := hF
    refine .inl ⟨AN.hdr, rfl, rfl, o, ⟨hc, hle, ?_, hn28, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · simp_all [Fr, upd_apply]
    · simp [upd_apply, h128]
    · simp [upd_apply, h128, h9]
    · simp [upd_apply, h152, h104]
    · simp [h160, h152, Call.hdr]
    · simp [h9, h128, h152, h104]
  case hdr =>
    refine rtst_ndW (fun s he hn => hcode.hdr s he hn) hW.hdr fun m σ c hA hD hJ => ?_
    obtain ⟨o, ⟨hc, hle, hF, hn28, h128⟩, hb, h9, h10⟩ := hJ
    have hk := Call.k_toNat hq.n_lt
    have hcl := hq.cells
    have hra : rAddr σ.regs .X10 0 = H (_root_.Executable.labels exe).label + o <<< 4 + (q.k * mOf q.h) <<< 3 := by
      rw [← h10]; simp [rAddr, Reg64s.getXReg]
    have hAeq : (rAddr σ.regs .X10 0).toNat = q.hdrAt ms o.toNat := by
      rw [hra, base_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.heap]; exact hq.room), hq.heap, hk]
      rfl
    have hofn : BitVec.ofNat 64 (q.hdrAt ms o.toNat) = rAddr σ.regs .X10 0 := by
      rw [← hAeq]; simp
    obtain ⟨hrt, hmp, hG⟩ := hq.hdr o.toNat hle
    have hnone := hmem _ (.inr ⟨o.toNat, hle, hAeq⟩)
    refine ⟨hAeq ▸ hrt, hofn ▸ hmp, ?_, hnone _ hD, c, .refl c, .inl ⟨AN.n13, rfl, rfl, o,
      ⟨hc, hle, hF, hn28, h128⟩, hb⟩⟩
    rw [← hofn, getRegOrZr_x]
    simpa [Reg64s.getXReg, h9] using hG
  case n13 =>
    anode b13 b13_ok n13; rw [N, b13_run]
    obtain ⟨o, ⟨hc, hle, hF, hn28, h128⟩, h80, h64⟩ := hJ
    obtain ⟨h16, h8, h160, h152, h144⟩ := hF
    refine .inl ⟨AN.ret, ?_, ?_, o, hc, hle, hn28, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · simp [h80, h64]
    · simp [h16]
    · simp [h8]
  case ret =>
    refine alloc_ndW (Ea ms q) (a := iRet) (lo := -160) (hi := 0) rfl (by rintro w op ⟨⟩) hF
      hR hal hlo hhi (fun s he hn => hcode.ret s he hn) hxa hW.ret fun σ c hJ => ?_
    obtain ⟨o, rfl, hle, hn28, h0, h29, h30⟩ := hJ
    have hk := Call.k_toNat hq.n_lt
    have hcl := hq.cells
    have hA : σ.regs.X0.toBitVec.toNat = ms.heap + 16 * o.toNat + ms.off q.n q.τ := by
      rw [h0, base8_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.heap]; exact hq.room), hq.heap, hk, hq.off]
    obtain ⟨us, hus⟩ := hq.accs
    refine ⟨σ.regs.X0.toBitVec, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, TermRun.cst (.num o.toNat), o.toNat, us, hq.term,
      hq.ev, hq.num, rfl, rfl, hA, hle, hus, fun l ini _ =>
      ⟨?_, rfl, ini, o.toNat, rfl, rfl, hA, hle, h29, h30, us, hus, rfl⟩⟩
    simp [Ea, iRet, AI.tgt, Reg64s.getXReg, h30]

/-- **`scc_rt_alloc` is one segment inside `W`** from its entry to its
return or its heap abort, for every frame condition `F` no write inside the
frame breaks (`seg_alloc` is the frame condition `DFrame R m0`): the counter
and every header the code may store are unmapped in private memory in every
memory of `F` (`hmem`); its nodes'
states lie in `W`, none moved by `K` (`hW`). -/
theorem seg_allocW {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop} (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OK ms (_root_.Executable.labels exe).label) (hcode : Code ms q exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_alloc" + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocW ms q W K exe endPc R F) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label ms q lbl x) s c) :=
  seg_allocW_at hF hR hal hlo hhi hq hcode hentry hmem hxa hW .e

/-- **`scc_rt_alloc` is one segment** from its entry to its return (the
source's allocation step taken, `x` bound at the base the code returns) or
its heap abort, for a call satisfying `Call.OK`, with the prologue falling
through into the entry label (`hentry`) and the counter and every header
the code may store outside the frame and unmapped in private memory
(`hmem`). The return is into the
allocation's continuation (`hxa`: every state at `Ea` for a fresh label is
one `ms.xa` continues in). -/
theorem seg_alloc (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OK ms (_root_.Executable.labels exe).label) (hcode : Code ms q exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_alloc" + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      a.toNat + 8 ≤ 2 ^ 64 ∧ ((a.toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a.toNat) ∧
      Mem.loadInt m0.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R (DFrame R m0) (Ea ms q l b w) s c → ms.xa l b w s c) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label ms q .e))
      (fun s c => ∃ x, At exe endPc R (DFrame R m0) (E (_root_.Executable.labels exe).label ms q lbl x) s c) :=
  (seg_allocW (FStable.dframe R m0) hR hal hlo hhi hq hcode hentry
    (fun a ha => let ⟨hfit, hout, hnone⟩ := hmem a ha; fun _ hD => (hD _ hfit hout).trans hnone)
    hxa (AllocW.triv ms q)).toSeg

end Proof

end Spike.Lib.A64.Alloc
