/-
**`scc_rt_stack_take` in `ret0.w` on AArch64, block by block**: the walks
of the runtime's stack allocator along its one feasible path when
`scc_rt_thread_init` asks for `size0 = 16384` bytes, the named entry and
exit predicates of its segment (S4), and the pcs of its accesses outside
the frame. The nodes at its single instructions (the label addresses, the
lock's swap and release, the free count's load, the next offset's add, the
take site) are the composition's; each walk takes the facts they establish
as hypotheses.

    scc_rt_stack_take(a = x0):                  frame of 208, x29/x30 at 192/200
      .0_entry: class 16384, index 0, offset 0  (stInit)
      .1_cls5:  class < a: next class           (stCls: 16384 fits, the loop exits)
      .3_clsdone7: F, the free list, L          (stFreeN, stFree, stLock)
      .4_spin14: old = swpal [L], 1             (swpPc; stSpin: old = 0, no spin)
      .5_locked15: n = ldr [F]                  (freeNPc; stEmpty: n = 0, to .7_bump)
      .7_bump:  stlr 0, [L]                     (unlPc)
                k = ldaddal [scc_rt_stack_next], a   (nextPc)
                if k + a > 2^29 goto full       (stBnd: not taken)
      .9_ok:    base = stacks + k               (stOk)
      .10_taken: x0 = base, x1 = a; take site; ret   (stSite, sitePc, stRet)

- **The specification**: `Pre g k0` at the entry (`sp`, `x29`, `x30` the
  ghosts `g`, `x0 = size0`) and `Post g k0 stacks` at `g.ra` (`x0 = stacks
  + k0`). The own words on entry are `scc_rt_stack_lock = 0`, the class's
  `scc_rt_stack_free_n = 0` and `scc_rt_stack_next = k0`; the lock is `1`
  between `swpPc` and `unlPc`, `scc_rt_stack_next` is `k0 + size0` after
  `nextPc`.
- **The frame** (`Fr0` … `Fr5`): the saved registers, the size and the
  intermediate values the later blocks read, offsets from the entry's `sp`.
- **The walks** (`stPro_walk` … `stRet_walk`): each block's run from its
  frame predicate to the next, with its pc, offsets and branch;
  `AllocTcb.labStep_spec` is the label address pair.
- **The code** (`stackTakeIn`, `ret0_stackTakeIn`): every block and single
  instruction on the path at its label and index in `ret0Prog`, decided by
  the kernel.
-/
import Spike.Lib.A64Ret0AllocTcb

namespace Spike.Lib.A64.Flow.Ret0.StackTake

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Alloc (subs_c subs_z subs_hi)
open Spike.Lib.A64.Flow.Ret0.AllocTcb (labStep labStep_spec)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- The offsets in the frame. -/
abbrev oI : SO := ⟨-208, []⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩

/-- The prologue: a frame of 208, `x29`/`x30` saved at 192/200, the size `a` at 0. -/
def stPro : List Directive := parseAArch64("sub sp, sp, #208
str x29, [sp, #192]
str x30, [sp, #200]
add x29, sp, #192
str x0, [sp]")

/-- The size classes' start: class 16384, offset 0, count 32768, index 0. -/
def stInit : List Directive := parseAArch64("movz x9, #16384
str x9, [sp, #8]
movz x9, #0
str x9, [sp, #16]
movz x9, #32768
str x9, [sp, #24]
movz x9, #0
str x9, [sp, #32]
b .L6_scc_rt_stack_take.1_cls5")

/-- A class below `a` goes on to the next. -/
def stCls : List Directive := parseAArch64("ldr x9, [sp, #8]
ldr x10, [sp]
subs xzr, x9, x10
b.lo .L6_scc_rt_stack_take.2_clsnext6")

/-- On to `.3_clsdone7`. -/
def stJ1 : List Directive := parseAArch64("b .L6_scc_rt_stack_take.3_clsdone7")

/-- The class's free count's address (the count array plus the index). -/
def stFreeN : List Directive := parseAArch64("str x9, [sp, #48]
ldr x9, [sp, #48]
ldr x10, [sp, #32]
add x9, x9, x10
str x9, [sp, #56]")

/-- The class's free list's address (the list array plus the offset). -/
def stFree : List Directive := parseAArch64("str x9, [sp, #64]
ldr x9, [sp, #64]
ldr x10, [sp, #16]
add x9, x9, x10
str x9, [sp, #72]")

/-- The lock's address saved; on to the spin. -/
def stLock : List Directive := parseAArch64("str x9, [sp, #80]
b .L6_scc_rt_stack_take.4_spin14")

/-- The swap's operands: `x9 = 1`, `x10` the lock's address. -/
def stSwp : List Directive := parseAArch64("movz x9, #1
ldr x10, [sp, #80]")

/-- The lock's old value saved; `0` goes on to `.5_locked15`. -/
def stSpin : List Directive := parseAArch64("str x11, [sp, #88]
ldr x9, [sp, #88]
movz x10, #0
subs xzr, x9, x10
b.eq .L6_scc_rt_stack_take.5_locked15")

/-- The free count's address. -/
def stLdN : List Directive := parseAArch64("ldr x10, [sp, #56]")

/-- An empty free list goes on to `.7_bump`. -/
def stEmpty : List Directive := parseAArch64("str x9, [sp, #96]
ldr x9, [sp, #96]
movz x10, #0
subs xzr, x9, x10
b.eq .L6_scc_rt_stack_take.7_bump")

/-- The unlock's operands: `x9 = 0`, `x10` the lock's address. -/
def stUnl : List Directive := parseAArch64("str x9, [sp, #144]
movz x9, #0
ldr x10, [sp, #144]")

/-- The add's operands: `x9 = a`, `x10` the next offset's address. -/
def stAdd : List Directive := parseAArch64("str x9, [sp, #152]
ldr x9, [sp]
ldr x10, [sp, #152]")

/-- The old offset saved; past the stacks' area (`2^29` bytes) goes to the abort. -/
def stBnd : List Directive := parseAArch64("str x11, [sp, #160]
ldr x9, [sp, #160]
ldr x10, [sp]
add x9, x9, x10
str x9, [sp, #168]
ldr x9, [sp, #168]
movz x10, #8192, lsl #16
subs xzr, x9, x10
b.hi .L6_scc_rt_stack_take.8_full")

/-- On to `.9_ok`. -/
def stJ2 : List Directive := parseAArch64("b .L6_scc_rt_stack_take.9_ok")

/-- The stack's base: the stacks' address plus the old offset; on to `.10_taken`. -/
def stOk : List Directive := parseAArch64("str x9, [sp, #176]
ldr x9, [sp, #176]
ldr x10, [sp, #160]
add x9, x9, x10
str x9, [sp, #128]
b .L6_scc_rt_stack_take.10_taken")

/-- The site's operands: `x0` the base, `x1 = a`. -/
def stSite : List Directive := parseAArch64("ldr x0, [sp, #128]
ldr x1, [sp]")

/-- `x0` the base; the epilogue and the return. -/
def stRet : List Directive := parseAArch64("ldr x0, [sp, #128]
ldr x29, [sp, #192]
ldr x30, [sp, #200]
add sp, sp, #208
ret")

block_spec stPro (-208) 0 oE stPro
block_spec stInit (-208) 0 oI stInit
block_spec stCls (-208) 0 oI stCls
block_spec stJ1 (-208) 0 oI stJ1
block_spec stFreeN (-208) 0 oI stFreeN
block_spec stFree (-208) 0 oI stFree
block_spec stLock (-208) 0 oI stLock
block_spec stSwp (-208) 0 oI stSwp
block_spec stSpin (-208) 0 oI stSpin
block_spec stLdN (-208) 0 oI stLdN
block_spec stEmpty (-208) 0 oI stEmpty
block_spec stUnl (-208) 0 oI stUnl
block_spec stAdd (-208) 0 oI stAdd
block_spec stBnd (-208) 0 oI stBnd
block_spec stJ2 (-208) 0 oI stJ2
block_spec stOk (-208) 0 oI stOk
block_spec stSite (-208) 0 oI stSite
block_spec stRet (-208) 0 oI stRet

/-! ## The specification -/

/-- **The ghosts of a call**: `sp`, `x29` and `x30` at entry. -/
structure G where
  /-- `sp` at entry. -/
  sp : BitVec 64
  /-- `x29` at entry. -/
  fp : BitVec 64
  /-- The return address. -/
  ra : BitVec 64

/-- The size `scc_rt_thread_init` asks for. -/
abbrev size0 : BitVec 64 := 16384#64

/-- **Entry**: `sp`, `x29`, `x30` the ghosts', `x0 = size0`. The own words
are `scc_rt_stack_lock = 0`, the class's `scc_rt_stack_free_n = 0` and
`scc_rt_stack_next = k0` (the map's, not the state's). -/
def Pre (g : G) (_k0 : BitVec 64) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧
  σ.regs.X0.toBitVec = size0

/-- **Exit** (at `g.ra`): `sp`, `x29`, `x30` restored, `x0` the stack's base
`stacks + k0`. The lock is `0` again, the free count `0` and
`scc_rt_stack_next = k0 + size0`. -/
def Post (g : G) (k0 stacks : BitVec 64) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧
  σ.regs.X0.toBitVec = stacks + k0

/-- The frame: `sp` down by 208, the saved `x29`/`x30` and the size. -/
def Fr0 (g : G) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp - 208#64 ∧ σ.slot (-16) = g.fp ∧ σ.slot (-8) = g.ra ∧ σ.slot (-208) = size0

/-- The frame after the classes' start: class `size0`, index and offset 0. -/
def Fr1 (g : G) (σ : AS) : Prop :=
  Fr0 g σ ∧ σ.slot (-200) = size0 ∧ σ.slot (-192) = 0#64 ∧ σ.slot (-176) = 0#64

/-- The frame with the free count's address `F`. -/
def Fr2 (g : G) (F : BitVec 64) (σ : AS) : Prop := Fr1 g σ ∧ σ.slot (-152) = F

/-- The frame with the lock's address `L`. -/
def Fr3 (g : G) (F L : BitVec 64) (σ : AS) : Prop := Fr2 g F σ ∧ σ.slot (-128) = L

/-- The frame after the bump: the old offset `k0`. -/
def Fr4 (g : G) (k0 : BitVec 64) (σ : AS) : Prop := Fr0 g σ ∧ σ.slot (-48) = k0

/-- The frame with the base `stacks + k0`. -/
def Fr5 (g : G) (k0 stacks : BitVec 64) (σ : AS) : Prop := Fr0 g σ ∧ σ.slot (-80) = stacks + k0

/-- `Fr3` gives `Fr0`. -/
theorem Fr3.fr0 {g : G} {F L : BitVec 64} {σ : AS} (h : Fr3 g F L σ) : Fr0 g σ := h.1.1.1

/-! ## The walks -/

/-- A test of `0` against `0` sets the zero flag. -/
theorem subs00_z : (StatusFlags.subs 0#64 0#64 0#64).z = true := by decide

/-- **The prologue**: from the entry to `.0_entry` (five instructions on). -/
theorem stPro_walk (lab : Label → Int64) (pc : Int64) {g : G} {k0 : BitVec 64} {σ : AS} (h : Pre g k0 σ) :
    (arun lab stPro ⟨pc, oE, σ⟩).pc = pc + Int64.ofNat (4 * 5) ∧
    (arun lab stPro ⟨pc, oE, σ⟩).so = ⟨-208, [(.X29, -16)]⟩ ∧ Fr0 g (arun lab stPro ⟨pc, oE, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [stPro_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4]

/-- **The classes' start**, then on to `.1_cls5`. -/
theorem stInit_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr0 g σ) :
    (arun lab stInit ⟨pc, oI, σ⟩).pc = lab ".L6_scc_rt_stack_take.1_cls5" ∧
    (arun lab stInit ⟨pc, oI, σ⟩).so = oI ∧ Fr1 g (arun lab stInit ⟨pc, oI, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [stInit_run]
  refine ⟨rfl, rfl, ?_⟩
  simp [Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4]

/-- **The first class fits** (`size0` is not below `size0`): the loop exits. -/
theorem stCls_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr1 g σ) :
    (arun lab stCls ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 4) ∧
    (arun lab stCls ⟨pc, oI, σ⟩).so = oI ∧ Fr1 g (arun lab stCls ⟨pc, oI, σ⟩).σ := by
  have h4 := h.1.2.2.2
  have h5 := h.2.1
  rw [stCls_run, subs_c, h4, h5]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, h⟩

/-- **The free count's address** `F` (in `x9` before; the index is 0). -/
theorem stFreeN_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {F : BitVec 64} (h : Fr1 g σ)
    (hF : σ.regs.X9.toBitVec = F) :
    (arun lab stFreeN ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 5) ∧
    (arun lab stFreeN ⟨pc, oI, σ⟩).so = oI ∧ Fr2 g F (arun lab stFreeN ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩ := h
  rw [stFreeN_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr2, Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, h6, h7, hF]

/-- **The free list's address** (unused on this path). -/
theorem stFree_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {F : BitVec 64} (h : Fr2 g F σ) :
    (arun lab stFree ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 5) ∧
    (arun lab stFree ⟨pc, oI, σ⟩).so = oI ∧ Fr2 g F (arun lab stFree ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩, h8⟩ := h
  rw [stFree_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr2, Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, h6, h7, h8]

/-- **The lock's address** `L` saved (in `x9` before); on to the spin. -/
theorem stLock_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {F L : BitVec 64} (h : Fr2 g F σ)
    (hL : σ.regs.X9.toBitVec = L) :
    (arun lab stLock ⟨pc, oI, σ⟩).pc = lab ".L6_scc_rt_stack_take.4_spin14" ∧
    (arun lab stLock ⟨pc, oI, σ⟩).so = oI ∧ Fr3 g F L (arun lab stLock ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩, h8⟩ := h
  rw [stLock_run]
  refine ⟨rfl, rfl, ?_⟩
  simp [Fr3, Fr2, Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, h6, h7, h8, hL]

/-- **The swap's operands**: `x9 = 1`, `x10 = L`. -/
theorem stSwp_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {F L : BitVec 64} (h : Fr3 g F L σ) :
    (arun lab stSwp ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 2) ∧
    (arun lab stSwp ⟨pc, oI, σ⟩).so = oI ∧ Fr3 g F L (arun lab stSwp ⟨pc, oI, σ⟩).σ ∧
    (arun lab stSwp ⟨pc, oI, σ⟩).σ.regs.X9.toBitVec = 1#64 ∧
    (arun lab stSwp ⟨pc, oI, σ⟩).σ.regs.X10.toBitVec = L := by
  obtain ⟨⟨⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩, h8⟩, h9⟩ := h
  rw [stSwp_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr3, Fr2, Fr1, Fr0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- **The lock was free** (the swap's old value `0`, in `x11`): on to
`.5_locked15`. -/
theorem stSpin_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {F L : BitVec 64} (h : Fr3 g F L σ)
    (h11 : σ.regs.X11.toBitVec = 0#64) :
    (arun lab stSpin ⟨pc, oI, σ⟩).pc = lab ".L6_scc_rt_stack_take.5_locked15" ∧
    (arun lab stSpin ⟨pc, oI, σ⟩).so = oI ∧ Fr3 g F L (arun lab stSpin ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩, h8⟩, h9⟩ := h
  rw [stSpin_run, h11]
  refine ⟨by simp [subs00_z], rfl, ?_⟩
  simp [Fr3, Fr2, Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- **The free count's address** in `x10`. -/
theorem stLdN_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {F L : BitVec 64} (h : Fr3 g F L σ) :
    (arun lab stLdN ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 1) ∧
    (arun lab stLdN ⟨pc, oI, σ⟩).so = oI ∧ Fr3 g F L (arun lab stLdN ⟨pc, oI, σ⟩).σ ∧
    (arun lab stLdN ⟨pc, oI, σ⟩).σ.regs.X10.toBitVec = F := by
  obtain ⟨⟨⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩, h8⟩, h9⟩ := h
  rw [stLdN_run]
  refine ⟨rfl, rfl, ?_⟩
  simp [Fr3, Fr2, Fr1, Fr0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- **The free list is empty** (the count `0`, in `x9`): on to `.7_bump`. -/
theorem stEmpty_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {F L : BitVec 64} (h : Fr3 g F L σ)
    (h9 : σ.regs.X9.toBitVec = 0#64) :
    (arun lab stEmpty ⟨pc, oI, σ⟩).pc = lab ".L6_scc_rt_stack_take.7_bump" ∧
    (arun lab stEmpty ⟨pc, oI, σ⟩).so = oI ∧ Fr3 g F L (arun lab stEmpty ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩, h8⟩, h10⟩ := h
  rw [stEmpty_run, h9]
  refine ⟨by simp [subs00_z], rfl, ?_⟩
  simp [Fr3, Fr2, Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, h6, h7, h8, h10]

/-- **The unlock's operands**: `x9 = 0`, `x10 = L` (in `x9` before). -/
theorem stUnl_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {L : BitVec 64} (h : Fr0 g σ)
    (hL : σ.regs.X9.toBitVec = L) :
    (arun lab stUnl ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 3) ∧
    (arun lab stUnl ⟨pc, oI, σ⟩).so = oI ∧ Fr0 g (arun lab stUnl ⟨pc, oI, σ⟩).σ ∧
    (arun lab stUnl ⟨pc, oI, σ⟩).σ.regs.X9.toBitVec = 0#64 ∧
    (arun lab stUnl ⟨pc, oI, σ⟩).σ.regs.X10.toBitVec = L := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [stUnl_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, hL]

/-- **The add's operands**: `x9 = size0`, `x10 = N` (in `x9` before). -/
theorem stAdd_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {N : BitVec 64} (h : Fr0 g σ)
    (hN : σ.regs.X9.toBitVec = N) :
    (arun lab stAdd ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 3) ∧
    (arun lab stAdd ⟨pc, oI, σ⟩).so = oI ∧ Fr0 g (arun lab stAdd ⟨pc, oI, σ⟩).σ ∧
    (arun lab stAdd ⟨pc, oI, σ⟩).σ.regs.X9.toBitVec = size0 ∧
    (arun lab stAdd ⟨pc, oI, σ⟩).σ.regs.X10.toBitVec = N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [stAdd_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, hN]

/-- **The bound is not crossed** when the old offset `k0` (in `x11`) has
room for `size0` more bytes below `2^29`. -/
theorem stBnd_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {k0 : BitVec 64} (h : Fr0 g σ)
    (h11 : σ.regs.X11.toBitVec = k0) (hk : k0.toNat + 16384 ≤ 536870912) :
    (arun lab stBnd ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 9) ∧
    (arun lab stBnd ⟨pc, oI, σ⟩).so = oI ∧ Fr4 g k0 (arun lab stBnd ⟨pc, oI, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc : ¬ ((StatusFlags.subs (k0 + size0 - 536870912#64) (k0 + size0) 536870912#64).c = true ∧
      (StatusFlags.subs (k0 + size0 - 536870912#64) (k0 + size0) 536870912#64).z = false) := by
    rw [subs_hi, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [stBnd_run, h11, h4, ite_eq_right_iff.mpr (fun h => absurd h hc)]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr4, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h11]

/-- **The base** `stacks + k0` (`stacks` in `x9` before); on to `.10_taken`. -/
theorem stOk_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {k0 B : BitVec 64} (h : Fr4 g k0 σ)
    (hB : σ.regs.X9.toBitVec = B) :
    (arun lab stOk ⟨pc, oI, σ⟩).pc = lab ".L6_scc_rt_stack_take.10_taken" ∧
    (arun lab stOk ⟨pc, oI, σ⟩).so = oI ∧ Fr5 g k0 B (arun lab stOk ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h
  rw [stOk_run]
  refine ⟨rfl, rfl, ?_⟩
  simp [Fr5, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, hB]

/-- **The site's operands**: `x0 = stacks + k0`, `x1 = size0`. -/
theorem stSite_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {k0 B : BitVec 64} (h : Fr5 g k0 B σ) :
    (arun lab stSite ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 2) ∧
    (arun lab stSite ⟨pc, oI, σ⟩).so = oI ∧ Fr5 g k0 B (arun lab stSite ⟨pc, oI, σ⟩).σ ∧
    (arun lab stSite ⟨pc, oI, σ⟩).σ.regs.X0.toBitVec = B + k0 ∧
    (arun lab stSite ⟨pc, oI, σ⟩).σ.regs.X1.toBitVec = size0 := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h
  rw [stSite_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr5, Fr0, h1, h2, h3, h4, h5]

/-- **The return**: to `g.ra` with `x0 = stacks + k0`, the frame popped. -/
theorem stRet_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {k0 B : BitVec 64} (h : Fr5 g k0 B σ) :
    (arun lab stRet ⟨pc, oI, σ⟩).pc = Int64.ofBitVec g.ra ∧
    (arun lab stRet ⟨pc, oI, σ⟩).so = oE ∧ Post g k0 B (arun lab stRet ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h
  rw [stRet_run]
  refine ⟨by rw [h3], rfl, ?_⟩
  simp [Post, h1, h2, h3, h5, BitVec.sub_add_cancel]

/-! ## The code -/

/-- `scc_rt_stack_take`'s label. -/
abbrev fnL : Label := "scc_rt_stack_take"
/-- Its entry label. -/
abbrev entryL : Label := ".L6_scc_rt_stack_take.0_entry"
/-- The class loop's label. -/
abbrev clsL : Label := ".L6_scc_rt_stack_take.1_cls5"
/-- The classes' end. -/
abbrev doneL : Label := ".L6_scc_rt_stack_take.3_clsdone7"
/-- The spin's label. -/
abbrev spinL : Label := ".L6_scc_rt_stack_take.4_spin14"
/-- The locked label. -/
abbrev lockedL : Label := ".L6_scc_rt_stack_take.5_locked15"
/-- The bump's label. -/
abbrev bumpL : Label := ".L6_scc_rt_stack_take.7_bump"
/-- The base's label. -/
abbrev okL : Label := ".L6_scc_rt_stack_take.9_ok"
/-- The taken label. -/
abbrev takenL : Label := ".L6_scc_rt_stack_take.10_taken"
/-- The site's label. -/
abbrev siteL : Label := "scc_rt_take_site"

/-- **The pc of the lock's swap** (`swpal`: the lock `0 → 1`). -/
abbrev swpPc (lab : Label → Int64) : Int64 := lab spinL + Int64.ofNat (4 * 2)
/-- The pc of the free count's load (read only: `0`). -/
abbrev freeNPc (lab : Label → Int64) : Int64 := lab lockedL + Int64.ofNat (4 * 1)
/-- **The pc of the unlock** (`stlr`: the lock `1 → 0`). -/
abbrev unlPc (lab : Label → Int64) : Int64 := lab bumpL + Int64.ofNat (4 * 5)
/-- **The pc of the next offset's add** (`ldaddal`: `k0 → k0 + size0`). -/
abbrev nextPc (lab : Label → Int64) : Int64 := lab bumpL + Int64.ofNat (4 * 11)
/-- The pc of the take site (`nop`). -/
abbrev sitePc (lab : Label → Int64) : Int64 := lab siteL

/-- A label's address in `prog`: the `adrp`/`add` pair at `l`, `k`. -/
def labIn (prog : List Directive) (l : Label) (k : Nat) (L : Label) : Bool :=
  blockAt prog l k [(SI.adrp .X9 L).toDir] && blockAt prog l (k + 1) [(SI.addLo12 .X9 .X9 L).toDir]

/-- **`scc_rt_stack_take`'s code on the feasible path in `prog`**: its
blocks, its single instructions and the fall-throughs into `.0_entry` and
the take site. -/
def stackTakeIn (prog : List Directive) : Bool :=
  labelGap prog fnL entryL 5 && blockAt prog fnL 0 stPro && blockAt prog entryL 0 stInit &&
  blockAt prog clsL 0 stCls && blockAt prog clsL 4 stJ1 &&
  labIn prog doneL 0 "scc_rt_stack_free_n" && blockAt prog doneL 2 stFreeN &&
  labIn prog doneL 7 "scc_rt_stack_free" && blockAt prog doneL 9 stFree &&
  labIn prog doneL 14 "scc_rt_stack_lock" && blockAt prog doneL 16 stLock &&
  blockAt prog spinL 0 stSwp && blockAt prog spinL 2 (parseAArch64("swpal x9, x11, [x10]")) &&
  blockAt prog spinL 3 stSpin &&
  blockAt prog lockedL 0 stLdN && blockAt prog lockedL 1 (parseAArch64("ldr x9, [x10]")) &&
  blockAt prog lockedL 2 stEmpty &&
  labIn prog bumpL 0 "scc_rt_stack_lock" && blockAt prog bumpL 2 stUnl &&
  blockAt prog bumpL 5 (parseAArch64("stlr x9, [x10]")) &&
  labIn prog bumpL 6 "scc_rt_stack_next" && blockAt prog bumpL 8 stAdd &&
  blockAt prog bumpL 11 (parseAArch64("ldaddal x9, x11, [x10]")) && blockAt prog bumpL 12 stBnd &&
  blockAt prog bumpL 21 stJ2 &&
  labIn prog okL 0 "scc_rt_stacks" && blockAt prog okL 2 stOk &&
  blockAt prog takenL 0 stSite && labelGap prog takenL siteL 2 &&
  blockAt prog siteL 0 (parseAArch64("nop")) && blockAt prog siteL 1 stRet

#guard stackTakeIn SccCode.ret0Prog

/-- The code's check on `ret0Prog`. -/
theorem ret0_stackTakeIn : stackTakeIn SccCode.ret0Prog = true := by decide +kernel

end Spike.Lib.A64.Flow.Ret0.StackTake
