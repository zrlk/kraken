/-
**`scc_rt_stack_take` in `ret0.w` on x64, block by block**: the x64 twin of
`Spike/Lib/A64Ret0StackTake.lean`. The walks of the runtime's stack
allocator along its one feasible path when `scc_rt_thread_init` asks for
`size0 = 16384` bytes, the named entry and exit predicates of its segment
(S4), and the pcs of its accesses outside the frame. The nodes at its
single instructions (the label addresses, the lock's `xchg` and release,
the free count's load, the next offset's `lock xadd`, the take site) are
the composition's; each walk takes the facts they establish as hypotheses.

    scc_rt_stack_take(a = %rdi):                 frame of 192 below %rbp
      .entry:    class 16384, index 0, offset 0  (stInit)
      .cls5:     class < a: next class           (stCls: 16384 fits, the loop exits)
      .clsdone7: F, the free list, L             (stFreeN, stFree, stLock)
      .spin14:   old = xchg [L], 1               (swpPc; stSpin: old = 0, no spin)
      .locked15: n = [F]                         (freeNPc; stEmpty: n = 0, to .bump)
      .bump:     [L] = 0                         (unlPc)
                 k = lock xadd [scc_rt_stack_next], a   (nextPc)
                 if k + a > 2^29 goto full       (stBnd: not taken)
      .ok:       base = stacks + k               (stOk)
      .taken:    %rdi = base, %rsi = a; take site; ret  (stSite, sitePc, stRet)

- **The specification**: `Pre g k0` at the entry (`%rsp`, `%rbp` and the
  return address the ghosts `g`, `%rdi = size0`) and `Post g k0 stacks` at
  `g.ra` (`%rax = stacks + k0`). The own words on entry are
  `scc_rt_stack_lock = 0`, the class's `scc_rt_stack_free_n = 0` and
  `scc_rt_stack_next = k0`; the lock is `1` between `swpPc` and `unlPc`,
  `scc_rt_stack_next` is `k0 + size0` after `nextPc`.
- **The frame** (`Fr g ss`): `%rsp` at the frame's base, `%rbp` at the
  saved `%rbp`, and the cells `ss` the later blocks read (`s0` … `s5`),
  offsets from the entry's `%rsp`; `Fr.mono` forgets cells.
- **The walks** (`stPro_walk` … `stRet_walk`): each block's run from its
  frame to the next, with its pc, offsets and branch, and the registers
  the next single instruction reads; `si_fr`, `si_so` and
  `AllocTcb.si_rax` are the label addresses.
- **The code** (`stackTakeIn`, `ret0_stackTakeIn`): every block and single
  instruction on the path at its label and byte offset in `ret0Cells`,
  decided by the kernel.
-/
import Spike.Lib.X64Ret0AllocTcb

namespace Spike.Lib.X64.Flow.Ret0.StackTake

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB)
open Spike.Lib.X64.Flow.Ret0.AllocTcb (G siAt)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- The offsets in the frame: `%rsp` at the frame's base, `%rbp` at the saved `%rbp`. -/
abbrev oI : SO := ⟨-200, [(.rbp, -8)]⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩
/-- The offsets after the return. -/
abbrev oR : SO := ⟨8, []⟩

/-- The prologue: a frame of 192, the size `a` at `-8(%rbp)`. -/
def stPro : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $192, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 7, 4]

/-- The size classes' start: class 16384, offset 0, count 32768, index 0. -/
def stInit : List (Directive × Nat) := (parse("movq $16384, %rax
movq %rax, -16(%rbp)
movq $0, %rax
movq %rax, -24(%rbp)
movq $32768, %rax
movq %rax, -32(%rbp)
movq $0, %rax
movq %rax, -40(%rbp)
jmp .Lscc_rt_stack_take.cls5")).zip [7, 4, 7, 4, 7, 4, 7, 4, 2]

/-- A class below `a` goes on to the next. -/
def stCls : List (Directive × Nat) := (parse("movq -16(%rbp), %rax
movq -8(%rbp), %rcx
cmpq %rcx, %rax
jb .Lscc_rt_stack_take.clsnext6")).zip [4, 4, 3, 2]

/-- On to `.clsdone7`. -/
def stJ1 : List (Directive × Nat) := (parse("jmp .Lscc_rt_stack_take.clsdone7")).zip [2]

/-- The class's free count's address (the count array plus the index). -/
def stFreeN : List (Directive × Nat) := (parse("movq %rax, -56(%rbp)
movq -56(%rbp), %rax
movq -40(%rbp), %rcx
addq %rcx, %rax
movq %rax, -64(%rbp)")).zip [4, 4, 4, 3, 4]

/-- The class's free list's address (the list array plus the offset). -/
def stFree : List (Directive × Nat) := (parse("movq %rax, -72(%rbp)
movq -72(%rbp), %rax
movq -24(%rbp), %rcx
addq %rcx, %rax
movq %rax, -80(%rbp)")).zip [4, 4, 4, 3, 4]

/-- The lock's address saved; on to the spin. -/
def stLock : List (Directive × Nat) := (parse("movq %rax, -88(%rbp)
jmp .Lscc_rt_stack_take.spin14")).zip [4, 2]

/-- The swap's operands: `%rcx` the lock's address, `%rax = 1`. -/
def stSwp : List (Directive × Nat) := (parse("movq -88(%rbp), %rcx
movq $1, %rax")).zip [4, 7]

/-- The lock's old value saved; `0` goes on to `.locked15`. -/
def stSpin : List (Directive × Nat) := (parse("movq %rax, -96(%rbp)
movq -96(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_stack_take.locked15")).zip [4, 4, 7, 3, 2]

/-- The free count's address. -/
def stLdN : List (Directive × Nat) := (parse("movq -64(%rbp), %rcx")).zip [4]

/-- An empty free list goes on to `.bump`. -/
def stEmpty : List (Directive × Nat) := (parse("movq %rax, -104(%rbp)
movq -104(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_stack_take.bump")).zip [4, 4, 7, 3, 2]

/-- The unlock's operands: `%rcx` the lock's address, `%rax = 0`. -/
def stUnl : List (Directive × Nat) := (parse("movq %rax, -152(%rbp)
movq -152(%rbp), %rcx
movq $0, %rax")).zip [7, 7, 7]

/-- The add's operands: `%rcx` the next offset's address, `%rax = a`. -/
def stAdd : List (Directive × Nat) := (parse("movq %rax, -160(%rbp)
movq -160(%rbp), %rcx
movq -8(%rbp), %rax")).zip [7, 7, 4]

/-- The old offset saved; past the stacks' area (`2^29` bytes) goes to the abort. -/
def stBnd : List (Directive × Nat) := (parse("movq %rax, -168(%rbp)
movq -168(%rbp), %rax
movq -8(%rbp), %rcx
addq %rcx, %rax
movq %rax, -176(%rbp)
movq -176(%rbp), %rax
movq $536870912, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_stack_take.full")).zip [7, 7, 4, 3, 7, 7, 7, 3, 2]

/-- On to `.ok`. -/
def stJ2 : List (Directive × Nat) := (parse("jmp .Lscc_rt_stack_take.ok")).zip [2]

/-- The stack's base: the stacks' address plus the old offset; on to `.taken`. -/
def stOk : List (Directive × Nat) := (parse("movq %rax, -184(%rbp)
movq -184(%rbp), %rax
movq -168(%rbp), %rcx
addq %rcx, %rax
movq %rax, -136(%rbp)
jmp .Lscc_rt_stack_take.taken")).zip [7, 7, 7, 3, 7, 2]

/-- The site's operands: `%rdi` the base, `%rsi = a`. -/
def stSite : List (Directive × Nat) := (parse("movq -136(%rbp), %rdi
movq -8(%rbp), %rsi")).zip [7, 4]

/-- `%rax` the base; the epilogue and the return. -/
def stRet : List (Directive × Nat) := (parse("movq -136(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [7, 3, 1, 1]

block_spec stPro (-200) 8 oE stPro
block_spec stInit (-200) 8 oI stInit
block_spec stCls (-200) 8 oI stCls
block_spec stJ1 (-200) 8 oI stJ1
block_spec stFreeN (-200) 8 oI stFreeN
block_spec stFree (-200) 8 oI stFree
block_spec stLock (-200) 8 oI stLock
block_spec stSwp (-200) 8 oI stSwp
block_spec stSpin (-200) 8 oI stSpin
block_spec stLdN (-200) 8 oI stLdN
block_spec stEmpty (-200) 8 oI stEmpty
block_spec stUnl (-200) 8 oI stUnl
block_spec stAdd (-200) 8 oI stAdd
block_spec stBnd (-200) 8 oI stBnd
block_spec stJ2 (-200) 8 oI stJ2
block_spec stOk (-200) 8 oI stOk
block_spec stSite (-200) 8 oI stSite
block_spec stRet (-200) 8 oI stRet

/-! ## The specification -/

/-- The size `scc_rt_thread_init` asks for. -/
abbrev size0 : BitVec 64 := 16384#64

/-- **Entry**: `%rsp`, `%rbp`, the return address the ghosts', `%rdi =
size0`. The own words are `scc_rt_stack_lock = 0`, the class's
`scc_rt_stack_free_n = 0` and `scc_rt_stack_next = k0` (the map's, not the
state's). -/
def Pre (g : G) (_k0 : BitVec 64) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.slot 0 = g.ra ∧ σ.regs.rdi.toBitVec = size0

/-- **Exit** (at `g.ra`): `%rsp` past the return address, `%rbp` restored,
`%rax` the stack's base `stacks + k0`. The lock is `0` again, the free
count `0` and `scc_rt_stack_next = k0 + size0`. -/
def Post (g : G) (k0 stacks : BitVec 64) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp + 8#64 ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.regs.rax.toBitVec = stacks + k0

/-- **The frame**: `%rsp` at the frame's base, `%rbp` at the saved `%rbp`,
the cells `ss` (offsets from the entry's `%rsp`). -/
def Fr (g : G) (ss : List (Int × BitVec 64)) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp - 200#64 ∧ σ.regs.rbp.toBitVec = g.sp - 8#64 ∧ ∀ p ∈ ss, σ.slot p.1 = p.2

/-- A frame with fewer cells. -/
theorem Fr.mono {g : G} {ss ss' : List (Int × BitVec 64)} {σ : AS} (h : Fr g ss σ) (hs : ∀ p ∈ ss', p ∈ ss) :
    Fr g ss' σ :=
  ⟨h.1, h.2.1, fun p hp => h.2.2 p (hs p hp)⟩

/-- The return address, the saved `%rbp` and the size. -/
abbrev s0 (g : G) : List (Int × BitVec 64) := [(0, g.ra), (-8, g.fp), (-16, size0)]
/-- With the class `size0`, the offset and the index `0`. -/
abbrev s1 (g : G) : List (Int × BitVec 64) := (-24, size0) :: (-32, 0#64) :: (-48, 0#64) :: s0 g
/-- With the free count's address `F`. -/
abbrev s2 (g : G) (F : BitVec 64) : List (Int × BitVec 64) := (-72, F) :: s1 g
/-- With the lock's address `L`. -/
abbrev s3 (g : G) (F L : BitVec 64) : List (Int × BitVec 64) := (-96, L) :: s2 g F
/-- With the old offset `k0`. -/
abbrev s4 (g : G) (k0 : BitVec 64) : List (Int × BitVec 64) := (-176, k0) :: s0 g
/-- With the base `B + k0`. -/
abbrev s5 (g : G) (k0 B : BitVec 64) : List (Int × BitVec 64) := (-144, B + k0) :: s4 g k0

/-- `s3` holds `s0`'s cells. -/
theorem s3_s0 (g : G) (F L : BitVec 64) : ∀ p ∈ s0 g, p ∈ s3 g F L := by simp

/-! ## The walks -/

/-- Unfolds a frame hypothesis. -/
local macro "frh" h:ident : tactic =>
  `(tactic| simp only [Fr, List.forall_mem_cons, List.forall_mem_nil] at $h:ident)

/-- Closes a walk's goal from the run's normal form. -/
local macro "walk" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Fr, Post, Reg64s.set64, Reg64s.get64, upd_apply, $ts,*])

/-- **The prologue**: from the entry to `.entry`, the frame set up. -/
theorem stPro_walk (lab : String → Int64) (pc : Int64) {g : G} {k0 : BitVec 64} {σ : AS} (h : Pre g k0 σ) :
    (arun lab stPro ⟨pc, oE, σ⟩).pc = pc + Int64.ofNat 15 ∧
    (arun lab stPro ⟨pc, oE, σ⟩).so = oI ∧ Fr g (s0 g) (arun lab stPro ⟨pc, oE, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [stPro_run]
  refine ⟨rfl, rfl, ?_⟩
  walk [h1, h2, h3, h4]
  bv_omega

/-- **The classes' start**, then on to `.cls5`. -/
theorem stInit_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (s0 g) σ) :
    (arun lab stInit ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_stack_take.cls5" ∧
    (arun lab stInit ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s1 g) (arun lab stInit ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [stInit_run]
  walk [h]

/-- **The first class fits** (`size0` is not below `size0`): the loop exits. -/
theorem stCls_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (s1 g) σ) :
    (arun lab stCls ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 13 ∧
    (arun lab stCls ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s1 g) (arun lab stCls ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [stCls_run]
  walk [h]

/-- On to `.clsdone7`. -/
theorem stJ1_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (s1 g) σ) :
    (arun lab stJ1 ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_stack_take.clsdone7" ∧
    (arun lab stJ1 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s1 g) (arun lab stJ1 ⟨pc, oI, σ⟩).σ := by
  rw [stJ1_run]
  exact ⟨rfl, rfl, h⟩

/-- **The free count's address** `F` (in `%rax` before; the index is 0). -/
theorem stFreeN_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {F : BitVec 64} (h : Fr g (s1 g) σ)
    (hF : σ.regs.rax.toBitVec = F) :
    (arun lab stFreeN ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 19 ∧
    (arun lab stFreeN ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s2 g F) (arun lab stFreeN ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [stFreeN_run]
  walk [h, hF]

/-- **The free list's address** (unused on this path). -/
theorem stFree_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {F : BitVec 64} (h : Fr g (s2 g F) σ) :
    (arun lab stFree ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 19 ∧
    (arun lab stFree ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s2 g F) (arun lab stFree ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [stFree_run]
  walk [h]

/-- **The lock's address** `L` saved (in `%rax` before); on to the spin. -/
theorem stLock_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {F L : BitVec 64} (h : Fr g (s2 g F) σ)
    (hL : σ.regs.rax.toBitVec = L) :
    (arun lab stLock ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_stack_take.spin14" ∧
    (arun lab stLock ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s3 g F L) (arun lab stLock ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [stLock_run]
  walk [h, hL]

/-- **The swap's operands**: `%rcx = L`, `%rax = 1`. -/
theorem stSwp_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {F L : BitVec 64} (h : Fr g (s3 g F L) σ) :
    (arun lab stSwp ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 11 ∧
    (arun lab stSwp ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s3 g F L) (arun lab stSwp ⟨pc, oI, σ⟩).σ ∧
    (arun lab stSwp ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = L ∧
    (arun lab stSwp ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 1#64 := by
  frh h
  rw [stSwp_run]
  walk [h]

/-- **The lock was free** (the swap's old value `0`, in `%rax`): on to
`.locked15`. -/
theorem stSpin_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {F L : BitVec 64} (h : Fr g (s3 g F L) σ)
    (ha : σ.regs.rax.toBitVec = 0#64) :
    (arun lab stSpin ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_stack_take.locked15" ∧
    (arun lab stSpin ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s3 g F L) (arun lab stSpin ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [stSpin_run]
  walk [h, ha]

/-- **The free count's address** in `%rcx`. -/
theorem stLdN_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {F L : BitVec 64} (h : Fr g (s3 g F L) σ) :
    (arun lab stLdN ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 4 ∧
    (arun lab stLdN ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s3 g F L) (arun lab stLdN ⟨pc, oI, σ⟩).σ ∧
    (arun lab stLdN ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = F := by
  frh h
  rw [stLdN_run]
  walk [h]

/-- **The free list is empty** (the count `0`, in `%rax`): on to `.bump`. -/
theorem stEmpty_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {F L : BitVec 64} (h : Fr g (s3 g F L) σ)
    (ha : σ.regs.rax.toBitVec = 0#64) :
    (arun lab stEmpty ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_stack_take.bump" ∧
    (arun lab stEmpty ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s3 g F L) (arun lab stEmpty ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [stEmpty_run]
  walk [h, ha]

/-- **The unlock's operands**: `%rcx = L` (in `%rax` before), `%rax = 0`. -/
theorem stUnl_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {L : BitVec 64} (h : Fr g (s0 g) σ)
    (hL : σ.regs.rax.toBitVec = L) :
    (arun lab stUnl ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 21 ∧
    (arun lab stUnl ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s0 g) (arun lab stUnl ⟨pc, oI, σ⟩).σ ∧
    (arun lab stUnl ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = L ∧
    (arun lab stUnl ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 0#64 := by
  frh h
  rw [stUnl_run]
  walk [h, hL]

/-- **The add's operands**: `%rcx = N` (in `%rax` before), `%rax = size0`. -/
theorem stAdd_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {N : BitVec 64} (h : Fr g (s0 g) σ)
    (hN : σ.regs.rax.toBitVec = N) :
    (arun lab stAdd ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 18 ∧
    (arun lab stAdd ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s0 g) (arun lab stAdd ⟨pc, oI, σ⟩).σ ∧
    (arun lab stAdd ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = N ∧
    (arun lab stAdd ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = size0 := by
  frh h
  rw [stAdd_run]
  walk [h, hN]

/-- **The bound is not crossed** when the old offset `k0` (in `%rax`) has
room for `size0` more bytes below `2^29`. -/
theorem stBnd_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {k0 : BitVec 64} (h : Fr g (s0 g) σ)
    (ha : σ.regs.rax.toBitVec = k0) (hk : k0.toNat + 16384 ≤ 536870912) :
    (arun lab stBnd ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 47 ∧
    (arun lab stBnd ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s4 g k0) (arun lab stBnd ⟨pc, oI, σ⟩).σ := by
  frh h
  have hr : (σ.regs.rax.toNat : Int) = k0.toNat := by rw [← ha]; rfl
  rw [stBnd_run]
  walk [h, ha]
  intro h1 h2
  by_cases he : k0.toNat + 16384 = 536870912
  · refine absurd (BitVec.eq_of_toNat_eq ?_) h2
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits] at he ⊢
    omega
  · rw [hr] at h1; omega

/-- On to `.ok`. -/
theorem stJ2_walk (lab : String → Int64) (pc : Int64) {g : G} {k0 : BitVec 64} {σ : AS} (h : Fr g (s4 g k0) σ) :
    (arun lab stJ2 ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_stack_take.ok" ∧
    (arun lab stJ2 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s4 g k0) (arun lab stJ2 ⟨pc, oI, σ⟩).σ := by
  rw [stJ2_run]
  exact ⟨rfl, rfl, h⟩

/-- **The base** `B + k0` (`B`, the stacks' address, in `%rax` before); on
to `.taken`. -/
theorem stOk_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {k0 B : BitVec 64} (h : Fr g (s4 g k0) σ)
    (hB : σ.regs.rax.toBitVec = B) :
    (arun lab stOk ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_stack_take.taken" ∧
    (arun lab stOk ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s5 g k0 B) (arun lab stOk ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [stOk_run]
  walk [h, hB]
  exact BitVec.add_comm _ _

/-- **The site's operands**: `%rdi = B + k0`, `%rsi = size0`. -/
theorem stSite_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {k0 B : BitVec 64}
    (h : Fr g (s5 g k0 B) σ) :
    (arun lab stSite ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 11 ∧
    (arun lab stSite ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s5 g k0 B) (arun lab stSite ⟨pc, oI, σ⟩).σ ∧
    (arun lab stSite ⟨pc, oI, σ⟩).σ.regs.rdi.toBitVec = B + k0 ∧
    (arun lab stSite ⟨pc, oI, σ⟩).σ.regs.rsi.toBitVec = size0 := by
  frh h
  rw [stSite_run]
  walk [h]

/-- **The return**: to `g.ra` with `%rax = B + k0`, the frame popped. -/
theorem stRet_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {k0 B : BitVec 64}
    (h : Fr g (s5 g k0 B) σ) :
    (arun lab stRet ⟨pc, oI, σ⟩).pc = Int64.ofBitVec g.ra ∧
    (arun lab stRet ⟨pc, oI, σ⟩).so = oR ∧ Post g k0 B (arun lab stRet ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [stRet_run]
  walk [h]

/-! ## The single instructions -/

/-- A label's address into `%rax` keeps the frame. -/
theorem si_fr (lab : Label → Int64) (L : Label) {g : G} {ss : List (Int × BitVec 64)} {σ : AS}
    (h : Fr g ss σ) : Fr g ss ((SI.leaRip .rax L).step lab σ) := h

/-- It forgets `%rax` only. -/
theorem si_so (L : Label) : (SI.leaRip .rax L).so oI = oI := by
  simp [SI.so, SI.dst, SO.kill, rm]

/-! ## The code -/

/-- `scc_rt_stack_take`'s label. -/
abbrev fnL : Label := "scc_rt_stack_take"
/-- Its entry label. -/
abbrev entryL : Label := ".Lscc_rt_stack_take.entry"
/-- The class loop's label. -/
abbrev clsL : Label := ".Lscc_rt_stack_take.cls5"
/-- The classes' end. -/
abbrev doneL : Label := ".Lscc_rt_stack_take.clsdone7"
/-- The spin's label. -/
abbrev spinL : Label := ".Lscc_rt_stack_take.spin14"
/-- The locked label. -/
abbrev lockedL : Label := ".Lscc_rt_stack_take.locked15"
/-- The bump's label. -/
abbrev bumpL : Label := ".Lscc_rt_stack_take.bump"
/-- The base's label. -/
abbrev okL : Label := ".Lscc_rt_stack_take.ok"
/-- The taken label. -/
abbrev takenL : Label := ".Lscc_rt_stack_take.taken"
/-- The site's label. -/
abbrev siteL : Label := "scc_rt_take_site"

/-- **The pc of the lock's swap** (`xchg`: the lock `0 → 1`). -/
abbrev swpPc (lab : Label → Int64) : Int64 := lab spinL + Int64.ofNat 11
/-- The pc of the free count's load (read only: `0`). -/
abbrev freeNPc (lab : Label → Int64) : Int64 := lab lockedL + Int64.ofNat 4
/-- **The pc of the unlock** (a plain store: the lock `1 → 0`). -/
abbrev unlPc (lab : Label → Int64) : Int64 := lab bumpL + Int64.ofNat 28
/-- **The pc of the next offset's add** (`lock xadd`: `k0 → k0 + size0`). -/
abbrev nextPc (lab : Label → Int64) : Int64 := lab bumpL + Int64.ofNat 56
/-- The pc of the take site (`nop`). -/
abbrev sitePc (lab : Label → Int64) : Int64 := lab siteL

/-- **`scc_rt_stack_take`'s code on the feasible path in `cells`**: its
blocks, its single instructions and the fall-throughs into `.entry` and
the take site. -/
def stackTakeIn (cells : List (Directive × Nat)) : Bool :=
  labelGapB cells fnL entryL 15 && blockAtB cells fnL 0 stPro && blockAtB cells entryL 0 stInit &&
  blockAtB cells clsL 0 stCls && blockAtB cells clsL 13 stJ1 &&
  siAt cells doneL 0 "scc_rt_stack_free_n" && blockAtB cells doneL 7 stFreeN &&
  siAt cells doneL 26 "scc_rt_stack_free" && blockAtB cells doneL 33 stFree &&
  siAt cells doneL 52 "scc_rt_stack_lock" && blockAtB cells doneL 59 stLock &&
  blockAtB cells spinL 0 stSwp && blockAtB cells spinL 11 ((parse("xchgq %rax, (%rcx)")).zip [3]) &&
  blockAtB cells spinL 14 stSpin &&
  blockAtB cells lockedL 0 stLdN && blockAtB cells lockedL 4 ((parse("movq (%rcx), %rax")).zip [3]) &&
  blockAtB cells lockedL 7 stEmpty &&
  siAt cells bumpL 0 "scc_rt_stack_lock" && blockAtB cells bumpL 7 stUnl &&
  blockAtB cells bumpL 28 ((parse("movq %rax, (%rcx)")).zip [3]) &&
  siAt cells bumpL 31 "scc_rt_stack_next" && blockAtB cells bumpL 38 stAdd &&
  blockAtB cells bumpL 56 ((parse("lock xaddq %rax, (%rcx)")).zip [5]) && blockAtB cells bumpL 61 stBnd &&
  blockAtB cells bumpL 108 stJ2 &&
  siAt cells okL 0 "scc_rt_stacks" && blockAtB cells okL 7 stOk &&
  blockAtB cells takenL 0 stSite && labelGapB cells takenL siteL 11 &&
  blockAtB cells siteL 0 ((parse("nop")).zip [1]) && blockAtB cells siteL 1 stRet

#guard stackTakeIn SccCode.ret0Cells

/-- The code's check on `ret0Cells`. -/
theorem ret0_stackTakeIn : stackTakeIn SccCode.ret0Cells = true := by decide +kernel

end Spike.Lib.X64.Flow.Ret0.StackTake
