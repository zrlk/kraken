/-
**`scc_rt_thread_init` in `ret0.w` on x64, block by block**: the x64 twin
of `Spike/Lib/A64Ret0ThreadInit.lean`. The walks of the runtime's thread
setup when `scc_rt_start` calls it with the TCB's address `tcb`, the named
entry and exit predicates of its segment (S3) and the pcs of its stores
into the TCB. The call of `scc_rt_stack_take` is the composition's
(`call_nd`, with `StackTake.Pre`/`Post`; its return leaves the offsets of
`%rsp` alone, so the composition puts `%rbp`'s back from `StackTake.Post`);
so are the nodes at the six stores.

    scc_rt_thread_init(tcb = %rdi):             frame of 32 below %rbp
      .entry: base = scc_rt_stack_take(16384)                (tiArg, the call)
      .x7:    limit = base + 4096, top = base + 16384        (tiSp)
              tcb[0] = tcb, tcb[8] = limit, tcb[16] = 0,
              tcb[24] = 0, tcb[32] = base, tcb[40] = top     (storePc 0 … 5)
              %rax = top; ret                                (tiRet)

- **The specification**: `Pre g tcb` at the entry (`%rsp`, `%rbp` and the
  return address the ghosts `g`, `%rdi = tcb`) and `Post g base` at `g.ra`
  (`%rax = base + 16384`, the stack's top). The TCB's fields after the
  stores are `fields tcb base`; the limit (`Tcb.stackLimit = 8`) is
  `base + 4096`.
- **The frame** (`Fr g ss`): `%rsp` at the frame's base, `%rbp` at the
  saved `%rbp`, and the cells `ss` (`s0`, `s1`): the TCB's address and the
  stack's base, limit and top.
- **The walks**: each block's run from its frame to the next, with the
  store operands (`%rax` the value, `%rcx = tcb`; `FieldOps`).
- **The code** (`threadInitIn`, `ret0_threadInitIn`): every block, the
  call and the stores at their label and byte offset in `ret0Cells`,
  decided by the kernel.
-/
import Spike.Lib.X64Ret0StackTake
import Scc.IR.Core

namespace Spike.Lib.X64.Flow.Ret0.ThreadInit

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB)
open Spike.Lib.X64.Flow.Ret0.AllocTcb (G)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- The offsets in the frame: `%rsp` at the frame's base, `%rbp` at the saved `%rbp`. -/
abbrev oI : SO := ⟨-40, [(.rbp, -8)]⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩
/-- The offsets after the return. -/
abbrev oR : SO := ⟨8, []⟩

/-- The prologue: a frame of 32, the TCB's address at `-8(%rbp)`. -/
def tiPro : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 4, 4]

/-- The stack's size, `scc_rt_stack_take`'s argument. -/
def tiArg : List (Directive × Nat) := (parse("movq $16384, %rdi")).zip [7]

/-- The stack's base, limit (`base + 4096`) and top (`base + 16384`) saved; the first field's operands. -/
def tiSp : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $4096, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -16(%rbp), %rax
movq $16384, %rcx
addq %rcx, %rax
movq %rax, -32(%rbp)
movq -8(%rbp), %rcx
movq -8(%rbp), %rax")).zip [4, 4, 7, 3, 4, 4, 7, 3, 4, 4, 4]

/-- The limit field's operands. -/
def tiF1 : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx
movq -24(%rbp), %rax")).zip [4, 4]

/-- A zero field's operands (the third and the fourth). -/
def tiZ : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx
movq $0, %rax")).zip [4, 7]

/-- The base field's operands. -/
def tiF4 : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx
movq -16(%rbp), %rax")).zip [4, 4]

/-- The top field's operands. -/
def tiF5 : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx
movq -32(%rbp), %rax")).zip [4, 4]

/-- `%rax` the top; the epilogue and the return. -/
def tiRet : List (Directive × Nat) := (parse("movq -32(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]

block_spec tiPro (-40) 8 oE tiPro
block_spec tiArg (-40) 8 oI tiArg
block_spec tiSp (-40) 8 oI tiSp
block_spec tiF1 (-40) 8 oI tiF1
block_spec tiZ (-40) 8 oI tiZ
block_spec tiF4 (-40) 8 oI tiF4
block_spec tiF5 (-40) 8 oI tiF5
block_spec tiRet (-40) 8 oI tiRet

/-! ## The specification -/

-- The limit's field is the thread control block's (`Scc.IR.Tcb.stackLimit`).
#guard Scc.IR.Tcb.stackLimit = 8

/-- **Entry**: `%rsp`, `%rbp`, the return address the ghosts', `%rdi = tcb`. -/
def Pre (g : G) (tcb : BitVec 64) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.slot 0 = g.ra ∧ σ.regs.rdi.toBitVec = tcb

/-- **Exit** (at `g.ra`): `%rsp` past the return address, `%rbp` restored,
`%rax` the stack's top. -/
def Post (g : G) (base : BitVec 64) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp + 8#64 ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.regs.rax.toBitVec = base + 16384#64

/-- **The TCB's fields after the stores**, by offset: itself, the limit,
two zeros, the stack's base and top. -/
def fields (tcb base : BitVec 64) : List (Nat × BitVec 64) :=
  [(0, tcb), (8, base + 4096#64), (16, 0#64), (24, 0#64), (32, base), (40, base + 16384#64)]

/-- The stores' byte offsets after `.x7`. -/
def storeOff : List Nat := [48, 59, 74, 89, 101, 113]

/-- **The pc of the store of field `i`** (`movq %rax, 8·i(%rcx)`). -/
abbrev storePc (lab : Label → Int64) (i : Nat) : Int64 :=
  lab ".Lscc_rt_thread_init.x7" + Int64.ofNat (storeOff.getD i 0)

/-- **The frame**: `%rsp` at the frame's base, `%rbp` at the saved `%rbp`,
the cells `ss` (offsets from the entry's `%rsp`). -/
def Fr (g : G) (ss : List (Int × BitVec 64)) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp - 40#64 ∧ σ.regs.rbp.toBitVec = g.sp - 8#64 ∧ ∀ p ∈ ss, σ.slot p.1 = p.2

/-- The return address, the saved `%rbp` and the TCB's address. -/
abbrev s0 (g : G) (tcb : BitVec 64) : List (Int × BitVec 64) := [(0, g.ra), (-8, g.fp), (-16, tcb)]
/-- With the stack's base, limit and top. -/
abbrev s1 (g : G) (tcb base : BitVec 64) : List (Int × BitVec 64) :=
  (-24, base) :: (-32, base + 4096#64) :: (-40, base + 16384#64) :: s0 g tcb

/-! ## The walks -/

/-- Unfolds a frame hypothesis. -/
local macro "frh" h:ident : tactic =>
  `(tactic| simp only [Fr, List.forall_mem_cons, List.forall_mem_nil] at $h:ident)

/-- Closes a walk's goal from the run's normal form. -/
local macro "walk" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Fr, Post, Reg64s.set64, Reg64s.get64, upd_apply, $ts,*])

/-- **The prologue**: from the entry to `.entry`, the frame set up. -/
theorem tiPro_walk (lab : String → Int64) (pc : Int64) {g : G} {tcb : BitVec 64} {σ : AS} (h : Pre g tcb σ) :
    (arun lab tiPro ⟨pc, oE, σ⟩).pc = pc + Int64.ofNat 12 ∧
    (arun lab tiPro ⟨pc, oE, σ⟩).so = oI ∧ Fr g (s0 g tcb) (arun lab tiPro ⟨pc, oE, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [tiPro_run]
  refine ⟨rfl, rfl, ?_⟩
  walk [h1, h2, h3, h4]
  bv_omega

/-- **The call's argument**: `%rdi = 16384` (`StackTake.size0`). -/
theorem tiArg_walk (lab : String → Int64) (pc : Int64) {g : G} {tcb : BitVec 64} {σ : AS}
    (h : Fr g (s0 g tcb) σ) :
    (arun lab tiArg ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 7 ∧
    (arun lab tiArg ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s0 g tcb) (arun lab tiArg ⟨pc, oI, σ⟩).σ ∧
    (arun lab tiArg ⟨pc, oI, σ⟩).σ.regs.rdi.toBitVec = StackTake.size0 := by
  frh h
  rw [tiArg_run]
  walk [h]

/-- **The stack's limit and top** from its base (in `%rax`, the call's
result); the first field's operands: `%rax = %rcx = tcb`. -/
theorem tiSp_walk (lab : String → Int64) (pc : Int64) {g : G} {tcb base : BitVec 64} {σ : AS}
    (h : Fr g (s0 g tcb) σ) (ha : σ.regs.rax.toBitVec = base) :
    (arun lab tiSp ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 48 ∧
    (arun lab tiSp ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s1 g tcb base) (arun lab tiSp ⟨pc, oI, σ⟩).σ ∧
    (arun lab tiSp ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = tcb ∧
    (arun lab tiSp ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = tcb := by
  frh h
  rw [tiSp_run]
  walk [h, ha]
  exact ⟨BitVec.add_comm _ _, BitVec.add_comm _ _⟩

/-- **A field's operands**: `%rax` the value, `%rcx = tcb`, the frame kept,
`z` bytes. -/
abbrev FieldOps (b : List (Directive × Nat)) (z : Nat) (v : BitVec 64 → BitVec 64 → BitVec 64) : Prop :=
  ∀ (lab : String → Int64) (pc : Int64) {g : G} {tcb base : BitVec 64} {σ : AS}, Fr g (s1 g tcb base) σ →
    (arun lab b ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat z ∧
    (arun lab b ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s1 g tcb base) (arun lab b ⟨pc, oI, σ⟩).σ ∧
    (arun lab b ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = v tcb base ∧
    (arun lab b ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = tcb

/-- The limit field's operands: `base + 4096`. -/
theorem tiF1_walk : FieldOps tiF1 8 fun _ base => base + 4096#64 := by
  intro lab pc g tcb base σ h
  frh h
  rw [tiF1_run]
  walk [h]

/-- A zero field's operands: `0`. -/
theorem tiZ_walk : FieldOps tiZ 11 fun _ _ => 0#64 := by
  intro lab pc g tcb base σ h
  frh h
  rw [tiZ_run]
  walk [h]

/-- The base field's operands: `base`. -/
theorem tiF4_walk : FieldOps tiF4 8 fun _ base => base := by
  intro lab pc g tcb base σ h
  frh h
  rw [tiF4_run]
  walk [h]

/-- The top field's operands: `base + 16384`. -/
theorem tiF5_walk : FieldOps tiF5 8 fun _ base => base + 16384#64 := by
  intro lab pc g tcb base σ h
  frh h
  rw [tiF5_run]
  walk [h]

/-- **The return**: to `g.ra` with `%rax` the stack's top, the frame popped. -/
theorem tiRet_walk (lab : String → Int64) (pc : Int64) {g : G} {tcb base : BitVec 64} {σ : AS}
    (h : Fr g (s1 g tcb base) σ) :
    (arun lab tiRet ⟨pc, oI, σ⟩).pc = Int64.ofBitVec g.ra ∧
    (arun lab tiRet ⟨pc, oI, σ⟩).so = oR ∧ Post g base (arun lab tiRet ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [tiRet_run]
  walk [h]

/-! ## The code -/

/-- `scc_rt_thread_init`'s label. -/
abbrev fnL : Label := "scc_rt_thread_init"
/-- Its entry label. -/
abbrev entryL : Label := ".Lscc_rt_thread_init.entry"
/-- The label after the call. -/
abbrev x7L : Label := ".Lscc_rt_thread_init.x7"

/-- The call `call scc_rt_stack_take`. -/
def callBlk : List (Directive × Nat) := (parse("call scc_rt_stack_take")).zip [5]

/-- The field stores `movq %rax, 8·i(%rcx)`. -/
def storeBlks : List (List (Directive × Nat)) :=
  [(parse("movq %rax, (%rcx)")).zip [3], (parse("movq %rax, 8(%rcx)")).zip [4],
   (parse("movq %rax, 16(%rcx)")).zip [4], (parse("movq %rax, 24(%rcx)")).zip [4],
   (parse("movq %rax, 32(%rcx)")).zip [4], (parse("movq %rax, 40(%rcx)")).zip [4]]

/-- **`scc_rt_thread_init`'s code in `cells`**: its blocks, the call, the
stores and the fall-throughs into `.entry` and `.x7`. -/
def threadInitIn (cells : List (Directive × Nat)) : Bool :=
  labelGapB cells fnL entryL 12 && blockAtB cells fnL 0 tiPro && blockAtB cells entryL 0 tiArg &&
  blockAtB cells entryL 7 callBlk && labelGapB cells entryL x7L 12 &&
  blockAtB cells x7L 0 tiSp && blockAtB cells x7L 51 tiF1 && blockAtB cells x7L 63 tiZ &&
  blockAtB cells x7L 78 tiZ && blockAtB cells x7L 93 tiF4 && blockAtB cells x7L 105 tiF5 &&
  blockAtB cells x7L 117 tiRet &&
  (storeOff.zip storeBlks).all fun (o, b) => blockAtB cells x7L o b

#guard threadInitIn SccCode.ret0Cells

/-- The code's check on `ret0Cells`. -/
theorem ret0_threadInitIn : threadInitIn SccCode.ret0Cells = true := by decide +kernel

end Spike.Lib.X64.Flow.Ret0.ThreadInit
