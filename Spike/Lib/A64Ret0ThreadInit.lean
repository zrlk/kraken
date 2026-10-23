/-
**`scc_rt_thread_init` in `ret0.w` on AArch64, block by block**: the walks
of the runtime's thread setup when `scc_rt_start` calls it with the TCB's
address `tcb`, the named entry and exit predicates of its segment (S3) and
the pcs of its stores into the TCB. The call of `scc_rt_stack_take` is the
composition's (`call_nd`, with `StackTake.Pre`/`Post`); so are the nodes at
the six stores.

    scc_rt_thread_init(tcb = x0):               frame of 48, x29/x30 at 32/40
      .0_entry: base = scc_rt_stack_take(16384)              (tiCall)
      .sp0:     limit = base + 4096, top = base + 16384      (tiSp)
                tcb[0] = tcb, tcb[8] = limit, tcb[16] = 0,
                tcb[24] = 0, tcb[32] = base, tcb[40] = top   (storePc 0 … 5)
                x0 = top; ret                                (tiRet)

- **The specification**: `Pre g tcb` at the entry (`sp`, `x29`, `x30` the
  ghosts `g`, `x0 = tcb`) and `Post g base` at `g.ra` (`x0 = base +
  16384`, the stack's top). The TCB's fields after the stores are
  `fields tcb base`; the limit (`Tcb.stackLimit = 8`) is `base + 4096`.
- **The frame** (`Fr0`, `Fr1`): the saved registers, the TCB's address and
  the stack's base, limit and top.
- **The walks**: each block's run from its frame predicate to the next,
  with the store operands (`x9` the value, `x10 = tcb`).
- **The code** (`threadInitIn`, `ret0_threadInitIn`): every block and store
  at its label and index in `ret0Prog`, decided by the kernel.
-/
import Spike.Lib.A64Ret0StackTake
import Scc.IR.Core

namespace Spike.Lib.A64.Flow.Ret0.ThreadInit

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- The offsets in the frame. -/
abbrev oI : SO := ⟨-48, []⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩

/-- The prologue: a frame of 48, `x29`/`x30` saved at 32/40, the TCB's address at 0. -/
def tiPro : List Directive := parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32
str x0, [sp]")

/-- The stack: `scc_rt_stack_take(16384)`. -/
def tiCall : List Directive := parseAArch64("movz x0, #16384
bl scc_rt_stack_take")

/-- The stack's base, limit (`base + 4096`) and top (`base + 16384`) saved; the first field's operands. -/
def tiSp : List Directive := parseAArch64("str x0, [sp, #8]
ldr x9, [sp, #8]
movz x10, #4096
add x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #8]
movz x10, #16384
add x9, x9, x10
str x9, [sp, #24]
ldr x9, [sp]
ldr x10, [sp]")

/-- The limit field's operands. -/
def tiF1 : List Directive := parseAArch64("ldr x9, [sp, #16]
ldr x10, [sp]")

/-- The third field's operands (`0`). -/
def tiF2 : List Directive := parseAArch64("movz x9, #0
ldr x10, [sp]")

/-- The fourth field's operands (`0`). -/
def tiF3 : List Directive := parseAArch64("movz x9, #0
ldr x10, [sp]")

/-- The base field's operands. -/
def tiF4 : List Directive := parseAArch64("ldr x9, [sp, #8]
ldr x10, [sp]")

/-- The top field's operands. -/
def tiF5 : List Directive := parseAArch64("ldr x9, [sp, #24]
ldr x10, [sp]")

/-- `x0` the top; the epilogue and the return. -/
def tiRet : List Directive := parseAArch64("ldr x0, [sp, #24]
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

block_spec tiPro (-48) 0 oE tiPro
block_spec tiCall (-48) 0 oI tiCall
block_spec tiSp (-48) 0 oI tiSp
block_spec tiF1 (-48) 0 oI tiF1
block_spec tiF2 (-48) 0 oI tiF2
block_spec tiF3 (-48) 0 oI tiF3
block_spec tiF4 (-48) 0 oI tiF4
block_spec tiF5 (-48) 0 oI tiF5
block_spec tiRet (-48) 0 oI tiRet

/-! ## The specification -/

/-- **The ghosts of a call**: `sp`, `x29` and `x30` at entry. -/
structure G where
  /-- `sp` at entry. -/
  sp : BitVec 64
  /-- `x29` at entry. -/
  fp : BitVec 64
  /-- The return address. -/
  ra : BitVec 64

-- The limit's field is the thread control block's (`Scc.IR.Tcb.stackLimit`).
#guard Scc.IR.Tcb.stackLimit = 8

/-- **Entry**: `sp`, `x29`, `x30` the ghosts', `x0 = tcb`. -/
def Pre (g : G) (tcb : BitVec 64) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧ σ.regs.X0.toBitVec = tcb

/-- **Exit** (at `g.ra`): `sp`, `x29`, `x30` restored, `x0` the stack's top. -/
def Post (g : G) (base : BitVec 64) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧
  σ.regs.X0.toBitVec = base + 16384#64

/-- **The TCB's fields after the stores**, by offset: itself, the limit,
two zeros, the stack's base and top. -/
def fields (tcb base : BitVec 64) : List (Nat × BitVec 64) :=
  [(0, tcb), (8, base + 4096#64), (16, 0#64), (24, 0#64), (32, base), (40, base + 16384#64)]

/-- **The pc of the store of field `i`** (`str x9, [x10, #8·i]`). -/
abbrev storePc (lab : Label → Int64) (i : Nat) : Int64 :=
  lab ".L5_scc_rt_thread_init.sp0" + Int64.ofNat (4 * (11 + 3 * i))

/-- The frame: `sp` down by 48, the saved `x29`/`x30` and the TCB's address. -/
def Fr0 (g : G) (tcb : BitVec 64) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp - 48#64 ∧ σ.slot (-16) = g.fp ∧ σ.slot (-8) = g.ra ∧ σ.slot (-48) = tcb

/-- The frame with the stack's base, limit and top. -/
def Fr1 (g : G) (tcb base : BitVec 64) (σ : AS) : Prop :=
  Fr0 g tcb σ ∧ σ.slot (-40) = base ∧ σ.slot (-32) = base + 4096#64 ∧ σ.slot (-24) = base + 16384#64

/-! ## The walks -/

/-- **The prologue**: from the entry to `.0_entry` (five instructions on). -/
theorem tiPro_walk (lab : Label → Int64) (pc : Int64) {g : G} {tcb : BitVec 64} {σ : AS} (h : Pre g tcb σ) :
    (arun lab tiPro ⟨pc, oE, σ⟩).pc = pc + Int64.ofNat (4 * 5) ∧
    (arun lab tiPro ⟨pc, oE, σ⟩).so = ⟨-48, [(.X29, -16)]⟩ ∧ Fr0 g tcb (arun lab tiPro ⟨pc, oE, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [tiPro_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4]

/-- **The call's argument**: `x0 = 16384`, the frame kept, to
`scc_rt_stack_take`. -/
theorem tiCall_walk (lab : Label → Int64) (pc : Int64) {g : G} {tcb : BitVec 64} {σ : AS} (h : Fr0 g tcb σ) :
    (arun lab tiCall ⟨pc, oI, σ⟩).pc = lab "scc_rt_stack_take" ∧
    Fr0 g tcb (arun lab tiCall ⟨pc, oI, σ⟩).σ ∧
    (arun lab tiCall ⟨pc, oI, σ⟩).σ.regs.X0.toBitVec = StackTake.size0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [tiCall_run]
  refine ⟨rfl, ?_⟩
  simp [Fr0, h1, h2, h3, h4]

/-- **The stack's base, limit and top** (the base in `x0`, the call's
result); the first field's operands `x9 = x10 = tcb`. -/
theorem tiSp_walk (lab : Label → Int64) (pc : Int64) {g : G} {tcb base : BitVec 64} {σ : AS} (h : Fr0 g tcb σ)
    (h0 : σ.regs.X0.toBitVec = base) :
    (arun lab tiSp ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 11) ∧
    (arun lab tiSp ⟨pc, oI, σ⟩).so = oI ∧ Fr1 g tcb base (arun lab tiSp ⟨pc, oI, σ⟩).σ ∧
    (arun lab tiSp ⟨pc, oI, σ⟩).σ.regs.X9.toBitVec = tcb ∧
    (arun lab tiSp ⟨pc, oI, σ⟩).σ.regs.X10.toBitVec = tcb := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [tiSp_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h0]

/-- **A field's operands**: `x9` the value, `x10 = tcb`, the frame kept. -/
abbrev FieldOps (b : List Directive) (v : BitVec 64 → BitVec 64 → BitVec 64) : Prop :=
  ∀ (lab : Label → Int64) (pc : Int64) {g : G} {tcb base : BitVec 64} {σ : AS}, Fr1 g tcb base σ →
    (arun lab b ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 2) ∧
    (arun lab b ⟨pc, oI, σ⟩).so = oI ∧ Fr1 g tcb base (arun lab b ⟨pc, oI, σ⟩).σ ∧
    (arun lab b ⟨pc, oI, σ⟩).σ.regs.X9.toBitVec = v tcb base ∧
    (arun lab b ⟨pc, oI, σ⟩).σ.regs.X10.toBitVec = tcb

/-- The limit field's operands: `base + 4096`. -/
theorem tiF1_walk : FieldOps tiF1 fun _ base => base + 4096#64 := by
  intro lab pc g tcb base σ h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩ := h
  rw [tiF1_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr1, Fr0, h1, h2, h3, h4, h5, h6, h7]

/-- The third field's operands: `0`. -/
theorem tiF2_walk : FieldOps tiF2 fun _ _ => 0#64 := by
  intro lab pc g tcb base σ h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩ := h
  rw [tiF2_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr1, Fr0, h1, h2, h3, h4, h5, h6, h7]

/-- The fourth field's operands: `0`. -/
theorem tiF3_walk : FieldOps tiF3 fun _ _ => 0#64 := by
  intro lab pc g tcb base σ h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩ := h
  rw [tiF3_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr1, Fr0, h1, h2, h3, h4, h5, h6, h7]

/-- The base field's operands: `base`. -/
theorem tiF4_walk : FieldOps tiF4 fun _ base => base := by
  intro lab pc g tcb base σ h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩ := h
  rw [tiF4_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr1, Fr0, h1, h2, h3, h4, h5, h6, h7]

/-- The top field's operands: `base + 16384`. -/
theorem tiF5_walk : FieldOps tiF5 fun _ base => base + 16384#64 := by
  intro lab pc g tcb base σ h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩ := h
  rw [tiF5_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr1, Fr0, h1, h2, h3, h4, h5, h6, h7]

/-- **The return**: to `g.ra` with `x0` the stack's top, the frame popped. -/
theorem tiRet_walk (lab : Label → Int64) (pc : Int64) {g : G} {tcb base : BitVec 64} {σ : AS}
    (h : Fr1 g tcb base σ) :
    (arun lab tiRet ⟨pc, oI, σ⟩).pc = Int64.ofBitVec g.ra ∧
    (arun lab tiRet ⟨pc, oI, σ⟩).so = oE ∧ Post g base (arun lab tiRet ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩ := h
  rw [tiRet_run]
  refine ⟨by rw [h3], rfl, ?_⟩
  simp [Post, h1, h2, h3, h7, BitVec.sub_add_cancel]

/-! ## The code -/

/-- `scc_rt_thread_init`'s label. -/
abbrev fnL : Label := "scc_rt_thread_init"
/-- Its entry label. -/
abbrev entryL : Label := ".L5_scc_rt_thread_init.0_entry"
/-- The label after the call. -/
abbrev spL : Label := ".L5_scc_rt_thread_init.sp0"

/-- **`scc_rt_thread_init`'s code in `prog`**: its blocks, its stores and
the fall-through into `.0_entry`. -/
def threadInitIn (prog : List Directive) : Bool :=
  labelGap prog fnL entryL 5 && blockAt prog fnL 0 tiPro && blockAt prog entryL 0 tiCall &&
  blockAt prog spL 0 tiSp && blockAt prog spL 11 (parseAArch64("str x9, [x10]")) &&
  blockAt prog spL 12 tiF1 && blockAt prog spL 14 (parseAArch64("str x9, [x10, #8]")) &&
  blockAt prog spL 15 tiF2 && blockAt prog spL 17 (parseAArch64("str x9, [x10, #16]")) &&
  blockAt prog spL 18 tiF3 && blockAt prog spL 20 (parseAArch64("str x9, [x10, #24]")) &&
  blockAt prog spL 21 tiF4 && blockAt prog spL 23 (parseAArch64("str x9, [x10, #32]")) &&
  blockAt prog spL 24 tiF5 && blockAt prog spL 26 (parseAArch64("str x9, [x10, #40]")) &&
  blockAt prog spL 27 tiRet

#guard threadInitIn SccCode.ret0Prog

/-- The code's check on `ret0Prog`. -/
theorem ret0_threadInitIn : threadInitIn SccCode.ret0Prog = true := by decide +kernel

end Spike.Lib.A64.Flow.Ret0.ThreadInit
