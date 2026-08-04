/-
Kraken - Example Programs

This demonstrates our proof style using the `kstep` stepping tactic that
advances through ASM instructions. This is a work in progress, and is the result
of several experiments, which can be found in the Git history at revision
a556993a and earlier.

For semantics, see Kraken/Semantics.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Kraken.X64.Tactics
import Kraken.X64.Parser
import Kraken.Eval
import Kraken.X64.Sep

open Kraken.X64.Parser

--------------------------------------------------------------------------------

def p1 := parse("start: mov $1, %rax")

-- Super-simple example to debug tactics
example [layout : Layout] s : straightlineStep (layout p1) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  kprologue p1
  sym => kstep; tactic =>
  decide
  /- simp [Instr.interp,Operation.interp,Operand.interp,MachineData.set] -/
  /- simp [MachineData.setReg,Reg64s.set,Reg64s.set64,ConstExpr.interp] -/
  /- simp [Width.bits] -/
  /- simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,eval_imm,set_reg_or_mem,next,MachineState.setReg,Registers.set] -/

def swap : Program := parse("
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax")

theorem swap_correct [layout : Layout] (d : MachineData) :
      Eventually (straightlineStep (layout swap))
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, layout.start) := by
  apply step_cps
  kprologue swap
  sym => kstep; tactic =>
  apply Eventually.done
  grind

-- Stepping demo. Ideally, this demo should be without the first .mov
def p2 : Program := parse("
start:
  mov $1, %rax
  xor %rax, %rax
  jnz start
  mov $2, %rax")

-- Example 2: stepping through both straightline and control instructions
example [layout : Layout] (s : MachineData): Eventually (straightlineStep (layout p2)) (fun s => s.1.regs.rax = 2) (s, layout.start) := by
  apply step_cps
  kprologue p2
  sym =>
  kstep
  tactic =>
  -- TODO: would be nice to have these simp steps be part of kstep
  rename_i v v1 status
  have: v = 0 := by grind
  simp [this]
  sym =>
  kstep
  tactic =>
  apply Eventually.done
  bv_decide

-- Example 3, more sophisticated

-- TODO: restore p3

def p3: Program := parse("
init:
  mov $2, %rdx             # rdx: current result = 2
start:
  sub $0, %rbx             # TEST: zf = (rbx == 0)
  jz _end                 # end loop if rbx == 0 (a.k.a. « while rbx >= 0 »)
  mulx %rdx, %rdx, %rax    # BODY: rdx := rdx * rdx
  sub $1, %rbx              # rbx -= 1
  jmp start               # go back to test & loop body
_end:
  nop
")

def p3_spec (s: MachineData): Nat := 2^(2^s.regs.rbx.toNat)

set_option maxHeartbeats 4000000 in
theorem p3_correct [layout: Layout] (s: MachineData):
    p3_spec s < 2^64 →
    Eventually (straightlineStep (layout p3)) (fun s => s.1.regs.rdx.toNat = p3_spec s.1 ∧ s.1.regs.rax = 0) (s, layout.start) :=
  by
    intros h_bounds
    apply step_cps
    kprologue p3

    sym =>
    -- kstep 3
    -- tactic =>
    -- apply reg_dec_loop
    -- intros

    sorry

/-     intros h_bounds h_rip
    simp [p3]
    -- First step sets rdx = 2
    apply step_cps
    step_one
    rw [h_rip]
    clear h_rip
    simp
    -- Loop invariant introduction
    apply reg_dec_loop p3 _ _ (fun i s => s.rip = 1 ∧ s.regs.rbx.toNat = i ∧ i ≤ initial.regs.rbx.toNat ∧ s.regs.rdx.toNat = 2^(2^(initial.regs.rbx.toNat - i))) initial.regs.rbx.toNat
    constructor
    . simp
    . constructor
      -- Invariant at index 0 ==> post
      . intros state inv
        rcases inv with ⟨ h_rip, h_rbx_zero, h_rbx_le, h_inv ⟩
        -- Step through a few program steps
        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp
        apply step_cps
        step_one
        have : state.regs.rbx.toNat = 0 := by grind
        simp [this]
        apply step_cps
        step_one
        apply eventually.done
        simp
        -- Now functional correctness for initial invariant
        simp [p3_spec]
        grind
      -- Invariant preserved
      . intro state k h_k_nonzero inv
        rcases inv with ⟨ h_rip, h_rbx_is_k, h_rbx_le, h_inv ⟩
        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp
        apply step_cps
        step_one
        have h_k_ne : k ≠ 0 := by grind
        -- state.regs.rbx.toNat = k and toNat < 2^64 for UInt64
        have h_k_lt : k < 2^64 := h_rbx_is_k ▸ (state.regs.rbx.toNat_lt)
        -- Simplify all the Int64.toUInt64 terms
        simp_all only [ne_eq, not_false_eq_true]
        -- Prove the if-condition is false: UInt64.ofInt ↑k ≠ 0 when k ≠ 0
        have h_cond : UInt64.ofInt (k : Int) ≠ 0 := UInt64_ofInt_natCast_ne_zero k h_k_lt h_k_ne
        rw [if_neg h_cond]
        apply step_cps
        step_one
        apply step_cps
        step_one
        apply step_cps
        step_one
        apply eventually.done
        -- Goals for invariant preservation
        constructor
        . simp -- back to correct address
        . match h_state:state.regs.rbx, h_init:initial.regs.rbx with
          | ⟨v_s⟩, ⟨v_i⟩ =>
            have h_k_lt : k < 2^64 := h_rbx_is_k ▸ (by rw [h_state]; exact v_s.isLt)
            have h_init_lt : v_i.toNat < 2^64 := v_i.isLt
            simp [h_state, h_init, p3_spec, Reg.width, UInt64.ofInt, UInt64.ofNat, UInt64.toNat_ofNat] at *
            constructor
            . omega
            . constructor
              . omega
              . rw [h_inv]
                have h_vi_k : v_i.toNat - (k - 1) = (v_i.toNat - k) + 1 := by omega
                rw [h_vi_k, Nat.mod_eq_of_lt]
                . rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
                . apply Nat.lt_of_le_of_lt _ h_bounds
                  rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
                  apply Nat.pow_le_pow_right (by decide)
                  apply Nat.pow_le_pow_right (by decide)
                  omega -/

def p4 := eval% parse("start: mov $2, %rax
dec %rax")

-- Super-simple example to debug tactics
example [layout : Layout] s : straightlineStep (layout p4) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  let ss := s
  change (straightlineStep _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax =>
  kprologue p4
  sym =>
  kstep
  -- intros
  tactic =>
  decide

/- Examples -/

def p5 := parse("start: mov $2, %rax
dec %rax
start2:
dec %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.all true -/

example [layout : Layout] s : straightlineStep (layout p5) (s, layout.start) (fun s => s.1.regs.rax = 0) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  let ss := s
  change (straightlineStep _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax =>
  kprologue p5
  sym => kstep; tactic =>
  bv_decide

def p6 := parse("push %rax
mov $0, %rax
pop %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.coercions false -/
/- set_option pp.all true -/

attribute [ksimp]
  BitVec.add_zero
  BitVec.ofInt_add
  BitVec.ofInt_ofNat
  BitVec.ofInt_toInt
  BitVec.ofNat_uInt64ToNat
  BitVec.reduceOfInt
  BitVec.setWidth_eq
  Int.add_zero
  Int.reduceBmod
  Int.reduceNeg
  Int64.reduceToInt
  Int64.toInt_neg
  Nat.reducePow
  Nat.shiftRight_zero
  Nat.sub_zero
  UInt64.ofBitVec_add
  UInt64.ofBitVec_ofNat
  UInt64.ofBitVec_sub
  UInt64.ofBitVec_toBitVec
  UInt64.sub_add_cancel
  UInt64.toBitVec_ofNat
  UInt64.toBitVec_sub
  UInt64.toNat_toBitVec

theorem p6_correct [layout : Layout] (s₀ : MachineData)
    (stack : List UInt8) (h_len : stack.length = 8) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 8#64)) ⋆ R) :
    Eventually (straightlineStep (layout p6))
      (fun s' => s'.1.regs.rax = s₀.regs.rax ∧ s'.1.regs.rsp = s₀.regs.rsp)
      (s₀, layout.start) := by
  apply step_cps
  let ss := s₀
  change (straightlineStep _ (ss, _) _)
  cases s₀ with | mk regs zmms flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  have h_bs : stack.length = 8 := h_len
  kprologue p6
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 stack R mem ⟨h_mem, h_bs⟩ rax.toBitVec.toInt
  sym =>
  kstep
  tactic =>
  apply Eventually.done
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  bv_decide

-- def bigp := parseFile("./ecc-secp521r1-modp.S")

/- set_option maxRecDepth 4000 -/
/- set_option maxHeartbeats 2000000 -/

-- example [layout : Layout] s
--   (hAlign: s.regs.rsp % 8 = 0)
--   (hContains: forall x, x ∈ s.dmem)
-- : straightlineStep (layout bigp) (s, layout.start) (fun s => s.1.regs.rax = 0) := by
--   -- Refine the state to make registers apparent -- note that `cases` consumes
--   -- the hypothesis, and substitutes it, so we make a copy of it to have a
--   -- refined state in the hypotheses, not the goal.
--   let ss := s
--   change (straightlineStep _ (ss, _) _)
--   cases s with | mk regs flags mem =>
--   cases regs with | mk rax =>
--   -- Rewrite the program to make layout, addresses, etc. apparent
--   delta bigp
--   dsimp only [straightlineStep,Executable.straightline]
--   rw [Executable.directivesFromStart]
--   simp [List.mapIdx,List.mapIdx.go]
--   sym =>
--   kstep
--   done


open Std
open Std.ExtHashMap

theorem BitVec.take_all {w : Nat} (x : BitVec w) : x.take w = x := by
  simp [BitVec.take]

def move_2_regs_to_heap := parse("
    movq %rax, (%rdi)
    movq %rcx, 8(%rdi)
    movq (%rdi), %r12
    movq 8(%rdi), %r13
")

theorem move_2_regs_to_heap_correct [layout : Layout] (s₀ : MachineData)
  (v1 v2 : UInt64)
  (R : DataMem → Prop)
  (h_mem : s₀.dmem =⋆ Eq (v1.At s₀.regs.rdi.toBitVec) ⋆ Eq (v2.At (s₀.regs.rdi.toBitVec + 8#64)) ⋆ R)
  : Eventually (straightlineStep (layout move_2_regs_to_heap))
      (fun s' =>
        s'.1.regs.r12 = s₀.regs.rax ∧
        s'.1.regs.r13 = s₀.regs.rcx ∧
        s'.1.regs.rdi = s₀.regs.rdi)
      (s₀, layout.start) := by
  apply step_cps
  cases s₀ with | mk regs zmms flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  kprologue move_2_regs_to_heap

  have h_bs1 : v1.toBytes.length = 8 := UInt64.toBytes_length v1
  have h_bs2 : v2.toBytes.length = 8 := UInt64.toBytes_length v2
  rw [sep_assoc] at h_mem
  have h_mem1 := Mem.storeInt_sep rdi.toBitVec 8 v1.toBytes (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆ R) mem ⟨h_mem, h_bs1⟩ rax.toBitVec.toInt
  have h_mem1' : (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆ (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem1
  have h_mem2 := Mem.storeInt_sep (rdi.toBitVec + 8#64) 8 v2.toBytes _ _ ⟨h_mem1', h_bs2⟩ rcx.toBitVec.toInt
  have h_mem2' : (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi) ⋆ (Eq ((Int.toBytes 8 rcx.toBitVec.toInt).At (rdi.toBitVec + 8#64)) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem2
  have h_mem2'' : (Eq ((Int.toBytes 8 rcx.toBitVec.toInt).At (rdi.toBitVec + 8#64)) ⋆ (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi.toBitVec) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem2'
  simp at h_mem
  sym =>
  -- TODO: these would be prime examples for cancellation!
  -- TODO: the kstep tactic is supposed to apply `exact`, but `exact` only applies after `simp`, so
  -- clearly, stuff is missing from the simp-set in `kstep`
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs1
  kstep
  case h_mem => tactic => simp; exact h_mem1'
  case h_len => exact h_bs2
  kstep
  case h_mem => tactic => simp; exact h_mem2'
  case h_len => tactic => rfl
  kstep
  case h_mem => tactic => simp; exact h_mem2''
  case h_len => tactic => rfl
  kstep
  tactic =>
  apply Eventually.done
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  exact ⟨rfl, rfl, rfl⟩

def sib_example := parse("
    movq $42, %rax
    movq %rax, (%rdi, %r15, 8)
    movq $0, %rax
    movq (%rdi, %r15, 8), %rax
")

-- FIXME: I had to replace `s₀.regs.r15.toBitVec * 8#64` with `BitVec.ofInt 64
-- (s₀.regs.r15.toBitVec.toInt * 8)` to make the example go through. Why?
theorem sib_example_correct [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdi.toBitVec + BitVec.ofInt 64 (s₀.regs.r15.toBitVec.toInt * 8))) ⋆ R) :
    Eventually (straightlineStep (layout sib_example))
      (fun s' => s'.1.regs.rax = 42)
      (s₀, layout.start) := by
  apply step_cps
  cases s₀ with | mk regs zmms flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  kprologue sib_example
  simp at h_mem
  have h_mem' := Mem.storeInt_sep (rdi.toBitVec + BitVec.ofInt 64 (r15.toBitVec.toInt * 8)) 8 v.toBytes R mem ⟨h_mem, h_bs⟩ 42
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  case h_mem => tactic => simp; exact h_mem'
  case h_len => exact by decide
  kstep
  tactic =>
  apply Eventually.done
  rfl

def alu_mem_example := parse("
    movq $42, %rax
    movq %rax, 136(%rdx)
    movq $100, %rcx
    addq 136(%rdx), %rcx
")

theorem alu_mem_example_correct [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdx.toBitVec + 136#64)) ⋆ R) :
    Eventually (straightlineStep (layout alu_mem_example))
      (fun s' => s'.1.regs.rcx = 142)
      (s₀, layout.start) := by
  apply step_cps
  cases s₀ with | mk regs zmms flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  kprologue alu_mem_example
  have h_mem1 := Mem.storeInt_sep (rdx.toBitVec + 136#64) 8 v.toBytes R mem ⟨h_mem, h_bs⟩ 42
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  case h_mem => tactic => simp; exact h_mem1
  case h_len => exact Int.toBytes_length 8 _
  kstep
  tactic =>
  apply Eventually.done
  dsimp [UInt64.toBitVec]
  change (100 : UInt64) + { toBitVec := BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (42#64).toInt)) } = (142 : UInt64)
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  rfl

def dynamic_stack_example := parse("
    movq $99, -8(%rsp)
    movq %rsp, %rbp
    leaq -1024(%rsp, %r9, 8), %rsp
    movq $42, %rax
    movq %rax, 16(%rsp, %r15, 8)
    movq $0, %rax
    movq 16(%rsp, %r15, 8), %rax
    movq %rbp, %rsp
    movq -8(%rsp), %rbx
")

theorem dynamic_stack_example_correct [layout : Layout] (s₀ : MachineData)
    (stack : List UInt8) (lstack : stack.length = 1024) R
    (h : s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 1024)) ⋆ R) :
    Eventually (straightlineStep (layout dynamic_stack_example))
      (fun s' => s'.1.regs.rax = 42 ∧ s'.1.regs.rbx = 99 ∧ s'.1.regs.rsp = s₀.regs.rsp)
      (s₀, layout.start) := by
  apply step_cps
  let ss := s₀
  change (straightlineStep _ (ss, _) _)
  cases s₀ with | mk regs zmms flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  have h_bs : stack.length = 1024 := lstack
  have h_take_drop : stack = stack.take 1016 ++ stack.drop 1016 := by exact (List.take_append_drop 1016 stack).symm
  rw [h_take_drop] at h_mem
  have h_len_take : (stack.take 1016).length = 1016 := by
    rw [List.length_take]
    rw [h_bs]
    rfl
  have h_len_drop : (stack.drop 1016).length = 8 := by
    rw [List.length_drop]
    rw [h_bs]
  have h_At_append := Mem.At_append_sep (w := 64) (stack.take 1016) (stack.drop 1016) (rsp.toBitVec - 1024#64) (by
    rw [h_len_take, h_len_drop]
    decide)
  change (Eq ((stack.take 1016 ++ stack.drop 1016).At (rsp.toBitVec - 1024#64)) ⋆ R) mem at h_mem
  rw [h_At_append] at h_mem
  rw [sep_assoc] at h_mem
  kprologue dynamic_stack_example
  have h_addr_eq : rsp.toBitVec - 1024#64 + BitVec.ofNat 64 (stack.take 1016).length = rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8) := by
    rw [h_len_take]
    change rsp.toBitVec - 1024#64 + 1016#64 = rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8)
    bv_decide
  rw [h_addr_eq] at h_mem
  replace h_mem : (Eq ((stack.drop 1016).At (rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8))) ⋆ (Eq ((stack.take 1016).At (rsp.toBitVec - 1024#64)) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8)) 8 (stack.drop 1016) (Eq ((stack.take 1016).At (rsp.toBitVec - 1024#64)) ⋆ R) mem ⟨h_mem, h_len_drop⟩ 99

  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_len_drop
  sorry
  -- kstep
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- -- FIXME: kstep here takes too long
  -- done


-- 1. Parse the assembly into the Kraken AST
def butterflies_float_prog := parse("
    shl $2, %edx
    add %rdx, %rdi
    add %rdx, %rsi
    neg %rdx
loop:
    movaps (%rdi,%rdx,1), %xmm0
    movaps (%rsi,%rdx,1), %xmm1
    movaps %xmm0, %xmm2
    subps %xmm1, %xmm2
    addps %xmm1, %xmm0
    movaps %xmm2, (%rsi,%rdx,1)
    movaps %xmm0, (%rdi,%rdx,1)
    add $16, %rdx
    jl loop
")

def butterflies_float_end_pc [layout : Layout] : Int64 :=
  let exe := layout butterflies_float_prog
  match exe.withAddresses.getLast? with
  | some (pc, _, sz) => pc + Int64.ofNat sz
  | none => 0  -- Fallback (unreachable since the program is non-empty)

-- k counts the number of iterations left
def butterflies_float_invariant (s₀ : MachineData) (bytes_len : Nat) (R : DataMem → Prop) [layout : Layout]
    (k : Nat) (s : MachineState) : Prop :=
  ∃ (mem1_curr mem2_curr : List UInt8),
    mem1_curr.length = bytes_len ∧
    mem2_curr.length = bytes_len ∧
    k * 16 ≤ bytes_len ∧
    -- r: Memory split guarantees disjointness and safety
    (s.1.dmem =⋆ Eq (mem1_curr.At s₀.regs.rdi.toBitVec) ⋆ Eq (mem2_curr.At s₀.regs.rsi.toBitVec) ⋆ R) ∧
    -- r: Pointer registers point to the end of the arrays
    s.1.regs.get Reg.rdi = s₀.regs.rdi.toBitVec + BitVec.ofNat 64 bytes_len ∧
    s.1.regs.get Reg.rsi = s₀.regs.rsi.toBitVec + BitVec.ofNat 64 bytes_len ∧
    -- r: Loop offset tracking (negative offset)
    s.1.regs.get Reg.rdx = - BitVec.ofNat 64 (k * 16) ∧
    -- r: Program counter sits exactly at the loop entry label
    -- the robot initially computed this to be 12 based on actual insn encodings?
    -- changed to a lookup on its suggestion
    -- then it later wanted to know the length of the program in encoded insns
    -- r: Dynamic PC check
    s.2 = if k = 0 then
            butterflies_float_end_pc
          else
            ((layout butterflies_float_prog).labels.label "loop")

def Executable.LabelIsFirstAtAddress (e : Executable) (l : Label) : Prop :=
  e.withAddresses.dropWhile (fun x => x.1 ≠ e.labels.label l) =
  e.withAddresses.dropWhile (fun x => x.2.1 != .label l)

theorem Executable.map_dropWhile_withAddresses (ds : List (Directive × Nat)) (a : Int64) (l : Label) :
    ((Executable.withAddresses (a, ds)).dropWhile (fun x => x.2.1 != .label l)).map (·.2) =
    ds.dropWhile (fun x => x.1 != .label l) := by
  induction ds generalizing a with
  | nil =>
    unfold Executable.withAddresses
    rfl
  | cons d ds ih =>
    unfold Executable.withAddresses
    simp only [List.dropWhile]
    split
    next h =>
      exact ih _
    next h =>
      simp only [h, List.map]
      rw [Executable.withAddresses_map_snd]

theorem directivesFromAddress_label [layout : Layout] (prog : Program) (l : Label)
    (h_wf : (layout prog).LabelIsFirstAtAddress l) :
    (layout prog).directivesFromAddress ((layout prog).labels.label l) =
      (layout prog).directivesFromLabel l := by
  dsimp [Executable.LabelIsFirstAtAddress, Executable.directivesFromAddress, Executable.directivesFromLabel] at *
  rw [h_wf]
  exact Executable.map_dropWhile_withAddresses (layout prog).2 (layout prog).1 l

-- The robot warns against 'pathological layouts' that assign 0 sizes to all insns.
-- istr something about `nop` possibly being given a 0 length (not sure what context
-- this makes sense in)

/-
a stubbed-out avx insn looks like this:
        -- movaps xmm1, XMMWORD PTR [rsi+rdx*1+0]
        kstep 1
        case h_mem => sorry
        case h_len => sorry
        case h_align => sorry
        case R => sorry   -- h_mem will provide this
        case bs => sorry  -- h_mem or h_align(?) will provide this
-/

theorem h_empty_sep : ∀ (P : ExtHashMap (BitVec 64) UInt8 → Prop) addr,
  (Eq ([].At addr) ⋆ P) = P := by
  intro P addr
  funext m
  apply propext; constructor
  · rintro ⟨a, b, h_union, h_inter, h_a, h_P⟩
    subst h_a
    have h_ub : ExtHashMap.union ([].At addr) b = b := by
      apply ExtHashMap.ext_getElem?; intro k
      have h_none : ([].At addr)[k]? = none := by
        apply ExtHashMap.getElem?_eq_none
        intro h_mem
        rw [mem_At_iff] at h_mem
        rcases h_mem with ⟨i, hi, _⟩
        change i < 0 at hi
        omega
      simp only [ExtHashMap.union_eq]
      rw [ExtHashMap.getElem?_union, h_none]
      -- Force evaluation of Option.or by destructing b[k]?
      cases b[k]? <;> rfl
    rw [h_ub] at h_union
    rw [← h_union]
    exact h_P
  · intro h_P
    refine ⟨[].At addr, m, ?_, ?_, rfl, h_P⟩
    · apply ExtHashMap.ext_getElem?; intro k
      have h_none : ([].At addr)[k]? = none := by
        apply ExtHashMap.getElem?_eq_none
        intro h_mem
        rw [mem_At_iff] at h_mem
        rcases h_mem with ⟨i, hi, _⟩
        change i < 0 at hi
        omega
      simp only [ExtHashMap.union_eq]
      rw [ExtHashMap.getElem?_union, h_none]
      -- Same here for m[k]?
      cases m[k]? <;> rfl
    · rw [eq_empty_iff_forall_not_mem]
      intro k h_mem
      -- Unfold `inter` first, then apply the intersection iff lemma
      rw [ExtHashMap.inter_eq, ExtHashMap.mem_inter_iff] at h_mem
      rcases h_mem with ⟨h_At, _⟩
      -- Now rewrite the At array membership
      rw [mem_At_iff] at h_At
      rcases h_At with ⟨i, hi, _⟩
      -- Prove i < 0 is impossible
      change i < 0 at hi
      omega

-- We only need the core BitVec module which is built-in
open BitVec

theorem h_neg_eq_aux (k : Nat) (hk : 0 < k) :
    -BitVec.ofNat 64 ((k - 1) * 16) = -BitVec.ofInt 64 ((↑k - 1) * 16) := by
  -- 1. Destructure k to eliminate the Nat subtraction truncation
  cases k with
  | zero =>
    -- 0 < 0 is a contradiction
    contradiction
  | succ k' =>
    -- Since k = k' + 1, (k - 1) simplifies definitionally to k'.
    -- We show that the RHS cast algebra also simplifies to k':
    have h_int : ((k' + 1 : Nat) : Int) - 1 = (k' : Int) := by omega

    -- Rewrite the integer subtraction on the RHS
    rw [h_int]

    -- The goal is now: -BitVec.ofNat 64 (k' * 16) = -BitVec.ofInt 64 (↑k' * 16)
    -- 2. Strip the negation using congrArg
    apply congrArg

    -- 3. Show the two BitVecs have the same underlying value (toNat)
    apply BitVec.eq_of_toNat_eq

    -- 4. Simplify using core BitVec theorems and let omega finish the arithmetic
    simp [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega

theorem butterflies_float_terminates_and_safe [layout : Layout]
  (s₀ : MachineData)
  (v1 v2 : List UInt8)
  (len : Nat)

  -- Preconditions on the length parameter
  (h_len_reg   : s₀.regs.get (Reg.low .rdx .W32) = BitVec.ofNat 32 len) -- len is passed in %edx
  (h_len_mod   : len % 4 = 0)                                           -- len is a multiple of 4
  (h_len_bound : len * 4 < 2^31)                                        -- prevent signed 32-bit overflow when multiplying by 4 bytes
  (h_len_gt    : len > 0)
  -- len mod 16 is 0

  -- Preconditions on the memory arrays
  (h_v1_len : v1.length = len * 4)
  (h_v2_len : v2.length = len * 4)

  -- Arrays are aligned.
  (h_v1_aligned : isAligned 16 s₀.regs.rdi)
  (h_v2_aligned : isAligned 16 s₀.regs.rsi)

  -- Separation Logic: v1 and v2 are disjoint regions in memory, and R represents everything else.
  (R : DataMem → Prop)
  (h_mem : s₀.dmem =⋆ Eq (v1.At s₀.regs.rdi.toBitVec) ⋆ Eq (v2.At s₀.regs.rsi.toBitVec) ⋆ R)

  -- well-formedness condition for the program (I don't like this, we need a more general result)
  (h_loop_wf : (layout butterflies_float_prog).LabelIsFirstAtAddress "loop") :
  -- Postcondition: The program eventually terminates (using instruction-by-instruction stepping)
  Eventually (straightlineStep (layout butterflies_float_prog))
    (fun s' =>
      -- We do not care about the exact output values, so we existentially quantify them
      ∃ (v1' v2' : List UInt8),
        -- The arrays maintain their original sizes
        v1'.length = len * 4 ∧
        v2'.length = len * 4 ∧

        -- The final memory consists of the updated arrays at the same addresses.
        -- Because `R` is completely unmodified, we have proven that NO out-of-bounds
        -- writes occurred, and NO other memory was touched!
        s'.1.dmem =⋆ Eq (v1'.At s₀.regs.rdi.toBitVec) ⋆ Eq (v2'.At s₀.regs.rsi.toBitVec) ⋆ R
    )
    (s₀, layout.start) := by
  -- 1. Put the instance at the very start of the proof!
  let inst : AddressSize := ⟨Width.W64⟩
  have h_as : address_size (self := inst) = Width.W64 := rfl

  apply Eventually.step (mid_p := fun mid => butterflies_float_invariant s₀ (len * 4) R (len / 4 - 1) mid)
  · -- GOAL 1: PROLOGUE + FIRST ITERATION OF THE LOOP
    kprologue butterflies_float_prog
    -- 1. Step through the shift-left instruction
    sym => kstep; tactic =>        -- nb: kstep 4 gets stuck after the shift
    rename_i count                 -- get rid of the shift amount
    dsimp only [count]
    ksimp_all
    simp (config := { decide := true })  -- decide conditionals depending on it
    intro af of
  ----------------------------------------------------------------------------------------------------------------------------------
    -- 1. Perform beta reduction to clean up the of lambda
    dsimp only

    -- 2. Execute memory splits on the ambient heap hypothesis for the first chunk (16 bytes)
    ksplit_array h_mem v1, 16, h_v1_len
    ksplit_array h_mem v2, 16, h_v2_len

    -- 3. Prove lengths of the taken slices for the memory subgoals
    have h_len_take16_1 : (List.take 16 v1).length = 16 := by
      rw [List.length_take, h_v1_len]
      omega
    have h_len_take16_2 : (List.take 16 v2).length = 16 := by
      rw [List.length_take, h_v2_len]
      omega

    -- 4. Expose the alignment of the base pointers
    have h_v1_aligned' : isAligned 16 s₀.regs.rdi.toBitVec = true := h_v1_aligned
    have h_v2_aligned' : isAligned 16 s₀.regs.rsi.toBitVec = true := h_v2_aligned

    -- 5. Prove base pointer address calculations (offset is 0)
    have h_addr1_calc : s₀.regs.rdi.toBitVec + setWidth 64 (BitVec.ofNat 32 s₀.regs.rdx.toNat <<< 2) + -setWidth 64 (BitVec.ofNat 32 s₀.regs.rdx.toNat <<< 2) = s₀.regs.rdi.toBitVec := by
      bv_decide
    have h_addr2_calc : s₀.regs.rsi.toBitVec + setWidth 64 (BitVec.ofNat 32 s₀.regs.rdx.toNat <<< 2) + -setWidth 64 (BitVec.ofNat 32 s₀.regs.rdx.toNat <<< 2) = s₀.regs.rsi.toBitVec := by
      bv_decide

    -- 6. Step through the remaining prologue instructions:
    --    "@1: add rdi, rdx", "@2: add rsi, rdx", "@3: neg rdx", "@4: loop:"
    sym => kstep 4; tactic =>

    -- 7. Step through the first movaps load: "@5: movaps xmm0, XMMWORD PTR [rdi+rdx*1+0]"
    sym =>
    kstep 1
    case h_len => tactic => exact h_len_take16_1
    case h_align =>
      tactic =>
        rename_i v3 status3 v2 status2 v1 status1

        -- 1. Simplify the initial match noise
        simp only [h_as]
        change isAligned 16 _ = true

        -- 2. Use a helper to strip `isAligned` and expose the pure address equality
        have helper : ∀ addr, addr = s₀.regs.rdi.toBitVec → isAligned 16 addr = true := by
          intro addr h_eq; rw [h_eq]; exact h_v1_aligned'
        apply helper

        -- 3. Run full `simp` BEFORE unfolding `v3` and `v1`.
        -- Because they are opaque local variables, `simp` will cleanly collapse all
        -- the `.toNat`, `.toInt`, `setWidth`, and `* 1` noise without translating them into `Nat` modulo math!
        simp

        -- 4. Now that the wrappers are gone (leaving `v3 + v1 = rdi`), unfold the variables
        unfold v3 v1

        -- 5. Strip the `.toNat >>> 0` bit-shift noise to expose the underlying registers
        simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

        -- 6. The goal is now a pure BitVec identity. bv_decide will effortlessly crush it!
        bv_decide
    case h_mem =>
      tactic =>
        rename_i n3 status3 n2 status2 n1 status1

        -- 1. Simplify the address_size match
        simp only [h_as]

        -- 2. Define a helper that abstracts over the messy address.
        have helper : ∀ addr, addr = s₀.regs.rdi.toBitVec →
          (Eq ((List.take 16 v1).At addr) ⋆
          (Eq ((List.drop 16 v1).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (List.take 16 v1).length)) ⋆
            (Eq ((List.take 16 v2).At s₀.regs.rsi.toBitVec) ⋆
              (Eq ((List.drop 16 v2).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 (List.take 16 v2).length)) ⋆ R)))) s₀.dmem := by
          intro addr h_eq; rw [h_eq]; exact h_mem

        -- 3. Apply the helper. Lean unifies `addr` with the messy address!
        apply helper

        -- 4. Prove our own local cleanup lemmas to dodge missing library imports
        have clean_mul : ∀ x : Int, x * 1 = x := by intro x; omega
        have clean_mul_cast : ∀ x : Int, x * (Nat.cast 1 : Int) = x := by intro x; omega
        have clean_zero : Int64.toInt 0 = 0 := rfl
        have clean_ofInt_zero : BitVec.ofInt 64 0 = 0#64 := rfl
        have clean_add_zero : ∀ x : BitVec 64, x + 0#64 = x := by intro x; bv_decide

        -- 5. Strip the wrappers BEFORE unfolding `n1` and `n3`.
        -- This elegantly collapses `.toInt * 1`, `+ 0`, and the `BitVec.ofInt_toInt` roundtrips!
        simp only [
          BitVec.ofNat_toNat, clean_mul, clean_mul_cast, clean_zero,
          clean_ofInt_zero, clean_add_zero, BitVec.ofInt_toInt, BitVec.setWidth_eq
        ]

        -- 6. Now that the goal is simply `n3 + n1 = rdi`, unfold the variables
        unfold n1 n3

        -- 7. Strip the `.toNat >>> 0` bit-shift noise
        simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

        -- 8. The goal is now pure `BitVec` arithmetic with no Nats. bv_decide crushes it!
        bv_decide

    -- movaps xmm1, XMMWORD PTR [rsi+rdx*1+0]
    kstep 1
    case h_len =>
      tactic =>
        exact h_len_take16_2
    case h_align =>
      tactic =>
        rename_i v3 status3 v2 status2 v1 status1

        -- 1. Simplify the address_size match
        simp only [h_as]
        change isAligned 16 _ = true

        -- 2. Define the helper for `rsi`
        have helper : ∀ addr, addr = s₀.regs.rsi.toBitVec → isAligned 16 addr = true := by
          intro addr h_eq; rw [h_eq]; exact h_v2_aligned'
        apply helper

        -- 3. Prove our own local cleanup lemmas to dodge missing library imports
        have clean_mul : ∀ x : Int, x * 1 = x := by intro x; omega
        have clean_mul_cast : ∀ x : Int, x * (Nat.cast 1 : Int) = x := by intro x; omega
        have clean_zero : Int64.toInt 0 = 0 := rfl
        have clean_ofInt_zero : BitVec.ofInt 64 0 = 0#64 := rfl
        have clean_add_zero : ∀ x : BitVec 64, x + 0#64 = x := by intro x; bv_decide

        -- 4. Strip the wrappers BEFORE unfolding `v1` and `v2`.
        -- This elegantly collapses `.toInt * 1`, `+ 0`, and the `BitVec.ofInt_toInt` roundtrips!
        simp only [
          BitVec.ofNat_toNat, clean_mul, clean_mul_cast, clean_zero,
          clean_ofInt_zero, clean_add_zero, BitVec.ofInt_toInt, BitVec.setWidth_eq
        ]

        -- 5. Now that the goal is simply `v2 + v1 = rsi`, unfold the variables
        unfold v1 v2

        -- 6. Strip the `.toNat >>> 0` bit-shift noise
        simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

        -- 7. The goal is now pure `BitVec` arithmetic with no Nats. bv_decide crushes it!
        bv_decide
    case h_mem =>
      tactic =>
        rename_i n3 status3 n2 status2 n1 status1

        -- 1. Simplify the match noise
        simp only [h_as]

        -- 2. Define the helper to pull the `v2` chunk to the very front of the heap
        have helper : ∀ addr, addr = s₀.regs.rsi.toBitVec →
          (Eq ((List.take 16 v2).At addr) ⋆
          (Eq ((List.take 16 v1).At s₀.regs.rdi.toBitVec) ⋆
          (Eq ((List.drop 16 v1).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (List.take 16 v1).length)) ⋆
          (Eq ((List.drop 16 v2).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 (List.take 16 v2).length)) ⋆ R)))) s₀.dmem := by
          intro addr h_eq; rw [h_eq]
          exact cast (congrFun (by ac_rfl) _) h_mem

        -- 3. Apply the helper.
        apply helper

        -- 4. Prove our own local cleanup lemmas to dodge missing library imports
        have clean_mul : ∀ x : Int, x * 1 = x := by intro x; omega
        have clean_mul_cast : ∀ x : Int, x * (Nat.cast 1 : Int) = x := by intro x; omega
        have clean_zero : Int64.toInt 0 = 0 := rfl
        have clean_ofInt_zero : BitVec.ofInt 64 0 = 0#64 := rfl
        have clean_add_zero : ∀ x : BitVec 64, x + 0#64 = x := by intro x; bv_decide

        -- 5. Strip the wrappers BEFORE unfolding `n1` and `n2`.
        -- This cleanly eliminates the scaling without converting BitVecs to Nats!
        simp only [
          BitVec.ofNat_toNat, clean_mul, clean_mul_cast, clean_zero,
          clean_ofInt_zero, clean_add_zero, BitVec.ofInt_toInt, BitVec.setWidth_eq
        ]

        -- 6. Now that the goal is simply `n2 + n1 = rsi`, unfold the variables
        unfold n1 n2

        -- 7. Strip the `.toNat >>> 0` bit-shift noise
        simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

        -- 8. The goal is now pure `BitVec` arithmetic. bv_decide crushes it!
        bv_decide

    -- "@7: movaps xmm2, xmm0"
    -- "@8: subps xmm2, xmm1"
    -- "@9: addps xmm0, xmm1"
    kstep 3

    -- NOTE: By this point in the prelude part of the proof, the robot had
    -- successfully pattern-matched what we needed to do for the memory ops and was
    -- dispatching them in one-two rounds. Getting the daggers out of the context
    -- was crucial.

    -- "@10: movaps XMMWORD PTR [rsi+rdx*1+0], xmm2"
    kstep 1
    case h_len =>
      tactic =>
        exact h_len_take16_2
    case h_align =>
      tactic =>
        -- Name all 8 daggers from top to bottom
        rename_i n4 status4 n3 status3 n2 status2 xmm_sub xmm_add

        -- 1. Simplify the address_size match
        simp only [h_as]
        change isAligned 16 _ = true

        -- 2. Define the helper for `rsi`
        have helper : ∀ addr, addr = s₀.regs.rsi.toBitVec → isAligned 16 addr = true := by
          intro addr h_eq; rw [h_eq]; exact h_v2_aligned'
        apply helper

        -- 3. Prove our own local cleanup lemmas to dodge missing library imports
        have clean_mul : ∀ x : Int, x * 1 = x := by intro x; omega
        have clean_mul_cast : ∀ x : Int, x * (Nat.cast 1 : Int) = x := by intro x; omega
        have clean_zero : Int64.toInt 0 = 0 := rfl
        have clean_ofInt_zero : BitVec.ofInt 64 0 = 0#64 := rfl
        have clean_add_zero : ∀ x : BitVec 64, x + 0#64 = x := by intro x; bv_decide

        -- 4. Strip the wrappers BEFORE unfolding `n2` and `n3`.
        -- This cleanly eliminates the scaling without converting BitVecs to Nats!
        simp only [
          BitVec.ofNat_toNat, clean_mul, clean_mul_cast, clean_zero,
          clean_ofInt_zero, clean_add_zero, BitVec.ofInt_toInt, BitVec.setWidth_eq
        ]

        -- 5. Now that the goal is simply `n3 + n2 = rsi`, unfold the variables
        unfold n2 n3

        -- 6. Strip the `.toNat >>> 0` bit-shift noise
        simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

        -- 7. The goal is now pure `BitVec` arithmetic. bv_decide crushes it!
        bv_decide
    case h_mem =>
      tactic =>
        -- Name all 8 daggers from top to bottom
        rename_i n4 status4 n3 status3 n2 status2 xmm_sub xmm_add

        -- 1. Simplify the match noise
        simp only [h_as]

        -- 2. Define the helper to pull the `v2` chunk to the very front of the heap
        have helper : ∀ addr, addr = s₀.regs.rsi.toBitVec →
          (Eq ((List.take 16 v2).At addr) ⋆
          (Eq ((List.take 16 v1).At s₀.regs.rdi.toBitVec) ⋆
          (Eq ((List.drop 16 v1).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (List.take 16 v1).length)) ⋆
          (Eq ((List.drop 16 v2).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 (List.take 16 v2).length)) ⋆ R)))) s₀.dmem := by
          intro addr h_eq; rw [h_eq]
          exact cast (congrFun (by ac_rfl) _) h_mem

        -- 3. Apply the helper. Lean unifies `addr` and `?R` seamlessly.
        apply helper

        -- 4. Prove our own local cleanup lemmas to dodge missing library imports
        have clean_mul : ∀ x : Int, x * 1 = x := by intro x; omega
        have clean_mul_cast : ∀ x : Int, x * (Nat.cast 1 : Int) = x := by intro x; omega
        have clean_zero : Int64.toInt 0 = 0 := rfl
        have clean_ofInt_zero : BitVec.ofInt 64 0 = 0#64 := rfl
        have clean_add_zero : ∀ x : BitVec 64, x + 0#64 = x := by intro x; bv_decide

        -- 5. Strip the wrappers BEFORE unfolding `n2` and `n3`.
        simp only [
          BitVec.ofNat_toNat, clean_mul, clean_mul_cast, clean_zero,
          clean_ofInt_zero, clean_add_zero, BitVec.ofInt_toInt, BitVec.setWidth_eq
        ]

        -- 6. Now that the goal is simply `n3 + n2 = rsi`, unfold the variables
        unfold n2 n3

        -- 7. Strip the `.toNat >>> 0` bit-shift noise to expose the underlying registers
        simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

        -- 8. The goal is now exactly: `(RDX_scaled + RSI) + -RDX_scaled = RSI`. bv_decide crushes it!
        bv_decide

    -- "@11: movaps XMMWORD PTR [rdi+rdx*1+0], xmm0"
    kstep 1
    case h_len =>
      tactic =>
        exact h_len_take16_1
    case h_align =>
      tactic =>
        -- Name all 8 daggers from top to bottom
        rename_i n3 status3 n2 status2 n1 status1 xmm_sub xmm_add

        -- 1. Simplify the match noise
        simp only [h_as]
        change isAligned 16 _ = true

        -- 2. Define the helper for `rdi`
        have helper : ∀ addr, addr = s₀.regs.rdi.toBitVec → isAligned 16 addr = true := by
          intro addr h_eq; rw [h_eq]; exact h_v1_aligned'
        apply helper

        -- 3. Prove our own local cleanup lemmas to dodge missing library imports
        have clean_mul : ∀ x : Int, x * 1 = x := by intro x; omega
        have clean_mul_cast : ∀ x : Int, x * (Nat.cast 1 : Int) = x := by intro x; omega
        have clean_zero : Int64.toInt 0 = 0 := rfl
        have clean_ofInt_zero : BitVec.ofInt 64 0 = 0#64 := rfl
        have clean_add_zero : ∀ x : BitVec 64, x + 0#64 = x := by intro x; bv_decide

        -- 4. Strip the wrappers BEFORE unfolding `n1` and `n3`.
        simp only [
          BitVec.ofNat_toNat, clean_mul, clean_mul_cast, clean_zero,
          clean_ofInt_zero, clean_add_zero, BitVec.ofInt_toInt, BitVec.setWidth_eq
        ]

        -- 5. Now that the goal is simply `n3 + n1 = rdi`, unfold the variables
        unfold n1 n3

        -- 6. Strip the `.toNat >>> 0` bit-shift noise
        simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

        -- 7. The goal is now pure `BitVec` arithmetic. bv_decide crushes it!
        bv_decide
    case h_mem =>
      tactic =>
        -- Name all 8 daggers from top to bottom
        rename_i n4 status4 n3 status3 n2 status2 xmm_sub xmm_add

        -- 1. Simplify the match noise
        simp only [h_as]

        -- 2. "Execute" the FIRST store logically in our separation hypothesis.
        -- First, reorder the initial memory state to put `v2` (rsi) at the front.
        have h_mem_rsi_front :
          (Eq ((List.take 16 v2).At s₀.regs.rsi.toBitVec) ⋆
          (Eq ((List.take 16 v1).At s₀.regs.rdi.toBitVec) ⋆
          (Eq ((List.drop 16 v1).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (List.take 16 v1).length)) ⋆
          (Eq ((List.drop 16 v2).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 (List.take 16 v2).length)) ⋆ R)))) s₀.dmem := cast (congrFun (by ac_rfl) _) h_mem

        -- Apply Mem.storeInt_sep to get the memory state AFTER the first store.
        have h_mem_after_store1 := Mem.storeInt_sep s₀.regs.rsi.toBitVec 16 (List.take 16 v2) _ s₀.dmem ⟨h_mem_rsi_front, h_len_take16_2⟩ xmm_sub.toInt

        -- 3. Define the helper for the SECOND store (`rdi`).
        -- We pull `v1` (rdi) to the front of the NEW memory state.
        have helper : ∀ addr1 addr2 val2,
          addr1 = s₀.regs.rdi.toBitVec →
          addr2 = s₀.regs.rsi.toBitVec →
          val2 = xmm_sub.toInt →
          (Eq ((List.take 16 v1).At addr1) ⋆
          (Eq ((Int.toBytes 16 val2).At addr2) ⋆
          (Eq ((List.drop 16 v1).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (List.take 16 v1).length)) ⋆
          (Eq ((List.drop 16 v2).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 (List.take 16 v2).length)) ⋆ R)))) (Mem.storeInt s₀.dmem addr2 16 val2) := by
          intro addr1 addr2 val2 h_eq1 h_eq2 h_val2
          rw [h_eq1, h_eq2, h_val2]
          exact cast (congrFun (by ac_rfl) _) h_mem_after_store1

        -- 5. Prove local cleanup lemmas to dodge missing library imports
        have clean_mul : ∀ x : Int, x * 1 = x := by intro x; omega
        have clean_mul_cast : ∀ x : Int, x * (Nat.cast 1 : Int) = x := by intro x; omega
        have clean_zero : Int64.toInt 0 = 0 := rfl
        have clean_ofInt_zero : BitVec.ofInt 64 0 = 0#64 := rfl
        have clean_add_zero : ∀ x : BitVec 64, x + 0#64 = x := by intro x; bv_decide

        -- 4. Apply the helper. Lean will generate 3 subgoals for the addresses and value.
        apply helper

        -- Subgoal 1: Prove the RDI address equality
        · simp only [BitVec.ofNat_toNat, clean_mul, clean_mul_cast, clean_zero, clean_ofInt_zero, clean_add_zero, BitVec.ofInt_toInt, BitVec.setWidth_eq]
          unfold n2 n4
          simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          bv_decide

        -- Subgoal 2: Prove the RSI address equality
        · simp only [BitVec.ofNat_toNat, clean_mul, clean_mul_cast, clean_zero, clean_ofInt_zero, clean_add_zero, BitVec.ofInt_toInt, BitVec.setWidth_eq]
          unfold n2 n3
          simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          bv_decide

        -- Subgoal 3: Prove the stored value is trivially identical
        · -- 1. Reduce the `AvxReg.base` match to select the `mm2` branch
          dsimp [AvxReg.base]

          -- 2. Strip the `.toInt` from both sides
          apply congrArg BitVec.toInt

          -- 3. Hide the massive AST values from `bv_decide` so it runs instantly
          clear_value xmm_sub xmm_add

          -- 4. Unfold the register update logic to expose the BitVec concatenation
          unfold BitVec.replaceLow BitVec.drop

          -- 5. Define a tiny, instant lemma proving that extracting 128 bits from a 512-bit concatenation works
          have h_trunc : ∀ (A : BitVec 384) (B : BitVec 128), BitVec.ofNat 128 (BitVec.setWidth 512 (BitVec.append A B)).toNat = B := by
            intro A B
            change (BitVec.setWidth 512 (BitVec.append A B)).setWidth 128 = B
            bv_decide

          -- 6. Apply the lemma to close the goal!
          rw [h_trunc]

    -- "@12: add rdx, 16"
    kstep 1

    -- "@13: jl loop"
    tactic =>
    sym => kstep 1; tactic =>

    -- Rename all 14 daggers from top to bottom
    rename_i hl1 hs1 hl2 hs2 v5 st5 v4 st4 v3 st3 xmm_sub xmm_add v_rdx_next status_add

    -- Clean up the local definitions
    kdsimp_all

    -- Split on whether this is the final iteration of the loop!
    by_cases h_last : len / 4 - 1 = 0
    · -- CASE 1: len / 4 - 1 = 0 (The loop terminates immediately)
      have h_len_eq_4 : len = 4 := by omega

      -- Instead of copying the exact condition, `split` handles the `if` automatically!
      split
      · -- Subgoal 1: Branch taken (condition = true). This is a contradiction!
        rename_i h_cond

        -- Unfold the local variables in the condition
        try dsimp [v_rdx_next, xmm_a] at h_cond
        try dsimp [v_rdx_next, v3] at h_cond

        -- Strip the noise
        simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_len_reg h_cond
        rw [h_len_eq_4] at h_len_reg

        -- Substitute `rdx` using `h_len_reg`
        have h_subst : BitVec.ofNat 32 s₀.regs.rdx.toNat = 4#32 := h_len_reg
        rw [h_subst] at h_cond

        -- `h_cond` is now purely concrete numbers. Lean's kernel can evaluate it natively!
        -- We simply assert that it reduces definitionally to `false = true`.
        change false = true at h_cond
        contradiction

      · -- Subgoal 2: Branch NOT taken (condition = false). This is the correct path!

        -- Simplify the empty Directives.interp to Effects.done
        dsimp only [Directives.interp]

        -- Evaluate `Effects.All` on `Effects.done`, which natively reduces to the loop invariant!
        dsimp only [Effects.All]

        -- Now expose the loop invariant
        unfold butterflies_float_invariant
        simp only [h_last, ↓reduceIte]

        -- Instantiate the existential arrays for the final memory state!
        -- xmm_add and xmm_sub perfectly captured the 128-bit results
        let mem1_next := Int.toBytes 16 xmm_add.toInt
        let mem2_next := Int.toBytes 16 xmm_sub.toInt
        refine ⟨mem1_next, mem2_next, ?h_len1, ?h_len2, ?h_k_bound, ?h_mem_sep, ?h_rdi, ?h_rsi, ?h_rdx, ?h_pc⟩

        case h_len1 =>
          rw [Int.toBytes_length]; omega
        case h_len2 =>
          rw [Int.toBytes_length]; omega
        case h_k_bound =>
          omega

        case h_mem_sep =>
          -- A. Logical Store 1 (rsi)
          have h_mem_rsi_front :
            (Eq ((List.take 16 v2).At s₀.regs.rsi.toBitVec) ⋆
            (Eq ((List.take 16 v1).At s₀.regs.rdi.toBitVec) ⋆
            (Eq ((List.drop 16 v1).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (List.take 16 v1).length)) ⋆
            (Eq ((List.drop 16 v2).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 (List.take 16 v2).length)) ⋆ R)))) s₀.dmem := cast (congrFun (by ac_rfl) _) h_mem

          have h_store1 := Mem.storeInt_sep s₀.regs.rsi.toBitVec 16 (List.take 16 v2) _ s₀.dmem ⟨h_mem_rsi_front, h_len_take16_2⟩ xmm_sub.toInt

          -- B. Logical Store 2 (rdi)
          have h_mem_rdi_front :
            (Eq ((List.take 16 v1).At s₀.regs.rdi.toBitVec) ⋆
            (Eq ((Int.toBytes 16 xmm_sub.toInt).At s₀.regs.rsi.toBitVec) ⋆
            (Eq ((List.drop 16 v1).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (List.take 16 v1).length)) ⋆
            (Eq ((List.drop 16 v2).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 (List.take 16 v2).length)) ⋆ R)))) (Mem.storeInt s₀.dmem s₀.regs.rsi.toBitVec 16 xmm_sub.toInt) := cast (congrFun (by ac_rfl) _) h_store1

          have h_store2 := Mem.storeInt_sep s₀.regs.rdi.toBitVec 16 (List.take 16 v1) _ _ ⟨h_mem_rdi_front, h_len_take16_1⟩ xmm_add.toInt

          -- C. Kill the dropped arrays (since len=4, dropping 16 bytes leaves an empty array)
          have h_drop1 : List.drop 16 v1 = [] := by apply List.drop_eq_nil_of_le; rw [h_v1_len, h_len_eq_4]; omega
          have h_drop2 : List.drop 16 v2 = [] := by apply List.drop_eq_nil_of_le; rw [h_v2_len, h_len_eq_4]; omega
          rw [h_drop1, h_drop2] at h_store2
          simp only [h_empty_sep] at h_store2

          -- D. Clean up the main goal's addresses IN-PLACE
          have clean_mul : ∀ x : Int, x * 1 = x := by intro x; omega
          have clean_mul_cast : ∀ x : Int, x * (Nat.cast 1 : Int) = x := by intro x; omega
          have clean_zero : Int64.toInt 0 = 0 := rfl
          have clean_ofInt_zero : BitVec.ofInt 64 0 = 0#64 := rfl
          have clean_add_zero : ∀ x : BitVec 64, x + 0#64 = x := by intro x; bv_decide

          simp only [BitVec.ofNat_toNat, clean_mul, clean_mul_cast, clean_zero, clean_ofInt_zero, clean_add_zero, BitVec.ofInt_toInt, BitVec.setWidth_eq]

          -- E. Substitute the RDI address
          have h_addr_rdi : v5 + v3 = s₀.regs.rdi.toBitVec := by
            unfold v5 v3
            simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_len_reg ⊢
            rw [h_len_eq_4] at h_len_reg
            have h_subst : BitVec.ofNat 32 s₀.regs.rdx.toNat = 4#32 := h_len_reg
            -- Substitute instantly without destroying the syntax tree!
            simp only [h_subst]
            bv_decide
          rw [h_addr_rdi]

          -- F. Substitute the RSI address
          have h_addr_rsi : v4 + v3 = s₀.regs.rsi.toBitVec := by
            unfold v4 v3
            simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_len_reg ⊢
            rw [h_len_eq_4] at h_len_reg
            have h_subst : BitVec.ofNat 32 s₀.regs.rdx.toNat = 4#32 := h_len_reg
            simp only [h_subst]
            bv_decide
          rw [h_addr_rsi]

          -- G. Clean up the massive ZMM/XMM match statements in the goal!
          dsimp [AvxReg.base]

          -- Provide an instant lemma proving that extracting 128 bits from a `replaceLow` works.
          -- We prove this by extracting the bit-level definition of `replaceLow` and truncating it!
          have h_extract : ∀ (Z : BitVec 512) (X : BitVec 128), (setWidth 128 (replaceLow Z X)).toInt = X.toInt := by
            intro Z X
            apply congrArg BitVec.toInt

            -- replaceLow is already expanded, so we safely unfold drop and collapse the widths
            -- using simp only (which won't crash if a definition is missing)
            simp only [BitVec.replaceLow, BitVec.drop, BitVec.setWidth_append, BitVec.setWidth_eq]
            try bv_decide

          -- This cleanly collapses both massive ZMM structures directly to xmm_add.toInt and xmm_sub.toInt!
          simp only [h_extract]

          -- H. The goal is now definitionally identical to `h_store2`!
          unfold mem1_next mem2_next
          exact cast (congrFun (by ac_rfl) _) h_store2

        case h_rdi =>
          dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb']
          unfold v5
          simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_len_reg ⊢
          rw [h_len_eq_4] at h_len_reg ⊢
          have h_subst : BitVec.ofNat 32 s₀.regs.rdx.toNat = 4#32 := h_len_reg

          -- Use `simp` instead of `rw` to substitute without destroying the BitVec `+` operator!
          simp only [h_subst]

          -- Let the full simplifier clean up the static `4 * 4` on the right-hand side
          simp

          -- The goal is now pure BitVec arithmetic: `16#64 + rdi = rdi + 16#64`.
          bv_decide

        case h_rsi =>
          dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb']
          unfold v4
          simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_len_reg ⊢
          rw [h_len_eq_4] at h_len_reg ⊢
          have h_subst : BitVec.ofNat 32 s₀.regs.rdx.toNat = 4#32 := h_len_reg

          simp only [h_subst]
          simp
          bv_decide
        case h_rdx =>
          -- 1. Unfold the register getter so the LHS becomes exactly `v_rdx_next`
          dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb']

          -- 2. Unfold the local variables
          try dsimp [v_rdx_next, v3]

          -- 3. Strip the bit-shift noise from both the goal and our `h_len_reg` hypothesis
          simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_len_reg ⊢

          -- 4. Substitute `len = 4` into `h_len_reg`
          rw [h_len_eq_4] at h_len_reg

          -- 5. Extract the equality `BitVec.ofNat 32 s₀.regs.rdx.toNat = 4#32` and substitute it into the goal!
          have h_subst : BitVec.ofNat 32 s₀.regs.rdx.toNat = 4#32 := h_len_reg
          rw [h_subst]

          -- 6. The goal is now `16 + -16 = 0`. bv_decide crushes it!
          bv_decide
        case h_pc =>
          unfold butterflies_float_end_pc
          -- Unroll the AST and list traversal functions so Lean can compute the final symbolic PC
          simp [butterflies_float_prog, Executable.withAddresses, Layout.apply, List.mapIdx, List.mapIdx.go, List.getLast?]
    · -- CASE 2: len / 4 - 1 > 0 (The loop continues)
      have h_len_gt_4 : len ≥ 8 := by omega

      -- `split` will handle the `if` statement for the jump automatically.
      split
      · -- Subgoal 1: condition = true (Branch taken). This is the CORRECT path!
        rename_i h_cond

        -- `Effects.All` on `Effects.done` reduces directly to our loop invariant!
        dsimp only [Effects.All]
        unfold butterflies_float_invariant

        -- Since `len ≥ 8`, we know `len / 4 - 1 ≠ 0`.
        -- This puts us in the `else` branch of the invariant (the inductive step).
        have h_k_not_zero : len / 4 - 1 ≠ 0 := by omega
        simp only [h_k_not_zero, ↓reduceIte]

        -- Instantiate the existential arrays for the NEW memory state!
        -- We stitch the 16 newly computed bytes onto the front of the remaining unread bytes.
        let mem1_next := Int.toBytes 16 xmm_add.toInt ++ List.drop 16 v1
        let mem2_next := Int.toBytes 16 xmm_sub.toInt ++ List.drop 16 v2
        refine ⟨mem1_next, mem2_next, ?h_len1, ?h_len2, ?h_k_bound, ?h_mem_sep, ?h_rdi, ?h_rsi, ?h_rdx, ?h_pc⟩

        case h_len1 =>
          dsimp [mem1_next]
          rw [List.length_append, Int.toBytes_length, List.length_drop, h_v1_len]
          omega

        case h_len2 =>
          dsimp [mem2_next]
          rw [List.length_append, Int.toBytes_length, List.length_drop, h_v2_len]
          omega

        case h_k_bound =>
          omega

        case h_mem_sep =>
          -- A. Logical Store 1 (rsi)
          have h_mem_rsi_front :
            (Eq ((List.take 16 v2).At s₀.regs.rsi.toBitVec) ⋆
            (Eq ((List.take 16 v1).At s₀.regs.rdi.toBitVec) ⋆
            (Eq ((List.drop 16 v1).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (List.take 16 v1).length)) ⋆
            (Eq ((List.drop 16 v2).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 (List.take 16 v2).length)) ⋆ R)))) s₀.dmem := cast (congrFun (by ac_rfl) _) h_mem

          have h_store1 := Mem.storeInt_sep s₀.regs.rsi.toBitVec 16 (List.take 16 v2) _ s₀.dmem ⟨h_mem_rsi_front, h_len_take16_2⟩ xmm_sub.toInt

          -- B. Logical Store 2 (rdi)
          have h_mem_rdi_front :
            (Eq ((List.take 16 v1).At s₀.regs.rdi.toBitVec) ⋆
            (Eq ((Int.toBytes 16 xmm_sub.toInt).At s₀.regs.rsi.toBitVec) ⋆
            (Eq ((List.drop 16 v1).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (List.take 16 v1).length)) ⋆
            (Eq ((List.drop 16 v2).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 (List.take 16 v2).length)) ⋆ R)))) (Mem.storeInt s₀.dmem s₀.regs.rsi.toBitVec 16 xmm_sub.toInt) := cast (congrFun (by ac_rfl) _) h_store1

          have h_store2 := Mem.storeInt_sep s₀.regs.rdi.toBitVec 16 (List.take 16 v1) _ _ ⟨h_mem_rdi_front, h_len_take16_1⟩ xmm_add.toInt

          -- C. Clean up the main goal's addresses IN-PLACE
          have clean_mul : ∀ x : Int, x * 1 = x := by intro x; omega
          have clean_mul_cast : ∀ x : Int, x * (Nat.cast 1 : Int) = x := by intro x; omega
          have clean_zero : Int64.toInt 0 = 0 := rfl
          have clean_ofInt_zero : BitVec.ofInt 64 0 = 0#64 := rfl
          have clean_add_zero : ∀ x : BitVec 64, x + 0#64 = x := by intro x; bv_decide

          simp only [BitVec.ofNat_toNat, clean_mul, clean_mul_cast, clean_zero, clean_ofInt_zero, clean_add_zero, BitVec.ofInt_toInt, BitVec.setWidth_eq]

          -- D. Substitute the RDI address (Tautology: A + rdi + -A = rdi)
          have h_addr_rdi : v5 + v3 = s₀.regs.rdi.toBitVec := by
            unfold v5 v3; simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_decide
          rw [h_addr_rdi]

          -- E. Substitute the RSI address (Tautology: A + rsi + -A = rsi)
          have h_addr_rsi : v4 + v3 = s₀.regs.rsi.toBitVec := by
            unfold v4 v3; simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_decide
          rw [h_addr_rsi]

          -- F. Clean up the massive ZMM/XMM match statements in the goal!
          dsimp [AvxReg.base]
          have h_extract : ∀ (Z : BitVec 512) (X : BitVec 128), (setWidth 128 (BitVec.replaceLow Z X)).toInt = X.toInt := by
            intro Z X; apply congrArg BitVec.toInt; unfold BitVec.replaceLow; bv_decide
          simp only [h_extract]

          -- G. Fold the separated chunks back into mem1_next and mem2_next!
          unfold mem1_next mem2_next

          -- We align the length offsets in h_store2 to exact numbers
          rw [h_len_take16_1, h_len_take16_2] at h_store2

          -- H. Now use the separation logic framework's append lemma!
          have h_fold :
            (Eq ((Int.toBytes 16 xmm_add.toInt ++ List.drop 16 v1).At s₀.regs.rdi.toBitVec) ⋆
             Eq ((Int.toBytes 16 xmm_sub.toInt ++ List.drop 16 v2).At s₀.regs.rsi.toBitVec) ⋆ R) =
            (Eq ((Int.toBytes 16 xmm_add.toInt).At s₀.regs.rdi.toBitVec) ⋆
             Eq ((List.drop 16 v1).At (s₀.regs.rdi.toBitVec + 16#64)) ⋆
             Eq ((Int.toBytes 16 xmm_sub.toInt).At s₀.regs.rsi.toBitVec) ⋆
             Eq ((List.drop 16 v2).At (s₀.regs.rsi.toBitVec + 16#64)) ⋆ R) := by
            -- Split the first array
            rw [Mem.At_append_sep]
            · -- Split the second array
              rw [Mem.At_append_sep]
              · -- The offsets are now `BitVec.ofNat 64 (...length)`. Rewrite them to 16#64!
                have h_len_16_1 : BitVec.ofNat 64 (Int.toBytes 16 xmm_add.toInt).length = 16#64 := by rw [Int.toBytes_length]
                have h_len_16_2 : BitVec.ofNat 64 (Int.toBytes 16 xmm_sub.toInt).length = 16#64 := by rw [Int.toBytes_length]
                rw [h_len_16_1, h_len_16_2]
                ac_rfl

              · -- Side condition for splitting array 2
                rw [Int.toBytes_length, List.length_drop, h_v2_len]
                omega

            · -- Side condition for splitting array 1
              rw [Int.toBytes_length, List.length_drop, h_v1_len]
              omega

          rw [h_fold]
          exact cast (congrFun (by ac_rfl) _) h_store2

        case h_rdi =>
          dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb']
          try dsimp [v5]
          simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_len_reg ⊢

          have h_subst : BitVec.ofNat 32 s₀.regs.rdx.toNat = BitVec.ofNat 32 len := h_len_reg
          simp only [h_subst]

          have h_math : setWidth 64 (BitVec.ofNat 32 len <<< 2) = BitVec.ofNat 64 (len * 4) := by
            apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_ofNat]
            omega

          simp only [h_math]
          -- Drop down to pure Nat modulo arithmetic and let omega prove A + B = B + A!
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_ofNat]
          omega

        case h_rsi =>
          dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb']
          try dsimp [v4]
          simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_len_reg ⊢

          have h_subst : BitVec.ofNat 32 s₀.regs.rdx.toNat = BitVec.ofNat 32 len := h_len_reg
          simp only [h_subst]

          have h_math : setWidth 64 (BitVec.ofNat 32 len <<< 2) = BitVec.ofNat 64 (len * 4) := by
            apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_ofNat]
            omega

          simp only [h_math]
          -- Drop down to pure Nat modulo arithmetic and let omega prove A + B = B + A!
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_ofNat]
          omega

        case h_rdx =>
          -- 1. Unfold the register getter to expose `v_rdx_next`
          dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb']
          try dsimp [v_rdx_next, v3]

          -- 2. Strip the bit-shift noise from `h_len_reg` and the goal
          simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_len_reg ⊢

          -- 3. Substitute `len` for `rdx`!
          have h_subst : BitVec.ofNat 32 s₀.regs.rdx.toNat = BitVec.ofNat 32 len := h_len_reg
          simp only [h_subst]

          -- 4. Bridge the BitVec shift to a pure multiplication `len * 4`
          have h_math1 : setWidth 64 (BitVec.ofNat 32 len <<< 2) = BitVec.ofNat 64 (len * 4) := by
            apply BitVec.eq_of_toNat_eq
            simp
            omega
          simp only [h_math1]

          -- 5. Generalize the RHS division math to a variable `K` so `omega` handles it perfectly
          generalize h_K : (len / 4 - 1) * 16 = K

          -- 6. Prove the relationship between `len * 4` and `K`
          have h_math2 : len * 4 = K + 16 := by omega

          -- 7. Use that relationship to split the BitVec representation
          have h_math3 : BitVec.ofNat 64 (len * 4) = BitVec.ofNat 64 K + 16#64 := by
            rw [h_math2]
            apply BitVec.eq_of_toNat_eq
            simp
            -- omega
          simp only [h_math3]

          -- 8. The goal is now `16#64 + -(L + 16#64) = -L`. We drop down to pure Nat arithmetic!
          apply BitVec.eq_of_toNat_eq

          -- 9. Simplify the BitVec operations into pure Nat modulo operations
          simp only [BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat]

          -- 10. Omega can easily solve this linear modulo arithmetic!
          omega

        case h_pc =>
          rfl
      · -- Subgoal 2: condition = false (Branch not taken). This is a CONTRADICTION!
        rename_i h_cond
        -- 1. Strip bit-shift and cast noise from h_len_reg
        simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_len_reg
        have h_subst : BitVec.ofNat 32 s₀.regs.rdx.toNat = BitVec.ofNat 32 len := h_len_reg

        -- 2. Simplify v3 into -BitVec.ofNat 64 (len * 4)
        have h_v3_eq : v3 = -BitVec.ofNat 64 (len * 4) := by
          unfold v3
          simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, h_subst]
          have h_shift : setWidth 64 (BitVec.ofNat 32 len <<< 2) = BitVec.ofNat 64 (len * 4) := by
            apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_ofNat]
            omega
          rw [h_shift]

        -- 3. Express v3.toInt as -(len * 4)
        have h_v3_toInt : v3.toInt = -((len * 4 : Nat) : Int) := by
          rw [h_v3_eq]
          have h_neg_cast : -BitVec.ofNat 64 (len * 4) = -BitVec.ofInt 64 (len * 4) := by
            apply congrArg
            apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
            omega
          rw [h_neg_cast, ← BitVec.ofInt_neg]
          have h_bounds : -(2 ^ 63 : Int) ≤ -((len * 4 : Nat) : Int) ∧ -((len * 4 : Nat) : Int) < (2 ^ 63 : Int) := by
            constructor <;> omega
          exact BitVec.toInt_ofInt_eq_self (by decide) h_bounds.1 h_bounds.2

        -- 4. Simplify v_rdx_next to -BitVec.ofNat 64 (len * 4 - 16)
        have h_rdx_next_eq : v_rdx_next = -BitVec.ofNat 64 (len * 4 - 16) := by
          unfold v_rdx_next
          simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rw [h_v3_eq]
          have h_bv_split : BitVec.ofNat 64 (len * 4) = BitVec.ofNat 64 (len * 4 - 16) + 16#64 := by
            have h_eq : BitVec.ofInt 64 ((len * 4 : Nat) : Int) = BitVec.ofInt 64 (((len * 4 - 16 : Nat) : Int)) + BitVec.ofInt 64 16 := by
              rw [← BitVec.ofInt_add]
              congr 1
              omega
            exact h_eq
          rw [h_bv_split]
          generalize BitVec.ofNat 64 (len * 4 - 16) = Y
          bv_decide

        -- 5. Express v_rdx_next.toInt as -(len * 4 - 16)
        have h_rdx_next_toInt : v_rdx_next.toInt = -(((len * 4 - 16 : Nat) : Int)) := by
          rw [h_rdx_next_eq]
          have h_neg_cast : -BitVec.ofNat 64 (len * 4 - 16) = -BitVec.ofInt 64 ((len * 4 - 16 : Nat) : Int) := by
            apply congrArg
            apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
          rw [h_neg_cast, ← BitVec.ofInt_neg]
          have h_bounds : -(2 ^ 63 : Int) ≤ -(((len * 4 - 16 : Nat) : Int)) ∧ -(((len * 4 - 16 : Nat) : Int)) < (2 ^ 63 : Int) := by
            constructor <;> omega
          exact @BitVec.toInt_ofInt_eq_self 64 (by decide) (-(((len * 4 - 16 : Nat) : Int))) h_bounds.1 h_bounds.2

        -- 6. Prove OF = false: v_rdx_next.toInt = 16 + v3.toInt
        have h_no_overflow : v_rdx_next.toInt = 16 + (BitVec.ofNat 64 (BitVec.ofNat 64 v3.toNat).toNat).toInt := by
          have h_v3_id : (BitVec.ofNat 64 (BitVec.ofNat 64 v3.toNat).toNat) = v3 := by
            simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rw [h_v3_id, h_rdx_next_toInt, h_v3_toInt]
          omega

        -- 7. Prove SF = true: v_rdx_next.msb = true
        have h_sf : v_rdx_next.msb = true := by
          by_cases h_msb : v_rdx_next.msb
          · exact h_msb
          · have h_msb_false : v_rdx_next.msb = false := Bool.eq_false_of_ne_true h_msb
            have h_nonneg : v_rdx_next.toInt ≥ 0 := by
              rw [BitVec.toInt_eq_toNat_of_msb h_msb_false]
              omega
            rw [h_rdx_next_toInt] at h_nonneg
            omega

        -- 8. Reduce the branch condition to true and contradict h_cond
        have h_cond_true : (v_rdx_next.msb != (v_rdx_next.toInt != 16 + (BitVec.ofNat 64 (BitVec.ofNat 64 v3.toNat).toNat).toInt)) = true := by
          rw [h_sf]
          have h_of_false : (v_rdx_next.toInt != 16 + (BitVec.ofNat 64 (BitVec.ofNat 64 v3.toNat).toNat).toInt) = false := by
            rw [h_no_overflow]
            simp only [bne_self_eq_false]
          rw [h_of_false]
          rfl

        -- Contradict h_cond directly
        rw [h_cond_true] at h_cond
        contradiction



----|-----------------------------------------------------------------------------------------------------------------------------
  · intro mid inv
    apply reg_dec_loop (straightlineStep (layout butterflies_float_prog)) _ _
      (butterflies_float_invariant s₀ (len * 4) R) (len / 4 - 1)
    constructor
    · exact inv
    · constructor
      · -- k = 0
        intros state inv_zero
        rcases inv_zero with ⟨mem1_curr, mem2_curr, h_len1, h_len2, h_k_bound, h_mem_sep, h_rdi, h_rsi, h_rdx, h_pc⟩
        apply Eventually.done
        exact ⟨mem1_curr, mem2_curr, h_len1, h_len2, h_mem_sep⟩
      · -- 🔄 Inductive Step: Stepping through one loop iteration
        intro state k h_k_nonzero inv_k
        -- 1. Destruct the strengthened invariant to expose current state
        rcases inv_k with ⟨mem1_curr, mem2_curr, h_len1, h_len2, h_k_bound, h_mem_sep, h_rdi, h_rsi, h_rdx, h_pc⟩
        cases state with | mk state_data state_pc =>
        simp only [h_k_nonzero] at h_pc
        subst state_pc
        simp

        -- get to the label
        apply step_cps
        dsimp only [straightlineStep, Executable.straightline]
        rw [directivesFromAddress_label _ "loop" h_loop_wf]
        delta butterflies_float_prog
        simp [Executable.directivesFromLabel, Layout.apply, List.mapIdx, List.mapIdx.go, List.dropWhile]
        have h_neq : ∀ i, ((Directive.instr i) != (Directive.label "loop")) = true := by
          intro i; rfl
        have h_eq : ((Directive.label "loop") != (Directive.label "loop")) = false := by
          rfl
        simp [h_neq, h_eq]  -- not sure why I need this, but I wrote these to clear out lots of matches on label directives

        -- step the label
        sym => kstep 1; tactic =>

        -- ====================================================================
        -- 🌟 GLOBAL HOISTING: SPLITS AND ADDRESSES 🌟
        -- ====================================================================
        let offset := len * 4 - k * 16

        -- 1. Pre-prove the lengths of the dropped chunks for ksplit_array
        have h_drop_len1 : (List.drop offset mem1_curr).length = k * 16 := by
          rw [List.length_drop, h_len1]; omega
        have h_drop_len2 : (List.drop offset mem2_curr).length = k * 16 := by
          rw [List.length_drop, h_len2]; omega

        -- 2. Execute ALL memory splits on the ambient h_mem_sep hypothesis
        ksplit_array h_mem_sep mem1_curr, offset, h_len1
        ksplit_array h_mem_sep (List.drop offset mem1_curr), 16, h_drop_len1

        ksplit_array h_mem_sep mem2_curr, offset, h_len2
        ksplit_array h_mem_sep (List.drop offset mem2_curr), 16, h_drop_len2

        -- 3. Clean up all lengths globally in h_mem_sep
        have h_len_take1 : (List.take offset mem1_curr).length = offset := by apply List.length_take_of_le; omega
        have h_len_take16_1 : (List.take 16 (List.drop offset mem1_curr)).length = 16 := by rw [List.length_take, h_drop_len1]; omega

        have h_len_take2 : (List.take offset mem2_curr).length = offset := by apply List.length_take_of_le; omega
        have h_len_take16_2 : (List.take 16 (List.drop offset mem2_curr)).length = 16 := by rw [List.length_take, h_drop_len2]; omega

        simp only [h_len_take1, h_len_take16_1, h_len_take2, h_len_take16_2] at h_mem_sep

        -- 4. Hoist address alignment proofs
        have h_addr1_aligned : isAligned 16 (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset) = true := by
          unfold isAligned at h_v1_aligned ⊢
          simp only [beq_iff_eq] at h_v1_aligned ⊢

          -- 1. Extract the fact that offset is a multiple of 16
          have h_offset_mod : offset % 16 = 0 := by omega

          -- 2. Push `.toNat` through the BitVec addition and literal
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]

          -- Now the goal is purely about natural numbers:
          -- ((base.toNat + offset % 2^64) % 2^64) % 16 = 0
          -- omega handles nested modulos beautifully, knowing 2^64 is a multiple of 16.
          omega

        have h_addr2_aligned : isAligned 16 (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) = true := by
          unfold isAligned at h_v2_aligned ⊢
          simp only [beq_iff_eq] at h_v2_aligned ⊢
          have h_offset_mod : offset % 16 = 0 := by omega
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega

        -- 5. Hoist address calculations
        have h_addr1_calc : state_data.regs.get (Reg.low Reg64.rdi Width.W64) + state_data.regs.get (Reg.low Reg64.rdx Width.W64) = s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset := by
          rw [h_rdi, h_rdx]
          dsimp only [offset]
          rw [BitVec.add_assoc]
          congr 1
          -- 1. Convert the BitVec equality into a Nat equality
          apply BitVec.eq_of_toNat_eq
          -- 2. Push .toNat through the BitVec addition, negation, and literals
          simp only [BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat]
          -- 3. omega now sees a pure Nat modulo arithmetic problem and bounds (h_k_bound)
          omega

        have h_addr2_calc : state_data.regs.get (Reg.low Reg64.rsi Width.W64) + state_data.regs.get (Reg.low Reg64.rdx Width.W64) = s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset := by
          rw [h_rsi, h_rdx]
          dsimp only [offset]
          rw [BitVec.add_assoc]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat]
          omega

        -- Hide arithmetic for future grind steps
        generalize h_rdx_val : (-BitVec.ofNat 64 (k * 16)) = rdx_val at h_rdx ⊢
        generalize h_rdi_val : (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (len * 4)) = rdi_val at h_rdi ⊢
        /- or:
          attribute [ksimp]
            BitVec.mul_one
            BitVec.add_zero
            BitVec.zero_add
        -/
        -- 5. Execute the first movaps instruction (movaps xmm0, XMMWORD PTR [rdi+rdx*1+0])
        sym =>
        kstep 1
        case h_mem =>
          tactic =>
            -- 1. Define a helper that parameterizes the target address.
            -- We just pull the 16-byte chunk we want from mem1_curr to the very front
            -- of the separation logic chain, and leave the rest in whatever order.
            have helper : ∀ addr, addr = (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset) →
              (Eq ((List.take 16 (List.drop offset mem1_curr)).At addr) ⋆
              (Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
              (Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 16)) ⋆
              (Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
              (Eq ((List.take 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset)) ⋆
              (Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 16)) ⋆
              R)))))) state_data.dmem := by
              intro addr h_eq
              rw [h_eq]
              -- `ac_rfl` magically handles the reordering of the commutative/associative ⋆ operator
              exact cast (congrFun (by ac_rfl) _) h_mem_sep

            -- 2. Apply the helper. Lean unifies `addr` with the messy bit-blasted goal address!
            apply helper

            -- 3. Now your only goal is: MESSY_ADDR = s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset
            -- We rewrite backwards using the calculation theorem we hoisted globally.
            rw [← h_addr1_calc]

            -- 4. Unfold the register getters so both sides are just raw BitVec additions
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, BitVec.extractLsb', Width.bits]

            -- 5. Simplify the remaining BitVec/Int arithmetic to close the equality
            simp
        case h_len =>
          tactic =>
            -- 1. The RHS is a match statement that trivially evaluates to 16.
            -- We use `change` to replace it with 16 to help `omega`.
            change (List.take 16 (List.drop offset mem1_curr)).length = 16

            -- 2. Rewrite `(take n l).length` to `min n l.length`
            rw [List.length_take]

            -- 3. Substitute the known length of our dropped list (k * 16)
            rw [h_drop_len1]

            -- 4. Solve the arithmetic: min 16 (k * 16) = 16 (since k ≠ 0)
            omega
        case h_align =>
          tactic =>
            -- 1. The first argument is a match that trivially evaluates to 16.
            -- Use `change` to clean it up while leaving the messy address wildcarded.
            change isAligned 16 _ = true

            -- 2. Define a helper that parameterizes the messy address.
            -- (`convert` might help here too)
            have helper : ∀ addr, addr = (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset) →
              isAligned 16 addr = true := by
              intro addr h_eq
              rw [h_eq]
              exact h_addr1_aligned

            -- 3. Apply the helper. Lean unifies `addr` with the messy goal address!
            apply helper

            -- 4. Now your goal is: MESSY_ADDR = s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset
            -- We rewrite backwards using your calculation theorem
            rw [← h_addr1_calc]

            -- 5. Unfold the register getters so both sides are just BitVec additions
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, BitVec.extractLsb', Width.bits]

            -- 6. Simplify the remaining BitVec/Int arithmetic to close the equality
            simp
        -- ?R and ?bs go away after h_mem
        -- movaps xmm1, XMMWORD PTR [rsi+rdx*1+0]
        kstep 1
        case h_mem =>
          tactic =>
            -- 1. Define a helper that parameterizes the target address.
            -- This time, we pull the 16-byte chunk we want from mem2_curr to the front,
            -- leaving the mem1_curr chunks and the rest of the mem2_curr chunks behind.
            have helper : ∀ addr, addr = (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) →
              (Eq ((List.take 16 (List.drop offset mem2_curr)).At addr) ⋆
              (Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
              (Eq ((List.take 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset)) ⋆
              (Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 16)) ⋆
              (Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
              (Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 16)) ⋆
              R)))))) state_data.dmem := by
              intro addr h_eq
              rw [h_eq]
              -- `ac_rfl` again magically handles the commutative/associative reordering
              exact cast (congrFun (by ac_rfl) _) h_mem_sep

            -- 2. Apply the helper to unify `addr` with the messy bit-blasted goal address.
            apply helper

            -- 3. Rewrite backwards using the rsi calculation theorem we hoisted globally.
            rw [← h_addr2_calc]

            -- 4. Unfold the register getters so both sides are just raw BitVec additions.
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, BitVec.extractLsb', Width.bits]

            -- 5. Simplify the remaining BitVec/Int arithmetic to close the equality.
            simp
        case h_len =>
          tactic =>
            -- 1. The RHS is a match statement that trivially evaluates to 16.
            change (List.take 16 (List.drop offset mem2_curr)).length = 16

            -- 2. Rewrite `(take n l).length` to `min n l.length`
            rw [List.length_take]

            -- 3. Rewrite `(drop n l).length` to `l.length - n`
            rw [List.length_drop]

            -- 4. Substitute the known length of our array (len * 4)
            rw [h_len2]

            -- 5. Solve the arithmetic.
            -- omega knows offset = len * 4 - k * 16, so len * 4 - offset = k * 16.
            -- Since k ≠ 0, min 16 (k * 16) = 16.
            omega
        case h_align =>
          tactic =>
            -- 1. The first argument is a match that trivially evaluates to 16.
            -- Use `change` to clean it up while leaving the messy address wildcarded.
            change isAligned 16 _ = true

            -- 2. State that the rsi target address is 16-byte aligned.
            -- (Matches h_addr1_aligned from your first instruction)
            have h_addr2_aligned : isAligned 16 (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) = true := by
              -- Offset is a multiple of 16. Adding to aligned base maintains alignment.
              exact h_addr2_aligned

            -- cleanup: hike this out and merge with h_mem
            -- 3. State the address calculation for rsi + rdx.
            have h_addr2_calc : state_data.regs.get (Reg.low Reg64.rsi Width.W64) + state_data.regs.get (Reg.low Reg64.rdx Width.W64) = s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset := by
              rw [h_rsi, h_rdx]
              -- Bitvector arithmetic: base + len*4 - k*16 = base + offset
              rw [← h_rdx_val]
              dsimp only [offset]
              rw [BitVec.add_assoc]
              congr 1
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat]
              omega

            -- 4. Define the helper that parameterizes the messy address.
            have helper : ∀ addr, addr = (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) →
              isAligned 16 addr = true := by
              intro addr h_eq
              rw [h_eq]
              exact h_addr2_aligned

            -- 5. Apply the helper. Lean unifies `addr` with the messy goal address!
            apply helper

            -- 6. Rewrite backwards using your calculation theorem
            rw [← h_addr2_calc]

            -- 7. Unfold the register getters so both sides are just BitVec additions
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, BitVec.extractLsb', Width.bits]

            -- 8. Simplify the remaining BitVec/Int arithmetic to close the equality
            simp
        kstep 3  -- register/register ops

        kstep 1  -- movaps XMMWORD PTR [rsi+rdx*1+0], xmm2"
        case h_mem =>
          tactic =>
            -- 1. Define the helper. Since memory hasn't mutated yet, we just pull
            -- the mem2_curr target chunk to the front exactly like we did for the load!
            have helper : ∀ addr, addr = (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) →
              (Eq ((List.take 16 (List.drop offset mem2_curr)).At addr) ⋆
              (Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
              (Eq ((List.take 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset)) ⋆
              (Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 16)) ⋆
              (Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
              (Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 16)) ⋆
              R)))))) state_data.dmem := by
              intro addr h_eq
              rw [h_eq]
              -- `ac_rfl` continues to do the heavy lifting
              exact cast (congrFun (by ac_rfl) _) h_mem_sep

            -- 2. Apply the helper.
            apply helper

            -- 3. Rewrite backwards using the rsi calculation theorem.
            rw [← h_addr2_calc]

            -- 4. Unfold the register getters so both sides are raw BitVec additions.
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, BitVec.extractLsb', Width.bits]

            -- 5. Simplify to close the equality.
            simp
        case h_len =>
          tactic =>
            -- 1. The RHS is a match statement that trivially evaluates to 16.
            change (List.take 16 (List.drop offset mem2_curr)).length = 16

            -- 2. Rewrite `(take n l).length` to `min n l.length`
            rw [List.length_take]

            -- 3. Rewrite `(drop n l).length` to `l.length - n`
            rw [List.length_drop]

            -- 4. Substitute the known length of our array (len * 4)
            rw [h_len2]

            -- 5. Solve the arithmetic.
            -- omega knows offset = len * 4 - k * 16, so len * 4 - offset = k * 16.
            -- Since k ≠ 0, min 16 (k * 16) = 16.
            omega
        case h_align =>
          tactic =>
            -- 1. The first argument is a match that trivially evaluates to 16.
            -- Use `change` to clean it up while leaving the messy address wildcarded.
            change isAligned 16 _ = true

            -- 2. State that the rsi target address is 16-byte aligned.
            -- (Matches h_addr1_aligned from your first instruction)
            have h_addr2_aligned : isAligned 16 (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) = true := by
              -- Offset is a multiple of 16. Adding to aligned base maintains alignment.
              unfold isAligned at h_v2_aligned ⊢
              simp only [beq_iff_eq] at h_v2_aligned ⊢
              have h_offset_mod : offset % 16 = 0 := by omega
              rw [BitVec.toNat_add, BitVec.toNat_ofNat]
              omega

            -- cleanup: hike this out and merge with h_mem
            -- 3. State the address calculation for rsi + rdx.
            have h_addr2_calc : state_data.regs.get (Reg.low Reg64.rsi Width.W64) + state_data.regs.get (Reg.low Reg64.rdx Width.W64) = s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset := by
              rw [h_rsi, h_rdx]
              -- Bitvector arithmetic: base + len*4 - k*16 = base + offset
              rw [← h_rdx_val]
              dsimp only [offset]
              rw [BitVec.add_assoc]
              congr 1
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat]
              omega

            -- 4. Define the helper that parameterizes the messy address.
            have helper : ∀ addr, addr = (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) →
              isAligned 16 addr = true := by
              intro addr h_eq
              rw [h_eq]
              exact h_addr2_aligned

            -- 5. Apply the helper. Lean unifies `addr` with the messy goal address!
            apply helper

            -- 6. Rewrite backwards using your calculation theorem
            rw [← h_addr2_calc]

            -- 7. Unfold the register getters so both sides are just BitVec additions
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, BitVec.extractLsb', Width.bits]

            -- 8. Simplify the remaining BitVec/Int arithmetic to close the equality
            simp
        -- movaps XMMWORD PTR [rdi+rdx*1+0], xmm0
        kstep 1
        case h_mem =>
          tactic =>
            -- 1. We must first establish the separation logic state AFTER the first store.
            -- We reorder the original `h_mem_sep` to put the `rsi` chunk first so we can "execute" the first store.
            have h_mem_ready_for_store1 :
              (Eq ((List.take 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset)) ⋆
              (Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
              (Eq ((List.take 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset)) ⋆
              (Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 16)) ⋆
              (Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
              (Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 16)) ⋆
              R)))))) state_data.dmem := cast (congrFun (by ac_rfl) _) h_mem_sep

            -- 2. Define a helper that abstracts over the messy value (v_sub) and BOTH messy addresses.
            -- We assert that the NEW memory state (after the first store) has the `rdi` chunk at the front.
            have helper : ∀ addr1 addr2 (val : Int),
              addr1 = (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset) →
              addr2 = (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) →
              (Eq ((List.take 16 (List.drop offset mem1_curr)).At addr1) ⋆
              (Eq ((Int.toBytes 16 val).At addr2) ⋆
              (Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
              (Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 16)) ⋆
              (Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
              (Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 16)) ⋆
              R)))))) (Mem.storeInt state_data.dmem addr2 16 val) := by
              intro addr1 addr2 val h_eq1 h_eq2
              rw [h_eq1, h_eq2]
              -- Apply Mem.storeInt_sep to "execute" the first store logically
              have h_store1 := Mem.storeInt_sep (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) 16 (List.take 16 (List.drop offset mem2_curr)) _ state_data.dmem ⟨h_mem_ready_for_store1, h_len_take16_2⟩ val
              -- Use ac_rfl to pull the `rdi` chunk to the front of this new memory state
              exact cast (congrFun (by ac_rfl) _) h_store1

            -- 3. Apply the helper. Lean beautifully unifies addr1, addr2, and val with the messy goal state!
            apply helper

            -- 4. Provide the proofs for the two address equalities using our hoisted calculations
            · rw [← h_addr1_calc]
              dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, BitVec.extractLsb', Width.bits]
              simp
            · rw [← h_addr2_calc]
              dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, BitVec.extractLsb', Width.bits]
              simp
        case h_len =>
          tactic =>
            -- 1. Simplify the match statement on the RHS of the goal to 16
            change (List.take 16 (List.drop offset mem1_curr)).length = 16

            -- 2. Expand the length of the taken slice to `min 16 L.length`
            rw [List.length_take]

            -- 3. Substitute the known length of the dropped list from `h_drop_len1` (k * 16)
            rw [h_drop_len1]

            -- 4. Solve the arithmetic: min 16 (k * 16) = 16 (since k ≠ 0 implies k ≥ 1)
            omega
        case h_align =>
          tactic =>
            simp only [h_as] at *
            change isAligned 16 (BitVec.setWidth 64
              (have base := (BitVec.ofNat (match Width.W64 with | Width.W8 => 8 | Width.W16 => 16 | Width.W32 => 32 | Width.W64 => 64) state_data.regs.rdi.toNat).toInt;
               have idx := (BitVec.ofNat (match Width.W64 with | Width.W8 => 8 | Width.W16 => 16 | Width.W32 => 32 | Width.W64 => 64) state_data.regs.rdx.toNat).toInt * ↑1;
               BitVec.ofInt (match Width.W64 with | Width.W8 => 8 | Width.W16 => 16 | Width.W32 => 32 | Width.W64 => 64) base +
               BitVec.ofInt (match Width.W64 with | Width.W8 => 8 | Width.W16 => 16 | Width.W32 => 32 | Width.W64 => 64) idx +
               BitVec.ofInt (match Width.W64 with | Width.W8 => 8 | Width.W16 => 16 | Width.W32 => 32 | Width.W64 => 64) (Int64.toInt 0))) = true
            dsimp only
            have h_addr1_val : BitVec.setWidth 64
              (BitVec.ofInt 64 (BitVec.ofNat 64 state_data.regs.rdi.toNat).toInt +
               BitVec.ofInt 64 ((BitVec.ofNat 64 state_data.regs.rdx.toNat).toInt * 1) +
               BitVec.ofInt 64 (Int64.toInt 0)) = s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset := by
              -- Prove directly using h_addr1_calc
              rw [← h_addr1_calc]
              dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, BitVec.extractLsb', Width.bits]
              simp
              try bv_decide
            rw [h_addr1_val]
            exact h_addr1_aligned
        kstep 1  -- add
        -- added this weird break into tactic and back into sym here, otherwise I kept getting
        -- unknown free variable `_fvar.26333.287085` (the robot was no help here)
        tactic =>
        sym => kstep 1; tactic =>
        -- the robot really wanted to use v✝, so we'll clean things up first
        rename_i v_sub v_add v_rdx_next status_add
        rename_i h_split1 h_len_sum1 h_split2 h_len_sum2
        kdsimp_all
        -- clear_value v_sub v_add v_rdx_next status_add
        -- Clear split, alignment, and label equality helpers
        -- clear h_split1 h_len_sum1 h_split2 h_len_sum2 h_neq h_eq h_addr1_aligned h_addr1_calc
        -- clear h_rdx_val h_rdx rdx_val
        generalize h_branch : (v_rdx_next.msb != (v_rdx_next.toInt != 16 + state_data.regs.rdx.toBitVec.toInt)) = cond_loop
        -- 1. Split on k = 1 FIRST to make loop induction variable concrete
        by_cases h_last : k = 1
        · -- Case k = 1 (Loop terminates)
          -- 1. Prove that rdx is currently -16, so its next value is 0
          have h_rdx_eq : state_data.regs.rdx.toBitVec = -16#64 := by
            -- Grab the equality from the loop invariant
            have h := h_rdx
            -- Clean up the `>>> 0` and `ofNat (toNat ...)` noise
            simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat] at h
            -- Now h is exactly `state_data.regs.rdx.toBitVec = rdx_val`
            -- Substitute the known definition of rdx_val
            rw [← h_rdx_val] at h
            -- Substitute k = 1
            rw [h_last] at h
            -- The RHS is now `-BitVec.ofNat 64 (1 * 16)`, which is definitionally `-16#64`!
            exact h

          -- 2. Prove that the next rdx is 0
          have h_rdx_next_eq : v_rdx_next = 0#64 := by
            -- Unfold the let-binding
            dsimp only [v_rdx_next]
            -- Clean up the exact same noise
            simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat]
            -- Substitute our proven value for rdx (-16)
            rw [h_rdx_eq]
            -- The goal is now `16#64 + -16#64 = 0#64`. bv_decide crushes this!
            bv_decide

          have h_cond : cond_loop = false := by
            -- 1. Unfold cond_loop into the explicit boolean expression
            rw [← h_branch]

            -- 2. Substitute our known concrete bitvectors (0 and -16)
            rw [h_rdx_next_eq, h_rdx_eq]

            -- 3. The goal is now exactly:
            -- `(0#64).msb != ((0#64).toInt != 16 + (-16#64).toInt) = false`
            -- Since all variables are gone and it's purely concrete numbers, `decide` crushes it!
            decide

          -- 2. Collapse the loop condition branch
          rw [h_cond]
          simp only [Bool.false_eq_true, ↓reduceIte]

          -- 3. Simplify the empty Directives.interp to Effects.done
          dsimp only [Directives.interp]

          -- 4. Since the loop terminates and we are at the end PC, we can finish!
          apply Eventually.done

          -- 5. Expose and establish the k = 0 invariant
          unfold butterflies_float_invariant
          simp only [h_last, Nat.sub_self]

          -- Define the updated lists of bytes containing our newly computed float32 values
          let mem1_next := List.take offset mem1_curr ++ Int.toBytes 16 v_add.toInt
          let mem2_next := List.take offset mem2_curr ++ Int.toBytes 16 v_sub.toInt

          refine ⟨mem1_next, mem2_next, ?h_len1, ?h_len2, ?h_k_bound, ?h_mem_sep, ?h_rdi, ?h_rsi, ?h_rdx, ?h_pc⟩

          case h_len1 =>
            -- Prove mem1_next has length len * 4 (since offset = len*4 - 16 and chunk is 16)
            -- discharged by lean_agent
            change (List.take offset mem1_curr ++ Int.toBytes 16 v_add.toInt).length = len * 4
            rw [List.length_append]
            rw [Int.toBytes_length]
            have h_offset_le : offset ≤ mem1_curr.length := by
              dsimp [offset]
              omega
            rw [List.length_take_of_le h_offset_le]
            dsimp [offset]
            omega

          case h_len2 =>
            -- Prove mem2_next has length len * 4
            -- discharged by lean_agent
            change (List.take offset mem2_curr ++ Int.toBytes 16 v_sub.toInt).length = len * 4
            rw [List.length_append]
            rw [Int.toBytes_length]
            have h_offset_le : offset ≤ mem2_curr.length := by
              dsimp [offset]
              omega
            rw [List.length_take_of_le h_offset_le]
            dsimp [offset]
            omega

          case h_k_bound =>
            -- 0 * 16 <= len * 4
            omega

          case h_mem_sep =>
            -- 1. Clean up messy addresses using hoisted calculations
            have h_clean_addr1 : BitVec.setWidth 64
              (BitVec.ofInt 64 (BitVec.ofNat 64 state_data.regs.rdi.toNat).toInt +
               BitVec.ofInt 64 ((BitVec.ofNat 64 state_data.regs.rdx.toNat).toInt * ↑1) +
               BitVec.ofInt 64 (Int64.toInt 0)) = s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset := by
              rw [← h_addr1_calc]
              -- The terms are already fully bit-blasted, so we just simplify and decide it
              simp
              try bv_decide

            have h_clean_addr2 : BitVec.setWidth 64
              (BitVec.ofInt 64 (BitVec.ofNat 64 state_data.regs.rsi.toNat).toInt +
               BitVec.ofInt 64 ((BitVec.ofNat 64 state_data.regs.rdx.toNat).toInt * ↑1) +
               BitVec.ofInt 64 (Int64.toInt 0)) = s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset := by
              rw [← h_addr2_calc]
              simp
              try bv_decide

            -- 2. Define a monolithic helper that completely abstracts the messy goal state
            have helper : ∀ addr1 addr2 val1 val2,
              addr1 = (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset) →
              addr2 = (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) →
              val1 = v_add.toInt →
              val2 = v_sub.toInt →
              (Eq (mem1_next.At s₀.regs.rdi.toBitVec) ⋆ Eq (mem2_next.At s₀.regs.rsi.toBitVec) ⋆ R)
                (Mem.storeInt (Mem.storeInt state_data.dmem addr2 16 val2) addr1 16 val1) := by
              intro addr1 addr2 val1 val2 h_eq1 h_eq2 h_val1 h_val2
              rw [h_eq1, h_eq2, h_val1, h_val2]

              -- A. Execute Inner Store (rsi, val2) logically
              have h_inner_ready :
                (Eq ((List.take 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                (Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
                (Eq ((List.take 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                (Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + 16#64)) ⋆
                (Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
                (Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + 16#64)) ⋆
                R)))))) state_data.dmem := cast (congrFun (by ac_rfl) _) h_mem_sep

              have h_inner := Mem.storeInt_sep (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) 16
                (List.take 16 (List.drop offset mem2_curr)) _ state_data.dmem
                ⟨h_inner_ready, h_len_take16_2⟩ v_sub.toInt

              -- B. Execute Outer Store (rdi, val1) logically
              have h_outer_ready :
                (Eq ((List.take 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                (Eq ((Int.toBytes 16 v_sub.toInt).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                (Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
                (Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + 16#64)) ⋆
                (Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
                (Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + 16#64)) ⋆
                R)))))) (Mem.storeInt state_data.dmem (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) 16 v_sub.toInt) := cast (congrFun (by ac_rfl) _) h_inner

              have h_outer := Mem.storeInt_sep (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset) 16
                (List.take 16 (List.drop offset mem1_curr)) _ _
                ⟨h_outer_ready, h_len_take16_1⟩ v_add.toInt

              -- C. Prove the tail drops are completely empty (since k=1)
              have h_empty1 : List.drop 16 (List.drop offset mem1_curr) = [] := by
                apply List.drop_eq_nil_of_le
                rw [h_drop_len1, h_last]
                omega
              have h_empty2 : List.drop 16 (List.drop offset mem2_curr) = [] := by
                apply List.drop_eq_nil_of_le
                rw [h_drop_len2, h_last]
                omega

              rw [h_empty1, h_empty2] at h_outer

              -- E. Recombine the chunks logically backwards into mem1_next and mem2_next
              have h_fold1 : Eq (mem1_next.At s₀.regs.rdi.toBitVec) =
                (Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
                 Eq ((Int.toBytes 16 v_add.toInt).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset))) := by
                dsimp [mem1_next]
                -- Safely swap `offset` for the `.length` of the chunk so the theorem matches
                have h_subst : BitVec.ofNat 64 offset = BitVec.ofNat 64 (List.take offset mem1_curr).length := by rw [h_len_take1]
                rw [h_subst]
                rw [← Mem.At_append_sep]
                -- Discharge the separation capacity proof
                rw [h_len_take1, Int.toBytes_length]
                omega

              have h_fold2 : Eq (mem2_next.At s₀.regs.rsi.toBitVec) =
                (Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
                 Eq ((Int.toBytes 16 v_sub.toInt).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset))) := by
                dsimp [mem2_next]
                -- Same safe swap for mem2
                have h_subst : BitVec.ofNat 64 offset = BitVec.ofNat 64 (List.take offset mem2_curr).length := by rw [h_len_take2]
                rw [h_subst]
                rw [← Mem.At_append_sep]
                rw [h_len_take2, Int.toBytes_length]
                omega

              -- F. Pull the empty arrays to the front of h_outer, eliminate them, and fold!
              have h_final_ready :
                (Eq ([].At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + 16#64)) ⋆
                (Eq ([].At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + 16#64)) ⋆
                ((Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
                  Eq ((Int.toBytes 16 v_add.toInt).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset))) ⋆
                ((Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
                  Eq ((Int.toBytes 16 v_sub.toInt).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset))) ⋆
                R)))) (Mem.storeInt (Mem.storeInt state_data.dmem (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) 16 v_sub.toInt) (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset) 16 v_add.toInt) := cast (congrFun (by ac_rfl) _) h_outer

              rw [h_empty_sep, h_empty_sep, ← h_fold1, ← h_fold2] at h_final_ready
              exact cast (congrFun (by ac_rfl) _) h_final_ready

            -- 3. Apply the helper and let Lean unify the massive goal state with addr1, addr2, val1, val2
            apply helper
            · exact h_clean_addr1
            · exact h_clean_addr2
            · -- Prove val1 is exactly v_add
              dsimp [AvxReg.base]
              apply congrArg BitVec.toInt
              clear_value v_add v_sub
              unfold BitVec.replaceLow BitVec.drop
              -- 1. Isolate the logic into a tiny lemma
              have h_trunc : ∀ (A : BitVec 384) (B : BitVec 128),
                BitVec.ofNat 128 (BitVec.setWidth 512 (BitVec.append A B)).toNat = B := by
                intro A B
                -- 2. Erase `.toNat` using `change`. Because we are inside the tiny lemma,
                -- this runs instantly and completely bypasses the recursion depth limit!
                change (BitVec.setWidth 512 (BitVec.append A B)).setWidth 128 = B
                -- 3. Now bv_decide only sees pure BitVecs and crushes it
                bv_decide
              -- 4. Syntactically rewrite the giant goal, avoiding deep typechecking
              rw [h_trunc]

            · -- Prove val2 is exactly v_sub
              dsimp [AvxReg.base]
              apply congrArg BitVec.toInt
              clear_value v_add v_sub
              unfold BitVec.replaceLow BitVec.drop
              have h_trunc : ∀ (A : BitVec 384) (B : BitVec 128),
                BitVec.ofNat 128 (BitVec.setWidth 512 (BitVec.append A B)).toNat = B := by
                intro A B
                change (BitVec.setWidth 512 (BitVec.append A B)).setWidth 128 = B
                bv_decide
              rw [h_trunc]

          case h_rdi =>
            -- Pointer rdi is still pointing at the end of the array
            -- discharged by lean_agent (iirc)
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb'] at *
            simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat] at h_rdi ⊢
            rw [h_rdi_val]
            exact h_rdi

          case h_rsi =>
            -- Pointer rsi is still pointing at the end of the array
            -- discharged by lean_agent (iirc)
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb'] at *
            simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat] at h_rsi ⊢
            exact h_rsi

          case h_rdx =>
            -- 1. Unfold the register getters so the LHS collapses to just `v_rdx_next`
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb']

            -- 2. Substitute our known value for the next rdx state (which is 0)
            rw [h_rdx_next_eq]

            -- 3. The goal is now `(0#64).extractLsb' ... = -BitVec.ofNat 64 (0 * 16)`.
            -- This is a trivial BitVec arithmetic identity!
            bv_decide

          case h_pc =>
            -- 1. Evaluate the `if True` branch since k = 1
            simp only [if_true]
            unfold butterflies_float_end_pc

            -- 2. Fully evaluate all list traversals.
            -- This tells Lean to unroll the AST, build the list of PC tuples,
            -- and execute `findSome?` and `getLast?` until they yield the raw additions.
            simp [Layout.apply, List.mapIdx, List.mapIdx.go, butterflies_float_prog,
                  Executable.withAddresses, List.findSome?, List.getLast?, Option.getD]

            -- 3. Both sides are now syntactically identical ASTs of `Int64` additions!
            -- (e.g. `((start + s0) + s1) ... + s13 = ((start + s0) + s1) ... + s13`)
            -- rfl - don't need this.

        · -- Case k > 1 (Loop continues)
          have h_k_gt_one : k > 1 := by omega
          have h_rdx_clean : BitVec.ofNat 64 ((BitVec.ofNat 64 (state_data.regs.rdx.toBitVec.toNat >>> 0)).toNat >>> 0) = state_data.regs.rdx.toBitVec := by
            simp only [Nat.shiftRight_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          have h_rdx_val_clean : state_data.regs.rdx.toBitVec = -BitVec.ofNat 64 (k * 16) := by
            have h1 : BitVec.ofNat 64 ((BitVec.ofNat (64 - 0) (state_data.regs.rdx.toBitVec.toNat >>> 0)).toNat >>> 0) = state_data.regs.rdx.toBitVec := by
              simp only [Nat.shiftRight_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
            rw [← h1, h_rdx]
            exact h_rdx_val.symm

          have h_rdx_next_toInt : v_rdx_next.toInt = -((k - 1) * 16 : Nat) := by
            unfold v_rdx_next
            rw [h_rdx_clean, h_rdx_val_clean]
            have h_bv_step : BitVec.ofNat 64 (k * 16) = BitVec.ofNat 64 ((k - 1) * 16) + 16#64 := by
              have h_eq : BitVec.ofInt 64 ((k * 16 : Nat) : Int) = BitVec.ofInt 64 (((k - 1) * 16 : Nat) : Int) + BitVec.ofInt 64 16 := by
                rw [← BitVec.ofInt_add]
                congr 1
                omega
              exact h_eq
            rw [h_bv_step]
            have h_eq_bv : 16#64 + -(BitVec.ofNat 64 ((k - 1) * 16) + 16#64) = -BitVec.ofNat 64 ((k - 1) * 16) := by
              generalize hY : BitVec.ofNat 64 ((k - 1) * 16) = Y
              clear hY
              bv_decide
            rw [h_eq_bv]
            have h_arith : (((k : Int) - 1) * 16) = (((k - 1) * 16 : Nat) : Int) := by omega
            have h_neg_eq : -BitVec.ofNat 64 ((k - 1) * 16) = -BitVec.ofInt 64 (((k : Int) - 1) * 16) := h_neg_eq_aux k (by omega)
            rw [h_neg_eq]
            rw [← BitVec.ofInt_neg]
            have h_bounds_check : -(2^(64 - 1) : Int) ≤ -(((k : Int) - 1) * 16) ∧ -(((k : Int) - 1) * 16) < (2^(64 - 1) : Int) := by
              clear inv
              have h_len_bound_eval : len * 4 < 2147483648 := h_len_bound
              have h_k_limit : (k - 1) * 16 < 2147483648 := by omega
              constructor <;> omega
            have h_eq_self := @BitVec.toInt_ofInt_eq_self 64 (by decide) (-(((k : Int) - 1) * 16)) h_bounds_check.left h_bounds_check.right
            rw [h_eq_self]
            omega

          have h_rdx_toInt : state_data.regs.rdx.toBitVec.toInt = -(k * 16 : Nat) := by
            have h_rdx_simp : state_data.regs.rdx.toBitVec = rdx_val := by
              rw [h_rdx_clean] at h_rdx
              exact h_rdx
            rw [h_rdx_simp]
            rw [← h_rdx_val]
            have h_neg_eq2 : -BitVec.ofNat 64 (k * 16) = -BitVec.ofInt 64 (k * 16) := by
              apply congrArg
              apply BitVec.eq_of_toNat_eq
              simp [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
              omega
            rw [h_neg_eq2]
            rw [← BitVec.ofInt_neg]
            have h_bounds_check2 : -(2^(64 - 1) : Int) ≤ -((k : Int) * 16) ∧ -((k : Int) * 16) < (2^(64 - 1) : Int) := by
              clear inv
              have h_len_bound_eval : len * 4 < 2147483648 := h_len_bound
              have h_k_limit2 : k * 16 < 2147483648 := by omega
              constructor <;> omega
            have h_eq_self2 := @BitVec.toInt_ofInt_eq_self 64 (by decide) (-((k : Int) * 16)) h_bounds_check2.left h_bounds_check2.right
            rw [h_eq_self2]
            omega


          have h_toInt_eq : v_rdx_next.toInt = 16 + state_data.regs.rdx.toBitVec.toInt := by
            rw [h_rdx_next_toInt, h_rdx_toInt]
            omega

          have h_msb : v_rdx_next.msb = true := by
            by_cases h_msb_eq : v_rdx_next.msb
            · exact h_msb_eq
            · have h_msb_false : v_rdx_next.msb = false :=
                Bool.eq_false_of_ne_true h_msb_eq
              have h_toInt_def : v_rdx_next.toInt = v_rdx_next.toNat :=
                BitVec.toInt_eq_toNat_of_msb h_msb_false
              have h_lt_zero : v_rdx_next.toInt < 0 := by
                rw [h_rdx_next_toInt]
                omega
              have h_ge_zero : v_rdx_next.toInt >= 0 := by
                rw [h_toInt_def]
                omega
              omega

          have h_cond : cond_loop = true := by
            rw [← h_branch]
            rw [h_toInt_eq]
            simp only [ne_eq, bne_self_eq_false, Bool.not_false, Bool.bne_false]
            rw [h_msb]
          -- 2. Collapse the branch using the decidable if_pos lemma
          rw [if_pos h_cond]

          -- 3. Since we've completed one full loop iteration,
          -- we re-establish the loop invariant for (k - 1)
          apply Eventually.done

          -- 4. Expose the invariant for the decremented step (k - 1)
          unfold butterflies_float_invariant

          -- Since k > 1, k - 1 is not zero, so the PC will correctly point to the "loop" label
          have h_k_minus_one_nz : ¬(k - 1) = 0 := by omega
          simp only [h_k_minus_one_nz, ↓reduceIte]

          -- Define the updated lists of bytes containing our newly computed float32 values
          let mem1_next := List.take offset mem1_curr ++ Int.toBytes 16 v_add.toInt ++ List.drop 16 (List.drop offset mem1_curr)
          let mem2_next := List.take offset mem2_curr ++ Int.toBytes 16 v_sub.toInt ++ List.drop 16 (List.drop offset mem2_curr)

          refine ⟨mem1_next, mem2_next, ?h_len1, ?h_len2, ?h_k_bound, ?h_mem_sep, ?h_rdi, ?h_rsi, ?h_rdx, ?h_pc⟩

          case h_len1 =>
            -- 1. Explicitly unfold mem1_next in the goal
            change (List.take offset mem1_curr ++ Int.toBytes 16 v_add.toInt ++ List.drop 16 (List.drop offset mem1_curr)).length = len * 4

            -- 2. Rewrite the lengths of the concatenated lists step-by-step
            rw [List.length_append, List.length_append]
            rw [Int.toBytes_length]
            rw [List.length_drop, List.length_drop]

            -- 3. Prove that offset ≤ mem1_curr.length so we can rewrite List.take
            have h_offset_le : offset ≤ mem1_curr.length := by
              unfold offset
              omega
            rw [List.length_take_of_le h_offset_le]

            -- 4. Substitute the known length of mem1_curr and let omega solve the arithmetic
            rw [h_len1]
            unfold offset
            omega

          case h_len2 =>
            -- 1. Explicitly unfold mem2_next in the goal
            change (List.take offset mem2_curr ++ Int.toBytes 16 v_sub.toInt ++ List.drop 16 (List.drop offset mem2_curr)).length = len * 4

            -- 2. Rewrite the lengths of the concatenated lists step-by-step
            rw [List.length_append, List.length_append]
            rw [Int.toBytes_length]
            rw [List.length_drop, List.length_drop]

            -- 3. Prove that offset ≤ mem2_curr.length so we can rewrite List.take
            have h_offset_le : offset ≤ mem2_curr.length := by
              unfold offset
              omega
            rw [List.length_take_of_le h_offset_le]

            -- 4. Substitute the known length of mem2_curr and let omega solve the arithmetic
            rw [h_len2]
            unfold offset
            omega

          case h_k_bound =>
            -- Expose the k * 16 ≤ len * 4 bound and use omega to subtract 16 from both sides
            have h_step : (k - 1) * 16 ≤ k * 16 := by
              apply Nat.mul_le_mul_right
              omega
            omega

          case h_mem_sep =>
            -- 1. Clean up messy addresses using hoisted calculations
            have h_clean_addr1 : BitVec.setWidth 64
              (BitVec.ofInt 64 (BitVec.ofNat 64 state_data.regs.rdi.toNat).toInt +
               BitVec.ofInt 64 ((BitVec.ofNat 64 state_data.regs.rdx.toNat).toInt * ↑1) +
               BitVec.ofInt 64 (Int64.toInt 0)) = s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset := by
              rw [← h_addr1_calc]
              -- The terms are already fully bit-blasted, so we just simplify!
              simp
              try bv_decide

            have h_clean_addr2 : BitVec.setWidth 64
              (BitVec.ofInt 64 (BitVec.ofNat 64 state_data.regs.rsi.toNat).toInt +
               BitVec.ofInt 64 ((BitVec.ofNat 64 state_data.regs.rdx.toNat).toInt * ↑1) +
               BitVec.ofInt 64 (Int64.toInt 0)) = s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset := by
              rw [← h_addr2_calc]
              simp
              try bv_decide

            -- 2. Define the monolithic helper
            have helper : ∀ addr1 addr2 val1 val2,
              addr1 = (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset) →
              addr2 = (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) →
              val1 = v_add.toInt →
              val2 = v_sub.toInt →
              (Eq (mem1_next.At s₀.regs.rdi.toBitVec) ⋆ Eq (mem2_next.At s₀.regs.rsi.toBitVec) ⋆ R)
                (Mem.storeInt (Mem.storeInt state_data.dmem addr2 16 val2) addr1 16 val1) := by
              intro addr1 addr2 val1 val2 h_eq1 h_eq2 h_val1 h_val2
              rw [h_eq1, h_eq2, h_val1, h_val2]

              -- A. Execute Inner Store (rsi, val2) logically
              have h_inner_ready :
                (Eq ((List.take 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                (Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
                (Eq ((List.take 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                (Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + 16#64)) ⋆
                (Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
                (Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + 16#64)) ⋆
                R)))))) state_data.dmem := cast (congrFun (by ac_rfl) _) h_mem_sep

              have h_inner := Mem.storeInt_sep (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) 16
                (List.take 16 (List.drop offset mem2_curr)) _ state_data.dmem
                ⟨h_inner_ready, h_len_take16_2⟩ v_sub.toInt

              -- B. Execute Outer Store (rdi, val1) logically
              have h_outer_ready :
                (Eq ((List.take 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                (Eq ((Int.toBytes 16 v_sub.toInt).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                (Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
                (Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + 16#64)) ⋆
                (Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
                (Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + 16#64)) ⋆
                R)))))) (Mem.storeInt state_data.dmem (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) 16 v_sub.toInt) := cast (congrFun (by ac_rfl) _) h_inner

              have h_outer := Mem.storeInt_sep (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset) 16
                (List.take 16 (List.drop offset mem1_curr)) _ _
                ⟨h_outer_ready, h_len_take16_1⟩ v_add.toInt

              -- C. Recombine the three chunks of mem1 logically backwards into mem1_next
              have h_fold1 : (Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
                 (Eq ((Int.toBytes 16 v_add.toInt).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                  Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + 16#64)))) =
                 Eq (mem1_next.At s₀.regs.rdi.toBitVec) := by
                dsimp [mem1_next]
                -- First fold the inner two chunks (toBytes ++ drop)
                have h_inner_fold : (Eq ((Int.toBytes 16 v_add.toInt).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset)) ⋆ Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + 16#64))) = Eq ((Int.toBytes 16 v_add.toInt ++ List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset)) := by
                  have h_sub2 : 16#64 = BitVec.ofNat 64 (Int.toBytes 16 v_add.toInt).length := by rw [Int.toBytes_length]
                  rw [h_sub2, ← Mem.At_append_sep]
                  rw [Int.toBytes_length, List.length_drop, h_drop_len1]; omega
                rw [h_inner_fold]
                -- Now fold the outer chunk (take ++ (toBytes ++ drop))
                have h_sub1 : BitVec.ofNat 64 offset = BitVec.ofNat 64 (List.take offset mem1_curr).length := by rw [h_len_take1]
                rw [h_sub1, ← Mem.At_append_sep]
                · rw [← List.append_assoc] -- <--- FIX IS HERE: shift parentheses!
                · rw [h_len_take1, List.length_append, Int.toBytes_length, List.length_drop, h_drop_len1]; omega

              -- D. Recombine the three chunks of mem2 logically backwards into mem2_next
              have h_fold2 : (Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
                 (Eq ((Int.toBytes 16 v_sub.toInt).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                  Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + 16#64)))) =
                 Eq (mem2_next.At s₀.regs.rsi.toBitVec) := by
                dsimp [mem2_next]
                have h_inner_fold : (Eq ((Int.toBytes 16 v_sub.toInt).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset)) ⋆ Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + 16#64))) = Eq ((Int.toBytes 16 v_sub.toInt ++ List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset)) := by
                  have h_sub2 : 16#64 = BitVec.ofNat 64 (Int.toBytes 16 v_sub.toInt).length := by rw [Int.toBytes_length]
                  rw [h_sub2, ← Mem.At_append_sep]
                  rw [Int.toBytes_length, List.length_drop, h_drop_len2]; omega
                rw [h_inner_fold]
                have h_sub1 : BitVec.ofNat 64 offset = BitVec.ofNat 64 (List.take offset mem2_curr).length := by rw [h_len_take2]
                rw [h_sub1, ← Mem.At_append_sep]
                · rw [← List.append_assoc] -- <--- FIX IS HERE: shift parentheses!
                · rw [h_len_take2, List.length_append, Int.toBytes_length, List.length_drop, h_drop_len2]; omega

              -- E. Reorder `h_outer` to group the chunks, apply the folds, and close the goal!
              have h_final_ready :
                ((Eq ((List.take offset mem1_curr).At s₀.regs.rdi.toBitVec) ⋆
                  (Eq ((Int.toBytes 16 v_add.toInt).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                   Eq ((List.drop 16 (List.drop offset mem1_curr)).At (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset + 16#64)))) ⋆
                ((Eq ((List.take offset mem2_curr).At s₀.regs.rsi.toBitVec) ⋆
                  (Eq ((Int.toBytes 16 v_sub.toInt).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset)) ⋆
                   Eq ((List.drop 16 (List.drop offset mem2_curr)).At (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset + 16#64)))) ⋆
                R)) (Mem.storeInt (Mem.storeInt state_data.dmem (s₀.regs.rsi.toBitVec + BitVec.ofNat 64 offset) 16 v_sub.toInt) (s₀.regs.rdi.toBitVec + BitVec.ofNat 64 offset) 16 v_add.toInt) := cast (congrFun (by ac_rfl) _) h_outer

              rw [h_fold1, h_fold2] at h_final_ready
              exact cast (congrFun (by ac_rfl) _) h_final_ready

            -- 3. Apply the helper and let Lean unify the massive goal state with addr1, addr2, val1, val2
            apply helper
            · exact h_clean_addr1
            · exact h_clean_addr2
            · dsimp [AvxReg.base]
              apply congrArg BitVec.toInt
              clear_value v_add v_sub
              unfold BitVec.replaceLow BitVec.drop
              have h_trunc : ∀ (A : BitVec 384) (B : BitVec 128), BitVec.ofNat 128 (BitVec.setWidth 512 (BitVec.append A B)).toNat = B := by
                intro A B; change (BitVec.setWidth 512 (BitVec.append A B)).setWidth 128 = B; bv_decide
              rw [h_trunc]
            · dsimp [AvxReg.base]
              apply congrArg BitVec.toInt
              clear_value v_add v_sub
              unfold BitVec.replaceLow BitVec.drop
              have h_trunc : ∀ (A : BitVec 384) (B : BitVec 128), BitVec.ofNat 128 (BitVec.setWidth 512 (BitVec.append A B)).toNat = B := by
                intro A B; change (BitVec.setWidth 512 (BitVec.append A B)).setWidth 128 = B; bv_decide
              rw [h_trunc]


          case h_rdi =>
            -- 1. Unfold register getters to expose the raw bitvectors
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb'] at *

            -- 2. Strip the bit-shift noise from h_rdi and the goal
            simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat] at h_rdi ⊢

            -- 3. Replace the arithmetic RHS in the goal with our generalized variable `rdi_val`
            rw [h_rdi_val]

            -- 4. Now the goal is exactly h_rdi!
            exact h_rdi

          case h_rsi =>
            -- 1. Unfold register getters to expose the raw bitvectors
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb'] at *

            -- 2. Strip the bit-shift noise from h_rsi and the goal
            simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat] at h_rsi ⊢

            -- 3. The goal is now exactly the hypothesis h_rsi!
            exact h_rsi

          case h_rdx =>
            -- 1. Unfold register getters and our let-binding
            dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop, BitVec.extractLsb', v_rdx_next] at *

            -- 2. Clean up the `>>> 0` and `64 - 0` noise
            simp only [Nat.shiftRight_zero, Nat.sub_zero, BitVec.ofNat_toNat] at h_rdx ⊢

            -- 3. Substitute -16k into h_rdx, and then into the goal
            rw [← h_rdx_val] at h_rdx
            rw [h_rdx]

            -- 4. Relate the k*16 and (k-1)*16 bitvectors
            have h_bv_step : BitVec.ofNat 64 (k * 16) = BitVec.ofNat 64 ((k - 1) * 16) + 16#64 := by
              have h_eq : BitVec.ofInt 64 ((k * 16 : Nat) : Int) = BitVec.ofInt 64 (((k - 1) * 16 : Nat) : Int) + BitVec.ofInt 64 16 := by
                rw [← BitVec.ofInt_add]
                congr 1
                omega
              exact h_eq

            -- 5. Substitute this relationship into the goal
            rw [h_bv_step]

            -- 6. The goal is now `16#64 + -(X + 16#64) = -X`.
            -- We abstract the exact term into a variable `Y` so bv_decide isn't confused by `k`.
            generalize hY : BitVec.ofNat 64 ((k - 1) * 16) = Y
            clear hY

            -- 7. bv_decide instantly bit-blasts and proves the algebraic identity!
            bv_decide

          case h_pc =>
            -- Prove the new PC value equals the "loop" label PC (since the jump was taken)
            rfl
