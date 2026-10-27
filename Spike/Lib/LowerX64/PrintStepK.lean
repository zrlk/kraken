/-
**The slots along `print`'s argument block** (x86-64): every proper
prefix of the block's cells before and after the multiply keeps the static
offsets `oB` and every slot but the block's fresh registers' (`olo`, `os`
before the multiply; `ocap`, `okk` after it), at any cell sizes.

- `StepK`, `arun_take_stepK`: a directive stepping past its cell, the
  offsets kept, the slots off a set `W` kept; every prefix of a block of such
  directives;
- `stepK_getOp`, `stepK_st`, `stepK_reg`: an operand's load, the store into
  a slot of `W`, a register operation;
- `preD_take`, `postD_take`: the prefixes of `print`'s argument block.
-/
import Spike.Lib.LowerX64.PrintCall
import Spike.Lib.LowerX64.PlacedBlk

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Emit.X64 (Item)

set_option linter.unusedSimpArgs false

/-- **A directive stepping past its cell**, the static offsets `o` kept,
every slot off `W` kept, at any pc, cell size and state. -/
def StepK (lab : String → Int64) (o : SO) (W : Int → Prop) (d : Directive) : Prop :=
  ∀ pc z σ, ∃ σ' : AS, arun lab [(d, z)] ⟨pc, o, σ⟩ = ⟨pc + Int64.ofNat z, o, σ'⟩ ∧
    ∀ j, ¬ W j → σ'.slot j = σ.slot j

/-- **Every prefix of a block of `StepK` directives** keeps the offsets and
the slots off `W`. -/
theorem arun_take_stepK {lab : String → Int64} {o : SO} {W : Int → Prop} :
    ∀ {ds : List Directive}, (∀ d ∈ ds, StepK lab o W d) →
    ∀ (zs : List Nat) (k : Nat) (pc : Int64) (σ : AS), ∃ (pc' : Int64) (σ' : AS),
      arun lab ((ds.zip zs).take k) ⟨pc, o, σ⟩ = ⟨pc', o, σ'⟩ ∧ ∀ j, ¬ W j → σ'.slot j = σ.slot j
  | [], _, zs, k, pc, σ => ⟨pc, σ, by simp [arun], fun _ _ => rfl⟩
  | _ :: _, _, [], k, pc, σ => ⟨pc, σ, by simp [arun], fun _ _ => rfl⟩
  | _ :: _, _, _ :: _, 0, pc, σ => ⟨pc, σ, by simp [arun], fun _ _ => rfl⟩
  | d :: ds, h, z :: zs, k + 1, pc, σ => by
    obtain ⟨σ1, e1, h1⟩ := h d (List.mem_cons_self ..) pc z σ
    obtain ⟨pc', σ', e', h'⟩ :=
      arun_take_stepK (fun d hd => h d (List.mem_cons_of_mem _ hd)) zs k (pc + Int64.ofNat z) σ1
    refine ⟨pc', σ', ?_, fun j hj => (h' j hj).trans (h1 j hj)⟩
    rw [List.zip_cons_cons, List.take_succ_cons]
    have e2 : dstep lab ⟨pc, o, σ⟩ (d, z) = ⟨pc + Int64.ofNat z, o, σ1⟩ := e1
    show List.foldl (dstep lab) (dstep lab ⟨pc, o, σ⟩ (d, z)) ((ds.zip zs).take k) = _
    rw [e2]
    exact e'

theorem StepK.mono {lab : String → Int64} {o : SO} {W W' : Int → Prop} {d : Directive} (h : StepK lab o W d)
    (hW : ∀ j, W j → W' j) : StepK lab o W' d := fun pc z σ =>
  let ⟨σ', e, hs⟩ := h pc z σ
  ⟨σ', e, fun j hj => hs j fun h => hj (hW j h)⟩

/-- **A register operation** (classified, writing no slot, not a branch,
keeping the offsets) is `StepK`. -/
theorem stepK_reg {lab : String → Int64} {o : SO} {W : Int → Prop} {d : Directive} {a : AI}
    (hc : classify d = some a) (hw : a.slotWr = false) (ht : a.isTerm = false) (hso : a.so o = o) :
    StepK lab o W d := fun pc z σ =>
  ⟨a.step o (pc + Int64.ofNat z) σ, by
    show dstep lab ⟨pc, o, σ⟩ (d, z) = _
    simp only [dstep, hc, AI.tgt_of_not_term ht, hso], fun j _ => by rw [AI.step_slot hw]⟩

section Frame

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (lab : String → Int64)

include hf h1 in
/-- **An operand's load** is `StepK`. -/
theorem stepK_getOp {W : Int → Prop} {t : Reg64} (ht : t ≠ .rbp) {a : Scc.IR.Operand} {l : List Item}
    (ha : getOp fr t a = .ok l) : ∀ d ∈ dirs l, StepK lab (oB fr) W d := by
  obtain ⟨d, hd⟩ := dirs_getOp ha
  rw [hd]
  intro d' hd' pc z σ
  rw [List.mem_singleton] at hd'
  subst hd'
  obtain ⟨v, -, e⟩ := arun_getOp hf h1 ht ha lab pc σ (zs := [z]) (by simp [hd])
  rw [hd] at e
  exact ⟨{ σ with regs := σ.regs.set64 t v }, by simpa using e, fun _ _ => rfl⟩

include hf h1 in
/-- **The store into a slot of `W`** is `StepK`. -/
theorem stepK_st {W : Int → Prop} {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) (hW : W off) :
    StepK lab (oB fr) W (stDir off) := by
  intro pc z σ
  obtain ⟨σ', e, rfl⟩ := runsP_st hf h1 lab hd σ [z] pc rfl
  refine ⟨_, by simpa using e, fun j hj => ?_⟩
  have : ¬ j = off := fun h => hj (h ▸ hW)
  simp only [upd_apply, this, ↓reduceIte]

theorem stepK_ext32 {W : Int → Prop} : StepK lab (oB fr) W ext32D := fun pc z σ =>
  ⟨_, arun_ext32D (oB_kill fr (by decide)) lab pc σ z, fun _ _ => rfl⟩

theorem stepK_add {W : Int → Prop} : StepK lab (oB fr) W addD := fun pc z σ =>
  let ⟨_, e⟩ := arun_addD (oB_kill fr (by decide)) lab pc σ z
  ⟨_, e, fun _ _ => rfl⟩

theorem stepK_cmp {W : Int → Prop} : StepK lab (oB fr) W cmpD :=
  stepK_reg rfl rfl rfl (by simp [AI.so, soReg, regDst, oB, SO.write, SO.kill, rm, Reg.base])

theorem stepK_movRsi {W : Int → Prop} : StepK lab (oB fr) W movRsiD :=
  stepK_reg rfl rfl rfl (by simp [AI.so, soReg, regDst, oB, SO.write, SO.kill, rm, Reg.base, SO.get, lk])

theorem stepK_cmov {W : Int → Prop} : StepK lab (oB fr) W (cmovD .c) :=
  stepK_reg rfl rfl rfl (by simp [AI.so, soReg, regDst, oB, SO.write, SO.kill, rm, Reg.base, Scc.Emit.X64.rax64, Scc.Emit.X64.lw])

include hf h1 in
/-- **Every prefix of `print`'s argument block before the multiply** keeps
the offsets and every slot but `lo`'s and `s`'s. -/
theorem preD_take {lo s : Scc.IR.Reg} {olo os : Int} (hlo : rsOf fr lo = some olo) (hs : rsOf fr s = some os)
    {o b m : Scc.IR.Operand} {lO lB lL lM l8 : List Item} (hO : getOp fr .rax o = .ok lO)
    (hB : getOp fr .rax b = .ok lB) (hL : getOp fr .rcx (.reg lo) = .ok lL) (hM : getOp fr .rax m = .ok lM)
    (h8 : getOp fr .rcx (Scc.Lower.imm 8) = .ok l8) (zs : List Nat) (k : Nat) (pc : Int64) (σ : AS) :
    ∃ (pc' : Int64) (σ' : AS), arun lab (((preD lO lB lL lM l8 olo os).zip zs).take k) ⟨pc, oB fr, σ⟩ =
      ⟨pc', oB fr, σ'⟩ ∧ ∀ j, j ≠ olo → j ≠ os → σ'.slot j = σ.slot j := by
  have hK : ∀ d ∈ preD lO lB lL lM l8 olo os, StepK lab (oB fr) (fun j => j = olo ∨ j = os) d := by
    intro d hd
    simp only [preD, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with ((h | rfl | rfl) | ((h | h) | rfl | rfl)) | (h | h)
    · exact stepK_getOp hf h1 lab (by decide) hO d h
    · exact stepK_ext32 lab
    · exact stepK_st hf h1 lab hlo (.inl rfl)
    · exact stepK_getOp hf h1 lab (by decide) hB d h
    · exact stepK_getOp hf h1 lab (by decide) hL d h
    · exact stepK_add lab
    · exact stepK_st hf h1 lab hs (.inr rfl)
    · exact stepK_getOp hf h1 lab (by decide) hM d h
    · exact stepK_getOp hf h1 lab (by decide) h8 d h
  obtain ⟨pc', σ', e, h⟩ := arun_take_stepK hK zs k pc σ
  exact ⟨pc', σ', e, fun j h1 h2 => h j (by rintro (h | h) <;> contradiction)⟩

include hf h1 in
/-- **Every prefix of `print`'s argument block after the multiply** keeps
the offsets and every slot but `cap`'s and `k`'s. -/
theorem postD_take {cap kk : Scc.IR.Reg} {ocap okk : Int} (hcap : rsOf fr cap = some ocap)
    (hk : rsOf fr kk = some okk) {s n : Scc.IR.Operand} {lN lC lN' lC' lS lK : List Item}
    (hN : getOp fr .rdx n = .ok lN) (hC : getOp fr .rsi (.reg cap) = .ok lC) (hN' : getOp fr .rax n = .ok lN')
    (hC' : getOp fr .rcx (.reg cap) = .ok lC') (hS : getOp fr .rdi s = .ok lS) (hK : getOp fr .rsi (.reg kk) = .ok lK)
    (zs : List Nat) (k : Nat) (pc : Int64) (σ : AS) :
    ∃ (pc' : Int64) (σ' : AS), arun lab (((postD lN lC lN' lC' lS lK ocap okk).zip zs).take k) ⟨pc, oB fr, σ⟩ =
      ⟨pc', oB fr, σ'⟩ ∧ ∀ j, j ≠ ocap → j ≠ okk → σ'.slot j = σ.slot j := by
  have hK' : ∀ d ∈ postD lN lC lN' lC' lS lK ocap okk, StepK lab (oB fr) (fun j => j = ocap ∨ j = okk) d := by
    intro d hd
    simp only [postD, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with (rfl | ((((h | h) | h) | h) | rfl | rfl | rfl | rfl)) | (h | h)
    · exact stepK_st hf h1 lab hcap (.inl rfl)
    · exact stepK_getOp hf h1 lab (by decide) hN d h
    · exact stepK_getOp hf h1 lab (by decide) hC d h
    · exact stepK_getOp hf h1 lab (by decide) hN' d h
    · exact stepK_getOp hf h1 lab (by decide) hC' d h
    · exact stepK_cmp lab
    · exact stepK_movRsi lab
    · exact stepK_cmov lab
    · exact stepK_st hf h1 lab hk (.inr rfl)
    · exact stepK_getOp hf h1 lab (by decide) hS d h
    · exact stepK_getOp hf h1 lab (by decide) hK d h
  obtain ⟨pc', σ', e, h⟩ := arun_take_stepK hK' zs k pc σ
  exact ⟨pc', σ', e, fun j h1 h2 => h j (by rintro (h | h) <;> contradiction)⟩

end Frame

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.arun_take_stepK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.arun_take_stepK

/-- info: 'Spike.Lib.LowerX64.StepK.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.StepK.mono

/-- info: 'Spike.Lib.LowerX64.stepK_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stepK_reg

/-- info: 'Spike.Lib.LowerX64.stepK_getOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stepK_getOp

/-- info: 'Spike.Lib.LowerX64.stepK_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stepK_st

/-- info: 'Spike.Lib.LowerX64.stepK_ext32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stepK_ext32

/-- info: 'Spike.Lib.LowerX64.stepK_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stepK_add

/-- info: 'Spike.Lib.LowerX64.stepK_cmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stepK_cmp

/-- info: 'Spike.Lib.LowerX64.stepK_movRsi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stepK_movRsi

/-- info: 'Spike.Lib.LowerX64.stepK_cmov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stepK_cmov

/-- info: 'Spike.Lib.LowerX64.preD_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.preD_take

/-- info: 'Spike.Lib.LowerX64.postD_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.postD_take
