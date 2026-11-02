/-
**A prologue keeps `wc_worker`'s and the thread worker's argument registers** (AArch64; at
`wc_worker` and the thread worker): the stack check, the limit's load into `x10`, the check's branch and the frame's
set-up write none of `x0`, `x2 .. x5`, so a prologue's states lie inside any `W` determined by the entry's values
of those registers. Shared by `A64HelloPlacedZWc` (`wz_placed`) and `A64HelloPlacedZKid` (`zT_placed`).

- `ArgR`: `x0`, `x2 .. x5`.
- `keepA_chkHead`, `keepA_chkBr`, `keepA_frameSet`, `keepA_chkRegs`, `keepA_ldStep`: those registers kept by each
  piece of a prologue.
- `proW_args`: a prologue's states inside `W` from its entry's argument registers.
-/
import Spike.Lib.A64HelloPlacedZEnv
import Spike.Lib.A64HelloWorkerSegRP

namespace Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker

/-! ## A prologue's states -/

section Pro

set_option linter.unusedSimpArgs false

variable {lab : Label → Int64}

/-- The argument registers of `wc_worker`'s packet: `x0`, `x2`, `x3`, `x4`, `x5`. -/
def ArgR (r : XReg) : Prop := r = .X0 ∨ r = .X2 ∨ r = .X3 ∨ r = .X4 ∨ r = .X5

/-- The argument registers kept by the stack check's head. -/
theorem keepA_chkHead (Z : Int64) (r : XReg) (hr : ArgR r) :
    ∀ d ∈ chkHead Z, ∀ am : AM, (dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r := by
  simp only [chkHead, List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rintro d (rfl | rfl) ⟨pc, o, σ⟩ <;> dstep_keep <;>
    simp [Spike.Lib.rm, Spike.Lib.A64.Flow.regDst]

/-- The argument registers kept by the stack check's branch. -/
theorem keepA_chkBr (L : Label) (r : XReg) (hr : ArgR r) :
    ∀ d ∈ chkBr L, ∀ am : AM, (dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r := by
  simp only [chkBr, List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rintro d (rfl | rfl) ⟨pc, o, σ⟩ <;> dstep_keep <;>
    simp [Spike.Lib.rm, Spike.Lib.A64.Flow.regDst]

/-- The argument registers kept by the frame's set-up and the parameters' stores. -/
theorem keepA_frameSet (Z : Int64) (ps : List (XReg × Int64)) (r : XReg) (hr : ArgR r) :
    ∀ d ∈ frameSet Z ps, ∀ am : AM, (dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r := by
  intro d hd am
  simp only [frameSet, List.mem_append, List.mem_map] at hd
  rcases hd with hd | ⟨q, -, rfl⟩
  · simp only [frSetup, List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain ⟨pc, o, σ⟩ := am
    rcases hd with rfl | rfl | rfl | rfl
    all_goals
      simp only [dstep, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly, Spike.Lib.A64.Flow.AI.so,
      Spike.Lib.A64.Flow.AI.step, Spike.Lib.A64.Flow.AI.tgt, Spike.Lib.A64.Flow.soReg, Spike.Lib.A64.Flow.regRes,
      spStr, Reg64s.getRegOrZr_X, Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp,
      Reg64s.setRegOrSp64, ConstExpr.interp, Spike.Lib.A64.Flow.SO.set, ExtOrImmReg.interp, Reg64s.getRegOrSp,
      Reg64s.getRegOrSp64, RegOrSp.base, Spike.Lib.A64.Flow.SO.get, MachineData.setRegOrZr, Reg64s.setRegOrZr,
      Reg64s.setRegOrZr64, Spike.Lib.A64.Flow.zrB, Spike.Lib.A64.Flow.SO.write, Spike.Lib.A64.Flow.SO.kill,
      Spike.Lib.A64.Flow.SO.killZ, Spike.Lib.rm, Spike.Lib.A64.Flow.regDst]
    all_goals rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
  · obtain ⟨pc, o, σ⟩ := am
    rw [dstep_spStr]

theorem keepA_chkRegs (Z : Int64) (rr : Reg64s) (r : XReg) (hr : ArgR r) :
    (chkRegs Z rr).getXReg r = rr.getXReg r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem keepA_ldStep (v : BitVec 64) (σ : AS) (r : XReg) (hr : ArgR r) :
    (ldStep .X10 v σ).regs.getXReg r = σ.regs.getXReg r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **A prologue's states inside `W`** from its entry's: every control of the entry invariant `J` in `W` at
every state agreeing with the entry's on the argument registers (`hW`); the prologue writes none of them
(`chkRegs`, the limit's load into `x10`, the check's branch, the frame's set-up). -/
theorem proW_args {W : Frag isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : AS → Ctl → Prop}
    (hW : ∀ σ c, J σ c → ∀ s : State, (∀ r : XReg, ArgR r → s.st.1.regs.getXReg r = σ.regs.getXReg r) →
      W s c) :
    ProW W (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps J := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs, arun_take_reg r (keepA_chkHead Z r hr) k]
  · rintro s c ⟨-, -, -, -, σ1, hA, -, σ, hJ, rfl⟩
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    rw [hA.regs]
    exact keepA_chkRegs Z σ.regs r hr
  · rintro s σ2 c _ _ _ _ _ _ ⟨σ, v, hJ, -, rfl⟩ k _ m hA' _
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs, arun_take_reg r (keepA_chkBr L r hr) k, keepA_ldStep _ _ r hr]
    exact keepA_chkRegs Z σ.regs r hr
  · rintro s σ3 c _ _ _ _ _ _ ⟨σ, v, hJ, -, he, -⟩ k _ m hA' _
    refine ⟨hW σ c hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs, arun_take_reg r (keepA_frameSet Z ps r hr) k, he, keepA_ldStep _ _ r hr]
    exact keepA_chkRegs Z σ.regs r hr

end Pro

/-- `ArgR` is inhabited (non-vacuity). -/
example : ArgR .X0 := Or.inl rfl

end Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepA_chkHead' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepA_chkHead

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepA_chkBr' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepA_chkBr

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepA_frameSet' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepA_frameSet

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepA_chkRegs' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepA_chkRegs

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepA_ldStep' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.keepA_ldStep

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.proW_args' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.proW_args
