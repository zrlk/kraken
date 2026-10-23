/-
**The saturating `-`** (x64): `.subSat` (`Scc/Emit/X64.lean`, `emitInst`)
emits `mov oa(%rbp), %rax; mov ob(%rbp), %rcx; sub %rcx, %rax;
movl $0, %edx; cmovb %rdx, %rax; mov %rax, od(%rbp)` (`subSeq`, copied
here as data with the cells' sizes as parameters, as in `Spike.Lib.X64`).

`seg_sub` is the `Seg` judgement from the entry of the sequence to its
exit: the two slot loads, the `sub` and the `movl` stutter, the source takes
its local step for `let x = a - b in e` at the `cmovb`, and the slot store
places `x`. Any operand words: the target's truncated difference represents
the source's truncated `subW` (`Scc.Sem.valRep_subW`), so no typing is
needed (the AArch64 analogue is `Spike.Lib.A64.seg_sub`).
-/
import Spike.Lib.X64Block
import Scc.Sem.TypingRows
import Kraken.X64.Parser
open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (ValRep)
open Kraken.X64.Parser

namespace Spike.Lib.X64

set_option linter.unusedSimpArgs false

/-- `sub %rcx, %rax`. -/
abbrev opSub : Operation .W64 := .sub (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .rcx .W64)))
/-- `movl $0, %edx` (zero-extended into `%rdx`, flags kept). -/
abbrev opMovl0 : Operation .W32 := .mov (.reg (.low .rdx .W32)) (.imm (.int64 (Int64.ofInt 0)))
/-- `cmovb %rdx, %rax`. -/
abbrev opCmovb : Operation .W64 := .cmovcc .c (.low .rax .W64) (.reg (.low .rdx .W64))

/-- `sub`'s result: the truncated difference. -/
theorem regRes_sub_rax (m : MachineData) :
    (regRes opSub m).regs.get (.low .rax .W64) = m.regs.get (.low .rax .W64) - m.regs.get (.low .rcx .W64) := by
  simp [regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set]

/-- `sub`'s carry: a borrow, the unsigned `%rax` below `%rcx`. -/
theorem regRes_sub_cf (m : MachineData) :
    (regRes opSub m).status.cf =
      decide ((m.regs.get (.low .rax .W64)).toNat < (m.regs.get (.low .rcx .W64)).toNat) := by
  simp [regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set,
    StatusFlags.from_result]
  have := m.regs.rax.toNat_lt; have := m.regs.rcx.toNat_lt
  rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; omega

/-- `movl $0, %edx` zeroes `%rdx`. -/
theorem regRes_movl0_rdx (m : MachineData) : (regRes opMovl0 m).regs.get (.low .rdx .W64) = 0#64 := by
  simp [regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set,
    ConstExpr.interp]

/-- `movl $0, %edx` keeps `%rax`. -/
theorem regRes_movl0_rax (m : MachineData) :
    (regRes opMovl0 m).regs.get (.low .rax .W64) = m.regs.get (.low .rax .W64) := by
  simp [regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set]

/-- `movl $0, %edx` keeps the flags. -/
theorem regRes_movl0_status (m : MachineData) : (regRes opMovl0 m).status = m.status := by
  simp [regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set]

/-- `cmovb %rdx, %rax`: `%rdx` on carry, else `%rax`. -/
theorem regRes_cmovb_rax (m : MachineData) :
    (regRes opCmovb m).regs.get (.low .rax .W64) =
      if m.status.cf then m.regs.get (.low .rdx .W64) else m.regs.get (.low .rax .W64) := by
  simp [regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set,
    CondCode.interp]


/-- A register operation keeps the private memory. -/
theorem regRes_dmem {w : Width} {op : Operation w} (h : RegOnly op = true) (m : MachineData) :
    (regRes op m).dmem = m.dmem := by
  rw [regRes_eq h m]

/-- The register operations as directives. -/
abbrev dSub : Directive := op64 opSub
abbrev dMovl0 : Directive := .instr (.regular .W64 .W32 opMovl0)
abbrev dCmovb : Directive := op64 opCmovb

/-- The saturating `-` of slots `oa` and `ob` into slot `od`, the cells of
sizes `z0` … `z5`. -/
def subSeq (oa ob od : Int64) (z0 z1 z2 z3 z4 z5 : Nat) : List (Directive × Nat) :=
  [(dLd .rax oa, z0), (dLd .rcx ob, z1), (dSub, z2), (dMovl0, z3), (dCmovb, z4), (dSt .rax od, z5)]

/-- The sequence is what the parser makes of the emitter's text. -/
example : subSeq (-32) (-40) (-96) 4 4 3 5 4 4 = (parse("movq -32(%rbp), %rax
movq -40(%rbp), %rcx
subq %rcx, %rax
movl $0, %edx
cmovb %rdx, %rax
movq %rax, -96(%rbp)")).zip [4, 4, 3, 5, 4, 4] := by decide

section Sub

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {F : Frame}
  {slot : String → Option Int64}

/-- The source term of `-`. -/
def subTerm (x a b : String) (e : Expr) : Expr := .let_ x (.sub (.var a) (.var b)) e

/-- **Entry of `-`.** -/
def SubIn (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x a b : String) (e : Expr) (oa ob od : Int64) (z0 z1 z2 z3 z4 z5 : Nat) (env0 : TermRun.Env) :
    Frag isa := fun s c =>
  s.st.2 = pc ∧ CodeAt s pc (subSeq oa ob od z0 z1 z2 z3 z4 z5) ∧ c = ⟨subTerm x a b e, env0, none⟩ ∧
    Slots lbl F slot s env0

/-- **Exit of `-`**: the source at `e` with `x` bound to the difference
`w`, placed at slot `od`. -/
def SubOut (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x : String) (e : Expr) (oa ob od : Int64) (z0 z1 z2 z3 z4 z5 : Nat) (env0 : TermRun.Env)
    (w : TermRun.Word) : Frag isa := fun s c =>
  s.st.2 = pc + Int64.ofNat (z0 + z1 + z2 + z3 + z4 + z5) ∧ CodeAt s pc (subSeq oa ob od z0 z1 z2 z3 z4 z5) ∧
    c = ⟨e, (x, .int, [w]) :: env0, none⟩ ∧
    Slots lbl F (fun y => if y = x then some od else slot y) s ((x, .int, [w]) :: env0)

/-- **The saturating `-` simulates the source's `-`**: two slot loads, `sub`
and `movl` (the source stutters), `cmovb` (the source's local step) and the
slot store. -/
theorem seg_sub {pc : Int64} {x a b : String} {e : Expr} {oa ob od : Int64} {z0 z1 z2 z3 z4 z5 : Nat}
    {env0 : TermRun.Env} (ha : slot a = some oa) (hb : slot b = some ob) {ta tb : Ty} {wa wb : TermRun.Word}
    (hla : TermRun.lookupE env0 a = some (ta, [wa])) (hlb : TermRun.lookupE env0 b = some (tb, [wb]))
    (hod : F.Off od) (hfree : ∀ y, slot y = some od → y = x) :
    Seg p lbl ms (SubIn lbl F slot pc x a b e oa ob od z0 z1 z2 z3 z4 z5 env0)
      (SubOut lbl F slot pc x e oa ob od z0 z1 z2 z3 z4 z5 env0 (TermRun.subW wa wb)) := by
  have hea : TermRun.evalAt env0 (.var a) = some (ta, [wa]) := by simpa [TermRun.evalAt] using hla
  have heb : TermRun.evalAt env0 (.var b) = some (tb, [wb]) := by simpa [TermRun.evalAt] using hlb
  let Pre (k : Nat) (s : State) (c : Ctl) : Prop :=
    s.st.2 = pc + Int64.ofNat k ∧ CodeAt s pc (subSeq oa ob od z0 z1 z2 z3 z4 z5) ∧ Slots lbl F slot s env0
  refine Seg.seq (Q := fun (s : State) (c : Ctl) => Pre z0 s c ∧ c = ⟨subTerm x a b e, env0, none⟩ ∧
      ValRep lbl wa.val (s.st.1.regs.get (.low .rax .W64)).toNat) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => Pre (z0 + z1) s c ∧ c = ⟨subTerm x a b e, env0, none⟩ ∧
      ValRep lbl wa.val (s.st.1.regs.get (.low .rax .W64)).toNat ∧
      ValRep lbl wb.val (s.st.1.regs.get (.low .rcx .W64)).toNat) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => Pre (z0 + z1 + z2) s c ∧ c = ⟨subTerm x a b e, env0, none⟩ ∧ ∃ va vb,
      ValRep lbl wa.val va ∧ ValRep lbl wb.val vb ∧ (s.st.1.status.cf = true → va < vb) ∧
      (s.st.1.status.cf = false → (s.st.1.regs.get (.low .rax .W64)).toNat = va - vb)) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => Pre (z0 + z1 + z2 + z3) s c ∧
      c = ⟨subTerm x a b e, env0, none⟩ ∧ ∃ va vb,
      ValRep lbl wa.val va ∧ ValRep lbl wb.val vb ∧ (s.st.1.status.cf = true → va < vb) ∧
      (s.st.1.status.cf = false → (s.st.1.regs.get (.low .rax .W64)).toNat = va - vb) ∧
      s.st.1.regs.get (.low .rdx .W64) = 0#64) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => Pre (z0 + z1 + z2 + z3 + z4) s c ∧
      c = ⟨e, (x, .int, [TermRun.subW wa wb]) :: env0, none⟩ ∧
      ValRep lbl (TermRun.subW wa wb).val (s.st.1.regs.get (.low .rax .W64)).toNat) (Seg.step ?_)
      (Seg.step ?_)))))
  · rintro s c ⟨hpc, hcode, rfl, hS⟩
    refine out_ld (hcode.cell0 rfl rfl hpc) hS ha fun ty w j hl hval => ?_
    rw [hla] at hl
    cases hl
    exact ⟨⟨by simp [hpc], hcode.after _ _, hS.regs rfl (by simp) rfl⟩, rfl, by simpa using hval⟩
  · rintro s c ⟨⟨hpc, hcode, hS⟩, rfl, hx⟩
    refine out_ld (hcode.cell (j := 1) rfl rfl rfl
      (by rw [hpc]; simp [cellOff, subSeq])) hS hb fun ty w j hl hval => ?_
    rw [hlb] at hl
    cases hl
    exact ⟨⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _, hS.regs rfl (by simp) rfl⟩, rfl,
      by simpa using hx, by simpa using hval⟩
  · rintro s c ⟨⟨hpc, hcode, hS⟩, rfl, hx, hy⟩
    have hc := hcode.cell (j := 2) rfl rfl rfl (by rw [hpc]; simp [cellOff, subSeq, Nat.add_assoc])
    refine .silent _ _ (exec_reg (by decide) hc) (.refl _) ?_
    refine ⟨⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _,
      hS.regs (regRes_dmem (by decide) _) (regRes_get64 (by decide) _ (by simp [regDst, Reg.base])) rfl⟩, rfl,
      _, _, hx, hy, fun hcar => ?_, fun hcar => ?_⟩
    · simpa [regRes_sub_cf] using hcar
    · simp only [regRes_sub_cf, decide_eq_false_iff_not, Nat.not_lt] at hcar
      rw [regRes_sub_rax, BitVec.toNat_sub, show 2 ^ Width.W64.bits = 2 ^ 64 from rfl]
      have : (s.st.1.regs.get (.low .rax .W64)).toNat < 2 ^ 64 := BitVec.isLt _
      have : (s.st.1.regs.get (.low .rcx .W64)).toNat < 2 ^ 64 := BitVec.isLt _
      omega
  · rintro s c ⟨⟨hpc, hcode, hS⟩, rfl, va, vb, hx, hy, hcar, hdif⟩
    have hc := hcode.cell (j := 3) rfl rfl rfl (by rw [hpc]; simp [cellOff, subSeq, Nat.add_assoc])
    refine .silent _ _ (exec_reg (by decide) hc) (.refl _) ?_
    refine ⟨⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _,
      hS.regs (regRes_dmem (by decide) _) (regRes_get64 (by decide) _ (by simp [regDst, Reg.base])) rfl⟩, rfl,
      va, vb, hx, hy, ?_, ?_, regRes_movl0_rdx _⟩
    · simpa [regRes_movl0_status] using hcar
    · simp only [after, regRes_movl0_status, regRes_movl0_rax]; exact hdif
  · rintro s c ⟨⟨hpc, hcode, hS⟩, rfl, va, vb, hx, hy, hcar, hdif, hdx⟩
    have hc := hcode.cell (j := 4) rfl rfl rfl (by rw [hpc]; simp [cellOff, subSeq, Nat.add_assoc])
    refine .silent _ _ (exec_reg (by decide) hc) (.single (localStep_sub rfl hea heb)) ?_
    refine ⟨⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _,
      hS.regs (regRes_dmem (by decide) _) (regRes_get64 (by decide) _ (by simp [regDst, Reg.base])) rfl⟩, rfl, ?_⟩
    have hv : ((regRes opCmovb s.st.1).regs.get (.low .rax .W64)).toNat = va - vb := by
      rw [regRes_cmovb_rax]
      cases hc' : s.st.1.status.cf
      · simpa using hdif hc'
      · have := hcar hc'
        simp only [Bool.true_eq_false, ↓reduceIte, hdx, BitVec.toNat_ofNat, Nat.zero_mod]
        omega
    show ValRep lbl _ ((regRes opCmovb s.st.1).regs.get (.low .rax .W64)).toNat
    rw [hv]
    exact Scc.Sem.valRep_subW hx hy
  · rintro s c ⟨⟨hpc, hcode, hS⟩, rfl, hv⟩
    refine out_st (hcode.cell (j := 5) rfl rfl rfl
      (by rw [hpc]; simp [cellOff, subSeq, Nat.add_assoc])) hS hod ?_
    exact ⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _, rfl,
      hS.store hod hfree hv rfl rfl rfl⟩

end Sub

end Spike.Lib.X64
