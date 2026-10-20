/-
**`vcgen` rules for the 16-byte accesses at absolute symbol operands
`(sym)`, x64**. Additive companion of
`Kraken/EnvVCGen.lean` (the `d(%b)` forms) and `Kraken/EnvVCGenAbs.lean`
(the 32-bit `(sym)` forms; `absAddr`,
`AddrExpr.zeroExtend_interp_abs_label`).

`movdqa` checks 16-byte alignment and, off `dmem`, is one atomic 16-byte
access (`AvxOperation.interp`, `atomic := w == .W128`; `toEv` makes it one
16-byte event); `lock cmpxchg16b` is one 16-byte `rmw .acqRel`
(`MachineData.rmw16K`). The rules below are EnvWPRules' `movdqa_load_shared`,
`movdqa_store_shared` and `lock_cmpxchg16b_shared` with the address
`s.regs.get64 b + d.toBitVec` replaced by `absAddr l`, all `@[spec]` (an
absolute operand names a shared location):

- `movdqa_load_abs_shared_spec`: `movdqa (sym), %xmm`;
- `movdqa_store_abs_shared_spec`: `movdqa %xmm, (sym)`;
- `lock_cmpxchg16b_abs_shared_spec`: `lock cmpxchg16b (sym)`.
-/
import Kraken.EnvVCGenAbs

open Kraken
open Std.WP
open Lean.Order

section X64VecAbsSpecs

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- Unfold the fall-through address past one instruction cell (a copy of
`EnvVCGen.lean`'s private `after_instr`). -/
private theorem after_instr_vec {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

set_option hygiene false in
/-- One cell (a copy of `EnvVCGen.lean`'s local `env_step`). -/
local macro "env_step_vec" : tactic =>
  `(tactic| (
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr_vec hseg]
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩))

omit [CodeEnv] in
private theorem w128_beq_vec : (AvxWidth.W128 == AvxWidth.W128) = true := rfl

/-- `movdqa (sym), %xmm` on a shared location: the symbol must be 16-byte
aligned; one atomic 16-byte load (`movdqa_load_shared_spec` at `(sym)`). -/
@[spec] theorem MachineWP.movdqa_load_abs_shared_spec (x : RegMm) (l : Label) :
    ⦃ fun s g =>
        let a := absAddr l
        (isAligned 16 a = true) ⊓ (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.load .plain false a 16) g ⊓
          (∀ v g', env.step (.load .plain false a 16) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with zmms := s.zmms.setLegacy (.xmm x) v } g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movdqa (.avx (.xmm x)) (.mem ⟨none, none, .label l⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨⟨hal, hnone⟩, hok⟩, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step_vec
    simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
      MachineData.loadAvx, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      AddrExpr.zeroExtend_interp_abs_label, AvxWidth.bytes, AvxWidth.bits,
      hal, hnone, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, w128_beq_vec,
      Effects.AllEnv]
    simp only [BitVec.setWidth_eq]
    exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `movdqa %xmm, (sym)` on a shared location: the symbol must be 16-byte
aligned; one atomic 16-byte store (`movdqa_store_shared_spec` at `(sym)`). -/
@[spec] theorem MachineWP.movdqa_store_abs_shared_spec (x : RegMm) (l : Label) :
    ⦃ fun s g =>
        let a := absAddr l
        let v := s.zmms.get (.xmm x)
        (isAligned 16 a = true) ⊓ (Mem.loadInt s.dmem a 16 = none) ⊓
          env.ok (.store .plain false a 16 v) g ⊓
          (∀ ok g', env.step (.store .plain false a 16 v) g ok g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.avx .W64 .W128
          (.movdqa (.mem ⟨none, none, .label l⟩) (.avx (.xmm x)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨⟨hal, hnone⟩, hok⟩, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step_vec
    simp only [Directive.interp, Instr.interp, AvxOperation.interp, AvxRegOrMem.interp,
      MachineData.storeAvx, MachineData.setAvxLegacy,
      AddrExpr.zeroExtend_interp_abs_label, AvxWidth.bytes, AvxWidth.bits,
      hal, hnone, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, w128_beq_vec,
      Effects.AllEnv]
    simp only [BitVec.setWidth_eq]
    exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `lock cmpxchg16b (sym)` on a shared location: the symbol must be 16-byte
aligned; one atomic 16-byte `rmw .acqRel` writing `rcx:rbx` if the old value
is `rdx:rax` (`lock_cmpxchg16b_shared_spec` at `(sym)`). -/
@[spec] theorem MachineWP.lock_cmpxchg16b_abs_shared_spec (l : Label) :
    ⦃ fun s g =>
        let a := absAddr l
        let acc := s.regs.get64 .rdx ++ s.regs.get64 .rax
        let op := fun old : BitVec 128 =>
          if old == acc then some (s.regs.get64 .rcx ++ s.regs.get64 .rbx) else none
        (isAligned 16 a = true) ⊓ (Mem.loadInt s.dmem a 16 = none) ⊓ env.ok (.rmw .acqRel a 16 op) g ⊓
          (∀ old g', env.step (.rmw .acqRel a 16 op) g old g' →
            (old = acc → WP.wp (⟨p⟩ : EnvProgram env) Q E
                { s with status := { s.status with zf := true } } g')
            ⊓ (old ≠ acc → WP.wp (⟨p⟩ : EnvProgram env) Q E
                { s with
                    regs := (s.regs.set64 .rax (old.extractLsb' 0 64)).set64 .rdx (old.extractLsb' 64 64),
                    status := { s.status with zf := false } } g')) ⦄
      (⟨Directive.instr (.avx .W64 .W128 (.cmpxchg16b true ⟨none, none, .label l⟩)) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨⟨hal, hnone⟩, hok⟩, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step_vec
    simp only [Directive.interp, Instr.interp, AvxOperation.interp, MachineData.rmw16K,
      AddrExpr.zeroExtend_interp_abs_label, hal, hnone, ite_true, Effects.AllEnv]
    refine ⟨hok, fun old g' hs => ?_⟩
    obtain ⟨heq, hne⟩ := hk old g' hs
    by_cases h : old = s.regs.get64 .rdx ++ s.regs.get64 .rax
    · have hb : (old == s.regs.get64 .rdx ++ s.regs.get64 .rax) = true := by simpa using h
      simp only [hb, ite_true]
      exact heq h _ hpl'
    · have hb : (old == s.regs.get64 .rdx ++ s.regs.get64 .rax) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ite_false]
      exact hne h _ hpl'

end X64VecAbsSpecs

#print axioms MachineWP.movdqa_load_abs_shared_spec
#print axioms MachineWP.movdqa_store_abs_shared_spec
#print axioms MachineWP.lock_cmpxchg16b_abs_shared_spec
