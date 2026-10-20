/-
**64-bit `vcgen` rules for absolute symbol operands `(sym)`, x64**
. Additive companion of `Kraken/EnvVCGenAbs.lean`
(32-bit rules only), for `treiber2.kl`'s `movq (top),%rax` and
`lock cmpxchgq %rbx,(top)`.

The rules are the `d(%b)` rules of `Kraken/EnvVCGen.lean`
(`mov_load_env_spec`, `mov_store_env_spec`, `lock_cmpxchg_shared_spec`) with
the address `s.regs.get64 b + d.toBitVec` replaced by `absAddr l`, the
label's address in the ambient code (`AddrExpr.zeroExtend_interp_abs_label`);
all `@[spec]`:

- `mov_load_abs_env_spec`: `movq (sym), %r`, mapped or shared;
- `mov_store_abs_env_spec`: `movq %r, (sym)`, mapped or shared;
- `lock_cmpxchg_abs_shared_spec`: `lock cmpxchgq %r, (sym)` on a shared
  location.

The `#guard_msgs` checks below confirm that the parser produces exactly the
directives the rules match.
-/
import Kraken.EnvVCGenAbs
import Kraken.X64.Parser

open Kraken
open Std.WP
open Lean.Order

section AbsSpecs64

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- Unfold the fall-through address past one instruction cell (a copy of
`EnvVCGen.lean`'s private `after_instr`). -/
private theorem after_instr64 {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

set_option hygiene false in
/-- One cell (a copy of `EnvVCGen.lean`'s local `env_step`). -/
local macro "env_step64" : tactic =>
  `(tactic| (
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr64 hseg]
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩))

/-- `movq (sym), %r`, mapped or shared: the register gets the 8 bytes at the
symbol's address (`mov_load_env_spec` at `(sym)`). -/
@[spec] theorem MachineWP.mov_load_abs_env_spec (r : Reg64) (l : Label) :
    ⦃ fun s g =>
        let a := absAddr l
        (Mem.loadInt s.dmem a 8 = none → env.ok (.load .plain false a 8) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt s.dmem a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 8 = none ∧
                ∃ v, env.step (.load .plain false a 8) g v g' ∧ x = v.setWidth 64) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with regs := s.regs.set64 r x } g') ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨none, none, .label l⟩)))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step64
    cases hl : Mem.loadInt s.dmem (absAddr l) 8 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
        AddrExpr.zeroExtend_interp_abs_label, Reg64s.set_low64, Width.bytes,
        hl, Effects.AllEnv]
      exact ⟨hok hl, fun v g' hs => hk _ g' (.inr ⟨hl, v, hs, rfl⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
        AddrExpr.zeroExtend_interp_abs_label, Reg64s.set_low64, Width.bytes,
        hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨w, hl, rfl, rfl⟩) _ hpl'

/-- `movq %r, (sym)`, mapped or shared (`mov_store_env_spec` at `(sym)`). -/
@[spec] theorem MachineWP.mov_store_abs_env_spec (l : Label) (r : Reg64) :
    ⦃ fun s g =>
        let a := absAddr l
        let v := (s.regs.get64 r).setWidth 128
        (Mem.loadInt s.dmem a 8 = none → env.ok (.store .plain false a 8 v) g) ⊓
          (∀ m g',
            ((Mem.loadInt s.dmem a 8).isSome = true ∧
                m = Mem.storeInt s.dmem a 8 (s.regs.get64 r).toInt ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 8 = none ∧ m = s.dmem ∧
                ∃ ok, env.step (.store .plain false a 8 v) g ok g') →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with dmem := m } g') ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨none, none, .label l⟩) (.regOrMem (.reg (.low r .W64))))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step64
    cases hl : Mem.loadInt s.dmem (absAddr l) 8 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.store,
        AddrExpr.zeroExtend_interp_abs_label, Reg64s.get_low64, Width.bytes,
        hl, Effects.AllEnv]
      exact ⟨hok hl, fun ok g' hs => hk s.dmem g' (.inr ⟨hl, rfl, ok, hs⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.store,
        AddrExpr.zeroExtend_interp_abs_label, Reg64s.get_low64, Width.bytes,
        hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨by rw [hl]; rfl, rfl, rfl⟩) _ hpl'

/-- `lock cmpxchgq %r, (sym)` on a shared location
(`lock_cmpxchg_shared_spec` at `(sym)`). -/
@[spec] theorem MachineWP.lock_cmpxchg_abs_shared_spec (l : Label) (r : Reg64) :
    ⦃ fun s g =>
        let a := absAddr l
        let acc := s.regs.get64 .rax
        let op := rmwOp128 .W64 (fun x => if x == acc then some (s.regs.get64 r) else none)
        (Mem.loadInt s.dmem a 8 = none) ⊓ env.ok (.rmw .acqRel a 8 op) g ⊓
          (∀ v g', env.step (.rmw .acqRel a 8 op) g v g' →
            let old := v.setWidth 64
            let dv := acc - old
            let status := StatusFlags.from_result dv
              { cf := dv.unsigned != acc.unsigned - old.unsigned,
                af := (dv.take 4).unsigned != (acc.take 4).unsigned - (old.take 4).unsigned,
                of := dv.signed != acc.signed - old.signed }
            (old = acc → WP.wp (⟨p⟩ : EnvProgram env) Q E { s with status } g')
            ⊓ (old ≠ acc → WP.wp (⟨p⟩ : EnvProgram env) Q E
                { s with regs := s.regs.set64 .rax old, status } g')) ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.cmpxchg true (.mem ⟨none, none, .label l⟩) (.low r .W64))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hnone, hok⟩, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step64
    simp only [Directive.interp, Instr.interp, Operation.interp,
      RegOrMem.rmw, MachineData.rmwK, MachineData.setReg,
      AddrExpr.zeroExtend_interp_abs_label, Reg64s.get_low64,
      Reg64s.set_low64, Width.bytes, hnone, Effects.AllEnv, ite_true]
    refine ⟨hok, fun v g' hs => ?_⟩
    obtain ⟨heq, hne⟩ := hk v g' hs
    by_cases h : v.setWidth 64 = s.regs.get64 .rax
    · have hb : (v.setWidth 64 == s.regs.get64 .rax) = true := by simpa using h
      simp only [hb, ite_true]
      exact heq h _ hpl'
    · have hb : (v.setWidth 64 == s.regs.get64 .rax) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ite_false]
      exact hne h _ hpl'

end AbsSpecs64

/-! ## The parser produces the matched directives -/

open Kraken.X64.Parser in
example : (parse("movq (top),%rax") : Program) =
    [Directive.instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.regOrMem (.mem ⟨none, none, .label "top"⟩))))] := by
  decide

open Kraken.X64.Parser in
example : (parse("movq %rax,(top)") : Program) =
    [Directive.instr (.regular .W64 .W64 (.mov (.mem ⟨none, none, .label "top"⟩) (.regOrMem (.reg (.low .rax .W64)))))] := by
  decide

open Kraken.X64.Parser in
example : (parse("lock cmpxchgq %rbx,(top)") : Program) =
    [Directive.instr (.regular .W64 .W64 (.cmpxchg true (.mem ⟨none, none, .label "top"⟩) (.low .rbx .W64)))] := by
  decide
