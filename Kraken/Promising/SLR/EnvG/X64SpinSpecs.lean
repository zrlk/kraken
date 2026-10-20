/-
**`vcgen` rules for the x64 spinlock worker**: the
three instruction shapes of `spinlock2.kl`'s worker that had no `vcgen`
rule. Not specific to `EnvG`: plain `MachineWP` / `EnvProgram` rules,
proved from the interpreter as their 64-bit / register-store siblings in
`Kraken/MachineWP.lean` and `Kraken/EnvVCGen.lean`.

- `test32_reg_reg_spec`: `testl %rb32, %ra32` (the 32-bit
  `MachineWP.test_reg_reg_spec`; `AF` is left undefined, so the tail must hold
  for either value).
- `xchg32_shared_spec`: `xchgl %r32, d(%b)` on a location outside `dmem`
  (the 32-bit `MachineWP.xchg_shared_spec`): one `rmw .acqRel` of 4 bytes that
  always writes.
- `mov32_store_imm_shared_spec`: `movl $i, d(%b)` on a location outside
  `dmem`: one `store .plain` of 4 bytes.
- `add32_reg_imm_spec`: `addl $i, %r32`.

**Moved.** The four rules now live next to their siblings, with
`@[spec]`: `MachineWP.add32_reg_imm_spec`, `MachineWP.test32_reg_reg_spec`
(`Kraken/MachineWP.lean`), `MachineWP.xchg32_shared_spec`,
`MachineWP.mov32_store_imm_shared_spec` (`Kraken/EnvVCGen.lean`). The names
here are statement-preserving aliases of those (`hoist_alias`,
`EnvG/Alias.lean`), without `@[spec]` (the rules are registered once, under
the `MachineWP` names). The helpers `fallthrough_nondet_spec'`,
`fallthrough_spec'` and `after_instr'` (public copies of the private
`fallthrough_nondet_spec` / `fallthrough_spec` / `after_instr` there) are
kept unchanged; the local `env_step'` macro, now unused, is gone.
-/
import Kraken.EnvVCGen
import Kraken.Promising.SLR.EnvG.Alias

open Kraken Std.WP Lean.Order

namespace Kraken.Promising.X64.EnvG.SpinSpecs

section Specs

open _root_.MachineWP

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {p : Program}

/-- Copy of `MachineWP.lean`'s private `fallthrough_nondet_spec`. -/
theorem fallthrough_nondet_spec' {α : Type} [NondetSupportingType α] {i : Instr}
    {f : MachineData → α → MachineData}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (P : MachineState → Prop),
      (∀ v : α, P (f s v, 0)) → (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All P) :
    ⦃ fun s => ∀ v : α, WP.wp p Q E (f s v) ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    have hafter : cenv.after pc (Directive.instr i :: p) = cenv.after (pc + .ofNat z) p := by
      simp only [Executable.after, hseg]
    rw [hafter]
    exact step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl (hcell s _ _ (fun v => h v _ hpl'))⟩

/-- Copy of `MachineWP.lean`'s private `fallthrough_spec`. -/
theorem fallthrough_spec' {i : Instr} {f : MachineData → MachineData}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (P : MachineState → Prop),
      P (f s, 0) → (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All P) :
    ⦃ fun s => WP.wp p Q E (f s) ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    have hafter : cenv.after pc (Directive.instr i :: p) = cenv.after (pc + .ofNat z) p := by
      simp only [Executable.after, hseg]
    rw [hafter]
    exact step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl (hcell s _ _ (h _ hpl'))⟩

end Specs

section SharedSpecs

open _root_.MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- Copy of `EnvVCGen.lean`'s private `after_instr`. -/
theorem after_instr' {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

end SharedSpecs

end Kraken.Promising.X64.EnvG.SpinSpecs

/-! The rules under their x64 names (aliases of the `MachineWP` rules). -/
hoist_alias [
  MachineWP.add32_reg_imm_spec ↦ Kraken.Promising.X64.EnvG.SpinSpecs.add32_reg_imm_spec,
  MachineWP.test32_reg_reg_spec ↦ Kraken.Promising.X64.EnvG.SpinSpecs.test32_reg_reg_spec,
  MachineWP.xchg32_shared_spec ↦ Kraken.Promising.X64.EnvG.SpinSpecs.xchg32_shared_spec,
  MachineWP.mov32_store_imm_shared_spec ↦ Kraken.Promising.X64.EnvG.SpinSpecs.mov32_store_imm_shared_spec]
