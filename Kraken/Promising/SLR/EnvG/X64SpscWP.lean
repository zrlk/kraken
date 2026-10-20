/-
**Part 0: the machine rules the SPSC code
needs and the existing rule set lacks** (new names only; hoist candidates for
`Kraken/MachineWP.lean` and `Kraken/EnvVCGen.lean`).

- `and32_reg_imm_spec` (`andl $i, %r32`) and `cmp32_reg_reg_spec`
  (`cmpl %rb32, %ra32`): register rules in the style of `MachineWP`'s
  `xor32_reg_reg_spec` / `cmp32_reg_imm_spec`. Through the generic rule
  (`envMonoX_lift_spec`) they serve the environment wp.
- `mov32_store_sib1_env_spec` (`movl %r32, (%b,%i,1)`) and
  `mov32_load_sib1_env_spec` (`movl (%b,%i,1), %r32`): the combined
  (mapped or shared) rules of `EnvVCGen`'s `mov32_store_env_spec` /
  `mov32_load_env_spec` at a base-plus-index address.

The private helpers of `MachineWP.lean` and `EnvVCGen.lean` (`wp_step`,
`after_instr`, `fallthrough_spec`, `fallthrough_nondet_spec`, `env_step`)
are restated locally.
-/
import Kraken.EnvVCGen
import Kraken.SharedEnvCounted

open Kraken
open Std.WP
open Lean.Order

namespace Kraken.Promising.X64.EnvG.SpscX

section Specs

open MachineWP

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

/-- Unfold the fall-through address past one instruction cell. -/
private theorem after_instr {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

private theorem step_here {post : @Post MachineState} {s : MachineData} {pc : Int64}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hseg : cenv.codeAt pc = (d, z) :: rest)
    (hall : cenv.stepAt d z (s, pc) (fun st => Eventually cenv.instrStep post st)) :
    Eventually cenv.instrStep post (s, pc) :=
  step_cps _ _ _ ⟨d, z, rest, hseg, hall⟩

private theorem fallthrough_spec {i : Instr} {f : MachineData → MachineData}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (P : MachineState → Prop),
      P (f s, 0) → (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All P) :
    ⦃ fun s => WP.wp p Q E (f s) ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    exact step_here hseg (Or.inl (hcell s _ _ (h _ hpl')))

private theorem fallthrough_nondet_spec {α : Type} [NondetSupportingType α] {i : Instr}
    {f : MachineData → α → MachineData}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (P : MachineState → Prop),
      (∀ v : α, P (f s v, 0)) → (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All P) :
    ⦃ fun s => ∀ v : α, WP.wp p Q E (f s v) ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    exact step_here hseg (Or.inl (hcell s _ _ (fun v => h v _ hpl')))

/-- `andl $i, %r32` : the 32-bit conjunction with the immediate's low half,
zero-extended into the register, and its flags, with `af` left arbitrary. -/
@[spec] theorem and32_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 32 &&& i.toBitVec.truncate 32
        ∀ af : Bool,
          WP.wp p Q E
            { s with
                regs := s.regs.set64 r (v.setWidth 64),
                status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32 (.and (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_nondet_spec (fun s rng P hP => by
    wp_step; simp only [Reg64s.get_low32, Reg64s.set_low32]; exact hP)

/-- `cmpl %rb32, %ra32` : the flags of the 32-bit difference `ra - rb`; no
register changes (`MachineWP.cmp32_reg_reg_spec`, `@[spec]`). -/
theorem cmp32_reg_reg_spec (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 ra).setWidth 32
        let b := (s.regs.get64 rb).setWidth 32
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned - b.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                  of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W32
          (.cmp (.reg (.low ra .W32)) (.regOrMem (.reg (.low rb .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  MachineWP.cmp32_reg_reg_spec asz ra rb

end Specs

section CombinedSpecs

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- Unfold the fall-through address past one instruction cell. -/
private theorem after_instr' {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

set_option hygiene false in
/-- One cell: place it, step it, and leave the `AllEnv` goal of its
fall-through tree, with the placement of the tail as `hpl'`. -/
local macro "env_step" : tactic =>
  `(tactic| (
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr' hseg]
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩))

/-- `movl %r32, (%b,%i,1)`, mapped or shared (`mov32_store_env_spec` at a
base-plus-index address). -/
@[spec] theorem mov32_store_sib1_env_spec (b i r : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i
        let v := ((s.regs.get64 r).setWidth 32).setWidth 128
        (Mem.loadInt s.dmem a 4 = none → env.ok (.store .plain false a 4 v) g) ⊓
          (∀ m g',
            ((Mem.loadInt s.dmem a 4).isSome = true ∧
                m = Mem.storeInt s.dmem a 4 ((s.regs.get64 r).setWidth 32).toInt ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 4 = none ∧ m = s.dmem ∧
                ∃ ok, env.step (.store .plain false a 4 v) g ok g') →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with dmem := m } g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 0⟩) (.regOrMem (.reg (.low r .W32))))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    cases hl : Mem.loadInt s.dmem (s.regs.get64 b + s.regs.get64 i) 4 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.store,
        AddrExpr.zeroExtend_interp_sib1, Reg64s.get_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact ⟨hok hl, fun ok g' hs => hk s.dmem g' (.inr ⟨hl, rfl, ok, hs⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.store,
        AddrExpr.zeroExtend_interp_sib1, Reg64s.get_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨by rw [hl]; rfl, rfl, rfl⟩) _ hpl'

/-- `movl (%b,%i,1), %r32`, mapped or shared (`mov32_load_env_spec` at a
base-plus-index address): the register gets the 4 bytes zero-extended. -/
@[spec] theorem mov32_load_sib1_env_spec (r b i : Reg64) :
    ⦃ fun s g =>
        let a := s.regs.get64 b + s.regs.get64 i
        (Mem.loadInt s.dmem a 4 = none → env.ok (.load .plain false a 4) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt s.dmem a 4 = some v ∧ x = BitVec.ofInt 32 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 4 = none ∧
                ∃ v, env.step (.load .plain false a 4) g v g' ∧ x = v.setWidth 32) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with regs := s.regs.set64 r (x.setWidth 64) } g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.mov (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 0⟩)))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    cases hl : Mem.loadInt s.dmem (s.regs.get64 b + s.regs.get64 i) 4 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
        AddrExpr.zeroExtend_interp_sib1, Reg64s.set_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact ⟨hok hl, fun v g' hs => hk _ g' (.inr ⟨hl, v, hs, rfl⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
        AddrExpr.zeroExtend_interp_sib1, Reg64s.set_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨w, hl, rfl, rfl⟩) _ hpl'

end CombinedSpecs

/-! ## The combined rules' outcomes under an empty private memory

The SPSC threads start with a private memory that maps no 4-byte word
(`DFrame`), so every `movl` is a shared access of the counted environment
and leaves `dmem` unchanged. -/

/-- The private-memory frame: no 4-byte word is mapped. -/
abbrev DFrame (s : MachineData) : Prop := ∀ a, Mem.loadInt s.dmem a 4 = none

/-- A combined `movl` load under an empty private memory is a counted load
step. -/
theorem ld_out {env : SharedEnv} {d : DataMem} {a : BitVec 64} {x : BitVec 32}
    {g g' : (SharedEnv.counted env).State} (hd : ∀ a, Mem.loadInt d a 4 = none)
    (h : (∃ v, Mem.loadInt d a 4 = some v ∧ x = BitVec.ofInt 32 v ∧ g' = g) ∨
      (Mem.loadInt d a 4 = none ∧ ∃ v, (SharedEnv.counted env).step (.load .plain false a 4) g v g' ∧
        x = v.setWidth 32)) :
    ∃ v, env.step (.load .plain false a 4) g.1 v g'.1 ∧ g'.2 = g.2 + 1 ∧ x = v.setWidth 32 := by
  rcases h with ⟨v, hv, -, -⟩ | ⟨-, v, hs, rfl⟩
  · rw [hd] at hv; cases hv
  · exact ⟨v, hs.1, hs.2, rfl⟩

/-- A combined `movl` store under an empty private memory is a counted store
step and leaves `dmem` unchanged. -/
theorem st_out {env : SharedEnv} {d m : DataMem} {a : BitVec 64} {i : Int} {v : BitVec 128}
    {g g' : (SharedEnv.counted env).State} (hd : ∀ a, Mem.loadInt d a 4 = none)
    (h : ((Mem.loadInt d a 4).isSome = true ∧ m = Mem.storeInt d a 4 i ∧ g' = g) ∨
      (Mem.loadInt d a 4 = none ∧ m = d ∧ ∃ ok, (SharedEnv.counted env).step (.store .plain false a 4 v) g ok g')) :
    m = d ∧ (∃ ok, env.step (.store .plain false a 4 v) g.1 ok g'.1) ∧ g'.2 = g.2 + 1 := by
  rcases h with ⟨hv, -, -⟩ | ⟨-, rfl, ok, hs⟩
  · rw [hd] at hv; cases hv
  · exact ⟨rfl, ⟨ok, hs.1⟩, hs.2⟩

end Kraken.Promising.X64.EnvG.SpscX
