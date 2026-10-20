/-
**`vcgen` rules for absolute symbol operands `(sym)`, x64**. Additive companion of `Kraken/EnvVCGen.lean`.

The x64 parser reads `(sym)` (no displacement in front, only a symbol inside
the parentheses; herd's and the `.kl` programs' way of naming a shared
location) as the address expression `⟨none, none, .label sym⟩` at 64-bit
address size (`Kraken/X64/Parser.lean`, `parseMemory`). The interpreter
computes it as `label sym` (`AddrExpr.interp`, `ConstExpr.interp`,
`Kraken/X64/Semantics.lean`), where the `Labels` instance is the ambient
executable's (`Executable.labels`: the address of the first `.label sym`
cell, `-1` if there is none). The `.kl` runner places one `.label sym` cell
per data symbol behind the code (`Kraken.Litmus.X64.prepareProgram`), so in
the runner's executable `label sym` is the symbol's address.

The rules below are the `d(%b)` rules of `EnvVCGen.lean` with the address
`s.regs.get64 b + d.toBitVec` replaced by `absAddr l`, the label's address in
the ambient code (`cenv`); all `@[spec]`:

- `mov32_load_abs_env_spec`: `movl (sym), %r32`, mapped or shared;
- `mov32_store_abs_env_spec`: `movl %r32, (sym)`, mapped or shared;
- `mov32_store_imm_abs_shared_spec`: `movl $i, (sym)` on a shared location;
- `xchg32_abs_shared_spec`: `xchgl %r32, (sym)` on a shared location;
- `lock_xadd32_abs_shared_spec` (from the x64 ticket lock): `lock xaddl
  %r32, (sym)` on a shared location;
- `lock_cmpxchg32_abs_shared_spec`: `lock cmpxchgl %r32, (sym)` on a shared
  location.

`AddrExpr.zeroExtend_interp_abs_label` is the address computation.
-/
import Kraken.EnvVCGen

open Kraken
open Std.WP
open Lean.Order

/-- The address an absolute operand `(sym)` computes: the symbol's label. -/
theorem AddrExpr.zeroExtend_interp_abs_label [Labels] (l : Label) (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64) (a := ⟨none, none, .label l⟩) regs rng).zeroExtend 64)
      = (label l).toBitVec := by
  simp only [AddrExpr.interp, ConstExpr.interp]
  show BitVec.ofInt 64 _ = _
  rw [Int.zero_add, Int.zero_add, BitVec.ofInt_toInt_int64]

/-- The address of the label `l` in the ambient code: the address an
absolute operand `(l)` computes. -/
abbrev absAddr [CodeEnv] (l : Label) : BitVec 64 := ((_root_.Executable.labels cenv).label l).toBitVec

section AbsSpecs

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- Unfold the fall-through address past one instruction cell (a copy of
`EnvVCGen.lean`'s private `after_instr`). -/
private theorem after_instr {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

set_option hygiene false in
/-- One cell (a copy of `EnvVCGen.lean`'s local `env_step`). -/
local macro "env_step" : tactic =>
  `(tactic| (
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩))

/-- `movl (sym), %r32`, mapped or shared: the register gets the 4 bytes at
the symbol's address zero-extended (`mov32_load_env_spec` at `(sym)`). -/
@[spec] theorem MachineWP.mov32_load_abs_env_spec (r : Reg64) (l : Label) :
    ⦃ fun s g =>
        let a := absAddr l
        (Mem.loadInt s.dmem a 4 = none → env.ok (.load .plain false a 4) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt s.dmem a 4 = some v ∧ x = BitVec.ofInt 32 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 4 = none ∧
                ∃ v, env.step (.load .plain false a 4) g v g' ∧ x = v.setWidth 32) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with regs := s.regs.set64 r (x.setWidth 64) } g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.mov (.reg (.low r .W32)) (.regOrMem (.mem ⟨none, none, .label l⟩)))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    cases hl : Mem.loadInt s.dmem (absAddr l) 4 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
        AddrExpr.zeroExtend_interp_abs_label, Reg64s.set_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact ⟨hok hl, fun v g' hs => hk _ g' (.inr ⟨hl, v, hs, rfl⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.setReg, MachineData.load,
        AddrExpr.zeroExtend_interp_abs_label, Reg64s.set_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨w, hl, rfl, rfl⟩) _ hpl'

/-- `movl %r32, (sym)`, mapped or shared (`mov32_store_env_spec` at
`(sym)`). -/
@[spec] theorem MachineWP.mov32_store_abs_env_spec (l : Label) (r : Reg64) :
    ⦃ fun s g =>
        let a := absAddr l
        let v := ((s.regs.get64 r).setWidth 32).setWidth 128
        (Mem.loadInt s.dmem a 4 = none → env.ok (.store .plain false a 4 v) g) ⊓
          (∀ m g',
            ((Mem.loadInt s.dmem a 4).isSome = true ∧
                m = Mem.storeInt s.dmem a 4 ((s.regs.get64 r).setWidth 32).toInt ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 4 = none ∧ m = s.dmem ∧
                ∃ ok, env.step (.store .plain false a 4 v) g ok g') →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with dmem := m } g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨none, none, .label l⟩) (.regOrMem (.reg (.low r .W32))))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    cases hl : Mem.loadInt s.dmem (absAddr l) 4 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.store,
        AddrExpr.zeroExtend_interp_abs_label, Reg64s.get_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact ⟨hok hl, fun ok g' hs => hk s.dmem g' (.inr ⟨hl, rfl, ok, hs⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.store,
        AddrExpr.zeroExtend_interp_abs_label, Reg64s.get_low32, Width.bytes,
        hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨by rw [hl]; rfl, rfl, rfl⟩) _ hpl'

/-- `movl $i, (sym)` on a shared location: one `store .plain` of 4 bytes of
the immediate's low word (`mov32_store_imm_shared_spec` at `(sym)`). -/
@[spec] theorem MachineWP.mov32_store_imm_abs_shared_spec (l : Label) (i : Int64) :
    ⦃ fun s g =>
        let a := absAddr l
        let v := (i.toBitVec.truncate 32).setWidth 128
        (Mem.loadInt s.dmem a 4 = none) ⊓ env.ok (.store .plain false a 4 v) g ⊓
          (∀ ok g', env.step (.store .plain false a 4 v) g ok g' → WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨none, none, .label l⟩) (.imm (.int64 i)))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hnone, hok⟩, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, ConstExpr.interp,
      MachineData.set, MachineData.store,
      AddrExpr.zeroExtend_interp_abs_label, Width.bytes,
      hnone, Effects.AllEnv]
    exact ⟨hok, fun ok g' hs => hk ok g' hs _ hpl'⟩

/-- `xchgl %r32, (sym)` on a shared location: one `rmw .acqRel` of 4 bytes
writing the low word of `r`; `r` gets the old word, zero-extended
(`xchg32_shared_spec` at `(sym)`). -/
@[spec] theorem MachineWP.xchg32_abs_shared_spec (r : Reg64) (l : Label) :
    ⦃ fun s g =>
        let a := absAddr l
        let acc := SharedAccess.rmw .acqRel a 4 (rmwOp128 .W32 (fun _ => some ((s.regs.get64 r).setWidth 32)))
        (Mem.loadInt s.dmem a 4 = none) ⊓ env.ok acc g ⊓
          (∀ old g', env.step acc g old g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.set64 r ((old.setWidth 32).setWidth 64) } g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.xchg (.low r .W32) (.mem ⟨none, none, .label l⟩))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hnone, hok⟩, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    simp only [Directive.interp, Instr.interp, Operation.interp,
      RegOrMem.rmw, MachineData.rmwK, MachineData.setReg,
      AddrExpr.zeroExtend_interp_abs_label, Reg64s.get_low32,
      Reg64s.set_low32, Width.bytes, hnone, Effects.AllEnv, ite_true]
    exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `lock xaddl %r32, (sym)` on a shared location: one `rmw .acqRel` of
4 bytes adding the low word of `r`; `r` gets the old word, zero-extended, and
the flags of the addition (`lock_xadd_shared_spec` at 32 bits and `(sym)`;
hoisted from the x64 ticket lock's `MachineWP.lock_xadd32_abs_shared_specX`,
which is now this). -/
@[spec] theorem MachineWP.lock_xadd32_abs_shared_spec (l : Label) (r : Reg64) :
    ⦃ fun s g =>
        let a := absAddr l
        let src := (s.regs.get64 r).setWidth 32
        let op := rmwOp128 .W32 (fun x => some (x + src))
        (Mem.loadInt s.dmem a 4 = none) ⊓ env.ok (.rmw .acqRel a 4 op) g ⊓
          (∀ v g', env.step (.rmw .acqRel a 4 op) g v g' →
            let old := v.setWidth 32
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with
              regs := s.regs.set64 r (old.setWidth 64),
              status := LockBinOp.add.status old src (old + src) false } g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.xadd true (.mem ⟨none, none, .label l⟩) (.low r .W32))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hnone, hok⟩, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    simp only [Directive.interp, Instr.interp, Operation.interp,
      RegOrMem.rmw, MachineData.rmwK, MachineData.setReg,
      AddrExpr.zeroExtend_interp_abs_label, Reg64s.get_low32,
      Reg64s.set_low32, Width.bytes, hnone, Effects.AllEnv, ite_true]
    exact ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩

/-- `lock cmpxchgl %r32, (sym)` on a shared location
(`lock_cmpxchg32_shared_spec` at `(sym)`). -/
@[spec] theorem MachineWP.lock_cmpxchg32_abs_shared_spec (l : Label) (r : Reg64) :
    ⦃ fun s g =>
        let a := absAddr l
        let acc := (s.regs.get64 .rax).setWidth 32
        let op := rmwOp128 .W32 (fun x => if x == acc then some ((s.regs.get64 r).setWidth 32) else none)
        (Mem.loadInt s.dmem a 4 = none) ⊓ env.ok (.rmw .acqRel a 4 op) g ⊓
          (∀ v g', env.step (.rmw .acqRel a 4 op) g v g' →
            let old := v.setWidth 32
            let dv := acc - old
            let status := StatusFlags.from_result dv
              { cf := dv.unsigned != acc.unsigned - old.unsigned,
                af := (dv.take 4).unsigned != (acc.take 4).unsigned - (old.take 4).unsigned,
                of := dv.signed != acc.signed - old.signed }
            (old = acc → WP.wp (⟨p⟩ : EnvProgram env) Q E { s with status } g')
            ⊓ (old ≠ acc → WP.wp (⟨p⟩ : EnvProgram env) Q E
                { s with regs := s.regs.set64 .rax (old.setWidth 64), status } g')) ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.cmpxchg true (.mem ⟨none, none, .label l⟩) (.low r .W32))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hnone, hok⟩, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    simp only [Directive.interp, Instr.interp, Operation.interp,
      RegOrMem.rmw, MachineData.rmwK, MachineData.setReg,
      AddrExpr.zeroExtend_interp_abs_label, Reg64s.get_low32,
      Reg64s.set_low32, Width.bytes, hnone, Effects.AllEnv, ite_true]
    refine ⟨hok, fun v g' hs => ?_⟩
    obtain ⟨heq, hne⟩ := hk v g' hs
    by_cases h : v.setWidth 32 = (s.regs.get64 .rax).setWidth 32
    · have hb : (v.setWidth 32 == (s.regs.get64 .rax).setWidth 32) = true := by simpa using h
      simp only [hb, ite_true]
      exact heq h _ hpl'
    · have hb : (v.setWidth 32 == (s.regs.get64 .rax).setWidth 32) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ite_false]
      exact hne h _ hpl'

end AbsSpecs
