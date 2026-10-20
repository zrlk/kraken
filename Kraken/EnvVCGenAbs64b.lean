/-
**64-bit `vcgen` rule for a compare with an absolute symbol operand, x64**
. Additive companion of `Kraken/EnvVCGenAbs64.lean`
(`movq` load/store and `lock cmpxchgq` at `(sym)`), for the x64
Michael–Scott queues' re-check loads `cmpq %rbx,(tail)` / `cmpq %rbx,(head)`
(`Kraken/Examples/LockFree/X64/msqueue{2,3}.kl`).

- `cmp_load_abs_env_spec` (`@[spec]`): `cmpq %r, (sym)`, mapped or shared.
- `mov_reg_imm_label_spec` (`@[spec]`, a `Program` rule lifted by
  `env_lift_spec`): `movq $sym, %r`, the symbol's address (`movq $n1,%rsi`).
  The 8 bytes at the symbol's address `absAddr l` are loaded as by
  `mov_load_abs_env_spec` (a plain load), and the flags are those of
  `[sym] - %r` (`Operation.interp`'s `.cmp`); no register changes.

The queues' other accesses need no new rule: the indirect `movq (%rbx),%rcx`
and `lock cmpxchgq %rsi,(%rbx)` are the `d(%b)` rules of
`Kraken/EnvVCGen.lean` at `d = 0` (`mov_load_env_spec`,
`lock_cmpxchg_shared_spec`), as for `treiber2.kl`'s `movq (%rax),%rcx`. The
`example`s below confirm the parser's directives.
-/
import Kraken.EnvVCGenAbs64

open Kraken
open Std.WP
open Lean.Order

section AbsSpecs64b

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- Unfold the fall-through address past one instruction cell (a copy of
`EnvVCGen.lean`'s private `after_instr`). -/
private theorem after_instr64b {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

set_option hygiene false in
/-- One cell (a copy of `EnvVCGen.lean`'s local `env_step`). -/
local macro "env_step64b" : tactic =>
  `(tactic| (
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr64b hseg]
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩))

/-- The flags of `cmpq %r, (sym)` when the memory operand is `x`: those of
`x - b` (`Operation.interp`'s `.cmp`). -/
def cmpStatus64 (x b : BitVec 64) : StatusFlags :=
  StatusFlags.from_result (x - b)
    { cf := (x - b).unsigned != x.unsigned - b.unsigned,
      af := ((x - b).take 4).unsigned != (x.take 4).unsigned - (b.take 4).unsigned,
      of := (x - b).signed != x.signed - b.signed }

/-- `cmpq %r, (sym)`, mapped or shared: the flags of `[sym] - %r`, the
8 bytes at the symbol's address loaded as by `mov_load_abs_env_spec`. -/
@[spec] theorem MachineWP.cmp_load_abs_env_spec (l : Label) (r : Reg64) :
    ⦃ fun s g =>
        let a := absAddr l
        (Mem.loadInt s.dmem a 8 = none → env.ok (.load .plain false a 8) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt s.dmem a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem a 8 = none ∧
                ∃ v, env.step (.load .plain false a 8) g v g' ∧ x = v.setWidth 64) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with status := cmpStatus64 x (s.regs.get64 r) } g') ⦄
      (⟨Directive.instr (.regular .W64 .W64
          (.cmp (.mem ⟨none, none, .label l⟩) (.regOrMem (.reg (.low r .W64))))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step64b
    cases hl : Mem.loadInt s.dmem (absAddr l) 8 with
    | none =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.load,
        AddrExpr.zeroExtend_interp_abs_label, Reg64s.get_low64, Width.bytes,
        hl, Effects.AllEnv]
      exact ⟨hok hl, fun v g' hs => hk _ g' (.inr ⟨hl, v, hs, rfl⟩) _ hpl'⟩
    | some w =>
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.load,
        AddrExpr.zeroExtend_interp_abs_label, Reg64s.get_low64, Width.bytes,
        hl, Effects.AllEnv]
      exact hk _ g (.inl ⟨w, hl, rfl, rfl⟩) _ hpl'

end AbsSpecs64b

section LabelImm

open MachineWP

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {p : Program}

/-- One cell's interpretation (a copy of `MachineWP.lean`'s local `wp_step`). -/
local macro "wp_step64b" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

/-- `movq $sym, %r`: the symbol's address (`mov_reg_imm_label_sub_spec` with
one label; the msqueues' `movq $n1,%rsi`). -/
@[spec] theorem MachineWP.mov_reg_imm_label_spec (asz : Width) (r : Reg64) (l : Label) :
    ⦃ fun s =>
        let v := (_root_.Executable.labels cenv).label l
        WP.wp p Q E { s with regs := s.regs.set64 r (BitVec.setWidth 64 v.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.label l)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    have ha : cenv.after pc (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.label l)))) :: p)
        = cenv.after (pc + .ofNat z) p := by simp only [Executable.after, hseg]
    rw [ha]
    exact step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl (by wp_step64b; exact h _ hpl')⟩

end LabelImm

/-! ## The parser produces the matched directives -/

open Kraken.X64.Parser in
example : (parse("cmpq %rbx,(tail)") : Program) =
    [Directive.instr (.regular .W64 .W64
      (.cmp (.mem ⟨none, none, .label "tail"⟩) (.regOrMem (.reg (.low .rbx .W64)))))] := by
  decide

open Kraken.X64.Parser in
example : (parse("movq (%rbx),%rcx") : Program) =
    [Directive.instr (.regular .W64 .W64
      (.mov (.reg (.low .rcx .W64)) (.regOrMem (.mem ⟨some (.reg .rbx), none, .int64 0⟩))))] := by
  decide

open Kraken.X64.Parser in
example : (parse("lock cmpxchgq %rsi,(%rbx)") : Program) =
    [Directive.instr (.regular .W64 .W64 (.cmpxchg true (.mem ⟨some (.reg .rbx), none, .int64 0⟩) (.low .rsi .W64)))] := by
  decide

open Kraken.X64.Parser in
example : (parse("movq $n1,%rsi") : Program) =
    [Directive.instr (.regular .W64 .W64 (.mov (.reg (.low .rsi .W64)) (.imm (.label "n1"))))] := by
  decide
