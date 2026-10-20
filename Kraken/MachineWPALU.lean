/-
More x64 rules for the machine-founded weakest precondition (`MachineWP`):
the 64-bit register forms of `or`, `and`, `not`, two-operand `imul`, `or`
with an immediate, `shl`/`shr` by a nonzero immediate, and the 64-bit loads
`movq d(%b), %r`, `movq (%b,%i,s), %r` and `movq d(%b,%i), %r`. They follow
the rule pattern of `MachineWP.lean` (one cell that falls through, its
interpretation reduced by `wp_step`); that file's plumbing (`after_instr`,
`step_here`, `wp_step`) is private or local, so it is repeated here.

An undefined flag is quantified in the precondition (`∀ af`, or `∀ st` for
the shifts, whose `CF`/`OF` depend on the count; the tail must hold for any
flags, which is weaker than the semantics but enough when the flags are
dead).

Helpers for proofs over these rules: `MachineWP.triple_of_pointwise` (a
triple from one triple per start state), `MachineData.retAddr_congr` and the
zero flag of a result as `v = 0` (`CondCode.z_interp_from_result`,
`…_false`).
-/
import Kraken.MachineWP

open Std.WP Kraken Lean.Order

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

private theorem after_instr {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

/-- One cell whose interpretation ends at a state satisfying `P` whenever the
precondition held: the tail runs from there. -/
private theorem cell_spec {i : Instr} {pre : MachineData → Prop}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (P : MachineState → Prop),
      pre s → (∀ s', WP.wp p Q E s' → P (s', 0)) →
      (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All P) :
    ⦃ fun s => pre s ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl (hcell s _ _ h ?_)⟩
    intro s' hs'
    exact hs' _ hpl'

/-- `or %rs, %rd` : the disjunction, the flags of the result, `af` arbitrary. -/
@[spec] theorem MachineWP.or_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd ||| s.regs.get64 rs
        ∀ af : Bool, WP.wp p Q E
          { s with regs := s.regs.set64 rd v,
                   status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.or (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  cell_spec (fun s rng P h hk => by wp_step; exact fun af => hk _ (h af))

/-- `and %rs, %rd` : the conjunction, the flags of the result, `af` arbitrary. -/
@[spec] theorem MachineWP.and_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd &&& s.regs.get64 rs
        ∀ af : Bool, WP.wp p Q E
          { s with regs := s.regs.set64 rd v,
                   status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.and (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  cell_spec (fun s rng P h hk => by wp_step; exact fun af => hk _ (h af))

/-- `or $i, %r` : the disjunction with the immediate, `af` arbitrary. -/
@[spec] theorem MachineWP.or_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := s.regs.get64 r ||| BitVec.setWidth 64 i.toBitVec
        ∀ af : Bool, WP.wp p Q E
          { s with regs := s.regs.set64 r v,
                   status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64 (.or (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  cell_spec (fun s rng P h hk => by wp_step; exact fun af => hk _ (h af))

/-- `not %r` : the complement; the flags are unchanged. -/
@[spec] theorem MachineWP.not_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s => WP.wp p Q E { s with regs := s.regs.set64 r (~~~s.regs.get64 r) } ⦄
      (Directive.instr (.regular asz .W64 (.not (.reg (.low r .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  cell_spec (fun s rng P h hk => by wp_step; exact hk _ h)

/-- `imul %rs, %rd` (two operands) : the low 64 bits of the product; `CF` and
`OF` say whether the signed product overflowed, `SF`, `ZF`, `AF` and `PF` are
arbitrary. -/
@[spec] theorem MachineWP.imul_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rd
        let b := s.regs.get64 rs
        let v := a * b
        let cf := v.signed != a.signed * b.signed
        ∀ sf zf af pf : Bool, WP.wp p Q E
          { s with regs := s.regs.set64 rd v,
                   status := { cf, pf, af, zf, sf, of := cf } } ⦄
      (Directive.instr (.regular asz .W64
          (.imul none (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  cell_spec (fun s rng P h hk => by
    wp_step; exact fun sf zf af pf => hk _ (h sf zf af pf))

omit [CodeEnv] in
/-- The count of a shift by an immediate at 64 bits: the immediate masked to
six bits. -/
private theorem interpMasked_imm64 [L : Labels] (i : Int64) (s : MachineData) (rng : Std.Rco Int64) :
    @ShiftCountExpr.interpMasked L (.imm8 (.int64 i)) s rng Width.W64
      = i.toBitVec.toNat % 64 := by
  show (i.toBitVec.take 8).toNat &&& (2 ^ 6 - 1) = _
  rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide)]

/-- `shr $i, %r` for a nonzero masked count: the logical right shift; the
flags are left arbitrary. -/
@[spec] theorem MachineWP.shr_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let n := i.toBitVec.toNat % 64
        (n ≠ 0) ⊓ (∀ st : StatusFlags, WP.wp p Q E
          { s with regs := s.regs.set64 r (s.regs.get64 r >>> n), status := st }) ⦄
      (Directive.instr (.regular asz .W64 (.shr (.reg (.low r .W64)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  cell_spec (fun s rng P h hk => by
    wp_step
    simp only [meet_prop_eq_and] at h
    obtain ⟨hz, h⟩ := h
    simp only [interpMasked_imm64, hz, beq_iff_eq, ite_false]
    repeat (first | exact hk _ (h _) | intro _ | split | simp only [Effects.All]))

/-- `shl $i, %r` for a nonzero masked count: the left shift; the flags are
left arbitrary. -/
@[spec] theorem MachineWP.shl_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let n := i.toBitVec.toNat % 64
        (n ≠ 0) ⊓ (∀ st : StatusFlags, WP.wp p Q E
          { s with regs := s.regs.set64 r (s.regs.get64 r <<< n), status := st }) ⦄
      (Directive.instr (.regular asz .W64 (.shl (.reg (.low r .W64)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  cell_spec (fun s rng P h hk => by
    wp_step
    simp only [meet_prop_eq_and] at h
    obtain ⟨hz, h⟩ := h
    simp only [interpMasked_imm64, hz, beq_iff_eq, ite_false]
    repeat (first | exact hk _ (h _) | intro _ | split | simp only [Effects.All]))

/-- `movq d(%b), %r` : the 8 bytes must be readable; the tail runs with them
in the register. -/
@[spec] theorem MachineWP.mov_load_base_disp_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with regs := s.regs.set64 r (BitVec.ofInt 64 v) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  cell_spec (fun s rng P h hk => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, h⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [MachineData.load, AddrExpr.zeroExtend_interp_base_disp,
      BitVec.ofInt_toInt_int64, Width.bytes, hv, Effects.All]
    exact hk _ (h v hv))

/-- `movq (%b,%i,s), %r` : the 8 bytes at `b + i * s` must be readable; the
tail runs with them in the register. -/
@[spec] theorem MachineWP.mov_load_sib_spec (r b i : Reg64) (c : Width) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * BitVec.ofNat 64 c.bytes
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with regs := s.regs.set64 r (BitVec.ofInt 64 v) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64))
            (.regOrMem (.mem ⟨some (.reg b), some ⟨i, c⟩, .int64 0⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  cell_spec (fun s rng P h hk => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, h⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [MachineData.load, AddrExpr.zeroExtend_interp_sib_scale, Width.bytes, hv,
      Effects.All]
    exact hk _ (h v hv))

/-- `movq d(%b,%i), %r` : the 8 bytes at `b + i + d` must be readable; the
tail runs with them in the register. -/
@[spec] theorem MachineWP.mov_load_sib1_disp_spec (r b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with regs := s.regs.set64 r (BitVec.ofInt 64 v) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64))
            (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  cell_spec (fun s rng P h hk => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, h⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [MachineData.load, AddrExpr.zeroExtend_interp_sib1_disp, Width.bytes, hv,
      Effects.All]
    exact hk _ (h v hv))

end Specs

/-! ## Helpers for proofs over these rules -/

/-- **A triple from one triple per start state**: `⦃ P ⦄ p ⦃ Q; E ⦄` holds
when, for every `s₀` satisfying `P`, it holds from exactly `s₀`. -/
theorem MachineWP.triple_of_pointwise [CodeEnv] {P : MachineData → Prop} {p : Program}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
    (h : ∀ s₀, P s₀ → ⦃ fun s => s = s₀ ⦄ p ⦃ Q; E ⦄) : ⦃ P ⦄ p ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (h s hs).le_wp s rfl

/-- The return address depends only on the memory and `rsp`. -/
theorem MachineData.retAddr_congr (s' s : MachineData) (hd : s'.dmem = s.dmem)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) : s'.retAddr = s.retAddr := by
  simp only [MachineData.retAddr_eq, hd, hsp]

/-- The zero flag of a result is set iff the result is `0`. -/
theorem CondCode.z_interp_from_result {w : Nat} (v : BitVec w) (f : StatusFlags.from_result.Remaining) :
    (CondCode.z.interp (StatusFlags.from_result v f) = true) = (v = 0#w) := by
  simp [CondCode.interp, StatusFlags.from_result]

/-- The zero flag of a result is clear iff the result is not `0`. -/
theorem CondCode.z_interp_from_result_false {w : Nat} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (CondCode.z.interp (StatusFlags.from_result v f) = false) = ¬(v = 0#w) := by
  simp [CondCode.interp, StatusFlags.from_result]
