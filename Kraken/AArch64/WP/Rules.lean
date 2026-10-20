/-
The straight-line dictionary of the AArch64 machine-founded wp, next
to the structural rules and the first register
rules of `Kraken.AArch64.WP.MachineWP` (`nil`, `label`, `byteArray`, `NOP`,
`MOVZ X`, `MOV X`, `ADD`/`SUB X` with an unshifted immediate).

One `@[spec]` triple per instruction shape, in composite form, as in x64's
`Kraken/MachineWP.lean`: the precondition is the tail's wp at the record update
the instruction performs. Most rules are generic in the operation width `w`; at
a register literal the API of `Kraken.AArch64.WP.Specs` reduces their reads and
writes, and a `W` write zero-extends into the `X` register. Rules whose value
spells a width-dependent literal (the move-wide immediates) are stated per
width.

A rule whose operand reads the instruction's range (an immediate operand is a
`ConstExpr`, an address is computed by `AddrExpr.eval`) quantifies over the
range: `∀ rng, …`. Every operand of a parsed program reduces without it
(`ExtOrImmReg.interp_imm`, `AddrExpr.eval_imm`, …), so `rng` drops out of the
VC; the pc-reading `ADR`/`ADRP` forms are `TripleAt` rules instead.

Memory rules act on mapped memory (`dmem`), like x64's: a load needs its bytes
readable and runs the tail at every value they may hold, a store needs them
owned (readable) and runs the tail on the updated memory; an access through
`SP` needs `SP` 16-byte aligned (`AddrExpr.SPAligned`).

## Coverage

| Rule | Instruction forms | Widths |
|---|---|---|
| `movz_spec` (MachineWP), `movz_w32_spec` | `MOVZ Rd, #i{, LSL #k}` | X, W |
| `movk_spec`, `movk_w32_spec` | `MOVK Rd, #i{, LSL #k}` | X, W |
| `movn_spec`, `movn_w32_spec` | `MOVN Rd, #i{, LSL #k}` (and `MOV` of such an immediate) | X, W |
| `mov_reg_spec` (MachineWP), `mov_reg_w32_spec` | `MOV Rd, Rm` (`ORR Rd, ZR, Rm`) | X, W |
| `add_imm_spec`, `sub_imm_spec` (MachineWP) | `ADD`/`SUB Xd\|SP, Xn\|SP, #i` | X |
| `add_e_spec`, `sub_e_spec` | `ADD`/`SUB Rd\|SP, Rn\|SP, #i{, LSL #12}` and `…, Rm, <extend> #k` | X, W |
| `adds_e_spec`, `subs_e_spec` | `ADDS`/`SUBS` (and `CMN`/`CMP`) with an immediate or extended register | X, W |
| `add_s_spec`, `sub_s_spec` | `ADD`/`SUB Rd, Rn, Rm{, LSL\|LSR\|ASR #k}` (and `NEG`) | X, W |
| `adds_s_spec`, `subs_s_spec` | `ADDS`/`SUBS` (and `CMN`/`CMP`/`NEGS`) with a shifted register | X, W |
| `and_i_spec`, `orr_i_spec`, `eor_i_spec`, `ands_i_spec` | `AND`/`ORR`/`EOR`/`ANDS` (`TST`) with a bitmask immediate (and `MOV` of one) | X, W |
| `and_s_spec`, `orr_s_spec`, `eor_s_spec`, `bic_s_spec`, `orn_s_spec`, `eon_s_spec` | the logical ops with a shifted register (and `MVN`) | X, W |
| `ands_s_spec`, `bics_s_spec` | `ANDS`/`BICS` (`TST`) with a shifted register | X, W |
| `ubfm_spec`, `sbfm_spec` | `UBFM`/`SBFM` and the aliases `LSL`/`LSR`/`ASR #k`, `UBFX`/`SBFX`, `UBFIZ`/`SBFIZ`, `UXTB`/`UXTH`/`SXTB`/`SXTH`/`SXTW` (`evalUBFM_lsl`, `evalUBFM_lsr`, `evalSBFM_asr` reduce the shifts) | X, W |
| `lslv_spec`, `lsrv_spec`, `asrv_spec`, `rorv_spec` | `LSLV`/`LSRV`/`ASRV`/`RORV` (`LSL`/`LSR`/`ASR`/`ROR Rd, Rn, Rm`) | X, W |
| `madd_spec`, `msub_spec` | `MADD`/`MSUB` (and `MUL`/`MNEG`) | X, W |
| `csel_spec`, `csinc_spec`, `csinv_spec`, `csneg_spec` | `CSEL`/`CSINC`/`CSINV`/`CSNEG` (and `CSET`/`CSETM`/`CINC`/`CINV`/`CNEG`) | X, W |
| `ccmp_reg_spec`, `ccmp_imm_spec`, `ccmn_reg_spec`, `ccmn_imm_spec` | `CCMP`/`CCMN` with a register or an immediate | X, W |
| `ldr_spec`, `str_spec` | `LDR`/`STR Rt, [Xn\|SP …]`: offset, pre-index, post-index, register offset | X, W |
| `ldrb_spec`, `ldrh_spec`, `strb_spec`, `strh_spec` | `LDRB`/`LDRH` (zero-extending) and `STRB`/`STRH`, every addressing form | W |
| `ldp_spec`, `stp_spec` | `LDP`/`STP Rt1, Rt2, [Xn\|SP …]`: offset, pre-index, post-index | X, W |
| `adr_label_spec`, `adrp_label_spec` | `ADR`/`ADRP Xd, label` | X |
| `adr_imm_at`, `adrp_imm_at` (`TripleAt`) | `ADR`/`ADRP Xd, #imm` (relative to the pc) | X |
-/
import Kraken.AArch64.WP.MachineWP

open Kraken
open Std.WP
open Lean.Order

/-! ## Operand reductions

The operands the rules leave in a VC, at the forms the parser produces. -/

/-- A shifted register operand ignores the instruction's range. -/
@[simp, grind =] theorem ShiftRegExpr.interp_lsl {w : RegWidth} (r : RegOrZr w) (a : Int64)
    (s : Reg64s) (p : Std.Rco Int64) :
    ShiftRegExpr.interp ⟨r, a, .LSL⟩ s p = s.getRegOrZr r <<< a.toInt.toNat := rfl

@[simp, grind =] theorem ShiftRegExpr.interp_lsr {w : RegWidth} (r : RegOrZr w) (a : Int64)
    (s : Reg64s) (p : Std.Rco Int64) :
    ShiftRegExpr.interp ⟨r, a, .LSR⟩ s p = s.getRegOrZr r >>> a.toInt.toNat := rfl

@[simp, grind =] theorem ShiftRegExpr.interp_asr {w : RegWidth} (r : RegOrZr w) (a : Int64)
    (s : Reg64s) (p : Std.Rco Int64) :
    ShiftRegExpr.interp ⟨r, a, .ASR⟩ s p = (s.getRegOrZr r).sshiftRight a.toInt.toNat := rfl

@[simp, grind =] theorem ShiftRegExpr.interp_ror {w : RegWidth} (r : RegOrZr w) (a : Int64)
    (s : Reg64s) (p : Std.Rco Int64) :
    ShiftRegExpr.interp ⟨r, a, .ROR⟩ s p = (s.getRegOrZr r).rotateRight a.toInt.toNat := rfl

/-- An arithmetic immediate, unshifted. -/
@[simp, grind =] theorem ExtOrImmReg.interp_imm64 [Labels] (i : Int64) (s : Reg64s) (p : Std.Rco Int64) :
    @ExtOrImmReg.interp _ .W64 (.imm ⟨.int64 i, .S0⟩) s p = i.toBitVec := by
  simp [ExtOrImmReg.interp]

@[simp, grind =] theorem ExtOrImmReg.interp_imm32 [Labels] (i : Int64) (s : Reg64s) (p : Std.Rco Int64) :
    @ExtOrImmReg.interp _ .W32 (.imm ⟨.int64 i, .S0⟩) s p = i.toBitVec.setWidth 32 := by
  simp [ExtOrImmReg.interp]

/-- An arithmetic immediate shifted by 12 (`#i, LSL #12`). -/
@[simp, grind =] theorem ExtOrImmReg.interp_imm64_lsl12 [Labels] (i : Int64) (s : Reg64s)
    (p : Std.Rco Int64) :
    @ExtOrImmReg.interp _ .W64 (.imm ⟨.int64 i, .S12⟩) s p = i.toBitVec <<< 12 := by
  simp [ExtOrImmReg.interp, BitVec.ofInt_shiftLeft]

@[simp, grind =] theorem ExtOrImmReg.interp_imm32_lsl12 [Labels] (i : Int64) (s : Reg64s)
    (p : Std.Rco Int64) :
    @ExtOrImmReg.interp _ .W32 (.imm ⟨.int64 i, .S12⟩) s p = i.toBitVec.setWidth 32 <<< 12 := by
  simp [ExtOrImmReg.interp, BitVec.ofInt_shiftLeft]

/-- An extended register operand ignores the instruction's range. -/
@[simp, grind =] theorem ExtOrImmReg.interp_ext [Labels] {w : RegWidth} (e : ExtRegExpr) (s : Reg64s)
    (p : Std.Rco Int64) :
    @ExtOrImmReg.interp _ w (.ext e) s p = BitVec.ofInt w.bits (e.interp s ⟨0, 0⟩) := rfl

/-- The bitmask immediate of a logical instruction, at the operation width. -/
def ConstExpr.immVal [Labels] (w : RegWidth) (c : ConstExpr) (p : Std.Rco Int64) : w.type :=
  BitVec.ofInt w.bits (c.interp p).toInt

@[simp, grind =] theorem ConstExpr.immVal_int64_W64 [Labels] (i : Int64) (p : Std.Rco Int64) :
    ConstExpr.immVal .W64 (.int64 i) p = i.toBitVec := by
  simp [ConstExpr.immVal]

@[simp, grind =] theorem ConstExpr.immVal_int64_W32 [Labels] (i : Int64) (p : Std.Rco Int64) :
    ConstExpr.immVal .W32 (.int64 i) p = i.toBitVec.setWidth 32 := by
  simp [ConstExpr.immVal]

/-! ### Shift aliases of the bitfield moves

`LSL #k`, `LSR #k` and `ASR #k` are `UBFM`/`SBFM` with immediates the parser
computes; these rewrite the bitfield move at those immediates (side
conditions on numerals, which `simp` decides) to the shift. -/

/-- `LSL Xd, Xn, #k` is `UBFM Xd, Xn, #(64-k), #(63-k)` for `0 < k`. -/
@[simp ↓] theorem evalUBFM_lsl64 (x : BitVec 64) (immr imms : Nat) (h₁ : imms + 1 = immr)
    (h₂ : immr < 64) : evalUBFM (w := .W64) x immr imms = x <<< (64 - immr) := by
  subst h₁
  have h3 : ¬ (imms + 1 ≤ imms) := by omega
  have hm : imms % 64 = imms := Nat.mod_eq_of_lt (by omega)
  simp only [evalUBFM, RegWidth.bits, MemWidth.bits, Nat.mod_eq_of_lt h₂, hm, ge_iff_le, h3,
    ite_false, BitVec.take]
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, BitVec.getLsbD_extractLsb']
  by_cases h : i < 63 - imms
  · simp [h]
  · have h5 : i - (63 - imms) < 64 := by omega
    simp [h, hm, show 64 - (imms + 1) = 63 - imms by omega,
      show i - (63 - imms) < imms + 1 by omega, BitVec.getLsbD_eq_getElem h5]

/-- `LSR Xd, Xn, #k` is `UBFM Xd, Xn, #k, #63`. -/
@[simp ↓] theorem evalUBFM_lsr64 (x : BitVec 64) (immr : Nat) (h : immr < 64) :
    evalUBFM (w := .W64) x immr 63 = x >>> immr := by
  have h3 : immr ≤ 63 := by omega
  simp only [evalUBFM, RegWidth.bits, MemWidth.bits, Nat.mod_eq_of_lt h, ge_iff_le,
    show 63 % 64 = 63 from rfl, h3, ite_true, BitVec.take]
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_extractLsb', BitVec.getElem_ushiftRight,
    BitVec.getLsbD_ushiftRight]
  by_cases h' : immr + i < 64
  · simp [Nat.mod_eq_of_lt h, show i < 63 - immr + 1 by omega, BitVec.getLsbD_eq_getElem h']
  · simp [BitVec.getLsbD_of_ge x (immr + i) (by omega)]

/-- `ASR Xd, Xn, #k` is `SBFM Xd, Xn, #k, #63`. -/
@[simp ↓] theorem evalSBFM_asr64 (x : BitVec 64) (immr : Nat) (h : immr < 64) :
    evalSBFM (w := .W64) x immr 63 = x.sshiftRight immr := by
  have h3 : immr ≤ 63 := by omega
  simp only [evalSBFM, RegWidth.bits, MemWidth.bits, Nat.mod_eq_of_lt h, ge_iff_le,
    show 63 % 64 = 63 from rfl, h3, ite_true, BitVec.take]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_signExtend, BitVec.getLsbD_sshiftRight]
  by_cases h' : immr + i < 64
  · have h4 : i < 63 - immr + 1 := by omega
    simp [hi, h4, h', Nat.mod_eq_of_lt h, show ¬ 64 ≤ i by omega]
  · have h4 : ¬ i < 63 - immr + 1 := by omega
    simp [hi, h4, h', Nat.mod_eq_of_lt h, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ushiftRight, show immr + (63 - immr) = 63 by omega, show ¬ 64 ≤ i by omega]

/-- `LSL Wd, Wn, #k` is `UBFM Wd, Wn, #(32-k), #(31-k)` for `0 < k`. -/
@[simp ↓] theorem evalUBFM_lsl32 (x : BitVec 32) (immr imms : Nat) (h₁ : imms + 1 = immr)
    (h₂ : immr < 32) : evalUBFM (w := .W32) x immr imms = x <<< (32 - immr) := by
  subst h₁
  have h3 : ¬ (imms + 1 ≤ imms) := by omega
  have hm : imms % 32 = imms := Nat.mod_eq_of_lt (by omega)
  simp only [evalUBFM, RegWidth.bits, MemWidth.bits, Nat.mod_eq_of_lt h₂, hm, ge_iff_le, h3,
    ite_false, BitVec.take]
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, BitVec.getLsbD_extractLsb']
  by_cases h : i < 31 - imms
  · simp [h]
  · have h5 : i - (31 - imms) < 32 := by omega
    simp [h, hm, show 32 - (imms + 1) = 31 - imms by omega,
      show i - (31 - imms) < imms + 1 by omega, BitVec.getLsbD_eq_getElem h5]

/-- `LSR Wd, Wn, #k` is `UBFM Wd, Wn, #k, #31`. -/
@[simp ↓] theorem evalUBFM_lsr32 (x : BitVec 32) (immr : Nat) (h : immr < 32) :
    evalUBFM (w := .W32) x immr 31 = x >>> immr := by
  have h3 : immr ≤ 31 := by omega
  simp only [evalUBFM, RegWidth.bits, MemWidth.bits, Nat.mod_eq_of_lt h, ge_iff_le,
    show 31 % 32 = 31 from rfl, h3, ite_true, BitVec.take]
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_extractLsb', BitVec.getElem_ushiftRight,
    BitVec.getLsbD_ushiftRight]
  by_cases h' : immr + i < 32
  · simp [Nat.mod_eq_of_lt h, show i < 31 - immr + 1 by omega, BitVec.getLsbD_eq_getElem h']
  · simp [BitVec.getLsbD_of_ge x (immr + i) (by omega)]

/-- `ASR Wd, Wn, #k` is `SBFM Wd, Wn, #k, #31`. -/
@[simp ↓] theorem evalSBFM_asr32 (x : BitVec 32) (immr : Nat) (h : immr < 32) :
    evalSBFM (w := .W32) x immr 31 = x.sshiftRight immr := by
  have h3 : immr ≤ 31 := by omega
  simp only [evalSBFM, RegWidth.bits, MemWidth.bits, Nat.mod_eq_of_lt h, ge_iff_le,
    show 31 % 32 = 31 from rfl, h3, ite_true, BitVec.take]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_signExtend, BitVec.getLsbD_sshiftRight]
  by_cases h' : immr + i < 32
  · have h4 : i < 31 - immr + 1 := by omega
    simp [hi, h4, h', Nat.mod_eq_of_lt h, show ¬ 32 ≤ i by omega]
  · have h4 : ¬ i < 31 - immr + 1 := by omega
    simp [hi, h4, h', Nat.mod_eq_of_lt h, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ushiftRight, show immr + (31 - immr) = 31 by omega, show ¬ 32 ≤ i by omega]

/-! ### Addresses -/

/-- `AddrExpr.checkSPAlignment` passes: an access through `SP` needs `SP`
16-byte aligned. At a base register literal it reduces to `True` or to the
alignment of `SP`. -/
def AddrExpr.SPAligned (a : AddrExpr) (s : MachineData) : Prop :=
  a.base = .SP → s.regs.SP.toBitVec % 16#64 = 0#64

@[simp, grind =] theorem AddrExpr.SPAligned_X (r : XReg) (off : AddrOff) (s : MachineData) :
    AddrExpr.SPAligned ⟨.low (.reg r) .W64, off⟩ s = True := by
  simp [AddrExpr.SPAligned]

@[simp, grind =] theorem AddrExpr.SPAligned_SP (off : AddrOff) (s : MachineData) :
    AddrExpr.SPAligned ⟨.low .SP .W64, off⟩ s = (s.regs.SP.toBitVec % 16#64 = 0#64) := by
  simp [AddrExpr.SPAligned]

private theorem AddrExpr.checkSP_All {a : AddrExpr} {s : MachineData} {ok : Unit → Effects}
    {P : MachineState → Prop} (ha : a.SPAligned s) (hk : (ok ()).All P) :
    (a.checkSPAlignment s ok).All P := by
  obtain ⟨⟨b, w⟩, off⟩ := a
  cases b with
  | reg r => exact hk
  | SP =>
    have h := ha rfl
    simp only [AddrExpr.checkSPAlignment, Reg64s.getRegOrSp_SP, h, bne_self_eq_false,
      Bool.false_eq_true, ite_false]
    exact hk

private theorem MachineData.load_All {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {ret : w.type → MachineData → Effects} {P : MachineState → Prop} {v : Int}
    (hv : Mem.loadInt s.dmem addr w.bytes = some v) (hk : (ret (.ofInt _ v) s).All P) :
    (s.load addr w ret).All P := by
  simp only [MachineData.load, Effects.All, hv]
  exact hk

private theorem MachineData.store_All {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {val : w.type} {ret : MachineData → Effects} {P : MachineState → Prop}
    (hv : (Mem.loadInt s.dmem addr w.bytes).isSome = true)
    (hk : (ret { s with dmem := Mem.storeInt s.dmem addr w.bytes val.toInt }).All P) :
    (s.store addr val ret).All P := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hv
  simp only [MachineData.store, Effects.All, hv]
  exact hk

section Specs

open MachineWP

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.All,
      or_false, false_or])

/-- Unfold the fall-through address past one instruction cell. -/
private theorem after_instr {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

/-- Run one cell and continue. -/
private theorem step_here {post : @Post MachineState} {s : MachineData} {pc : Int64}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hseg : cenv.codeAt pc = (d, z) :: rest)
    (hall : cenv.stepAt d z (s, pc) (fun st => Eventually cenv.instrStep post st)) :
    Eventually cenv.instrStep post (s, pc) :=
  step_cps _ _ _ ⟨d, z, rest, hseg, hall⟩

/-- The rule of a cell that runs and falls through to the state the cell
computes (`MachineWP.lean`'s `fallthrough_spec`). -/
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

/-- The rule of a cell that falls through with an arbitrary precondition: one
that reads the instruction's range, or carries side conditions (memory
rules). -/
private theorem fallthrough_pre_spec {i : Instr} {P : MachineData → Prop}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (R : MachineState → Prop),
      P s → (∀ s', WP.wp p Q E s' → R (s', 0)) →
      (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All R) :
    ⦃ P ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    exact step_here hseg (Or.inl (hcell s _ _ h (fun s' hs' => hs' _ hpl')))

/-! ### Move wide -/

/-- `MOVZ Wd, #i, LSL #k` : the low 16 bits of the immediate, shifted, zero-extended. -/
@[spec] theorem MachineWP.movz_w32_spec (dst : RegOrZr .W32) (i : Int64) (sh : MovShift .W32) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst ((i.toBitVec.setWidth 32 &&& 0xFFFF#32) <<< sh.toNat) } ⦄
      (Directive.instr ⟨.W32, .MOVZ dst (.int64 i) sh⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; simpa using hP)

/-- `MOVK Xd, #i, LSL #k` : the 16-bit field at `k` replaced by the immediate's low bits. -/
@[spec] theorem MachineWP.movk_spec (dst : RegOrZr .W64) (i : Int64) (sh : MovShift .W64) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    ((s.regs.getRegOrZr dst &&& ~~~(0xFFFF#64 <<< sh.toNat))
                      ||| ((i.toBitVec &&& 0xFFFF#64) <<< sh.toNat)) } ⦄
      (Directive.instr ⟨.W64, .MOVK dst (.int64 i) sh⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; simpa using hP)

/-- `MOVK Wd, #i, LSL #k` : as `MOVK X`, at 32 bits, zero-extended. -/
@[spec] theorem MachineWP.movk_w32_spec (dst : RegOrZr .W32) (i : Int64) (sh : MovShift .W32) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    ((s.regs.getRegOrZr dst &&& ~~~(0xFFFF#32 <<< sh.toNat))
                      ||| ((i.toBitVec.setWidth 32 &&& 0xFFFF#32) <<< sh.toNat)) } ⦄
      (Directive.instr ⟨.W32, .MOVK dst (.int64 i) sh⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; simpa using hP)

/-- `MOVN Xd, #i, LSL #k` : the complement of the shifted 16-bit immediate. -/
@[spec] theorem MachineWP.movn_spec (dst : RegOrZr .W64) (i : Int64) (sh : MovShift .W64) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (~~~((i.toBitVec &&& 0xFFFF#64) <<< sh.toNat)) } ⦄
      (Directive.instr ⟨.W64, .MOVN dst (.int64 i) sh⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; simpa using hP)

/-- `MOVN Wd, #i, LSL #k` : as `MOVN X`, at 32 bits, zero-extended. -/
@[spec] theorem MachineWP.movn_w32_spec (dst : RegOrZr .W32) (i : Int64) (sh : MovShift .W32) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    (~~~((i.toBitVec.setWidth 32 &&& 0xFFFF#32) <<< sh.toNat)) } ⦄
      (Directive.instr ⟨.W32, .MOVN dst (.int64 i) sh⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; simpa using hP)

/-- `MOV Wd, Wm` (the alias `ORR Wd, WZR, Wm`) : the low half copied, zero-extended. -/
@[spec] theorem MachineWP.mov_reg_w32_spec (dst src : RegOrZr .W32) :
    ⦃ fun s => WP.wp p Q E { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src) } ⦄
      (Directive.instr ⟨.W32, .ORR_s dst (.low .XZR .W32) ⟨src, 0, .LSL⟩⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    wp_step
    simp only [ShiftRegExpr.interp_lsl_zero, Reg64s.getRegOrZr_XZR]
    simpa using hP)

/-! ### Add and subtract -/

/-- `ADD Rd|SP, Rn|SP, <imm|extended register>` : no flags. -/
@[spec low] theorem MachineWP.add_e_spec {w : RegWidth} (dst src1 : RegOrSp w) (src2 : ExtOrImmReg) :
    ⦃ fun s => ∀ rng, WP.wp p Q E
        { s with regs := s.regs.setRegOrSp dst
                    (s.regs.getRegOrSp src1 + @ExtOrImmReg.interp (_root_.Executable.labels cenv) w src2 s.regs rng) } ⦄
      (Directive.instr ⟨w, .ADD_e dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by wp_step; exact hR _ (h rng))

/-- `SUB Rd|SP, Rn|SP, <imm|extended register>` : no flags. -/
@[spec low] theorem MachineWP.sub_e_spec {w : RegWidth} (dst src1 : RegOrSp w) (src2 : ExtOrImmReg) :
    ⦃ fun s => ∀ rng, WP.wp p Q E
        { s with regs := s.regs.setRegOrSp dst
                    (s.regs.getRegOrSp src1 - @ExtOrImmReg.interp (_root_.Executable.labels cenv) w src2 s.regs rng) } ⦄
      (Directive.instr ⟨w, .SUB_e dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by wp_step; exact hR _ (h rng))

/-- `ADDS Rd, Rn|SP, <imm|extended register>` (`CMN` when `Rd` is `ZR`) : the
sum, and the flags of the addition. -/
@[spec] theorem MachineWP.adds_e_spec {w : RegWidth} (dst : RegOrZr w) (src1 : RegOrSp w)
    (src2 : ExtOrImmReg) :
    ⦃ fun s => ∀ rng,
        let a := s.regs.getRegOrSp src1
        let b := @ExtOrImmReg.interp (_root_.Executable.labels cenv) w src2 s.regs rng
        WP.wp p Q E
          { s with regs := s.regs.setRegOrZr dst (a + b), status := StatusFlags.adds (a + b) a b } ⦄
      (Directive.instr ⟨w, .ADDS_e dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by wp_step; exact hR _ (h rng))

/-- `SUBS Rd, Rn|SP, <imm|extended register>` (`CMP` when `Rd` is `ZR`) : the
difference, and the flags of the subtraction. -/
@[spec] theorem MachineWP.subs_e_spec {w : RegWidth} (dst : RegOrZr w) (src1 : RegOrSp w)
    (src2 : ExtOrImmReg) :
    ⦃ fun s => ∀ rng,
        let a := s.regs.getRegOrSp src1
        let b := @ExtOrImmReg.interp (_root_.Executable.labels cenv) w src2 s.regs rng
        WP.wp p Q E
          { s with regs := s.regs.setRegOrZr dst (a - b), status := StatusFlags.subs (a - b) a b } ⦄
      (Directive.instr ⟨w, .SUBS_e dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by wp_step; exact hR _ (h rng))

/-- `ADD Rd, Rn, Rm{, shift #k}` : no flags. -/
@[spec] theorem MachineWP.add_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src1 + src2.interp s.regs ⟨0, 0⟩) } ⦄
      (Directive.instr ⟨w, .ADD_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `SUB Rd, Rn, Rm{, shift #k}` (`NEG` when `Rn` is `ZR`) : no flags. -/
@[spec] theorem MachineWP.sub_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src1 - src2.interp s.regs ⟨0, 0⟩) } ⦄
      (Directive.instr ⟨w, .SUB_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `ADDS Rd, Rn, Rm{, shift #k}` (`CMN`) : the sum and the flags of the addition. -/
@[spec] theorem MachineWP.adds_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s =>
        let a := s.regs.getRegOrZr src1
        let b := src2.interp s.regs ⟨0, 0⟩
        WP.wp p Q E
          { s with regs := s.regs.setRegOrZr dst (a + b), status := StatusFlags.adds (a + b) a b } ⦄
      (Directive.instr ⟨w, .ADDS_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `SUBS Rd, Rn, Rm{, shift #k}` (`CMP`, `NEGS`) : the difference and the flags
of the subtraction. -/
@[spec] theorem MachineWP.subs_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s =>
        let a := s.regs.getRegOrZr src1
        let b := src2.interp s.regs ⟨0, 0⟩
        WP.wp p Q E
          { s with regs := s.regs.setRegOrZr dst (a - b), status := StatusFlags.subs (a - b) a b } ⦄
      (Directive.instr ⟨w, .SUBS_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-! ### Logical -/

/-- `AND Rd|SP, Rn, #imm`. -/
@[spec] theorem MachineWP.and_i_spec {w : RegWidth} (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) :
    ⦃ fun s => ∀ rng, WP.wp p Q E
        { s with regs := s.regs.setRegOrSp dst
                    (s.regs.getRegOrZr src1 &&& @ConstExpr.immVal (_root_.Executable.labels cenv) w imm rng) } ⦄
      (Directive.instr ⟨w, .AND_i dst src1 imm⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by wp_step; exact hR _ (h rng))

/-- `ORR Rd|SP, Rn, #imm` (`MOV Rd, #imm` of a bitmask immediate). -/
@[spec] theorem MachineWP.orr_i_spec {w : RegWidth} (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) :
    ⦃ fun s => ∀ rng, WP.wp p Q E
        { s with regs := s.regs.setRegOrSp dst
                    (s.regs.getRegOrZr src1 ||| @ConstExpr.immVal (_root_.Executable.labels cenv) w imm rng) } ⦄
      (Directive.instr ⟨w, .ORR_i dst src1 imm⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by wp_step; exact hR _ (h rng))

/-- `EOR Rd|SP, Rn, #imm`. -/
@[spec] theorem MachineWP.eor_i_spec {w : RegWidth} (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) :
    ⦃ fun s => ∀ rng, WP.wp p Q E
        { s with regs := s.regs.setRegOrSp dst
                    (s.regs.getRegOrZr src1 ^^^ @ConstExpr.immVal (_root_.Executable.labels cenv) w imm rng) } ⦄
      (Directive.instr ⟨w, .EOR_i dst src1 imm⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by wp_step; exact hR _ (h rng))

/-- `ANDS Rd, Rn, #imm` (`TST`) : the conjunction; `N`, `Z` from it, `C`, `V` cleared. -/
@[spec] theorem MachineWP.ands_i_spec {w : RegWidth} (dst src1 : RegOrZr w) (imm : ConstExpr) :
    ⦃ fun s => ∀ rng,
        let v := s.regs.getRegOrZr src1 &&& @ConstExpr.immVal (_root_.Executable.labels cenv) w imm rng
        WP.wp p Q E
          { s with regs := s.regs.setRegOrZr dst v,
                   status := StatusFlags.from_result v { c := false, v := false } } ⦄
      (Directive.instr ⟨w, .ANDS_i dst src1 imm⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by wp_step; exact hR _ (h rng))

/-- `AND Rd, Rn, Rm{, shift #k}`. -/
@[spec] theorem MachineWP.and_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src1 &&& src2.interp s.regs ⟨0, 0⟩) } ⦄
      (Directive.instr ⟨w, .AND_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `ORR Rd, Rn, Rm{, shift #k}`. -/
@[spec low] theorem MachineWP.orr_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src1 ||| src2.interp s.regs ⟨0, 0⟩) } ⦄
      (Directive.instr ⟨w, .ORR_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `EOR Rd, Rn, Rm{, shift #k}`. -/
@[spec] theorem MachineWP.eor_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src1 ^^^ src2.interp s.regs ⟨0, 0⟩) } ⦄
      (Directive.instr ⟨w, .EOR_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `BIC Rd, Rn, Rm{, shift #k}` : `Rn` and not `Rm`. -/
@[spec] theorem MachineWP.bic_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src1 &&& ~~~src2.interp s.regs ⟨0, 0⟩) } ⦄
      (Directive.instr ⟨w, .BIC_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `ORN Rd, Rn, Rm{, shift #k}` (`MVN` when `Rn` is `ZR`) : `Rn` or not `Rm`. -/
@[spec] theorem MachineWP.orn_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src1 ||| ~~~src2.interp s.regs ⟨0, 0⟩) } ⦄
      (Directive.instr ⟨w, .ORN_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `EON Rd, Rn, Rm{, shift #k}` : `Rn` xor not `Rm`. -/
@[spec] theorem MachineWP.eon_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src1 ^^^ ~~~src2.interp s.regs ⟨0, 0⟩) } ⦄
      (Directive.instr ⟨w, .EON_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `ANDS Rd, Rn, Rm{, shift #k}` (`TST`) : `N`, `Z` from the conjunction, `C`, `V` cleared. -/
@[spec] theorem MachineWP.ands_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s =>
        let v := s.regs.getRegOrZr src1 &&& src2.interp s.regs ⟨0, 0⟩
        WP.wp p Q E
          { s with regs := s.regs.setRegOrZr dst v,
                   status := StatusFlags.from_result v { c := false, v := false } } ⦄
      (Directive.instr ⟨w, .ANDS_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `BICS Rd, Rn, Rm{, shift #k}` : as `BIC`, with the flags of `ANDS`. -/
@[spec] theorem MachineWP.bics_s_spec {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) :
    ⦃ fun s =>
        let v := s.regs.getRegOrZr src1 &&& ~~~src2.interp s.regs ⟨0, 0⟩
        WP.wp p Q E
          { s with regs := s.regs.setRegOrZr dst v,
                   status := StatusFlags.from_result v { c := false, v := false } } ⦄
      (Directive.instr ⟨w, .BICS_s dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-! ### Bitfield moves and variable shifts -/

/-- `UBFM Rd, Rn, #immr, #imms` (`LSL`/`LSR #k`, `UBFX`, `UBFIZ`, `UXTB`, `UXTH`). -/
@[spec] theorem MachineWP.ubfm_spec {w : RegWidth} (dst src : RegOrZr w) (immr imms : Nat) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (evalUBFM (s.regs.getRegOrZr src) immr imms) } ⦄
      (Directive.instr ⟨w, .UBFM dst src immr imms⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `SBFM Rd, Rn, #immr, #imms` (`ASR #k`, `SBFX`, `SBFIZ`, `SXTB`, `SXTH`, `SXTW`). -/
@[spec] theorem MachineWP.sbfm_spec {w : RegWidth} (dst src : RegOrZr w) (immr imms : Nat) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst (evalSBFM (s.regs.getRegOrZr src) immr imms) } ⦄
      (Directive.instr ⟨w, .SBFM dst src immr imms⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `LSLV Rd, Rn, Rm` (`LSL Rd, Rn, Rm`) : the shift count is `Rm` modulo the width. -/
@[spec] theorem MachineWP.lslv_spec {w : RegWidth} (dst src1 src2 : RegOrZr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    (s.regs.getRegOrZr src1 <<< ((s.regs.getRegOrZr src2).toNat % w.bits)) } ⦄
      (Directive.instr ⟨w, .LSLV dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `LSRV Rd, Rn, Rm` (`LSR Rd, Rn, Rm`). -/
@[spec] theorem MachineWP.lsrv_spec {w : RegWidth} (dst src1 src2 : RegOrZr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    (s.regs.getRegOrZr src1 >>> ((s.regs.getRegOrZr src2).toNat % w.bits)) } ⦄
      (Directive.instr ⟨w, .LSRV dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `ASRV Rd, Rn, Rm` (`ASR Rd, Rn, Rm`). -/
@[spec] theorem MachineWP.asrv_spec {w : RegWidth} (dst src1 src2 : RegOrZr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    ((s.regs.getRegOrZr src1).sshiftRight ((s.regs.getRegOrZr src2).toNat % w.bits)) } ⦄
      (Directive.instr ⟨w, .ASRV dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `RORV Rd, Rn, Rm` (`ROR Rd, Rn, Rm`). -/
@[spec] theorem MachineWP.rorv_spec {w : RegWidth} (dst src1 src2 : RegOrZr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    ((s.regs.getRegOrZr src1).rotateRight ((s.regs.getRegOrZr src2).toNat % w.bits)) } ⦄
      (Directive.instr ⟨w, .RORV dst src1 src2⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-! ### Multiply -/

/-- `MADD Rd, Rn, Rm, Ra` (`MUL` when `Ra` is `ZR`) : `Rn * Rm + Ra`. -/
@[spec] theorem MachineWP.madd_spec {w : RegWidth} (dst src1 src2 src3 : RegOrZr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    (s.regs.getRegOrZr src1 * s.regs.getRegOrZr src2 + s.regs.getRegOrZr src3) } ⦄
      (Directive.instr ⟨w, .MADD dst src1 src2 src3⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `MSUB Rd, Rn, Rm, Ra` (`MNEG` when `Ra` is `ZR`) : `Ra - Rn * Rm`. -/
@[spec] theorem MachineWP.msub_spec {w : RegWidth} (dst src1 src2 src3 : RegOrZr w) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    (s.regs.getRegOrZr src3 - s.regs.getRegOrZr src1 * s.regs.getRegOrZr src2) } ⦄
      (Directive.instr ⟨w, .MSUB dst src1 src2 src3⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-! ### Conditional select and compare -/

/-- `CSEL Rd, Rn, Rm, cond`. -/
@[spec] theorem MachineWP.csel_spec {w : RegWidth} (dst src1 src2 : RegOrZr w) (cond : CondCode) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    (if cond.interp s.status then s.regs.getRegOrZr src1 else s.regs.getRegOrZr src2) } ⦄
      (Directive.instr ⟨w, .CSEL dst src1 src2 cond⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `CSINC Rd, Rn, Rm, cond` (`CSET`, `CINC`). -/
@[spec] theorem MachineWP.csinc_spec {w : RegWidth} (dst src1 src2 : RegOrZr w) (cond : CondCode) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    (if cond.interp s.status then s.regs.getRegOrZr src1
                     else s.regs.getRegOrZr src2 + 1#w.bits) } ⦄
      (Directive.instr ⟨w, .CSINC dst src1 src2 cond⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `CSINV Rd, Rn, Rm, cond` (`CSETM`, `CINV`). -/
@[spec] theorem MachineWP.csinv_spec {w : RegWidth} (dst src1 src2 : RegOrZr w) (cond : CondCode) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    (if cond.interp s.status then s.regs.getRegOrZr src1 else ~~~(s.regs.getRegOrZr src2)) } ⦄
      (Directive.instr ⟨w, .CSINV dst src1 src2 cond⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `CSNEG Rd, Rn, Rm, cond` (`CNEG`). -/
@[spec] theorem MachineWP.csneg_spec {w : RegWidth} (dst src1 src2 : RegOrZr w) (cond : CondCode) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    (if cond.interp s.status then s.regs.getRegOrZr src1 else -(s.regs.getRegOrZr src2)) } ⦄
      (Directive.instr ⟨w, .CSNEG dst src1 src2 cond⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `CCMP Rn, Rm, #nzcv, cond` : the flags of `Rn - Rm` if `cond` holds, else `#nzcv`. -/
@[spec] theorem MachineWP.ccmp_reg_spec {w : RegWidth} (src1 src2 : RegOrZr w) (nzcv : Nat)
    (cond : CondCode) :
    ⦃ fun s =>
        let a := s.regs.getRegOrZr src1
        let b := s.regs.getRegOrZr src2
        WP.wp p Q E
          { s with status := if cond.interp s.status then StatusFlags.subs (a - b) a b
                             else StatusFlags.ofNat nzcv } ⦄
      (Directive.instr ⟨w, .CCMP_reg src1 src2 nzcv cond⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `CCMP Rn, #imm, #nzcv, cond`. -/
@[spec] theorem MachineWP.ccmp_imm_spec {w : RegWidth} (src1 : RegOrZr w) (imm nzcv : Nat)
    (cond : CondCode) :
    ⦃ fun s =>
        let a := s.regs.getRegOrZr src1
        let b := BitVec.ofNat w.bits imm
        WP.wp p Q E
          { s with status := if cond.interp s.status then StatusFlags.subs (a - b) a b
                             else StatusFlags.ofNat nzcv } ⦄
      (Directive.instr ⟨w, .CCMP_imm src1 imm nzcv cond⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `CCMN Rn, Rm, #nzcv, cond` : the flags of `Rn + Rm` if `cond` holds, else `#nzcv`. -/
@[spec] theorem MachineWP.ccmn_reg_spec {w : RegWidth} (src1 src2 : RegOrZr w) (nzcv : Nat)
    (cond : CondCode) :
    ⦃ fun s =>
        let a := s.regs.getRegOrZr src1
        let b := s.regs.getRegOrZr src2
        WP.wp p Q E
          { s with status := if cond.interp s.status then StatusFlags.adds (a + b) a b
                             else StatusFlags.ofNat nzcv } ⦄
      (Directive.instr ⟨w, .CCMN_reg src1 src2 nzcv cond⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `CCMN Rn, #imm, #nzcv, cond`. -/
@[spec] theorem MachineWP.ccmn_imm_spec {w : RegWidth} (src1 : RegOrZr w) (imm nzcv : Nat)
    (cond : CondCode) :
    ⦃ fun s =>
        let a := s.regs.getRegOrZr src1
        let b := BitVec.ofNat w.bits imm
        WP.wp p Q E
          { s with status := if cond.interp s.status then StatusFlags.adds (a + b) a b
                             else StatusFlags.ofNat nzcv } ⦄
      (Directive.instr ⟨w, .CCMN_imm src1 imm nzcv cond⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-! ### Loads and stores

`AddrExpr.eval a s rng` is the address and the state after any base
writeback; at each addressing form `Specs.lean` reduces it (`AddrExpr.eval_imm`,
`eval_pre`, `eval_post`, `eval_reg`). -/

/-- `LDR Rt, [Xn|SP …]` : the bytes must be readable; the tail runs with them
in `Rt` (a `W` load zero-extends), after the base writeback. -/
@[spec] theorem MachineWP.ldr_spec {w : RegWidth} (dst : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt e.2.dmem e.1 w.bytes).isSome = true)
          ⊓ (∀ v, Mem.loadInt e.2.dmem e.1 w.bytes = some v →
            WP.wp p Q E { e.2 with regs := e.2.regs.setRegOrZr dst (BitVec.ofInt w.bits v) }) ⦄
      (Directive.instr ⟨w, .LDR dst (.addr a)⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [AddrOrLit.interpLoad, AddrExpr.interpLoad]
    exact AddrExpr.checkSP_All ha (MachineData.load_All hv (hR _ (hk v hv))))

/-- `STR Rt, [Xn|SP …]` : the bytes must be owned (readable); the tail runs on
the updated memory, after the base writeback. -/
@[spec] theorem MachineWP.str_spec {w : RegWidth} (src : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt e.2.dmem e.1 w.bytes).isSome = true)
          ⊓ WP.wp p Q E { e.2 with
              dmem := Mem.storeInt e.2.dmem e.1 w.bytes (s.regs.getRegOrZr src).toInt } ⦄
      (Directive.instr ⟨w, .STR src a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    wp_step
    simp only [AddrExpr.interpStore]
    exact AddrExpr.checkSP_All ha (MachineData.store_All hsome (hR _ hk)))

/-- `LDRB Wt, [Xn|SP …]` : the byte, zero-extended. -/
@[spec] theorem MachineWP.ldrb_spec (dst : RegOrZr .W32) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt e.2.dmem e.1 1).isSome = true)
          ⊓ (∀ v, Mem.loadInt e.2.dmem e.1 1 = some v →
            WP.wp p Q E { e.2 with regs := e.2.regs.setRegOrZr dst ((BitVec.ofInt 8 v).setWidth 32) }) ⦄
      (Directive.instr ⟨.W32, .LDRB dst a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [AddrExpr.interpLoad]
    exact AddrExpr.checkSP_All ha (MachineData.load_All (w := .W8) hv (hR _ (hk v hv))))

/-- `LDRH Wt, [Xn|SP …]` : the halfword, zero-extended. -/
@[spec] theorem MachineWP.ldrh_spec (dst : RegOrZr .W32) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt e.2.dmem e.1 2).isSome = true)
          ⊓ (∀ v, Mem.loadInt e.2.dmem e.1 2 = some v →
            WP.wp p Q E { e.2 with regs := e.2.regs.setRegOrZr dst ((BitVec.ofInt 16 v).setWidth 32) }) ⦄
      (Directive.instr ⟨.W32, .LDRH dst a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [AddrExpr.interpLoad]
    exact AddrExpr.checkSP_All ha (MachineData.load_All (w := .W16) hv (hR _ (hk v hv))))

/-- `STRB Wt, [Xn|SP …]` : the low byte stored. -/
@[spec] theorem MachineWP.strb_spec (src : RegOrZr .W32) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt e.2.dmem e.1 1).isSome = true)
          ⊓ WP.wp p Q E { e.2 with
              dmem := Mem.storeInt e.2.dmem e.1 1 ((s.regs.getRegOrZr src).setWidth 8).toInt } ⦄
      (Directive.instr ⟨.W32, .STRB src a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    wp_step
    simp only [AddrExpr.interpStore, BitVec.take_eq_setWidth]
    exact AddrExpr.checkSP_All ha (MachineData.store_All (w := .W8) hsome (hR _ hk)))

/-- `STRH Wt, [Xn|SP …]` : the low halfword stored. -/
@[spec] theorem MachineWP.strh_spec (src : RegOrZr .W32) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt e.2.dmem e.1 2).isSome = true)
          ⊓ WP.wp p Q E { e.2 with
              dmem := Mem.storeInt e.2.dmem e.1 2 ((s.regs.getRegOrZr src).setWidth 16).toInt } ⦄
      (Directive.instr ⟨.W32, .STRH src a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    wp_step
    simp only [AddrExpr.interpStore, BitVec.take_eq_setWidth]
    exact AddrExpr.checkSP_All ha (MachineData.store_All (w := .W16) hsome (hR _ hk)))

/-- `LDP Rt1, Rt2, [Xn|SP …]` : two loads, at the address and the next slot,
both readable; the tail runs with both registers written, after the base
writeback. -/
@[spec] theorem MachineWP.ldp_spec {w : RegWidth} (dst1 dst2 : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let a₂ := e.1 + BitVec.ofNat 64 w.bytes
        ((Mem.loadInt e.2.dmem e.1 w.bytes).isSome = true)
          ⊓ ((Mem.loadInt e.2.dmem a₂ w.bytes).isSome = true)
          ⊓ (∀ v₁ v₂, Mem.loadInt e.2.dmem e.1 w.bytes = some v₁ →
              Mem.loadInt e.2.dmem a₂ w.bytes = some v₂ →
            let r := (e.2.regs.setRegOrZr dst1 (BitVec.ofInt w.bits v₁)).setRegOrZr dst2
              (BitVec.ofInt w.bits v₂)
            WP.wp p Q E { e.2 with regs := r }) ⦄
      (Directive.instr ⟨w, .LDP dst1 dst2 a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨⟨hsome₁, hsome₂⟩, hk⟩ := h rng
    obtain ⟨v₁, hv₁⟩ := Option.isSome_iff_exists.mp hsome₁
    obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp hsome₂
    wp_step
    exact AddrExpr.checkSP_All ha (MachineData.load_All hv₁ (MachineData.load_All hv₂
      (hR _ (hk v₁ v₂ hv₁ hv₂)))))

/-- `STP Rt1, Rt2, [Xn|SP …]` : two stores, at the address and the next slot,
both owned; the tail runs on the updated memory, after the base writeback. -/
@[spec] theorem MachineWP.stp_spec {w : RegWidth} (src1 src2 : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let a₂ := e.1 + BitVec.ofNat 64 w.bytes
        let m₁ := Mem.storeInt e.2.dmem e.1 w.bytes (s.regs.getRegOrZr src1).toInt
        ((Mem.loadInt e.2.dmem e.1 w.bytes).isSome = true)
          ⊓ ((Mem.loadInt m₁ a₂ w.bytes).isSome = true)
          ⊓ WP.wp p Q E { e.2 with
              dmem := Mem.storeInt m₁ a₂ w.bytes (s.regs.getRegOrZr src2).toInt } ⦄
      (Directive.instr ⟨w, .STP src1 src2 a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨⟨hsome₁, hsome₂⟩, hk⟩ := h rng
    wp_step
    exact AddrExpr.checkSP_All ha (MachineData.store_All hsome₁ (MachineData.store_All hsome₂
      (hR _ hk))))

/-! ### Addresses of labels -/

/-- `ADR Xd, label` : the label's address, wherever the instruction sits. -/
@[spec] theorem MachineWP.adr_label_spec (dst : RegOrZr .W64) (l : Label) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst ((_root_.Executable.labels cenv).label l).toBitVec } ⦄
      (Directive.instr ⟨.W64, .ADR dst (.label l)⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; simpa using hP)

/-- `ADRP Xd, label` : the address of the label's 4KB page. -/
@[spec] theorem MachineWP.adrp_label_spec (dst : RegOrZr .W64) (l : Label) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrZr dst
                    (((_root_.Executable.labels cenv).label l).toBitVec &&& ~~~0xFFF#64) } ⦄
      (Directive.instr ⟨.W64, .ADRP dst (.label l)⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; simpa using hP)

end Specs

/-! ## Rules at an address

`ADR`/`ADRP` with a numeric offset read the pc: the value is relative to the
instruction's own address, which no position-independent precondition can
name. Their rules are `TripleAt` judgments at that address, like x64's
`lea_rip_disp_at`. -/

namespace MachineWP

/-- `ADR Xd, #imm` at `pc` : the register gets `pc + imm`. -/
theorem adr_imm_at [CodeEnv] (dst : RegOrZr .W64) (imm : Int64) (pc : Int64)
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    TripleAt pc
      (fun s => Q () { s with regs := s.regs.setRegOrZr dst (pc.toBitVec + imm.toBitVec) })
      [Directive.instr ⟨.W64, .ADR dst (.int64 imm)⟩] Q E := by
  intro s hq hs
  obtain ⟨z, rest, hseg, -⟩ := hs
  simp only [Executable.after, hseg]
  refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setRegOrZr, Effects.All]
  refine Eventually.done _ (Or.inl ⟨rfl, ?_⟩)
  simpa [BitVec.ofInt_add] using hq

/-- `ADRP Xd, #imm` at `pc` : the register gets the 4KB page of `pc + imm`. -/
theorem adrp_imm_at [CodeEnv] (dst : RegOrZr .W64) (imm : Int64) (pc : Int64)
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    TripleAt pc
      (fun s =>
        Q () { s with regs := s.regs.setRegOrZr dst ((pc.toBitVec + imm.toBitVec) &&& ~~~0xFFF#64) })
      [Directive.instr ⟨.W64, .ADRP dst (.int64 imm)⟩] Q E := by
  intro s hq hs
  obtain ⟨z, rest, hseg, -⟩ := hs
  simp only [Executable.after, hseg]
  refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setRegOrZr, Effects.All]
  refine Eventually.done _ (Or.inl ⟨rfl, ?_⟩)
  simpa [BitVec.ofInt_add] using hq

end MachineWP
