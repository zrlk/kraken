import Kraken.AArch64.LSE2

/-!
**AArch64 instruction semantics depend only on the labels an instruction
names** (shared by the post-pass transfer, `Spike/Lib/A64RestTail.lean`):
the granule pass re-places `scc_text_end` and adds `.Lgw0`, so the pre- and
post-pass executables resolve labels differently (`Executable.labels`); an
instruction naming neither interprets alike under both.

- `ConstExpr.Free`, `ExtOrImmReg.Free`, `AddrExpr.Free`,
  `UnscaledAddrExpr.Free`, `Literal.Free`, `AddrOrLit.Free`,
  `Operation.Free` (one arm per constructor, its label-bearing operands),
  `Instr.Free`, `Directive.Free`: the syntax names no label of `B`;
- `constExpr_congr` … `aolLoad_congr`: each operand's interpretation agrees
  under two label maps agreeing off `B`;
- `op_congr`, `instr_congr`, `directive_congr`, `directives_congr`: the
  instruction's (`Kraken/AArch64/Semantics.lean`);
- `lse2q_congr`, `lse2_congr`: the FEAT_LSE2 reading's
  (`Kraken/AArch64/LSE2.lean`), the one `isaLSE2` executes.
-/

namespace Spike.Lib.A64LabelCongr

variable (B : List Label)

/-- A constant expression names no label of `B`. -/
def ConstExpr.Free : ConstExpr → Prop
  | .label l => l ∉ B
  | .int64 _ | .before_current_instruction | .after_current_instruction => True
  | .add a b | .sub a b => ConstExpr.Free a ∧ ConstExpr.Free b
  | .pg_hi21 e | .lo12 e => ConstExpr.Free e

/-- An extended-or-immediate operand names no label of `B`. -/
def ExtOrImmReg.Free : ExtOrImmReg → Prop
  | .ext _ => True
  | .imm i => ConstExpr.Free B i.imm

/-- An address operand names no label of `B` (its immediate offset's). -/
def AddrExpr.Free (a : AddrExpr) : Prop :=
  match a.off with
  | .imm i => ConstExpr.Free B i.imm
  | .reg _ => True

/-- An unscaled address operand names no label of `B`. -/
def UnscaledAddrExpr.Free (a : UnscaledAddrExpr) : Prop := ConstExpr.Free B a.imm

/-- A literal operand names no label of `B`. -/
def Literal.Free : Literal → Prop
  | .addr a => a.label ∉ B
  | .pool e => ConstExpr.Free B e.expr

/-- An address-or-literal operand names no label of `B`. -/
def AddrOrLit.Free : AddrOrLit → Prop
  | .addr a => AddrExpr.Free B a
  | .lit l => Literal.Free B l

/-- An operation names no label of `B`: its label-bearing operands' (one arm
per constructor of `Operation`, `Kraken/AArch64/Syntax.lean`). -/
def Operation.Free {w : RegWidth} (op : Operation w) : Prop :=
  match op with
  | .LDR _ x1 => AddrOrLit.Free B x1
  | .STR _ x1 => AddrExpr.Free B x1
  | .LDUR _ x1 => UnscaledAddrExpr.Free B x1
  | .STUR _ x1 => UnscaledAddrExpr.Free B x1
  | .LDP _ _ x2 => AddrExpr.Free B x2
  | .STP _ _ x2 => AddrExpr.Free B x2
  | .LDRB _ x1 => AddrExpr.Free B x1
  | .LDURB _ x1 => UnscaledAddrExpr.Free B x1
  | .STRB _ x1 => AddrExpr.Free B x1
  | .STURB _ x1 => UnscaledAddrExpr.Free B x1
  | .LDRSB _ x1 => AddrExpr.Free B x1
  | .LDURSB _ x1 => UnscaledAddrExpr.Free B x1
  | .LDRH _ x1 => AddrExpr.Free B x1
  | .LDURH _ x1 => UnscaledAddrExpr.Free B x1
  | .STRH _ x1 => AddrExpr.Free B x1
  | .STURH _ x1 => UnscaledAddrExpr.Free B x1
  | .LDRSH _ x1 => AddrExpr.Free B x1
  | .LDURSH _ x1 => UnscaledAddrExpr.Free B x1
  | .LDRSW _ x1 => AddrOrLit.Free B x1
  | .LDURSW _ x1 => UnscaledAddrExpr.Free B x1
  | .LDPSW _ _ x2 => AddrExpr.Free B x2
  | .ADD_e _ _ x2 => ExtOrImmReg.Free B x2
  | .ADD_s _ _ _ => True
  | .ADDS_e _ _ x2 => ExtOrImmReg.Free B x2
  | .ADDS_s _ _ _ => True
  | .SUB_e _ _ x2 => ExtOrImmReg.Free B x2
  | .SUB_s _ _ _ => True
  | .SUBS_e _ _ x2 => ExtOrImmReg.Free B x2
  | .SUBS_s _ _ _ => True
  | .ADC _ _ _ => True
  | .ADCS _ _ _ => True
  | .SBC _ _ _ => True
  | .SBCS _ _ _ => True
  | .SDIV _ _ _ => True
  | .UDIV _ _ _ => True
  | .MADD _ _ _ _ => True
  | .MSUB _ _ _ _ => True
  | .SMULH _ _ _ => True
  | .UMULH _ _ _ => True
  | .SMADDL _ _ _ _ => True
  | .UMADDL _ _ _ _ => True
  | .SMSUBL _ _ _ _ => True
  | .UMSUBL _ _ _ _ => True
  | .AND_i _ _ x2 => ConstExpr.Free B x2
  | .AND_s _ _ _ => True
  | .ANDS_i _ _ x2 => ConstExpr.Free B x2
  | .ANDS_s _ _ _ => True
  | .ORR_i _ _ x2 => ConstExpr.Free B x2
  | .ORR_s _ _ _ => True
  | .ORN_s _ _ _ => True
  | .EOR_i _ _ x2 => ConstExpr.Free B x2
  | .EOR_s _ _ _ => True
  | .EON_s _ _ _ => True
  | .BIC_s _ _ _ => True
  | .BICS_s _ _ _ => True
  | .BFM _ _ _ _ => True
  | .SBFM _ _ _ _ => True
  | .UBFM _ _ _ _ => True
  | .CLZ _ _ => True
  | .CLS _ _ => True
  | .RBIT _ _ => True
  | .REV _ _ => True
  | .REV16 _ _ => True
  | .REV32 _ _ => True
  | .EXTR _ _ _ _ => True
  | .MOVZ _ x1 _ => ConstExpr.Free B x1
  | .MOVK _ x1 _ => ConstExpr.Free B x1
  | .MOVN _ x1 _ => ConstExpr.Free B x1
  | .LSLV _ _ _ => True
  | .LSRV _ _ _ => True
  | .ASRV _ _ _ => True
  | .RORV _ _ _ => True
  | .CSEL _ _ _ _ => True
  | .CSINC _ _ _ _ => True
  | .CSINV _ _ _ _ => True
  | .CSNEG _ _ _ _ => True
  | .CCMP_reg _ _ _ _ => True
  | .CCMP_imm _ _ _ _ => True
  | .CCMN_reg _ _ _ _ => True
  | .CCMN_imm _ _ _ _ => True
  | .ADR _ x1 => ConstExpr.Free B x1
  | .ADRP _ x1 => ConstExpr.Free B x1
  | .B x0 => ConstExpr.Free B x0
  | .B_cond _ x1 => ConstExpr.Free B x1
  | .BL x0 => ConstExpr.Free B x0
  | .BLR _ => True
  | .BR _ => True
  | .RET _ => True
  | .CBZ _ x1 => ConstExpr.Free B x1
  | .CBNZ _ x1 => ConstExpr.Free B x1
  | .TBZ _ _ x2 => ConstExpr.Free B x2
  | .TBNZ _ _ x2 => ConstExpr.Free B x2
  | .LDAR _ _ _ _ _ => True
  | .STLR _ _ _ => True
  | .STXR _ _ _ _ _ => True
  | .CAS _ _ _ _ _ => True
  | .SWP _ _ _ _ _ => True
  | .LDOP _ _ _ _ _ _ => True
  | .LDXP _ _ _ _ => True
  | .STXP _ _ _ _ _ => True
  | .CASP _ _ _ _ _ _ => True
  | .DMB _ => True
  | .DSB _ => True
  | .ISB => True
  | .NOP => True
  | .SVC _ => True
  | .MRS _ _ => True
  | .MSR _ _ => True

/-- An instruction names no label of `B`. -/
def Instr.Free (i : Instr) : Prop := Operation.Free B i.operation

/-- A cell names no label of `B` (only instructions name labels). -/
def Directive.Free : Directive → Prop
  | .instr i => Instr.Free B i
  | _ => True

/-! Each `Free` is decidable, so a concrete text's `Directive.Free` follows
by `decide`. -/

instance ConstExpr.decFree : ∀ e : ConstExpr, Decidable (ConstExpr.Free B e)
  | .label l => inferInstanceAs (Decidable (l ∉ B))
  | .int64 _ | .before_current_instruction | .after_current_instruction => isTrue trivial
  | .add a b | .sub a b =>
    have := ConstExpr.decFree a; have := ConstExpr.decFree b
    inferInstanceAs (Decidable (ConstExpr.Free B a ∧ ConstExpr.Free B b))
  | .pg_hi21 e | .lo12 e => ConstExpr.decFree e

instance ExtOrImmReg.decFree (e : ExtOrImmReg) : Decidable (ExtOrImmReg.Free B e) := by
  unfold ExtOrImmReg.Free; split <;> infer_instance

instance AddrExpr.decFree (a : AddrExpr) : Decidable (AddrExpr.Free B a) := by
  unfold AddrExpr.Free; split <;> infer_instance

instance UnscaledAddrExpr.decFree (a : UnscaledAddrExpr) : Decidable (UnscaledAddrExpr.Free B a) := by
  unfold UnscaledAddrExpr.Free; infer_instance

instance Literal.decFree (l : Literal) : Decidable (Literal.Free B l) := by
  unfold Literal.Free; split <;> infer_instance

instance AddrOrLit.decFree (a : AddrOrLit) : Decidable (AddrOrLit.Free B a) := by
  unfold AddrOrLit.Free; split <;> infer_instance

instance Operation.decFree {w : RegWidth} (op : Operation w) : Decidable (Operation.Free B op) := by
  unfold Operation.Free; split <;> infer_instance

instance Instr.decFree (i : Instr) : Decidable (Instr.Free B i) := Operation.decFree B i.operation

instance Directive.decFree (d : Directive) : Decidable (Directive.Free B d) := by
  unfold Directive.Free; split <;> infer_instance

variable {B} (L1 L2 : Labels) (hL : ∀ l, l ∉ B → L1.label l = L2.label l)
include hL

/-- **A constant expression's value** agrees under label maps agreeing off
`B` when it names no label of `B`; likewise for each operand below. -/
theorem constExpr_congr : ∀ (e : ConstExpr), ConstExpr.Free B e → ∀ p,
    @ConstExpr.interp L1 e p = @ConstExpr.interp L2 e p
  | .label l, h, _ => hL l h
  | .int64 _, _, _ | .before_current_instruction, _, _ | .after_current_instruction, _, _ => rfl
  | .add a b, h, p | .sub a b, h, p => by
    simp only [ConstExpr.interp, constExpr_congr a h.1 p, constExpr_congr b h.2 p]
  | .pg_hi21 e, h, p | .lo12 e, h, p => by
    simp only [ConstExpr.interp, constExpr_congr e h p]

theorem branch_congr (e : ConstExpr) (h : ConstExpr.Free B e) (p) :
    @ConstExpr.evalBranchTarget L1 e p = @ConstExpr.evalBranchTarget L2 e p := by
  unfold ConstExpr.evalBranchTarget
  split
  · rfl
  · exact constExpr_congr L1 L2 hL e h p

theorem extOrImm_congr {w : RegWidth} (e : ExtOrImmReg) (h : ExtOrImmReg.Free B e) (s p) :
    @ExtOrImmReg.interp L1 w e s p = @ExtOrImmReg.interp L2 w e s p := by
  cases e with
  | ext _ => rfl
  | imm i => simp only [ExtOrImmReg.interp, constExpr_congr L1 L2 hL i.imm h p]

theorem addrEval_congr (a : AddrExpr) (h : AddrExpr.Free B a) (s p) :
    @AddrExpr.eval L1 a s p = @AddrExpr.eval L2 a s p := by
  rcases a with ⟨b, off⟩
  cases off with
  | reg _ => rfl
  | imm i => simp only [AddrExpr.eval, constExpr_congr L1 L2 hL i.imm h p]

theorem addrLoad_congr {w : MemWidth} (a : AddrExpr) (h : AddrExpr.Free B a) (s p ret) :
    @AddrExpr.interpLoad L1 w a s p ret = @AddrExpr.interpLoad L2 w a s p ret := by
  simp only [AddrExpr.interpLoad, addrEval_congr L1 L2 hL a h]

theorem addrStore_congr {w : MemWidth} (a : AddrExpr) (h : AddrExpr.Free B a) (s p v next) :
    @AddrExpr.interpStore L1 w a s p v next = @AddrExpr.interpStore L2 w a s p v next := by
  simp only [AddrExpr.interpStore, addrEval_congr L1 L2 hL a h]

theorem uEval_congr (a : UnscaledAddrExpr) (h : UnscaledAddrExpr.Free B a) (s p) :
    @UnscaledAddrExpr.eval L1 a s p = @UnscaledAddrExpr.eval L2 a s p := by
  simp only [UnscaledAddrExpr.eval, constExpr_congr L1 L2 hL a.imm h p]

theorem uLoad_congr {w : MemWidth} (a : UnscaledAddrExpr) (h : UnscaledAddrExpr.Free B a) (s p ret) :
    @UnscaledAddrExpr.interpLoad L1 w a s p ret = @UnscaledAddrExpr.interpLoad L2 w a s p ret := by
  simp only [UnscaledAddrExpr.interpLoad, uEval_congr L1 L2 hL a h]

theorem uStore_congr {w : MemWidth} (a : UnscaledAddrExpr) (h : UnscaledAddrExpr.Free B a) (s p v next) :
    @UnscaledAddrExpr.interpStore L1 w a s p v next = @UnscaledAddrExpr.interpStore L2 w a s p v next := by
  simp only [UnscaledAddrExpr.interpStore, uEval_congr L1 L2 hL a h]

theorem litLoad_congr {w : MemWidth} (a : Literal) (h : Literal.Free B a) (s p ret) :
    @Literal.interpLoad L1 w a s p ret = @Literal.interpLoad L2 w a s p ret := by
  cases a with
  | addr x => simp only [Literal.interpLoad, hL x.label h]
  | pool e => simp only [Literal.interpLoad, constExpr_congr L1 L2 hL e.expr h p]

theorem aolLoad_congr {w : MemWidth} (a : AddrOrLit) (h : AddrOrLit.Free B a) (s p ret) :
    @AddrOrLit.interpLoad L1 w a s p ret = @AddrOrLit.interpLoad L2 w a s p ret := by
  cases a with
  | addr x => exact addrLoad_congr L1 L2 hL x h s p ret
  | lit x => exact litLoad_congr L1 L2 hL x h s p ret

/-- **An operation's interpretation** agrees under label maps agreeing off
`B` when it names no label of `B`. -/
theorem op_congr {w : RegWidth} (op : Operation w) (hf : Operation.Free B op) (p s next jmp) :
    @Operation.interp L1 w op p s next jmp = @Operation.interp L2 w op p s next jmp := by
  cases op <;> simp only [Operation.Free] at hf <;>
    simp (disch := first | assumption | exact hf) only [Operation.interp, constExpr_congr L1 L2 hL,
      branch_congr L1 L2 hL, extOrImm_congr L1 L2 hL, addrEval_congr L1 L2 hL, addrLoad_congr L1 L2 hL,
      addrStore_congr L1 L2 hL, uLoad_congr L1 L2 hL, uStore_congr L1 L2 hL,
      aolLoad_congr L1 L2 hL]

theorem instr_congr (i : Instr) (hf : Instr.Free B i) (s p next jmp) :
    @Instr.interp L1 i s p next jmp = @Instr.interp L2 i s p next jmp := by
  simp only [Instr.interp, op_congr L1 L2 hL i.operation hf]

theorem directive_congr (d : Directive) (hf : Directive.Free B d) (s p next jmp) :
    @Directive.interp L1 d s p next jmp = @Directive.interp L2 d s p next jmp := by
  cases d with
  | instr i => exact instr_congr L1 L2 hL i hf s p next jmp
  | _ => rfl

/-- **A run of cells' interpretation** agrees when no cell names a label of
`B`. -/
theorem directives_congr : ∀ (ds : List (Directive × Nat)), (∀ d ∈ ds, Directive.Free B d.1) → ∀ s pc ret,
    @Directives.interp L1 ds s pc ret = @Directives.interp L2 ds s pc ret
  | [], _, _, _, _ => rfl
  | (d, sz) :: ds, hf, s, pc, ret => by
    simp only [Directives.interp]
    rw [directive_congr L1 L2 hL d (hf _ (List.mem_cons_self ..))]
    congr 1
    funext s'
    exact directives_congr ds (fun x hx => hf x (List.mem_cons_of_mem _ hx)) s' _ ret

theorem lse2q_congr (d : Directive) (hf : Directive.Free B d) (s p next) :
    @Directive.interpLSE2? L1 d s p next = @Directive.interpLSE2? L2 d s p next := by
  unfold Directive.interpLSE2?
  split
  · rename_i dst1 dst2 src
    have h : AddrExpr.Free B src := hf
    simp only [addrEval_congr L1 L2 hL src h]
  · rename_i src1 src2 dst
    have h : AddrExpr.Free B dst := hf
    simp only [addrEval_congr L1 L2 hL dst h]
  · rfl

/-- **The FEAT_LSE2 reading of a cell** agrees when it names no label of
`B`. -/
theorem lse2_congr (d : Directive) (hf : Directive.Free B d) (s p next jmp) :
    @Directive.interpLSE2 L1 d s p next jmp = @Directive.interpLSE2 L2 d s p next jmp := by
  simp only [Directive.interpLSE2, lse2q_congr L1 L2 hL d hf, directive_congr L1 L2 hL d hf]

end Spike.Lib.A64LabelCongr

-- `Free` decides: a label off `B` is free, one in `B` is not.
#guard decide (Spike.Lib.A64LabelCongr.ConstExpr.Free ["scc_text_end"] (.sub (.label "f") .after_current_instruction))
#guard !decide (Spike.Lib.A64LabelCongr.ConstExpr.Free ["scc_text_end"] (.lo12 (.label "scc_text_end")))

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64LabelCongr.op_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64LabelCongr.op_congr

/-- info: 'Spike.Lib.A64LabelCongr.directives_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64LabelCongr.directives_congr

/-- info: 'Spike.Lib.A64LabelCongr.lse2_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64LabelCongr.lse2_congr
