/-
Spike: an x86-64 instruction's interpretation depends on the label table only
at the labels it mentions. Each `Free` is decidable (`Directive.decFree`).
-/
import Kraken.X64.Semantics

namespace Spike.Lib.X64LabelCongr

/-- The constant expression names no label of `B`. -/
def ConstExpr.Free (B : List Label) : ConstExpr → Prop
  | .label l => l ∉ B
  | .add a b => ConstExpr.Free B a ∧ ConstExpr.Free B b
  | .sub a b => ConstExpr.Free B a ∧ ConstExpr.Free B b
  | _ => True

/-- The address expression's displacement names no label of `B`. -/
def AddrExpr.Free (B : List Label) (a : AddrExpr) : Prop := ConstExpr.Free B a.disp

/-- A register or memory operand names no label of `B`. -/
def RegOrMem.Free {w} (B : List Label) : RegOrMem w → Prop
  | .reg _ => True
  | .mem a => AddrExpr.Free B a

/-- A vector register or memory operand names no label of `B`. -/
def AvxRegOrMem.Free {w} (B : List Label) : AvxRegOrMem w → Prop
  | .avx _ => True
  | .mem a => AddrExpr.Free B a

/-- An operand names no label of `B`. -/
def Operand.Free {w} (B : List Label) : Operand w → Prop
  | .regOrMem rm => RegOrMem.Free B rm
  | .imm v => ConstExpr.Free B v

/-- A shift count names no label of `B`. -/
def ShiftCountExpr.Free (B : List Label) : ShiftCountExpr → Prop
  | .cl => True
  | .imm8 v => ConstExpr.Free B v

/-- A branch target names no label of `B`. -/
def RelRegOrMem.Free (B : List Label) : RelRegOrMem → Prop
  | .rel c => ConstExpr.Free B c
  | .reg _ => True
  | .mem a => AddrExpr.Free B a

/-- An operation names no label of `B` (its operands do not). -/
def Operation.Free {w} (B : List Label) : Operation w → Prop
  | .mov x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1
  | .movsx x0 x1 => RegOrMem.Free B x0 ∧ RegOrMem.Free B x1
  | .movzx x0 x1 => RegOrMem.Free B x0 ∧ RegOrMem.Free B x1
  | .push x0 => Operand.Free B x0
  | .pop x0 => RegOrMem.Free B x0
  | .setcc _ x1 => RegOrMem.Free B x1
  | .cmovcc _ _ x2 => RegOrMem.Free B x2
  | .lea _ x1 => AddrExpr.Free B x1
  | .add x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1
  | .adc x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1
  | .adcx _ x1 => RegOrMem.Free B x1
  | .adox _ x1 => RegOrMem.Free B x1
  | .inc x0 => RegOrMem.Free B x0
  | .dec x0 => RegOrMem.Free B x0
  | .neg x0 => RegOrMem.Free B x0
  | .sub x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1
  | .sbb x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1
  | .cmp x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1
  | .mul x0 => RegOrMem.Free B x0
  | .mulx _ _ x2 => RegOrMem.Free B x2
  | .imul1 x0 => RegOrMem.Free B x0
  | .imul x0 x1 x2 => (∀ d, x0 = some d → RegOrMem.Free B d) ∧ RegOrMem.Free B x1 ∧ Operand.Free B x2
  | .test x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1
  | .and x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1
  | .not x0 => RegOrMem.Free B x0
  | .or x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1
  | .xor x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1
  | .shl x0 x1 => RegOrMem.Free B x0 ∧ ShiftCountExpr.Free B x1
  | .shr x0 x1 => RegOrMem.Free B x0 ∧ ShiftCountExpr.Free B x1
  | .sar x0 x1 => RegOrMem.Free B x0 ∧ ShiftCountExpr.Free B x1
  | .shld x0 _ x2 => RegOrMem.Free B x0 ∧ ShiftCountExpr.Free B x2
  | .shrd x0 _ x2 => RegOrMem.Free B x0 ∧ ShiftCountExpr.Free B x2
  | .rol x0 x1 => RegOrMem.Free B x0 ∧ ShiftCountExpr.Free B x1
  | .ror x0 x1 => RegOrMem.Free B x0 ∧ ShiftCountExpr.Free B x1
  | .rcl x0 x1 => RegOrMem.Free B x0 ∧ ShiftCountExpr.Free B x1
  | .rcr x0 x1 => RegOrMem.Free B x0 ∧ ShiftCountExpr.Free B x1
  | .bswap _ => True
  | .tzcnt _ x1 => RegOrMem.Free B x1
  | .jcc _ x1 => x1 ∉ B
  | .jmp x0 => RelRegOrMem.Free B x0
  | .call x0 => RelRegOrMem.Free B x0
  | .ret => True
  | .nop _ => True
  | .nopalign _ _ => True
  | .lockBin _ x1 x2 => AddrExpr.Free B x1 ∧ Operand.Free B x2
  | .lockUn _ x1 => AddrExpr.Free B x1
  | .xchg _ x1 => RegOrMem.Free B x1
  | .xadd _ x1 _ => RegOrMem.Free B x1
  | .cmpxchg _ x1 _ => RegOrMem.Free B x1
  | .mfence => True
  | .lfence => True
  | .sfence => True
  | .movnti x0 _ => AddrExpr.Free B x0
  | .syscall => True
  | .movfs x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1
  | .ud2 => True
  | .div x0 => RegOrMem.Free B x0
  | .idiv x0 => RegOrMem.Free B x0
  | .cqo => True
  | .popcnt _ x1 => RegOrMem.Free B x1
  | .cmpfs x0 x1 => RegOrMem.Free B x0 ∧ Operand.Free B x1

/-- A vector operation names no label of `B` (its operands do not). -/
def AvxOperation.Free {w} (B : List Label) : AvxOperation w → Prop
  | .movups x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .vmovups x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .movaps x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .subps x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .addps x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .mulps x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .xorps x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .vmovaps x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .vxorps _ _ x2 => AvxRegOrMem.Free B x2
  | .vaddps _ _ x2 => AvxRegOrMem.Free B x2
  | .vmulps _ _ x2 => AvxRegOrMem.Free B x2
  | .vfmadd231ps _ _ x2 => AvxRegOrMem.Free B x2
  | .vshufps _ _ x2 _ => AvxRegOrMem.Free B x2
  | .vextractf128 _ _ _ => True
  | .vmovhlps _ _ _ => True
  | .vmovss _ _ _ => True
  | .vaddss _ _ _ => True
  | .vzeroupper => True
  | .movapd x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .movdqa x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .movdqu x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .vmovapd x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .vmovdqa x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .vmovdqu x0 x1 => AvxRegOrMem.Free B x0 ∧ AvxRegOrMem.Free B x1
  | .cmpxchg16b _ x1 => AddrExpr.Free B x1

/-- An instruction names no label of `B`. -/
def Instr.Free (B : List Label) : Instr → Prop
  | .regular _ _ op => Operation.Free B op
  | .avx _ _ op => AvxOperation.Free B op

/-- A directive names no label of `B` (labels and data are free). -/
def Directive.Free (B : List Label) : Directive → Prop
  | .instr i => Instr.Free B i
  | _ => True

section Congr

variable {B : List Label} {L1 L2 : Labels} (hL : ∀ l, l ∉ B → L1.label l = L2.label l)
include hL

theorem constExpr_congr : ∀ (e : ConstExpr), ConstExpr.Free B e →
    ∀ p, @ConstExpr.interp L1 e p = @ConstExpr.interp L2 e p
  | .label l, h, _ => hL l h
  | .int64 _, _, _ => rfl
  | .before_current_instruction, _, _ => rfl
  | .after_current_instruction, _, _ => rfl
  | .add a b, h, p => by
    simp only [ConstExpr.interp, constExpr_congr a h.1 p, constExpr_congr b h.2 p]
  | .sub a b, h, p => by
    simp only [ConstExpr.interp, constExpr_congr a h.1 p, constExpr_congr b h.2 p]

theorem addrExpr_congr [AddressSize] {a : AddrExpr} (h : AddrExpr.Free B a) (s : Reg64s) (p : Std.Rco Int64) :
    @AddrExpr.interp L1 _ a s p = @AddrExpr.interp L2 _ a s p := by
  simp only [AddrExpr.interp, constExpr_congr hL a.disp h p]

theorem regOrMem_congr [AddressSize] {w} {o : RegOrMem w} (h : RegOrMem.Free B o) (s : MachineData)
    (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :
    @RegOrMem.interp w L1 _ o s p ret = @RegOrMem.interp w L2 _ o s p ret := by
  cases o with
  | reg r => rfl
  | mem a => simp only [RegOrMem.interp, addrExpr_congr hL h]

theorem avxRegOrMem_congr [AddressSize] {w} {o : AvxRegOrMem w} (h : AvxRegOrMem.Free B o) (s : MachineData)
    (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) (ca atm : Bool) :
    @AvxRegOrMem.interp w L1 _ o s p ret ca atm = @AvxRegOrMem.interp w L2 _ o s p ret ca atm := by
  cases o with
  | avx r => rfl
  | mem a => simp only [AvxRegOrMem.interp, addrExpr_congr hL h]

theorem operand_congr [AddressSize] {w} {o : Operand w} (h : Operand.Free B o) (s : MachineData)
    (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :
    @Operand.interp w L1 _ o s p ret = @Operand.interp w L2 _ o s p ret := by
  cases o with
  | regOrMem rm => exact regOrMem_congr hL h s p ret
  | imm v => simp only [Operand.interp, constExpr_congr hL v h p]

theorem avxOperand_congr [AddressSize] {w} {o : AvxOperand w} (h : AvxRegOrMem.Free B (match o with | .regOrMem rm => rm))
    (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) (ca : Bool) :
    @AvxOperand.interp w L1 _ o s p ret ca = @AvxOperand.interp w L2 _ o s p ret ca := by
  cases o with
  | regOrMem rm => exact avxRegOrMem_congr hL h s p ret ca false

theorem set_congr [AddressSize] {w} {d : Dst w} (h : RegOrMem.Free B d) (s : MachineData) (v : w.type)
    (p : Std.Rco Int64) (ret : MachineData → Effects) :
    @MachineData.set w L1 _ s d v p ret = @MachineData.set w L2 _ s d v p ret := by
  cases d with
  | reg r => rfl
  | mem a => simp only [MachineData.set, addrExpr_congr hL h]

theorem setAvx_congr [AddressSize] {w} {d : AvxDst w} (h : AvxRegOrMem.Free B d) (s : MachineData) (v : w.type)
    (p : Std.Rco Int64) (ret : MachineData → Effects) (ca atm : Bool) :
    @MachineData.setAvx w L1 _ s d v p ret ca atm = @MachineData.setAvx w L2 _ s d v p ret ca atm := by
  cases d with
  | avx r => rfl
  | mem a => simp only [MachineData.setAvx, addrExpr_congr hL h]

theorem setAvxLegacy_congr [AddressSize] {w} {d : AvxDst w} (h : AvxRegOrMem.Free B d) (s : MachineData)
    (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) (ca atm : Bool) :
    @MachineData.setAvxLegacy w L1 _ s d v p ret ca atm = @MachineData.setAvxLegacy w L2 _ s d v p ret ca atm := by
  cases d with
  | avx r => rfl
  | mem a => simp only [MachineData.setAvxLegacy, addrExpr_congr hL h]

theorem rmw_congr [AddressSize] {w} {o : RegOrMem w} (h : RegOrMem.Free B o) (lock : Bool) (s : MachineData)
    (p : Std.Rco Int64) (op : w.type → Option w.type) (ret : w.type → MachineData → Effects) :
    @RegOrMem.rmw w L1 _ o lock s p op ret = @RegOrMem.rmw w L2 _ o lock s p op ret := by
  cases o with
  | reg r => rfl
  | mem a => simp only [RegOrMem.rmw, addrExpr_congr hL h]

theorem shift_congr {c : ShiftCountExpr} (h : ShiftCountExpr.Free B c) (s : MachineData) (p : Std.Rco Int64) :
    @ShiftCountExpr.interp L1 c s p = @ShiftCountExpr.interp L2 c s p := by
  cases c with
  | cl => rfl
  | imm8 v => simp only [ShiftCountExpr.interp, constExpr_congr hL v h p]

theorem shiftMasked_congr {c : ShiftCountExpr} (h : ShiftCountExpr.Free B c) (s : MachineData)
    (p : Std.Rco Int64) (w : Width) :
    @ShiftCountExpr.interpMasked L1 c s p w = @ShiftCountExpr.interpMasked L2 c s p w := by
  simp only [ShiftCountExpr.interpMasked, shift_congr hL h]

theorem rel_congr [AddressSize] {o : RelRegOrMem} (h : RelRegOrMem.Free B o) (s : MachineData)
    (p : Std.Rco Int64) (ret : BitVec 64 → MachineData → Effects) :
    @RelRegOrMem.interp L1 _ o s p ret = @RelRegOrMem.interp L2 _ o s p ret := by
  cases o with
  | rel c => simp only [RelRegOrMem.interp, constExpr_congr hL c h p]
  | reg r => rfl
  | mem a => simp only [RelRegOrMem.interp, addrExpr_congr hL h]

theorem interpSeg_congr [AddressSize] {w} {o : RegOrMem w} (h : RegOrMem.Free B o) (seg : BitVec 64)
    (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :
    @RegOrMem.interpSeg w L1 _ o seg s p ret = @RegOrMem.interpSeg w L2 _ o seg s p ret := by
  cases o with
  | reg r => rfl
  | mem a => simp only [RegOrMem.interpSeg, AddrExpr.interpSeg, addrExpr_congr hL h]

theorem operandSeg_congr [AddressSize] {w} {o : Operand w} (h : Operand.Free B o) (seg : BitVec 64)
    (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :
    @Operand.interpSeg w L1 _ o seg s p ret = @Operand.interpSeg w L2 _ o seg s p ret := by
  cases o with
  | regOrMem rm => simp only [Operand.interpSeg, interpSeg_congr hL h]
  | imm v => simp only [Operand.interpSeg, constExpr_congr hL v h p]

theorem setSeg_congr [AddressSize] {w} {d : Dst w} (h : RegOrMem.Free B d) (seg : BitVec 64) (s : MachineData)
    (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) :
    @MachineData.setSeg w L1 _ s seg d v p ret = @MachineData.setSeg w L2 _ s seg d v p ret := by
  cases d with
  | reg r => rfl
  | mem a => simp only [MachineData.setSeg, AddrExpr.interpSeg, addrExpr_congr hL h]

/-- **An operation's interpretation under two label tables agreeing off
`B`**, the operation naming no label of `B`. -/
theorem operation_congr [AddressSize] {w} (op : Operation w) (hf : Operation.Free B op) (p : Std.Rco Int64)
    (s : MachineData) (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) :
    @Operation.interp L1 _ w op p s next jmp = @Operation.interp L2 _ w op p s next jmp := by
  cases op <;> simp only [Operation.Free] at hf <;>
    simp (disch := first | assumption | exact hf.1 | exact hf.2 | exact hf.2.1 | exact hf.2.2 | simp_all)
      only [Operation.interp, operand_congr hL, regOrMem_congr hL, set_congr hL, rmw_congr hL,
        shiftMasked_congr hL, rel_congr hL, addrExpr_congr hL, interpSeg_congr hL,
        operandSeg_congr hL, setSeg_congr hL]
  case imul d src1 src2 =>
    obtain ⟨hd, h1, -⟩ := hf
    cases d with
    | none => simp only [set_congr hL h1]
    | some d => simp only [set_congr hL (hd d rfl)]
  case jcc cc l => simp only [hL l hf]
  case xadd lock d src =>
    cases d with
    | reg r => rfl
    | mem a => simp only [rmw_congr hL hf]

/-- A vector operation's interpretation under two such label tables. -/
theorem avxOperation_congr [AddressSize] {w} (op : AvxOperation w) (hf : AvxOperation.Free B op)
    (p : Std.Rco Int64) (s : MachineData) (next : MachineData → Effects) :
    @AvxOperation.interp L1 _ w op p s next = @AvxOperation.interp L2 _ w op p s next := by
  cases op <;> simp only [AvxOperation.Free] at hf <;>
    simp (disch := first | assumption | exact hf.1 | exact hf.2 | simp_all)
      only [AvxOperation.interp, addrExpr_congr hL, avxRegOrMem_congr hL, setAvx_congr hL, setAvxLegacy_congr hL]

theorem instr_congr {i : Instr} (hf : Instr.Free B i) (s : MachineData) (p : Std.Rco Int64)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) :
    @Instr.interp L1 i s p next jmp = @Instr.interp L2 i s p next jmp := by
  cases i with
  | regular a w op => simp only [Instr.interp, @operation_congr _ _ _ hL ⟨a⟩ w op hf]
  | avx a w op => simp only [Instr.interp, @avxOperation_congr _ _ _ hL ⟨a⟩ w op hf]

theorem directive_congr {d : Directive} (hf : Directive.Free B d) (s : MachineData) (p : Std.Rco Int64)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) :
    @Directive.interp L1 d s p next jmp = @Directive.interp L2 d s p next jmp := by
  cases d with
  | instr i => simp only [Directive.interp, instr_congr hL hf]
  | label _ => rfl
  | byteArray _ => rfl

/-- **The interpretation of a run of directives under two label tables**
agreeing off `B`, none of the directives naming a label of `B`. -/
theorem directives_congr : ∀ (ds : List (Directive × Nat)), (∀ d ∈ ds, Directive.Free B d.1) →
    ∀ (s : MachineData) (pc : Int64) (ret : Int64 → MachineData → Effects),
    @Directives.interp L1 ds s pc ret = @Directives.interp L2 ds s pc ret
  | [], _, _, _, _ => rfl
  | (d, sz) :: ds, hf, s, pc, ret => by
    simp only [Directives.interp]
    rw [directive_congr hL (hf _ List.mem_cons_self)]
    congr 1; funext s'
    exact directives_congr ds (fun d hd => hf d (List.mem_cons_of_mem _ hd)) s' _ ret

end Congr

/-! ### Decidability

Each `Free` is decidable, so a concrete text's `Directive.Free` follows by
`decide`. -/

section Dec

variable (B : List Label)

instance ConstExpr.decFree : ∀ e : ConstExpr, Decidable (ConstExpr.Free B e)
  | .label l => inferInstanceAs (Decidable (l ∉ B))
  | .int64 _ | .before_current_instruction | .after_current_instruction => isTrue trivial
  | .add a b | .sub a b =>
    have := ConstExpr.decFree a; have := ConstExpr.decFree b
    inferInstanceAs (Decidable (ConstExpr.Free B a ∧ ConstExpr.Free B b))

instance AddrExpr.decFree (a : AddrExpr) : Decidable (AddrExpr.Free B a) := by
  unfold AddrExpr.Free; infer_instance

instance RegOrMem.decFree {w} (x : RegOrMem w) : Decidable (RegOrMem.Free B x) := by
  unfold RegOrMem.Free; split <;> infer_instance

instance AvxRegOrMem.decFree {w} (x : AvxRegOrMem w) : Decidable (AvxRegOrMem.Free B x) := by
  unfold AvxRegOrMem.Free; split <;> infer_instance

instance Operand.decFree {w} (x : Operand w) : Decidable (Operand.Free B x) := by
  unfold Operand.Free; split <;> infer_instance

instance ShiftCountExpr.decFree (x : ShiftCountExpr) : Decidable (ShiftCountExpr.Free B x) := by
  unfold ShiftCountExpr.Free; split <;> infer_instance

instance RelRegOrMem.decFree (x : RelRegOrMem) : Decidable (RelRegOrMem.Free B x) := by
  unfold RelRegOrMem.Free; split <;> infer_instance

instance Operation.decFree {w} (op : Operation w) : Decidable (Operation.Free B op) := by
  unfold Operation.Free; split <;> infer_instance

instance AvxOperation.decFree {w} (op : AvxOperation w) : Decidable (AvxOperation.Free B op) := by
  unfold AvxOperation.Free; split <;> infer_instance

instance Instr.decFree (i : Instr) : Decidable (Instr.Free B i) := by
  unfold Instr.Free; split <;> infer_instance

instance Directive.decFree (d : Directive) : Decidable (Directive.Free B d) := by
  unfold Directive.Free; split <;> infer_instance

end Dec

-- `Free` decides: a label off `B` is free, one in `B` is not.
#guard decide (ConstExpr.Free ["scc_text_end"] (.sub (.label "f") .after_current_instruction))
#guard !decide (ConstExpr.Free ["scc_text_end"] (.sub (.label "scc_text_end") .after_current_instruction))

end Spike.Lib.X64LabelCongr

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64LabelCongr.operation_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64LabelCongr.operation_congr

/-- info: 'Spike.Lib.X64LabelCongr.directives_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64LabelCongr.directives_congr
