/-
AArch64 counterpart of the control-flow and call rules of x64's
`Kraken/MachineWP.lean` (`jmp_label_spec`, `jcc_spec`, `jmp_reg_spec`,
`ret_spec`, `call_spec`, `fun_spec_from_label`, `call_proc_spec(_at)`,
`call_proc_specK(_at)`, `call_simp`), written for AArch64's branches:
`B`, `B.cond`, `CBZ`/`CBNZ`, `TBZ`/`TBNZ`, `BR`, and the calls `BL`/`BLR`
and `RET` through the link register `X30` (`MachineData.setLr`/`lr` in
`Kraken.AArch64.WP.Step`).

A branch to a label exits at the label's address: the parser writes the
target as `.label l`, which `ConstExpr.evalBranchTarget` reads as the label's
address, so unlike x64's `rel (label - after)` no cancellation is needed. A
conditional branch has the tail's wp on the fall-through side and the exit on
the taken side, as x64's `jcc_spec`. A branch through a register exits at the
register's value. A call writes `X30` and no memory, so the call rules carry
no side condition on the stack, unlike x64's.
-/
import Kraken.AArch64.WP.MachineWP

open Kraken
open Std.WP
open Lean.Order

/-- A 64-bit register read as a jump target (`BR`, `BLR`, `RET`): the
interpreter converts through `Int`, which is the identity on the bits. -/
@[simp, grind =] theorem Int64.ofInt_signed (x : BitVec 64) :
    Int64.ofInt x.signed = Int64.ofBitVec x := by
  apply Int64.toBitVec_inj.mp
  simp [BitVec.signed_eq]

/-- The address a 64-bit register holds, read back from its bits. -/
@[simp, grind =] theorem Int64.ofBitVec_toBitVec_toUInt64 (a : Int64) :
    Int64.ofBitVec a.toUInt64.toBitVec = a :=
  Int64.ofBitVec_toBitVec a

/- A return address goes into `X30` as the bits of an `Int64` and comes back
out of it as the `Int64` of those bits: `grind` reads the round trip. -/
@[grind =] theorem Int64.ofBitVec_toBitVec_eq (a : Int64) : Int64.ofBitVec a.toBitVec = a :=
  Int64.ofBitVec_toBitVec a

/-- The bit `TBZ`/`TBNZ #0` tests is the parity of the value. -/
@[grind =] theorem BitVec.getLsbD_zero_eq_mod {n : Nat} (x : BitVec n) :
    x.getLsbD 0 = decide (x.toNat % 2 = 1) := by
  simp [BitVec.getLsbD, Nat.testBit_zero]

section Specs

open MachineWP

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, ConstExpr.evalBranchTarget, ConstExpr.interp,
      MachineData.setRegOrZr, Effects.All, or_false, false_or])

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

/-- The rule of a two-way branch: the interpretation is the jump to `tgt` when
`c` holds and the fall-through otherwise. -/
private theorem branch_spec {i : Instr} {c : MachineData → Prop} [∀ s, Decidable (c s)]
    (tgt : Int64)
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (next : MachineData → Effects)
        (jmp : Int64 → MachineData → Effects),
      @Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng next jmp
        = require_exec_access rng (fun _ => if c s then jmp tgt s else next s)) :
    ⦃ fun s => (c s → E tgt s) ⊓ (¬ c s → WP.wp p Q E s) ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg ?_
    unfold Executable.stepAt
    simp only [hcell]
    by_cases hc : c s
    · simp only [hc, ite_true, Effects.All]
      exact Or.inr (Eventually.done _ (Or.inr (h.1 hc)))
    · simp only [hc, ite_false, Effects.All]
      exact Or.inl (h.2 hc _ hpl')

/-- `B l` : the jump to the label. -/
@[spec] theorem MachineWP.b_spec (l : Label) :
    ⦃ fun s => E ((_root_.Executable.labels cenv).label l) s ⦄
      (Directive.instr ⟨.W64, .B (.label l)⟩ :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, -⟩ := hpl
    refine step_here hseg (Or.inr ?_)
    wp_step
    exact Eventually.done _ (Or.inr h)

/-- `B.cond l` : the jump when the condition holds of the flags. -/
@[spec] theorem MachineWP.b_cond_spec (cc : CondCode) (l : Label) :
    ⦃ fun s =>
        (cc.interp s.status = true → E ((_root_.Executable.labels cenv).label l) s)
          ⊓ (cc.interp s.status = false → WP.wp p Q E s) ⦄
      (Directive.instr ⟨.W64, .B_cond cc (.label l)⟩ :: p)
    ⦃ Q; E ⦄ := by
  have h := branch_spec (p := p) (Q := Q) (E := E)
    (i := ⟨.W64, .B_cond cc (.label l)⟩) (c := fun s => cc.interp s.status = true)
    ((_root_.Executable.labels cenv).label l) (fun s rng next jmp => by
      simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
        ConstExpr.interp])
  simpa only [Bool.not_eq_true] using h

/-- `CBZ Rt, l` : the jump when the register is zero. -/
@[spec] theorem MachineWP.cbz_spec {w : RegWidth} (r : RegOrZr w) (l : Label) :
    ⦃ fun s =>
        (s.regs.getRegOrZr r = 0 → E ((_root_.Executable.labels cenv).label l) s)
          ⊓ (s.regs.getRegOrZr r ≠ 0 → WP.wp p Q E s) ⦄
      (Directive.instr ⟨w, .CBZ r (.label l)⟩ :: p)
    ⦃ Q; E ⦄ :=
  branch_spec (c := fun s => s.regs.getRegOrZr r = 0)
    ((_root_.Executable.labels cenv).label l) (fun s rng next jmp => by
      simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
        ConstExpr.interp, beq_iff_eq])

/-- `CBNZ Rt, l` : the jump when the register is not zero. -/
@[spec] theorem MachineWP.cbnz_spec {w : RegWidth} (r : RegOrZr w) (l : Label) :
    ⦃ fun s =>
        (s.regs.getRegOrZr r ≠ 0 → E ((_root_.Executable.labels cenv).label l) s)
          ⊓ (s.regs.getRegOrZr r = 0 → WP.wp p Q E s) ⦄
      (Directive.instr ⟨w, .CBNZ r (.label l)⟩ :: p)
    ⦃ Q; E ⦄ := by
  have h := branch_spec (p := p) (Q := Q) (E := E)
    (i := ⟨w, .CBNZ r (.label l)⟩) (c := fun s => s.regs.getRegOrZr r ≠ 0)
    ((_root_.Executable.labels cenv).label l) (fun s rng next jmp => by
      simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
        ConstExpr.interp, bne_iff_ne])
  simpa only [ne_eq, Decidable.not_not] using h

/-- `TBZ Rt, #bit, l` : the jump when the bit is clear. -/
@[spec] theorem MachineWP.tbz_spec {w : RegWidth} (r : RegOrZr w) (bit : Nat) (l : Label) :
    ⦃ fun s =>
        ((s.regs.getRegOrZr r).getLsbD bit = false → E ((_root_.Executable.labels cenv).label l) s)
          ⊓ ((s.regs.getRegOrZr r).getLsbD bit = true → WP.wp p Q E s) ⦄
      (Directive.instr ⟨w, .TBZ r bit (.label l)⟩ :: p)
    ⦃ Q; E ⦄ := by
  have h := branch_spec (p := p) (Q := Q) (E := E)
    (i := ⟨w, .TBZ r bit (.label l)⟩) (c := fun s => (s.regs.getRegOrZr r).getLsbD bit = false)
    ((_root_.Executable.labels cenv).label l) (fun s rng next jmp => by
      simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
        ConstExpr.interp, beq_iff_eq])
  simpa only [Bool.not_eq_false] using h

/-- `TBNZ Rt, #bit, l` : the jump when the bit is set. -/
@[spec] theorem MachineWP.tbnz_spec {w : RegWidth} (r : RegOrZr w) (bit : Nat) (l : Label) :
    ⦃ fun s =>
        ((s.regs.getRegOrZr r).getLsbD bit = true → E ((_root_.Executable.labels cenv).label l) s)
          ⊓ ((s.regs.getRegOrZr r).getLsbD bit = false → WP.wp p Q E s) ⦄
      (Directive.instr ⟨w, .TBNZ r bit (.label l)⟩ :: p)
    ⦃ Q; E ⦄ := by
  have h := branch_spec (p := p) (Q := Q) (E := E)
    (i := ⟨w, .TBNZ r bit (.label l)⟩) (c := fun s => (s.regs.getRegOrZr r).getLsbD bit = true)
    ((_root_.Executable.labels cenv).label l) (fun s rng next jmp => by
      simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
        ConstExpr.interp, beq_iff_eq])
  simpa only [Bool.not_eq_true] using h

/-! ### Computed jumps

A jump through a register exits at the register's value: the exit channel is
pc-valued, so a computed target needs no new machinery. Where control lands is
the table's business (`Table.ofLabels` asks that the value be some label's
address). -/

/-- `BR Xn` : a computed jump, to the address the register holds. -/
@[spec] theorem MachineWP.br_spec (r : RegOrZr .W64) :
    ⦃ fun s => E (Int64.ofBitVec (s.regs.getRegOrZr r)) s ⦄
      (Directive.instr ⟨.W64, .BR r⟩ :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, -⟩ := hpl
    refine step_here hseg (Or.inr ?_)
    wp_step
    simp only [Int64.ofInt_signed]
    exact Eventually.done _ (Or.inr h)

/-- `RET Xn` (`RET` is `RET X30`) : the return, to the address the register
holds. Under the convention of `ProcSpec` the entry state has `t.lr = ra`, and
`MachineData.lr_eq` reads that as `X30`. -/
@[spec] theorem MachineWP.ret_spec (r : RegOrZr .W64) :
    ⦃ fun s => E (Int64.ofBitVec (s.regs.getRegOrZr r)) s ⦄
      (Directive.instr ⟨.W64, .RET r⟩ :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, -⟩ := hpl
    refine step_here hseg (Or.inr ?_)
    wp_step
    simp only [Int64.ofInt_signed]
    exact Eventually.done _ (Or.inr h)

/-! ### Calls

`BL l` writes the address behind it to `X30` and jumps to `l`; `BLR Xn` does
the same with the target read from `Xn` first. The rules take the callee's
run as a premise: its text and triple (`call_spec`, `fun_spec_from_label`) or
its specification (`call_proc_spec`, `call_proc_specK`, `blr_proc_spec`). The
address behind the call depends on where it sits, so the caller's
precondition holds for every `ra` the machine may write. -/

/-- The cell of `BL l`: `X30` gets the address behind it, and control goes to
the label. -/
private theorem bl_cell (l : Label) (s : MachineData) (pc : Int64) (z : Nat)
    (post : @Post MachineState) :
    (@Directive.interp (_root_.Executable.labels cenv)
        (Directive.instr ⟨.W64, .BL (.label l)⟩) s (.mk pc (pc + .ofNat z))
        (fun _ => .unimplemented "fallthrough") (fun pc' s' => .done (s', pc'))).All post
      = post (s.setLr (pc + .ofNat z), (_root_.Executable.labels cenv).label l) := by
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp, MachineData.setRegOrZr, Effects.All, BitVec.ofInt_toInt_int64]
  rfl

/-- One call, with the callee's run as its premise. `P ra` is the callee's
assertion at its entry, for a run that returns to `ra`. The conclusion rolls
`P` back over the write of `X30`, quantified over the address the machine
writes, and the callee's exit at that address continues the caller's wp of the
cells behind the call. An exit anywhere else is the caller's own. -/
theorem MachineWP.call_spec {P : Int64 → MachineData → Prop} (l : Label)
    (body : Program) (hplace : cenv.sits ((_root_.Executable.labels cenv).label l) body)
    (hbody : ∀ ra : Int64,
      ⦃ P ra ⦄
        body
      ⦃ (fun _ _ => False);
        fun a s' => if a = ra then WP.wp p Q E s' else E a s' ⦄) :
    ⦃ fun s => ∀ ra : Int64, P ra (s.setLr ra) ⦄
      (Directive.instr ⟨.W64, .BL (.label l)⟩ :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hP => ?_
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  rw [bl_cell]
  have hrun := (hbody (pc + Int64.ofNat z)).le_wp (s.setLr (pc + Int64.ofNat z))
    (hP (pc + Int64.ofNat z))
  rw [MachineWP.wp_eq] at hrun
  refine eventually_trans _ _ _ _ (hrun ((_root_.Executable.labels cenv).label l) hplace) ?_
  rintro ⟨s', a⟩ (⟨-, hbot⟩ | hexit)
  · exact hbot.elim
  · dsimp only at hexit
    by_cases ha : a = pc + Int64.ofNat z
    · rw [if_pos ha] at hexit
      rw [after_instr hseg]
      subst ha
      exact hexit _ hpl'
    · rw [if_neg ha] at hexit
      exact Eventually.done _ (Or.inr hexit)

/-- The spec of a procedure at a label, in the form `vcgen` steps a call with.
`Pre` is what the procedure needs of the caller's state and `Post` relates that
state to the one the caller resumes in, so neither mentions the return address.
The tail and the channels stay open: one `have` per procedure serves every call
site. -/
theorem MachineWP.fun_spec_from_label {Pre : MachineData → Prop}
    {Post : MachineData → MachineData → Prop} {l : Label} {body : Program}
    (hplace : cenv.sits ((_root_.Executable.labels cenv).label l) body)
    (hbody : ∀ (ra : Int64) (s : MachineData),
      ⦃ fun t => t = s.setLr ra ∧ Pre s ⦄
        body
      ⦃ (fun _ _ => False); fun a s' => a = ra ∧ Post s s' ⦄) :
    ∀ ⦃p : Program⦄ ⦃Q : Unit → MachineData → Prop⦄ ⦃E : Int64 → MachineData → Prop⦄,
      ⦃ fun s => (Pre s) ⊓ (∀ s' : MachineData, Post s s' → WP.wp p Q E s') ⦄
        (Directive.instr ⟨.W64, .BL (.label l)⟩ :: p)
      ⦃ Q; E ⦄ := by
  intro p Q E
  refine Triple.intro fun s h => ?_
  simp only [meet_prop_eq_and] at h
  obtain ⟨hpre, hcont⟩ := h
  refine (MachineWP.call_spec
    (P := fun ra t => ∃ s₀ : MachineData, t = s₀.setLr ra ∧ Pre s₀
      ∧ ∀ s' : MachineData, Post s₀ s' → WP.wp p Q E s')
    l body hplace ?_).le_wp s (fun ra => ⟨s, rfl, hpre, hcont⟩)
  intro ra
  refine Triple.intro fun t ht => ?_
  obtain ⟨s₀, rfl, hpre₀, hcont₀⟩ := ht
  rw [MachineWP.wp_eq]
  have hrun := (hbody ra s₀).le_wp (s₀.setLr ra) ⟨rfl, hpre₀⟩
  rw [MachineWP.wp_eq] at hrun
  refine Executable.wp_mono (fun _ hq => hq) ?_ hrun
  rintro a s' ⟨rfl, hpost⟩
  rw [if_pos rfl]
  exact hcont₀ s' hpost

/-- Stepping a `BL` through the callee's spec: the caller fixes the logical
variable `x`, and for whatever address the machine writes to `X30`, the
callee's precondition holds of the state after the write and its
postcondition continues the caller's tail. -/
theorem MachineWP.call_proc_spec {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (x : α)
    (l : Label) (hproc : cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post) :
    ⦃ fun s =>
        ∀ ra : Int64, Pre x ra (s.setLr ra)
          ∧ ∀ s' : MachineData, Post x ra (s.setLr ra) s' → WP.wp p Q E s' ⦄
      (Directive.instr ⟨.W64, .BL (.label l)⟩ :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hP => ?_
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  rw [bl_cell]
  refine eventually_trans _ _ _ _
    (hproc x (pc + Int64.ofNat z) (s.setLr (pc + Int64.ofNat z)) (hP _).1) ?_
  rintro ⟨s', a⟩ ⟨rfl, hpost⟩
  rw [after_instr hseg]
  exact (hP _).2 s' hpost _ hpl'

/-- `call_proc_spec` with the tail and the channels open, in the form
`vcgen [hc]` steps a call with: `have hc := call_proc_spec_at x l hproc` at
the call site, `x` the callee's logical variable for this call. -/
theorem MachineWP.call_proc_spec_at {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (x : α) (l : Label)
    (hproc : cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post) :
    ∀ ⦃p : Program⦄ ⦃Q : Unit → MachineData → Prop⦄ ⦃E : Int64 → MachineData → Prop⦄,
      ⦃ fun s =>
          ∀ ra : Int64, Pre x ra (s.setLr ra)
            ∧ ∀ s' : MachineData, Post x ra (s.setLr ra) s' → WP.wp p Q E s' ⦄
        (Directive.instr ⟨.W64, .BL (.label l)⟩ :: p)
      ⦃ Q; E ⦄ :=
  fun _ _ _ => MachineWP.call_proc_spec x l hproc

/-- `call_proc_spec` for the continuation form: the callee's `Spec` is asked
with the caller's tail as the continuation. -/
theorem MachineWP.call_proc_specK {Spec : Int64 → (MachineData → Prop) → MachineData → Prop}
    (l : Label) (hproc : cenv.ProcSpecK ((_root_.Executable.labels cenv).label l) Spec) :
    ⦃ fun s => ∀ ra : Int64, Spec ra (WP.wp p Q E) (s.setLr ra) ⦄
      (Directive.instr ⟨.W64, .BL (.label l)⟩ :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hP => ?_
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  rw [bl_cell]
  refine eventually_trans _ _ _ _
    (hproc (pc + Int64.ofNat z) _ (s.setLr (pc + Int64.ofNat z)) (hP _)) ?_
  rintro ⟨s', a⟩ ⟨rfl, hpost⟩
  rw [after_instr hseg]
  exact hpost _ hpl'

/-- `call_proc_specK` with the tail and the channels open, for `vcgen [hc]`
with `have hc := call_proc_specK_at l hproc` at the call site. -/
theorem MachineWP.call_proc_specK_at {Spec : Int64 → (MachineData → Prop) → MachineData → Prop}
    (l : Label) (hproc : cenv.ProcSpecK ((_root_.Executable.labels cenv).label l) Spec) :
    ∀ ⦃p : Program⦄ ⦃Q : Unit → MachineData → Prop⦄ ⦃E : Int64 → MachineData → Prop⦄,
      ⦃ fun s => ∀ ra : Int64, Spec ra (WP.wp p Q E) (s.setLr ra) ⦄
        (Directive.instr ⟨.W64, .BL (.label l)⟩ :: p)
      ⦃ Q; E ⦄ :=
  fun _ _ _ => MachineWP.call_proc_specK l hproc

/-- `BLR Xn` through the callee's spec at the address `f` the register holds:
`X30` gets the address behind the call, and the target is read before the
write (so `BLR X30` calls the old `X30`). -/
theorem MachineWP.blr_proc_spec {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (x : α) (r : RegOrZr .W64)
    (f : Int64) (hproc : cenv.ProcSpec f Pre Post) :
    ⦃ fun s => Int64.ofBitVec (s.regs.getRegOrZr r) = f
        ∧ ∀ ra : Int64, Pre x ra (s.setLr ra)
          ∧ ∀ s' : MachineData, Post x ra (s.setLr ra) s' → WP.wp p Q E s' ⦄
      (Directive.instr ⟨.W64, .BLR r⟩ :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s ⟨hf, hP⟩ => ?_
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setRegOrZr,
    Effects.All, BitVec.ofInt_toInt_int64, Int64.ofInt_signed, hf]
  refine eventually_trans _ _ _ _
    (hproc x (pc + Int64.ofNat z) (s.setLr (pc + Int64.ofNat z)) (hP _).1) ?_
  rintro ⟨s', a⟩ ⟨rfl, hpost⟩
  rw [after_instr hseg]
  exact (hP _).2 s' hpost _ hpl'

/-- The state `vcgen` leaves at a call site is `s.setLr ra`. `grind` reads a
register out of it through `regs_setLr` and the per-field `setXReg` lemmas;
this does the same by `simp`, in every hypothesis and the goal, for the
`refine` that opens a call rule's `∀ ra` (see x64's `call_simp`). -/
macro "call_simp" : tactic =>
  `(tactic| try simp only [MachineData.regs_setLr, MachineData.dmem_setLr,
      MachineData.status_setLr, MachineData.lr_setLr, Reg64s.getXReg_setXReg,
      reduceCtorEq, ite_true, ite_false] at *)

end Specs
