/-
Copied from x64's `Kraken/MachineWP.lean` at commit `9953817`, adapted for AArch64:
the core only (`wp`, `sits`, `after`, `wp_cons`, the `WP` instance), the
shared rule helpers, `TripleAt`, and the first rules of the dictionary. The
structure (`cfg`, procedures, linking, the read-back) comes with W2, W3 and W5.

The machine-founded weakest precondition. `Executable.wp` is defined by the
baseline interpreter: a fragment `q`, placed anywhere in the ambient code,
runs its cells and every stop lands in the fall-through postcondition at the
placement's end, or in the exit channel at the pc it stopped at. Exits are
pc values: `E : Int64 → MachineData → Prop`. A label exit is
`E ((_root_.Executable.labels cenv).label l)`; a computed exit is `E` at the value.

The step relation `instrStep`, the ambient code `CodeEnv` and the procedure
specifications `ProcSpec`/`ProcSpecK` are in `Kraken.Step`: a caller or a
linker needs those and not this file.
-/
import Kraken.AArch64.WP.Step

open Kraken
open Std.WP
open Lean.Order

/-! ## The wp -/

/-- The fragment `q` sits at `pc`: a label costs no address, and every other
cell is the next instruction there. -/
def Kraken.Executable.sits (e : Kraken.Executable Directive) (pc : Int64) : Program → Prop
  | [] => True
  | .label _ :: q => e.sits pc q
  | d :: q => ∃ z rest, e.codeAt pc = (d, z) :: rest ∧ e.sits (pc + .ofNat z) q

/-- The address behind the fragment `q` placed at `pc`. -/
def Kraken.Executable.after (e : Kraken.Executable Directive) (pc : Int64) : Program → Int64
  | [] => pc
  | .label _ :: q => e.after pc q
  | _ :: q =>
    match e.codeAt pc with
    | [] => pc
    | (_, z) :: _ => e.after (pc + .ofNat z) q

/-- The run of the fragment `q` from `s`: placed anywhere in the ambient
code, the machine eventually falls through to the placement's end with `Q`,
or stops at a pc satisfying `E`. Re-entry inside the fragment is free: the
judgment is the fixpoint `Eventually`, so a back edge simply keeps stepping. -/
def Kraken.Executable.wp (e : Kraken.Executable Directive) (q : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ (pc : Int64), e.sits pc q →
    Eventually (e.instrStep)
      (fun st => (st.2 = e.after pc q ∧ Q st.1) ∨ E st.2 st.1) (s, pc)

theorem Kraken.Executable.wp_mono {e : Kraken.Executable Directive} {q : Program}
    {Q₁ Q₂ : MachineData → Prop} {E₁ E₂ : Int64 → MachineData → Prop}
    (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : e.wp q Q₁ E₁ s) : e.wp q Q₂ E₂ s := fun pc hpl =>
  eventually_weaken _ _ _ _
    (fun _ hst => hst.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ hq⟩) (hE _ _)) (h pc hpl)

/-- The run of `d :: q` is the run of `d` with the run of `q` as its
post: the machine falls through `d` to the address where `q` sits. -/
theorem Kraken.Executable.wp_cons {e : Kraken.Executable Directive} {d : Directive} {q : Program}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : e.wp [d] (fun s' => e.wp q Q E s') E s) : e.wp (d :: q) Q E s := by
  intro pc hpl
  have hcont : ∀ pc', e.sits pc' q → ∀ st : MachineState,
      (st.2 = pc' ∧ e.wp q Q E st.1) ∨ E st.2 st.1 →
      Eventually e.instrStep (fun st => (st.2 = e.after pc' q ∧ Q st.1) ∨ E st.2 st.1) st := by
    intro pc' hq ⟨sd, spc⟩ hst
    rcases hst with ⟨hpc, hwp⟩ | hE
    · dsimp only at hpc hwp
      subst hpc
      exact hwp _ hq
    · exact .done _ (Or.inr hE)
  cases d with
  | label l =>
    have h1 := h pc trivial
    exact eventually_trans _ _ _ _ h1 (hcont pc hpl)
  | instr i =>
    obtain ⟨z, rest, hcode, hq⟩ := hpl
    have h1 := h pc ⟨z, rest, hcode, trivial⟩
    simp only [Executable.after, hcode] at h1 ⊢
    exact eventually_trans _ _ _ _ h1 (hcont _ hq)
  | byteArray a =>
    obtain ⟨z, rest, hcode, hq⟩ := hpl
    have h1 := h pc ⟨z, rest, hcode, trivial⟩
    simp only [Executable.after, hcode] at h1 ⊢
    exact eventually_trans _ _ _ _ h1 (hcont _ hq)

namespace MachineWP

/-- A triple on a program is the machine-founded wp of the ambient code. -/
scoped instance instWP [CodeEnv] :
    WP Program Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  wpTrans q := ⟨fun Q E s => cenv.wp q (Q ()) E s⟩
  wp_trans_monotone _ _ _ _ _ hE hQ := fun _ h =>
    Executable.wp_mono (fun s' => hQ () s') hE h

/-- Unfold a triple's wp into the machine-founded transformer. -/
theorem wp_eq [CodeEnv] (q : Program) (Q : Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) :
    WP.wp q Q E s = cenv.wp q (Q ()) E s := rfl

/- An immediate in a machine-founded VC is the payload of an `Int64` literal.
With `MachineWP` open, `grind`'s normalizer rewrites it to a `BitVec` literal,
so no `Int64` literal enters the E-graph: one there, among register reads, has
been seen to exhaust `grind`'s recursion depth. The rules are scoped because
the separation-logic proofs (`SepAluMem`, `SepDynamicStack`) need immediates
in their `Int64` form. -/
attribute [scoped grind norm] Int64.toBitVec_ofNat_norm Int64.toBitVec_neg_ofNat_norm

/- A jump exit of `MachineWP.cfg` asks where its target sits in the list of
labels of the program, `["start", ".loop", …]`. With `MachineWP` open,
`grind`'s normalizer answers by evaluation. -/
attribute [scoped grind norm] List.idxOf_cons List.contains_cons

end MachineWP

/-! ## The rule set

One `@[spec]` triple per instruction shape, in composite form: the
precondition is the tail's wp at the record update the instruction performs,
a jump's precondition is `E` at the target's address. Proofs unfold one cell
of the interpreter and advance the placement.

The dictionary is demand-driven: this file has the
structural rules and the four register rules of `Examples/WPBasic.lean`. -/

/-- `LSL #0` of a register is the register: the shifted operand of `MOV`
(`ORR Xd, XZR, Xm`). -/
@[simp, grind =] theorem ShiftRegExpr.interp_lsl_zero {w : RegWidth} (r : RegOrZr w) (s : Reg64s)
    (p : Std.Rco Int64) :
    ShiftRegExpr.interp ⟨r, 0, .LSL⟩ s p = s.getRegOrZr r := by
  simp [ShiftRegExpr.interp]

section Specs

open MachineWP

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, ExtOrImmReg.interp, ConstExpr.interp,
      MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.All, or_false, false_or])

/-- Unfold the fall-through address past one instruction cell. -/
private theorem after_instr {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

/-- Run one cell and continue: the rule pattern shared by every
instruction. -/
private theorem step_here {post : @Post MachineState} {s : MachineData} {pc : Int64}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hseg : cenv.codeAt pc = (d, z) :: rest)
    (hall : cenv.stepAt d z (s, pc) (fun st => Eventually cenv.instrStep post st)) :
    Eventually cenv.instrStep post (s, pc) :=
  step_cps _ _ _ ⟨d, z, rest, hseg, hall⟩

/-- The rule of a cell that runs and falls through: its interpretation stops
at the state the cell computes, so the tail's wp there is the cell's
precondition. Each entry of the dictionary below is this rule at one
instruction, with the reduction of its interpretation as the only content. -/
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

/-- The rule of a cell whose fall-through leaves a value unspecified: the
tail's wp must hold whatever the machine picks. (Unused here; the
store-exclusive rules of `WP.RulesAtomic` need it.) -/
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

@[spec] theorem MachineWP.nil_spec :
    ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc _
    exact Eventually.done _ (Or.inl ⟨rfl, h⟩)

/-- A label costs no step and no address. -/
@[spec] theorem MachineWP.label_spec (l : Label) :
    ⦃ fun s => WP.wp p Q E s ⦄ (Directive.label l :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => h

@[spec] theorem MachineWP.nop_spec (w : RegWidth) :
    ⦃ fun s => WP.wp p Q E s ⦄ (Directive.instr ⟨w, .NOP⟩ :: p) ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- A data cell does not run: the machine faults on reaching it. Its rule asks
that control never get there, which a table entry of `False` provides. -/
@[spec] theorem MachineWP.byteArray_spec (a : ByteArray) :
    ⦃ fun _ => False ⦄ (Directive.byteArray a :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => False.elim h

/-- `MOVZ Xd, #i, LSL #k` : the low 16 bits of the immediate, shifted. -/
@[spec] theorem MachineWP.movz_spec (dst : RegOrZr .W64) (i : Int64) (sh : MovShift .W64) :
    ⦃ fun s =>
        let v := (BitVec.ofInt 64 i.toInt &&& 0xFFFF#64) <<< sh.toNat
        WP.wp p Q E { s with regs := s.regs.setRegOrZr dst v } ⦄
      (Directive.instr ⟨.W64, .MOVZ dst (.int64 i) sh⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `MOV Xd, Xm` (the alias `ORR Xd, XZR, Xm`) : the register copied. -/
@[spec] theorem MachineWP.mov_reg_spec (dst src : RegOrZr .W64) :
    ⦃ fun s => WP.wp p Q E { s with regs := s.regs.setRegOrZr dst (s.regs.getRegOrZr src) } ⦄
      (Directive.instr ⟨.W64, .ORR_s dst (.low .XZR .W64) ⟨src, 0, .LSL⟩⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    wp_step
    simp only [ShiftRegExpr.interp_lsl_zero, Reg64s.getRegOrZr_XZR]
    simpa using hP)

/-- `ADD Xd|SP, Xn|SP, #i` : the register plus the immediate; no flags. -/
@[spec] theorem MachineWP.add_imm_spec (dst src : RegOrSp .W64) (i : Int64) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrSp dst (s.regs.getRegOrSp src + BitVec.ofInt 64 i.toInt) } ⦄
      (Directive.instr ⟨.W64, .ADD_e dst src (.imm ⟨.int64 i, .S0⟩)⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `SUB Xd|SP, Xn|SP, #i` : the register minus the immediate; no flags. -/
@[spec] theorem MachineWP.sub_imm_spec (dst src : RegOrSp .W64) (i : Int64) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.setRegOrSp dst (s.regs.getRegOrSp src - BitVec.ofInt 64 i.toInt) } ⦄
      (Directive.instr ⟨.W64, .SUB_e dst src (.imm ⟨.int64 i, .S0⟩)⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

end Specs

/-! ## Triples at an address

`Executable.wp` quantifies over every placement of a fragment, which is what
lets one triple serve wherever the fragment sits, and what rules out reading
the pc: `ADR`/`ADRP` and `BL` yield addresses relative to the instruction,
which no position-independent precondition can name. `TripleAt pc` is the
judgment at one address. Every triple gives one at each address
(`TripleAt.of_triple`); the pc-reading rules (`ADR`/`ADRP` in `WP.Rules`, x64's
`lea_rip_disp_at`) are stated in this form. -/

namespace MachineWP

/-- The run of `q` placed at `pc`, from a state with `P`: it falls through to
the end of the placement with `Q`, or stops at a pc satisfying `E`. -/
def TripleAt [CodeEnv] (pc : Int64) (P : MachineData → Prop) (q : Program)
    (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop) : Prop :=
  ∀ s, P s → cenv.sits pc q →
    Eventually cenv.instrStep (fun st => (st.2 = cenv.after pc q ∧ Q () st.1) ∨ E st.2 st.1) (s, pc)

theorem TripleAt.of_triple [CodeEnv] {pc : Int64} {P : MachineData → Prop} {q : Program}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
    (h : ⦃ P ⦄ q ⦃ Q; E ⦄) : TripleAt pc P q Q E :=
  fun s hp hs => h.le_wp s hp pc hs

theorem TripleAt.mono [CodeEnv] {pc : Int64} {P : MachineData → Prop} {q : Program}
    {Q₁ Q₂ : Unit → MachineData → Prop} {E₁ E₂ : Int64 → MachineData → Prop}
    (hQ : ∀ s, Q₁ () s → Q₂ () s) (hE : ∀ a s, E₁ a s → E₂ a s)
    (h : TripleAt pc P q Q₁ E₁) : TripleAt pc P q Q₂ E₂ :=
  fun s hp hs => eventually_weaken _ _ _ _
    (fun _ hst => hst.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ hq⟩) (hE _ _)) (h s hp hs)

theorem TripleAt.pre [CodeEnv] {pc : Int64} {P P' : MachineData → Prop} {q : Program}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
    (hP : ∀ s, P s → P' s) (h : TripleAt pc P' q Q E) : TripleAt pc P q Q E :=
  fun s hp hs => h s (hP s hp) hs

end MachineWP

-- Smoke test: the walk steps a placed fragment through the registered specs.
set_option mvcgen.warning false in
open MachineWP in
example [CodeEnv] :
    ⦃ fun (_ : MachineData) => True ⦄
      ([Directive.instr ⟨.W64, .MOVZ (.low (.reg .X0) .W64) (.int64 1) .LSL0⟩] : Program)
    ⦃ fun _ s => s.regs.X0.toNat = 1 ⦄ := by
  vcgen simplifying_assumptions with finish
