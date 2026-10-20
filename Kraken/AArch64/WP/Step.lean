/-
Copied from x64's `Kraken/Step.lean` at commit `9953817`, adapted for AArch64.
The SysV `pushRa`/`retAddr` section becomes "The link register at a call"
(`MachineData.setLr`/`lr`): AArch64 hands the return address over in `X30`.

The machine's step relation, and procedure specifications over it.

`instrStep` runs one instruction of the ambient code; `Eventually instrStep`
(`Kraken.OmniSemantics`) is the run. A procedure specification `ProcSpec`
says that a run entered at an address reaches the return address with a
postcondition — a proposition about the executable alone, in these terms and
nothing else. This file is the interface between a procedure's proof and its
callers and linker: a caller or a linker imports this; how a body is shown to
meet its `ProcSpec` is a separate matter (`Kraken.MachineWP`'s `wp` and
`ProcSpec.of_cfg_post`, or any other method that concludes `Eventually`).
-/
import Kraken.AArch64.WP.SegmentExtract

open Kraken

/-! ## The ambient code -/

/-- The ambient executable. -/
class CodeEnv where
  env : _root_.Executable

/-- The ambient code. -/
abbrev cenv [CodeEnv] : Kraken.Executable Directive := CodeEnv.env

/- Upstream marks `Executable.labels` reducible for the kstep pipeline. The
grind patterns of the spec dictionary key on `labels` as a stable head, so it
is semireducible here and in every file that consumes the dictionary. -/
set_option allowUnsafeReducibility true in
attribute [semireducible] _root_.Executable.labels

/-! ## The step relation

`instrStep` runs exactly the cell at the current pc: the machine's own
interpreter, with the fall-through and jump continuations both stopping. It
refines kraken's `straightlineStep`, which runs a whole segment burst, into
the granularity the per-instruction rules need. -/

/-- The cells at an address, past the labels that share it. A label occupies
no bytes, so several cells sit at one address; the machine runs the first one
that is not a label. -/
def Kraken.Executable.codeAt (e : Kraken.Executable Directive) (pc : Int64) : List (Directive × Nat) :=
  (e.directivesFromAddress pc).dropWhile (fun c => c.1.isLabel)

/-- Running the cell `(d, z)` at `st`: either every resolution falls through,
into `post` at the address behind the cell, or every resolution jumps, into
`post` at the target. Each disjunct poisons the other continuation, which is
the shape `Directive.interp_sound` consumes. -/
def Kraken.Executable.stepAt (e : Kraken.Executable Directive) (d : Directive) (z : Nat) (st : MachineState)
    (post : @Post MachineState) : Prop :=
  (@Directive.interp (_root_.Executable.labels e) d st.1 (.mk st.2 (st.2 + .ofNat z))
      (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All
    (fun m => post (m.1, st.2 + .ofNat z))
  ∨ (@Directive.interp (_root_.Executable.labels e) d st.1 (.mk st.2 (st.2 + .ofNat z))
      (fun _ => .unimplemented "fallthrough") (fun pc' s' => .done (s', pc'))).All post

/-- One instruction of the ambient code, run from `st`. -/
def Kraken.Executable.instrStep (e : Kraken.Executable Directive) (st : MachineState) (post : @Post MachineState) :
    Prop :=
  ∃ d z rest, e.codeAt st.2 = (d, z) :: rest ∧ e.stepAt d z st post

/-! ## The link register at a call

AArch64's counterpart of x64's SysV `pushRa`/`retAddr`: `BL` and `BLR` leave
the return address in `X30` (the link register) instead of on the stack, and
`RET` jumps to it. The call writes one register and no memory, so a call has
no side condition on the stack; a procedure that calls another saves `X30`
itself (`STP X29, X30, [SP, #-16]!` … `LDP`). -/

/-- The state a call leaves behind: the return address in `X30`. -/
def MachineData.setLr (s : MachineData) (ra : Int64) : MachineData :=
  { s with regs := s.regs.setXReg .X30 ra.toBitVec }

/-- The address the link register holds. -/
def MachineData.lr (t : MachineData) : Int64 := Int64.ofBitVec t.regs.X30.toBitVec

@[grind =] theorem MachineData.lr_eq (t : MachineData) :
    t.lr = Int64.ofBitVec t.regs.X30.toBitVec := rfl

@[grind =] theorem MachineData.regs_setLr (s : MachineData) (ra : Int64) :
    (s.setLr ra).regs = s.regs.setXReg .X30 ra.toBitVec := rfl

@[grind =] theorem MachineData.status_setLr (s : MachineData) (ra : Int64) :
    (s.setLr ra).status = s.status := rfl

@[grind =] theorem MachineData.dmem_setLr (s : MachineData) (ra : Int64) :
    (s.setLr ra).dmem = s.dmem := rfl

@[simp, grind =] theorem MachineData.lr_setLr (s : MachineData) (ra : Int64) :
    (s.setLr ra).lr = ra := by
  simp [MachineData.lr, MachineData.setLr, Reg64s.setXReg]

/-! ## Procedures by specification

`call_spec` takes the callee's text. A procedure that calls one that is not
yet verified — itself, or its partner in a mutual recursion — needs the callee
as a *specification* instead. `ProcSpec` is that: a proposition about the
executable alone, so it can be assumed by one proof and established by
another, and be the subject of an induction.

The specification is stated at the callee's entry state `t` and the address
`ra` the run must reach. Nothing in it mentions the stack: how `ra` is handed
over is part of `Pre` (`t.lr = ra` under the AArch64
convention, where `BL` leaves it in `X30`), and `Post` relates `t` to the exit state however
the convention has it. A tail call `b f` is a run that reaches `ra` through
`f`, so it is covered by `f`'s `ProcSpec` at the same `ra`.

Two forms. `ProcSpec` carries a logical variable `x : α` (the argument, the
caller's memory frame) that a call site instantiates. `ProcSpecK` packs the
logical variables inside `Spec`, existentially, with the continuation `K` the
run must end in, in the style of `fun_spec_from_label`. They are
interderivable (`ProcSpec.toK`); the examples show both. -/

/-- A run of `e` entered at `entry` in a state `t` with `Pre x ra t` reaches
`ra` in a state `s'` with `Post x ra t s'`. -/
def Kraken.Executable.ProcSpec (e : Kraken.Executable Directive) (entry : Int64) {α : Type}
    (Pre : α → Int64 → MachineData → Prop)
    (Post : α → Int64 → MachineData → MachineData → Prop) : Prop :=
  ∀ (x : α) (ra : Int64) (t : MachineData), Pre x ra t →
    Eventually e.instrStep (fun st => st.2 = ra ∧ Post x ra t st.1) (t, entry)

/-- The continuation form: `Spec ra K t` is what the procedure asks of its
entry state `t` for a run that reaches `ra` in a state satisfying `K`. -/
def Kraken.Executable.ProcSpecK (e : Kraken.Executable Directive) (entry : Int64)
    (Spec : Int64 → (MachineData → Prop) → MachineData → Prop) : Prop :=
  ∀ (ra : Int64) (K : MachineData → Prop) (t : MachineData), Spec ra K t →
    Eventually e.instrStep (fun st => st.2 = ra ∧ K st.1) (t, entry)

theorem Kraken.Executable.ProcSpec.toK {e : Kraken.Executable Directive} {entry : Int64}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : e.ProcSpec entry Pre Post) :
    e.ProcSpecK entry (fun ra K t => ∃ x, Pre x ra t ∧ ∀ s', Post x ra t s' → K s') := by
  rintro ra K t ⟨x, hpre, hk⟩
  exact eventually_weaken _ _ _ _ (fun st ⟨ha, hp⟩ => ⟨ha, hk _ hp⟩) (h x ra t hpre)

theorem Kraken.Executable.ProcSpecK.toGhost {e : Kraken.Executable Directive} {entry : Int64}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : e.ProcSpecK entry (fun ra K t => ∃ x, Pre x ra t ∧ ∀ s', Post x ra t s' → K s')) :
    e.ProcSpec entry Pre Post :=
  fun x ra t hpre => h ra (Post x ra t) t ⟨x, hpre, fun _ hp => hp⟩
