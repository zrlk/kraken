/-
**The placement facts wake's lift reads** (AArch64): `PlaceW cfg Λ o`, the
components A1, A2, A4, A6 and A8 of `Scc.Cert.PlaceOK.A64.checks` at the
layout `Λ`, in place of the whole `placeOKAt`.

wake's output passes `placeOK2` (`Scc.Cert.Spawn.A64.placeOK2`), not
`placeOK`: its A7, A11 and A12 are `placeOK2`'s `a7'`, `a11'`, `a12' ∧ a13`.
A hypothesis `placeOKAt cfg Λ o = true` at wake's output is false, so a
theorem taking it is vacuous at the root. `PlaceW` keeps only the
components both checks share (`checks2` is `checks` with A7, A11, A12
replaced), so wake's certificate instantiates it.

- `PlaceW`: the five components, by name.
- `PlaceW.ofAt`, `PlaceW.of2`: from `placeOKAt`, from `placeOK2At`.
- The extraction lemmas `*_of_placeW`: the twins of
  `Scc.Cert.PlaceOK.A64.*_of_placeOKAt` (A1: `wf`, `layoutOk`, `abortLbl`,
  `regionsTied`, `below32`, `clear`; A2: `loadOk`; A4: `wideIn`; A8:
  `rtWordsOk`, `rtInit`, `rtOff`), their proofs those lemmas' with the
  component the field; at the link with an immediate table (`wf_link`,
  `clear_link`, `loadOk_link`, `rtWordsOk_link`, `lab_link`).
-/
import Scc.Cert.SpawnA64

namespace Spike.Lib

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- **wake's placement facts**: A1, A2, A4, A6 and A8 of
`Scc.Cert.PlaceOK.A64.checks cfg` at the layout `Λ` (shared by `checks` and
`Scc.Cert.Spawn.A64.checks2`). -/
structure PlaceW (cfg : Scc.Cert.PlaceOK.Config) (Λ : Scc.Sem.Layout) (o : Scc.Cert.PlaceOK.A64.Out) : Prop where
  a1 : Scc.Cert.PlaceOK.A64.a1 o ⟨Λ⟩ = true
  a2 : Scc.Cert.PlaceOK.A64.a2 o ⟨Λ⟩ = true
  a4 : Scc.Cert.PlaceOK.A64.a4 cfg o ⟨Λ⟩ = true
  a6 : Scc.Cert.PlaceOK.A64.a6 o ⟨Λ⟩ = true
  a8 : Scc.Cert.PlaceOK.A64.a8 o ⟨Λ⟩ = true

namespace PlaceW

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out}

/-- `PlaceW` from `placeOKAt`. -/
theorem ofAt (h : placeOKAt cfg Λ o = true) : PlaceW cfg Λ o where
  a1 := Checks.a1_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a2 := Checks.a2_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a4 := Checks.a4_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a6 := Checks.a6_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a8 := Checks.a8_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

/-- `PlaceW` from `placeOK2At` (`checks2` keeps A1, A2, A4, A6, A8). -/
theorem of2 (h : Scc.Cert.Spawn.A64.placeOK2At cfg Λ o = true) : PlaceW cfg Λ o where
  a1 := Checks.a1_of_ok (C := Scc.Cert.Spawn.A64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a2 := Checks.a2_of_ok (C := Scc.Cert.Spawn.A64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a4 := Checks.a4_of_ok (C := Scc.Cert.Spawn.A64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a6 := Checks.a6_of_ok (C := Scc.Cert.Spawn.A64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a8 := Checks.a8_of_ok (C := Scc.Cert.Spawn.A64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h

/-! ## Extraction lemmas -/

/-- **A1**: the static link is well-formed. -/
theorem wf_of_placeW (h : PlaceW cfg Λ o) : Λ.WF := by
  have := h.a1; simp only [Scc.Cert.PlaceOK.A64.a1, Bool.and_eq_true] at this; exact wf_of_a1 this.1.1.1

/-- **A1**: the layout facts (`PlaceOK.layoutOk`). -/
theorem layoutOk_of_placeW (h : PlaceW cfg Λ o) : layoutOk o.secs Λ = true := by
  have := h.a1; simp only [Scc.Cert.PlaceOK.A64.a1, Bool.and_eq_true] at this; exact this.1.1.2

/-- **A1**: the abort labels are the runtime's (`PlaceOK.abortStd`). -/
theorem abortLbl_of_placeW (h : PlaceW cfg Λ o) : Λ.abortLbl = Scc.Cert.Link.abortName :=
  abortLbl_of_layoutOk (layoutOk_of_placeW h)

/-- **A1**: the heap arena, the stack pool and the pinned region at their
symbols, of the sizes the output gives them. -/
theorem regionsTied_of_placeW (h : PlaceW cfg Λ o) : regionsTied o.secs Λ = true :=
  regionsTied_of_layoutOk (layoutOk_of_placeW h)

/-- **A1**: `.rodata` and every region end at or below `2 ^ 32`. -/
theorem below32_of_placeW (h : PlaceW cfg Λ o) :
    ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32 :=
  below32_of_layoutOk (layoutOk_of_placeW h)

/-- The Linux entry stack is clear of the static link. -/
theorem clear_of_placeW (h : PlaceW cfg Λ o) : Scc.Sem.Entry.linux.clear Λ = true :=
  clear_of_below32 (below32_of_placeW h)

/-- **A2**: the loader's checks. -/
theorem loadOk_of_placeW (h : PlaceW cfg Λ o) : Scc.Cert.Link.A64.loadOk Λ o.prog o.secs = true := by
  have := h.a2; simp only [Scc.Cert.PlaceOK.A64.a2, Bool.and_eq_true] at this; exact this.1.1

/-- **A4**: the program is in the one-word fragment. -/
theorem wideIn_of_placeW (h : PlaceW cfg Λ o) : Scc.Cert.WideA64.wideIn o.prog = true := by
  have := h.a4; simp only [Scc.Cert.PlaceOK.A64.a4, Bool.and_eq_true] at this; exact this.1

/-- **A8**: the runtime's data words' checks. -/
theorem rtWordsOk_of_placeW (h : PlaceW cfg Λ o) : Scc.Cert.Rt.A64.rtWordsOk Λ o.prog o.secs = true := by
  have h8 := h.a8; simp only [Scc.Cert.PlaceOK.A64.a8, Bool.and_eq_true] at h8; exact h8.1.1.1

/-- **A8**: no runtime word has an initial word in the load. -/
theorem rtInit_of_placeW (h : PlaceW cfg Λ o) : Scc.Cert.Rt.A64.rtInitOk Λ o.prog o.secs = true := by
  have h8 := h.a8; simp only [Scc.Cert.PlaceOK.A64.a8, Bool.and_eq_true] at h8; exact h8.1.1.2

/-- **A8**: the runtime's words clear of the placed data. -/
theorem rtOff_of_placeW (h : PlaceW cfg Λ o) : Scc.Cert.Rt.A64.rtOffOk Λ o.prog o.secs = true := by
  have h8 := h.a8; simp only [Scc.Cert.PlaceOK.A64.a8, Bool.and_eq_true] at h8; exact h8.1.2

/-! ## At the link with an immediate table -/

section ImmsAt

variable (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`PlaceW` at the link with an immediate table**: the checks read no
immediates, so each component is the static one's by definition. -/
theorem link (h : PlaceW cfg Λ o) : PlaceW cfg { Λ with imms := i } o :=
  ⟨h.a1, h.a2, h.a4, h.a6, h.a8⟩

/-- **A1** at the link with an immediate table. -/
theorem wf_link_of_placeW (h : PlaceW cfg Λ o) : ({ Λ with imms := i } : Scc.Sem.Layout).WF :=
  wf_withImms (wf_of_placeW h) i

/-- **A1** at the link with an immediate table: the entry stack clear of it. -/
theorem clear_link_of_placeW (h : PlaceW cfg Λ o) : Scc.Sem.Entry.linux.clear { Λ with imms := i } = true :=
  (clear_withImms _ i).trans (clear_of_placeW h)

/-- **A2** at the link with an immediate table: the loader's checks. -/
theorem loadOk_link_of_placeW (h : PlaceW cfg Λ o) :
    Scc.Cert.Link.A64.loadOk { Λ with imms := i } o.prog o.secs = true :=
  (loadOk_withImms _ i _ _).trans (loadOk_of_placeW h)

/-- **A8** at the link with an immediate table: the runtime's data words' checks. -/
theorem rtWordsOk_link_of_placeW (h : PlaceW cfg Λ o) :
    Scc.Cert.Rt.A64.rtWordsOk { Λ with imms := i } o.prog o.secs = true :=
  (rtWordsOk_withImms _ i _ _).trans (rtWordsOk_of_placeW h)

/-- **A8** at the link with an immediate table: a runtime word at its label
in the loaded thread. -/
theorem lab_link_of_placeW (h : PlaceW cfg Λ o) {x : String} (hx : x ∈ Scc.Cert.Rt.A64.rtNames)
    (E : Scc.Sem.Entry) :
    let Λ : Scc.Sem.Layout := { Λ with imms := i }
    ((_root_.Executable.labels (Scc.Sem.A64.threadAt E Λ.code.lo o.prog
        (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label x).toBitVec =
      Scc.Cert.Rt.A64.rtA Λ o.prog o.secs x :=
  Scc.Cert.Rt.A64.label_of_rtWordsOk (loadOk_link_of_placeW i h) (rtWordsOk_link_of_placeW i h) hx E

end ImmsAt

end PlaceW

/-- info: 'Spike.Lib.PlaceW.of2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PlaceW.of2
/-- info: 'Spike.Lib.PlaceW.lab_link_of_placeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PlaceW.lab_link_of_placeW

end Spike.Lib
