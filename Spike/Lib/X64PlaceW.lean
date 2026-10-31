/-
**The placement facts wake's lift reads** (x86-64): `PlaceWX cfg Λ o`, the
components A1–A9 of `Scc.Cert.PlaceOK.X64.checks` at the layout `Λ`, in
place of the whole `placeOKAt`. The x86-64 twin of `Spike/Lib/PlaceW.lean`.

wake's output passes `placeOK2` (`Scc.Cert.Spawn.X64.placeOK2`), not
`placeOK`: its A11 and A12 are `placeOK2`'s `a11'`, `a12' ∧ a13`. A
hypothesis `placeOKAt cfg Λ o = true` at wake's output is false
(`#guard`ed in `Spike/Test/WakeLinkedX64.lean`), so a theorem taking it is
vacuous at the root. `PlaceWX` keeps the components both checks share. On
x86-64 `checks2` replaces only A11 and A12 (on AArch64 also A7), so all of
A1–A9 are shared; `PlaceWX` carries them all, so every `*_of_placeOKAt`
extraction of A1–A9 has a twin.

- `PlaceWX`: the nine components, by name.
- `PlaceWX.ofAt`, `PlaceWX.of2`: from `placeOKAt`, from `placeOK2At`.
- The extraction lemmas `*_of_placeWX`: the twins of the A1, A2, A4 and A8
  lemmas `PlaceW` has (`wf`, `layoutOk`, `abortLbl`, `regionsTied`, `below32`,
  `clear`, `start_at_lo`, `loadOk`, `abortsIn`, `imageIn`, `wideIn`,
  `rtWordsOk`, `rtInit`, `rtOff`, `heapOk`), their proofs those of
  `Scc.Cert.PlaceOK.X64.*_of_placeOKAt` with the component the field; at the
  link with an immediate table (`link`, `wf_link`, `clear_link`,
  `loadOk_link`, `rtWordsOk_link`, `lab_link`).
-/
import Scc.Cert.SpawnX64

namespace Spike.Lib

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **wake's placement facts** (x86-64): A1–A9 of
`Scc.Cert.PlaceOK.X64.checks cfg` at the layout `Λ` (shared by `checks` and
`Scc.Cert.Spawn.X64.checks2`). -/
structure PlaceWX (cfg : Scc.Cert.PlaceOK.Config) (Λ : Scc.Sem.Layout) (o : Scc.Cert.PlaceOK.X64.Out) : Prop where
  a1 : Scc.Cert.PlaceOK.X64.a1 o ⟨Λ⟩ = true
  a2 : Scc.Cert.PlaceOK.X64.a2 o ⟨Λ⟩ = true
  a3 : Scc.Cert.PlaceOK.X64.a3 o ⟨Λ⟩ = true
  a4 : Scc.Cert.PlaceOK.X64.a4 cfg o ⟨Λ⟩ = true
  a5 : Scc.Cert.PlaceOK.X64.a5 o ⟨Λ⟩ = true
  a6 : Scc.Cert.PlaceOK.X64.a6 o ⟨Λ⟩ = true
  a7 : Scc.Cert.PlaceOK.X64.a7 o ⟨Λ⟩ = true
  a8 : Scc.Cert.PlaceOK.X64.a8 o ⟨Λ⟩ = true
  a9 : Scc.Cert.PlaceOK.X64.a9 o ⟨Λ⟩ = true

namespace PlaceWX

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}

/-- `PlaceWX` from `placeOKAt`. -/
theorem ofAt (h : placeOKAt cfg Λ o = true) : PlaceWX cfg Λ o where
  a1 := Checks.a1_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a2 := Checks.a2_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a3 := Checks.a3_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a4 := Checks.a4_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a5 := Checks.a5_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a6 := Checks.a6_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a7 := Checks.a7_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a8 := Checks.a8_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a9 := Checks.a9_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

/-- `PlaceWX` from `placeOK2At` (`checks2` keeps A1–A9). -/
theorem of2 (h : Scc.Cert.Spawn.X64.placeOK2At cfg Λ o = true) : PlaceWX cfg Λ o where
  a1 := Checks.a1_of_ok (C := Scc.Cert.Spawn.X64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a2 := Checks.a2_of_ok (C := Scc.Cert.Spawn.X64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a3 := Checks.a3_of_ok (C := Scc.Cert.Spawn.X64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a4 := Checks.a4_of_ok (C := Scc.Cert.Spawn.X64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a5 := Checks.a5_of_ok (C := Scc.Cert.Spawn.X64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a6 := Checks.a6_of_ok (C := Scc.Cert.Spawn.X64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a7 := Checks.a7_of_ok (C := Scc.Cert.Spawn.X64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a8 := Checks.a8_of_ok (C := Scc.Cert.Spawn.X64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h
  a9 := Checks.a9_of_ok (C := Scc.Cert.Spawn.X64.checks2 cfg) (tablesOf := fun _ => ⟨Λ⟩) h

/-! ## Extraction lemmas -/

/-- **A1**: the static link is well-formed. -/
theorem wf_of_placeWX (h : PlaceWX cfg Λ o) : Λ.WF := by
  have := h.a1; simp only [Scc.Cert.PlaceOK.X64.a1, Bool.and_eq_true] at this; exact wf_of_a1 this.1.1.1

/-- **A1**: the layout facts (`PlaceOK.layoutOk`). -/
theorem layoutOk_of_placeWX (h : PlaceWX cfg Λ o) : layoutOk o.secs Λ = true := by
  have := h.a1; simp only [Scc.Cert.PlaceOK.X64.a1, Bool.and_eq_true] at this; exact this.1.1.2

/-- **A1**: the abort labels are the runtime's (`PlaceOK.abortStd`). -/
theorem abortLbl_of_placeWX (h : PlaceWX cfg Λ o) : Λ.abortLbl = Scc.Cert.Link.abortName :=
  abortLbl_of_layoutOk (layoutOk_of_placeWX h)

/-- **A1**: the heap arena, the stack pool and the pinned region at their
symbols, of the sizes the output gives them. -/
theorem regionsTied_of_placeWX (h : PlaceWX cfg Λ o) : regionsTied o.secs Λ = true :=
  regionsTied_of_layoutOk (layoutOk_of_placeWX h)

/-- **A1**: `.rodata` and every region end at or below `2 ^ 32`. -/
theorem below32_of_placeWX (h : PlaceWX cfg Λ o) :
    ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32 :=
  below32_of_layoutOk (layoutOk_of_placeWX h)

/-- The Linux entry stack is clear of the static link. -/
theorem clear_of_placeWX (h : PlaceWX cfg Λ o) : Scc.Sem.Entry.linux.clear Λ = true :=
  clear_of_below32 (below32_of_placeWX h)

/-- **A1**: `_start` is a code label at the code base. -/
theorem start_at_lo_of_placeWX (h : PlaceWX cfg Λ o) :
    Scc.Sem.X64.codeLabel Λ.code.lo o.prog "_start" = some Λ.code.lo := by
  have := h.a1; simp only [Scc.Cert.PlaceOK.X64.a1, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2

/-- **A2**: the canonical loader's checks of the link. -/
theorem loadOk_of_placeWX (h : PlaceWX cfg Λ o) :
    Scc.Cert.Link.X64.loadOk Λ o.prog o.secs o.labelOffs = true := by
  have := h.a2; simp only [Scc.Cert.PlaceOK.X64.a2, Bool.and_eq_true] at this; exact this.1.1

/-- **A2**: each abort label of the link is a code label of the cells. -/
theorem abortsIn_of_placeWX (h : PlaceWX cfg Λ o) : Scc.Cert.Link.X64.abortsIn o.prog Λ = true := by
  have := h.a2; simp only [Scc.Cert.PlaceOK.X64.a2, Bool.and_eq_true] at this; exact this.1.2

/-- **A2**: the link's image holds each data symbol's item. -/
theorem imageIn_of_placeWX (h : PlaceWX cfg Λ o) : Scc.Cert.Link.X64.imageIn o.prog o.secs Λ = true := by
  have := h.a2; simp only [Scc.Cert.PlaceOK.X64.a2, Bool.and_eq_true] at this; exact this.2

/-- **A4**: the program is in the one-word fragment. -/
theorem wideIn_of_placeWX (h : PlaceWX cfg Λ o) : Scc.Cert.WideX64.wideIn (o.prog.map (·.1)) = true := by
  have := h.a4; simp only [Scc.Cert.PlaceOK.X64.a4, Bool.and_eq_true] at this; exact this.1

/-- **A8**: the runtime's data words' checks. -/
theorem rtWordsOk_of_placeWX (h : PlaceWX cfg Λ o) : Scc.Cert.Rt.X64.rtWordsOk Λ o.prog o.secs = true := by
  have h8 := h.a8; simp only [Scc.Cert.PlaceOK.X64.a8, Bool.and_eq_true] at h8; exact h8.1.1.1

/-- **A8**: no runtime word has an initial word in the load. -/
theorem rtInit_of_placeWX (h : PlaceWX cfg Λ o) : Scc.Cert.Rt.X64.rtInitOk Λ o.prog o.secs = true := by
  have h8 := h.a8; simp only [Scc.Cert.PlaceOK.X64.a8, Bool.and_eq_true] at h8; exact h8.1.1.2

/-- **A8**: the first TCB's words clear of `.data` and the heap. -/
theorem rtOff_of_placeWX (h : PlaceWX cfg Λ o) : Scc.Cert.Rt.X64.rtOffOk Λ o.prog o.secs = true := by
  have h8 := h.a8; simp only [Scc.Cert.PlaceOK.X64.a8, Bool.and_eq_true] at h8; exact h8.1.2

/-- **A8**: the heap arena's symbols and size (`heapOk`). -/
theorem heapOk_of_placeWX (h : PlaceWX cfg Λ o) : heapOk o Λ = true := by
  have h8 := h.a8; simp only [Scc.Cert.PlaceOK.X64.a8, Bool.and_eq_true] at h8; exact h8.2

/-! ## At the link with an immediate table -/

section ImmsAt

variable (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`PlaceWX` at the link with an immediate table**: the checks read no
immediates, so each component is the static one's by definition. -/
theorem link (h : PlaceWX cfg Λ o) : PlaceWX cfg { Λ with imms := i } o :=
  ⟨h.a1, h.a2, h.a3, h.a4, h.a5, h.a6, h.a7, h.a8, h.a9⟩

/-- **A1** at the link with an immediate table. -/
theorem wf_link_of_placeWX (h : PlaceWX cfg Λ o) : ({ Λ with imms := i } : Scc.Sem.Layout).WF :=
  wf_withImms (wf_of_placeWX h) i

/-- **A1** at the link with an immediate table: the entry stack clear of it. -/
theorem clear_link_of_placeWX (h : PlaceWX cfg Λ o) : Scc.Sem.Entry.linux.clear { Λ with imms := i } = true :=
  (clear_withImms _ i).trans (clear_of_placeWX h)

/-- **A2** at the link with an immediate table: the loader's checks. -/
theorem loadOk_link_of_placeWX (h : PlaceWX cfg Λ o) :
    Scc.Cert.Link.X64.loadOk { Λ with imms := i } o.prog o.secs o.labelOffs = true :=
  (loadOk_withImms _ i _ _ _).trans (loadOk_of_placeWX h)

/-- **A8** at the link with an immediate table: the runtime's data words' checks. -/
theorem rtWordsOk_link_of_placeWX (h : PlaceWX cfg Λ o) :
    Scc.Cert.Rt.X64.rtWordsOk { Λ with imms := i } o.prog o.secs = true :=
  (rtWordsOk_withImms _ i _ _).trans (rtWordsOk_of_placeWX h)

/-- **A8** at the link with an immediate table: a runtime word at its label
in the loaded thread. -/
theorem lab_link_of_placeWX (h : PlaceWX cfg Λ o) {x : String} (hx : x ∈ Scc.Cert.Rt.X64.rtNames)
    (E : Scc.Sem.Entry) :
    let Λ : Scc.Sem.Layout := { Λ with imms := i }
    ((_root_.Executable.labels (Scc.Sem.X64.threadAt E Λ.code.lo o.prog
        (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label x).toBitVec =
      Scc.Cert.Rt.X64.rtA Λ o.prog o.secs x :=
  Scc.Cert.Rt.X64.label_of_rtWordsOk (loadOk_link_of_placeWX i h) (rtWordsOk_link_of_placeWX i h) hx E

end ImmsAt

end PlaceWX

/-- info: 'Spike.Lib.PlaceWX.of2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PlaceWX.of2
/-- info: 'Spike.Lib.PlaceWX.lab_link_of_placeWX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PlaceWX.lab_link_of_placeWX

end Spike.Lib
