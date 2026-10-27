import Spike.Lib.Src.SrcSafe2
import Spike.Lib.FrameRunM
import Spike.Lib.ZeroTy
import Spike.Lib.Consumer1

/-!
**The frame runs' obligations at an `Accepted2` program's pairs**
(ISA-neutral): `SFactsA`'s `cell` and `zero` (the loads and stores a frame
run reaches access single-word cells; the buffers it allocates have types
the zero check accepts) at every pair whose frames are free of acquire
loads, release stores, spawns and buffer allocations of a type the zero
check rejects (`FrOk2`). No block of an `Accepted2` program has any
(`progNoS_zbad_of_accepted2`: `body2`'s buffers are of one-word element
types, `elem2`, which the zero check accepts), so `FrOk2` is kept by every
frame step and memory let (`FrOk2.run`, `FrOk2.runM`).

- `ZBad`, `FrOk2`: the operations excluded, at a pair;
- `zeroOkTy_of_elem2`, `noS_zbad_of_body2`, `progNoS_zbad_of_accepted2`;
- `FrOk2.step`, `FrOk2.run`, `FrOk2.stepM`, `FrOk2.runM`: kept by the runs;
- `RunOk2`, `RunOk2.run`, `runOk2_of`: the obligations, kept by a frame
  run, from `FrOk2`.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm A9NoSpawn Scc.Sem
open Scc.Lower (body2)
open Spike.Lib (FrameRun FrameStep FrameRunM FrameStepM)
open Spike.Lib.Consumer1 (OneCellTy)

/-- **The operations excluded at an `Accepted2` program's pairs**: an
acquire load, a release store, a spawn (`AcqOp`), a buffer allocation of a
type the zero check rejects. -/
def ZBad : Op → Prop
  | .load true _ | .store true _ _ _ | .spawn .. => True
  | .newBuf _ τ => ZeroOkTy τ = false
  | _ => False

/-- **A pair free of `ZBad`**: its control's term and every suspended
frame's body. -/
def FrOk2 (c : Ctl) (fs : List TermRun.Frame) : Prop := NoS ZBad c.term ∧ ∀ fr ∈ fs, NoS ZBad fr.body

/-- **A one-word element type passes the zero check.** -/
theorem zeroOkTy_of_elem2 {τ : Ty} (h : Scc.Lower.elem2 τ = true) : ZeroOkTy τ = true := by
  cases τ <;> simp_all [Scc.Lower.elem2, ZeroOkTy, TermRun.zeroWords, TermRun.close, substTs, zeroWordB]

/-- **An `Accepted2` body is free of `ZBad`.** -/
theorem noS_zbad_of_body2 : ∀ (e : Expr) {cx : Scc.Lower.Cx2} {cs bufs : List (String × Nat)}
    {scope : List String}, body2 cx cs bufs scope e = true → NoS ZBad e := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro cx cs bufs scope h
    cases op
    case newBuf n τ =>
      simp only [body2, Bool.and_eq_true] at h
      obtain ⟨⟨⟨-, -⟩, hτ⟩, hm⟩ := h
      refine ⟨fun hz => ?_, ?_⟩
      · simp only [ZBad] at hz
        rw [zeroOkTy_of_elem2 hτ] at hz; cases hz
      · split at hm
        · simp only [Bool.and_eq_true] at hm
          exact ih hm.2
        · simp at hm
    case xchgAt b i v =>
      cases b <;> cases i <;> simp only [body2, Bool.and_eq_true, Bool.false_eq_true] at h
      exact ⟨id, ih h.2⟩
    all_goals first
      | (simp [body2] at h; done)
      | (simp only [body2, Bool.and_eq_true] at h
         exact ⟨fun hz => by simp [ZBad] at hz <;> simp_all [body2], ih h.2⟩)
  | split a x y e ih =>
    intro cx cs bufs scope h
    simp only [body2, Bool.and_eq_true] at h
    exact ih h.2
  | unpack a i x e ih =>
    intro cx cs bufs scope h
    simp only [body2, Bool.and_eq_true] at h
    exact ih h.2
  | ifeq a b yes no ihy ihn =>
    intro cx cs bufs scope h
    simp only [body2, Bool.and_eq_true] at h
    exact ⟨ihy h.1.2, ihn h.2⟩
  | ret a => intro _ _ _ _ _; trivial
  | _ => intro _ _ _ _ h; simp [body2] at h

theorem printExt_noZBad : NoS ZBad Scc.Frontend.printExtD.body := by
  simp [Scc.Frontend.printExtD, Scc.Frontend.printBody, NoS, ZBad]

theorem printLoop_noZBad : NoS ZBad Scc.Frontend.printLoopD.body := by
  simp [Scc.Frontend.printLoopD, Scc.Frontend.printLBody, Scc.Frontend.printAdv, Scc.Frontend.printNext, NoS,
    ZBad]

/-- **No block of an `Accepted2` program has a `ZBad` operation.** -/
theorem progNoS_zbad_of_accepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) : ProgNoS ZBad p := by
  intro d hd
  rcases blocks_of_accepted2 hp d hd with (rfl | rfl) | ⟨cx, scope, h⟩
  · exact printExt_noZBad
  · exact printLoop_noZBad
  · exact noS_zbad_of_body2 _ h

namespace FrOk2

variable {p : Prog} {c c' : Ctl} {fs fs' : List TermRun.Frame}

/-- **A frame step keeps `FrOk2`** (`tstep_noS` at the step's `tstep`,
`FrameStep.tstep`). -/
theorem step (hp : ProgNoS ZBad p) (h : FrameStep p (c, fs) (c', fs')) (hf : FrOk2 c fs) : FrOk2 c' fs' := by
  let g : TermRun.G := { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 }
  let th : TermRun.TTh := { term := c.term, env := c.env, stack := fs }
  have ht := FrameStep.tstep h (g := g) (mem := #[]) (pairs := []) (th := th) rfl rfl rfl rfl rfl
  have hr := tstep_noS (g := g) hp ⟨hf.1, hf.2⟩ (ht ▸ List.mem_singleton.mpr rfl)
  exact ⟨hr.1, hr.2⟩

/-- **A frame run keeps `FrOk2`.** -/
theorem run (hp : ProgNoS ZBad p) (h : FrameRun p (c, fs) (c', fs')) (hf : FrOk2 c fs) : FrOk2 c' fs' := by
  generalize hq : (c, fs) = q at h
  generalize hq' : (c', fs') = q' at h
  induction h generalizing c fs with
  | refl => cases hq; cases hq'; exact hf
  | step hs _ ih =>
    subst hq
    exact ih (step hp hs hf) rfl hq'

/-- **A frame step or a memory let keeps `FrOk2`.** -/
theorem stepM (hp : ProgNoS ZBad p) (h : FrameStepM p (c, fs) (c', fs')) (hf : FrOk2 c fs) : FrOk2 c' fs' := by
  cases h with
  | frame hs => exact step hp hs hf
  | mem _ ht _ =>
    have h1 := hf.1
    rw [ht] at h1
    exact ⟨h1.2, hf.2⟩

/-- **A `FrameRunM` keeps `FrOk2`.** -/
theorem runM (hp : ProgNoS ZBad p) (h : FrameRunM p (c, fs) (c', fs')) (hf : FrOk2 c fs) : FrOk2 c' fs' := by
  generalize hq : (c, fs) = q at h
  generalize hq' : (c', fs') = q' at h
  induction h generalizing c fs with
  | refl => cases hq; cases hq'; exact hf
  | step hs _ ih =>
    subst hq
    exact ih (stepM hp hs hf) rfl hq'

end FrOk2

/-- **The obligations at the controls the frame runs reach** from `(c, fs)`
(`SFactsA.cell`, `SFactsA.zero`): the loads and stores access single-word
cells, and every buffer allocated has a type the zero check accepts. -/
structure RunOk2 (p : Prog) (c : Ctl) (fs : List TermRun.Frame) : Prop where
  cell : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a e ty w,
    (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty
  zero : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a τ e, c'.term = .let_ x (.newBuf a τ) e →
    ZeroOkTy τ = true

variable {p : Prog} {c c' : Ctl} {fs fs' : List TermRun.Frame}

/-- **A frame run keeps `RunOk2`.** -/
theorem RunOk2.run (h : RunOk2 p c fs) (hr : FrameRun p (c, fs) (c', fs')) : RunOk2 p c' fs' :=
  ⟨fun _ _ hr' => h.cell _ _ (hr.trans hr'), fun _ _ hr' => h.zero _ _ (hr.trans hr')⟩

/-- **`RunOk2` from `FrOk2`**: no control a frame run reaches loads
acquiring or stores releasing, and every buffer it allocates passes the zero
check. -/
theorem runOk2_of (hp : ProgNoS ZBad p) (h : FrOk2 c fs) : RunOk2 p c fs where
  cell := fun _ _ hr x a e _ _ hc => by
    have h1 := (FrOk2.run hp hr h).1
    rcases hc with hc | ⟨b, hc⟩ <;> rw [hc] at h1 <;> exact (h1.1 trivial).elim
  zero := fun _ _ hr x a τ e hc => by
    have h1 := (FrOk2.run hp hr h).1
    rw [hc] at h1
    cases hz : ZeroOkTy τ
    · exact (h1.1 hz).elim
    · rfl

/--
info: 'Spike.Lib.LowerNode.runOk2_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runOk2_of

end Spike.Lib.LowerNode
