/-
**The controls an `Accepted1` program's frame runs reach** (ISA-neutral):
every term along a frame run (`FrameRun`, `Spike/Lib/SegS.lean`) from the
start's tail call into `main` is a subterm of a code block's `Accepted1` body,
and so is every suspended frame's body (`Good1`, kept by every frame step:
`good1_run`). Such a control is at no load, store or buffer allocation
(`Good1.not_load`, `Good1.not_store`, `Good1.not_newBuf`).

- `body1_mono`: `body1` is monotone in the code blocks it may call;
  `body1_of_decls1`: every code block of a `decls1` program has an
  `Accepted1` body over all of the program's names.
- `LocalStepS.not_call`: a control at a call takes no local step (the step
  pushes a frame).
- `Good1.quiet_run`: every control a frame run reaches from a `Good1` pair
  with no hold is `Quiet` (`SegWS.lag`'s `hq`).
-/
import Spike.Lib.SegS
import Spike.Lib.Quiet1

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising
open Scc.Lower (body1 decls1 decl1 callee1 Accepted1 params1)

/-! ## `body1` over all of the program's names -/

theorem callee1_mono {E E' : List String} (hE : ∀ g, g ∈ E → g ∈ E') {g : String} (h : callee1 E g = true) :
    callee1 E' g = true := by
  simp only [callee1, Bool.and_eq_true, List.contains_iff_mem] at h ⊢
  exact ⟨hE _ h.1, h.2⟩

/-- **`body1` is monotone in the code blocks it may call.** -/
theorem body1_mono {E E' : List String} (hE : ∀ g, g ∈ E → g ∈ E') (e : Expr) :
    ∀ sc, body1 E sc e = true → body1 E' sc e = true := by
  induction e with
  | let_ x op e ih =>
    intro sc h
    cases op <;> simp only [body1, Bool.and_eq_true] at h ⊢
    all_goals first | (simp at h; done) | skip
    all_goals first
      | exact ⟨h.1, ih _ h.2⟩
      | exact ⟨⟨⟨⟨callee1_mono hE h.1.1.1.1, h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, ih _ h.2⟩
  | ifeq a b yes no ihy ihn =>
    intro sc h
    simp only [body1, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, ihy _ h.1.2⟩, ihn _ h.2⟩
  | ret a => intro sc h; simpa only [body1] using h
  | _ => intro sc h; simp [body1] at h

/-- **Every code block of a `decls1` program** has an `Accepted1` body over
the names before the program and all of its own. -/
theorem body1_of_decls1 : ∀ (E : List String) (p : Prog), decls1 E p = true →
    ∀ d ∈ p, body1 (E ++ p.map (·.name)) (params1 d) d.body = true
  | _, [], _, _, hd => by simp at hd
  | E, d' :: ds, h, d, hd => by
    simp only [decls1, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hd with rfl | hd
    · have h1 := h.1
      simp only [decl1, Bool.and_eq_true] at h1
      exact body1_mono (fun g hg => List.mem_append_left _ hg) _ _ h1.2
    · refine body1_mono (fun g hg => ?_) _ _ (body1_of_decls1 _ ds h.2 d hd)
      simp only [List.mem_append, List.mem_cons, List.map_cons] at hg ⊢
      rcases hg with (h | h) | h
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

/-! ## The controls reached -/

/-- **A term of an `Accepted1` program's run**: a subterm of a code block's
body (`body1` over all of `p`'s names, at some scope), or the start's tail
call into `main`. -/
def Term1 (p : Prog) (e : Expr) : Prop :=
  (∃ sc, body1 (p.map (·.name)) sc e = true) ∨ ∃ i a ts, e = .tail "main" i a ts

/-- **A control with frames an `Accepted1` program's run reaches**: its
term a `Term1`, every frame's body a subterm of a code block's body. -/
def Good1 (p : Prog) (q : Ctl × List TermRun.Frame) : Prop :=
  Term1 p q.1.term ∧ ∀ f ∈ q.2, ∃ sc, body1 (p.map (·.name)) sc f.body = true

/-- The start's control (a tail call into `main`, no frame) is `Good1`. -/
theorem good1_tail {p : Prog} {c : Ctl} {i : List String} {a : At} {ts : List Ty}
    (h : c.term = .tail "main" i a ts) : Good1 p (c, []) :=
  ⟨.inr ⟨i, a, ts, h⟩, fun _ hf => by simp at hf⟩

variable {p : Prog}

/-- **A control at a call takes no local step**: the step pushes the
caller's frame. -/
theorem LocalStepS.not_call {c c' : Ctl} (h : LocalStepS p c c') {x f : String} {is : List String} {a : At}
    {ts : List Ty} {e : Expr} (ht : c.term = .let_ x (.call f is a ts) e) : False := by
  have := h.2 { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
    { term := c.term, env := c.env } rfl rfl rfl rfl
  simp only [TermRun.tstep, ht, TermRun.callFrame, TermRun.enter, TermRun.ol] at this
  cases hf : p.find? (·.name == f) with
  | none => simp [hf] at this
  | some d =>
    cases hv : TermRun.evalAt c.env a with
    | none => simp [hf, hv] at this
    | some v =>
      simp [hf, hv] at this

private theorem term1_body {c : Ctl} (h : Term1 p c.term) (hn : ∀ i a ts, c.term ≠ .tail "main" i a ts) :
    ∃ sc, body1 (p.map (·.name)) sc c.term = true :=
  h.elim id fun ⟨i, a, ts, ht⟩ => (hn i a ts ht).elim

/-- **A local step keeps `Term1`.** -/
theorem term1_localStepS (hp : Accepted1 p = true) {c c' : Ctl} (hs : LocalStepS p c c') (h : Term1 p c.term) :
    Term1 p c'.term := by
  rcases h with ⟨sc, hb⟩ | ⟨i, a, ts, ht⟩
  · cases hc : c.term with
    | let_ x op e =>
      rw [hc] at hb
      cases op <;> simp only [body1, Bool.and_eq_true] at hb
      all_goals first | (simp at hb; done) | skip
      case atom a => exact .inl ⟨x :: sc, localStep_let1 hs.toLocalStep hc (.inl ⟨a, rfl⟩) ▸ hb.2⟩
      case add a b => exact .inl ⟨x :: sc, localStep_let1 hs.toLocalStep hc (.inr (.inl ⟨a, b, rfl⟩)) ▸ hb.2⟩
      case sub a b => exact .inl ⟨x :: sc, localStep_let1 hs.toLocalStep hc (.inr (.inr ⟨a, b, rfl⟩)) ▸ hb.2⟩
      case call f is a ts => exact (hs.not_call hc).elim
    | ifeq a b yes no =>
      rw [hc] at hb
      simp only [body1, Bool.and_eq_true] at hb
      rcases localStep_ifeq hs.toLocalStep hc with h | h
      · exact .inl ⟨sc, h ▸ hb.1.2⟩
      · exact .inl ⟨sc, h ▸ hb.2⟩
    | ret a => exact absurd hc (hs.not_ret a)
    | _ => rw [hc] at hb; simp [body1] at hb
  · have hp' := hp
    simp only [Accepted1, Bool.and_eq_true] at hp'
    cases hf : p.find? (·.name == "main") with
    | none =>
      have := hs.2 { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
        { term := .tail "main" i a ts, env := c.env } rfl ht.symm rfl rfl
      simp [TermRun.tstep, TermRun.enter, TermRun.ol, hf] at this
    | some d =>
      have hb := body1_of_decls1 [] p hp'.1.2 d (List.mem_of_find?_eq_some hf)
      exact .inl ⟨params1 d, localStep_tail hs.toLocalStep ht hf ▸ hb⟩

/-- **A frame step keeps `Good1`.** -/
theorem good1_step (hp : Accepted1 p = true) {q q' : Ctl × List TermRun.Frame} (h : FrameStep p q q')
    (hg : Good1 p q) : Good1 p q' := by
  cases h with
  | loc hs => exact ⟨term1_localStepS hp hs hg.1, hg.2⟩
  | @call c fs x f is a e d t ws ht hd ha =>
    obtain ⟨sc, hb⟩ := term1_body hg.1 (fun _ _ _ h => by rw [ht] at h; cases h)
    rw [ht] at hb
    simp only [body1, Bool.and_eq_true] at hb
    have hp' := hp
    simp only [Accepted1, Bool.and_eq_true] at hp'
    refine ⟨.inl ⟨params1 d, body1_of_decls1 [] p hp'.1.2 d (List.mem_of_find?_eq_some hd)⟩, ?_⟩
    rintro f' hf'
    rcases List.mem_cons.mp hf' with rfl | hf'
    · exact ⟨x :: sc, hb.2⟩
    · exact hg.2 f' hf'
  | @ret c fr fs a t ws ht hσ ha =>
    exact ⟨.inl (hg.2 fr List.mem_cons_self), fun f hf => hg.2 f (List.mem_cons_of_mem _ hf)⟩

/-- **A frame run keeps `Good1`.** -/
theorem good1_run (hp : Accepted1 p = true) {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q')
    (hg : Good1 p q) : Good1 p q' := by
  induction h with
  | refl => exact hg
  | step hs _ ih => exact ih (good1_step hp hs hg)

/-- A `Good1` control is at no buffer allocation. -/
theorem Good1.not_newBuf {q : Ctl × List TermRun.Frame} (h : Good1 p q) :
    ∀ x a τ e, q.1.term ≠ .let_ x (.newBuf a τ) e := by
  intro x a τ e ht
  rcases h.1 with ⟨sc, hb⟩ | ⟨i, a', ts, ht'⟩
  · rw [ht] at hb; simp [body1] at hb
  · rw [ht] at ht'; cases ht'

/-- A `Good1` control is at no box allocation. -/
theorem Good1.not_new {q : Ctl × List TermRun.Frame} (h : Good1 p q) :
    ∀ x a e, q.1.term ≠ .let_ x (.new a) e := by
  intro x a e ht
  rcases h.1 with ⟨sc, hb⟩ | ⟨i, a', ts, ht'⟩
  · rw [ht] at hb; simp [body1] at hb
  · rw [ht] at ht'; cases ht'

/-- A `Good1` control is at no publication (`PubStep`). -/
theorem Good1.noPub {q : Ctl × List TermRun.Frame} (h : Good1 p q) : ∀ k c', ¬ PubStep k q.1 c' :=
  noPub_of_term (fun x a e ht => by
      rcases h.1 with ⟨sc, hb⟩ | ⟨i, a', ts, ht'⟩
      · rw [ht] at hb; simp [body1] at hb
      · rw [ht] at ht'; cases ht')
    fun x r a e ht => by
      rcases h.1 with ⟨sc, hb⟩ | ⟨i, a', ts, ht'⟩
      · rw [ht] at hb; simp [body1] at hb
      · rw [ht] at ht'; cases ht'

/-- A `Good1` control is at no load. -/
theorem Good1.not_load {q : Ctl × List TermRun.Frame} (h : Good1 p q) :
    ∀ x k a e, q.1.term ≠ .let_ x (.load k a) e := by
  intro x k a e ht
  rcases h.1 with ⟨sc, hb⟩ | ⟨i, a', ts, ht'⟩
  · rw [ht] at hb; simp [body1] at hb
  · rw [ht] at ht'; cases ht'

/-- A `Good1` control is at no store. -/
theorem Good1.not_store {q : Ctl × List TermRun.Frame} (h : Good1 p q) :
    ∀ x k a b o e, q.1.term ≠ .let_ x (.store k a b o) e := by
  intro x k a b o e ht
  rcases h.1 with ⟨sc, hb⟩ | ⟨i, a', ts, ht'⟩
  · rw [ht] at hb; simp [body1] at hb
  · rw [ht] at ht'; cases ht'

/-- A frame step leaves no hold. -/
theorem FrameStep.hold_none {q q' : Ctl × List TermRun.Frame} (h : FrameStep p q q') : q'.1.hold = none := by
  cases h with
  | loc hs => exact hs.1
  | call => rfl
  | ret => rfl

/-- A frame run from a control with no hold leaves none. -/
theorem FrameRun.hold_none {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q') (hh : q.1.hold = none) :
    q'.1.hold = none := by
  induction h with
  | refl => exact hh
  | step hs _ ih => exact ih hs.hold_none

/-- **Every control a frame run reaches from a `Good1` pair with no hold is
`Quiet`** (`SegWS.lag`'s `hq`). -/
theorem Good1.quiet_run (hp : Accepted1 p = true) {c c₁ : Ctl} {fs fs₁ : List TermRun.Frame}
    (hg : Good1 p (c, fs)) (hh : c.hold = none) (hr : FrameRun p (c, fs) (c₁, fs₁)) : Quiet c₁ := by
  have hg' := good1_run hp hr hg
  have hh' : c₁.hold = none := hr.hold_none hh
  refine ⟨hh', fun x a e ht => hg'.not_load x true a e ht, fun x a b e ht => hg'.not_store x true a b none e ht,
    hg'.not_newBuf, fun x sa u v e hx => ?_, noPub_of_term (fun x a e ht => ?_) (fun x r a e ht => ?_),
    hg'.not_new⟩
  · obtain ⟨-, ⟨a, t, pw, μ, ht, -⟩ | ⟨b, i, t, pw, ti, iws, μ, sb, k, ht, -⟩⟩ := hx <;>
    · rcases hg'.1 with ⟨sc, hb⟩ | ⟨i', a', ts, ht'⟩
      · rw [ht] at hb; simp [body1] at hb
      · rw [ht] at ht'; cases ht'
  all_goals
    rcases hg'.1 with ⟨sc, hb⟩ | ⟨i', a', ts, ht'⟩
    · rw [ht] at hb; simp [body1] at hb
    · rw [ht] at ht'; cases ht'

end Spike.Lib
