/-
**The controls of an `Accepted0` program's start are `Quiet`** (ISA
independent): every control a local run reaches from a tail call into
`main`, with no hold, has no source event pending. This discharges the
`hQ` premise of a lowered body's blocks (`Spike/Lib/LowerA64/BodyW.lean`)
and of its x86-64 counterpart.

- `localStep_let`: a local step at a `let` of an atom or a `+` moves to the
  `let`'s body.
- `localStep_tail`: a local step at a tail call into `main` moves to
  `main`'s body.
- `quiet_of_body0`: a control at a term of an `Accepted0` body (`body0`),
  with no hold, is `Quiet`.
- `quiet_run`, `quiet_of_accepted0`: along a local run from a tail call into
  `main`, every control is `Quiet`, when `main`'s body is `body0` (in
  particular for an `Accepted0` program).
-/
import Spike.Lib.SegLag
import Scc.Lower.Spec

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising
open Scc.Lower (body0 Accepted0)

variable {p : Prog}

/-- The global context of the steps below (any would do). -/
private def gQ (p : Prog) : TermRun.G := { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 }

/-- A control at `ret` takes no local step (as `localStep_not_ret`,
`Spike/Lib/SrcRun.lean`, without its imports). -/
private theorem localStep_not_ret' {c c₁ : Ctl} (h : LocalStep p c c₁) : ∀ a, c.term ≠ .ret a := by
  intro a hc
  have := h.2 (gQ p) #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl rfl
  simp [TermRun.tstep, hc] at this

/-- **A local step at a `let` of an atom or a `+`** moves to the `let`'s
body. -/
theorem localStep_let {c c₁ : Ctl} {x : String} {op : Op} {e : Expr} (h : LocalStep p c c₁)
    (ht : c.term = .let_ x op e) (hop : (∃ a, op = .atom a) ∨ ∃ a b, op = .add a b) : c₁.term = e := by
  have := h.2 (gQ p) #[] [] { term := .let_ x op e, env := c.env } rfl ht.symm rfl rfl rfl
  rcases hop with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;>
  · simp only [TermRun.tstep, List.map_eq_singleton_iff] at this
    obtain ⟨_, -, hf⟩ := this
    have := congrArg (fun q => q.2.2.term) hf
    simpa [TermRun.withS] using this.symm

/-- **A local step at a tail call into `main`** moves to `main`'s body. -/
theorem localStep_tail {c c₁ : Ctl} {i : List String} {a : At} {ts : List Ty} {d : Decl} (h : LocalStep p c c₁)
    (ht : c.term = .tail "main" i a ts) (hd : p.find? (·.name == "main") = some d) : c₁.term = d.body := by
  have := h.2 (gQ p) #[] [] { term := .tail "main" i a ts, env := c.env } rfl ht.symm rfl rfl rfl
  simp only [TermRun.tstep, TermRun.enter, TermRun.ol, gQ, hd] at this
  cases hv : TermRun.evalAt c.env a with
  | none => simp [hv] at this
  | some v =>
    have := congrArg (fun l => l.head?.map (·.2.2.term)) this
    simpa [hv] using this.symm

/-- **A control at a term of an `Accepted0` body**, with no hold, is
`Quiet`. -/
theorem quiet_of_body0 {c : Ctl} {scope : List String} (hb : body0 scope c.term = true) (hh : c.hold = none) :
    Quiet c := by
  obtain ⟨t, env, hold⟩ := c
  simp only at hb hh
  refine ⟨hh, ?_, ?_, ?_, fun x sa u v e ⟨_, hx⟩ => ?_⟩
  · rintro x a e rfl; simp [body0] at hb
  · rintro x a b e rfl; simp [body0] at hb
  · rintro x a τ e rfl; simp [body0] at hb
  · rcases hx with ⟨_, _, _, _, ht, _⟩ | ⟨_, _, _, _, _, _, _, _, _, ht, _⟩ <;>
    · simp only at ht; subst ht; simp [body0] at hb

/-- **Along a local run from a tail call into `main`**, with no hold, every
control is `Quiet`, `main`'s body being `body0` (`hd`). -/
theorem quiet_run (hd : ∀ d, p.find? (·.name == "main") = some d → body0 [] d.body = true) {c0 : Ctl}
    {i : List String} {a : At} {ts : List Ty} (ht : c0.term = .tail "main" i a ts) (h0 : c0.hold = none) :
    ∀ c, LocalRun p c0 c → Quiet c := by
  -- the controls reached: `c0`, or one at a `body0` term with no hold
  suffices H : ∀ c c', LocalRun p c c' → (c = c0 ∨ (c.hold = none ∧ ∃ sc, body0 sc c.term = true)) →
      Quiet c' from fun c hr => H _ _ hr (.inl rfl)
  intro c c' hr
  induction hr with
  | refl c =>
    rintro (rfl | ⟨hh, sc, hb⟩)
    · refine ⟨h0, ?_, ?_, ?_, fun x sa u v e ⟨_, hx⟩ => ?_⟩
      · intro x a e h; rw [ht] at h; cases h
      · intro x a b e h; rw [ht] at h; cases h
      · intro x a τ e h; rw [ht] at h; cases h
      · rcases hx with ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, _, _, _, h, _⟩ <;> · rw [ht] at h; cases h
    · exact quiet_of_body0 hb hh
  | @step c c₁ c' hs _ ih =>
    rintro (rfl | ⟨hh, sc, hb⟩)
    · cases hf : p.find? (·.name == "main") with
      | none =>
        have := hs.2 (gQ p) #[] [] { term := .tail "main" i a ts, env := _ } rfl ht.symm rfl rfl rfl
        simp [TermRun.tstep, TermRun.enter, TermRun.ol, gQ, hf] at this
      | some d => exact ih (.inr ⟨hs.1, [], localStep_tail hs ht hf ▸ hd d hf⟩)
    · refine ih (.inr ⟨hs.1, ?_⟩)
      cases hc : c.term with
      | let_ x op e =>
        rw [hc] at hb
        cases op <;> simp only [body0, Bool.and_eq_true, Bool.false_eq_true] at hb
        case atom a => exact ⟨x :: sc, localStep_let hs hc (.inl ⟨a, rfl⟩) ▸ hb.2⟩
        case add a b => exact ⟨x :: sc, localStep_let hs hc (.inr ⟨a, b, rfl⟩) ▸ hb.2⟩
      | ret a => exact absurd hc (localStep_not_ret' hs a)
      | _ => rw [hc] at hb; simp [body0] at hb

/-- **The controls of an `Accepted0` program's start are `Quiet`**: along a
local run from a tail call into `main` with no hold. -/
theorem quiet_of_accepted0 (hp : Accepted0 p = true) {c0 : Ctl} {i : List String} {a : At} {ts : List Ty}
    (ht : c0.term = .tail "main" i a ts) (h0 : c0.hold = none) : ∀ c, LocalRun p c0 c → Quiet c := by
  refine quiet_run (fun d hd => ?_) ht h0
  match p, hp with
  | [d'], hp =>
    simp only [Accepted0, Bool.and_eq_true, beq_iff_eq] at hp
    simp only [List.find?, hp.1.1.1.1.1.1, beq_self_eq_true, Option.some.injEq] at hd
    exact hd ▸ hp.1.2

end Spike.Lib
