/-
**The controls of a one-block `Accepted1` program's start are `Quiet`**
(ISA independent), the twin of `Spike/Lib/Quiet0.lean`: every control a
local run reaches from a tail call into `main`, with no hold, has no source
event pending.

- `localStep_let1`: a local step at a `let` of an atom, a `+` or a `-` moves
  to the `let`'s body.
- `localStep_ifeq`: a local step at an `if` moves to one of its branches.
- `quiet_of_body1`: a control at a term of a call-free `Accepted1` body
  (`body1 []`), with no hold, is `Quiet`.
- `quiet_run1`, `quiet_of_accepted1main`: along a local run from a tail call
  into `main`, every control is `Quiet`, when `main`'s body is `body1 [] []`
  (in particular for a one-block `Accepted1` program).
-/
import Spike.Lib.Quiet0
import Scc.Lower.InvProg1

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising
open Scc.Lower (body1 Accepted1)

variable {p : Prog}

/-- The global context of the steps below (any would do). -/
private def gQ1 (p : Prog) : TermRun.G := { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 }

/-- A control at `ret` takes no local step (as `localStep_not_ret`,
`Spike/Lib/SrcRun.lean`, without its imports). -/
private theorem localStep_not_ret1 {c c₁ : Ctl} (h : LocalStep p c c₁) : ∀ a, c.term ≠ .ret a := by
  intro a hc
  have := h.2 (gQ1 p) #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl rfl
  simp [TermRun.tstep, hc] at this

/-- **A local step at a `let` of an atom, a `+` or a `-`** moves to the
`let`'s body. -/
theorem localStep_let1 {c c₁ : Ctl} {x : String} {op : Op} {e : Expr} (h : LocalStep p c c₁)
    (ht : c.term = .let_ x op e) (hop : (∃ a, op = .atom a) ∨ (∃ a b, op = .add a b) ∨ ∃ a b, op = .sub a b) :
    c₁.term = e := by
  have := h.2 (gQ1 p) #[] [] { term := .let_ x op e, env := c.env } rfl ht.symm rfl rfl rfl
  rcases hop with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ <;>
  · simp only [TermRun.tstep, List.map_eq_singleton_iff] at this
    obtain ⟨_, -, hf⟩ := this
    have := congrArg (fun q => q.2.2.term) hf
    simpa [TermRun.withS] using this.symm

/-- **A local step at an `if`** moves to one of its branches. -/
theorem localStep_ifeq {c c₁ : Ctl} {a b : At} {yes no : Expr} (h : LocalStep p c c₁)
    (ht : c.term = .ifeq a b yes no) : c₁.term = yes ∨ c₁.term = no := by
  have := h.2 (gQ1 p) #[] [] { term := .ifeq a b yes no, env := c.env } rfl ht.symm rfl rfl rfl
  simp only [TermRun.tstep] at this
  split at this
  · split at this
    · have := congrArg (fun l => l.head?.map (·.2.2.term)) this
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at this
      split at this <;> simp [← this]
    · have := congrArg (fun l => l.head?.map (·.2.2.term)) this
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at this
      split at this <;> simp [← this]
    · cases this
  · cases this

/-- **A control at a term of a call-free `Accepted1` body**, with no hold,
is `Quiet`. -/
theorem quiet_of_body1 {c : Ctl} {scope : List String} (hb : body1 [] scope c.term = true) (hh : c.hold = none) :
    Quiet c := by
  obtain ⟨t, env, hold⟩ := c
  simp only at hb hh
  refine ⟨hh, ?_, ?_, ?_, fun x sa u v e ⟨_, hx⟩ => ?_, noPub_of_term ?_ ?_, ?_⟩
  · rintro x a e rfl; simp [body1] at hb
  · rintro x a b e rfl; simp [body1] at hb
  · rintro x a τ e rfl; simp [body1] at hb
  · rcases hx with ⟨_, _, _, _, ht, _⟩ | ⟨_, _, _, _, _, _, _, _, _, ht, _⟩ <;>
    · simp only at ht; subst ht; simp [body1] at hb
  · rintro x a e rfl; simp [body1] at hb
  · rintro x r a e rfl; simp [body1] at hb
  · rintro x a _ e rfl; simp [body1] at hb

/-- **Along a local run from a tail call into `main`**, with no hold, every
control is `Quiet`, `main`'s body being `body1 [] []` (`hd`). -/
theorem quiet_run1 (hd : ∀ d, p.find? (·.name == "main") = some d → body1 [] [] d.body = true) {c0 : Ctl}
    {i : List String} {a : At} {ts : List Ty} (ht : c0.term = .tail "main" i a ts) (h0 : c0.hold = none) :
    ∀ c, LocalRun p c0 c → Quiet c := by
  -- the controls reached: `c0`, or one at a `body1 []` term with no hold
  suffices H : ∀ c c', LocalRun p c c' → (c = c0 ∨ (c.hold = none ∧ ∃ sc, body1 [] sc c.term = true)) →
      Quiet c' from fun c hr => H _ _ hr (.inl rfl)
  intro c c' hr
  induction hr with
  | refl c =>
    rintro (rfl | ⟨hh, sc, hb⟩)
    · refine ⟨h0, ?_, ?_, ?_, fun x sa u v e ⟨_, hx⟩ => ?_, noPub_of_term ?_ ?_, ?_⟩
      · intro x a e h; rw [ht] at h; cases h
      · intro x a b e h; rw [ht] at h; cases h
      · intro x a τ e h; rw [ht] at h; cases h
      · rcases hx with ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, _, _, _, h, _⟩ <;> · rw [ht] at h; cases h
      · intro x a e h; rw [ht] at h; cases h
      · intro x r a e h; rw [ht] at h; cases h
      · intro x a _ e h; rw [ht] at h; cases h
    · exact quiet_of_body1 hb hh
  | @step c c₁ c' hs _ ih =>
    rintro (rfl | ⟨hh, sc, hb⟩)
    · cases hf : p.find? (·.name == "main") with
      | none =>
        have := hs.2 (gQ1 p) #[] [] { term := .tail "main" i a ts, env := _ } rfl ht.symm rfl rfl rfl
        simp [TermRun.tstep, TermRun.enter, TermRun.ol, gQ1, hf] at this
      | some d => exact ih (.inr ⟨hs.1, [], localStep_tail hs ht hf ▸ hd d hf⟩)
    · refine ih (.inr ⟨hs.1, ?_⟩)
      cases hc : c.term with
      | let_ x op e =>
        rw [hc] at hb
        cases op <;> simp only [body1, Scc.Lower.callee1, Bool.and_eq_true, Bool.false_eq_true] at hb
        case atom a => exact ⟨x :: sc, localStep_let1 hs hc (.inl ⟨a, rfl⟩) ▸ hb.2⟩
        case add a b => exact ⟨x :: sc, localStep_let1 hs hc (.inr (.inl ⟨a, b, rfl⟩)) ▸ hb.2⟩
        case sub a b => exact ⟨x :: sc, localStep_let1 hs hc (.inr (.inr ⟨a, b, rfl⟩)) ▸ hb.2⟩
        all_goals simp at hb
      | ifeq a b yes no =>
        rw [hc] at hb
        simp only [body1, Bool.and_eq_true] at hb
        rcases localStep_ifeq hs hc with h | h
        · exact ⟨sc, h ▸ hb.1.2⟩
        · exact ⟨sc, h ▸ hb.2⟩
      | ret a => exact absurd hc (localStep_not_ret1 hs a)
      | _ => rw [hc] at hb; simp [body1] at hb

/-- **The controls of a one-block `Accepted1` program's start are
`Quiet`**: along a local run from a tail call into `main` with no hold. -/
theorem quiet_of_accepted1main {d : Decl} (hp : Accepted1 [d] = true) {c0 : Ctl} {i : List String} {a : At}
    {ts : List Ty} (ht : c0.term = .tail "main" i a ts) (h0 : c0.hold = none) :
    ∀ c, LocalRun [d] c0 c → Quiet c := by
  obtain ⟨hn, -, -, -, -, -, hb⟩ := Scc.Lower.Inv.accepted1_main hp
  refine quiet_run1 (fun d' hd' => ?_) ht h0
  simp only [List.find?, hn, beq_self_eq_true, Option.some.injEq] at hd'
  exact hd' ▸ hb

end Spike.Lib
