/-
**main's source control after the spawn** (`post_step0`; terms in `Spike/Lib/WakeM0.lean`). The thread-0 twin of
`Spike/Lib/WakeW1Src.lean`'s `WCtl`.

main's source runs `mTail` (the tail call of `waitLoop`), `wlBody` (the
acquire load of `c`), `wlIf` (the test of the flag), `wlPark` (the park and
the tail call) and `wlRet`. A local step at a `let` binds one fresh name in
front of the environment, so `c`'s binding survives every local step; the
tail call rebinds `c` to the same word.

- `MCtl cw c`: main's control invariant (no hold, an `MTerm`, `EnvC cw`).
- `localStep_let`, `localStep_ifeq`: where a local step at a `let` of a
  non-call / at an `ifeq` moves, and its environment.
- `localStep_mTail`: a local step at `mTail` enters `waitLoop`'s body with
  `c` bound to the same word.
- `localStep_mCtl`, `localRun_mCtl`: a local step / run keeps `MCtl`.
-/
import Spike.Lib.WakeM0
import Spike.Lib.SrcFrames
import Spike.Lib.SrcRun

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm TermRun
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1
open Spike.Lib.WakeMLive (wlRet)

/-! ## The control invariant -/

/-- **main's control invariant after the spawn**: no hold, an `MTerm`, `c`
bound to the pointer word `cw`. -/
structure MCtl (cw : Word) (c : Ctl) : Prop where
  hold : c.hold = none
  term : MTerm c.term
  env : EnvC cw c.env

/-- The global context of the inversions below (any would do). -/
private def gM : G := { p := wakeSrc, k := Promises.Knobs.all, arch := .arm, n := 2, i := 0, lbase := 0 }

/-! ## Where a local step moves -/

variable {p : Prog}

/-- **A local step at a `let` of anything but a call** moves to the `let`'s
body, with one binding of `x` pushed on the environment. -/
theorem localStep_let {c c' : Ctl} (h : LocalStep p c c') {x : String} {op : Op} {e : Expr}
    (ht : c.term = .let_ x op e) (hc : ∀ f is a ts, op ≠ .call f is a ts) (hcc : ∀ f a, op ≠ .callc f a) :
    c'.term = e ∧ ∃ t ws, c'.env = (x, t, ws) :: c.env := by
  have := h.2 { gM with p := p } #[] [] { term := .let_ x op e, env := c.env } rfl ht.symm rfl rfl rfl
  cases op
  case call f is a ts => exact (hc f is a ts rfl).elim
  case callc f a => exact (hcc f a rfl).elim
  all_goals
    simp only [TermRun.tstep, List.map_eq_singleton_iff] at this
    obtain ⟨⟨_, t, ws⟩, -, hf⟩ := this
    try split at hf
    all_goals
      have e1 := congrArg (fun q => q.2.2.term) hf
      have e2 := congrArg (fun q => q.2.2.env) hf
      simp only [TermRun.withS] at e1 e2
      exact ⟨e1.symm, t, ws, e2.symm⟩

/-- **A local step at an `ifeq`** keeps the environment and moves to one of
the two branches. -/
theorem localStep_ifeq {c c' : Ctl} (h : LocalStep p c c') {a b : At} {yes no : Expr}
    (ht : c.term = .ifeq a b yes no) : (c'.term = yes ∨ c'.term = no) ∧ c'.env = c.env := by
  have := h.2 { gM with p := p } #[] [] { term := .ifeq a b yes no, env := c.env } rfl ht.symm rfl rfl rfl
  simp only [TermRun.tstep] at this
  repeat' split at this
  all_goals first
    | cases this
    | (simp only [List.cons.injEq, Prod.mk.injEq, and_true] at this
       have e1 := congrArg TTh.term this.2.2
       have e2 := congrArg TTh.env this.2.2
       simp only at e1 e2
       exact ⟨by simp [← e1], e2.symm⟩)

/-- `EnvC` survives a binding of another name. -/
theorem envC_cons {cw : Word} {env : Env} (h : EnvC cw env) {x : String} (hx : x ≠ "c") (t : Ty)
    (ws : List Word) : EnvC cw ((x, t, ws) :: env) := by
  obtain ⟨t', μ, u, hev, hcell, hu⟩ := h
  refine ⟨t', μ, u, ?_, hcell, hu⟩
  have hb : (x == "c") = false := by simpa using hx
  simpa [evalAt, lookupE, List.find?, hb] using hev

/-- **A local step at `mTail`** enters `waitLoop`'s body with `c` bound to
the same word. -/
theorem localStep_mTail {cw : Word} {c c' : Ctl} (h : LocalStep wakeSrc c c') (ht : c.term = mTail)
    (he : EnvC cw c.env) : c'.term = wlBody ∧ EnvC cw c'.env := by
  obtain ⟨t, μ, u, hev, -, -⟩ := he
  have e := tstep_tail (g := gM) (mem := #[]) (pairs := []) (th := { term := c.term, env := c.env })
    (by rw [ht]; rfl) rfl rfl hev
  have := h.2 gM #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl rfl
  rw [e] at this
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at this
  have e1 := congrArg TTh.term this.2.2
  have e2 := congrArg TTh.env this.2.2
  simp only [close_nil, List.reverse_nil] at e1 e2
  refine ⟨e1.symm, ?_⟩
  rw [← e2]
  exact ⟨.ptr .pub .int, .pub, .int, rfl, rfl, rfl⟩

/-! ## The invariant is kept -/

/-- **A local step keeps main's control invariant**: `mTail` to `wlBody`,
`wlBody` to `wlIf`, `wlIf` to `wlRet` or `wlPark`, `wlPark` to `mTail`;
none at `wlRet`. -/
theorem localStep_mCtl {cw : Word} {c c' : Ctl} (h : LocalStep wakeSrc c c') (hc : MCtl cw c) : MCtl cw c' := by
  rcases hc.term with ht | ht | ht | ht | ht
  · obtain ⟨e1, he⟩ := localStep_mTail h ht hc.env
    exact ⟨h.1, .inr (.inl e1), he⟩
  · obtain ⟨e1, t, ws, e2⟩ := localStep_let h (ht.trans rfl) (by intros; simp) (by intros; simp)
    exact ⟨h.1, .inr (.inr (.inl e1)), e2 ▸ envC_cons hc.env (by decide) t ws⟩
  · obtain ⟨e1, e2⟩ := localStep_ifeq h (ht.trans rfl)
    refine ⟨h.1, ?_, e2 ▸ hc.env⟩
    rcases e1 with e1 | e1
    · exact .inr (.inr (.inr (.inr e1)))
    · exact .inr (.inr (.inr (.inl e1)))
  · obtain ⟨e1, t, ws, e2⟩ := localStep_let h (ht.trans rfl) (by intros; simp) (by intros; simp)
    exact ⟨h.1, .inl e1, e2 ▸ envC_cons hc.env (by decide) t ws⟩
  · exact (localStep_not_ret h (.lit 0) ht).elim

/-- **A local run keeps main's control invariant.** -/
theorem localRun_mCtl {cw : Word} {c c' : Ctl} (h : LocalRun wakeSrc c c') (hc : MCtl cw c) : MCtl cw c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (localStep_mCtl hs hc)

/-- info: 'Spike.Lib.WakeM0.localRun_mCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms localRun_mCtl

end Spike.Lib.WakeM0
