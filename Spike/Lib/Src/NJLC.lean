import Spike.Lib.Src.NJLW

/-!
**`EnvLit` across calls and returns** (ISA-neutral). At a call that passes
`callsOk2` the operand's layout, literals dropped, is the callee's parameter
layout (`argShape`), so the callee's entry environment has `EnvLit` at its
parameters' walk bindings (`EnvLit.entry`); the caller's environment is kept
in the pushed frame with its walk bindings (`FrameLit`). At a `ret` that
passes `callsOk2` the operand's layout is the block's result layout, which
the frame's type is (`FrameStep.call` pushes the callee's `retTy`), so the
caller's environment extended by the result has `EnvLit` at the walk's
binding of the call's result (`opLit`'s `retShape`).

- `EnvLit.evalAt'`: an atom's facts without a symbolic environment;
- `FrameLit`;
- `envLit_call`, `envLit_ret`: the two frame steps of `FrameStep`;
- `retShape_of_find`, `argShape_of_find`: the walk's layouts at a callee;
- `CallLk`: a call's operand at its callee's parameter layout, at a point
  of the literal walk;
- `callsOk2_parts`, `callLk_of`, `call_layout`, `ret_layout`: `callsOk2` at
  the points of a block's walk.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (LitV litAt shapeOf params2 litWalk2 callsOk2 argShape retShape)

/-- **An atom's words keep their layout's facts** (`EnvLit.evalAt` with a
bound on literals instead of a symbolic environment). -/
theorem EnvLit.evalAt' {lits : List (String × LitV)} {env : TermRun.Env} (h : EnvLit lits env) {a : At}
    {t : Ty} {ws : List TermRun.Word} (hsc : InLits lits a) (hlit : ∀ n, a = .lit n → n < 2 ^ 64)
    (he : TermRun.evalAt env a = some (t, ws)) : Compat t (litAt lits a) = true ∧ NumL (litAt lits a) ws := by
  cases a with
  | var x =>
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.1 (hsc x rfl)
    obtain ⟨t0, ws0, he0, hc, hn⟩ := h x L hL
    simp only [TermRun.evalAt, he0, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [litAt, hL, Option.getD_some]
    exact ⟨hc, hn⟩
  | lit n =>
    have hs : Spike.Lib.Form.sevalAt [] (.lit n) = some (.intS (.lit n), [.one (.imm (UInt64.ofNat n))]) := by
      simp [Spike.Lib.Form.sevalAt, hlit n rfl]
    exact h.evalAt hsc hs he
  | unit => exact h.evalAt (s := []) hsc rfl he

/-- **A suspended frame against the walk**: its environment has `EnvLit` at
the walk's bindings `lits` at its call, and its type has its layout. -/
def FrameLit (fr : TermRun.Frame) (lits : List (String × LitV)) : Prop :=
  EnvLit lits fr.env ∧ Compat fr.ty (shapeOf fr.ty) = true

/-- **A call** (`FrameStep.call`): the callee's entry has `EnvLit` at its
parameter's walk binding, and the pushed frame keeps the caller's. -/
theorem envLit_call {lits : List (String × LitV)} {c : Ctl} {x : String} {a : At} {e : Expr} {d : Decl}
    {t : Ty} {ws : List TermRun.Word} (h : EnvLit lits c.env) (hsc : InLits lits a)
    (hlit : ∀ n, a = .lit n → n < 2 ^ 64) (he : TermRun.evalAt c.env a = some (t, ws))
    (hcall : (litAt lits a).erase = shapeOf d.argTy) (hca : Compat d.argTy (shapeOf d.argTy) = true)
    (hcr : Compat d.retTy (shapeOf d.retTy) = true) :
    EnvLit ((params2 d).map (·, shapeOf d.argTy)) [(d.arg, d.argTy, ws)] ∧
      FrameLit ⟨x, e, c.env, [], d.retTy⟩ lits :=
  ⟨EnvLit.entry hca ((h.evalAt' hsc hlit he).2.of_erase hcall), h, hcr⟩

/-- **A return** (`FrameStep.ret`): the caller's environment extended by the
result has `EnvLit` at the walk's binding of the result. -/
theorem envLit_ret {lc lf : List (String × LitV)} {c : Ctl} {fr : TermRun.Frame} {a : At} {t : Ty}
    {ws : List TermRun.Word} (h : EnvLit lc c.env) (hsc : InLits lc a) (hlit : ∀ n, a = .lit n → n < 2 ^ 64)
    (he : TermRun.evalAt c.env a = some (t, ws)) (hret : (litAt lc a).erase = shapeOf fr.ty)
    (hf : FrameLit fr lf) : EnvLit ((fr.x, shapeOf fr.ty) :: lf) ((fr.x, fr.ty, ws) :: fr.env) :=
  hf.1.cons hf.2 ((h.evalAt' hsc hlit he).2.of_erase hret)

/-- **The walk's layout of a call's result** is the callee's declared one. -/
theorem retShape_of_find {p : Prog} {g : String} {d : Decl} (hd : p.find? (·.name == g) = some d) :
    retShape p g = shapeOf d.retTy := by
  simp [retShape, hd]

/-- **A callee's parameter layout** is its declared one. -/
theorem argShape_of_find {p : Prog} {g : String} {d : Decl} (hd : p.find? (·.name == g) = some d) :
    argShape p g = shapeOf d.argTy := by
  simp [argShape, hd]

/-- **`callsOk2` at every point of a block's walk**: a call's operand at its
callee's parameter layout, a `ret`'s at the block's result layout. -/
theorem callsOk2_parts {p : Prog} (h : callsOk2 p = true) {d : Decl} (hd : d ∈ p)
    {q : Expr × List (String × LitV)} (hq : q ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body) :
    (∀ x g is a ts e, q.1 = .let_ x (.call g is a ts) e → (litAt q.2 a).erase = argShape p g) ∧
      (∀ a, q.1 = .ret a → (litAt q.2 a).erase = shapeOf d.retTy) := by
  have hq' := List.all_eq_true.mp (List.all_eq_true.mp h d hd) q hq
  refine ⟨fun x g is a ts e he => ?_, fun a he => ?_⟩
  · rw [he] at hq'; simpa using hq'
  · rw [he] at hq'; simpa using hq'

/-- **The literal walk's fact at a call** (in program `p`): the operand's
layout, literals dropped, the callee's parameter layout (`argShape`; from
`callsOk2`, `callLk_of`). -/
def CallLk (p : Prog) (q : Expr × List (String × LitV)) : Prop :=
  ∀ x g is a ts e, q.1 = .let_ x (.call g is a ts) e → (litAt q.2 a).erase = argShape p g

/-- **`CallLk` at every point of a block's walk** (`callsOk2_parts`). -/
theorem callLk_of {p : Prog} (h : callsOk2 p = true) {d : Decl} (hd : d ∈ p) :
    ∀ q ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body, CallLk p q :=
  fun _ hq => (callsOk2_parts h hd hq).1

/-- **A call at a walk point of an `Accepted2` block** passes `envLit_call`'s
layout premise. -/
theorem call_layout {p : Prog} (h : callsOk2 p = true) {d : Decl} (hd : d ∈ p) {lits : List (String × LitV)}
    {x g : String} {is : List String} {a : At} {ts : List Ty} {e : Expr} {d' : Decl}
    (hq : (.let_ x (.call g is a ts) e, lits) ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body)
    (hf : p.find? (·.name == g) = some d') : (litAt lits a).erase = shapeOf d'.argTy := by
  rw [← argShape_of_find hf]
  exact (callsOk2_parts h hd hq).1 x g is a ts e rfl

/-- **A `ret` at a walk point of an `Accepted2` block** passes `envLit_ret`'s
layout premise, the frame's type the block's result type. -/
theorem ret_layout {p : Prog} (h : callsOk2 p = true) {d : Decl} (hd : d ∈ p) {lits : List (String × LitV)}
    {a : At} (hq : (.ret a, lits) ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body) :
    (litAt lits a).erase = shapeOf d.retTy :=
  (callsOk2_parts h hd hq).2 a rfl

/-- info: 'Spike.Lib.LowerNode.callLk_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms callLk_of

end Spike.Lib.LowerNode
