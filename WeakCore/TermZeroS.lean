import WeakCore.CoreLang
import Lean

/-! # TermZeroS: a structurally recursive restatement of `zeroableIn`

`CoreLang.zeroableIn` and `CoreLang.zeroArmP` are mutually recursive by well-founded recursion
(`zeroArmP`'s fallback calls `zeroableIn` at the same type), so the kernel cannot evaluate them:
`decide +kernel` gets stuck on any closed instance.  `zeroPair` computes both at once by
structural recursion on the type, and `zeroableIn_eq` proves it equal to the original, so a
closed goal mentioning `zeroableIn` can be rewritten into a kernel-reducible one.

The tactic `zero_decide` does that for a closed Boolean goal `e = true`: `delta_reach zeroableIn`
delta-expands every constant of the goal whose definition reaches `zeroableIn` (a definitional
change), `rw [zeroableIn_eq]` replaces `zeroableIn` by `zeroPair`, and `decide +kernel` evaluates
the result.  The kernel checks all three steps; no new axiom.
-/

namespace TermZeroS

open CoreLang

/-- Both `zeroableIn · · t` and `zeroArmP · · · t`, by structural recursion on `t`. -/
def zeroPair : Ty → (IEnv → KEnv → Bool) × ((Ty → Bool) → IEnv → KEnv → Option Bool)
  | .unit => let z := fun _ _ => true; (z, fun sel env ke => if sel .unit then some (z env ke) else none)
  | .void => (fun _ _ => false, fun _ _ _ => none)
  | .int => let z := fun _ _ => true; (z, fun sel env ke => if sel .int then some (z env ke) else none)
  | .intS i => let z := fun env _ => i.evalIn env == some 0
      (z, fun sel env ke => if sel (.intS i) then some (z env ke) else none)
  | .fix sg w => let z := fun _ _ => true
      (z, fun sel env ke => if sel (.fix sg w) then some (z env ke) else none)
  | .lanes sg w => let z := fun _ _ => true
      (z, fun sel env ke => if sel (.lanes sg w) then some (z env ke) else none)
  | .prod a b => let z := fun env ke => (zeroPair a).1 env ke && (zeroPair b).1 env ke
      (z, fun sel env ke => if sel (.prod a b) then some (z env ke) else none)
  | .sum a b =>
      let z := fun env ke =>
        match (Ty.sum a b).tier with
        | .niche => ((zeroPair a).2 Ty.payloadFree env ke <|> (zeroPair b).2 Ty.payloadFree env ke) == some true
        | .wide  => ((zeroPair a).2 (fun _ => true) env ke <|> (zeroPair b).2 (fun _ => true) env ke) == some true
        | .boxed => false
      (z, fun sel env ke => (zeroPair a).2 sel env ke <|> (zeroPair b).2 sel env ke)
  | .code a b => let z := fun _ _ => false
      (z, fun sel env ke => if sel (.code a b) then some (z env ke) else none)
  | .tid => let z := fun _ _ => false
      (z, fun sel env ke => if sel .tid then some (z env ke) else none)
  | .array i t => let z := fun env ke => (zeroPair t).1 env ke
      (z, fun sel env ke => if sel (.array i t) then some (z env ke) else none)
  | .ptr μ t => let z := fun _ _ => false
      (z, fun sel env ke => if sel (.ptr μ t) then some (z env ke) else none)
  | .ptrOpt μ t => let z := fun _ _ => true
      (z, fun sel env ke => if sel (.ptrOpt μ t) then some (z env ke) else none)
  | .loc μ t =>
      let z := fun env (_ : KEnv) => match t with
        | .array i _ => i.evalIn env == some 0
        | _ => false
      (z, fun sel env ke => if sel (.loc μ t) then some (z env ke) else none)
  | .share r => let z := fun _ _ => false
      (z, fun sel env ke => if sel (.share r) then some (z env ke) else none)
  | .cap s r => let z := fun _ _ => false
      (z, fun sel env ke => if sel (.cap s r) then some (z env ke) else none)
  | .word r P => let z := fun _ _ => false
      (z, fun sel env ke => if sel (.word r P) then some (z env ke) else none)
  | .tok r st => let z := fun _ _ => false
      (z, fun sel env ke => if sel (.tok r st) then some (z env ke) else none)
  | .word2 r P => let z := fun _ _ => false
      (z, fun sel env ke => if sel (.word2 r P) then some (z env ke) else none)
  | .tok2 r P i0 i1 => let z := fun _ _ => false
      (z, fun sel env ke => if sel (.tok2 r P i0 i1) then some (z env ke) else none)
  | .epair r P => let z := fun _ _ => false
      (z, fun sel env ke => if sel (.epair r P) then some (z env ke) else none)
  | .tokE r P e => let z := fun _ _ => false
      (z, fun sel env ke => if sel (.tokE r P e) then some (z env ke) else none)
  | .tvar k => let z := fun _ ke => ke.ask k false (·.zero)
      (z, fun sel env ke => if sel (.tvar k) then some (z env ke) else none)
  | .mu t => (fun env ke => (zeroPair t).1 env (none :: ke),
              fun sel env ke => (zeroPair t).2 sel env (none :: ke))
  | .tex _ t => (fun _ _ => false,
                 fun sel env ke => ((zeroPair t).2 sel env (none :: ke)).map fun _ => false)
  | .iall t => (fun env ke => (zeroPair t).1 (none :: env) ke,
                fun sel env ke => (zeroPair t).2 sel (none :: env) ke)
  | .iex t => (fun env ke => (zeroPair t).1 (some 0 :: env) ke,
               fun sel env ke => (zeroPair t).2 sel (some 0 :: env) ke)
  | .refine t ψ => (fun env ke => (zeroPair t).1 env ke && ψ.zeroHolds env,
                    fun sel env ke => ((zeroPair t).2 sel env ke).map (· && ψ.zeroHolds env))

/-- `zeroPair` computes `zeroableIn` and `zeroArmP`. -/
theorem zeroPair_spec (t : Ty) :
    (∀ env ke, zeroableIn env ke t = (zeroPair t).1 env ke) ∧
    (∀ sel env ke, zeroArmP sel env ke t = (zeroPair t).2 sel env ke) := by
  induction t with
  | prod a b iha ihb =>
      refine ⟨fun env ke => ?_, fun sel env ke => ?_⟩
      · rw [zeroableIn, iha.1, ihb.1]; rfl
      · rw [zeroArmP, zeroableIn, iha.1, ihb.1] <;> first | rfl | (intros; contradiction)
  | sum a b iha ihb =>
      refine ⟨fun env ke => ?_, fun sel env ke => ?_⟩
      · rw [zeroableIn, iha.2, iha.2, ihb.2, ihb.2]; rfl
      · rw [zeroArmP, iha.2, ihb.2]; rfl
  | array i t ih =>
      refine ⟨fun env ke => ?_, fun sel env ke => ?_⟩
      · rw [zeroableIn, ih.1]; rfl
      · rw [zeroArmP, zeroableIn, ih.1] <;> first | rfl | (intros; contradiction)
  | loc μ t _ =>
      refine ⟨fun env ke => ?_, fun sel env ke => ?_⟩
      · cases t <;> rw [zeroableIn] <;> first | rfl | (intros; contradiction)
      · cases t <;> rw [zeroArmP, zeroableIn] <;> first | rfl | (intros; contradiction)
  | mu t ih =>
      refine ⟨fun env ke => ?_, fun sel env ke => ?_⟩
      · rw [zeroableIn, ih.1]; rfl
      · rw [zeroArmP, ih.2]; rfl
  | tex κ t ih =>
      refine ⟨fun env ke => ?_, fun sel env ke => ?_⟩
      · rw [zeroableIn]; rfl
      · rw [zeroArmP, ih.2]; rfl
  | iall t ih =>
      refine ⟨fun env ke => ?_, fun sel env ke => ?_⟩
      · rw [zeroableIn, ih.1]; rfl
      · rw [zeroArmP, ih.2]; rfl
  | iex t ih =>
      refine ⟨fun env ke => ?_, fun sel env ke => ?_⟩
      · rw [zeroableIn, ih.1]; rfl
      · rw [zeroArmP, ih.2]; rfl
  | refine t ψ ih =>
      refine ⟨fun env ke => ?_, fun sel env ke => ?_⟩
      · rw [zeroableIn, ih.1]; rfl
      · rw [zeroArmP, ih.2]; rfl
  | void => exact ⟨fun env ke => by rw [zeroableIn]; rfl, fun sel env ke => by rw [zeroArmP]; rfl⟩
  | _ =>
      refine ⟨fun env ke => ?_, fun sel env ke => ?_⟩
      · rw [zeroableIn] <;> first | rfl | (intros; contradiction)
      · rw [zeroArmP, zeroableIn] <;> first | rfl | (intros; contradiction)

/-- **`zeroableIn` is `zeroPair`'s first component.** -/
theorem zeroableIn_eq : zeroableIn = fun env ke t => (zeroPair t).1 env ke := by
  funext env ke t; exact (zeroPair_spec t).1 env ke

open Lean Meta Elab Tactic

/-- Does `n`'s definition reach `tgt` (depth-bounded by `fuel`; unknown counts as no)?  Memoized. -/
def reachesGo (env : Environment) (tgt : Name) :
    Nat → Name → Std.HashMap Name Bool → NameSet → Bool × Std.HashMap Name Bool
  | 0, _, memo, _ => (false, memo)
  | fuel + 1, n, memo, stack =>
    if n == tgt then (true, memo) else
    match memo.get? n with
    | some b => (b, memo)
    | none =>
      if stack.contains n then (false, memo) else
      match env.find? n with
      | some (.defnInfo d) => Id.run do
          let mut m := memo
          let mut r := false
          for c in d.value.getUsedConstants do
            let (b, m') := reachesGo env tgt fuel c m (stack.insert n)
            m := m'
            r := r || b
          return (r, m.insert n r)
      | _ => (false, memo.insert n false)

/-- The constants reachable from `roots` whose definition (transitively) mentions `tgt`. -/
def reachesSet (env : Environment) (tgt : Name) (roots : List Name) : NameSet := Id.run do
  let mut memo : Std.HashMap Name Bool := {}
  for r in roots do
    memo := (reachesGo env tgt 10000 r memo {}).2
  let mut out : NameSet := {}
  for (n, b) in memo.toList do
    if b then out := out.insert n
  return out

/-- Delta-expand, to a fixpoint, every constant of the goal whose definition reaches `tgt`. -/
elab "delta_reach " tgt:ident : tactic => do
  let tgtN ← realizeGlobalConstNoOverload tgt
  let env ← getEnv
  let g ← getMainGoal
  let mut ty ← instantiateMVars (← g.getType)
  let roots := ty.getUsedConstants.toList
  let R := reachesSet env tgtN roots
  let R := R.erase tgtN
  let mut i : Nat := 0
  while ty.getUsedConstants.any R.contains do
    ty ← deltaExpand ty R.contains
    i := i + 1
    if i > 200 then throwError "delta_reach: no fixpoint"
  replaceMainGoal [← g.replaceTargetDefEq ty]

/-- `delta_reach zeroableIn`, `rw [zeroableIn_eq]`, `decide +kernel`. -/
macro "zero_decide" : tactic =>
  `(tactic| (delta_reach CoreLang.zeroableIn; rw [TermZeroS.zeroableIn_eq]; decide +kernel))

end TermZeroS

#print axioms TermZeroS.zeroPair_spec
#print axioms TermZeroS.zeroableIn_eq
