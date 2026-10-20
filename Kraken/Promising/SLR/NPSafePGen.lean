/-
The existing names of the Theorem 1′ chain as instances of the generic chain.

The chain (`SLR/Theorem1Run.lean` … `SLR/Theorem1Final.lean`) is generic in
the prepay guard `G` (`NPSafeP`, `RelFulfilled'`, `PromisePure'`), the
virtual guard `GV` (`Status'`, `Config.VirtualOfG`) and the K2 frame `K`
(`MicroStep'`); its declarations carry a prime. Every existing name keeps its
statement and is the instance at `G₀`, `GRF`, `K2₀`. The tactic `npgen X'`
proves such an instance from its generic version `X'`:

- the generic binders named `G`, `GV`, `K`, `KF` are set to `G₀`, `GRF`,
  `K2₀ (model I)`, and the step guard `S` to
  `StepGuard.top (model I)`, the erasure `Er` and the obligation `Ob` to `Erase` and `ObPure`; those named `ErOK` to
  `chainExt_Erase`, and those named `GOK`, `GVOK`, `hGV`, `KOK` to `guardOK_G₀`,
  `guardOK_GRF`, `G₀_le_GRF`, `k2OK_K2₀`;
- every other binder is matched by name with a hypothesis of the goal (the
  existing statement and the generic one use the same binder names), or by
  instance synthesis;
- the conclusion is unified with the goal.

`NPSafe` and `NPSafeP` are irreducible (well-founded); the unification runs
with them unsealed (`NPSafeP_G₀_K₀` is `rfl` then).
-/
import Lean
import Kraken.Promising.SLR.NPSafeP

namespace Kraken.Promising.SLR

open Lean Meta Elab Tactic

/-- Close an existing statement of the Theorem 1′ chain from its generic
(primed) version, at `G₀`, `GRF`, `K2₀` (see the module docstring). -/
elab "npgen " id:ident : tactic => withMainContext do
  let goal ← getMainGoal
  let tgt ← goal.getType
  let c ← realizeGlobalConstNoOverloadWithInfo id
  let e ← mkConstWithFreshMVarLevels c
  let ety ← inferType e
  let rec binderNames : Expr → List Name
    | .forallE n _ b _ => n :: binderNames b
    | _ => []
  -- the goal's own leading `∀`s match the generic conclusion's
  let nArgs := (binderNames ety).length - (binderNames tgt).length
  let (ms, bis, concl) ← forallMetaBoundedTelescope ety nArgs
  let names := ((binderNames ety).take nArgs).toArray
  let lctx ← getLCtx
  let assignTerm (m : Expr) (stx : Term) : TermElabM Unit := do
    let v ← Term.elabTermEnsuringType stx (← inferType m)
    Term.synthesizeSyntheticMVarsNoPostponing
    unless ← isDefEq m v do throwError "npgen: cannot assign {stx}"
  withTransparency .all do
    -- guards and frame
    for m in ms, n in names do
      match n with
      | `G => assignTerm m (← `(G₀))
      | `GV => assignTerm m (← `(GRF))
      | `K | `KF => assignTerm m (← `(K2₀ (model _)))
      | `Er => assignTerm m (← `(Erase))
      | `Ob => assignTerm m (mkIdent `ObPure)
      | `S => assignTerm m (← `(StepGuard.top (model _)))
      | _ => pure ()
    -- the remaining binders by name
    for m in ms, n in names, bi in bis do
      if ← m.mvarId!.isAssigned then continue
      match n with
      | `GOK => assignTerm m (← `(guardOK_G₀))
      | `GVOK => assignTerm m (← `(guardOK_GRF))
      | `hGV => assignTerm m (← `(fun _ _ _ _ _ h => G₀_le_GRF h))
      | `KOK => assignTerm m (← `(k2OK_K2₀ _))
      | `ErOK => assignTerm m (mkIdent `chainExt_Erase)
      | _ =>
        if bi.isInstImplicit then continue
        match lctx.findFromUserName? n with
        | some d =>
          unless ← isDefEq m d.toExpr do
            throwError "npgen: hypothesis {n} does not match{indentExpr (← inferType m)}"
        | none => pure ()
    unless ← isDefEq concl tgt do
      throwError "npgen: conclusion{indentExpr concl}\ndoes not match{indentExpr tgt}"
    for m in ms, bi in bis do
      if ← m.mvarId!.isAssigned then continue
      if bi.isInstImplicit then
        m.mvarId!.assign (← synthInstance (← inferType m))
    let pf ← instantiateMVars (mkAppN e ms)
    if pf.hasExprMVar then
      throwError "npgen: unassigned arguments in{indentExpr pf}"
    goal.assign pf
  replaceMainGoal []

end Kraken.Promising.SLR
