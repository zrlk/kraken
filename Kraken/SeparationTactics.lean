import Kraken.Separation
import Lean.Elab.Tactic
import Lean.Meta.Tactic.AC

open Lean Elab Tactic Meta

namespace Kraken.Tactic

private partial def denoteClauses (predType : Expr) : List Expr → MetaM Expr
  | [] => withLocalDeclD `m predType.bindingDomain! fun m => do
      let body ← mkAppM ``Std.ExtHashMap.emp #[m]
      mkLambdaFVars #[m] body (etaReduce := true)
  | p :: ps => do
    let rest ← denoteClauses predType ps
    mkAppM ``Std.ExtHashMap.sep #[p, rest]

private partial def reifyClauses (e : Expr) : MetaM (List Expr) := do
  let e ← instantiateMVars e
  if e.getAppFn.constName? == some ``Std.ExtHashMap.emp then
    return []
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let p ← reifyClauses args[args.size - 2]!
    let q ← reifyClauses args[args.size - 1]!
    return p ++ q
  return [e]

-- A "naked" metavariable may also be applied to bound variables (`?R v`, e.g.
-- when the frame is elaborated under a binder); `isDefEq` then performs
-- higher-order pattern unification.
private def isNakedMVar (e : Expr) : Bool :=
  e.getAppFn.isMVar && e.getAppArgs.all (·.isFVar)

private def assignNaked (predType : Expr) (lhs rhs : List Expr) : MetaM Bool := do
  let [l] := lhs | return false
  unless isNakedMVar l do return false
  isDefEq l (← denoteClauses predType rhs)

private def reduceProjectionApp (e : Expr) : MetaM Expr := do
  let some declName := e.getAppFn.constName? | return e
  let some info ← getProjectionFnInfo? declName | return e
  if info.fromClass then return e
  let some unfolded ← unfoldDefinition? e | return e
  let some fn ← reduceProj? unfolded.getAppFn | return e
  return mkAppN fn unfolded.getAppArgs

-- fuel: bound definitional unfolding to avoid expensive general reduction.
private partial def matchClosed (lhs rhs : Expr) (fuel : Nat := 2) : MetaM Bool := do
  let lhs ← reduceProjectionApp lhs
  let rhs ← reduceProjectionApp rhs
  if lhs == rhs then return true
  if lhs.getAppFn == rhs.getAppFn then
    let lhsArgs := lhs.getAppArgs
    let rhsArgs := rhs.getAppArgs
    unless lhsArgs.size == rhsArgs.size do return false
    for lhsArg in lhsArgs, rhsArg in rhsArgs do
      unless ← matchClosed lhsArg rhsArg fuel do return false
    return true
  if fuel == 0 then return false
  if let some lhs ← unfoldDefinition? lhs then
    if ← matchClosed lhs rhs (fuel - 1) then return true
  if let some rhs ← unfoldDefinition? rhs then
    if ← matchClosed lhs rhs (fuel - 1) then return true
  return false

-- Matching with metavariables. A failed match against the wrong clause must fail
-- fast: plain `isDefEq` at default transparency may unfold both sides arbitrarily
-- deep (e.g. `Int.toBytes 16 ?v =?= List.take n m`). So we unify at `instances`
-- transparency, descending into applications with the same head, and only allow a
-- bounded number of definition unfoldings (e.g. `UInt64.At v a ~~> v.toBytes.At a`).
private partial def matchWithMVars (lhs rhs : Expr) (fuel : Nat := 2) : MetaM Bool := do
  if ← withTransparency .instances (isDefEq lhs rhs) then return true
  if lhs.getAppFn == rhs.getAppFn && lhs.getAppNumArgs == rhs.getAppNumArgs then
    let ok ← commitWhen do
      for a in lhs.getAppArgs, b in rhs.getAppArgs do
        unless ← matchWithMVars (← instantiateMVars a) (← instantiateMVars b) fuel do
          return false
      return true
    if ok then return true
  if fuel == 0 then return false
  if let some rhs' ← unfoldDefinition? rhs then
    if ← matchWithMVars lhs rhs' (fuel - 1) then return true
  if let some lhs' ← unfoldDefinition? lhs then
    if ← matchWithMVars lhs' rhs (fuel - 1) then return true
  return false

private def matchAtom (lhs rhs : Expr) : MetaM Bool := do
  if lhs == rhs then return true
  if lhs.hasExprMVar || rhs.hasExprMVar then matchWithMVars lhs rhs
  else matchClosed lhs rhs


-- Closed clauses can be cancelled greedily: unlike clauses containing
-- metavariables, matching them cannot constrain a later cancellation choice.
private partial def cancelClosedClauses : List Expr → List Expr → MetaM (List Expr × List Expr)
  | [], rhs => return ([], rhs)
  | l :: ls, rhs => do
    if l.hasExprMVar then
      let (ls, rhs) ← cancelClosedClauses ls rhs
      return (l :: ls, rhs)
    let some j ← rhs.toArray.findIdxM? (fun r => do
        if r.hasExprMVar then return false
        matchClosed l r) | do
      let (ls, rhs) ← cancelClosedClauses ls rhs
      return (l :: ls, rhs)
    cancelClosedClauses ls (rhs.eraseIdx j)

private partial def cancelClauses (predType : Expr) (lhs rhs : List Expr) : MetaM Bool := do
  let (lhs, rhs) ← cancelClosedClauses lhs rhs
  if lhs.isEmpty && rhs.isEmpty then return true
  for i in List.range lhs.length do
    for j in List.range rhs.length do
      let l := lhs[i]!
      let r := rhs[j]!
      -- Closed matches have already been removed. A naked metavariable is
      -- reserved for assignment to the conjunction of all remaining clauses
      -- below.
      if (l.hasExprMVar || r.hasExprMVar) && !isNakedMVar l && !isNakedMVar r then
        let matched ← commitWhen do
          unless ← matchAtom l r do return false
          -- Matching may instantiate metavariables in the remaining clauses.
          let lhs ← (lhs.eraseIdx i).mapM instantiateMVars
          let rhs ← (rhs.eraseIdx j).mapM instantiateMVars
          cancelClauses predType lhs rhs
        if matched then return true
  assignNaked predType lhs rhs <||> assignNaked predType rhs lhs

private partial def alignClauses : List Expr → List Expr → MetaM (Option (List Expr))
  | [], [] => return some []
  | lhs, r :: rs => do
    let some i ← lhs.toArray.findIdxM? (fun l => matchAtom l r) | return none
    let some rest ← alignClauses (lhs.eraseIdx i) rs | return none
    return some (lhs[i]! :: rest)
  | _, _ => return none

/--
Rebuilds `e` while preserving its sep/emp tree structure and replacing each
atomic leaf, from left to right, with the next entry in `clauses`.
Returns none if there are not enough clauses to replace every atomic leaf.
Returns some (rebuilt expr, unused clauses) otherwise.
-/
private partial def canonicalize (e : Expr) (clauses : List Expr) :
    MetaM (Option (Expr × List Expr)) := do
  let e ← instantiateMVars e
  if e.getAppFn.constName? == some ``Std.ExtHashMap.emp then
    return some (e, clauses)
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let some (p, clauses) ← canonicalize args[args.size - 2]! clauses | return none
    let some (q, clauses) ← canonicalize args[args.size - 1]! clauses | return none
    return some (← mkAppM ``Std.ExtHashMap.sep #[p, q], clauses)
  return match clauses with
  | c :: clauses => some (c, clauses)
  | [] => none

private def proveSeqEq (lhs rhs : Expr) : MetaM (Option Expr) :=
  commitWhenSomeNoEx? do
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    let lhsClauses ← reifyClauses lhs
    let rhsClauses ← reifyClauses rhs
    let some rhsClauses ← alignClauses lhsClauses rhsClauses | return none
    let some (lhs, []) ← canonicalize lhs lhsClauses | return none
    let some (rhs, []) ← canonicalize rhs rhsClauses | return none
    let proof ← mkFreshExprMVar (← mkEq lhs rhs)
    Lean.Meta.AC.rewriteUnnormalizedRefl proof.mvarId!
    return some (← instantiateMVars proof)

private def solveSepEq (lhs rhs : Expr) : MetaM (Option Expr) := do
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if lhs == rhs then
    return some (← mkEqRefl lhs)
  let predType ← inferType lhs
  let lhsClauses ← reifyClauses lhs
  let rhsClauses ← reifyClauses rhs
  unless ← cancelClauses predType lhsClauses rhsClauses do return none
  proveSeqEq lhs rhs

private def solveFromHypothesis (target hypType hyp : Expr) : MetaM (Option Expr) := do
  let target ← instantiateMVars target
  let hypType ← instantiateMVars hypType
  unless hypType.isApp && target.isApp do return none
  let targetFn := target.appFn!
  let targetArg := target.appArg!
  let hypFn := hypType.appFn!
  let hypArg := hypType.appArg!
  unless ← matchAtom (← reduceProjectionApp targetArg) (← reduceProjectionApp hypArg) do
    return none
  let some hSeps ← solveSepEq hypFn targetFn | return none
  let hFunEq ← mkAppM ``congrFun #[hSeps, hypArg]
  return some (← mkAppM ``Eq.mp #[hFunEq, hyp])

/-- Like `solveFromHypothesis`, but the hypothesis may be universally quantified
(`h : ∀ v, (P v ⋆ Q) (m v)`); its binders are instantiated by unification. This lets
the user state, *before* symbolic execution, facts about memories that are only
computed later (e.g. the memory after a store of a yet-unknown value). -/
private def solveFromForallHypothesis (target : Expr) (localDecl : LocalDecl) :
    MetaM (Option Expr) := do
  let type ← instantiateMVars localDecl.type
  unless type.isForall do
    return ← solveFromHypothesis target type localDecl.toExpr
  commitWhenSome? do
    let (mvars, _, body) ← forallMetaTelescopeReducing type
    let some proof ← solveFromHypothesis target body (mkAppN localDecl.toExpr mvars)
      | return none
    let proof ← instantiateMVars proof
    -- all binders must have been determined by unification
    if (← mvars.anyM fun m => return (← instantiateMVars m).hasExprMVar) then
      return none
    return some proof

/-- Try to close `goal` (an `=`-between-separation-predicates goal, or a
separation predicate applied to a memory) using AC-matching of the clauses,
possibly against a hypothesis. Metavariables in the goal (e.g. `?bs`, `?R`) are
instantiated. Returns `true` on success. -/
def ecancelCore (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  -- Existential witnesses introduced by tactics are synthetic-opaque goals;
  -- `ecancel` intentionally instantiates them as part of cancellation.
  withConfig (fun config => { config with assignSyntheticOpaque := true }) do
    if target.isAppOfArity ``Eq 3 then
      let args := target.getAppArgs
      if let some proof ← solveSepEq args[1]! args[2]! then
        goal.assign proof
        return true
    for localDecl? in (← getLCtx).decls.toArray.reverse do
      if let some localDecl := localDecl? then
        if localDecl.isImplementationDetail then continue
        if let some proof ← solveFromForallHypothesis target localDecl then
          goal.assign proof
          return true
    return false

syntax (name := ecancel) "ecancel" : tactic

@[tactic ecancel]
def evalEcancel : Tactic :=
  fun _stx : Syntax => withMainContext do
  let goal ← getMainGoal
  unless ← ecancelCore goal do
    throwError "ecancel: could not automatically solve goal {← goal.getType}"
end Kraken.Tactic
