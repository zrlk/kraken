/-
**The semantic twins: `#sem_twin`, the `ReachableSem` twins of the published theorems**
.

`#sem_twin n₁ n₂ …` adds, for each theorem `n`, the theorem `semName n`
(`ChainK.semName`: `_sem` before the first `_concrete`, otherwise appended
before any trailing primes). Its statement is `semType` of `n`'s: every
`Reachable A fuel c₀ c` becomes `ReachableSem A fuel c₀ c`, with the same
arguments and so the same fuel binder (now the certification fuel), and every
`Config.FaultFree` becomes `Config.FaultFreeSem` (`ChainK/FaultFree.lean`).

The proof is built from the K clone `nK` (`#chaink_clone` of `n`'s module).
`nK` has `n`'s statement at the K world, and the proof transports it
position by position:

- a `ReachableSem` hypothesis is turned into `ReachableK` by
  `ReachableK.of_reachableSem'` from `Config.init_bnd` (the start must be a
  `Config.init`);
- the `Config.FaultFreeSem` conclusion comes from `Config.FaultFreeSem.of_K`;
- a conjunction is transported componentwise;
- any other position must agree by definitional unfolding.

Nothing is assumed. The kernel checks every twin, and
`Kraken/Examples/LockFree/tools/sem_twins.py` re-checks every twin's
statement against `semType` independently and regenerates the listing
`Kraken/Examples/LockFree/SEM_TWINS.md`.
-/
import Kraken.Promising.SLR.ChainK.FaultFree
import Kraken.Promising.ChainK.Clone

namespace Kraken.Promising.ChainK

open Lean Elab Command Meta
open Kraken.Promising.Live.Bridge

/-- `foo ↦ foo_sem`, `foo_concreteN ↦ foo_sem_concreteN`, `foo' ↦ foo_sem'`. -/
def semName (n : Name) : Name :=
  match n with
  | .str p s =>
    let parts := s.splitOn "_concrete"
    if parts.length > 1 then
      .str p (parts.head! ++ "_sem_concrete" ++ "_concrete".intercalate parts.tail!)
    else
      let cs := s.toList
      let core := (cs.reverse.dropWhile (· == '\'')).reverse
      .str p (String.ofList core ++ "_sem" ++ String.ofList (cs.drop core.length))
  | _ => n

/-- The twin's statement: `Reachable ↦ ReachableSem`, `Config.FaultFree ↦ Config.FaultFreeSem`. -/
partial def semType (e : Expr) : Expr :=
  e.replace fun x =>
    -- `@Reachable A I fuel c c'` ↦ `@ReachableSem I A fuel c c'`
    if x.isAppOfArity ``Reachable 5 then
      let a := x.getAppArgs.map semType
      some (mkAppN (.const ``ReachableSem x.getAppFn.constLevels!) #[a[1]!, a[0]!, a[2]!, a[3]!, a[4]!])
    else match x with
      | .const n us => if n == ``Config.FaultFree then some (.const ``Config.FaultFreeSem us) else none
      | _ => none

/-- `c.Bnd` for an initial configuration `c = Config.init states initMem`. -/
def mkBnd (c : Expr) : MetaM Expr := do
  let c ← instantiateMVars c
  if c.isAppOfArity ``Config.init 3 then
    mkAppOptM ``Config.init_bnd #[some (c.getArg! 0), some (c.getArg! 1), some (c.getArg! 2)]
  else throwError "sem_twin: the start configuration {c} is not a `Config.init`"

/-- From `eK` (of the K clone's type at this position), a proof of `tS`. -/
partial def transport (eK tS : Expr) : MetaM Expr := do
  match tS with
  | .forallE nm d b bi =>
    withLocalDecl nm bi d fun x => do
      let arg ← if d.isAppOfArity ``ReachableSem 5 then
          mkAppOptM ``ReachableK.of_reachableSem'
            #[none, none, none, none, none, some (← mkBnd (d.getArg! 3)), some x]
        else pure x
      let body ← transport (mkApp eK arg) (b.instantiate1 x)
      mkLambdaFVars #[x] body
  | _ =>
    if tS.isAppOfArity ``And 2 then
      let tK ← whnfR (← inferType eK)
      unless tK.isAppOfArity ``And 2 do throwError "sem_twin: expected a conjunction, got {tK}"
      let l ← transport (mkApp3 (.const ``And.left []) (tK.getArg! 0) (tK.getArg! 1) eK) (tS.getArg! 0)
      let r ← transport (mkApp3 (.const ``And.right []) (tK.getArg! 0) (tK.getArg! 1) eK) (tS.getArg! 1)
      return mkApp4 (.const ``And.intro []) (tS.getArg! 0) (tS.getArg! 1) l r
    else if tS.isAppOfArity ``Config.FaultFreeSem 4 then
      mkAppOptM ``Config.FaultFreeSem.of_K
        #[some (tS.getArg! 0), some (tS.getArg! 1), some (tS.getArg! 2), none, some (tS.getArg! 3),
          some (← mkBnd (tS.getArg! 3)), some eK]
    else
      let tK ← inferType eK
      unless ← isDefEq tK tS do throwError "sem_twin: cannot transport{indentExpr tK}\nto{indentExpr tS}"
      return eK

/-- Add the twin `semName n` of `n` (see the module docstring). -/
def semTwin (n : Name) : CommandElabM Unit := liftTermElabM do
  let ci ← getConstInfo n
  let nK := addK n
  let ciK ← getConstInfo nK
  let tS := semType ci.type
  if tS == ci.type then throwError "sem_twin: {n} mentions neither `Reachable` nor `Config.FaultFree`"
  if (tS.find? (·.isConstOf ``Reachable)).isSome then throwError "sem_twin: {n} has a partially applied `Reachable`"
  let us := ciK.levelParams.map mkLevelParam
  let v ← transport (.const nK us) tS
  let v ← instantiateMVars v
  if v.hasMVar then throwError "sem_twin: unassigned metavariables in the proof of {semName n}"
  let new := semName n
  addDecl (.thmDecl { name := new, levelParams := ci.levelParams, type := tS, value := v })
  addDocStringCore new s!"**`{n}` on the semantic machine** (TWINS, `#sem_twin`): its statement with `Reachable` ↦ `ReachableSem` and `Config.FaultFree` ↦ `Config.FaultFreeSem` (same fuel binder, now the certification fuel). Proved from the K clone `{nK}`."

/-- `#sem_twin n₁ n₂ …`: add the `ReachableSem` twin of each `nᵢ`. -/
syntax (name := semTwinCmd) "#sem_twin " ident+ : command

@[command_elab semTwinCmd] def elabSemTwin : CommandElab := fun stx => do
  match stx with
  | `(#sem_twin $ids:ident*) =>
    for id in ids do
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      semTwin n
  | _ => throwUnsupportedSyntax

end Kraken.Promising.ChainK
