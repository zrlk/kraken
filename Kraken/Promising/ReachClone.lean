/-
**Cloning a definition with some constants substituted**: the tool that makes `decide` able to replay x64/AArch64 runs.

The kernel cannot evaluate a lookup in a hash map: the bucket index is a
`USize`, whose width `System.Platform.numBits` is opaque. Every private
memory (`Mem w`, an `ExtHashMap`) lookup of the ISA semantics is such a
lookup, even in the empty map, so `decide` gets stuck on any instruction
that touches memory.

`#reach_clone root as newRoot using [c₁ := r₁ by h₁, …]` copies every
definition reachable from `root` that (transitively) mentions some `cᵢ`,
replacing each `cᵢ` by `rᵢ` and each copied constant by its copy, and proves
`hroot : @newRoot = @root`. Each `hᵢ : @rᵢ = @cᵢ` is the user's proof that
the replacement is harmless. The copy of a definition `f` with body `B` is
`B[g := g']`; its equation is `congr … (congrArg (fun x … => B[g := x]) hg) …`,
which the kernel checks by unfolding `f` and `f'` (no evaluation). Nothing is
assumed: the copies are ordinary definitions and the equations ordinary
theorems.
-/
import Lean

namespace Kraken.Promising.Reach

open Lean Meta Elab Command

/-- The definitions reachable from `root` through definition bodies, in
post-order (dependencies first), not looking inside `stop` constants. -/
private partial def reachPostOrder (env : Environment) (root : Name) (stop : Name → Bool) :
    Array Name := Id.run do
  let rec go (n : Name) (st : NameSet × Array Name) : NameSet × Array Name := Id.run do
    let (visited, out) := st
    if visited.contains n then return st
    let visited := visited.insert n
    if stop n then return (visited, out.push n)
    match env.find? n with
    | some (.defnInfo d) =>
      let (visited, out) := d.value.getUsedConstants.foldl (fun st c => go c st) (visited, out)
      return (visited, out.push n)
    | _ => return (visited, out.push n)
  return (go root ({}, #[])).2

/-- The distinct occurrences `.const c ls` of substituted constants in `e`. -/
private partial def reachOccs (map : NameMap (Name × Name)) (e : Expr) (st : Array Expr × Std.HashSet Expr) :
    Array Expr × Std.HashSet Expr :=
  match e with
  | .const c _ => if map.contains c && !st.2.contains e then (st.1.push e, st.2.insert e) else st
  | .app f a => reachOccs map a (reachOccs map f st)
  | .lam _ t b _ | .forallE _ t b _ => reachOccs map b (reachOccs map t st)
  | .letE _ t v b _ => reachOccs map b (reachOccs map v (reachOccs map t st))
  | .mdata _ b => reachOccs map b st
  | .proj _ _ b => reachOccs map b st
  | _ => st

/-- Clone `root`; see the module docstring. Returns the copy of `root`
(and its equation `<copy>_reach_eq`). -/
def reachClone (root newRoot : Name) (subst : Array (Name × Name × Name)) : CommandElabM Unit := do
  let env ← getEnv
  let isKey (n : Name) : Bool := subst.any (·.1 == n)
  let order := reachPostOrder env root isKey
  -- `map`: original ↦ (replacement, equation `@replacement = @original`)
  let mut map : NameMap (Name × Name) := subst.foldl (fun m (c, r, h) => m.insert c (r, h)) {}
  for n in order do
    if isKey n then continue
    let some (.defnInfo d) := env.find? n | continue
    let used := d.value.getUsedConstants
    unless used.any (map.contains ·) do continue
    let newName := if n == root then newRoot else `Kraken.Promising.Reach.K ++ n
    let eqName := newName ++ `_reach_eq
    -- the occurrences to abstract: distinct `(constant, levels)` pairs
    let occs := (reachOccs map d.value (#[], {})).1
    let lvls := d.levelParams.map Level.param
    liftTermElabM do
      -- abstracted body `A`
      let tys ← occs.mapM fun e => inferType e
      let A ← withLocalDeclsDND (occs.mapIdx fun i _ => ((`x).appendIndexAfter i, tys[i]!)) fun xs => do
        let body := d.value.replace fun e =>
          match e with
          | .const c _ => if map.contains c then (occs.findIdx? (· == e)).map (xs[·]!) else none
          | _ => none
        mkLambdaFVars xs body
      let news := occs.map fun e => match e with
        | .const c ls => .const (map.find? c).get!.1 ls
        | e => e
      let newBody := (mkAppN A news).headBeta
      let dv : DefinitionVal :=
        { name := newName, levelParams := d.levelParams, type := d.type, value := newBody, hints := d.hints, safety := d.safety }
      addDecl (.defnDecl dv)
      -- the equation
      let mut pf ← mkEqRefl A
      for i in [0:occs.size] do
        let .const c ls := occs[i]! | unreachable!
        let h := Expr.const (map.find? c).get!.2 ls
        pf ← mkCongr pf h
      let ty ← mkEq (.const newName lvls) (.const n lvls)
      let tv : TheoremVal := { name := eqName, levelParams := d.levelParams, type := ty, value := pf }
      addDecl (.thmDecl tv)
    map := map.insert n (newName, eqName)
  unless map.contains root do throwError "#reach_clone: {root} mentions none of the substituted constants"

syntax (name := reachCloneCmd) "#reach_clone " ident " as " ident " using " "["
  (ident " := " ident " by " ident),* "]" : command

@[command_elab reachCloneCmd] def elabReachClone : CommandElab := fun stx => do
  match stx with
  | `(#reach_clone $root:ident as $newRoot:ident using [$[$cs:ident := $rs:ident by $hs:ident],*]) =>
    let res (i : Ident) : CommandElabM Name := liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
    let root ← res root
    let subst ← (cs.zip (rs.zip hs)).mapM fun (c, r, h) => return (← res c, ← res r, ← res h)
    let ns ← getCurrNamespace
    reachClone root (ns ++ newRoot.getId) subst
  | _ => throwUnsupportedSyntax

end Kraken.Promising.Reach
