/-
**`#inf_twin`, the fuel-free twins of the `ReachableSem`
twins** (ISA-neutral).

`#inf_twin n₁ n₂ …` adds, for each theorem `n` (typically a `#sem_twin`
twin, `ChainK/SemTwin.lean`, over `ReachableSem A fuel` /
`Config.FaultFreeSem A fuel` with a `∀ fuel` binder), the theorem
`semInfName n` over the fuel-free semantic machine (`LiveSemInf.lean`). Its
statement is `n`'s with

- the **fuel binder dropped**: the first `∀ (fuel : Nat)` binder whose
  variable `φ` is the fuel argument of some `ReachableSem`/`FaultFreeSem`;
- every `ReachableSem A φ c c'` ↦ `ReachableSemInf A c c'`;
- every `Config.FaultFreeSem A φ init` ↦ `Config.FaultFreeSemInf A init`.

The proof is built from `n` by transport under the binder (nothing is
assumed; the kernel checks every twin):

- a `ReachableSemInf` hypothesis gives a fuel (`reachableSemInf_elim`,
  from `reachableSemInf_iff`), at which `n` is instantiated; the rest of that
  statement must not mention `φ`;
- a `Config.FaultFreeSemInf` conclusion comes from `n` at every fuel
  (`Config.FaultFreeSemInf.of_forall`);
- a conjunction is transported componentwise; hypotheses not mentioning `φ`
  are passed through; a position not mentioning `φ` is `n` at fuel `0`.

Any other occurrence of `φ` (in a hypothesis that is not `ReachableSem`, or
in a positive `ReachableSem`) is rejected with an error. The independent
checker `Kraken/Examples/LockFree/tools/inf_twins.py` re-checks every twin's
statement and writes the listing `Kraken/Examples/LockFree/INF_TWINS.md`.

Also here: `Config.FaultFreeSemInf.iff_forall` (fault freedom at every fuel
is fault freedom on the Inf machine) and `Config.FaultFreeSemInf.of_K`.
-/
import Kraken.Promising.SLR.ChainK.FaultFree
import Kraken.Promising.LiveSemInf

namespace Kraken.Promising

open Kraken.Promising.Live.Bridge Kraken.Promising.Live.Inf

variable {I : ISA}

/-- **Fault freedom at every fuel is fault freedom on the fuel-free machine**
(and conversely). -/
theorem Config.FaultFreeSemInf.iff_forall {A : Arch} {init : Config I} :
    Config.FaultFreeSemInf A init ↔ ∀ fuel, Config.FaultFreeSem A fuel init :=
  forall_reachableSemInf_iff (P := fun c => ∀ tid m, ¬ c.FaultStep A tid m)

theorem Config.FaultFreeSemInf.of_forall {A : Arch} {init : Config I}
    (h : ∀ fuel, Config.FaultFreeSem A fuel init) : Config.FaultFreeSemInf A init :=
  Config.FaultFreeSemInf.iff_forall.mpr h

theorem Config.FaultFreeSemInf.toSem {A : Arch} {init : Config I} (h : Config.FaultFreeSemInf A init)
    (fuel : Nat) : Config.FaultFreeSem A fuel init :=
  Config.FaultFreeSemInf.iff_forall.mp h fuel

/-- K-world fault freedom (at any fuel) gives fault freedom on the fuel-free
machine, from a bounded start. -/
theorem Config.FaultFreeSemInf.of_K {A : Arch} {fuel : Nat} {init : Config I} (hb : init.Bnd)
    (h : Config.FaultFreeK A fuel init) : Config.FaultFreeSemInf A init :=
  fun c hc => h c (ReachableK.of_reachableSemInf hb hc)

end Kraken.Promising

namespace Kraken.Promising.Live.Inf

open Kraken.Promising Kraken.Promising.Live.Bridge

variable {I : ISA}

/-- Eliminate a fuel-free reachability hypothesis into a fuel (the form used
by `#inf_twin`). -/
theorem reachableSemInf_elim {A : Arch} {c c' : Config I} {P : Prop} (h : ReachableSemInf A c c')
    (k : ∀ fuel, ReachableSem A fuel c c' → P) : P :=
  let ⟨f, hf⟩ := reachableSemInf_iff.mp h
  k f hf

end Kraken.Promising.Live.Inf

namespace Kraken.Promising.ChainK

open Lean Elab Command Meta
open Kraken.Promising.Live.Bridge Kraken.Promising.Live.Inf

/-- `foo_sem ↦ foo_semInf`, `foo_sem_concreteN ↦ foo_semInf_concreteN`,
`foo_sem' ↦ foo_semInf'`; a name without `_sem` gets `_semInf` (before any
trailing primes). -/
def semInfName (n : Name) : Name :=
  match n with
  | .str p s =>
    let parts := s.splitOn "_sem_concrete"
    if parts.length > 1 then
      .str p (parts.head! ++ "_semInf_concrete" ++ "_sem_concrete".intercalate parts.tail!)
    else
      let cs := s.toList
      let core := String.ofList (cs.reverse.dropWhile (· == '\'')).reverse
      let primes := String.ofList (cs.drop core.length)
      if core.endsWith "_sem" then .str p (core ++ "Inf" ++ primes)
      else .str p (core ++ "_semInf" ++ primes)
  | _ => n

/-- `e` is `ReachableSem _ _ φ _ _` or `Config.FaultFreeSem _ _ φ _`. -/
def isFuelUse (φ : Expr) (e : Expr) : Bool :=
  (e.isAppOfArity ``ReachableSem 5 && e.getArg! 2 == φ) ||
  (e.isAppOfArity ``Config.FaultFreeSem 4 && e.getArg! 2 == φ)

/-- The twin's statement at fuel variable `φ`: `ReachableSem A φ ↦
ReachableSemInf A`, `Config.FaultFreeSem A φ ↦ Config.FaultFreeSemInf A`. -/
partial def infType (φ : Expr) (e : Expr) : Expr :=
  e.replace fun x =>
    if x.isAppOfArity ``ReachableSem 5 && x.getArg! 2 == φ then
      let a := x.getAppArgs
      some (mkAppN (.const ``ReachableSemInf x.getAppFn.constLevels!) #[a[0]!, a[1]!, infType φ a[3]!, infType φ a[4]!])
    else if x.isAppOfArity ``Config.FaultFreeSem 4 && x.getArg! 2 == φ then
      let a := x.getAppArgs
      some (mkAppN (.const ``Config.FaultFreeSemInf x.getAppFn.constLevels!) #[a[0]!, a[1]!, infType φ a[3]!])
    else none

/-- Under the fuel binder: from `mk f : B[f/φ]` (for every fuel `f`), a proof
of `infType φ B`. -/
partial def transportInf (φ : Expr) (mk : Expr → MetaM Expr) (B : Expr) : MetaM Expr := do
  let B := B.consumeMData
  let fv := φ.fvarId!
  if !B.containsFVar fv then
    let p ← mk (mkNatLit 0)
    unless ← isDefEq (← inferType p) B do throwError "inf_twin: cannot transport{indentExpr B}"
    return p
  match B with
  | .forallE nm d b bi =>
    let d := d.consumeMData
    if !d.containsFVar fv then
      withLocalDecl nm bi d fun x => do
        let p ← transportInf φ (fun f => do return mkApp (← mk f) x) (b.instantiate1 x)
        mkLambdaFVars #[x] p
    else if d.isAppOfArity ``ReachableSem 5 && d.getArg! 2 == φ then
      let rest := d.getAppArgs.toList.eraseIdx 2
      if rest.any (·.containsFVar fv) || b.hasLooseBVars then
        throwError "inf_twin: unsupported `ReachableSem` hypothesis{indentExpr d}"
      if b.containsFVar fv then
        throwError "inf_twin: the fuel occurs after a `ReachableSem` hypothesis in{indentExpr b}"
      withLocalDecl nm bi (infType φ d) fun x => do
        let k ← withLocalDecl `fuel .default (.const ``Nat []) fun f => do
          withLocalDecl `hf .default (d.replaceFVar φ f) fun hf => do
            let p := mkApp (← mk f) hf
            unless ← isDefEq (← inferType p) b do throwError "inf_twin: cannot transport{indentExpr b}"
            mkLambdaFVars #[f, hf] p
        let v ← mkAppOptM ``reachableSemInf_elim
          #[none, none, none, none, some b, some x, some k]
        mkLambdaFVars #[x] v
    else throwError "inf_twin: the fuel occurs in a hypothesis that is not `ReachableSem`{indentExpr d}"
  | _ =>
    if B.isAppOfArity ``And 2 then
      let L := B.getArg! 0
      let R := B.getArg! 1
      let side (pr : Name) (f : Expr) : MetaM Expr := do
        let e ← mk f
        return mkApp3 (.const pr []) (L.replaceFVar φ f) (R.replaceFVar φ f) e
      let l ← transportInf φ (side ``And.left) L
      let r ← transportInf φ (side ``And.right) R
      return mkApp4 (.const ``And.intro []) (infType φ L) (infType φ R) l r
    else if B.isAppOfArity ``Config.FaultFreeSem 4 && B.getArg! 2 == φ &&
        !(B.getArg! 0).containsFVar fv && !(B.getArg! 1).containsFVar fv && !(B.getArg! 3).containsFVar fv then
      let lam ← withLocalDecl `fuel .default (.const ``Nat []) fun f => do
        mkLambdaFVars #[f] (← mk f)
      mkAppOptM ``Config.FaultFreeSemInf.of_forall
        #[some (B.getArg! 0), some (B.getArg! 1), some (B.getArg! 3), some lam]
    else throwError "inf_twin: unsupported occurrence of the fuel in{indentExpr B}"

/-- Before the fuel binder: returns the twin's statement and its proof from
`e : tS`. -/
partial def outerInf (e tS : Expr) : MetaM (Expr × Expr) := do
  match tS.consumeMData with
  | .forallE nm d b bi =>
    withLocalDecl nm bi d fun x => do
      let b' := b.instantiate1 x
      let isFuel := d.isConstOf ``Nat && (b'.find? (isFuelUse x)).isSome
      if isFuel then
        let tI := infType x b'
        if tI.containsFVar x.fvarId! then
          throwError "inf_twin: the fuel {nm} has another occurrence in{indentExpr tI}"
        let p ← transportInf x (fun f => do return mkApp e f) b'
        return (tI, p)
      else
        let (tI, p) ← outerInf (mkApp e x) b'
        return (← mkForallFVars #[x] tI, ← mkLambdaFVars #[x] p)
  | _ => throwError "inf_twin: no fuel binder (a `∀ fuel` used by `ReachableSem`/`Config.FaultFreeSem`)"

/-- Add the twin `semInfName n` of `n` (see the module docstring). -/
def infTwin (n : Name) : CommandElabM Unit := liftTermElabM do
  let ci ← getConstInfo n
  let us := ci.levelParams.map mkLevelParam
  let (tI, v) ← outerInf (.const n us) ci.type
  let tI ← instantiateMVars tI
  let v ← instantiateMVars v
  if (tI.find? fun x => x.isConstOf ``ReachableSem || x.isConstOf ``Config.FaultFreeSem).isSome then
    throwError "inf_twin: {n}'s twin still mentions `ReachableSem` or `Config.FaultFreeSem`"
  if v.hasMVar || tI.hasMVar then throwError "inf_twin: unassigned metavariables in the twin of {n}"
  let new := semInfName n
  addDecl (.thmDecl { name := new, levelParams := ci.levelParams, type := tI, value := v })
  addDocStringCore new s!"**`{n}` on the fuel-free semantic machine** (P2, `#inf_twin`): its statement with the fuel binder dropped, `ReachableSem A fuel` ↦ `ReachableSemInf A` and `Config.FaultFreeSem A fuel` ↦ `Config.FaultFreeSemInf A`. Proved from `{n}`."

/-- `#inf_twin n₁ n₂ …`: add the fuel-free twin of each `nᵢ`. -/
syntax (name := infTwinCmd) "#inf_twin " ident+ : command

@[command_elab infTwinCmd] def elabInfTwin : CommandElab := fun stx => do
  match stx with
  | `(#inf_twin $ids:ident*) =>
    for id in ids do
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      infTwin n
  | _ => throwUnsupportedSyntax

/-! ## `#semU_inf_twin`: the fuel-free liveness headlines on the Inf machine

`#semU_inf_twin n` adds `n` with `_semU` ↦ `_semInf` in its name, for a
theorem `n` concluding (under any binders, componentwise under `∧`)
`TermBoundSemU A c₀`, or `LiveFromSemU`/`ProgressFromSemU`/`TermFromSemU A
c₀ (fun cfg => WeakFairSemU A cfg ∧ MemFair A cfg) …`. The statement replaces
the constants `TermBoundSemU`, `LiveFromSemU`, `ProgressFromSemU`,
`TermFromSemU`, `WeakFairSemU` by their `…SemInf` counterparts
(`LiveSemInf.lean`, same arguments); a statement whose head is a definition
named `…SemU` is unfolded first. Proofs: `termBoundSemInf_iff`,
`liveFromSemInf_of_semU`, `progressFromSemInf_of_semU`,
`termFromSemInf_of_semU`. -/

/-- `foo_semU…` ↦ `foo_semInf…` (first occurrence). -/
def semUInfName (n : Name) : Option Name :=
  match n with
  | .str p s =>
    let parts := s.splitOn "_semU"
    if parts.length > 1 then some (.str p (parts.head! ++ "_semInf" ++ "_semU".intercalate parts.tail!))
    else none
  | _ => none

/-- The `…SemU` ↦ `…SemInf` constants of `#semU_inf_twin`. -/
def uInfConsts : List (Name × Name) :=
  [(``Live.CertBounded.TermBoundSemU, ``TermBoundSemInf), (``Live.CertBounded.LiveFromSemU, ``LiveFromSemInf),
   (``Live.CertBounded.ProgressFromSemU, ``ProgressFromSemInf),
   (``Live.CertBounded.TermFromSemU, ``TermFromSemInf), (``Live.CertBounded.WeakFairSemU, ``WeakFairSemInf)]

def uInfType (e : Expr) : Expr :=
  e.replace fun
    | .const n us => (uInfConsts.lookup n).map (.const · us)
    | _ => none

/-- Unfold a head definition named `…SemU`. -/
def unfoldSemU (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if let .const n _ := e.getAppFn then
    if n.toString.endsWith "SemU" && !(uInfConsts.any (·.1 == n)) then
      if let some e' ← unfoldDefinition? e then return e'.headBeta
  return e

/-- From `e : tU`, a proof of `uInfType tU`. -/
partial def transportU (e tU : Expr) : MetaM Expr := do
  let tU ← unfoldSemU tU
  match tU with
  | .forallE nm d b bi =>
    if uInfType d != d then throwError "semU_inf_twin: a hypothesis mentions the fuel-free machine{indentExpr d}"
    withLocalDecl nm bi d fun x => do
      mkLambdaFVars #[x] (← transportU (mkApp e x) (b.instantiate1 x))
  | _ =>
    if tU.isAppOfArity ``And 2 then
      let L := tU.getArg! 0
      let R := tU.getArg! 1
      let l ← transportU (mkApp3 (.const ``And.left []) L R e) L
      let r ← transportU (mkApp3 (.const ``And.right []) L R e) R
      return mkApp4 (.const ``And.intro []) (← unfoldU L) (← unfoldU R) l r
    let tI ← unfoldU tU
    let p ← if tU.isAppOfArity ``Live.CertBounded.TermBoundSemU 3 then
        mkAppM ``Iff.mpr #[← mkAppOptM ``termBoundSemInf_iff #[none, tU.getArg! 1, tU.getArg! 2], e]
      else if tU.isAppOfArity ``Live.CertBounded.LiveFromSemU 6 then mkAppM ``liveFromSemInf_of_semU #[e]
      else if tU.isAppOfArity ``Live.CertBounded.ProgressFromSemU 6 then mkAppM ``progressFromSemInf_of_semU #[e]
      else if tU.isAppOfArity ``Live.CertBounded.TermFromSemU 4 then mkAppM ``termFromSemInf_of_semU #[e]
      else throwError "semU_inf_twin: unsupported conclusion{indentExpr tU}"
    unless ← isDefEq (← inferType p) tI do throwError "semU_inf_twin: cannot transport{indentExpr tU}"
    return p
where
  /-- The statement after unfolding, as `transportU` sees it. -/
  unfoldU (t : Expr) : MetaM Expr := do
    let t ← unfoldSemU t
    match t with
    | .forallE nm d b bi =>
      withLocalDecl nm bi d fun x => do mkForallFVars #[x] (← unfoldU (b.instantiate1 x))
    | _ =>
      if t.isAppOfArity ``And 2 then
        return mkApp2 (.const ``And []) (← unfoldU (t.getArg! 0)) (← unfoldU (t.getArg! 1))
      else return uInfType t

/-- Add the twin `semUInfName n` of `n`. -/
def semUInfTwin (n : Name) : CommandElabM Unit := liftTermElabM do
  let ci ← getConstInfo n
  let some new := semUInfName n | throwError "semU_inf_twin: {n} has no `_semU` in its name"
  let us := ci.levelParams.map mkLevelParam
  let v ← instantiateMVars (← transportU (.const n us) ci.type)
  let tI ← instantiateMVars (← transportU.unfoldU ci.type)
  if (tI.find? fun x => uInfConsts.any (x.isConstOf ·.1)).isSome then
    throwError "semU_inf_twin: the twin of {n} still mentions a `…SemU` predicate"
  if v.hasMVar || tI.hasMVar then throwError "semU_inf_twin: unassigned metavariables in the twin of {n}"
  addDecl (.thmDecl { name := new, levelParams := ci.levelParams, type := tI, value := v })
  addDocStringCore new s!"**`{n}` on the fuel-free semantic machine `…SemInf`** (P2, `#semU_inf_twin`): its statement with `TermBoundSemU`/`LiveFromSemU`/`ProgressFromSemU`/`TermFromSemU`/`WeakFairSemU` ↦ `…SemInf`. Proved from `{n}` (`LiveSemInf.lean`: the Inf and `…SemU` predicates coincide)."

/-- `#semU_inf_twin n₁ n₂ …`: add the Inf-machine form of each `…_semU…` theorem. -/
syntax (name := semUInfTwinCmd) "#semU_inf_twin " ident+ : command

@[command_elab semUInfTwinCmd] def elabSemUInfTwin : CommandElab := fun stx => do
  match stx with
  | `(#semU_inf_twin $ids:ident*) =>
    for id in ids do
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      semUInfTwin n
  | _ => throwUnsupportedSyntax

end Kraken.Promising.ChainK
