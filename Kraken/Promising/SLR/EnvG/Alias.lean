/-
**Statement-preserving aliases**.

When an ISA-specific copy of ISA-neutral code is replaced by the neutral
original, every public name of the copy is kept, with its original statement.
`hoist_alias [o₁ ↦ n₁, …, oₖ ↦ nₖ]` adds, in order, each `nᵢ` with

- type: the type of `oᵢ` with every constant `oⱼ` of the list replaced by
  `nⱼ` (so a copy's statement, which mentions the copy's own names, comes back
  verbatim);
- value: `oᵢ` itself (accepted by definitional unfolding of the earlier
  aliases);
- kind: a `theorem` if the type is a proposition, otherwise a reducible
  definition (`abbrev`); definitions are not compiled (they are used in proofs
  and instance arguments only).

Names are fully qualified (no namespace resolution). Attributes (`instance`,
`simp`, …) are added by the caller with `attribute [...]`.

A pair `oᵢ ↦ nᵢ` whose `nᵢ` already exists as an alias of `oᵢ` (its value
is the constant `oᵢ`) adds nothing and only takes part in the renaming: so a
copy whose statement mentions an earlier alias (`EnvGTCI` for
`EnvGTC`) can be aliased with its statement verbatim. (This also
holds of theorem aliases, such as an aliased constructor of a `Prop`-valued
inductive, which a recursor's statement mentions.)
-/
import Lean

namespace Kraken.Promising.SLR.EnvG.Alias

open Lean Elab Command Meta

/-- `hoist_alias [o₁ ↦ n₁, …]`: add each `nᵢ` as an alias of `oᵢ`, its type
that of `oᵢ` with the `oⱼ` renamed to the `nⱼ` (see the module docstring). -/
syntax (name := hoistAlias) "hoist_alias " "[" sepBy1(ident " ↦ " ident, ", ") "]" : command

@[command_elab hoistAlias] def elabHoistAlias : CommandElab := fun stx => do
  let args := stx[2].getSepArgs
  let pairs : Array (Name × Name) := args.map fun p => (p[0].getId, p[2].getId)
  let ren : NameMap Name := pairs.foldl (fun m (o, n) => m.insert o n) {}
  for (o, n) in pairs do
    let some ci := (← getEnv).find? o | throwError "hoist_alias: unknown constant {o}"
    if let some ci' := (← getEnv).find? n then
      -- an existing alias of `oᵢ` is kept and only used for the renaming
      if (ci'.value? (allowOpaque := true)).any (·.isConstOf o) then continue
      throwError "hoist_alias: {n} already exists"
    let ty := ci.type.replace fun
      | .const c ls => (ren.find? c).map (Expr.const · ls)
      | _ => none
    let lps := ci.levelParams
    let val := Expr.const o (lps.map Level.param)
    let isP ← liftTermElabM <| Meta.isProp ty
    if isP then
      liftCoreM <| addDecl (.thmDecl { name := n, levelParams := lps, type := ty, value := val })
    else
      let dv : DefinitionVal :=
        { name := n
          levelParams := lps
          type := ty
          value := val
          hints := .abbrev
          safety := .safe }
      liftCoreM <| addDecl (.defnDecl dv)
      liftCoreM <| setReducibleAttribute n
    liftTermElabM <| addDeclarationRangesFromSyntax n stx

end Kraken.Promising.SLR.EnvG.Alias
