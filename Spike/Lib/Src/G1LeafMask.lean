import Spike.Lib.Src.NJL
import Spike.Lib.Src.GroupPl

/-!
**A one-operand atom's layout is a leaf** (ISA-neutral): the walk's layout
`L` of an atom that the lowering keeps as one operand, at a type compatible
with `L`, has the mask `[true]` (one scalar word). This is the fact an
allocation's count needs (its word a number, `NumL` at index 0), read off
the node's own facts instead of the literal walk's bindings.

- `compat_opLen`: a type compatible with a layout takes the layout's
  operands (`flatL`: a locative two, any other word one);
- `opLen_of_group`: a grouping of exactly `os` takes `os.length` operands;
- `litMask_one_of_atomV`: an atom bound to one operand in a grouped
  lowering environment, at a type compatible with `L`, has `litMask L =
  [true]` (`litMask_of_flatL`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (LitV)

/-- **A type of layout `L` takes `L`'s operands** (`flatL`: a locative two,
any other word one; as `compat_plLen` for placements). -/
theorem compat_opLen : ∀ (t : Ty) (L : LitV), Compat t L = true → opLen t = some (flatL L).length := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L h
    cases L <;> simp only [Compat, Bool.and_eq_true, Bool.false_eq_true] at h
    simp [opLen, iha _ h.1, ihb _ h.2, flatL]
  | refine t _ ih => intro L h; exact ih L h
  | iall t ih => intro L h; exact ih L h
  | mu t ih => intro L h; exact ih L h
  | iex b ih =>
    intro L h
    simp only [Compat, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [opLen, h.1, ih L h.2]
  | tex k b ih =>
    intro L h
    simp only [Compat, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [opLen, h.1, ih L h.2]
  | _ => intro L h; cases L <;> simp_all [Compat, opLen, flatL]

/-- **A grouping of exactly `os` takes all of `os`** (`grp_spec`, nothing
left). -/
theorem opLen_of_group {t : Ty} {os : List Scc.IR.Operand} {pls : List Spike.Lib.Form.WordPl}
    (h : Spike.Lib.Form.group t os = some pls) : opLen t = some os.length := by
  simp only [Spike.Lib.Form.group] at h
  split at h
  · rename_i pls' hg
    obtain ⟨k, hk, -, hle, hr, -⟩ := grp_spec t os pls' [] hg
    have : k = os.length := by
      have := congrArg List.length hr
      simp at this
      omega
    rw [hk, this]
  · cases h

/-- **A one-operand atom's layout is a leaf**: an atom the grouped lowering
environment `env` binds to one operand (`atomV`), at a type compatible with
the layout `L`, has `L`'s mask `[true]`. -/
theorem litMask_one_of_atomV {env : Scc.Lower.Env} (hg : GrpL env) {a : At} {t : Ty} {w : Scc.IR.Operand}
    (ha : Scc.Lower.Inv.atomV env a = some (t, [w])) {L : LitV} (hc : Compat t L = true) :
    litMask L = [true] := by
  obtain ⟨pls, hp, -⟩ := sevalAt_ofEnv2G hg ha
  have h1 := opLen_of_group hp
  rw [compat_opLen t L hc] at h1
  have hl : (flatL L).length = 1 := by simpa using h1
  obtain ⟨f, hf⟩ : ∃ f, flatL L = [f] := by
    cases h : flatL L with
    | nil => rw [h] at hl; cases hl
    | cons f fs => cases fs with
      | nil => exact ⟨f, rfl⟩
      | cons _ _ => rw [h] at hl; simp at hl
  exact litMask_of_flatL hf

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.compat_opLen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.compat_opLen

/-- info: 'Spike.Lib.LowerNode.opLen_of_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.opLen_of_group

/-- info: 'Spike.Lib.LowerNode.litMask_one_of_atomV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.litMask_one_of_atomV
