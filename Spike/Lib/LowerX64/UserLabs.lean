/-
**A user function's labels are none of the write abort's** (x86-64): the
label facts `CdCL`'s producers need (`Spike/Lib/LowerX64/UserAbC.lean`). The
x86-64 labels are by name: a user function's block label `labelOf fn l` with
`fn = Names.user f = "wc_" ++ …` begins `.Lwc_`, which no label of `abLabs`
does, and a return label `.L{fn}.x{k}` has the return labels' shape
(`retSfx`), which no label of `abLabs` has.

- `wc_not_abLabs`: no label beginning `.Lwc_` is in `abLabs`.
- `labelOf_user_not_abLabs`: a user function's block label is none of
  `abLabs`.
- `ret_not_abLabs`: a return label is none of `abLabs`.
- `wcL_wc`, `labelOf_user_usr`, `ret_user_usr`: a user function's block and
  return labels begin `.Lwc_` (`WcL`), `CdCL`'s label condition.
-/
import Spike.Lib.LowerX64.UserAbC
import Spike.Lib.LowerX64.AllocRa

namespace Spike.Lib.LowerX64

open Spike.Lib.X64.AllocG (abLabs)
open Scc.Emit.X64 (labelOf)

/-- No label of `abLabs` begins `.Lwc_`. -/
theorem abLabs_take5 : abLabs.all (fun a => a.toList.take 5 != ".Lwc_".toList) = true := by decide

/-- **No label beginning `.Lwc_` is one of the write abort's.** -/
theorem wc_not_abLabs (s : String) : ".Lwc_" ++ s ∉ abLabs := by
  intro h
  have := List.all_eq_true.mp abLabs_take5 _ h
  rw [String.toList_append, List.take_append_of_le_length (by decide)] at this
  simp at this

/-- **A user function's block label is none of the write abort's.** -/
theorem labelOf_user_not_abLabs (f : String) (l : Scc.IR.Label) :
    labelOf (Scc.Lower.Names.user f) l ∉ abLabs := by
  have e : labelOf (Scc.Lower.Names.user f) l = ".Lwc_" ++ (Scc.Lower.Names.mangle f ++ "." ++ l) := by
    simp only [labelOf, Scc.Lower.Names.user, String.append_assoc]
    rfl
  rw [e]
  exact wc_not_abLabs _

/-- The write abort's labels do not have the return labels' shape. -/
theorem abLabs_retSfx : abLabs.all (fun a => !retSfx a) = true := by decide

/-- **A return label is none of the write abort's.** -/
theorem ret_not_abLabs (fn : String) (k : Nat) : s!".L{fn}.x{k}" ∉ abLabs := by
  intro h
  have := List.all_eq_true.mp abLabs_retSfx _ h
  rw [retSfx_ret] at this
  cases this

/-- **A label beginning `.Lwc_` is a user run's** (`WcL`). -/
theorem wcL_wc (s : String) : WcL (".Lwc_" ++ s) := by
  show (".Lwc_" ++ s).toList.take 5 = ".Lwc_".toList
  rw [String.toList_append, List.take_append_of_le_length (by decide)]
  decide

/-- **A user function's block label is a user run's, none of the write
abort's** (`CdCL`'s label condition). -/
theorem labelOf_user_usr (f : String) (l : Scc.IR.Label) :
    labelOf (Scc.Lower.Names.user f) l ∉ abLabs ∧ WcL (labelOf (Scc.Lower.Names.user f) l) := by
  refine ⟨labelOf_user_not_abLabs f l, ?_⟩
  have e : labelOf (Scc.Lower.Names.user f) l = ".Lwc_" ++ (Scc.Lower.Names.mangle f ++ "." ++ l) := by
    simp only [labelOf, Scc.Lower.Names.user, String.append_assoc]
    rfl
  rw [e]
  exact wcL_wc _

/-- **A user function's return label is a user run's, none of the write
abort's** (`CdCL`'s label condition). -/
theorem ret_user_usr (f : String) (k : Nat) :
    s!".L{Scc.Lower.Names.user f}.x{k}" ∉ abLabs ∧ WcL s!".L{Scc.Lower.Names.user f}.x{k}" := by
  refine ⟨ret_not_abLabs _ k, ?_⟩
  have e : s!".L{Scc.Lower.Names.user f}.x{k}" = ".Lwc_" ++ (Scc.Lower.Names.mangle f ++ ".x" ++ toString k) := by
    simp only [Scc.Lower.Names.user, String.append_assoc]
    rfl
  rw [e]
  exact wcL_wc _

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.labelOf_user_not_abLabs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms labelOf_user_not_abLabs

/-- info: 'Spike.Lib.LowerX64.ret_not_abLabs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ret_not_abLabs

end Spike.Lib.LowerX64
