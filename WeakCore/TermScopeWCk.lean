import WeakCore.TermScopeW
import WeakCore.TermCkB

/-! # TermScopeWCk: A1's program check gives the checker-pinned entry frames (A1 checker invariant)

`declWrapOK` checks each body by `checkW` at `declCx`'s context: `ProgWrapOK` is `ProgCkW`.
-/

namespace TermA4
open CoreLang CoreTerm CoreTyping TermScope

/-- **`ProgWrapOK` gives `ProgCkW`**: `declWrapOK`'s context is `declCx`. -/
theorem progCkW_of_wrap {p : Prog} (h : ProgWrapOK p = true) : ProgCkW p := by
  intro d hd
  have h1 := List.all_eq_true.1 h d hd
  simp only [declWrapOK, Bool.and_eq_true] at h1
  obtain ⟨⟨ha, -⟩, hc⟩ := h1
  refine ⟨?_, ha⟩
  revert hc
  show (match checkW p (declCx d) d.body with | .ok _ => true | _ => false) = true → _
  cases checkW p (declCx d) d.body with
  | ok u => intro _; cases u; rfl
  | error e => intro hc; simp at hc

/-- **`ProgScopeOKW` gives `ProgCkW`.** -/
theorem progCkW_of_scopeW {p : Prog} (h : ProgScopeOKW p = true) : ProgCkW p :=
  progCkW_of_wrap (ProgScopeOKW.wrap h)

end TermA4

#print axioms TermA4.progCkW_of_wrap
#print axioms TermA4.progCkW_of_scopeW
