import WeakCore.FlatHashMap
import WeakCore.TermScopeW
import WeakCore.TermZeroS
import WeakCore.TermScopeLib

/-! # TermScopeFHM: the typing-aware scope check and the checker on FlatHashMap

`ProgScopeOKW … = true` (the syntactic check `ProgScopeOK` and the typing-aware pass
`ProgWrapOK`) and `checkProg … = .ok ()` for FlatHashMap's `lib`, `instLib` and `ownLib` at their
`#guard`-checked parameters.

The checkers call `CoreLang.zeroableIn` (at `newBuf` and at every zero-kinded type argument), which
is defined by well-founded recursion and does not kernel-reduce.  Each theorem is therefore proved by
`zero_decide` (`TermZeroS`): delta-expand the checker down to `zeroableIn`, rewrite it by the proved
`TermZeroS.zeroableIn_eq` into the structurally recursive `zeroPair`, and evaluate in the kernel
(`decide +kernel`).  No `native_decide`, no new axiom.
-/

namespace TermScopeFHM

open CoreLang CoreTerm TermScope FlatHashMap TermScopeLib

/-! ## `ProgScopeOKW` -/

theorem fhm_lib_false_scopeW : ProgScopeOKW (lib false) = true := by zero_decide
theorem fhm_lib_true_scopeW : ProgScopeOKW (lib true) = true := by zero_decide
theorem fhm_inst_9_scopeW : ProgScopeOKW (instLib false 9 false) = true := by zero_decide
theorem fhm_inst_20_scopeW : ProgScopeOKW (instLib true 20 true) = true := by zero_decide
theorem fhm_own_false_scopeW : ProgScopeOKW (ownLib false) = true := by zero_decide
theorem fhm_own_true_scopeW : ProgScopeOKW (ownLib true) = true := by zero_decide

/-! ## `checkProg` -/

theorem fhm_lib_false_checked : checkProg (lib false) = .ok () := ok_of_accepts (by zero_decide)
theorem fhm_lib_true_checked : checkProg (lib true) = .ok () := ok_of_accepts (by zero_decide)
theorem fhm_inst_9_checked : checkProg (instLib false 9 false) = .ok () := ok_of_accepts (by zero_decide)
theorem fhm_inst_20_checked : checkProg (instLib true 20 true) = .ok () := ok_of_accepts (by zero_decide)
theorem fhm_own_false_checked : checkProg (ownLib false) = .ok () := ok_of_accepts (by zero_decide)
theorem fhm_own_true_checked : checkProg (ownLib true) = .ok () := ok_of_accepts (by zero_decide)

end TermScopeFHM

#print axioms TermScopeFHM.fhm_lib_false_scopeW
#print axioms TermScopeFHM.fhm_lib_true_scopeW
#print axioms TermScopeFHM.fhm_inst_9_scopeW
#print axioms TermScopeFHM.fhm_inst_20_scopeW
#print axioms TermScopeFHM.fhm_own_false_scopeW
#print axioms TermScopeFHM.fhm_own_true_scopeW
#print axioms TermScopeFHM.fhm_lib_false_checked
#print axioms TermScopeFHM.fhm_lib_true_checked
#print axioms TermScopeFHM.fhm_inst_9_checked
#print axioms TermScopeFHM.fhm_inst_20_checked
#print axioms TermScopeFHM.fhm_own_false_checked
#print axioms TermScopeFHM.fhm_own_true_checked
