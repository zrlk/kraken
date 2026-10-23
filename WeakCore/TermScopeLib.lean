import WeakCore.FlatHashMap
import WeakCore.TermScopeW
import WeakCore.TermScopeStart

/-! # TermScopeLib: scope-check and checker theorems for the MS queue and FlatHashMap

The program-side `ObligationsF` fields for the library programs
that were only `#guard`-checked before.  Every theorem is by **kernel evaluation**
(`decide +kernel`; no `native_decide`, no new axiom).

* MS queue `queueLib τ` at the three `#guard`-checked payloads (`int`, `pay`, `Ptr pub int`):
  `checkProg … = .ok ()` (`checked`), `ProgScopeOKW … = true` (`scopeW`), and `RunScope` at every
  entry-call start (`runScope`, via `TermScopeStart.runScope_entry`).
* FlatHashMap (`lib`, `instLib`, `ownLib` at their `#guard`-checked parameters): the syntactic half
  `ProgScopeOK … = true` and `RunScope` at every entry-call start.  The typing-aware half
  `ProgWrapOK` (the typing-aware pass `checkW`) is proved in `TermScopeFHM`: the checker reaches the
  well-founded `zeroableIn`, which needs the proved restatement of `TermZeroS` to kernel-reduce.
-/

namespace TermScopeLib

open CoreLang CoreTerm TermRun TermScope TermScopeStart

/-- An accepted check result is `.ok ()`. -/
theorem ok_of_accepts {r : M Unit} (h : accepts r = true) : r = .ok () := by
  cases r with
  | ok u => cases u; rfl
  | error e => simp [accepts] at h

/-! ## The MS queue -/

theorem queue_int_checked : checkProg (queueLib .int) = .ok () := ok_of_accepts (by decide +kernel)
theorem queue_pay_checked : checkProg (queueLib pay) = .ok () := ok_of_accepts (by decide +kernel)
theorem queue_ptr_checked : checkProg (queueLib (.ptr .pub .int)) = .ok () := ok_of_accepts (by decide +kernel)

theorem queue_int_scopeW : ProgScopeOKW (queueLib .int) = true := by decide +kernel
theorem queue_pay_scopeW : ProgScopeOKW (queueLib pay) = true := by decide +kernel
theorem queue_ptr_scopeW : ProgScopeOKW (queueLib (.ptr .pub .int)) = true := by decide +kernel

/-- The entry-call start shape of `runScope_entry`, for program `p`. -/
def EntryStart (p : Prog) (c0 : Cfg) : Prop :=
  ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → ∃ d ∈ p, ∃ (ts : List Ty) (ws : List Word),
    th.term = .tail d.name [] (.var "a") ts ∧ th.env = [("a", d.argTy, ws)] ∧ th.σs = [] ∧
    th.stack = [] ∧ ts.all drf = true

theorem queue_int_runScope {c0 : Cfg} (h : EntryStart (queueLib .int) c0) : RunScope c0 :=
  runScope_entry (ProgScopeOKW.scope queue_int_scopeW) h
theorem queue_pay_runScope {c0 : Cfg} (h : EntryStart (queueLib pay) c0) : RunScope c0 :=
  runScope_entry (ProgScopeOKW.scope queue_pay_scopeW) h
theorem queue_ptr_runScope {c0 : Cfg} (h : EntryStart (queueLib (.ptr .pub .int)) c0) : RunScope c0 :=
  runScope_entry (ProgScopeOKW.scope queue_ptr_scopeW) h

/-! ## FlatHashMap (syntactic half) -/

theorem fhm_lib_false_scope : ProgScopeOK (FlatHashMap.lib false) = true := by decide +kernel
theorem fhm_lib_true_scope : ProgScopeOK (FlatHashMap.lib true) = true := by decide +kernel
theorem fhm_inst_9_scope : ProgScopeOK (FlatHashMap.instLib false 9 false) = true := by decide +kernel
theorem fhm_inst_20_scope : ProgScopeOK (FlatHashMap.instLib true 20 true) = true := by decide +kernel
theorem fhm_own_false_scope : ProgScopeOK (FlatHashMap.ownLib false) = true := by decide +kernel
theorem fhm_own_true_scope : ProgScopeOK (FlatHashMap.ownLib true) = true := by decide +kernel

theorem fhm_lib_false_runScope {c0 : Cfg} (h : EntryStart (FlatHashMap.lib false) c0) : RunScope c0 :=
  runScope_entry fhm_lib_false_scope h
theorem fhm_lib_true_runScope {c0 : Cfg} (h : EntryStart (FlatHashMap.lib true) c0) : RunScope c0 :=
  runScope_entry fhm_lib_true_scope h
theorem fhm_inst_9_runScope {c0 : Cfg} (h : EntryStart (FlatHashMap.instLib false 9 false) c0) : RunScope c0 :=
  runScope_entry fhm_inst_9_scope h
theorem fhm_inst_20_runScope {c0 : Cfg} (h : EntryStart (FlatHashMap.instLib true 20 true) c0) : RunScope c0 :=
  runScope_entry fhm_inst_20_scope h
theorem fhm_own_false_runScope {c0 : Cfg} (h : EntryStart (FlatHashMap.ownLib false) c0) : RunScope c0 :=
  runScope_entry fhm_own_false_scope h
theorem fhm_own_true_runScope {c0 : Cfg} (h : EntryStart (FlatHashMap.ownLib true) c0) : RunScope c0 :=
  runScope_entry fhm_own_true_scope h

end TermScopeLib

#print axioms TermScopeLib.ok_of_accepts
#print axioms TermScopeLib.queue_int_checked
#print axioms TermScopeLib.queue_pay_checked
#print axioms TermScopeLib.queue_ptr_checked
#print axioms TermScopeLib.queue_int_scopeW
#print axioms TermScopeLib.queue_pay_scopeW
#print axioms TermScopeLib.queue_ptr_scopeW
#print axioms TermScopeLib.queue_int_runScope
#print axioms TermScopeLib.queue_pay_runScope
#print axioms TermScopeLib.queue_ptr_runScope
#print axioms TermScopeLib.fhm_lib_false_scope
#print axioms TermScopeLib.fhm_lib_true_scope
#print axioms TermScopeLib.fhm_inst_9_scope
#print axioms TermScopeLib.fhm_inst_20_scope
#print axioms TermScopeLib.fhm_own_false_scope
#print axioms TermScopeLib.fhm_own_true_scope
#print axioms TermScopeLib.fhm_lib_false_runScope
#print axioms TermScopeLib.fhm_lib_true_runScope
#print axioms TermScopeLib.fhm_inst_9_runScope
#print axioms TermScopeLib.fhm_inst_20_runScope
#print axioms TermScopeLib.fhm_own_false_runScope
#print axioms TermScopeLib.fhm_own_true_runScope
