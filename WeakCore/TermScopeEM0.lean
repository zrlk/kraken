import WeakCore.EM0
import WeakCore.TermZeroS
import WeakCore.TermScopeLib
import WeakCore.ExtArmZ

/-! # TermScopeEM0: the program-side obligations of EM0 and its finals (E3)

For `EM0.em0` at the wrapper start `TermStartW.startW em0 2`:

* `em0_checked : checkProg em0 = .ok ()`, `em0_scopeW : ProgScopeOKW em0 = true`, and the wrapper's
  `check`/`checkW` at `wcx`: kernel evaluation through `TermZeroS.zero_decide` (the checkers reach the
  well-founded `zeroableIn`, at `hello`'s `newBuf` and `main`'s `zero[Int]`), as `TermScopeFHM`;
  no `native_decide`, no new axiom.
* `em0_initShape`, `em0_initOK`: the start is an `InitShape`/`InitOK` start (`TermStartW.initShape_startW`).
* `em0_oblX`: `ObligationsFX` at `Sp := Spawn … 2 ∨ Ext` (every field proved for EM0).
* `machine_tokens_main_hello`, `token_unique_net_hello`, `token_unique_final_hello`, `reachable_typed_hello`:
  `ExtArmZ`'s EM0 finals at this program and start.

These are soundness facts (typing, token uniqueness) along every run.  They say nothing about the
output; see `EM0`'s header for what the bounded search checks about the trace (R1, R2).
-/

namespace TermScopeEM0

open CoreLang CoreTerm CoreTyping TermRun TermScope TermStartW TermScopeLib EM0
open TermSound TermMem TermStep TermCut TermSys TermMain TermExtStep TermSpawn
open WeakMem (Arch AllocLabel Ts)

theorem em0_checked : checkProg em0 = .ok () := TermScopeLib.ok_of_accepts (by zero_decide)
theorem em0_scopeW : ProgScopeOKW em0 = true := by zero_decide
theorem em0_wrap_check : check em0 wcx (wrapTerm (mainRet em0)) = .ok () := TermScopeLib.ok_of_accepts (by zero_decide)
theorem em0_wrap_checkW : checkW em0 wcx (wrapTerm (mainRet em0)) = .ok () := TermScopeLib.ok_of_accepts (by zero_decide)

/-- The EM0 start is an `InitShape` start. -/
theorem em0_initShape : TermInit.InitShape em0 (startW em0 2) := initShape_startW em0_wrap_check em0_wrap_checkW

/-- The EM0 start is an `InitOK` start. -/
theorem em0_initOK {k : Promises.Knobs} {arch : Arch} {Init : Res} :
    InitOK em0 k arch Init (fun _ => True) (startW em0 2) :=
  initOK_of em0_initShape trivial

/-- EM0's run relation besides `Step`: a spawn (capacity 2) or an extern step. -/
abbrev SpE (k : Promises.Knobs) (arch : Arch) : Cfg → Cfg → Prop :=
  fun c c' => TermSpawnStep.Spawn em0 k arch 2 c c' ∨ Ext em0 k arch c c'

/-- **EM0's obligations**. -/
theorem em0_oblX {k : Promises.Knobs} {arch : Arch} {Init : Res} :
    ObligationsFX em0 k arch (SpE k arch) Init (fun _ => True) (startW em0 2) :=
  ⟨em0_checked, em0_scopeW, runScope_startW em0 2⟩

/-- **`machine_tokens_main_em0` for EM0.** -/
theorem machine_tokens_main_hello {k : Promises.Knobs} {arch : Arch} {Init : Res}
    (hk : k.storeDepRts = true) {c : Cfg} (hr : StepsE em0 k arch 2 (startW em0 2) c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvN em0 k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧
      (AllNoProm c → SysInvW em0 k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
        ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j) ∧
      ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK em0 η ∧ Typed em0 cx th.term ∧
        FInvR ρ η th.σs (ResumeR em0 th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
        MemInv (gOf em0 k arch c i) (CE η) (stOf c.mem c.pairs th) :=
  ExtArmZ.machine_tokens_main_em0 (em0_oblX (Init := Init)) hk (em0_initOK (Init := Init)) hr

/-- **`token_unique_net_em0` for EM0.** -/
theorem token_unique_net_hello {k : Promises.Knobs} {arch : Arch} {Init : Res}
    (hk : k.storeDepRts = true) {c : Cfg} (hr : StepsE em0 k arch 2 (startW em0 2) c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      FrameTie em0 k arch c Eg Tot ∧ SysInvN em0 k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      ∀ n, Debt c db (.rg n) = 0 →
      ∀ i j, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  ExtArmZ.token_unique_net_em0 (em0_oblX (Init := Init)) hk (em0_initOK (Init := Init)) hr

/-- **`token_unique_final_em0` for EM0.** -/
theorem token_unique_final_hello {k : Promises.Knobs} {arch : Arch} {Init : Res}
    (hk : k.storeDepRts = true) {c : Cfg} (hr : StepsE em0 k arch 2 (startW em0 2) c) (hn : AllNoProm c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie em0 k arch c Eg Tot ∧ ∀ i j n, i < c.ths.size → j < c.ths.size →
      1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  ExtArmZ.token_unique_final_em0 (em0_oblX (Init := Init)) hk (em0_initOK (Init := Init)) hr hn

/-- **`reachable_typed_em0` for EM0.** -/
theorem reachable_typed_hello {k : Promises.Knobs} {arch : Arch} {Init : Res}
    (hk : k.storeDepRts = true) {c : Cfg} (hr : StepsE em0 k arch 2 (startW em0 2) c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie em0 k arch c Eg Tot :=
  ExtArmZ.reachable_typed_em0 (em0_oblX (Init := Init)) hk (em0_initOK (Init := Init)) hr

end TermScopeEM0

#print axioms TermScopeEM0.em0_checked
#print axioms TermScopeEM0.em0_scopeW
#print axioms TermScopeEM0.em0_wrap_check
#print axioms TermScopeEM0.em0_wrap_checkW
#print axioms TermScopeEM0.em0_initShape
#print axioms TermScopeEM0.em0_initOK
#print axioms TermScopeEM0.em0_oblX
#print axioms TermScopeEM0.machine_tokens_main_hello
#print axioms TermScopeEM0.token_unique_net_hello
#print axioms TermScopeEM0.token_unique_final_hello
#print axioms TermScopeEM0.reachable_typed_hello
