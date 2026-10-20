/- The checkable core of CERTX (c1).  At any config satisfying `SysInvN` (in particular at
the pre-spawn config of `Step.spawn`, where the parent is promise-free), a promise-free thread `j` has
NO predicted unit at any of its unpublished own cells: a planted (frontier-carrying) unpublished own
cell exposes to readers (pub, child or otherwise) only slots below the real count. -/
import WeakCore.TermMain
open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep TermCut TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
namespace A9C1

theorem noPredU_of_noProm {Eg : GEnv} {c : Cfg} {j : Nat} {th : TTh} {S : AllocLabel → Prop} {a : Address}
    (hph : TermPredHold.PredHoldG Eg c) (hth : c.ths[j]? = some th) (hnp : th.promises = [])
    (hown : ∃ cl, Eg.sto a.label = some cl ∧ cl.owner = some j) (hnpub : ¬ Eg.pubd a.label) :
    ¬ PredU (Cut Eg j S) a := fun hq => by
  obtain ⟨h, -, hmem, -⟩ := hph j th S a hth hown hnpub hq
  rw [hnp] at hmem; cases hmem

/-- The same from the system invariant (`SysInvN.predHold`). -/
theorem noPredU_sys {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) {j : Nat} {th : TTh} {S : AllocLabel → Prop}
    {a : Address} (hth : c.ths[j]? = some th) (hnp : th.promises = [])
    (hown : ∃ cl, Eg.sto a.label = some cl ∧ cl.owner = some j) (hnpub : ¬ Eg.pubd a.label) :
    ¬ PredU (Cut Eg j S) a :=
  noPredU_of_noProm hN.predHold hth hnp hown hnpub

#print axioms noPredU_sys
#print axioms noPredU_of_noProm
end A9C1
