/-
Whole-thread environment (`EnvG`): **the AArch64 no-fault rule**
`NoFaultRule (ThreadRuleRX.ofSafelyEnvG …)`.

The rule link's `LinkNF` (`EnvG/RuleNoFault.lean`) at `QA64` asks a no-fault
live tree judgment (`TreeJLiveNF`, no `fault` law) of the thread's tree.
`exec_treeJLive_of_instrStepEnv'` gives only `TreeJLive` judgments (with a
`fault` law), and `Effects.AllEnv` does not make every fault leaf `False`:
`toEv` turns an `undefined` value of a register or flags type into a fault
leaf, while `AllEnv` of `undefined` is `∀ v, …` (`unimplemented` and
`unaligned_sp` are `False` in `AllEnv`). So the code's trees must be
fault-free, `DirsNoFault e` (`EnvLinkTermAArch64.lean`, decided per program
by `dirs_no_fault`): a `TreeJLiveNF` read on fault-free trees is a
`TreeJLive` (`TreeJLiveNF.onNoFault`), and the thread's tree is fault-free
(`noFault_of_codeAt`).

- `linkNF_QA64`: `LinkNF` at `QA64` from `DirsNoFault e`.
- `noFault_ofSafelyEnvG_promFree`: no faulting run of a promise-free thread.
- `noFaultRule_ofSafelyEnvG`: `NoFaultRule` under `EnvGAnswersAt`.

`DirsNoFault e` alone suffices, with or without promises:
`noFaultRule_ofSafelyEnvG_struct` (`EnvG/A64Answers.lean`).
-/
import Kraken.Promising.SLR.EnvG.A64Link
import Kraken.Promising.SLR.EnvG.RuleNoFault
import Kraken.Promising.EnvLinkTermAArch64

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

/-- **A no-fault live judgment on fault-free trees is a live judgment**:
`W t g := t.NoFault → J.W t g` (the `fault` law holds vacuously). -/
def TreeJLiveNF.onNoFault {E : SharedEnv} {σ : Type} (J : TreeJLiveNF E σ) : TreeJLive E σ where
  W t g := t.NoFault → J.W t g
  Post := J.Post
  done h _ := J.done h
  fault h := h.elim
  choose h hn := J.choose fun i => h i (hn.2 i)
  load h₁ h₂ hn := J.load h₁ fun v g' hs => h₂ v g' hs (hn v)
  store h₁ h₂ hn := J.store h₁ fun b g' hs => h₂ b g' hs (hn b)
  rmw h₁ h₂ hn := J.rmw h₁ fun v g' hs => h₂ v g' hs (hn v)
  fence h₁ h₂ hn := J.fence h₁ fun g' hs => h₂ g' hs hn

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **The thread's tree is fault-free** at a pc whose directive has a
fault-free tree (`DirNoFault`), with no declarations. -/
theorem noFault_of_codeAt {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)} (he : st.exe = e) (hds : st.decls = {})
    (hcode : e.codeAt st.st.2 = (d, z) :: rest) (hnf : DirNoFault e d z) :
    ∀ tree, isa.exec st = some tree → tree.NoFault := by
  intro tree htree
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hds hcode hat ⊢
  subst he hds
  have hdir : ({ exe, endPc, st := (s, pc), showPc, decls := {} } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  simp only [isa, exec, hdir, Option.isNone_some, Bool.or_false] at htree
  split at htree
  · cases htree
  · cases htree
    refine (EvTree.noFault_map (σ := MachineState) (τ := State) _ _).mpr ?_
    unfold Executable.step
    letI := Executable.labels exe
    simp only
    rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
    simp only [Directives.interp]
    exact hnf s pc

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
  {endPc : Int64} {post : MachineState × EStateA → Prop}

/-- **`LinkNF` at `QA64`**: `exec_treeJLive_of_instrStepEnv'` at
`TreeJLiveNF.onNoFault`, with the thread's tree fault-free by
`DirsNoFault e`. -/
theorem linkNF_QA64 (hlive : e.rmwLive = true) (hnf : DirsNoFault e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkNF (I := isa) A tid pl (QA64 A tid pl e endPc post) := by
  intro J st σ tree h hex hJ
  obtain ⟨he, hds, hend, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, hk⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · obtain ⟨d, z, rest, hcode, -⟩ := id hR
    exact exec_treeJLive_of_instrStepEnv' J.onNoFault he hds hR
      (fun m g' hz => hJ _ _ ⟨he, hds, hend, hk _ hz⟩) hlive tree hex
      (noFault_of_codeAt he hds hcode (hnf d z (mem_of_codeAt hcode)) tree hex)

/-- **No fault for a promise-free thread** proved by `ofSafelyEnvG`: under
the hypotheses of the rule's `wp`, `t.prom = []` and fault-free code
(`DirsNoFault e`), no run of the thread's tree faults. -/
theorem noFault_ofSafelyEnvG_promFree {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) {cl : Prop} {c₀ c : Config isa} {r : Res} {g₀ g : Ghost} (rF : Nat → Res)
    (t : Thread isa) (tree : EvTree isa.State)
    (h : (ThreadRuleRX.ofSafelyEnvG hpl hlive hshape hpost hstuck hB).Inv cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : isa.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) (hp : t.prom = []) :
    tree.NoFaultRun A tid (instrViews t (isa.deps t.st)) (ctx₀ t tid c.mem) :=
  noFault_ofEnvG_promFree _ _ (linkNF_QA64 hlive hnf hpost) rF t tree h he hg ht hex E hm hp

/-- **The AArch64 no-fault rule**: `NoFaultRule (ofSafelyEnvG …)` for
fault-free code (`DirsNoFault e`), under the missing fact `EnvGAnswersAt`
(for promise-free threads see `noFault_ofSafelyEnvG_promFree`).
`EnvGAnswersAt` is believed false for threads with a pure own promise (see
`EnvGAnswers`), so this may be vacuous; `DirsNoFault e` alone suffices:
use `noFaultRule_ofSafelyEnvG_struct` (`EnvG/A64Answers.lean`). -/
theorem noFaultRule_ofSafelyEnvG {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e.instrStepEnv (EnvGA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFault e) (hans : EnvGAnswersAt (I := isa) A tid pl) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvG hpl hlive hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG _ _ (linkNF_QA64 hlive hnf hpost) hans

end Link

end Kraken.Promising.AArch64.EnvG
