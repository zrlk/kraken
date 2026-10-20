/-
The no-fault shape of the thread rules.

`succsL` drops faulting outcomes, and the rules' weakest preconditions
(`EvTree.EraseWPR`, `EvTree.EraseWPRD`, `EvTree.All`) treat a `.fault` leaf
as `True`, so a rule proves nothing about faults. This file adds, without
changing any rule, the stricter variant in which a fault is `False`:

- `EvTree.NoFault` (`SeqLinkTerm.lean`): the tree has no `.fault` leaf and
  every `choose` is nonempty (structural; every cell of the lock and MP
  programs is of this shape under its invariant);
- `EvTree.NoFaultRun`: no run of the tree from a context reaches a fault
  (`runTree` has no `.error` outcome); `EvTree.NoFault.run`;
- `stepOne_noFault`: then the instruction has no fault outcome;
- `NoFaultRule R`: a `ThreadRuleRX` whose `wp` also yields `False` at
  `.fault`: under exactly the hypotheses of `R.wp`, the tree has no faulting
  run. Together with `R.wp` this is the weakest precondition with
  `.fault ↦ False` (the runs `EraseWPRD` quantifies over are those of
  `runTree`). `NoFaultRule.not_faultStep`: at a configuration where those
  hypotheses hold, thread `tid` has no `Config.FaultStep`.

Per-rule instances: `SLR/SwpNoFault.lean`, `SLR/X64SpinNoFault.lean`,
`SLR/MpNoFault.lean`. The no-fault theorem and its open lemma:
`SLR/Sim/CertExtOpen.lean`.
-/
import Kraken.Promising.SLR.ThreadRuleX
import Kraken.Promising.Faults
import Kraken.Promising.SeqLinkTerm

namespace Kraken.Promising

variable {I : ISA}

/-! ## Trees without faults -/

/-- No run of the tree from `cx` reaches a fault. -/
def EvTree.NoFaultRun (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} (cx : Ctx) (tree : EvTree σ) : Prop :=
  ∀ m, (.error m : Except String (σ × Ctx)) ∉ runTree A tid iv cx tree

section Run

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- A tree without fault leaves (`EvTree.NoFault`) has no faulting run, from
any context. -/
theorem EvTree.NoFault.run {σ : Type} {tree : EvTree σ} (h : tree.NoFault) :
    ∀ cx, tree.NoFaultRun A tid iv cx := by
  induction tree with
  | done s => intro cx m hm; simp [runTree] at hm
  | fault _ => exact h.elim
  | choose n k ih =>
    intro cx m hm
    simp only [runTree, List.mem_flatMap] at hm
    obtain ⟨i, -, hi⟩ := hm
    exact ih i (h.2 i) _ m hi
  | load k xcl l ret ih =>
    intro cx m hm
    simp only [runTree, List.mem_flatMap] at hm
    obtain ⟨x, -, hx⟩ := hm
    exact ih _ (h _) _ m hx
  | store k xcl l v ret ih =>
    intro cx m hm
    simp only [runTree, List.mem_append] at hm
    rcases hm with hm | hm
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at hm
      obtain ⟨-, c', -, hc⟩ := hm
      exact ih true (h true) _ m hc
    · rw [List.mem_ite_nil_right] at hm
      exact ih false (h false) _ m hm.2
  | fence k ret ih =>
    intro cx m hm
    simp only [runTree] at hm
    exact ih () h _ m hm
  | rmw k noRet l op ret ih =>
    intro cx m hm
    simp only [runTree, List.mem_flatMap] at hm
    obtain ⟨⟨tr, old, c'⟩, -, hx⟩ := hm
    simp only at hx
    split at hx
    · exact ih old (h old) _ m hx
    · rw [List.mem_flatMap] at hx
      obtain ⟨c'', -, hc⟩ := hx
      exact ih old (h old) _ m hc

end Run

/-- **No faulting run, no fault outcome.** If every tree the thread may run
next has no faulting run from its start context, `stepOne` has no `.error`
outcome. -/
theorem stepOne_noFault (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    (h : ∀ tree, I.exec t.st = some tree → tree.NoFaultRun A tid (instrViews t (I.deps t.st))
      { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] })
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs) (m : String) :
    (.error m : Except String (Outcome I)) ∉ outs := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    intro ho
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m' =>
      simp only [List.mem_singleton, Except.error.injEq] at ho
      subst ho
      exact h tree hex m hr
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp at ho

/-- **No faulting run, no `FaultStep`.** -/
theorem Config.not_faultStep_of_noFaultRun (A : Arch) {c : Config I} {tid : Nat} {t : Thread I}
    (ht : c.threads[tid]? = some t)
    (h : ∀ tree, I.exec t.st = some tree → tree.NoFaultRun A tid (instrViews t (I.deps t.st))
      { views := t.views, prom := t.prom, mem := c.mem, log := [.instr tid (I.showInstr t.st)] })
    (m : String) : ¬ c.FaultStep A tid m := by
  rintro ⟨outs, hs, ho⟩
  simp only [stepThread, ht, Option.bind_eq_bind, Option.bind_some] at hs
  exact stepOne_noFault A h hs m ho

namespace SLR

/-! ## The stricter rule -/

/-- **A rule whose `wp` yields `False` at `.fault`.** Under exactly the
hypotheses of `R.wp`, no run of the next instruction's tree from the
instruction's start context reaches a fault. (Additive: `ThreadRuleRX` and
every existing rule are unchanged.) -/
structure NoFaultRule {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRX A B tid) : Prop where
  noFault : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), R.Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.NoFaultRun A tid (instrViews t (I.deps t.st)) (ctx₀ t tid c.mem)

/-- `NoFaultRule` from the structural form: under the hypotheses of `R.wp`
the tree has no fault leaf. -/
theorem NoFaultRule.ofNoFault {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    {R : ThreadRuleRX A B tid}
    (h : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
      (tree : EvTree I.State), R.Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
      c.threads[tid]? = some t → I.exec t.st = some tree →
      Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
      (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) → tree.NoFault) :
    NoFaultRule R :=
  ⟨fun rF t tree hI he hg ht hex E hinv hwf hnp =>
    (h rF t tree hI he hg ht hex E hinv hwf hnp).run A tid _ _⟩

/-- **The no-fault rule at a configuration.** Where the hypotheses of
`R.wp` hold for thread `tid` (an instance `Inv` at `c₀`, an environment
extension to `c`, an erasure of `c`, the machine invariants), thread `tid`
has no faulting step at `c`. -/
theorem NoFaultRule.not_faultStep {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    {R : ThreadRuleRX A B tid} (hR : NoFaultRule R) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) {t : Thread I} (hI : R.Inv cl c₀ r g₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g)
    (ht : c.threads[tid]? = some t) (E : Erase (setRes rF tid r) g (fun _ => True) c) (hinv : c.MachInv)
    (hwf : c.WfProm tid) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) (m : String) :
    ¬ c.FaultStep A tid m :=
  Config.not_faultStep_of_noFaultRun A ht
    (fun tree hex => hR.noFault rF t tree hI he hg ht hex E hinv hwf hnp) m

/-- A `ThreadRuleR` is a no-fault rule (through `toRX`) when its own `wp`
hypotheses exclude faults (the instance `Inv` already at `c`). -/
theorem NoFaultRule.ofR {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    {R : ThreadRuleR A B tid}
    (h : ∀ {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (t : Thread I) (tree : EvTree I.State),
      R.Inv cl c r g → c.threads[tid]? = some t → I.exec t.st = some tree → tree.NoFault) :
    NoFaultRule R.toRX :=
  ⟨fun _ t tree hI he hg ht hex _ _ _ _ => (h t tree (R.env hI he hg) ht hex).run A tid _ _⟩

end SLR

end Kraken.Promising
