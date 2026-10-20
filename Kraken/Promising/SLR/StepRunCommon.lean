/-
**Machine-step helpers shared by path arguments**.
ISA-neutral.

The ticket lock proof's dispenser argument (`SLR/DispenserRun.lean`,
`SLR/DispenserFresh.lean`) proved three facts about one machine step that
do not mention the dispenser. They are stated here once, in
`Kraken.Promising.SLR`, for later path arguments:

- `stepOne_run`: the successful outcomes of `stepOne` are runs of the
  instruction's tree (`runTree`) from the thread's promises and the memory,
  with the thread's state, promises and memory taken from the run;
- `optFence_mem_prom`: an optional `fenceStep` keeps the context's memory and
  promises;
- `succ_cases'`: a machine step (`succs`) is an instruction step or a promise
  step (`succs_cases`, with the successor as an equation).

The ticket lock proof's copies (`SingleRmw.stepOne_run`, `SingleRmw.optFence_mem_prom`,
`SingleRmw.succ_cases'`) are unchanged; a later round may alias them to these
(same statements).
-/
import Kraken.Promising.SLR.PromiseFulfil
import Kraken.Promising.PromiseSafe
import Kraken.Promising.ReleasePrefix

namespace Kraken.Promising.SLR

open Kraken.Promising

variable {I : ISA}

/-- An optional fence (`if b then fenceStep c k else c`) keeps the context's
memory and promises. -/
theorem optFence_mem_prom (c : Ctx) (b : Bool) (k : FenceKind) :
    (if b then fenceStep c k else c).mem = c.mem ∧ (if b then fenceStep c k else c).prom = c.prom := by
  split
  · exact fenceStep_mem_prom c k
  · exact ⟨rfl, rfl⟩

/-- **The successful outcomes of `stepOne`, in full**: runs of the
instruction's tree from the context `stepOne` builds (the instruction's
views `instrViews`, the thread's views and promises, the memory, the
instruction's log entry), with the outcome's state, promises, memory and log
taken from the run, and its views those of the run but `vCAP`
(`finishInstr_relKey`). The shared body of `stepOne_run`,
`EnvG.TicketX2.stepOne_runV` and `Live.TicketStep.stepOne_out`. -/
theorem stepOne_runK (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    ∃ tree c', I.exec t.st = some tree ∧
      .ok (o.thread.st, c') ∈ runTree A tid (instrViews t (I.deps t.st))
        { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } tree ∧
      o.thread.prom = c'.prom ∧ ({ o.thread.views with vCAP := 0 } : Views) = { c'.views with vCAP := 0 } ∧
      o.mem = c'.mem ∧ o.log = c'.log := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok q =>
      obtain ⟨st, c'⟩ := q
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      refine ⟨tree, c', rfl, ?_, (finishInstr_relKey hth).1, (finishInstr_relKey hth).2, rfl, rfl⟩
      show Except.ok (th.st, c') ∈ _
      rw [finishInstr_st hth]
      exact hr

/-- The successful outcomes of `stepOne` are runs of the instruction's tree
from the thread's promises and the memory, with the thread's promises and
state taken from the run. -/
theorem stepOne_run (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    ∃ tree iv c', I.exec t.st = some tree ∧
      .ok (o.thread.st, c') ∈
        runTree A tid iv { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } tree ∧
      o.thread.prom = c'.prom ∧ o.mem = c'.mem :=
  let ⟨tree, c', hex, hr, hp, _, hm, _⟩ := stepOne_runK A hstep ho
  ⟨tree, _, c', hex, hr, hp, hm⟩

/-- A machine step is an instruction step or a promise step (`succs_cases`,
with the successor as an equation). -/
theorem succ_cases' {A : Arch} [I.LawfulState] {fuel : Nat} {c c' : Config I} (hs : c' ∈ (succs A c fuel).1) :
    (∃ tid t outs o, c.threads[tid]? = some t ∧ stepOne A t tid c.mem = some outs ∧ .ok o ∈ outs ∧
      c' = c.withThread tid o.thread o.mem) ∨
    (∃ tid t p, c.threads[tid]? = some t ∧ CertWrite A tid t c.mem p ∧
      c' = c.withThread tid { t with prom := t.prom ++ [(c.mem.append { p.1 with tid }).2] }
        (c.mem.append { p.1 with tid }).1) := by
  cases succs_cases hs with
  | instr ht hstep ho => exact .inl ⟨_, _, _, _, ht, hstep, ho, rfl⟩
  | promise ht hcw => exact .inr ⟨_, _, _, ht, hcw, rfl⟩

end Kraken.Promising.SLR

#print axioms Kraken.Promising.SLR.optFence_mem_prom
#print axioms Kraken.Promising.SLR.stepOne_run
#print axioms Kraken.Promising.SLR.succ_cases'
