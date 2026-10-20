/-
**Checkpointed trace replay**: a long witness checked
in segments, each a separate kernel evaluation, so the kernel's memory is
bounded by the longest segment rather than the whole trace.

A segment replays a trace from a checkpoint configuration `c` and compares
the result with the next checkpoint `d` by `reachCfgBeq` (thread `==` and
memory `==`, which the kernel evaluates). Thread `==` is equality only on
threads with the same static part (`ISA.LawfulState`), so the comparison is
completed by `ReachSameStatic c0 d`: the checkpoint has the static parts of
the initial configuration, as every configuration reachable from it does
(`reachable_sameStatic`; an instruction does not change the static part, a
promise does not touch the state). `reach_segment` chains segments,
`reach_witness_promise_from` ends the chain with the final check.
-/
import Kraken.Promising.ReachCertCore

namespace Kraken.Promising

variable {I : ISA}

/-- Two configurations have threads with the same static parts. -/
def ReachSameStatic [L : I.LawfulState] (c d : Config I) : Prop :=
  ∀ i : Nat, (c.threads[i]?).map (fun t => L.static t.st) = (d.threads[i]?).map (fun t => L.static t.st)

theorem ReachSameStatic.trans [I.LawfulState] {a b c : Config I} (h₁ : ReachSameStatic a b)
    (h₂ : ReachSameStatic b c) : ReachSameStatic a c := fun i => (h₁ i).trans (h₂ i)

theorem ReachSameStatic.symm [I.LawfulState] {a b : Config I} (h : ReachSameStatic a b) :
    ReachSameStatic b a := fun i => (h i).symm

private theorem reach_sameStatic_withThread [L : I.LawfulState] {c : Config I} {tid : Nat} {t t' : Thread I}
    (ht : c.threads[tid]? = some t) (hs : L.static t'.st = L.static t.st) (mem : Memory) :
    ReachSameStatic c (c.withThread tid t' mem) := by
  intro i
  obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp ht
  simp only [Config.withThread, Array.set!, Array.getElem?_setIfInBounds]
  by_cases hi : tid = i
  · subst hi
    simp [hlt, hget, hs]
  · simp [hi]

/-- Every configuration reachable from `c` has `c`'s static parts. -/
theorem reachable_sameStatic [L : I.LawfulState] {A : Arch} {fuel : Nat} {c c' : Config I}
    (h : Reachable A fuel c c') : ReachSameStatic c c' := by
  induction h with
  | refl => exact fun _ => rfl
  | step hs _ ih =>
    refine ReachSameStatic.trans ?_ ih
    cases succs_cases hs with
    | instr ht hstep ho => exact reach_sameStatic_withThread ht (stepOne_static A hstep ho) _
    | promise ht _ =>
      apply reach_sameStatic_withThread ht
      rfl

/-- Thread-wise `==` and memory `==`: what a checkpoint comparison
evaluates. -/
def reachCfgBeq (c d : Config I) : Bool :=
  c.threads.size == d.threads.size && (List.range c.threads.size).all (fun i => c.threads[i]? == d.threads[i]?) &&
    c.mem == d.mem

theorem reach_eq_of_cfgBeq [L : I.LawfulState] {c d : Config I} (hs : ReachSameStatic c d)
    (h : reachCfgBeq c d = true) : c = d := by
  simp only [reachCfgBeq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hsz, hall⟩, hmem⟩ := h
  obtain ⟨ct, cm⟩ := c
  obtain ⟨dt, dm⟩ := d
  simp only at hsz hall hmem
  subst hmem
  congr
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < ct.size
  · have hb := hall i hi
    have hsi := hs i
    simp only at hsi
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem (hsz ▸ hi)] at hb hsi ⊢
    simp only [Option.map_some, Option.some.injEq] at hsi
    have hb' : (ct[i] == dt[i]) = true := hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := (Thread.beq_iff _ _).mp hb'
    have h1 := L.eq_of_beq _ _ h1 hsi
    revert h1 h2 h3 h4 h5
    cases ct[i]
    cases dt[i]
    intro h1 h2 h3 h4 h5
    simp_all
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

/-- A segment: replaying `tr` from `c` gives the checkpoint `d`. -/
def reachPSeg (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    (fuel : Nat) (c : Config I) (tr : List ReachPStep) (d : Config I) : Bool :=
  match reachPRun ex dp A fuel c tr with
  | some c' => reachCfgBeq c' d
  | none => false

/-- **Chaining a segment**: if `c` is reachable from `c0` and replaying `tr`
from `c` gives `d` (up to `==`), with `d` having `c0`'s static parts, then
`d` is reachable from `c0`. -/
theorem reach_segment [I.LawfulState] (A : Arch) (fuel : Nat) {ex : I.State → Option (EvTree I.State)}
    {dp : I.State → InstrDeps I.RegId} (hex : ex = I.exec) (hdp : dp = I.deps) {c0 c d : Config I}
    {tr : List ReachPStep} (h0 : Reachable A fuel c0 c) (hs : ReachSameStatic c0 d)
    (h : reachPSeg ex dp A fuel c tr d = true) : Reachable A fuel c0 d := by
  subst hex hdp
  unfold reachPSeg at h
  split at h
  · rename_i c' hc
    have hr := Reachable.trans A fuel h0 (reachPRun_sound A fuel hc)
    have he := reach_eq_of_cfgBeq ((reachable_sameStatic hr).symm.trans hs) h
    exact he ▸ hr
  · cases h

/-- `reach_witness_promise` from a configuration reachable from `c0`: the
last segment of a checkpointed witness. -/
theorem reach_witness_promise_from [I.LawfulState] (A : Arch) (fuel : Nat)
    {ex : I.State → Option (EvTree I.State)} {dp : I.State → InstrDeps I.RegId} (hex : ex = I.exec)
    (hdp : dp = I.deps) {c0 c : Config I} (h0 : Reachable A fuel c0 c) {tr : List ReachPStep}
    {P : Config I → Prop} [DecidablePred P] (h : reachPCheck ex dp A fuel c tr (fun c => decide (P c)) = true) :
    ∃ c', Reachable A fuel c0 c' ∧ c'.final = true ∧ P c' :=
  let ⟨c', hr, hf, hp⟩ := reach_witness_promise A fuel hex hdp h
  ⟨c', Reachable.trans A fuel h0 hr, hf, hp⟩

end Kraken.Promising

#print axioms Kraken.Promising.reach_segment
#print axioms Kraken.Promising.reach_witness_promise_from
