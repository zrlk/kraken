/-
**Lemma 1's projection direction,
proved** (`PromProjection`, Q3 of `LiveBridge.lean`). ISA-neutral and
architecture-neutral; no hypothesis.

A certifying run of the thread after the semantic promise of `w` at `|M| + 1`
(the *post-run*) is replayed step by step by a run of the thread before the
promise (the *pre-run*), `stepOne_psim` (`PromProjectionSim.lean`): while `w`
is outstanding the pre-run is one timestamp lower on fresh writes; the
post-run's fulfilment of `|M| + 1` is the pre-run's "promise now" of `w`,
with a constraining view `≤ |M|`; after it both runs hold the same messages
above `|M|`. Lemma J (`prom_le_of_certOkN_promThread`,
`PromProjectionDead.lean`) supplies the one fact about the initial threads
that `Thread.Bnd` does not: every old promise is at most `|M|`.

Contents:
- `certOkN_of_psim`: a phase-B post-run certifies the pre-run;
- `certWriteN_of_psim`: a phase-A post-run makes `w` a `CertWriteN`;
- `psim_init`: the initial threads simulate;
- `promProjection : PromProjection A I`;
- `ReachableK.of_reachableSem'`: the semantic machine is inside `ReachableK`,
  with no open hypothesis.
-/
import Kraken.Promising.PromProjectionSim
import Kraken.Promising.PromProjectionDead
import Kraken.Promising.LiveBridge

namespace Kraken.Promising.Proj

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- **Phase B certifies the pre-run**: if the post-run empties its promise
set within `n` instructions and the threads simulate with `w` already
fulfilled, the pre-run empties its promise set within `n` instructions. -/
theorem certOkN_of_psim (A : Arch) {M : Memory} {tid : Nat} {w : Msg} :
    ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn A tid n p q → q.1.prom = [] →
      ∀ {t' : Thread I} {mem' : Memory}, p.1.PSim M tid w false p.2 t' mem' → CertOkN A tid t' mem' n := by
  intro n p q h hq
  induction h with
  | refl n p =>
    intro t' mem' hs
    have he := hs.promEq
    rw [hq] at he
    simp only [outL, Bool.false_eq_true, ↓reduceIte, List.append_nil] at he
    exact ⟨t', mem', .refl _ _, he.symm⟩
  | @step n p q r hst _ ih =>
    intro t' mem' hs
    obtain ⟨outs, o, hstep, ho, rfl⟩ := hst
    obtain ⟨outs', o', out2, hstep', ho', hs2, hof, -⟩ := stepOne_psim A hs hstep ho
    rw [hof rfl] at hs2
    obtain ⟨t2, mem2, hr, hp⟩ := ih hq hs2
    exact ⟨t2, mem2, .step ⟨outs', o', hstep', ho', rfl⟩ hr, hp⟩

/-- **Phase A writes `w`**: if the post-run empties its promise set within
`n` instructions and the threads simulate with `w` outstanding, the pre-run
writes `w` as "promise now" with a constraining view `≤ |M|` within `n`
instructions and then certifies in the remaining fuel. -/
theorem certWriteN_of_psim (A : Arch) {M : Memory} {tid : Nat} {w : Msg} :
    ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn A tid n p q → q.1.prom = [] →
      ∀ {t' : Thread I} {mem' : Memory}, p.1.PSim M tid w true p.2 t' mem' →
        ∃ ν, ν ≤ M.last ∧ CertWriteN A tid t' mem' n (w, ν) := by
  intro n p q h hq
  induction h with
  | refl n p =>
    intro t' mem' hs
    have he := hs.promEq
    rw [hq] at he
    simp only [outL, ↓reduceIte] at he
    exact absurd he.symm (by simp)
  | @step n p q r hst hr ih =>
    intro t' mem' hs
    obtain ⟨outs, o, hstep, ho, rfl⟩ := hst
    obtain ⟨outs', o', out2, hstep', ho', hs2, -, hnow⟩ := stepOne_psim A hs hstep ho
    cases out2 with
    | false =>
      obtain ⟨ν, hν, hp⟩ := hnow rfl rfl
      refine ⟨ν, hν, 0, t', mem', outs', o', by omega, .refl _ _, hstep', ho', hp, ?_⟩
      rw [show n + 1 - 0 - 1 = n by omega]
      exact certOkN_of_psim A hr hq hs2
    | true =>
      obtain ⟨ν, hν, k, t1, mem1, outs1, o1, hk, hr1, hs1, ho1, hp1, hc1⟩ := ih hq hs2
      refine ⟨ν, hν, k + 1, t1, mem1, outs1, o1, by omega, .step ⟨outs', o', hstep', ho', rfl⟩ hr1, hs1, ho1,
        hp1, ?_⟩
      rw [show n + 1 - (k + 1) - 1 = n - k - 1 by omega]
      exact hc1

/-- **The initial threads simulate**: the thread after promising `w` at
`|M| + 1`, against `M ++ [w]`, and the thread before, against `M`, given
`t.Bnd |M|`, `w` of the thread, and Lemma J's conclusion. -/
theorem psim_init {M : Memory} {tid : Nat} {w : Msg} {t : Thread I} (hb : t.Bnd M.last) (hw : w.tid = tid)
    (hJ : ∀ s ∈ t.prom, s ≤ M.last) :
    (promThread t M w).PSim M tid w true (M.append w).1 t M := by
  have hnone : ∀ u x, M.last < u → M.get? u = some x → False := fun u x hu hx => by
    have := M.last_le_of_get?_eq_some hx; omega_t
  have happ : ∀ u x, M.last < u → (M.append w).1.get? u = some x → u = M.last + 1 ∧ x = w :=
    fun u x hu hx => by
      rcases Memory.get?_append_eq_some _ _ hx with ⟨-, hx'⟩ | h
      · exact (hnone u x hu hx').elim
      · exact h
  have hfwd : ∀ (mem : Memory) (out : Bool), FwdLast mem M.last out t.views := fun _ _ l f hf hlt => by
    have := hb.views.fwdTime l f hf; omega_t
  exact
    { rel :=
        { st := rfl
          rview := rfl
          wview := rfl
          views := Views.Rel.refl _ _
          prom := by
            show t.prom = (t.prom ++ [(M.append w).2]).filter (· ≤ M.last)
            rw [List.filter_append, Memory.append_time, List.filter_eq_self.mpr (fun s hs => by simpa using hJ s hs)]
            simp }
      promEq := by
        show t.prom ++ [(M.append w).2] = t.prom ++ outL M.last true
        rw [Memory.append_time]; rfl
      promLe := hJ
      memR := Memory.Prefix.append _ _
      memP := Memory.Prefix.refl _
      outW := fun _ => Memory.get?_append_last _ _
      tidR := fun u x hu hx => by rw [(happ u x hu hx).2]; exact hw
      tidP := fun u x hu hx => (hnone u x hu hx).elim
      ownR := fun u x hu hp hx => absurd (happ u x hu hx).1 (hp rfl)
      fwdR := hfwd _ _
      fwdP := hfwd _ _
      lat :=
        { fwd := fun l s x hl hx => by
            obtain ⟨y, hy, -⟩ := hl.msg
            exact absurd (happ s y hl.gt hy).1 (hl.pf rfl)
          back := fun u x hu hx => (hnone u x hu hx).elim }
      bnd := hb }

/-- **Lemma 1, projection direction (Q3), proved**: a semantic promise is
a `CertWriteN` of the pre-promise thread with a constraining view `≤ |M|`. -/
theorem promProjection (A : Arch) (I : ISA) : PromProjection A I := by
  intro fuel tid t mem w hb hw hc
  have hJ := prom_le_of_certOkN_promThread hc
  obtain ⟨t', mem', hr, hp⟩ := hc
  exact certWriteN_of_psim A hr hp (psim_init hb hw hJ)

end Kraken.Promising.Proj

namespace Kraken.Promising.Live.Bridge

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem

variable {I : ISA}

/-- **The semantic machine is inside `ReachableK`**, with no open hypothesis
(`ReachableK.of_reachableSem` at `Proj.promProjection`). -/
theorem ReachableK.of_reachableSem' {A : Arch} {fuel : Nat} {c c' : Config I} (hb : c.Bnd)
    (h : ReachableSem A fuel c c') : ReachableK A c c' :=
  ReachableK.of_reachableSem (Proj.promProjection A I) hb h

end Kraken.Promising.Live.Bridge
