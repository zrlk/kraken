/-
**Lemma 1's replay direction, proved**
(`PromReplay`, Q2 of `LiveBridge.lean`). ISA-neutral and
architecture-neutral; no hypothesis.

A certifying run of the thread before the semantic promise of `w` (the
*original*, a `CertWriteN` run writing `(w, ν)` with `ν ≤ |M|`) is replayed
step by step by a run of the thread after promising `w` at `|M| + 1`, against
`M ++ [w]`, `stepOne_rsim` (`PromReplaySim.lean`). Up to the write (phase A)
the original's `coh w.loc` stays `≤ |M|` (`stepOne_cohLe` and monotonicity of
`coh`); the write is replayed as the fulfilment of `|M| + 1`; after it
(phase B) both runs hold the same messages above `|M|` and the replay
certifies when the original does. The initial threads simulate by the promise projection's
`psim_init`, with the old promises at most `|M|` because a certifying thread
has no promise above the memory (`not_certOkN_of_dead`).

Contents:
- `ThreadNPn.append`, `ThreadNPn.coh_le`;
- `rsim_init`: the initial threads simulate;
- `certOkN_of_rsim` (phase B), `replay_prefix` (phase A);
- `promReplay : PromReplay A I`.
-/
import Kraken.Promising.PromReplaySim
import Kraken.Promising.PromProjection
import Kraken.Promising.CertifySoundN2

namespace Kraken.Promising.Proj

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

theorem _root_.Kraken.Promising.Live.ThreadNPn.append {A : Arch} {tid : Nat} :
    ∀ {a b : Nat} {p q r : Thread I × Memory}, ThreadNPn A tid a p q → ThreadNPn A tid b q r →
      ThreadNPn A tid (a + b) p r := by
  intro a b p q r h₁ h₂
  induction h₁ with
  | refl n p => exact h₂.mono (by omega)
  | @step n p q' r' hs _ ih =>
    rw [show n + 1 + b = (n + b) + 1 by omega]
    exact .step hs (ih h₂)

/-- `coh` only grows along a run. -/
theorem _root_.Kraken.Promising.Live.ThreadNPn.coh_le {A : Arch} {tid : Nat} :
    ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn A tid n p q → ∀ l, p.1.views.getCoh l ≤ q.1.views.getCoh l := by
  intro n p q h
  induction h with
  | refl => exact fun _ => Nat.le_refl _
  | step hs _ ih =>
    obtain ⟨outs, o, hstep, ho, rfl⟩ := hs
    exact fun l => Nat.le_trans ((stepOne_dord A hstep ho).2.1 l) (ih l)

/-- **The initial threads simulate** (replay direction): `psim_init`, and
the original has nothing above `|M|`. -/
theorem rsim_init {M : Memory} {tid : Nat} {w : Msg} {t : Thread I} (hb : t.Bnd M.last) (hw : w.tid = tid)
    (hJ : ∀ s ∈ t.prom, s ≤ M.last) :
    (promThread t M w).RSim M tid w true (M.append w).1 t M :=
  { ps := psim_init hb hw hJ
    ownP := fun u x hu hx => by have := M.last_le_of_get?_eq_some hx; omega_t
    xclP := fun a ν l hx ha => by have := (hb.views.xclb a ν l hx).1; omega_t
    bndR :=
      have h : M.last ≤ (M.append w).1.last := by rw [Memory.last_append]; omega_t
      ⟨hb.views.mono h, hb.regs.mono h⟩ }

/-- **Phase B certifies the replay**: if the original empties its promise
set within `n` instructions and the threads simulate with `w` fulfilled, the
replay empties its promise set within `n` instructions. -/
theorem certOkN_of_rsim (A : Arch) {M : Memory} {tid : Nat} {w : Msg} :
    ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn A tid n p q → q.1.prom = [] →
      ∀ {t : Thread I} {mem : Memory}, t.RSim M tid w false mem p.1 p.2 → CertOkN A tid t mem n := by
  intro n p q h hq
  induction h with
  | refl n p =>
    intro t mem hs
    have he := hs.ps.promEq
    rw [hq] at he
    simp only [outL, Bool.false_eq_true, ↓reduceIte, List.append_nil] at he
    exact ⟨t, mem, .refl _ _, he⟩
  | @step n p q r hst _ ih =>
    intro t mem hs
    obtain ⟨outs', o', hstep', ho', rfl⟩ := hst
    obtain ⟨outs, o, out2, hstep, ho, hs2, hof, -⟩ :=
      stepOne_rsim A hs hstep' ho' (fun h => absurd h Bool.false_ne_true)
    rw [hof rfl] at hs2
    obtain ⟨t2, mem2, hr, hp⟩ := ih hq hs2
    exact ⟨t2, mem2, .step ⟨outs, o, hstep, ho, rfl⟩ hr, hp⟩

/-- **Phase A, replayed**: a run of the original that ends with
`coh w.loc ≤ |M|` is replayed by a run of the replay of the same length. -/
theorem replay_prefix (A : Arch) {M : Memory} {tid : Nat} {w : Msg} :
    ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn A tid n p q → q.1.views.getCoh w.loc ≤ M.last →
      ∀ {out : Bool} {t : Thread I} {mem : Memory}, t.RSim M tid w out mem p.1 p.2 →
        ∃ t1 mem1 out1, ThreadNPn A tid n (t, mem) (t1, mem1) ∧ t1.RSim M tid w out1 mem1 q.1 q.2 := by
  intro n p q h hq
  induction h with
  | refl n p => intro out t mem hs; exact ⟨t, mem, out, .refl _ _, hs⟩
  | @step n p q r hst hr ih =>
    intro out t mem hs
    obtain ⟨outs', o', hstep', ho', rfl⟩ := hst
    obtain ⟨outs, o, out2, hstep, ho, hs2, -, -⟩ :=
      stepOne_rsim A hs hstep' ho' (fun _ => .inl (Nat.le_trans (hr.coh_le w.loc) hq))
    obtain ⟨t1, mem1, out1, hr1, hs1⟩ := ih hq hs2
    exact ⟨t1, mem1, out1, .step ⟨outs, o, hstep, ho, rfl⟩ hr1, hs1⟩

/-- **Lemma 1, replay direction (Q2), proved**: a write `(w, ν)` of a
certifying run within `fuel` with `ν ≤ |M|` can be promised, and the thread
then certifies within the same `fuel`. -/
theorem promReplay (A : Arch) (I : ISA) : PromReplay A I := by
  intro fuel tid t mem w ν hb hcw hν
  have hw := hcw.tid
  obtain ⟨k, t1, mem1, outs', o', hk, hr1, hstep', ho', hp, hc⟩ := hcw
  -- the original certifies, so its promises are in `mem`
  have hJ : ∀ s ∈ t.prom, s ≤ mem.last := by
    intro s hs
    refine Nat.le_of_not_lt fun hlt => not_certOkN_of_dead (A := A) (tid := tid) (n := fuel) (ts := s)
      ⟨hs, .inl hlt⟩ ?_
    obtain ⟨t2, mem2, hr2, hp2⟩ := hc
    exact ⟨t2, mem2, ((hr1.tail ⟨outs', o', hstep', ho', rfl⟩).append hr2).mono (by omega), hp2⟩
  have hcoh := stepOne_cohLe A hstep' ho' hν hp
  obtain ⟨t2, mem2, out1, hr2, hs2⟩ := replay_prefix A hr1 hcoh (rsim_init hb hw hJ)
  obtain ⟨outs, o, out3, hstep, ho, hs3, -, hof⟩ :=
    stepOne_rsim A hs2 hstep' ho' (fun _ => .inr ⟨ν, hν, hp⟩)
  rw [hof ⟨ν, hν, hp⟩] at hs3
  obtain ⟨t3, mem3, hr3, hp3⟩ := hc
  obtain ⟨t4, mem4, hr4, hp4⟩ := certOkN_of_rsim A hr3 hp3 hs3
  exact ⟨t4, mem4, ((hr2.tail ⟨outs, o, hstep, ho, rfl⟩).append hr4).mono (by omega), hp4⟩

end Kraken.Promising.Proj
