/-
**A segment at depth keeps its pairs `Good1`** (either ISA): for an
`Accepted1` program, a segment whose entry pairs are `Good1`
(`Spike/Lib/Frames1.lean`) has every pair of its invariant `Good1`, so it is
a segment inside `W ∧ Good1` to `Q ∧ Good1`.

A row at a `Good1` pair moves the source only by local or frame runs, which
keep `Good1` (`good1_run`): the rows at a load, a store, an exchange or a
buffer allocation are not at a `Good1` control (`Good1.not_load`, …), and a
`write` to the output is ruled out by the caller (`hnw`); the pending frame
runs after a row and the runs after an outside move are frame runs.

This lets obligations proved over all controls (the runtime's, inside
`SFacts`) be lifted to `SFactsS` at the `Good1` pairs only (`Good1 p (c, fs) →
SFactsS …`, `SFactsS.ofSFacts0`), the segment's own pairs then carrying
`SFactsS`.

- `Good1.not_xchg`: a `Good1` control is at no exchange.
- `Out.good1`, `OutS.good1`, `KOutS.good1`: the rows' landings `Good1`.
- `SegWS.good1`: the segment inside `W ∧ Good1`.
-/
import Spike.Lib.SegS
import Spike.Lib.Frames1

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising
open Scc.Lower (body1)

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}

/-- A `Good1` control is at no exchange. -/
theorem Good1.not_xchg {q : Ctl × List TermRun.Frame} (h : Good1 p q) :
    ∀ x sa u v e, ¬ XchgSite q.1 x sa u v e := by
  intro x sa u v e hx
  obtain ⟨-, ⟨a, t, pw, μ, ht, -⟩ | ⟨b, i, t, pw, ti, iws, μ, sb, k, ht, -⟩⟩ := hx <;>
  · rcases h.1 with ⟨sc, hb⟩ | ⟨i', a', ts, ht'⟩
    · rw [ht] at hb; simp [body1] at hb
    · rw [ht] at ht'; cases ht'

/-- **A row at a `Good1` control lands at `Good1` pairs** at the frames
`fs`, for an `Accepted1` program, given no `write` to the output (`hnw`). -/
theorem Out.good1 (hp : Scc.Lower.Accepted1 p = true) {ms : MemSide I} {X : Frag I} {s : I.State} {c : Ctl}
    {fs : List TermRun.Frame} (hg : Good1 p (c, fs))
    (hnw : ∀ K', ms.K = some K' → K'.atSys s = true → ∀ buf n,
      Scc.Sem.Kernel.decode K'.nrs (K'.nr s) (K'.arg s) ≠ some (.write 1 buf n))
    (h : Out p lbl ms X s c) : Out p lbl ms (fun s c => X s c ∧ Good1 p (c, fs)) s c := by
  have hl : ∀ {c'}, LocalRun p c c' → Good1 p (c', fs) := fun hr => good1_run hp (FrameRun.ofLocal hr fs) hg
  cases h with
  | silent s₁ c₂ he hr hx => exact .silent s₁ c₂ he hr ⟨hx, hl hr⟩
  | choice P t he ht hl' =>
    exact .choice P t he ht fun s₁ hs₁ => let ⟨c₂, hr, hx⟩ := hl' s₁ hs₁; ⟨c₂, hr, hx, hl hr⟩
  | load _ _ _ x a e _ _ _ ht => exact (hg.not_load x true a e ht).elim
  | store _ _ _ _ x a b e _ _ _ _ _ ht => exact (hg.not_store x true a b none e ht).elim
  | rtStore kr L V s₁ c₂ he hrt hmp hG hr hx => exact .rtStore kr L V s₁ c₂ he hrt hmp hG hr ⟨hx, hl hr⟩
  | rtLoad kl L g c₂ he hrt hmp hr hx =>
    exact .rtLoad kl L g c₂ he hrt hmp hr fun v hG ho => ⟨hx v hG ho, hl hr⟩
  | rtRmw k L op g c₂ he hrt hmp hr hx =>
    exact .rtRmw k L op g c₂ he hrt hmp hr fun old hG ho =>
      let h := hx old hG ho; ⟨h.1, h.2, hl hr⟩
  | sys K' call hK' hat hd hok hs =>
    exact .sys K' call hK' hat hd hok fun s₁ hs₁ => let ⟨c₂, hr, hx⟩ := hs s₁ hs₁; ⟨c₂, hr, hx, hl hr⟩
  | holdLoad _ _ _ x sa u v e _ hx => exact (hg.not_xchg x sa u v e hx).elim
  | xchgStore _ _ _ _ x sa u v e _ _ _ _ hx => exact (hg.not_xchg x sa u v e hx).elim
  | ctrRmw _ _ _ x τ e _ _ _ _ hs =>
    exact (hs.elim (fun ⟨a, _, _, ht, _⟩ => hg.not_newBuf x a τ e ht)
      fun ⟨_, a, _, ⟨_, ht⟩, _⟩ => hg.not_new x a _ e ht).elim
  | alloc _ _ x a τ e _ _ _ _ _ _ _ ht => exact (hg.not_newBuf x a τ e ht).elim
  | newStore _ _ _ _ x a _ e _ _ _ _ _ _ ht => exact ht.elim fun _ ht => (hg.not_new x a _ e ht).elim
  | emit K' buf n _ _ hK' hat hd _ _ _ _ => exact (hnw K' hK' hat buf n hd).elim
  | fence k s₁ c₂ he hr hx =>
    cases hr with
    | loc hr => exact .fence k s₁ c₂ he (.loc hr) ⟨hx, hl hr⟩
    | pub _ hps _ => exact (hg.noPub _ _ hps).elim

/-- **A row at depth from a `Good1` pair lands at `Good1` pairs** (`Out.good1`
after the source's frame run, which keeps `Good1`). -/
theorem OutS.good1 (hp : Scc.Lower.Accepted1 p = true) {ms : List TermRun.Frame → MemSide I} {X : FragS I}
    {s : I.State} {c : Ctl} {fs : List TermRun.Frame} (hg : Good1 p (c, fs))
    (hnw : ∀ fs' K', (ms fs').K = some K' → K'.atSys s = true → ∀ buf n,
      Scc.Sem.Kernel.decode K'.nrs (K'.nr s) (K'.arg s) ≠ some (.write 1 buf n))
    (h : OutS p lbl ms X s c fs) : OutS p lbl ms (fun s c fs => X s c fs ∧ Good1 p (c, fs)) s c fs := by
  cases h with
  | pre c₁ fs₁ hr ho => exact .pre c₁ fs₁ hr (ho.good1 hp (good1_run hp hr hg) (hnw fs₁))
  | frame s' c' fs' he hr hx => exact .frame s' c' fs' he hr ⟨hx, good1_run hp hr hg⟩

/-- **An outside move from a `Good1` pair lands at `Good1` pairs.** -/
theorem KOutS.good1 (hp : Scc.Lower.Accepted1 p = true) {K : I.State → I.State → Prop} {X : FragS I}
    {s : I.State} {c : Ctl} {fs : List TermRun.Frame} (hg : Good1 p (c, fs)) (h : KOutS K p X s c fs) :
    KOutS K p (fun s c fs => X s c fs ∧ Good1 p (c, fs)) s c fs :=
  fun s' hk => let ⟨c', fs', hr, hx⟩ := h s' hk; ⟨c', fs', hr, hx, good1_run hp hr hg⟩

/-- **A segment from `Good1` pairs is inside `W ∧ Good1`**, to `Q ∧ Good1`,
for an `Accepted1` program (`hp`), its entry pairs `Good1` (`hP`), no state
of `W` at a `Good1` pair at a `write` to the output (`hnw`). -/
theorem SegWS.good1 (hp : Scc.Lower.Accepted1 p = true) {W : FragS I} {K : I.State → I.State → Prop}
    {ms : List TermRun.Frame → MemSide I} {P Q : FragS I} (h : SegWS W K p lbl ms P Q)
    (hP : ∀ s c fs, P s c fs → Good1 p (c, fs))
    (hnw : ∀ s c fs, W s c fs → Good1 p (c, fs) → ∀ fs' K', (ms fs').K = some K' → K'.atSys s = true →
      ∀ buf n, Scc.Sem.Kernel.decode K'.nrs (K'.nr s) (K'.arg s) ≠ some (.write 1 buf n)) :
    SegWS (fun s c fs => W s c fs ∧ Good1 p (c, fs)) K p lbl ms P (fun s c fs => Q s c fs ∧ Good1 p (c, fs)) := by
  obtain ⟨inv, hPi, hiW, hcl⟩ := h
  -- a pending run's target from a `Good1` pair is `Good1`
  have hX : ∀ s c fs, (Pend p (fun s c fs => inv s c fs ∨ Q s c fs) s c fs ∧ Good1 p (c, fs)) →
      Pend p (fun s c fs => (inv s c fs ∧ Good1 p (c, fs)) ∨ (Q s c fs ∧ Good1 p (c, fs))) s c fs :=
    fun _ _ _ ⟨⟨c', fs', hr, hx⟩, hg⟩ =>
      ⟨c', fs', hr, hx.imp (fun h => ⟨h, good1_run hp hr hg⟩) fun h => ⟨h, good1_run hp hr hg⟩⟩
  refine ⟨fun s c fs => inv s c fs ∧ Good1 p (c, fs), fun s c fs h => ⟨hPi s c fs h, hP s c fs h⟩,
    fun s c fs ⟨hi, hg⟩ => ⟨hiW s c fs hi, hg⟩, ?_⟩
  rintro s c fs ⟨hi, hg⟩
  obtain ⟨hout, hk⟩ := hcl s c fs hi
  exact ⟨fun hK => ((hout hK).good1 hp hg (hnw s c fs (hiW s c fs hi) hg)).mono hX,
    (hk.good1 hp hg).mono fun _ _ _ ⟨hx, hg'⟩ => hx.imp (fun h => ⟨h, hg'⟩) fun h => ⟨h, hg'⟩⟩

end Spike.Lib
