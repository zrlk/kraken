/-
**An unmapped range stays unmapped across a segment with frames** (AArch64): `KeepUn`'s `SegW` results over
segments with frames (`SegWS`, `Spike/Lib/SegS.lean`), generic (no program, layout or frame is fixed).

- `SegWS.mono_xa`: a segment under memory sides with larger allocation fragments (wake's `StartH0U.SegW.mono_xa`
  at every frame list).
- `SegWS.keepUn`: a segment under `unXa (ms fs) r` whose outside moves keep `r` unmapped is one under `ms` with `r`
  unmapped at its entry and its exits (`KeepUn.SegW.keepUn` at every frame list).
-/
import Spike.Lib.A64KeepUn
import Spike.Lib.A64SegInstA

namespace Spike.Lib.A64.KeepUnS

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem
open Spike.Lib (FragS SegWS OutS KOutS Pend)
open Spike.Lib.A64.KeepUn (U unXa out_un exec_un)

variable {W : FragS isaLSE2} {K : State → State → Prop} {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat}

/-- **A segment with frames under memory sides with larger allocation fragments** (`OutS.mono_xa` at every pair of
the invariant). -/
theorem SegWS.mono_xa {ms ms' : List TermRun.Frame → MemSide isaLSE2} {P Q : FragS isaLSE2}
    (h : SegWS W K p lbl ms P Q) (he : ∀ fs, ms' fs = { ms fs with xa := (ms' fs).xa })
    (hxa : ∀ fs l b n s c, (ms fs).xa l b n s c → (ms' fs).xa l b n s c) :
    SegWS W K p lbl ms' P Q := by
  obtain ⟨inv, hP, hW, hcl⟩ := h
  exact ⟨inv, hP, hW, fun s c fs hi =>
    ⟨fun hk => Spike.Lib.A64ConsumerA.OutS.mono_xa ((hcl s c fs hi).1 hk) he hxa, (hcl s c fs hi).2⟩⟩

/-- **A segment with frames keeps `r` unmapped**: a segment under `unXa (ms fs) r` at every frame list `fs` (its
allocation landings asked only with `r` unmapped) whose outside moves keep `r` unmapped (`hKu`) is one under `ms`
with `r` unmapped at its entry and its exits. -/
theorem SegWS.keepUn {ms : List TermRun.Frame → MemSide isaLSE2} {P Q : FragS isaLSE2} {r : Range}
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi) (h : SegWS W K p lbl (fun fs => unXa (ms fs) r) P Q)
    (hKu : ∀ s c fs, W s c fs → ∀ s', K s s' → U r s → U r s') :
    SegWS W K p lbl ms (fun s c fs => P s c fs ∧ U r s) (fun s c fs => Q s c fs ∧ U r s) := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  refine ⟨fun s c fs => inv s c fs ∧ U r s, fun s c fs hp => ⟨hP s c fs hp.1, hp.2⟩,
    fun s c fs h => hiW s c fs h.1, fun s c fs hi => ?_⟩
  obtain ⟨hout, hk⟩ := hcl s c fs hi.1
  have hmv : ∀ s c fs, (Pend p (fun s c fs => inv s c fs ∨ Q s c fs) s c fs ∧ U r s) →
      Pend p (fun s c fs => (inv s c fs ∧ U r s) ∨ (Q s c fs ∧ U r s)) s c fs :=
    fun _ _ _ ⟨⟨c', fs', hr, hx⟩, hu⟩ => ⟨c', fs', hr, hx.elim (fun h => .inl ⟨h, hu⟩) fun h => .inr ⟨h, hu⟩⟩
  refine ⟨fun hK' => ?_, fun s' hks => ?_⟩
  · cases hout hK' with
    | pre c₁ fs₁ hr ho =>
      exact .pre c₁ fs₁ hr ((out_un (hK fs₁) hi.2 ho).mono fun s c h => hmv s c fs₁ h)
    | frame s' c' fs' he hr hx =>
      exact .frame s' c' fs' he hr (hmv s' c' fs' ⟨hx, exec_un hi.2 he⟩)
  · obtain ⟨c', fs', hr, hx⟩ := hk s' hks
    have hu := hKu s c fs (hiW s c fs hi.1) s' hks hi.2
    exact ⟨c', fs', hr, hx.elim (fun h => .inl ⟨h, hu⟩) fun h => .inr ⟨h, hu⟩⟩

end Spike.Lib.A64.KeepUnS

/-- info: 'Spike.Lib.A64.KeepUnS.SegWS.mono_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.KeepUnS.SegWS.mono_xa

/-- info: 'Spike.Lib.A64.KeepUnS.SegWS.keepUn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.KeepUnS.SegWS.keepUn
