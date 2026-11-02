/-
**An unmapped range stays unmapped across a segment with publication rows** (x86-64; no AArch64 twin):
`KeepUnS.SegWS.keepUn` (`Spike/Lib/X64KeepUnS.lean`) for `X64SegWPub.SegWSP`, generic (no program, layout or
frame is fixed).

- `SegWSP.keepUn`: a `SegWSP` under `unXa (ms fs) r` whose outside moves keep `r` unmapped is one under `ms` with
  `r` unmapped at its entry and its exits. A publication row is at the same state (the publication moves the
  control only), so `out_un`/`exec_un` apply to both disjuncts of `OutSP`, as `RootL1U.segInvSP_keepUn`'s.
-/
import Spike.Lib.X64KeepUnS
import Spike.Lib.X64SegWPub

namespace Spike.Lib.X64SegWPub

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib (FragS OutS Pend)
open Spike.Lib.X64.KeepUn (U unXa out_un exec_un)

variable {W : FragS isa} {K : State → State → Prop} {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat}

/-- **A `SegWSP` keeps `r` unmapped** (`KeepUnS.SegWS.keepUn` for `SegWSP`): a segment under `unXa (ms fs) r` at
every frame list whose outside moves keep `r` unmapped (`hKu`) is one under `ms` with `r` unmapped at its entry
and its exits. -/
theorem SegWSP.keepUn {ms : List TermRun.Frame → MemSide isa} {P Q : FragS isa} {r : Range}
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi) (h : SegWSP W K p lbl (fun fs => unXa (ms fs) r) P Q)
    (hKu : ∀ s c fs, W s c fs → ∀ s', K s s' → U r s → U r s') :
    SegWSP W K p lbl ms (fun s c fs => P s c fs ∧ U r s) (fun s c fs => Q s c fs ∧ U r s) := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  refine ⟨fun s c fs => inv s c fs ∧ U r s, fun s c fs hp => ⟨hP s c fs hp.1, hp.2⟩,
    fun s c fs h => hiW s c fs h.1, fun s c fs hi => ?_⟩
  obtain ⟨hout, hk⟩ := hcl s c fs hi.1
  have hmv : ∀ s c fs, (Pend p (fun s c fs => inv s c fs ∨ Q s c fs) s c fs ∧ U r s) →
      Pend p (fun s c fs => (inv s c fs ∧ U r s) ∨ (Q s c fs ∧ U r s)) s c fs :=
    fun _ _ _ ⟨⟨c', fs', hr, hx⟩, hu⟩ => ⟨c', fs', hr, hx.elim (fun h => .inl ⟨h, hu⟩) fun h => .inr ⟨h, hu⟩⟩
  have hO : ∀ c₀, OutS p lbl (fun fs => unXa (ms fs) r) (Pend p fun s c fs => inv s c fs ∨ Q s c fs) s c₀ fs →
      OutS p lbl ms (Pend p fun s c fs => (inv s c fs ∧ U r s) ∨ (Q s c fs ∧ U r s)) s c₀ fs := fun c₀ ho => by
    cases ho with
    | pre c₁ fs₁ hr ho =>
      exact .pre c₁ fs₁ hr ((out_un (hK fs₁) hi.2 ho).mono fun s c h => hmv s c fs₁ h)
    | frame s' c' fs' he hr hx =>
      exact .frame s' c' fs' he hr (hmv s' c' fs' ⟨hx, exec_un hi.2 he⟩)
  refine ⟨fun hK' => ?_, fun s' hks => ?_⟩
  · rcases hout hK' with ho | ⟨hns, hpub, c₁, hps, hy, ho⟩
    · exact .inl (hO c ho)
    · exact .inr ⟨hns, hpub, c₁, hps, ⟨hy, hi.2⟩, hO c₁ ho⟩
  · obtain ⟨c', fs', hr, hx⟩ := hk s' hks
    have hu := hKu s c fs (hiW s c fs hi.1) s' hks hi.2
    exact ⟨c', fs', hr, hx.elim (fun h => .inl ⟨h, hu⟩) fun h => .inr ⟨h, hu⟩⟩

end Spike.Lib.X64SegWPub

/-- info: 'Spike.Lib.X64SegWPub.SegWSP.keepUn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWSP.keepUn
