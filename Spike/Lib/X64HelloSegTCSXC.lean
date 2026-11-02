/-
**More combinators for segments with a fact at every landing pair, for the x86-64 hello twin**: the `SegTCSX`
combinators (`Spike/Lib/HelloSegTCSX.lean`) the x86-64 spawned child's segment chain uses. The thread and worker
bodies lift their flat prologues with `ofTC_seq`, `print`'s chain sequences one branch with `seq_or`, and the
worker's segments under a proposition use `of_imp`.

- `SegTCSX.seq_or`: sequencing on one branch.
- `SegTCSX.of_imp`: a segment under a proposition.
- `SegTCSX.ofTC_seq`: a flat segment at depth `0` before a segment.

## Differences from the AArch64 version
`Spike/Lib/HelloSegTCSXC.lean`.
- Only the combinators the x86-64 chain uses are twinned (`ofPend`, `ofWS`, `liftL_seq` and `withBW` are not).
  So the module imports `Spike/Lib/HelloSegTCSX.lean` alone, not `HelloMsW`, whose `OutTS.withBW` only `withBW`
  needs.
- The lemmas are in `Spike.Lib.X64HelloSegTCSX.SegTCSX`, not in `SegTCSX`'s own namespace, so they are not
  available through dot notation: call them as `SegTCSX.seq_or h₁ h₂` with `Spike.Lib.X64HelloSegTCSX` open.
  Their statements are unchanged.
-/
import Spike.Lib.HelloSegTCSX

namespace Spike.Lib.X64HelloSegTCSX.SegTCSX

open CoreLang CoreTerm
open Kraken.Promising
open Spike.Lib Spike.Lib.HelloSegThrS Spike.Lib.HelloSegTCS
open Spike.Lib.HelloSegTCSX (SegTCSX)

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I}
  {S X P Q Y : FragS I}

/-- **Sequencing on one branch**: a segment to `Q ∨ Y`, then one from `Y` to `R`, is one to `Q ∨ R`. -/
theorem seq_or {R : FragS I} (h₁ : SegTCSX S X p lbl ms P (fun s c fs => Q s c fs ∨ Y s c fs))
    (h₂ : SegTCSX S X p lbl ms Y R) : SegTCSX S X p lbl ms P (fun s c fs => Q s c fs ∨ R s c fs) := by
  obtain ⟨i₁, hs₁, hw₁, hx₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, hx₂, ho₂⟩ := h₂
  refine ⟨fun s c fs => i₁ s c fs ∨ i₂ s c fs, fun s c fs h => .inl (hs₁ s c fs h),
    fun s c fs h => h.elim (hw₁ s c fs) (hw₂ s c fs), fun s c fs h => h.elim (hx₁ s c fs) (hx₂ s c fs), ?_⟩
  rintro s c fs (h | h)
  · exact (ho₁ s c fs h).mono fun s c fs h => ⟨h.1, h.2.mono fun s c fs h => by
      rcases h with h | h | h
      · exact .inl (.inl h)
      · exact .inr (.inl h)
      · exact .inl (.inr (hs₂ s c fs h))⟩
  · exact (ho₂ s c fs h).mono fun s c fs h => ⟨h.1, h.2.mono fun s c fs h =>
      h.elim (fun h => .inl (.inr h)) fun h => .inr (.inr h)⟩

/-- **A segment under a proposition.** -/
theorem of_imp {A : Prop} (h : A → SegTCSX S X p lbl ms P Q) :
    SegTCSX S X p lbl ms (fun s c fs => A ∧ P s c fs) Q :=
  (Classical.em A).elim (fun ha => (h ha).mono_pre fun _ _ _ h => h.2)
    fun hn => SegTCSX.empty fun _ _ _ h => hn h.1

/-- **A flat segment at depth `0` before a segment**: its fragment in `S` and `X`; its exit, the next segment's
entry, in `X` through the next segment's invariant (`ofTC` needs no `X` at the flat exit). -/
theorem ofTC_seq {S₀ P₀ Q₀ : Frag I} {R : FragS I} (h₁ : SegTC S₀ p lbl (ms []) P₀ Q₀)
    (hS : ∀ s c, S₀ s c → S s c []) (hX : ∀ s c, S₀ s c → X s c []) (h₂ : SegTCSX S X p lbl ms (Q₀.at []) R) :
    SegTCSX S X p lbl ms (P₀.at []) R := by
  obtain ⟨inv, hP, hiS, ho⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, hx₂, ho₂⟩ := h₂
  refine ⟨fun s c fs => (inv s c ∧ fs = []) ∨ i₂ s c fs, fun s c fs ⟨h, e⟩ => .inl ⟨hP s c h, e⟩,
    fun s c fs h => h.elim (fun ⟨h, e⟩ => e ▸ hS s c (hiS s c h)) (hw₂ s c fs),
    fun s c fs h => h.elim (fun ⟨h, e⟩ => e ▸ hX s c (hiS s c h)) (hx₂ s c fs), ?_⟩
  rintro s c fs (⟨hi, rfl⟩ | h)
  · refine OutTS.ofT ((ho s c hi).mono fun s c h => ?_)
    rcases h with h | h
    · exact ⟨hX s c (hiS s c h), Pend.of (.inl (.inl ⟨h, rfl⟩))⟩
    · exact ⟨hx₂ s c [] (hs₂ s c [] ⟨h, rfl⟩), Pend.of (.inl (.inr (hs₂ s c [] ⟨h, rfl⟩)))⟩
  · exact (ho₂ s c fs h).mono fun s c fs h => ⟨h.1, h.2.mono fun s c fs h => h.imp_left .inr⟩

end Spike.Lib.X64HelloSegTCSX.SegTCSX

/-- info: 'Spike.Lib.X64HelloSegTCSX.SegTCSX.seq_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSegTCSX.SegTCSX.seq_or

/-- info: 'Spike.Lib.X64HelloSegTCSX.SegTCSX.of_imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSegTCSX.SegTCSX.of_imp

/-- info: 'Spike.Lib.X64HelloSegTCSX.SegTCSX.ofTC_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSegTCSX.SegTCSX.ofTC_seq
