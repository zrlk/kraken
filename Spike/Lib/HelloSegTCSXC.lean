/-
**More combinators for segments with a fact at every landing pair** (hello.w, row 5j-wit-W; the `SegTCSX` twins
of `SegTCS`'s combinators outside `Spike/Lib/HelloSegTCS.lean`): the ones the spawned child's segment chain uses
(`A64HelloPrintTCS`'s `SegTCS.seq_or`, `HelloMsW`'s `SegTCS.withBW`, `A64HelloWorkerSegP`'s `SegTCS.of_imp`),
`HelloSegTCS`'s `ofWS`, and a plain segment whose landings are in `X` once `X` holds before every pending frame
run into `S` or the exit (`ofPend`).

Release note: each `SegTCS` lemma of the child's chain that gets an `X` twin here or in the `*X` files becomes a
one-line corollary through `SegTCSX.toS`, or is deleted, when the `X` chain replaces it; the release keeps one
chain.

- `SegTCSX.ofPend`: a `SegTCS` segment is a `SegTCSX` one when `X` holds at every pair with a pending frame run
  into `S` or `Q`.
- `SegTCSX.ofWS`: a `SegWS` segment with no outside move, under the same premise.
- `SegTCSX.seq_or`: sequencing on one branch.
- `SegTCSX.of_imp`: a segment under a proposition.
- `SegTCSX.withBW`: a segment under the memory sides `ms` is one under `(ms ·).withBW bo we`.
-/
import Spike.Lib.HelloSegTCSX
import Spike.Lib.HelloMsW

namespace Spike.Lib.HelloSegTCSX.SegTCSX

open CoreLang CoreTerm
open Kraken.Promising
open Spike.Lib Spike.Lib.HelloSegThrS Spike.Lib.HelloSegTCS

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I}
  {S X P Q Y : FragS I}

/-- **A plain segment landing in `X`**: `X` at every pair with a pending frame run into `S` or `Q` (the hidden
invariant lies in `S`). -/
theorem ofPend (h : SegTCS S p lbl ms P Q)
    (hX : ∀ s c fs, Pend p (fun s c fs => S s c fs ∨ Q s c fs) s c fs → X s c fs) : SegTCSX S X p lbl ms P Q :=
  let ⟨inv, hs, hw, ho⟩ := h
  ⟨inv, hs, hw, fun s c fs h => hX s c fs (Pend.of (.inl (hw s c fs h))), fun s c fs h =>
    (ho s c fs h).mono fun s c fs h => ⟨hX s c fs (h.mono fun s c fs h => h.imp_left (hw s c fs)), h⟩⟩

/-- **A segment with frames and no outside move** (`SegTCS.ofWS`), landing in `X` as `ofPend`. -/
theorem ofWS (h : SegWS S (fun _ _ => False) p lbl ms P Q)
    (hX : ∀ s c fs, Pend p (fun s c fs => S s c fs ∨ Q s c fs) s c fs → X s c fs) : SegTCSX S X p lbl ms P Q :=
  ofPend (SegTCS.ofWS h) hX

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
    fun hn => empty fun _ _ _ h => hn h.1

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

/-- **A flat segment at frames `fs` before a segment**, its fragment's pairs `NoTop` (`liftL`; its exit in `X`
through the next segment's invariant). -/
theorem liftL_seq {S₀ P₀ Q₀ : Frag I} {R : FragS I} (fs : List TermRun.Frame) (h₁ : SegTC S₀ p lbl (ms fs) P₀ Q₀)
    (hS : ∀ s c, S₀ s c → S s c fs) (hn : ∀ s c, S₀ s c → NoTop (ms fs) s c) (hX : ∀ s c, S₀ s c → X s c fs)
    (h₂ : SegTCSX S X p lbl ms (Q₀.at fs) R) : SegTCSX S X p lbl ms (P₀.at fs) R := by
  obtain ⟨inv, hP, hiS, ho⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, hx₂, ho₂⟩ := h₂
  refine ⟨fun s c fs' => (inv s c ∧ fs' = fs) ∨ i₂ s c fs', fun s c fs' ⟨h, e⟩ => .inl ⟨hP s c h, e⟩,
    fun s c fs' h => h.elim (fun ⟨h, e⟩ => e ▸ hS s c (hiS s c h)) (hw₂ s c fs'),
    fun s c fs' h => h.elim (fun ⟨h, e⟩ => e ▸ hX s c (hiS s c h)) (hx₂ s c fs'), ?_⟩
  rintro s c fs' (⟨hi, rfl⟩ | h)
  · refine OutT.toTS ((ho s c hi).mono fun s c h => ?_) (hn s c (hiS s c hi))
    rcases h with h | h
    · exact ⟨hX s c (hiS s c h), Pend.of (.inl (.inl ⟨h, rfl⟩))⟩
    · exact ⟨hx₂ s c fs' (hs₂ s c fs' ⟨h, rfl⟩), Pend.of (.inl (.inr (hs₂ s c fs' ⟨h, rfl⟩)))⟩
  · exact (ho₂ s c fs' h).mono fun s c fs h => ⟨h.1, h.2.mono fun s c fs h => h.imp_left .inr⟩

/-- **A segment under the memory sides `ms`** is one under `(ms ·).withBW bo we`. -/
theorem withBW {bo : I.State → Nat → Ctl → (Ctl → Prop) → Prop} {we : I.State → Ctl → Prop}
    (h : SegTCSX S X p lbl ms P Q)
    (hbo : ∀ fs s a c Q, (ms fs).bo s a c Q → bo s a c Q) (hwe : ∀ fs s c, (ms fs).we s c → we s c) :
    SegTCSX S X p lbl (fun fs => (ms fs).withBW bo we) P Q :=
  let ⟨inv, hP, hS, hX, hcl⟩ := h
  ⟨inv, hP, hS, hX, fun s c fs hi => HelloMsW.OutTS.withBW (hcl s c fs hi) hbo hwe⟩

end Spike.Lib.HelloSegTCSX.SegTCSX

/-- info: 'Spike.Lib.HelloSegTCSX.SegTCSX.ofPend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSegTCSX.SegTCSX.ofPend

/-- info: 'Spike.Lib.HelloSegTCSX.SegTCSX.ofWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSegTCSX.SegTCSX.ofWS

/-- info: 'Spike.Lib.HelloSegTCSX.SegTCSX.seq_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSegTCSX.SegTCSX.seq_or

/-- info: 'Spike.Lib.HelloSegTCSX.SegTCSX.of_imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSegTCSX.SegTCSX.of_imp

/-- info: 'Spike.Lib.HelloSegTCSX.SegTCSX.withBW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSegTCSX.SegTCSX.withBW
