/-
**The worker's segments at any call depth, their invariant inside a fragment
with frames** (hello.w): the frame-aware twin of
`Spike/Lib/SegThrS.lean`'s `SegTC`, over `Spike/Lib/HelloSegThrS.lean`'s
`OutTS` rows, every row landing with a pending frame run (`Pend`, as
`Spike/Lib/SegS.lean`'s `SegWS`).

hello's worker calls `print` (a pushed frame `uFrame`), so the flat `SegTC`
of the worker's body does not see the source's call; the worker's side
(`HelloW1.WSideH.closed`) asks its invariant closed under `OutTS` at any
frames. A segment here hides that invariant, inside the fragment `S` (the
worker's facts `WCompatH` asks: `wide`, `noSite`, `sysExec`, `sysOkH`).

- `OutTS.conjS`: a row from an `S'` state lands in `X ∧ S'`
  (`OutT.conjS` at depth).
- `NoTop`, `OutT.toTS`: a thread row at frames `fs` other than `unpk` and
  `texit` (no `unpark` binding, no `exit` call) is an `OutTS` row at `fs`
  (a callee's rows: `print`'s at `[uFrame]`).
- `SegTCS S p lbl ms P Q`: the invariant inside `S`, each row into
  `Pend p (inv ∨ Q)`.
- `SegTCS.ofTC` (a flat `SegTC` at depth `0`), `liftL` (at frames `fs`,
  its fragment `NoTop`), `ofWS` (a `SegWS` with no outside move), `step`,
  `seq`, `mono_pre`, `mono_post`, `mono_S`, `or_pre`, `empty`, `cfg`,
  `exists_pre`, `pre_run`, `post_run` (a call's frame run before the
  callee's entry, a return's after its exit; `A64CallS.call_ndS`'s
  pattern).
- `SegTCS.conjS`, `closed`, `closed_conjS`, `closed_of_back`: the closed
  invariant of a segment to the empty fragment (`WSideH.Wi`), each pair with
  a pending frame run into `S` (into `S` itself when `S` is closed under
  frame runs backwards; `Pend.state`: a state fact).
-/
import Spike.Lib.HelloSegThrS
import Spike.Lib.SegThrS

namespace Spike.Lib.HelloSegTCS

open CoreLang CoreTerm
open Kraken.Promising
open Spike.Lib Spike.Lib.HelloSegThrS

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I}

/-! ## Rows -/

/-- **An `OutTS` row from an `S'` state lands in `X ∧ S'`** (`OutT.conjS`
at depth; the kernel model keeps `S'` at every frames). -/
theorem _root_.Spike.Lib.HelloSegThrS.OutTS.conjS {S' : I.State → Prop} {X : FragS I} {s : I.State} {c : Ctl}
    {fs : List TermRun.Frame} (h : OutTS p lbl ms X s c fs) (hs : S' s) (hE : ExecKeeps I S')
    (hK : ∀ fs, KernKeeps (ms fs) S') : OutTS p lbl ms (fun s c fs => X s c fs ∧ S' s) s c fs := by
  cases h with
  | pre c₁ fs₁ hr h => exact .pre c₁ fs₁ hr (h.conjS hs hE (hK fs₁))
  | frame s' c' fs' he hr hx => exact .frame s' c' fs' he hr ⟨hx, hE _ _ _ hs he rfl⟩
  | fnc k s' c' fs' he hr hx => exact .fnc k s' c' fs' he hr ⟨hx, hE _ _ _ hs he ⟨(), rfl⟩⟩
  | top c₁ hr h => exact .top c₁ hr (h.conjS hs hE (hK []))

/-- **No thread-only row**: the control at no `unpark` binding, and a
system call under the kernel model not an `exit` (a callee's pairs:
`print`'s, whose one call is a `write`). -/
def NoTop {I : ISA} (ms : MemSide I) (s : I.State) (c : Ctl) : Prop :=
  (∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e) ∧
    ∀ K, ms.K = some K → K.atSys s = true → Scc.Sem.Kernel.decode K.nrs (K.nr s) (K.arg s) ≠ some .exit

/-- **A thread row at depth**: an `OutT` row under the memory side at `fs`
from a `NoTop` pair is an `OutTS` row at `fs` (an `OutL` row with no frame
run, a fence with the local run as a frame run). -/
theorem OutT.toTS {X : FragS I} {s : I.State} {c : Ctl} {fs : List TermRun.Frame}
    (h : OutT p lbl (ms fs) (fun s c => X s c fs) s c) (hn : NoTop (ms fs) s c) : OutTS p lbl ms X s c fs := by
  cases h with
  | outL h => exact .pre c fs (.refl _) h
  | unpk _ _ _ _ _ x a e _ _ _ _ _ _ ht => exact absurd ht (hn.1 x a e)
  | texit K a hk hat hd _ => exact absurd hd (hn.2 K hk hat)
  | fnc k s' c' he hr hx => exact .fnc k s' c' fs he (.ofLocal hr fs) hx

/-! ## Segments -/

/-- **A segment with the worker's rows at any depth whose invariant lies
inside the fragment `S`**: each row lands with a pending frame run in the
invariant or `Q`. -/
def SegTCS (S : FragS I) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide I)
    (P Q : FragS I) : Prop :=
  ∃ inv : FragS I, (∀ s c fs, P s c fs → inv s c fs) ∧ (∀ s c fs, inv s c fs → S s c fs) ∧
    ∀ s c fs, inv s c fs → OutTS p lbl ms (Pend p fun s c fs => inv s c fs ∨ Q s c fs) s c fs

/-- A state fact under a pending frame run is a fact of the state. -/
theorem Pend.state {T : I.State → Prop} {s : I.State} {c : Ctl} {fs : List TermRun.Frame}
    (h : Pend p (fun s _ _ => T s) s c fs) : T s :=
  let ⟨_, _, _, h⟩ := h; h

namespace SegTCS

variable {S S' : FragS I} {P P' Q Q' R : FragS I}

/-- **A flat segment at depth `0`** (`OutTS.ofT`). -/
theorem ofTC {S₀ P₀ Q₀ : Frag I} (h : SegTC S₀ p lbl (ms []) P₀ Q₀) (hS : ∀ s c, S₀ s c → S s c []) :
    SegTCS S p lbl ms (P₀.at []) (Q₀.at []) := by
  obtain ⟨inv, hP, hiS, ho⟩ := h
  refine ⟨inv.at [], fun s c fs ⟨h, e⟩ => ⟨hP s c h, e⟩, fun s c fs ⟨h, e⟩ => e ▸ hS s c (hiS s c h), ?_⟩
  rintro s c fs ⟨hi, rfl⟩
  refine OutTS.ofT ((ho s c hi).mono fun s c h => ?_)
  exact Pend.of (h.imp (fun h => ⟨h, rfl⟩) fun h => ⟨h, rfl⟩)

/-- **A flat segment at frames `fs`**, its fragment's pairs `NoTop`
(`OutT.toTS`; a callee's body). -/
theorem liftL {S₀ P₀ Q₀ : Frag I} (fs : List TermRun.Frame) (h : SegTC S₀ p lbl (ms fs) P₀ Q₀)
    (hS : ∀ s c, S₀ s c → S s c fs) (hn : ∀ s c, S₀ s c → NoTop (ms fs) s c) :
    SegTCS S p lbl ms (P₀.at fs) (Q₀.at fs) := by
  obtain ⟨inv, hP, hiS, ho⟩ := h
  refine ⟨inv.at fs, fun s c fs' ⟨h, e⟩ => ⟨hP s c h, e⟩, fun s c fs' ⟨h, e⟩ => e ▸ hS s c (hiS s c h), ?_⟩
  rintro s c fs' ⟨hi, rfl⟩
  refine OutT.toTS ((ho s c hi).mono fun s c h => ?_) (hn s c (hiS s c hi))
  exact Pend.of (h.imp (fun h => ⟨h, rfl⟩) fun h => ⟨h, rfl⟩)

/-- **A segment with frames and no outside move** (`OutTS.ofS`). -/
theorem ofWS (h : SegWS S (fun _ _ => False) p lbl ms P Q) : SegTCS S p lbl ms P Q :=
  let ⟨inv, hs, hw, ho⟩ := h
  ⟨inv, hs, hw, fun s c fs h => OutTS.ofS ((ho s c fs h).1 fun _ h => h)⟩

/-- **One instruction** from every pair of `P`, inside `S`, into `Q`. -/
theorem step (hS : ∀ s c fs, P s c fs → S s c fs) (h : ∀ s c fs, P s c fs → OutTS p lbl ms Q s c fs) :
    SegTCS S p lbl ms P Q :=
  ⟨P, fun _ _ _ h => h, hS, fun s c fs hp => (h s c fs hp).mono fun _ _ _ h => Pend.of (.inr h)⟩

/-- **Sequencing.** -/
theorem seq (h₁ : SegTCS S p lbl ms P Q) (h₂ : SegTCS S p lbl ms Q R) : SegTCS S p lbl ms P R := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c fs => i₁ s c fs ∨ i₂ s c fs, fun s c fs h => .inl (hs₁ s c fs h),
    fun s c fs h => h.elim (hw₁ s c fs) (hw₂ s c fs), ?_⟩
  rintro s c fs (h | h)
  · exact (ho₁ s c fs h).mono fun s c fs h => h.mono fun s c fs h =>
      h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c fs h))
  · exact (ho₂ s c fs h).mono fun s c fs h => h.mono fun s c fs h => h.elim (fun h => .inl (.inr h)) .inr

theorem mono_pre (h : SegTCS S p lbl ms P Q) (hP : ∀ s c fs, P' s c fs → P s c fs) : SegTCS S p lbl ms P' Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, fun s c fs h => hs s c fs (hP s c fs h), hw, ho⟩

theorem mono_post (h : SegTCS S p lbl ms P Q) (hQ : ∀ s c fs, Q s c fs → Q' s c fs) : SegTCS S p lbl ms P Q' :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c fs h => (ho s c fs h).mono fun _ _ _ h => h.mono fun s c fs h => h.imp_right (hQ s c fs)⟩

/-- A weaker fragment. -/
theorem mono_S (h : SegTCS S p lbl ms P Q) (hS : ∀ s c fs, S s c fs → S' s c fs) : SegTCS S' p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, fun s c fs h => hS s c fs (hw s c fs h), ho⟩

/-- A case split on the entry. -/
theorem or_pre (h : SegTCS S p lbl ms P Q) (h' : SegTCS S p lbl ms P' Q) :
    SegTCS S p lbl ms (fun s c fs => P s c fs ∨ P' s c fs) Q := by
  obtain ⟨i, hs, hw, ho⟩ := h
  obtain ⟨i', hs', hw', ho'⟩ := h'
  refine ⟨fun s c fs => i s c fs ∨ i' s c fs, fun s c fs h => h.imp (hs s c fs) (hs' s c fs),
    fun s c fs h => h.elim (hw s c fs) (hw' s c fs), ?_⟩
  rintro s c fs (h | h)
  · exact (ho s c fs h).mono fun _ _ _ h => h.mono fun _ _ _ h => h.imp_left .inl
  · exact (ho' s c fs h).mono fun _ _ _ h => h.mono fun _ _ _ h => h.imp_left .inr

/-- A segment from nowhere. -/
theorem empty (h : ∀ s c fs, ¬ P s c fs) : SegTCS S p lbl ms P Q :=
  ⟨fun _ _ _ => False, fun s c fs hP => h s c fs hP, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩

/-- **A control-flow graph** of nodes `N i`, each a segment inside `S` to
some node or the exit `X` (`SegTC.cfg` at depth). -/
theorem cfg {ι : Sort _} (N : ι → FragS I) {X : FragS I}
    (h : ∀ i, SegTCS S p lbl ms (N i) (fun s c fs => (∃ j, N j s c fs) ∨ X s c fs)) :
    SegTCS S p lbl ms (fun s c fs => ∃ i, N i s c fs) X := by
  let Inv : FragS I := fun s c fs => ∃ i, ∃ J : FragS I, (∀ s c fs, N i s c fs → J s c fs) ∧
      (∀ s c fs, J s c fs → S s c fs) ∧
      (∀ s c fs, J s c fs → OutTS p lbl ms (Pend p fun s c fs => J s c fs ∨ ((∃ j, N j s c fs) ∨ X s c fs)) s c fs) ∧
      J s c fs
  refine ⟨Inv, ?_, ?_, ?_⟩
  · rintro s c fs ⟨i, hi⟩
    obtain ⟨J, hs, hw, ho⟩ := h i
    exact ⟨i, J, hs, hw, ho, hs s c fs hi⟩
  · rintro s c fs ⟨i, J, -, hw, -, hJ⟩
    exact hw s c fs hJ
  · rintro s c fs ⟨i, J, hs, hw, ho, hJ⟩
    refine (ho s c fs hJ).mono fun s c fs hx => hx.mono fun s c fs hx => ?_
    rcases hx with hx | ⟨j, hj⟩ | hx
    · exact .inl ⟨i, J, hs, hw, ho, hx⟩
    · obtain ⟨J', hs', hw', ho'⟩ := h j
      exact .inl ⟨j, J', hs', hw', ho', hs' s c fs hj⟩
    · exact .inr hx

/-- **Ghost parameters.** -/
theorem exists_pre {γ : Sort _} {P : γ → FragS I} (h : ∀ g, SegTCS S p lbl ms (P g) Q) :
    SegTCS S p lbl ms (fun s c fs => ∃ g, P g s c fs) Q :=
  cfg P fun g => (h g).mono_post fun _ _ _ h => .inr h

/-- **A frame run before a segment, at the entry** (`SegWS.pre_run`): a
segment from `P'` is one from `P` when every pair of `P` is inside `S` and
has a pending frame run to `P'` (a caller's pair at a callee's entry, the
source's call still to take). -/
theorem pre_run (h : SegTCS S p lbl ms P' Q) (hP : ∀ s c fs, P s c fs → S s c fs ∧ Pend p P' s c fs) :
    SegTCS S p lbl ms P Q := by
  obtain ⟨inv, hs, hw, ho⟩ := h
  refine ⟨fun s c fs => inv s c fs ∨ P s c fs, fun s c fs h => .inr h,
    fun s c fs h => h.elim (hw s c fs) fun h => (hP s c fs h).1, ?_⟩
  have hX : ∀ s c fs, Pend p (fun s c fs => inv s c fs ∨ Q s c fs) s c fs →
      Pend p (fun s c fs => (inv s c fs ∨ P s c fs) ∨ Q s c fs) s c fs :=
    fun s c fs h => h.mono fun _ _ _ h => h.imp_left .inl
  rintro s c fs (h | h)
  · exact (ho s c fs h).mono hX
  · obtain ⟨c', fs', hr, h'⟩ := (hP s c fs h).2
    exact ((ho s c' fs' (hs s c' fs' h')).run hr).mono hX

/-- **A frame run after a segment** (`SegWS.post_run`): a segment to the
pairs with a pending frame run to `Q` (a callee's exit, the source's return
still to take) is one to `Q`. -/
theorem post_run (h : SegTCS S p lbl ms P (Pend p Q)) : SegTCS S p lbl ms P Q :=
  let ⟨inv, hs, hw, ho⟩ := h
  ⟨inv, hs, hw, fun s c fs hi => (ho s c fs hi).mono fun _ _ _ h => h.or_pend⟩

/-- **A kept state predicate along a segment** (`SegTC.conjS` at depth). -/
theorem conjS {S' : I.State → Prop} (h : SegTCS S p lbl ms P Q) (hE : ExecKeeps I S')
    (hK : ∀ fs, KernKeeps (ms fs) S') :
    SegTCS (fun s c fs => S s c fs ∧ S' s) p lbl ms (fun s c fs => P s c fs ∧ S' s)
      (fun s c fs => Q s c fs ∧ S' s) := by
  obtain ⟨i, hs, hw, ho⟩ := h
  refine ⟨fun s c fs => i s c fs ∧ S' s, fun s c fs h => ⟨hs s c fs h.1, h.2⟩,
    fun s c fs h => ⟨hw s c fs h.1, h.2⟩, fun s c fs h => ?_⟩
  refine ((ho s c fs h.1).conjS h.2 hE hK).mono fun s c fs ⟨⟨c', fs', hr, h⟩, hS⟩ => ?_
  exact ⟨c', fs', hr, h.imp (fun h => ⟨h, hS⟩) fun h => ⟨h, hS⟩⟩

/-- **The closed invariant** of a segment to the empty fragment
(`WSideH.Wi`): the pairs with a pending frame run into the hidden
invariant, closed under the rows (`OutTS.run`), each with a pending frame
run into `S`. -/
theorem closed (h : SegTCS S p lbl ms P (fun _ _ _ => False)) :
    ∃ Wi : FragS I, (∀ s c fs, P s c fs → Wi s c fs) ∧ (∀ s c fs, Wi s c fs → Pend p S s c fs) ∧
      ∀ s c fs, Wi s c fs → OutTS p lbl ms Wi s c fs := by
  obtain ⟨inv, hP, hS, ho⟩ := h
  refine ⟨Pend p inv, fun s c fs h => Pend.of (hP s c fs h), fun s c fs h => h.mono hS, ?_⟩
  rintro s c fs ⟨c', fs', hr, hi⟩
  exact ((ho s c' fs' hi).run hr).mono fun _ _ _ h => h.mono fun _ _ _ h => h.resolve_right id

/-- **The closed invariant inside `S`** when `S` holds at every pair whose
source runs to a pair of `S` at the same state. -/
theorem closed_of_back (h : SegTCS S p lbl ms P (fun _ _ _ => False))
    (hb : ∀ s c fs c' fs', FrameRun p (c, fs) (c', fs') → S s c' fs' → S s c fs) :
    ∃ Wi : FragS I, (∀ s c fs, P s c fs → Wi s c fs) ∧ (∀ s c fs, Wi s c fs → S s c fs) ∧
      ∀ s c fs, Wi s c fs → OutTS p lbl ms Wi s c fs := by
  obtain ⟨Wi, hP, hS, ho⟩ := h.closed
  exact ⟨Wi, hP, fun s c fs h => let ⟨c', fs', hr, h'⟩ := hS s c fs h; hb s c fs c' fs' hr h', ho⟩

/-- **The closed invariant with a kept state predicate `S'`**, from the
entry's pairs in `S'` (`SegTC.closed_conjS` at depth). -/
theorem closed_conjS {S' : I.State → Prop} (h : SegTCS S p lbl ms P (fun _ _ _ => False))
    (hE : ExecKeeps I S') (hK : ∀ fs, KernKeeps (ms fs) S') :
    ∃ Wi : FragS I, (∀ s c fs, P s c fs → S' s → Wi s c fs) ∧
      (∀ s c fs, Wi s c fs → Pend p S s c fs ∧ S' s) ∧ ∀ s c fs, Wi s c fs → OutTS p lbl ms Wi s c fs := by
  obtain ⟨Wi, hP, hS, ho⟩ := ((h.conjS hE hK).mono_post fun _ _ _ h => h.1).closed
  exact ⟨Wi, fun s c fs h h' => hP s c fs ⟨h, h'⟩, fun s c fs h =>
    ⟨(hS s c fs h).mono fun _ _ _ h => h.1, Pend.state ((hS s c fs h).mono fun _ _ _ h => h.2)⟩, ho⟩

end SegTCS

end Spike.Lib.HelloSegTCS
