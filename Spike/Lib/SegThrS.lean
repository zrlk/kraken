/-
**A state predicate kept along a segment with the thread rows**
(`SegT.conjS`, `WCompat.wide`).

`SegT p lbl ms P Q` hides its invariant. A fact `S` of the target state
alone that every instruction keeps (each leaf of `I.exec`) and that the
kernel model keeps (each state a system call resumes in, each `write`
return) holds of the whole invariant once it holds at the entry: every
row's successor is a leaf of the instruction's tree or a kernel return.
The exception is `Out.alloc`, which does not land in the invariant (it lands
in `ms.xa`), so it needs nothing.

- `ExecKeeps`, `KernKeeps`: the two closure premises.
- `silentTree_leafy`: a silent tree's leaves satisfy its predicate and are
  leaves (`TreeLeaf`) of the tree.
- `Out.conjS`, `OutL.conjS`, `OutT.conjS`: a row from an `S` state is a row
  into `X ∧ S`.
- `SegT.conjS`: a segment from `P ∧ S` has an invariant inside `S`, closed
  under the rows into the invariant or `Q ∧ S` (`SegTS`).
- `SegTS.toT`, `closedS_of_segT`: forget `S`; the closed invariant inside `S`
  of a segment to the empty fragment (the worker's `WSide.Wi` with
  `WCompat.wide`).
- `SegTS.ofT`, `step`, `seq`, `loop`, `mono_pre`, `mono_post`, `mono_S`,
  `or_pre`, `cfg`, `exists_pre`; `SegW.toTS`: `SegT`'s and `SegW`'s
  combinators with the invariant inside `S`, for a fact that each node proves
  of its own states (the worker's pcs off the transfer sites,
  `WCompat.noSite`).
- `SegTC`, `SegTS.toC`, `SegW.toTC`, `SegTC.toT`, `toS`, `step`, `seq`,
  `mono_pre`, `mono_post`, `mono_S`, `cfg`, `exists_pre`, `conjS`,
  `closed_conjS`: the same with the invariant inside a fragment (state and
  control: the worker's store point, `WCompat.pass`).
-/
import Spike.Lib.SegThr
import Spike.Lib.SegW
import Scc.Sem.Wide

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising
open Kraken.Promising.Lower (SilentTree)
open Scc.Sem (TreeLeaf)

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}

/-- **Every instruction keeps `S`**: each leaf of the tree `I.exec` gives
from an `S` state is an `S` state. -/
def ExecKeeps (I : ISA) (S : I.State → Prop) : Prop :=
  ∀ s t s', S s → I.exec s = some t → TreeLeaf t s' → S s'

/-- **The kernel model keeps `S`**: from an `S` state, every state a system
call resumes in (`Kernel.certSuccs`) and every return (`Abi.ret`) is an `S`
state. -/
def KernKeeps (ms : MemSide I) (S : I.State → Prop) : Prop :=
  ∀ K, ms.K = some K → ∀ s, S s → (∀ call, ∀ s' ∈ Scc.Sem.Kernel.certSuccs K s call, S s') ∧ ∀ r, S (K.ret s r)

/-- **A silent tree's leaves**: they satisfy its predicate and are leaves of
the tree. -/
theorem silentTree_leafy {σ : Type} {P : σ → Prop} :
    ∀ {t : EvTree σ}, SilentTree P t → SilentTree (fun s => P s ∧ TreeLeaf t s) t
  | .done _, h => ⟨h, rfl⟩
  | .choose _ k, h => ⟨h.1, fun i =>
      SilentTree.mono (fun s (h : P s ∧ TreeLeaf (k i) s) => ⟨h.1, i, h.2⟩) (silentTree_leafy (h.2 i))⟩
  | .fault _, h => h.elim
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .fence .., h => h.elim
  | .rmw .., h => h.elim

variable {S : I.State → Prop} {X : Frag I} {s : I.State} {c : Ctl}

/-- **An `Out` row from an `S` state lands in `X ∧ S`.** -/
theorem Out.conjS (h : Out p lbl ms X s c) (hs : S s) (hE : ExecKeeps I S) (hK : KernKeeps ms S) :
    Out p lbl ms (fun s c => X s c ∧ S s) s c := by
  cases h with
  | silent s' c' he hr hx => exact .silent s' c' he hr ⟨hx, hE _ _ _ hs he rfl⟩
  | choice P t he hst hx =>
    exact .choice _ t he (silentTree_leafy hst) fun s' ⟨hp, hl⟩ =>
      let ⟨c', hr, h⟩ := hx s' hp; ⟨c', hr, h, hE _ _ _ hs he hl⟩
  | load kl A g x a e ty w he ht hev hv hx htag =>
    exact .load kl A g x a e ty w he ht hev hv (fun v w' hr h => ⟨hx v w' hr h, hE _ _ _ hs he ⟨v, rfl⟩⟩) htag
  | store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag =>
    exact .store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb ⟨hx, hE _ _ _ hs he ⟨true, rfl⟩⟩ htag
  | rtStore kr L V s' c' he hrt hm hG hr hx =>
    exact .rtStore kr L V s' c' he hrt hm hG hr ⟨hx, hE _ _ _ hs he ⟨true, rfl⟩⟩
  | rtLoad kl L g c' he hrt hm hr hx =>
    exact .rtLoad kl L g c' he hrt hm hr fun v hG ho => ⟨hx v hG ho, hE _ _ _ hs he ⟨v, rfl⟩⟩
  | rtRmw k L op g c' he hrt hm hr hx =>
    exact .rtRmw k L op g c' he hrt hm hr fun old hG ho =>
      ⟨(hx old hG ho).1, (hx old hG ho).2, hE _ _ _ hs he ⟨old, rfl⟩⟩
  | sys K call hk ha hd hok hx =>
    exact .sys K call hk ha hd hok fun s' hm =>
      let ⟨c', hr, h⟩ := hx s' hm; ⟨c', hr, h, (hK K hk s hs).1 call s' hm⟩
  | holdLoad kl A g x sa u v e he hx hA hh hX =>
    exact .holdLoad kl A g x sa u v e he hx hA hh fun r w' hr h => ⟨hX r w' hr h, hE _ _ _ hs he ⟨r, rfl⟩⟩
  | xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX =>
    exact .xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv ⟨hX, hE _ _ _ hs he ⟨true, rfl⟩⟩
  | ctrRmw k op g x τ e n he hrt hm hsite hh hop hX =>
    exact .ctrRmw k op g x τ e n he hrt hm hsite hh hop fun old hG ho hc hl =>
      ⟨(hX old hG ho hc hl).1, (hX old hG ho hc hl).2, hE _ _ _ hs he ⟨old, rfl⟩⟩
  | alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX =>
    exact .alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX
  | newStore kr A V s' x a ty e w wold old hN he hm ht hev hu hv hh hold hA hc hX =>
    exact .newStore kr A V s' x a ty e w wold old hN he hm ht hev hu hv hh hold hA hc hX
  | emit K buf n Pw Qw hk ha hd h0 hb hr hq =>
    exact .emit K buf n Pw Qw hk ha hd h0 hb (fun j hj c1 hp r hm hok =>
      ⟨⟨(hr j hj c1 hp r hm hok).1, (hK K hk s hs).2 r⟩, (hr j hj c1 hp r hm hok).2⟩) hq
  | fence k s' c' he hr hx => exact .fence k s' c' he hr ⟨hx, hE _ _ _ hs he ⟨(), rfl⟩⟩

/-- **An `OutL` row from an `S` state lands in `X ∧ S`.** -/
theorem OutL.conjS (h : OutL p lbl ms X s c) (hs : S s) (hE : ExecKeeps I S) (hK : KernKeeps ms S) :
    OutL p lbl ms (fun s c => X s c ∧ S s) s c := by
  cases h with
  | out h => exact .out (h.conjS hs hE hK)
  | ldSt kl A g x a e ty w V he ht hev hv hn hy htag =>
    exact .ldSt kl A g x a e ty w V he ht hev hv (fun v h => ⟨hn v h, hE _ _ _ hs he ⟨v, rfl⟩⟩)
      (fun v w' h hr hr' => ⟨hy v w' h hr hr', hE _ _ _ hs he ⟨v, rfl⟩⟩) htag

/-- **An `OutT` row from an `S` state lands in `X ∧ S`.** -/
theorem OutT.conjS (h : OutT p lbl ms X s c) (hs : S s) (hE : ExecKeeps I S) (hK : KernKeeps ms S) :
    OutT p lbl ms (fun s c => X s c ∧ S s) s c := by
  cases h with
  | outL h => exact .outL (h.conjS hs hE hK)
  | unpk k A B op g x a e ty jw he hrt hmp hop ht hh hev hv hA hX =>
    exact .unpk k A B op g x a e ty jw he hrt hmp hop ht hh hev hv hA fun old hg ho =>
      ⟨(hX old hg ho).1, (hX old hg ho).2, hE _ _ _ hs he ⟨old, rfl⟩⟩
  | texit K a hk hat hd ht => exact .texit K a hk hat hd ht
  | fnc k s' c' he hr hx => exact .fnc k s' c' he hr ⟨hx, hE _ _ _ hs he ⟨(), rfl⟩⟩

/-- **A segment with the thread rows whose invariant lies inside `S`**:
`SegT` with the invariant named inside `S`. -/
def SegTS (S : I.State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I)
    (P Q : Frag I) : Prop :=
  ∃ inv : Frag I, (∀ s c, P s c → inv s c) ∧ (∀ s c, inv s c → S s) ∧
    ∀ s c, inv s c → OutT p lbl ms (fun s c => inv s c ∨ Q s c) s c

/-- Forget `S`. -/
theorem SegTS.toT {P Q : Frag I} (h : SegTS S p lbl ms P Q) : SegT p lbl ms P Q :=
  let ⟨i, hs, _, ho⟩ := h
  ⟨i, hs, ho⟩

/-- **A kept state predicate along a segment**: from `P ∧ S`, the segment's
invariant cut down to `S` is closed under the rows into it or `Q ∧ S`. -/
theorem SegT.conjS {P Q : Frag I} (h : SegT p lbl ms P Q) (hE : ExecKeeps I S) (hK : KernKeeps ms S) :
    SegTS S p lbl ms (fun s c => P s c ∧ S s) (fun s c => Q s c ∧ S s) := by
  obtain ⟨i, hs, ho⟩ := h
  refine ⟨fun s c => i s c ∧ S s, fun s c h => ⟨hs s c h.1, h.2⟩, fun _ _ h => h.2, fun s c h => ?_⟩
  exact ((ho s c h.1).conjS h.2 hE hK).mono fun s c ⟨h, hS⟩ => h.imp (fun h => ⟨h, hS⟩) fun h => ⟨h, hS⟩

/-! ## Segments inside `S`, composed

`SegTS S` is also how a fact of the state that is not kept by every step (a
pc off the transfer sites) rides along a segment: each node proves it of its
own states (`step`), and the combinators below carry it, as `SegW`'s do. -/

namespace SegTS

variable {P P' Q Q' R : Frag I}

/-- A segment is one inside the trivial predicate. -/
theorem ofT (h : SegT p lbl ms P Q) : SegTS (fun _ => True) p lbl ms P Q :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, hs, fun _ _ _ => trivial, ho⟩

/-- **One instruction** from every pair of `P`, inside `S`, into `Q`. -/
theorem step (hS : ∀ s c, P s c → S s) (h : ∀ s c, P s c → OutT p lbl ms Q s c) : SegTS S p lbl ms P Q :=
  ⟨P, fun _ _ h => h, hS, fun s c hp => (h s c hp).mono fun _ _ h => .inr h⟩

/-- **Sequencing.** -/
theorem seq (h₁ : SegTS S p lbl ms P Q) (h₂ : SegTS S p lbl ms Q R) : SegTS S p lbl ms P R := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), fun s c h => h.elim (hw₁ s c) (hw₂ s c), ?_⟩
  rintro s c (h | h)
  · exact (ho₁ s c h).mono fun s c h => h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c h))
  · exact (ho₂ s c h).mono fun s c h => h.elim (fun h => .inl (.inr h)) .inr

/-- **A tail-call loop.** -/
theorem loop {H X : Frag I} (h : SegTS S p lbl ms H (fun s c => H s c ∨ X s c)) : SegTS S p lbl ms H X := by
  obtain ⟨i, hs, hw, ho⟩ := h
  refine ⟨i, hs, hw, fun s c hi => (ho s c hi).mono fun s c h => ?_⟩
  rcases h with h | h | h
  · exact .inl h
  · exact .inl (hs s c h)
  · exact .inr h

theorem mono_pre (h : SegTS S p lbl ms P Q) (hP : ∀ s c, P' s c → P s c) : SegTS S p lbl ms P' Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, fun s c h => hs s c (hP s c h), hw, ho⟩

theorem mono_post (h : SegTS S p lbl ms P Q) (hQ : ∀ s c, Q s c → Q' s c) : SegTS S p lbl ms P Q' :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c h => (ho s c h).mono fun s c h => h.imp_right (hQ s c)⟩

/-- A weaker predicate. -/
theorem mono_S {S' : I.State → Prop} (h : SegTS S p lbl ms P Q) (hS : ∀ s, S s → S' s) :
    SegTS S' p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, fun s c h => hS s (hw s c h), ho⟩

/-- A case split on the entry. -/
theorem or_pre (h : SegTS S p lbl ms P Q) (h' : SegTS S p lbl ms P' Q) :
    SegTS S p lbl ms (fun s c => P s c ∨ P' s c) Q := by
  obtain ⟨i, hs, hw, ho⟩ := h
  obtain ⟨i', hs', hw', ho'⟩ := h'
  refine ⟨fun s c => i s c ∨ i' s c, fun s c h => h.imp (hs s c) (hs' s c),
    fun s c h => h.elim (hw s c) (hw' s c), ?_⟩
  rintro s c (h | h)
  · exact (ho s c h).mono fun s c h => h.imp_left .inl
  · exact (ho' s c h).mono fun s c h => h.imp_left .inr

/-- **A control-flow graph** of nodes `N i`, each a segment inside `S` to
some node or the exit `X`. -/
theorem cfg {ι : Sort _} (N : ι → Frag I) {X : Frag I}
    (h : ∀ i, SegTS S p lbl ms (N i) (fun s c => (∃ j, N j s c) ∨ X s c)) :
    SegTS S p lbl ms (fun s c => ∃ i, N i s c) X := by
  let Inv : Frag I := fun s c => ∃ i, ∃ J : Frag I, (∀ s c, N i s c → J s c) ∧ (∀ s c, J s c → S s) ∧
      (∀ s c, J s c → OutT p lbl ms (fun s c => J s c ∨ ((∃ j, N j s c) ∨ X s c)) s c) ∧ J s c
  refine ⟨Inv, ?_, ?_, ?_⟩
  · rintro s c ⟨i, hi⟩
    obtain ⟨J, hs, hw, ho⟩ := h i
    exact ⟨i, J, hs, hw, ho, hs s c hi⟩
  · rintro s c ⟨i, J, -, hw, -, hJ⟩
    exact hw s c hJ
  · rintro s c ⟨i, J, hs, hw, ho, hJ⟩
    refine (ho s c hJ).mono fun s c h => ?_
    rcases h with h | ⟨j, hj⟩ | h
    · exact .inl ⟨i, J, hs, hw, ho, h⟩
    · obtain ⟨J', hs', hw', ho'⟩ := h j
      exact .inl ⟨j, J', hs', hw', ho', hs' s c hj⟩
    · exact .inr h

/-- **Ghost parameters.** -/
theorem exists_pre {γ : Sort _} {P : γ → Frag I} {X : Frag I} (h : ∀ g, SegTS S p lbl ms (P g) X) :
    SegTS S p lbl ms (fun s c => ∃ g, P g s c) X :=
  cfg P fun g => (h g).mono_post fun _ _ h => .inr h

/-- **A kept predicate along a segment inside `S`** (`SegT.conjS` over
`SegTS`): from `P ∧ S'`, `S'` kept by every instruction and the kernel
model, the invariant lies inside `S ∧ S'`. -/
theorem conjS {S' : I.State → Prop} (h : SegTS S p lbl ms P Q) (hE : ExecKeeps I S') (hK : KernKeeps ms S') :
    SegTS (fun s => S s ∧ S' s) p lbl ms (fun s c => P s c ∧ S' s) (fun s c => Q s c ∧ S' s) := by
  obtain ⟨i, hs, hw, ho⟩ := h
  refine ⟨fun s c => i s c ∧ S' s, fun s c h => ⟨hs s c h.1, h.2⟩, fun s c h => ⟨hw s c h.1, h.2⟩,
    fun s c h => ?_⟩
  exact ((ho s c h.1).conjS h.2 hE hK).mono fun s c ⟨h, hS⟩ => h.imp (fun h => ⟨h, hS⟩) fun h => ⟨h, hS⟩

/-- **The closed invariant inside `S ∧ S'`** of a segment inside `S` to the
empty fragment, from its entry's `P` states in `S'`. -/
theorem closed_conjS {S' : I.State → Prop} {P : Frag I} (h : SegTS S p lbl ms P (fun _ _ => False))
    (hE : ExecKeeps I S') (hK : KernKeeps ms S') :
    ∃ inv : Frag I, (∀ s c, P s c → S' s → inv s c) ∧ (∀ s c, inv s c → S s ∧ S' s) ∧
      ∀ s c, inv s c → OutT p lbl ms inv s c := by
  obtain ⟨inv, hP, hS, ho⟩ := h.conjS hE hK
  exact ⟨inv, fun s c h h' => hP s c ⟨h, h'⟩, hS, fun s c h =>
    (ho s c h).mono fun _ _ h => h.resolve_right fun h => h.1⟩

end SegTS

/-- **A `SegW` segment with no outside moves** inside the state predicate
`S` is one with the thread rows inside `S`. -/
theorem SegW.toTS {P Q : Frag I} (h : SegW (fun s _ => S s) (fun _ _ => False) p lbl ms P Q) :
    SegTS S p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c h => .outL (.out ((ho s c h).1 fun _ h => h))⟩

/-! ## Segments inside a fragment

`SegTC S` is `SegTS` with the invariant inside a fragment `S` (a fact of the
state and the control together: the worker's store point on both sides,
`WCompat.pass`). `SegTS S` is `SegTC (fun s _ => S s)` (`SegTS.toC`,
`SegTC.toS`). -/

/-- **A segment with the thread rows whose invariant lies inside the
fragment `S`.** -/
def SegTC (S : Frag I) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I)
    (P Q : Frag I) : Prop :=
  ∃ inv : Frag I, (∀ s c, P s c → inv s c) ∧ (∀ s c, inv s c → S s c) ∧
    ∀ s c, inv s c → OutT p lbl ms (fun s c => inv s c ∨ Q s c) s c

/-- A segment inside a state predicate is one inside its fragment. -/
theorem SegTS.toC {P Q : Frag I} (h : SegTS S p lbl ms P Q) : SegTC (fun s _ => S s) p lbl ms P Q := h

/-- **A `SegW` segment with no outside moves** inside the fragment `W` is
one with the thread rows inside `W`. -/
theorem SegW.toTC {W P Q : Frag I} (h : SegW W (fun _ _ => False) p lbl ms P Q) : SegTC W p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c h => .outL (.out ((ho s c h).1 fun _ h => h))⟩

namespace SegTC

variable {S S' : Frag I} {P P' Q Q' R : Frag I}

/-- Forget `S`. -/
theorem toT (h : SegTC S p lbl ms P Q) : SegT p lbl ms P Q :=
  let ⟨i, hs, _, ho⟩ := h
  ⟨i, hs, ho⟩

/-- Down to a state predicate implied by `S`. -/
theorem toS {T : I.State → Prop} (h : SegTC S p lbl ms P Q) (hT : ∀ s c, S s c → T s) :
    SegTS T p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, fun s c h => hT s c (hw s c h), ho⟩

/-- **One instruction** from every pair of `P`, inside `S`, into `Q`. -/
theorem step (hS : ∀ s c, P s c → S s c) (h : ∀ s c, P s c → OutT p lbl ms Q s c) : SegTC S p lbl ms P Q :=
  ⟨P, fun _ _ h => h, hS, fun s c hp => (h s c hp).mono fun _ _ h => .inr h⟩

/-- **Sequencing.** -/
theorem seq (h₁ : SegTC S p lbl ms P Q) (h₂ : SegTC S p lbl ms Q R) : SegTC S p lbl ms P R := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), fun s c h => h.elim (hw₁ s c) (hw₂ s c), ?_⟩
  rintro s c (h | h)
  · exact (ho₁ s c h).mono fun s c h => h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c h))
  · exact (ho₂ s c h).mono fun s c h => h.elim (fun h => .inl (.inr h)) .inr

theorem mono_pre (h : SegTC S p lbl ms P Q) (hP : ∀ s c, P' s c → P s c) : SegTC S p lbl ms P' Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, fun s c h => hs s c (hP s c h), hw, ho⟩

theorem mono_post (h : SegTC S p lbl ms P Q) (hQ : ∀ s c, Q s c → Q' s c) : SegTC S p lbl ms P Q' :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c h => (ho s c h).mono fun s c h => h.imp_right (hQ s c)⟩

/-- A weaker fragment. -/
theorem mono_S (h : SegTC S p lbl ms P Q) (hS : ∀ s c, S s c → S' s c) : SegTC S' p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, fun s c h => hS s c (hw s c h), ho⟩

/-- **A control-flow graph** of nodes `N i`, each a segment inside `S` to
some node or the exit `X`. -/
theorem cfg {ι : Sort _} (N : ι → Frag I) {X : Frag I}
    (h : ∀ i, SegTC S p lbl ms (N i) (fun s c => (∃ j, N j s c) ∨ X s c)) :
    SegTC S p lbl ms (fun s c => ∃ i, N i s c) X := by
  let Inv : Frag I := fun s c => ∃ i, ∃ J : Frag I, (∀ s c, N i s c → J s c) ∧ (∀ s c, J s c → S s c) ∧
      (∀ s c, J s c → OutT p lbl ms (fun s c => J s c ∨ ((∃ j, N j s c) ∨ X s c)) s c) ∧ J s c
  refine ⟨Inv, ?_, ?_, ?_⟩
  · rintro s c ⟨i, hi⟩
    obtain ⟨J, hs, hw, ho⟩ := h i
    exact ⟨i, J, hs, hw, ho, hs s c hi⟩
  · rintro s c ⟨i, J, -, hw, -, hJ⟩
    exact hw s c hJ
  · rintro s c ⟨i, J, hs, hw, ho, hJ⟩
    refine (ho s c hJ).mono fun s c h => ?_
    rcases h with h | ⟨j, hj⟩ | h
    · exact .inl ⟨i, J, hs, hw, ho, h⟩
    · obtain ⟨J', hs', hw', ho'⟩ := h j
      exact .inl ⟨j, J', hs', hw', ho', hs' s c hj⟩
    · exact .inr h

/-- **Ghost parameters.** -/
theorem exists_pre {γ : Sort _} {P : γ → Frag I} {X : Frag I} (h : ∀ g, SegTC S p lbl ms (P g) X) :
    SegTC S p lbl ms (fun s c => ∃ g, P g s c) X :=
  cfg P fun g => (h g).mono_post fun _ _ h => .inr h

/-- **A kept state predicate along a segment inside `S`** (`SegTS.conjS`
over `SegTC`). -/
theorem conjS {S' : I.State → Prop} (h : SegTC S p lbl ms P Q) (hE : ExecKeeps I S') (hK : KernKeeps ms S') :
    SegTC (fun s c => S s c ∧ S' s) p lbl ms (fun s c => P s c ∧ S' s) (fun s c => Q s c ∧ S' s) := by
  obtain ⟨i, hs, hw, ho⟩ := h
  refine ⟨fun s c => i s c ∧ S' s, fun s c h => ⟨hs s c h.1, h.2⟩, fun s c h => ⟨hw s c h.1, h.2⟩,
    fun s c h => ?_⟩
  exact ((ho s c h.1).conjS h.2 hE hK).mono fun s c ⟨h, hS⟩ => h.imp (fun h => ⟨h, hS⟩) fun h => ⟨h, hS⟩

/-- **The closed invariant inside `S ∧ S'`** of a segment inside `S` to the
empty fragment, from its entry's `P` states in `S'`. -/
theorem closed_conjS {S' : I.State → Prop} {P : Frag I} (h : SegTC S p lbl ms P (fun _ _ => False))
    (hE : ExecKeeps I S') (hK : KernKeeps ms S') :
    ∃ inv : Frag I, (∀ s c, P s c → S' s → inv s c) ∧ (∀ s c, inv s c → S s c ∧ S' s) ∧
      ∀ s c, inv s c → OutT p lbl ms inv s c := by
  obtain ⟨inv, hP, hS, ho⟩ := h.conjS hE hK
  exact ⟨inv, fun s c h h' => hP s c ⟨h, h'⟩, hS, fun s c h =>
    (ho s c h).mono fun _ _ h => h.resolve_right fun h => h.1⟩

end SegTC

/-- **The closed invariant inside `S`** of a segment to the empty fragment
(as `WakeW1.closed_of_segT`), from the entry's `P` states in `S`. -/
theorem closedS_of_segT {P : Frag I} (h : SegT p lbl ms P (fun _ _ => False)) (hE : ExecKeeps I S)
    (hK : KernKeeps ms S) :
    ∃ inv : Frag I, (∀ s c, P s c → S s → inv s c) ∧ (∀ s c, inv s c → S s) ∧
      ∀ s c, inv s c → OutT p lbl ms inv s c := by
  obtain ⟨inv, hP, hS, ho⟩ := h.conjS hE hK
  exact ⟨inv, fun s c h h' => hP s c ⟨h, h'⟩, hS, fun s c h =>
    (ho s c h).mono fun _ _ h => h.resolve_right fun h => h.1⟩

end Spike.Lib
