/-
**Segments with a load-or-stutter row** (main's half;
`s1_threads.md` §2.2 option B, proposal 2).

`Out.load` matches a target load with the source's acquire load for *every*
value read. A spin-wait (`waitLoop` of `hello.w`: `let d = load acq c in if
d = 1 then ret 0 else park ; waitLoop c`) needs a weaker row: the source
loads only when the target reads the value `V` it waits for (`1`), and
**stutters** at its load on every other value (the target goes round its
loop, parks, comes back; the source stays at `let d = load acq c`). Which
values the target can read and why the stutter keeps the memory relation is
the whole-program proof's business (`Spike/Lib/Inv2Read.lean`: a pre-spawn
`0` or the worker's `1`); the row only fixes the source's moves.

- `OutL`: `Out`, or the load-or-stutter row `ldSt` (the same premises as
  `Out.load` on the address; a value whose low 64 bits are not `V` lands
  with the control unchanged; `V` lands with the source's load taken);
- `OutL.mono`, `Out.toL`;
- `SegL`: `Seg` over `OutL`, with `Seg.toL` and the combinators `step`,
  `seq`, `loop`, `mono_pre`, `mono_post`, `or_pre`, `cfg`, `exists_pre`.

`Out` and `Seg` are unchanged (no constructor is added to `Out`): a `SegL`
whose proof uses no `ldSt` row is a `Seg` (`Seg.toL` goes the other way).
-/
import Spike.Lib.Seg

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising
open Scc.Sem (ValRep)

/-- **What one instruction does, with the load-or-stutter row**: an `Out`
row, or `ldSt`: one load of `⟨A, 8⟩` at the source's acquire load `let x =
load acq a in e` of the word at `A` (as `Out.load`), where a value whose
low 64 bits are not `V` lands with the source control unchanged (the source
stutters at its load), and the value `V` lands with `x` bound to any word
the memory relation lets the source read (`ms.rd`) representing it, as
`Out.load`. -/
inductive OutL {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I) (X : Frag I)
    (s : I.State) (c : Ctl) : Prop where
  /-- An `Out` row. -/
  | out : Out p lbl ms X s c → OutL p lbl ms X s c
  /-- The load-or-stutter row. -/
  | ldSt (kl : Kraken.LoadKind) (A : BitVec 64) (g : Val → I.State) (x : String) (a : At) (e : Expr)
      (ty : Ty) (w : TermRun.Word) (V : Nat) :
      I.exec s = some (.load kl false ⟨A, 8⟩ fun v => .done (g v)) →
      c.term = .let_ x (.load true a) e → TermRun.evalAt c.env a = some (ty, [w]) → ValRep lbl w.val A.toNat →
      (∀ v : Val, (v.setWidth 64).toNat ≠ V → X (g v) c) →
      (∀ (v : Val) (w' : TermRun.Word), (v.setWidth 64).toNat = V → ms.rd w' → ValRep lbl w'.val V →
        X (g v) ⟨e, (x, loadTy ty, [w']) :: c.env, none⟩) →
      (∃ sa, w.val = .loc sa 0) → OutL p lbl ms X s c

theorem OutL.mono {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {X Y : Frag I} {s : I.State} {c : Ctl}
    (h : OutL p lbl ms X s c) (hXY : ∀ s c, X s c → Y s c) : OutL p lbl ms Y s c := by
  cases h with
  | out h => exact .out (h.mono hXY)
  | ldSt kl A g x a e ty w V he ht hev hv hn hy htag =>
    exact .ldSt kl A g x a e ty w V he ht hev hv (fun v h => hXY _ _ (hn v h))
      (fun v w' h hr hr' => hXY _ _ (hy v w' h hr hr')) htag

/-- An `Out` row is an `OutL` row. -/
theorem Out.toL {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {X : Frag I} {s : I.State} {c : Ctl} (h : Out p lbl ms X s c) : OutL p lbl ms X s c :=
  .out h

/-- **Segment simulation with the load-or-stutter row**: `Seg` over
`OutL`. -/
def SegL {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I) (P Q : Frag I) : Prop :=
  ∃ inv : Frag I, (∀ s c, P s c → inv s c) ∧
    ∀ s c, inv s c → OutL p lbl ms (fun s c => inv s c ∨ Q s c) s c

/-- A segment is one with the load-or-stutter row. -/
theorem Seg.toL {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {P Q : Frag I} (h : Seg p lbl ms P Q) : SegL p lbl ms P Q :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, hs, fun s c hi => .out (ho s c hi)⟩

namespace SegL

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
  {P P' Q Q' R : Frag I}

/-- **One instruction** from every pair of `P` into `Q`. -/
theorem step (h : ∀ s c, P s c → OutL p lbl ms Q s c) : SegL p lbl ms P Q :=
  ⟨P, fun _ _ h => h, fun s c hp => (h s c hp).mono fun _ _ h => .inr h⟩

/-- **Sequencing**. -/
theorem seq (h₁ : SegL p lbl ms P Q) (h₂ : SegL p lbl ms Q R) : SegL p lbl ms P R := by
  obtain ⟨i₁, hs₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), ?_⟩
  rintro s c (h | h)
  · exact (ho₁ s c h).mono fun s c h => h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c h))
  · exact (ho₂ s c h).mono fun s c h => h.elim (fun h => .inl (.inr h)) .inr

/-- **A tail-call loop**. -/
theorem loop {H X : Frag I} (h : SegL p lbl ms H (fun s c => H s c ∨ X s c)) : SegL p lbl ms H X := by
  obtain ⟨i, hs, ho⟩ := h
  refine ⟨i, hs, fun s c hi => (ho s c hi).mono fun s c h => ?_⟩
  rcases h with h | h | h
  · exact .inl h
  · exact .inl (hs s c h)
  · exact .inr h

theorem mono_pre (h : SegL p lbl ms P Q) (hP : ∀ s c, P' s c → P s c) : SegL p lbl ms P' Q :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, fun s c h => hs s c (hP s c h), ho⟩

theorem mono_post (h : SegL p lbl ms P Q) (hQ : ∀ s c, Q s c → Q' s c) : SegL p lbl ms P Q' :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, hs, fun s c h => (ho s c h).mono fun s c h => h.imp_right (hQ s c)⟩

/-- A case split on the entry. -/
theorem or_pre (h : SegL p lbl ms P Q) (h' : SegL p lbl ms P' Q) :
    SegL p lbl ms (fun s c => P s c ∨ P' s c) Q := by
  obtain ⟨i, hs, ho⟩ := h
  obtain ⟨i', hs', ho'⟩ := h'
  refine ⟨fun s c => i s c ∨ i' s c, fun s c h => h.imp (hs s c) (hs' s c), ?_⟩
  rintro s c (h | h)
  · exact (ho s c h).mono fun s c h => h.imp_left .inl
  · exact (ho' s c h).mono fun s c h => h.imp_left .inr

/-- **A control-flow graph** of segments with the load-or-stutter row. -/
theorem cfg {ι : Sort _} (N : ι → Frag I) {X : Frag I}
    (h : ∀ i, SegL p lbl ms (N i) (fun s c => (∃ j, N j s c) ∨ X s c)) :
    SegL p lbl ms (fun s c => ∃ i, N i s c) X := by
  refine ⟨fun s c => ∃ i, ∃ J : Frag I, (∀ s c, N i s c → J s c) ∧
      (∀ s c, J s c → OutL p lbl ms (fun s c => J s c ∨ ((∃ j, N j s c) ∨ X s c)) s c) ∧ J s c, ?_, ?_⟩
  · rintro s c ⟨i, hi⟩
    obtain ⟨J, hs, ho⟩ := h i
    exact ⟨i, J, hs, ho, hs s c hi⟩
  · rintro s c ⟨i, J, hs, ho, hJ⟩
    refine (ho s c hJ).mono fun s c h => ?_
    rcases h with h | ⟨j, hj⟩ | h
    · exact .inl ⟨i, J, hs, ho, h⟩
    · obtain ⟨J', hs', ho'⟩ := h j
      exact .inl ⟨j, J', hs', ho', hs' s c hj⟩
    · exact .inr h

/-- **Ghost parameters**. -/
theorem exists_pre {γ : Sort _} {P : γ → Frag I} {X : Frag I} (h : ∀ g, SegL p lbl ms (P g) X) :
    SegL p lbl ms (fun s c => ∃ g, P g s c) X :=
  cfg P fun g => (h g).mono_post fun _ _ h => .inr h

end SegL

end Spike.Lib
