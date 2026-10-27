import Spike.Lib.Src.NJLB

/-!
**A new buffer at any label, by a ghost memory** (ISA-neutral). `NJB`'s
labels `L`, memory `sm` and bound `B` are existential at each node: a ghost
the invariant keeps consistent, tied to no machine or source state. So at a
`newBuf` the node may pick a new ghost instead of following the source's
memory: `ghostMem L sm l k` keeps the messages at labels of `L` and off `l`,
drops `l`'s others, and gives `l`'s first `k` words a message holding `0`.
The new buffer's label `l` is then any label at all (the source's
`freshLabel lbase n i nalloc` of any thread), with no freshness premise and
no bound on it: `EnvB.newBuf` (`freshLabel b 1 0 k`, `MemB L s.mem (b + k)`)
generalised.

- `ghostMem`, `HasCell.ghostMem` (a cell at a label of `L` kept),
  `hasCell_ghostMem` (`l`'s first `k` words), `heapLit_ghostMem`,
  `labelsIn_ghostMem`;
- `EnvB.newBufG`: the facts after `let x = newBuf n τ` at label `l`, at
  `L ∨ (· = l)`, `ghostMem`, `max B (l + 1)`;
- `close_elem2`, `eraseLen_newBuf`: the source's binding type and the
  lowering's (`newBufTy τ`) agree up to `Ty.eraseLen` (an `elem2` element is
  closed).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Scc.Lower (LitV constOf csAfter bufsAfter elem2)

/-! ## The ghost memory -/

open Classical in
/-- **The ghost memory after a new buffer at `l`** of `k` words: the
messages at labels of `L` or off `l`, then one message holding `0` at each
of `l`'s first `k` words. -/
noncomputable def ghostMem (L : WeakMem.AllocLabel → Prop) (sm : WeakMem.Memory) (l : WeakMem.AllocLabel)
    (k : Nat) : WeakMem.Memory :=
  sm.filter (fun m => decide (L m.loc.label ∨ m.loc.label ≠ l)) ++
    Array.ofFn (n := k) fun i => ⟨⟨l, i.val⟩, .num 0, 0⟩

open Classical in
theorem mem_ghostMem {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {l : WeakMem.AllocLabel} {k : Nat}
    {m : WeakMem.Msg} (h : m ∈ ghostMem L sm l k) :
    (m ∈ sm ∧ (L m.loc.label ∨ m.loc.label ≠ l)) ∨ ∃ i < k, m = ⟨⟨l, i⟩, .num 0, 0⟩ := by
  unfold ghostMem at h
  rcases Array.mem_append.1 h with h | h
  · obtain ⟨hm, hp⟩ := Array.mem_filter.1 h
    exact .inl ⟨hm, of_decide_eq_true hp⟩
  · obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 h
    exact .inr ⟨i.val, i.isLt, rfl⟩

open Classical in
/-- **A cell at a label of `L` is kept.** -/
theorem HasCell.ghostMem {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {sa : WeakMem.Address}
    (h : HasCell sm sa) (hl : L sa.label) (l : WeakMem.AllocLabel) (k : Nat) :
    HasCell (Spike.Lib.LowerNode.ghostMem L sm l k) sa := by
  obtain ⟨j, m, hj, rfl⟩ := h
  obtain ⟨j', hj'⟩ := Array.mem_iff_getElem?.1 (show m ∈ Spike.Lib.LowerNode.ghostMem L sm l k by
    unfold Spike.Lib.LowerNode.ghostMem
    refine Array.mem_append.2 (.inl (Array.mem_filter.2 ⟨Array.mem_of_getElem? hj, ?_⟩))
    exact decide_eq_true (.inl hl))
  exact ⟨j', m, hj', rfl⟩

/-- **`l`'s first `k` words have messages.** -/
theorem hasCell_ghostMem (L : WeakMem.AllocLabel → Prop) (sm : WeakMem.Memory) (l : WeakMem.AllocLabel)
    {k i : Nat} (hi : i < k) : HasCell (ghostMem L sm l k) ⟨l, i⟩ := by
  obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 (show (⟨⟨l, i⟩, .num 0, 0⟩ : WeakMem.Msg) ∈ ghostMem L sm l k from
    Array.mem_append.2 (.inr (Array.mem_ofFn.2 ⟨⟨i, hi⟩, rfl⟩)))
  exact ⟨j, _, hj, rfl⟩

/-- **The ghost memory holds numbers at `L`'s labels and `l`.** -/
theorem heapLit_ghostMem {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} (h : HeapLit sm L)
    (l : WeakMem.AllocLabel) (k : Nat) : HeapLit (ghostMem L sm l k) (fun l' => L l' ∨ l' = l) := by
  intro j m hj hl
  rcases mem_ghostMem (Array.mem_of_getElem? hj) with ⟨hm, hp⟩ | ⟨i, -, rfl⟩
  · obtain ⟨j0, hj0⟩ := Array.mem_iff_getElem?.1 hm
    refine h j0 m hj0 ?_
    rcases hl with hl | hl
    · exact hl
    · rcases hp with hp | hp
      · exact hp
      · exact absurd hl hp
  · exact ⟨0, rfl, by decide⟩

/-- **The ghost memory's labels are below `max B (l + 1)`.** -/
theorem labelsIn_ghostMem {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {B : Nat}
    (h : LabelsIn sm L B) (l : WeakMem.AllocLabel) (k : Nat) :
    LabelsIn (ghostMem L sm l k) (fun l' => L l' ∨ l' = l) (max B (l + 1)) := by
  refine ⟨fun j m hj => ?_, fun l' hl' => ?_⟩
  · rcases mem_ghostMem (Array.mem_of_getElem? hj) with ⟨hm, -⟩ | ⟨i, -, rfl⟩
    · obtain ⟨j0, hj0⟩ := Array.mem_iff_getElem?.1 hm
      exact Nat.lt_of_lt_of_le (h.1 j0 m hj0) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self l) (Nat.le_max_right _ _)
  · rcases hl' with hl' | rfl
    · exact Nat.lt_of_lt_of_le (h.2 l' hl') (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)

/-! ## The new buffer -/

/-- **`let x = newBuf n τ`** of an `elem2` element at any label `l` (the
source's binding, `src_newBuf_step`'s): the facts at the ghost labels
`L ∨ (· = l)`, the ghost memory `ghostMem L sm l kk` and the bound
`max B (l + 1)`, at sizes `lsize'` no smaller at `L`'s labels and holding
the count at `l` (`hz`, `hkz`). `EnvB.newBuf` without its one-thread label
and freshness. -/
theorem EnvB.newBufG {lits : List (String × LitV)} {cs bufs : List (String × Nat)}
    {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {lsize lsize' : WeakMem.AllocLabel → Nat} {B : Nat}
    {env : TermRun.Env} (h : EnvB lits cs bufs L sm lsize env) (hm : MemB L sm B) {x : String} {n : At} {τ : Ty}
    {σs : List Ty} {ta : Ty} {ws : List TermRun.Word} {kk : Nat} (hn : TermRun.evalAt env n = some (ta, ws))
    (hk : TermRun.numOf ws = some kk) (he2 : elem2 τ = true) (l : WeakMem.AllocLabel) (ini : Nat)
    (hz : ∀ l', L l' → lsize l' ≤ lsize' l') (hkz : kk ≤ lsize' l) :
    EnvB ((x, .loc) :: lits) (csAfter x cs (.newBuf n τ)) (bufsAfter x cs bufs (.newBuf n τ))
        (fun l' => L l' ∨ l' = l) (ghostMem L sm l kk) lsize'
        ((x, .refine (.loc .own (.array (.lit kk) (TermRun.close σs τ))) (.ini (.lit ini)),
          [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: env) ∧
      MemB (fun l' => L l' ∨ l' = l) (ghostMem L sm l kk) (max B (l + 1)) := by
  have hL : ∀ l', L l' → L l' ∨ l' = l := fun _ hl => Or.inl hl
  have hP : ∀ l' m, SlP L sm l' m → SlP (fun l' => L l' ∨ l' = l) (ghostMem L sm l kk) l' m :=
    fun _ _ hs => ⟨hL _ hs.1, fun i hi => (hs.2.1 i hi).ghostMem hs.1 l kk, hs.2.2⟩
  have hB : SBufs env bufs (fun l' => L l' ∨ l' = l) (ghostMem L sm l kk) lsize' := by
    intro b k' hb
    obtain ⟨t, u, lb, he, hu, he2', hl, hc, hkb⟩ := h.2.1 b k' hb
    exact ⟨t, u, lb, he, hu, he2', hL _ hl, fun i hi => (hc i hi).ghostMem hl l kk, Nat.le_trans hkb (hz _ hl)⟩
  refine ⟨⟨(h.1.mono hP).cons (SliceL.loc _), ?_, h.2.2.cons x _ _⟩,
    heapLit_ghostMem hm.1 l kk, labelsIn_ghostMem hm.2 l kk⟩
  cases hc : constOf cs n with
  | none =>
    simp only [bufsAfter, hc]
    exact hB.cons x _ _
  | some k' =>
    obtain ⟨w, rfl, hw⟩ := h.2.2.constOf hc hn
    simp only [TermRun.numOf, hw, Option.some.injEq] at hk
    subst hk
    simp only [bufsAfter, hc]
    exact hB.new x rfl (elem2_close he2) (Or.inr rfl) (fun i hi => hasCell_ghostMem L sm l hi) hkz

/-! ## The binding's type -/

/-- **An `elem2` element is closed.** -/
theorem close_elem2 {τ : Ty} (h : elem2 τ = true) (σs : List Ty) : TermRun.close σs τ = τ := by
  cases τ <;> simp [elem2] at h <;> simp [TermRun.close, substTs]

/-- **The source's new buffer type and the lowering's** (`newBufTy τ`)
agree up to the buffers' literal lengths. -/
theorem eraseLen_newBuf {τ : Ty} (h : elem2 τ = true) (σs : List Ty) (kk ini : Nat) :
    (Ty.refine (.loc .own (.array (.lit kk) (TermRun.close σs τ))) (.ini (.lit ini))).eraseLen =
      (Ty.refine (.loc .own (.array (.lit 0) τ)) (.ini (.lit 0))).eraseLen := by
  rw [close_elem2 h]; rfl

/-! ## Tests -/

/-- info: 'Spike.Lib.LowerNode.EnvB.newBufG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EnvB.newBufG

/-- info: 'Spike.Lib.LowerNode.eraseLen_newBuf' depends on axioms: [propext] -/
#guard_msgs in #print axioms eraseLen_newBuf

end Spike.Lib.LowerNode
