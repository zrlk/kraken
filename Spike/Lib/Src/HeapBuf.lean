import Spike.Lib.Src.HeapLit
import Spike.Lib.Src.ImmIn2

/-!
**The exchange's premises** (ISA-neutral), beyond `HeapLit`:

- `post_storeAt`, `post_xchgAt_leaf`: the lowering stores a value's words
  only into as many cell words (`storeAt`), and an `elem2` element is one,
  so an `xchgAt` the lowering accepts stores an atom at a `.leaf` of the
  walk. `Accepted2` needs no check of its own for it (storing a locative is
  refused by the lowering, "store: 2 words for a cell of 1").
- `SBufs env bufs L sm lsize`: every buffer of the body's `bufs` is bound in
  the source environment to the locative of a label in `L`, at an own buffer
  type of an `elem2` element, its first `n` words with a message, `n` within
  the label's size `lsize`; kept by
  other bindings (`.cons`), memory growth (`.mono`), its `newBuf`
  (`.new`, `sBufs_newBuf`), and gives an exchange its cell (`.cell`).
- `LabelsBelow sm B`: every message's label is below `B`, so a label at or
  above `B` is fresh (`freshIn_of_labelsBelow`): with one thread the
  `k`-th label is `lbase + k` (`freshLabel_one`), and the allocation moves
  the bound to `lbase + k + 1` (`labelsBelow_allocBuf`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower (LitV litAt lowerOp elem2 atom1 unbuf)
open Scc.Sem.MemRel (SLatest)

/-! ## The lowering stores one word into an `elem2` element -/

theorem post_storeAt (o : Order) (as : List Addr) (ws : List Operand) :
    Post (Scc.Lower.storeAt o as ws) fun _ => as.length = ws.length := by
  unfold Scc.Lower.storeAt
  split
  · exact Post.throw
  · rename_i h
    exact fun _ _ _ _ => by simpa using h

/-- **An exchange the lowering accepts stores a one-word atom**, at a
`.leaf` of the walk (as `post_evalOne_leaf` for `if`). -/
theorem post_xchgAt_leaf (cx : Scc.Lower.Ctx) {env : Scc.Lower.Env} {lits : List (String × LitV)}
    {scope : List String} (hR : Rel env lits scope) (x b : String) (i : Nat) {v : At}
    (hv : atom1 scope v = true) {e : String × Ty × List Operand} {τ : Ty} (he : env.find? (·.1 == b) = some e)
    (ht : e.2.1 = bufTy τ) (hτ : elem2 τ = true) :
    Post (lowerOp cx env x (.xchgAt (.var b) (.lit i) v)) fun _ => litMask (litAt lits v) = [true] := by
  simp only [lowerOp]
  refine Post.bind (post_lookupV env b) fun r ⟨e1, he1, hr⟩ => ?_
  rw [he] at he1; cases he1; subst hr
  dsimp only
  rw [ht]
  refine Post.bind' fun _ => Post.bind' fun _ => Post.bind (post_needSome _ _) fun mu hmu => ?_
  simp only [bufTy, Scc.Lower.bufElem, Option.some.injEq] at hmu
  subst hmu
  refine Post.bind' fun _ => Post.bind (post_evalAt hR (atom1_var hv)) fun rv hrv => ?_
  obtain ⟨tv, vs⟩ := rv
  refine Post.bind (post_cellAddrs _ _ _ _) fun as ⟨sl, hsl, hl⟩ =>
    Post.bind' fun _ => Post.bind (post_storeAt _ _ _) fun _ hst => Post.pure ?_
  have h1 : sl.length = 1 := by
    cases τ <;> simp [elem2] at hτ <;> simp [Scc.Obj.slots] at hsl <;> subst hsl <;> rfl
  have hlen : vs.length = (flatL (litAt lits v)).length := hrv.2.length
  have hst' : as.length = vs.length := hst
  have hf : (flatL (litAt lits v)).length = 1 := by omega
  obtain ⟨f, hf'⟩ : ∃ f, flatL (litAt lits v) = [f] := by
    cases h : flatL (litAt lits v) with
    | nil => rw [h] at hf; cases hf
    | cons f fs => cases fs with
      | nil => exact ⟨f, rfl⟩
      | cons _ _ => rw [h] at hf; simp at hf
  exact litMask_of_flatL hf'

/-! ## Buffers in the source environment -/

/-- **The body's buffers in the source**: each `b` of `bufs` with count `n` is
bound to the locative of a label `lbl ∈ L` at an own buffer type of an
`elem2` element, its first `n` words have messages, and `n` is within the
label's size `lsize lbl` (the link to the machine's label ranges). -/
def SBufs (env : TermRun.Env) (bufs : List (String × Nat)) (L : WeakMem.AllocLabel → Prop)
    (sm : WeakMem.Memory) (lsize : WeakMem.AllocLabel → Nat) : Prop :=
  ∀ b n, bufs.lookup b = some n → ∃ t u lbl, TermRun.lookupE env b = some (t, [TermRun.cst (.loc ⟨lbl, 0⟩ 0)]) ∧
    TermRun.bufElem t = some (.own, u) ∧ elem2 u = true ∧ L lbl ∧ (∀ i < n, HasCell sm ⟨lbl, i⟩) ∧ n ≤ lsize lbl

theorem sBufs_nil (env : TermRun.Env) (L : WeakMem.AllocLabel → Prop) (sm : WeakMem.Memory)
    (lsize : WeakMem.AllocLabel → Nat) : SBufs env [] L sm lsize := fun _ _ h => by cases h

/-- **Another binding keeps the buffers** that it does not shadow. -/
theorem SBufs.cons {env : TermRun.Env} {bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
    {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} (h : SBufs env bufs L sm lsize) (x : String) (t : Ty)
    (ws : List TermRun.Word) : SBufs ((x, t, ws) :: env) (unbuf x bufs) L sm lsize := by
  intro b n hb
  rw [lookup_unbuf] at hb
  split at hb
  · cases hb
  · rename_i hbx
    obtain ⟨t', u, lbl, he, h1⟩ := h b n hb
    exact ⟨t', u, lbl, by rw [lookupE_cons]; simp only [hbx, ↓reduceIte]; exact he, h1⟩

/-- **Memory growth, more labels and larger sizes at `L`'s labels keep the
buffers.** -/
theorem SBufs.mono {env : TermRun.Env} {bufs : List (String × Nat)} {L L' : WeakMem.AllocLabel → Prop}
    {sm sm' : WeakMem.Memory} {lsize lsize' : WeakMem.AllocLabel → Nat} (h : SBufs env bufs L sm lsize)
    (hL : ∀ l, L l → L' l) (hm : ∀ sa, HasCell sm sa → HasCell sm' sa) (hz : ∀ l, L l → lsize l ≤ lsize' l) :
    SBufs env bufs L' sm' lsize' := by
  intro b n hb
  obtain ⟨t, u, lbl, he, hu, he2, hl, hc, hn⟩ := h b n hb
  exact ⟨t, u, lbl, he, hu, he2, hL _ hl, fun i hi => hm _ (hc i hi), Nat.le_trans hn (hz _ hl)⟩

/-- **A new buffer**: `x` bound to label `lbl`'s locative with `k` words,
within `lbl`'s size. -/
theorem SBufs.new {env : TermRun.Env} {bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
    {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} (h : SBufs env bufs L sm lsize) (x : String) {t u : Ty}
    {lbl : WeakMem.AllocLabel} {k : Nat} (hu : TermRun.bufElem t = some (.own, u)) (he2 : elem2 u = true)
    (hl : L lbl) (hc : ∀ i < k, HasCell sm ⟨lbl, i⟩) (hk : k ≤ lsize lbl) :
    SBufs ((x, t, [TermRun.cst (.loc ⟨lbl, 0⟩ 0)]) :: env) ((x, k) :: unbuf x bufs) L sm lsize := by
  intro b n hb
  rw [lookup_cons_name] at hb
  split at hb
  · cases hb; rename_i hbx
    exact ⟨t, u, lbl, by rw [lookupE_cons]; simp [hbx], hu, he2, hl, hc, hk⟩
  · exact h.cons x t _ b n hb

theorem elem2_close {σs : List Ty} {τ : Ty} (h : elem2 τ = true) : elem2 (TermRun.close σs τ) = true := by
  cases τ <;> simp [elem2] at h <;> simp [TermRun.close, substTs, elem2]

theorem accs_elem2 {u : Ty} (h : elem2 u = true) : TermRun.accs u = some [.one] := by
  cases u <;> simp [elem2] at h <;> rfl

/-- **The buffers after `newBuf`** (`src_newBuf_step`'s binding and memory):
the new buffer at its fresh label, added to `L`, at sizes `lsize'` no smaller
at `L`'s labels and holding `k` words at `lbl`. -/
theorem sBufs_newBuf {env : TermRun.Env} {bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
    {s : TermRun.St} {lsize lsize' : WeakMem.AllocLabel → Nat} (h : SBufs env bufs L s.mem lsize) (x : String)
    {σs : List Ty} {τ : Ty} (he2 : elem2 τ = true)
    {lbl : WeakMem.AllocLabel} {k ini : Nat} {us : List TermRun.Acc} (hus : TermRun.accs (TermRun.close σs τ) = some us)
    (z : Option (List WeakMem.Val)) (hz : ∀ l, L l → lsize l ≤ lsize' l) (hk : k ≤ lsize' lbl) :
    SBufs ((x, .refine (.loc .own (.array (.lit k) (TermRun.close σs τ))) (.ini (.lit ini)),
        [TermRun.cst (.loc ⟨lbl, 0⟩ 0)]) :: env) ((x, k) :: unbuf x bufs) (fun l => L l ∨ l = lbl)
      (TermRun.allocBuf lbl (k * TermRun.nWords us) z s).1.mem lsize' := by
  have hus' : us = [.one] := by rw [accs_elem2 (elem2_close he2)] at hus; cases hus; rfl
  subst hus'
  refine (h.mono (fun l hl => Or.inl hl) (fun sa hc => hc.allocBuf lbl _ z) hz).new x rfl (elem2_close he2)
    (Or.inr rfl) (fun i hi => hasCell_allocBuf lbl _ z s (by simp [TermRun.nWords, TermRun.Acc.size]; omega)) hk

/-- **A pushed message keeps the buffers.** -/
theorem SBufs.push {env : TermRun.Env} {bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
    {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} (h : SBufs env bufs L sm lsize) (m : WeakMem.Msg) :
    SBufs env bufs L (sm.push m) lsize :=
  h.mono (fun _ hl => hl) (fun _ hc => hc.push m) fun _ _ => Nat.le_refl _

/-- **An exchange's cell**: buffer `b` of `bufs` at word `i < n`, its
binding the premises of `src_xchgAt_step` (`bufElem`, `accs`, the address),
and the latest message of the cell a number. -/
theorem SBufs.cell {env : TermRun.Env} {bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
    {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} (h : SBufs env bufs L sm lsize) (hH : HeapLit sm L)
    {b : String} {n i : Nat} (hb : bufs.lookup b = some n) (hi : i < n) :
    ∃ t u lbl, TermRun.lookupE env b = some (t, [TermRun.cst (.loc ⟨lbl, 0⟩ 0)]) ∧
      TermRun.bufElem t = some (.own, u) ∧ TermRun.accs u = some [.one] ∧ elem2 u = true ∧ L lbl ∧
      (∃ j m, SLatest sm (TermRun.offs ⟨lbl, 0⟩ i) j ∧ sm[j]? = some m ∧ IsNum ⟨m.val, m.view, j⟩) ∧
      i < lsize lbl := by
  obtain ⟨t, u, lbl, he, hu, he2, hl, hc, hn⟩ := h b n hb
  have ho : TermRun.offs ⟨lbl, 0⟩ i = ⟨lbl, i⟩ := by simp [TermRun.offs]
  refine ⟨t, u, lbl, he, hu, accs_elem2 he2, he2, hl, ?_, by omega⟩
  rw [ho]; exact latest_num hH (hc i hi) hl

/-! ## Buffers at some sizes -/

/-- **`SBufs` at some sizes**: the source's own invariant (no machine label
ranges to link to), each count below `2^28` (`body2`'s `newBuf` bound). -/
def SBufsA (env : TermRun.Env) (bufs : List (String × Nat)) (L : WeakMem.AllocLabel → Prop)
    (sm : WeakMem.Memory) : Prop :=
  (∃ lsize, SBufs env bufs L sm lsize) ∧ ∀ b n, bufs.lookup b = some n → n < 2 ^ 28

theorem sBufsA_nil (env : TermRun.Env) (L : WeakMem.AllocLabel → Prop) (sm : WeakMem.Memory) :
    SBufsA env [] L sm := ⟨⟨fun _ => 0, sBufs_nil env L sm _⟩, fun _ _ h => by cases h⟩

theorem small_unbuf' {bufs : List (String × Nat)} (h : ∀ b n, bufs.lookup b = some n → n < 2 ^ 28) (y : String) :
    ∀ b n, (unbuf y bufs).lookup b = some n → n < 2 ^ 28 := by
  intro b n hb
  rw [lookup_unbuf] at hb
  split at hb
  · cases hb
  · exact h b n hb

theorem SBufsA.cons {env : TermRun.Env} {bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
    {sm : WeakMem.Memory} (h : SBufsA env bufs L sm) (x : String) (t : Ty) (ws : List TermRun.Word) :
    SBufsA ((x, t, ws) :: env) (unbuf x bufs) L sm :=
  let ⟨⟨z, h⟩, hs⟩ := h; ⟨⟨z, h.cons x t ws⟩, small_unbuf' hs x⟩

theorem SBufsA.unbuf {env : TermRun.Env} {bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
    {sm : WeakMem.Memory} (h : SBufsA env bufs L sm) (i : String) : SBufsA env (unbuf i bufs) L sm := by
  obtain ⟨⟨z, h⟩, hs⟩ := h
  refine ⟨⟨z, fun b n hb => ?_⟩, small_unbuf' hs i⟩
  rw [lookup_unbuf] at hb
  split at hb
  · cases hb
  · exact h b n hb

theorem SBufsA.mono {env : TermRun.Env} {bufs : List (String × Nat)} {L L' : WeakMem.AllocLabel → Prop}
    {sm sm' : WeakMem.Memory} (h : SBufsA env bufs L sm) (hL : ∀ l, L l → L' l)
    (hm : ∀ sa, HasCell sm sa → HasCell sm' sa) : SBufsA env bufs L' sm' :=
  let ⟨⟨z, h⟩, hs⟩ := h; ⟨⟨z, h.mono hL hm fun _ _ => Nat.le_refl _⟩, hs⟩

/-- **The buffers after `newBuf`** at some sizes (`sBufs_newBuf` at sizes
grown by `k` everywhere), a count below `2^28`. -/
theorem sBufsA_newBuf {env : TermRun.Env} {bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
    {s : TermRun.St} (h : SBufsA env bufs L s.mem) (x : String) {σs : List Ty} {τ : Ty} (he2 : elem2 τ = true)
    {lbl : WeakMem.AllocLabel} {k ini : Nat} {us : List TermRun.Acc} (hus : TermRun.accs (TermRun.close σs τ) = some us)
    (z : Option (List WeakMem.Val)) (hk : k < 2 ^ 28) :
    SBufsA ((x, .refine (.loc .own (.array (.lit k) (TermRun.close σs τ))) (.ini (.lit ini)),
        [TermRun.cst (.loc ⟨lbl, 0⟩ 0)]) :: env) ((x, k) :: unbuf x bufs) (fun l => L l ∨ l = lbl)
      (TermRun.allocBuf lbl (k * TermRun.nWords us) z s).1.mem :=
  let ⟨⟨lz, h⟩, hs⟩ := h
  ⟨⟨fun l => lz l + k, sBufs_newBuf h x he2 hus z (fun _ _ => Nat.le_add_right _ _) (Nat.le_add_left _ _)⟩,
    fun b n hb => by
      rw [lookup_cons_name] at hb
      split at hb
      · cases hb; exact hk
      · exact small_unbuf' hs x b n hb⟩

/-! ## Fresh labels -/

/-- **Every message's label is below `B`.** -/
def LabelsBelow (sm : WeakMem.Memory) (B : Nat) : Prop :=
  ∀ (k : Nat) (m : WeakMem.Msg), sm[k]? = some m → m.loc.label < B

theorem labelsBelow_empty (B : Nat) : LabelsBelow #[] B := fun _ _ h => by simp at h

theorem freshIn_of_labelsBelow {sm : WeakMem.Memory} {B : Nat} (h : LabelsBelow sm B) {lbl : WeakMem.AllocLabel}
    (hl : B ≤ lbl) : FreshIn sm lbl := fun k m hk he =>
  absurd (he ▸ h k m hk) (Nat.not_lt.2 hl)

theorem LabelsBelow.mono {sm : WeakMem.Memory} {B B' : Nat} (h : LabelsBelow sm B) (hB : B ≤ B') :
    LabelsBelow sm B' := fun k m hk => Nat.lt_of_lt_of_le (h k m hk) hB

theorem LabelsBelow.push {sm : WeakMem.Memory} {B : Nat} (h : LabelsBelow sm B) {m : WeakMem.Msg}
    (hm : m.loc.label < B) : LabelsBelow (sm.push m) B := by
  intro k m' hk
  rw [Array.getElem?_push] at hk
  split at hk
  · cases hk; exact hm
  · exact h k m' hk

/-- **The one-thread labels**: thread 0 of 1 takes `lbase + k`. -/
theorem freshLabel_one (b k : Nat) : TermRun.freshLabel b 1 0 k = b + k := by
  simp [TermRun.freshLabel]

/-- **`allocBuf` at label `lbl` moves the bound past `lbl`.** -/
theorem labelsBelow_allocBuf {s : TermRun.St} {B : Nat} (h : LabelsBelow s.mem B) {lbl : WeakMem.AllocLabel}
    (hl : B ≤ lbl) (n : Nat) (z : Option (List WeakMem.Val)) :
    LabelsBelow (TermRun.allocBuf lbl n z s).1.mem (lbl + 1) := by
  intro k m hk
  by_cases hold : k < s.mem.size
  · rw [Scc.Sem.allocBuf_mem_old _ _ _ _ hold] at hk
    exact Nat.lt_of_lt_of_le (h k m hk) (Nat.le_succ_of_le hl)
  · have hsz := Scc.Sem.allocBuf_mem_size lbl n z s
    have hlt : k < s.mem.size + n := by
      rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hk).1
    obtain ⟨i, rfl⟩ : ∃ i, k = s.mem.size + i := ⟨k - s.mem.size, by omega⟩
    rw [Scc.Sem.allocBuf_mem_new _ _ _ _ (by omega)] at hk
    cases hk
    exact Nat.lt_succ_self lbl

/-- **One thread's next label is fresh** when every label is below
`lbase + nalloc`. -/
theorem freshIn_one {sm : WeakMem.Memory} {b k : Nat} (h : LabelsBelow sm (b + k)) :
    FreshIn sm (TermRun.freshLabel b 1 0 k) :=
  freshIn_of_labelsBelow h (Nat.le_of_eq (freshLabel_one b k).symm)

end Spike.Lib.LowerNode
