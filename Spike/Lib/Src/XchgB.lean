import Scc.Lower.Spec2
import Spike.Lib.Src.ImmIn2

/-!
**Lane stores in range** (ISA-neutral). `body2` (`Scc/Lower/Spec2.lean`)
accepts `let x = xchgAt b i v` only at a buffer `b` of the walk's buffers
with a literal index below its count, and a buffer's count is below `2^28`
(`newBuf`). The node of a lane store needs both: the source exchanges at a
locative (the buffer's), and the lowered displacement `8 * i` is the
source's word offset. `countsB` does not keep them, so `xchgsB` walks a body
as `countsB` does (`csAfter`, `bufsAfter`) and checks them at each lane store.

- `XchgB`: at a lane store, `b` a buffer of count `n` above the literal
  index, `n < 2^28`; at a pair whose left part is a buffer, its count below
  `2^28` (`pairSmall_head`, the slice's count bound);
- `xchgsB`: `XchgB` at every lane store of a body, the walk's known values
  and buffers threaded as `countsB` threads them;
- `xchgsB_of_body2`: an `Accepted2` body (`body2`) whose buffers' counts
  are below `2^28` is `xchgsB`;
- `LblRoom`: every placed label has `2^31` bytes below `2^64` after its
  base, so an element's address `base + 8 * i` (`i < 2^28`) does not wrap.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (csAfter bufsAfter unbuf constOf bindC body2 Cx2)

/-- **A lane store's buffer and index** (`body2`'s check): `b` a buffer of
the walk's `bufs` of count `n`, the index a literal below `n`, `n < 2^28`. -/
def XchgB (bufs : List (String × Nat)) (b j : At) : Prop :=
  ∃ b' k n, b = .var b' ∧ j = .lit k ∧ bufs.lookup b' = some n ∧ k < n ∧ n < 2 ^ 28

/-- **Room after every placed label**: `2^31` bytes below `2^64` (a buffer
of fewer than `2^28` words lies there; the memory side's placement). -/
def LblRoom (lbl : WeakMem.AllocLabel → Option Nat) : Prop := ∀ l A, lbl l = some A → A + 2 ^ 31 ≤ 2 ^ 64

/-- `XchgB` as a check. -/
def xchgOk (bufs : List (String × Nat)) : Op → Bool
  | .xchgAt (.var b) (.lit k) _ =>
      match bufs.lookup b with
      | some n => decide (k < n) && decide (n < 2 ^ 28)
      | none => false
  | .xchgAt _ _ _ => false
  | .pair (.var b) _ =>
      match bufs.lookup b with
      | some n => decide (n < 2 ^ 28)
      | none => true
  | _ => true

/-- **Every lane store of a body in range**, its known values `cs` and
buffers `bufs` threaded as `countsB` threads them. -/
def xchgsB : List (String × Nat) → List (String × Nat) → Expr → Bool
  | cs, bufs, .let_ x op e => xchgOk bufs op && xchgsB (csAfter x cs op) (bufsAfter x cs bufs op) e
  | cs, bufs, .split _ x y e => xchgsB (unbuf y (unbuf x cs)) (unbuf y (unbuf x bufs)) e
  | cs, bufs, .unpack _ i x e => xchgsB (unbuf x (unbuf i cs)) (unbuf x (unbuf i bufs)) e
  | cs, bufs, .ifeq _ _ y n => xchgsB cs bufs y && xchgsB cs bufs n
  | _, _, _ => true

theorem xchgB_of_ok {bufs : List (String × Nat)} {x : String} {b j v : At} {e : Expr}
    {cs : List (String × Nat)} (h : xchgsB cs bufs (.let_ x (.xchgAt b j v) e) = true) : XchgB bufs b j := by
  simp only [xchgsB, Bool.and_eq_true] at h
  obtain ⟨h, -⟩ := h
  cases b <;> cases j <;> simp only [xchgOk] at h <;> try cases h
  rename_i b' k
  cases hb : bufs.lookup b' with
  | none => simp [hb] at h
  | some n =>
    simp only [hb, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨b', k, n, rfl, rfl, hb, h.1, h.2⟩

/-- The tail of `xchgsB` past a `let`. -/
theorem xchgsB_tail {cs bufs : List (String × Nat)} {x : String} {op : Op} {e : Expr}
    (h : xchgsB cs bufs (.let_ x op e) = true) : xchgsB (csAfter x cs op) (bufsAfter x cs bufs op) e = true := by
  simp only [xchgsB, Bool.and_eq_true] at h
  exact h.2

/-- **A pair's buffer count is small** (`xchgOk`'s pair check): a pair
whose left part is a buffer of `bufs` has that buffer's count below `2^28`. -/
theorem pairSmall_head {cs bufs : List (String × Nat)} {x : String} {op : Op} {e : Expr}
    (h : xchgsB cs bufs (.let_ x op e) = true) :
    ∀ y n, (∃ b, op = .pair (.var y) b) → bufs.lookup y = some n → n < 2 ^ 28 := by
  rintro y n ⟨b, rfl⟩ hl
  simp only [xchgsB, xchgOk, hl, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Small counts survive dropping a name. -/
theorem small_unbuf {bufs : List (String × Nat)} (h : ∀ b n, bufs.lookup b = some n → n < 2 ^ 28) (y : String) :
    ∀ b n, (unbuf y bufs).lookup b = some n → n < 2 ^ 28 := by
  intro b n hb
  rw [lookup_unbuf] at hb
  split at hb
  · cases hb
  · exact h b n hb

/-- **An `Accepted2` body's lane stores are in range**: `body2` with
buffers of counts below `2^28` is `xchgsB`. -/
theorem xchgsB_of_body2 {cx : Cx2} (e : Expr) : ∀ (cs bufs : List (String × Nat)) (scope : List String),
    (∀ b n, bufs.lookup b = some n → n < 2 ^ 28) → body2 cx cs bufs scope e = true → xchgsB cs bufs e = true := by
  induction e with
  | let_ x op e ih =>
    intro cs bufs scope hs h
    cases op with
    | newBuf n τ =>
      simp only [body2, Bool.and_eq_true] at h
      obtain ⟨⟨⟨-, -⟩, -⟩, h⟩ := h
      cases hc : constOf cs n with
      | none => simp [hc] at h
      | some k =>
        simp only [hc, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨-, hk⟩, h⟩ := h
        simp only [xchgsB, xchgOk, bufsAfter, hc, Bool.true_and]
        refine ih _ _ _ (fun b m hb => ?_) h
        simp only [List.lookup] at hb
        split at hb
        · cases hb; exact hk
        · exact small_unbuf hs x b m hb
    | xchgAt b j v =>
      cases b <;> cases j <;> simp only [body2] at h <;> try cases h
      rename_i b' k
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨-, hb⟩, -⟩, h⟩ := h
      cases hl : bufs.lookup b' with
      | none => simp [hl] at hb
      | some n =>
        simp only [hl, decide_eq_true_eq] at hb
        simp only [xchgsB, xchgOk, hl, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hb, hs b' n hl⟩, ih _ _ _ (small_unbuf hs x) h⟩
    | pair a b =>
      simp only [body2, Bool.and_eq_true] at h
      have hok : xchgOk bufs (.pair a b) = true := by
        cases a with
        | var y =>
          simp only [xchgOk]
          cases hl : bufs.lookup y with
          | none => rfl
          | some n => simpa using hs y n hl
        | _ => rfl
      simp only [xchgsB, hok, bufsAfter, Bool.true_and]
      exact ih _ _ _ (small_unbuf hs x) h.2
    | _ =>
      first
        | (simp only [body2] at h; cases h)
        | (simp only [body2, Bool.and_eq_true] at h
           simp only [xchgsB, xchgOk, bufsAfter, Bool.true_and]
           first
             | exact ih _ _ _ (small_unbuf hs x) h.2
             | exact ih _ _ _ (small_unbuf hs x) h.2.2
             | exact ih _ _ _ (small_unbuf hs x) h.2.2.2)
  | split a x y e ih =>
    intro cs bufs scope hs h
    simp only [body2, Bool.and_eq_true] at h
    exact ih _ _ _ (small_unbuf (small_unbuf hs x) y) h.2
  | unpack a i x e ih =>
    intro cs bufs scope hs h
    simp only [body2, Bool.and_eq_true] at h
    exact ih _ _ _ (small_unbuf (small_unbuf hs i) x) h.2
  | ifeq a b y n ihy ihn =>
    intro cs bufs scope hs h
    simp only [body2, Bool.and_eq_true] at h
    simp only [xchgsB, Bool.and_eq_true]
    exact ⟨ihy _ _ _ hs h.1.2, ihn _ _ _ hs h.2⟩
  | _ => intros; simp [xchgsB]

end Spike.Lib.LowerNode
