/-
**The labels a function's direct jumps may go to are emitted** (x86-64):
`emitFunc` emits the label of each of its blocks, the overflow stub's
label where a block has a checked `+`, the stack check's label where the
function checks its stack, and the grow stub's return label where it also
has growth (`tgLabs`). Pure emitter structure: no hypothesis on the
function.

- `Em`, `Yields` and their rules: an action appending items among which
  some given ones, a loop body that yields;
- `tgLabs`: the labels;
- `emitFunc_tgLabs`: each is emitted.
-/
import Spike.Lib.LowerX64.EmitLabels

namespace Spike.Lib.LowerX64

open Kraken
open Scc.Emit.X64

/-! ## Actions appending given items -/

/-- **An action appending items among which those of `L`.** -/
structure Em (L : List Item) {α : Type} (x : E α) : Prop where
  out : ∀ (s : S) (a : α) (s' : S), x s = .ok (a, s') → ∃ c, s'.out = c ++ s.out ∧ ∀ it ∈ L, it ∈ c

namespace Em

theorem of_prep {P : Item → Bool} {α : Type} {x : E α} (h : PreP P x) : Em [] x :=
  ⟨fun s a s' e => by
    obtain ⟨c, hc, -⟩ := h.out s a s' e
    exact ⟨c, hc, fun _ h => by cases h⟩⟩

theorem item' (it : Item) : Em [it] (item it) :=
  ⟨fun s a s' e => by cases e; exact ⟨[it], rfl, fun _ h => h⟩⟩

theorem bind' {L1 L2 : List Item} {α β : Type} {x : E α} {f : α → E β} (hx : Em L1 x) (hf : ∀ a, Em L2 (f a)) :
    Em (L1 ++ L2) (x >>= f) :=
  ⟨fun s b s' e => by
    obtain ⟨a, s1, h1, h2⟩ := bind_inv_E e
    obtain ⟨c1, hc1, hm1⟩ := hx.out _ _ _ h1
    obtain ⟨c2, hc2, hm2⟩ := (hf a).out _ _ _ h2
    refine ⟨c2 ++ c1, by rw [hc2, hc1, List.append_assoc], fun it hit => ?_⟩
    rcases List.mem_append.mp hit with h | h
    · exact List.mem_append_right _ (hm1 it h)
    · exact List.mem_append_left _ (hm2 it h)⟩

theorem ite' {L1 L2 : List Item} {α : Type} {c : Prop} [Decidable c] {x y : E α} (hx : Em L1 x) (hy : Em L2 y) :
    Em (if c then L1 else L2) (if c then x else y) := by
  by_cases h : c
  · simp only [h, ite_true]; exact hx
  · simp only [h, ite_false]; exact hy

theorem mono {L L' : List Item} {α : Type} {x : E α} (h : Em L x) (hL : ∀ it ∈ L', it ∈ L) : Em L' x :=
  ⟨fun s a s' e => by
    obtain ⟨c, hc, hm⟩ := h.out s a s' e
    exact ⟨c, hc, fun it hit => hm it (hL it hit)⟩⟩

/-- **A loop whose body appends `F b` at each element `b`** and yields. -/
theorem forIn_map {β σ : Type} (F : β → Item) (f : β → σ → E (ForInStep σ)) :
    ∀ (l : List β), (∀ b ∈ l, ∀ st, Em [F b] (f b st) ∧
      ∀ s r s', f b st s = .ok (r, s') → ∃ st', r = .yield st') →
    ∀ (init : σ), Em (l.map F) (forIn l init f)
  | [], _, init => ⟨fun s a s' e => by
      simp only [List.forIn_nil] at e
      cases e
      exact ⟨[], rfl, fun _ h => by cases h⟩⟩
  | b :: l, hf, init => ⟨fun s a s' e => by
      rw [List.forIn_cons] at e
      obtain ⟨r, s1, h1, h2⟩ := bind_inv_E e
      obtain ⟨hem, hy⟩ := hf b (List.mem_cons_self ..) init
      obtain ⟨st', rfl⟩ := hy _ _ _ h1
      obtain ⟨c1, hc1, hm1⟩ := hem.out _ _ _ h1
      obtain ⟨c2, hc2, hm2⟩ :=
        (forIn_map F f l (fun b' hb' => hf b' (List.mem_cons_of_mem _ hb')) st').out _ _ _ h2
      refine ⟨c2 ++ c1, by rw [hc2, hc1, List.append_assoc], fun it hit => ?_⟩
      rw [List.map_cons, List.mem_cons] at hit
      rcases hit with rfl | hit
      · exact List.mem_append_right _ (hm1 _ (List.mem_singleton_self _))
      · exact List.mem_append_left _ (hm2 it hit)⟩

end Em

/-- An action whose result is a loop's `yield`. -/
def Yields {σ : Type} (x : E (ForInStep σ)) : Prop := ∀ s r s', x s = .ok (r, s') → ∃ st', r = .yield st'

theorem Yields.bind' {α σ : Type} {x : E α} {f : α → E (ForInStep σ)} (hf : ∀ a, Yields (f a)) : Yields (x >>= f) :=
  fun s r s' e => by
    obtain ⟨a, s1, -, h2⟩ := bind_inv_E e
    exact hf a _ _ _ h2

theorem Yields.pure' {σ : Type} (st : σ) : Yields (pure (ForInStep.yield st) : E (ForInStep σ)) :=
  fun s r s' e => by cases e; exact ⟨st, rfl⟩

/-! ## The labels -/

/-- The labels a function's direct jumps may go to. -/
def tgLabs (growth : Option Scc.IR.Growth) (f : Scc.IR.Func) : List String :=
  f.blocks.map (fun b => labelOf f.name b.label) ++
  (if f.blocks.any (·.insts.any fun | .addChk .. => true | _ => false) then [labelOf f.name "ovf"] else []) ++
  (if f.checkStack then [labelOf f.name "stk"] else []) ++
  (if f.checkStack && growth.isSome then [labelOf f.name "chk"] else [])

/-! ## The labels are emitted -/

/-- A block label among `tgLabs`'s is among the blocks loop's. -/
theorem mem_blocks_zip {f : Scc.IR.Func} {it : Item}
    (h : it ∈ List.map (fun T => Item.d (.label T)) (f.blocks.map fun b => labelOf f.name b.label)) :
    it ∈ (f.blocks.zip (Scc.IR.StackMap.callMaps f)).map
      (fun (x : Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) => Item.d (.label (labelOf f.name x.1.label))) := by
  rw [List.map_map, List.mem_map] at h
  obtain ⟨b, hb, rfl⟩ := h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  have hlen : (Scc.IR.StackMap.callMaps f).length = f.blocks.length := by
    simp [Scc.IR.StackMap.callMaps, Scc.IR.StackMap.callLives]
  refine List.mem_map.mpr ⟨(f.blocks[k], (Scc.IR.StackMap.callMaps f)[k]'(hlen ▸ hk)),
    List.mem_iff_getElem.mpr ⟨k, by simp [hlen, hk], by simp⟩, rfl⟩

set_option linter.unusedSimpArgs false in
/-- `emitFunc` appends the labels `tgLabs` (growth `none`, stack check `false`). -/
theorem emitFunc_em_none_false (a : Scc.IR.Sym) (ar : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func)
    (hcs : f.checkStack = false) (hpar : ¬ f.params.length > Scc.IR.maxArgs) :
    Em ((tgLabs none f).map fun T => Item.d (.label T)) (emitFunc a none ar f) := by
  unfold emitFunc
  simp only [hpar, hcs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  apply Em.mono
  case h =>
    repeat (first
      | (apply Em.forIn_map (fun (x : Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) =>
            Item.d (.label (labelOf f.name x.1.label))) _ (f.blocks.zip _)
         intro ⟨b, ms⟩ hb st
         dsimp only
         refine ⟨Em.mono (Em.bind' (Em.item' _) fun _ => Em.of_prep (P := textN) (by repeat prep_fn_step))
           (by simp), ?_⟩
         repeat (first | exact Yields.pure' _ | (apply Yields.bind'; intro _)))
      | (with_reducible apply Em.bind')
      | (exact Em.item' _)
      | (apply Em.ite')
      | (exact Em.of_prep (P := textN) (by repeat prep_fn_step))
      | (intro _) | (dsimp only))
  case hL =>
    intro it hit
    unfold tgLabs at hit
    simp only [List.map_append, List.mem_append] at hit
    split at hit <;> split
    all_goals first
      | (exfalso; contradiction)
      | skip
    all_goals simp only [hcs, Option.isSome, Bool.and_self, Bool.and_false, Bool.and_true, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
      false_or] at hit
    all_goals try simp only [or_assoc] at hit
    iterate 4 (all_goals try (refine hit.elim (fun hit => ?_) (fun hit => ?_)))
    all_goals first
      | (subst hit; simp only [List.mem_append, List.mem_singleton, true_or, or_true]; done)
      | (have hm := mem_blocks_zip hit; simp only [List.mem_append, hm, true_or, or_true]; done)

set_option linter.unusedSimpArgs false in
/-- `emitFunc` appends the labels `tgLabs` (growth `none`, stack check `true`). -/
theorem emitFunc_em_none_true (a : Scc.IR.Sym) (ar : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func)
    (hcs : f.checkStack = true) (hpar : ¬ f.params.length > Scc.IR.maxArgs) :
    Em ((tgLabs none f).map fun T => Item.d (.label T)) (emitFunc a none ar f) := by
  unfold emitFunc
  simp only [hpar, hcs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  apply Em.mono
  case h =>
    repeat (first
      | (apply Em.forIn_map (fun (x : Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) =>
            Item.d (.label (labelOf f.name x.1.label))) _ (f.blocks.zip _)
         intro ⟨b, ms⟩ hb st
         dsimp only
         refine ⟨Em.mono (Em.bind' (Em.item' _) fun _ => Em.of_prep (P := textN) (by repeat prep_fn_step))
           (by simp), ?_⟩
         repeat (first | exact Yields.pure' _ | (apply Yields.bind'; intro _)))
      | (with_reducible apply Em.bind')
      | (exact Em.item' _)
      | (apply Em.ite')
      | (exact Em.of_prep (P := textN) (by repeat prep_fn_step))
      | (intro _) | (dsimp only))
  case hL =>
    intro it hit
    unfold tgLabs at hit
    simp only [List.map_append, List.mem_append] at hit
    split at hit <;> split
    all_goals first
      | (exfalso; contradiction)
      | skip
    all_goals simp only [hcs, Option.isSome, Bool.and_self, Bool.and_false, Bool.and_true, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
      false_or] at hit
    all_goals try simp only [or_assoc] at hit
    iterate 4 (all_goals try (refine hit.elim (fun hit => ?_) (fun hit => ?_)))
    all_goals first
      | (subst hit; simp only [List.mem_append, List.mem_singleton, true_or, or_true]; done)
      | (have hm := mem_blocks_zip hit; simp only [List.mem_append, hm, true_or, or_true]; done)

set_option linter.unusedSimpArgs false in
/-- `emitFunc` appends the labels `tgLabs` (growth `some`, stack check `false`). -/
theorem emitFunc_em_some_false (a : Scc.IR.Sym) (gr : Scc.IR.Growth) (ar : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func)
    (hcs : f.checkStack = false) (hpar : ¬ f.params.length > Scc.IR.maxArgs) :
    Em ((tgLabs (some gr) f).map fun T => Item.d (.label T)) (emitFunc a (some gr) ar f) := by
  unfold emitFunc
  simp only [hpar, hcs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  apply Em.mono
  case h =>
    repeat (first
      | (apply Em.forIn_map (fun (x : Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) =>
            Item.d (.label (labelOf f.name x.1.label))) _ (f.blocks.zip _)
         intro ⟨b, ms⟩ hb st
         dsimp only
         refine ⟨Em.mono (Em.bind' (Em.item' _) fun _ => Em.of_prep (P := textN) (by repeat prep_fn_step))
           (by simp), ?_⟩
         repeat (first | exact Yields.pure' _ | (apply Yields.bind'; intro _)))
      | (with_reducible apply Em.bind')
      | (exact Em.item' _)
      | (apply Em.ite')
      | (exact Em.of_prep (P := textN) (by repeat prep_fn_step))
      | (intro _) | (dsimp only))
  case hL =>
    intro it hit
    unfold tgLabs at hit
    simp only [List.map_append, List.mem_append] at hit
    split at hit <;> split
    all_goals first
      | (exfalso; contradiction)
      | skip
    all_goals simp only [hcs, Option.isSome, Bool.and_self, Bool.and_false, Bool.and_true, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
      false_or] at hit
    all_goals try simp only [or_assoc] at hit
    iterate 4 (all_goals try (refine hit.elim (fun hit => ?_) (fun hit => ?_)))
    all_goals first
      | (subst hit; simp only [List.mem_append, List.mem_singleton, true_or, or_true]; done)
      | (have hm := mem_blocks_zip hit; simp only [List.mem_append, hm, true_or, or_true]; done)

set_option linter.unusedSimpArgs false in
/-- `emitFunc` appends the labels `tgLabs` (growth `some`, stack check `true`). -/
theorem emitFunc_em_some_true (a : Scc.IR.Sym) (gr : Scc.IR.Growth) (ar : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func)
    (hcs : f.checkStack = true) (hpar : ¬ f.params.length > Scc.IR.maxArgs) :
    Em ((tgLabs (some gr) f).map fun T => Item.d (.label T)) (emitFunc a (some gr) ar f) := by
  unfold emitFunc
  simp only [hpar, hcs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  apply Em.mono
  case h =>
    repeat (first
      | (apply Em.forIn_map (fun (x : Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) =>
            Item.d (.label (labelOf f.name x.1.label))) _ (f.blocks.zip _)
         intro ⟨b, ms⟩ hb st
         dsimp only
         refine ⟨Em.mono (Em.bind' (Em.item' _) fun _ => Em.of_prep (P := textN) (by repeat prep_fn_step))
           (by simp), ?_⟩
         repeat (first | exact Yields.pure' _ | (apply Yields.bind'; intro _)))
      | (with_reducible apply Em.bind')
      | (exact Em.item' _)
      | (apply Em.ite')
      | (exact Em.of_prep (P := textN) (by repeat prep_fn_step))
      | (intro _) | (dsimp only))
  case hL =>
    intro it hit
    unfold tgLabs at hit
    simp only [List.map_append, List.mem_append] at hit
    split at hit <;> split
    all_goals first
      | (exfalso; contradiction)
      | skip
    all_goals simp only [hcs, Option.isSome, Bool.and_self, Bool.and_false, Bool.and_true, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
      false_or] at hit
    all_goals try simp only [or_assoc] at hit
    iterate 4 (all_goals try (refine hit.elim (fun hit => ?_) (fun hit => ?_)))
    all_goals first
      | (subst hit; simp only [List.mem_append, List.mem_singleton, true_or, or_true]; done)
      | (have hm := mem_blocks_zip hit; simp only [List.mem_append, hm, true_or, or_true]; done)

/-- **Each label a function's direct jumps may go to is emitted** (`tgLabs`). -/
theorem emitFunc_tgLabs {a g ar} {f : Scc.IR.Func} {s s' : S} {u : Unit}
    (h : emitFunc a g ar f s = .ok (u, s')) : ∀ T ∈ tgLabs g f, Item.d (.label T) ∈ s'.out := by
  intro T hT
  by_cases hpar : f.params.length > Scc.IR.maxArgs
  · unfold emitFunc at h
    simp only [hpar, ite_true] at h
    obtain ⟨_, _, h1, -⟩ := bind_inv_E h
    cases h1
  have hem : Em ((tgLabs g f).map fun T => Item.d (.label T)) (emitFunc a g ar f) := by
    cases g <;> cases hcs : f.checkStack
    · exact emitFunc_em_none_false a ar f hcs hpar
    · exact emitFunc_em_none_true a ar f hcs hpar
    · exact emitFunc_em_some_false a _ ar f hcs hpar
    · exact emitFunc_em_some_true a _ ar f hcs hpar
  obtain ⟨c, hc, hm⟩ := hem.out _ _ _ h
  rw [hc]
  exact List.mem_append_left _ (hm _ (List.mem_map.mpr ⟨T, hT, rfl⟩))

/-- info: 'Spike.Lib.LowerX64.emitFunc_tgLabs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms emitFunc_tgLabs

end Spike.Lib.LowerX64
