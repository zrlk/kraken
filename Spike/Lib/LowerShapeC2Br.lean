/-
**The branch targets of `lowerC2`'s blocks are its blocks** (ISA-neutral):
every label a terminator of the closed form `lowerC2`
(`Spike/Lib/LowerShapeC2.lean`) branches to labels one of its later blocks,
so every branch of a code block's function `func2` goes to a block of the
function. The AArch64 emitter refuses an unknown block label
(`FnCtx.blockLabel`); the x86-64 one prints any (`labelOf`), so its
branch-target check needs this of the IR.

- `termTgts`: the labels a terminator branches to;
- `BrClosed`, `lowerC2_brClosed`: every branch of a closed form's
  terminators goes to one of its blocks;
- `func2_brClosed`: every branch of a code block's function goes to a block
  of the function.
-/
import Spike.Lib.LowerShapeC2Shape

namespace Spike.Lib.LowerShape

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv

/-- **The labels a terminator branches to.** -/
def termTgts : Term → List Label
  | .jmp l => [l]
  | .br _ _ _ t f => [t, f]
  | _ => []

/-- **Every branch of a closed form's terminators** (the open block's and
every later block's) **goes to one of its later blocks.** -/
def BrClosed (r : Res2) : Prop :=
  ∀ t ∈ r.term :: r.blocks.map (·.term), ∀ L ∈ termTgts t, L ∈ r.blocks.map (·.label)

/-- **`lowerC2`'s closed forms are branch-closed.** -/
theorem lowerC2_brClosed (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res2),
      lowerC2 cx env n l k e = some r → BrClosed r := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
    cases op with
    | add a b =>
      obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_add_inv hr
      exact ih _ _ _ _ r' hr'
    | sub a b =>
      obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_sub_inv hr
      exact ih _ _ _ _ r' hr'
    | call g is a ts =>
      rcases lowerC2_call_inv hr with ⟨_, _, _, r', -, -, -, -, hr', rfl⟩ |
        ⟨_, _, _, _, _, _, _, r', -, -, -, -, hr', rfl⟩
      · exact ih _ _ _ _ r' hr'
      · exact ih _ _ _ _ r' hr'
    | newBuf c τ =>
      obtain ⟨_, _, _, _, _, _, _, r', -, -, -, -, -, hr', rfl⟩ := lowerC2_newBuf_inv hr
      exact ih _ _ _ _ r' hr'
    | xchgAt b i v =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r', -, -, -, -, -, -, -, -, hr', rfl⟩ :=
        lowerC2_xchg_inv hr
      exact ih _ _ _ _ r' hr'
    | _ =>
      first
      | (obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_pure_inv rfl hr
         exact ih _ _ _ _ r' hr')
      | simp [lowerC2, pureOp] at hr
  | split a x y e ih =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, _, -, -, -, hr'⟩ := lowerC2_split_inv hr
    exact ih _ _ _ _ _ hr'
  | unpack a i x e ih =>
    intro env n l k r hr
    obtain ⟨_, _, -, hr'⟩ := lowerC2_unpack_inv hr
    exact ih _ _ _ _ _ hr'
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, ry, rn, -, -, hy, hn, rfl⟩ := lowerC2_ifeq_inv hr
    have hy' := ihy _ _ _ _ _ hy
    have hn' := ihn _ _ _ _ _ hn
    intro t ht L hL
    have mem : ∀ L', (L' = labName "then" n ∨ L' ∈ ry.blocks.map (·.label) ∨ L' = labName "else" (n + 1) ∨
        L' ∈ rn.blocks.map (·.label)) →
        L' ∈ (⟨labName "then" n, ry.insts, ry.term⟩ :: ry.blocks ++
          ⟨labName "else" (n + 1), rn.insts, rn.term⟩ :: rn.blocks : List Block).map (·.label) := by
      intro L' h
      simp only [List.map_append, List.map_cons]
      rcases h with rfl | h | rfl | h
      · exact List.mem_append_left _ (List.mem_cons_self ..)
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
      · exact List.mem_append_right _ (List.mem_cons_self ..)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    apply mem
    simp only [List.map_cons, List.map_append, List.mem_cons, List.mem_append, List.mem_map] at ht
    rcases ht with rfl | ((rfl | ⟨b, hb, rfl⟩) | (rfl | ⟨b, hb, rfl⟩))
    · simp only [termTgts, List.mem_cons, List.mem_nil_iff, or_false] at hL
      rcases hL with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inr (.inl rfl))
    · exact .inr (.inl (hy' _ (List.mem_cons_self ..) L hL))
    · exact .inr (.inl (hy' _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b, hb, rfl⟩)) L hL))
    · exact .inr (.inr (.inr (hn' _ (List.mem_cons_self ..) L hL)))
    · exact .inr (.inr (.inr (hn' _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b, hb, rfl⟩)) L hL)))
  | ret a =>
    intro env n l k r hr
    obtain ⟨_, _, -, rfl⟩ := lowerC2_ret_inv hr
    intro t ht L hL
    simp only [List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    simp [termTgts] at hL
  | _ => intro env n l k r hr; simp [lowerC2] at hr

/-- **Every branch of a code block's function goes to a block of the
function**, its body's closed form branch-closed. -/
theorem func2_brClosed {name : Sym} {params sc hp : List Reg} {r : Res2} (hr : BrClosed r) :
    ∀ b ∈ (func2 name params sc hp r).blocks, ∀ L ∈ termTgts b.term,
      ∃ b' ∈ (func2 name params sc hp r).blocks, b'.label = L := by
  intro b hb L hL
  have hm : b.term ∈ r.term :: r.blocks.map (·.term) := by
    simp only [func2, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  obtain ⟨b', hb', e⟩ := List.mem_map.mp (hr _ hm L hL)
  exact ⟨b', by simp only [func2]; exact List.mem_cons_of_mem _ hb', e⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerShape.lowerC2_brClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lowerC2_brClosed

/-- info: 'Spike.Lib.LowerShape.func2_brClosed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms func2_brClosed

end Spike.Lib.LowerShape
