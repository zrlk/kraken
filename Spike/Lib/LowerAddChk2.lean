/-
**A checked `+` at a tail of an `Accepted2` body is an instruction**
(ISA-neutral), the `Accepted2` twin of `Spike/Lib/LowerAddChk1.lean`: if
`lowerC2` succeeds on a body one of whose tails (`TailOf`) is a
`let x = a + b`, one of the lowered function's blocks has a checked `+`
(so the function has the local overflow block: `hasAddChk (func2 …)`).

- `AddIn2`: a closed form with a checked `+` in its open block or a later
  block;
- `lowerC2_let_inner`: a `let`'s closed form holds its body's (its open
  block's instructions after the `let`'s own, its later blocks the same);
- `lowerC2_addIn`: at a `+` among the body's tails, `lowerC2` emits a
  checked `+`;
- `lowerC2_add_blocks`: the statement on the function's blocks
  (`func2`'s `entry` block, then the closed form's blocks).
-/
import Spike.Lib.LowerAddChk1
import Spike.Lib.Src.CallOrder2

namespace Spike.Lib.LowerAddChk

open CoreLang CoreTerm
open Spike.Lib.LowerShape (lowerC2 Res2 lowerC2_add_inv lowerC2_sub_inv lowerC2_call_inv lowerC2_newBuf_inv
  lowerC2_xchg_inv lowerC2_split_inv lowerC2_unpack_inv lowerC2_ifeq_inv lowerC2_pure_inv)
open Spike.Lib.LowerNode (TailOf)

/-- A closed form has a checked `+`: in its open block or a later block. -/
def AddIn2 (r : Res2) : Prop := (∃ i ∈ r.insts, IsAdd i) ∨ ∃ b ∈ r.blocks, ∃ i ∈ b.insts, IsAdd i

/-- **A `let`'s closed form holds its body's**: the body's closed form
`r'` (at some environment, counter and instruction count), its open
block's instructions after the `let`'s own, its later blocks the same. -/
theorem lowerC2_let_inner {cx : Scc.Lower.Ctx} {env : Scc.Lower.Env} {n : Nat} {l : Scc.IR.Label} {k : Nat}
    {x : String} {op : Op} {e : Expr} {r : Res2} (hr : lowerC2 cx env n l k (.let_ x op e) = some r) :
    ∃ env' n' k' r', lowerC2 cx env' n' l k' e = some r' ∧ (∃ pre, r.insts = pre ++ r'.insts) ∧
      r.blocks = r'.blocks := by
  cases op with
  | add a b =>
    obtain ⟨_, _, _, _, r', -, -, h, rfl⟩ := lowerC2_add_inv hr
    exact ⟨_, _, _, r', h, ⟨[_], rfl⟩, rfl⟩
  | sub a b =>
    obtain ⟨_, _, _, _, r', -, -, h, rfl⟩ := lowerC2_sub_inv hr
    exact ⟨_, _, _, r', h, ⟨[_], rfl⟩, rfl⟩
  | call g is a ts =>
    rcases lowerC2_call_inv hr with ⟨_, _, _, r', -, -, -, -, h, rfl⟩ | ⟨_, _, _, _, _, _, _, r', -, -, -, -, h, rfl⟩
    · exact ⟨_, _, _, r', h, ⟨[_], rfl⟩, rfl⟩
    · exact ⟨_, _, _, r', h, ⟨_, rfl⟩, rfl⟩
  | newBuf c τ =>
    obtain ⟨_, _, _, _, _, _, _, r', -, -, -, -, -, h, rfl⟩ := lowerC2_newBuf_inv hr
    exact ⟨_, _, _, r', h, ⟨[_], rfl⟩, rfl⟩
  | xchgAt b i v =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r', -, -, -, -, -, -, -, -, h, rfl⟩ :=
      lowerC2_xchg_inv hr
    exact ⟨_, _, _, r', h, ⟨[_, _], rfl⟩, rfl⟩
  | _ =>
    first
      | (obtain ⟨_, _, _, _, r', -, -, h, rfl⟩ := lowerC2_pure_inv rfl hr
         exact ⟨_, _, _, r', h, ⟨[], rfl⟩, rfl⟩)
      | (simp [lowerC2, Spike.Lib.LowerShape.pureOp] at hr)

/-- **At a `+` among the body's tails, `lowerC2` emits a checked `+`**
(in its open block or a later block). -/
theorem lowerC2_addIn :
    ∀ (e : Expr) {cx : Scc.Lower.Ctx} {env : Scc.Lower.Env} {n : Nat} {l : Scc.IR.Label} {k : Nat} {r : Res2},
      lowerC2 cx env n l k e = some r → ∀ {x : String} {a b : At} {e' : Expr},
      TailOf (.let_ x (.add a b) e') e → AddIn2 r := by
  intro e
  induction e with
  | let_ y op e ih =>
    intro cx env n l k r hr x a b e' ht
    cases ht with
    | refl =>
      obtain ⟨_, _, _, _, r', -, -, -, rfl⟩ := lowerC2_add_inv hr
      exact .inl ⟨_, List.mem_cons_self .., _, _, _, rfl⟩
    | let_ _ _ ht =>
      obtain ⟨_, _, _, r', h, ⟨pre, hi⟩, hb⟩ := lowerC2_let_inner hr
      rcases ih h ht with ⟨i, hi', hA⟩ | ⟨bl, hbl, hA⟩
      · exact .inl ⟨i, by rw [hi]; exact List.mem_append_right _ hi', hA⟩
      · exact .inr ⟨bl, by rw [hb]; exact hbl, hA⟩
  | split a0 y z e ih =>
    intro cx env n l k r hr x a b e' ht
    cases ht with
    | split _ _ _ ht =>
      obtain ⟨_, _, _, _, _, -, -, -, h⟩ := lowerC2_split_inv hr
      exact ih h ht
  | unpack a0 i y e ih =>
    intro cx env n l k r hr x a b e' ht
    cases ht with
    | unpack _ _ _ ht =>
      obtain ⟨_, _, -, h⟩ := lowerC2_unpack_inv hr
      exact ih h ht
  | unpackT a0 α y e ih =>
    intro cx env n l k r hr
    simp [lowerC2] at hr
  | ifeq a0 b0 yes no ihy ihn =>
    intro cx env n l k r hr x a b e' ht
    obtain ⟨_, _, _, _, ry, rn, -, -, hy, hn, rfl⟩ := lowerC2_ifeq_inv hr
    right
    have lift : ∀ (lb : Scc.IR.Label) (rr : Res2), AddIn2 rr →
        ∃ bl ∈ (⟨lb, rr.insts, rr.term⟩ :: rr.blocks : List Scc.IR.Block), ∃ i ∈ bl.insts, IsAdd i := by
      intro lb rr h
      rcases h with ⟨i, hi, hi'⟩ | ⟨bl, hbl, i, hi, hi'⟩
      · exact ⟨_, List.mem_cons_self .., i, hi, hi'⟩
      · exact ⟨bl, List.mem_cons_of_mem _ hbl, i, hi, hi'⟩
    cases ht with
    | yes _ _ _ ht =>
      obtain ⟨bl, hbl, hA⟩ := lift _ _ (ihy hy ht)
      exact ⟨bl, List.mem_append_left _ hbl, hA⟩
    | no _ _ _ ht =>
      obtain ⟨bl, hbl, hA⟩ := lift _ _ (ihn hn ht)
      exact ⟨bl, List.mem_append_right _ hbl, hA⟩
  | _ =>
    intro cx env n l k r hr x a b e' ht
    cases ht

/-- **A checked `+` at a tail of the body is an instruction** of one of the
lowered function's blocks (`func2`'s: the `entry` block, then `r`'s), so
`hasAddChk (func2 name ps sc hp r) = true`. -/
theorem lowerC2_add_blocks {cx : Scc.Lower.Ctx} {env : Scc.Lower.Env} {n : Nat} {l : Scc.IR.Label} {k : Nat}
    {e : Expr} {r : Res2} (hr : lowerC2 cx env n l k e = some r) {x : String} {a b : At} {e' : Expr}
    (ht : TailOf (.let_ x (.add a b) e') e) :
    ((⟨"entry", r.insts, r.term⟩ :: r.blocks : List Scc.IR.Block).any fun bl =>
      bl.insts.any fun | .addChk .. => true | _ => false) = true := by
  have h : ∃ bl ∈ (⟨"entry", r.insts, r.term⟩ :: r.blocks : List Scc.IR.Block), ∃ i ∈ bl.insts, IsAdd i := by
    rcases lowerC2_addIn e hr ht with ⟨i, hi, hi'⟩ | ⟨bl, hbl, i, hi, hi'⟩
    · exact ⟨_, List.mem_cons_self .., i, hi, hi'⟩
    · exact ⟨bl, List.mem_cons_of_mem _ hbl, i, hi, hi'⟩
  obtain ⟨bl, hbl, i, hi, d, p, q, rfl⟩ := h
  exact List.any_eq_true.mpr ⟨bl, hbl, List.any_eq_true.mpr ⟨_, hi, rfl⟩⟩

end Spike.Lib.LowerAddChk

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerAddChk.lowerC2_add_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerAddChk.lowerC2_add_blocks
