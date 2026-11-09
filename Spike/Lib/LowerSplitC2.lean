/-
**The split leaves `lowerC2`'s functions unchanged** (ISA-neutral): the
weights of the closed form `lowerC2` (`Spike/Lib/LowerShapeC2.lean`)
against `Scc.Lower.openW2` and `Scc.Lower.armsW2`, the `Accepted2` twin of
`Scc/Lower/SplitInv1.lean`.

- `RetsLe rw r`: every `ret` of the closed form `r` is of at most `rw`
  words.
- `extCallsOk isExt ext e`: every call in `e` of an extern (`isExt`) is a
  call of `print` in a program with the extern (`ext`).
- `lowerC2_weight`: without the depth counter, on a body whose extern calls
  are `extCallsOk` and whose closed form's `ret`s are `RetsLe rw`, the open
  block's appended instructions and terminator weigh at most
  `openW2 ext rw e`, every block closed after it at most `armsW2 ext rw e`.
- `blocksOk_func2`: so `func2` of a code block within `blocksOk2`'s bound
  is `blocksOk`, and `splitFuncMarks_func2`: the split pass leaves it and
  its trace `marks2` as they are.

The word counts stay premises (`RetsLe`, `extCallsOk`): the results'
words and the extern calls are facts of the program, not of `lowerC2`.
-/
import Spike.Lib.LowerShapeC2
import Scc.Lower.Split
import Scc.Lower.Spec2

namespace Spike.Lib.LowerShape

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv

/-- **Every `ret` of the closed form `r` is of at most `rw` words**: its
open block's terminator and every later block's. -/
def RetsLe (rw : Nat) (r : Res2) : Prop :=
  (∀ ws, r.term = .ret ws → ws.length ≤ rw) ∧ ∀ b ∈ r.blocks, ∀ ws, b.term = .ret ws → ws.length ≤ rw

/-- **The extern calls of `e`**: every call of an extern (`isExt`) is a
call of `print` in a program with the extern (`ext`), the calls
`openW2` weighs as `printInsts`. -/
def extCallsOk (isExt : String → Bool) (ext : Bool) : Expr → Bool
  | .let_ _ (.call g ..) e => (!isExt g || (ext && g == "print")) && extCallsOk isExt ext e
  | .let_ _ _ e => extCallsOk isExt ext e
  | .split _ _ _ e => extCallsOk isExt ext e
  | .unpack _ _ _ e => extCallsOk isExt ext e
  | .ifeq _ _ y n => extCallsOk isExt ext y && extCallsOk isExt ext n
  | _ => true

/-- `RetsLe` of a closed form with other instructions in its open block. -/
theorem RetsLe.insts {rw : Nat} {r : Res2} (h : RetsLe rw r) {is : List Inst} :
    RetsLe rw { r with insts := is } := h

theorem instsWeight_cons (i : Inst) (is : List Inst) : instsWeight (i :: is) = instWeight i + instsWeight is := by
  simp [instsWeight]

theorem instsWeight_printInsts (n : Nat) (b o m c : Operand) : instsWeight (printInsts n b o m c) = 8 := by
  simp [printInsts, instsWeight, instWeight]

/-- **The weights of `lowerC2`'s output without the depth counter**: the
open block's appended instructions and terminator weigh at most
`openW2 ext rw e`, every block closed after it at most `armsW2 ext rw e`. -/
theorem lowerC2_weight (cx : Scc.Lower.Ctx) (ext : Bool) (rw : Nat) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res2),
      extCallsOk (fun g => (cx.externs.find? (·.1 == g)).isSome) ext e = true →
      lowerC2 cx env n l k e = some r → RetsLe rw r →
        instsWeight r.insts + termWeight r.term ≤ openW2 ext rw e ∧
          ∀ b ∈ r.blocks, blockWeight b ≤ armsW2 ext rw e := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hx hr hR
    cases op with
    | add a b =>
      obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_add_inv hr
      obtain ⟨h1, h2⟩ := ih _ _ _ _ r' (by simpa [extCallsOk] using hx) hr' hR
      refine ⟨?_, by simpa [armsW2] using h2⟩
      simp only [instsWeight_cons, openW2, instWeight] at h1 ⊢
      omega
    | sub a b =>
      obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_sub_inv hr
      obtain ⟨h1, h2⟩ := ih _ _ _ _ r' (by simpa [extCallsOk] using hx) hr' hR
      refine ⟨?_, by simpa [armsW2] using h2⟩
      simp only [instsWeight_cons, openW2, instWeight] at h1 ⊢
      omega
    | call g is a ts =>
      simp only [extCallsOk, Bool.and_eq_true] at hx
      rcases lowerC2_call_inv hr with ⟨_, _, _, r', hn, -, -, -, hr', rfl⟩ |
        ⟨_, _, _, _, _, _, _, r', hs, -, -, -, hr', rfl⟩
      · obtain ⟨h1, h2⟩ := ih _ _ _ _ r' hx.2 hr' hR
        refine ⟨?_, by simpa [armsW2] using h2⟩
        simp only [instsWeight_cons, openW2, instWeight, List.length_singleton] at h1 ⊢
        split <;> omega
      · obtain ⟨h1, h2⟩ := ih _ _ _ _ r' hx.2 hr' hR
        refine ⟨?_, by simpa [armsW2] using h2⟩
        have he : (ext && g == "print") = true := by
          have := hx.1
          simp only [hs, Option.isSome_some, Bool.not_true, Bool.false_or] at this
          exact this
        simp only [instsWeight_append, instsWeight_printInsts, openW2, he, ite_true] at h1 ⊢
        omega
    | newBuf c τ =>
      obtain ⟨_, _, _, _, _, _, _, r', -, -, -, -, -, hr', rfl⟩ := lowerC2_newBuf_inv hr
      obtain ⟨h1, h2⟩ := ih _ _ _ _ r' (by simpa [extCallsOk] using hx) hr' hR
      refine ⟨?_, by simpa [armsW2] using h2⟩
      simp only [instsWeight_cons, openW2, newBufCall, instWeight, List.length_cons, List.length_nil] at h1 ⊢
      omega
    | xchgAt b i v =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r', -, -, -, -, -, -, -, -, hr', rfl⟩ :=
        lowerC2_xchg_inv hr
      obtain ⟨h1, h2⟩ := ih _ _ _ _ r' (by simpa [extCallsOk] using hx) hr' hR
      refine ⟨?_, by simpa [armsW2] using h2⟩
      simp only [instsWeight_cons, openW2, xchgLoad, xchgStore, instWeight] at h1 ⊢
      omega
    | _ =>
      first
      | (obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_pure_inv rfl hr
         obtain ⟨h1, h2⟩ := ih _ _ _ _ r' (by simpa [extCallsOk] using hx) hr' hR
         exact ⟨by simpa [openW2] using h1, by simpa [armsW2] using h2⟩)
      | simp [lowerC2, pureOp] at hr
  | split a x y e ih =>
    intro env n l k r hx hr hR
    obtain ⟨_, _, _, _, _, -, -, -, hr'⟩ := lowerC2_split_inv hr
    obtain ⟨h1, h2⟩ := ih _ _ _ _ r (by simpa [extCallsOk] using hx) hr' hR
    exact ⟨by simpa [openW2] using h1, by simpa [armsW2] using h2⟩
  | unpack a i x e ih =>
    intro env n l k r hx hr hR
    obtain ⟨_, _, -, hr'⟩ := lowerC2_unpack_inv hr
    obtain ⟨h1, h2⟩ := ih _ _ _ _ r (by simpa [extCallsOk] using hx) hr' hR
    exact ⟨by simpa [openW2] using h1, by simpa [armsW2] using h2⟩
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hx hr hR
    simp only [extCallsOk, Bool.and_eq_true] at hx
    obtain ⟨_, _, _, _, ry, rn, -, -, hy, hn, rfl⟩ := lowerC2_ifeq_inv hr
    obtain ⟨-, hRb⟩ := hR
    have hRy : RetsLe rw ry := ⟨fun ws h => hRb ⟨labName "then" n, ry.insts, ry.term⟩ (by simp) ws h,
      fun b hb ws h => hRb b (by simp [hb]) ws h⟩
    have hRn : RetsLe rw rn := ⟨fun ws h => hRb ⟨labName "else" (n + 1), rn.insts, rn.term⟩ (by simp) ws h,
      fun b hb ws h => hRb b (by simp [hb]) ws h⟩
    obtain ⟨hy1, hy2⟩ := ihy _ _ _ _ ry hx.1 hy hRy
    obtain ⟨hn1, hn2⟩ := ihn _ _ _ _ rn hx.2 hn hRn
    refine ⟨by simp [instsWeight, termWeight, openW2], ?_⟩
    intro bl hbl
    simp only [List.mem_cons, List.mem_append] at hbl
    simp only [armsW2]
    rcases hbl with (rfl | hbl) | rfl | hbl
    · simp only [blockWeight]; omega
    · have := hy2 bl hbl; omega
    · simp only [blockWeight]; omega
    · have := hn2 bl hbl; omega
  | ret a =>
    intro env n l k r _ hr hR
    obtain ⟨_, ws, -, rfl⟩ := lowerC2_ret_inv hr
    have := hR.1 ws rfl
    simp only [instsWeight, List.map_nil, List.sum_nil, termWeight, openW2, armsW2, List.not_mem_nil,
      false_imp_iff, implies_true, and_true]
    omega
  | _ => intro env n l k r _ hr; simp [lowerC2] at hr

theorem paramsR_length (d : Decl) (na : Nat) : (paramsR d na).length = na := by
  simp [paramsR]

/-- **`func2` within the bound**: the closed form of a code block `d` with
`na` argument and `nr` result words (`Obj.valWords`) whose `ret`s are of
at most `nr` words and whose extern calls are `extCallsOk`, where
`blocksOk2`'s bound holds for `d`. -/
theorem blocksOk_func2 (cx : Scc.Lower.Ctx) (ext : Bool) {d : Decl} {na nr : Nat} (name : Sym) (sc hp : List Reg)
    (hna : Scc.Obj.valWords d.argTy = some na) (hnr : Scc.Obj.valWords d.retTy = some nr)
    (hb : decide ((Scc.Obj.valWords d.argTy).getD 0 + openW2 ext ((Scc.Obj.valWords d.retTy).getD 0) d.body ≤
        maxBlockLen) && decide (armsW2 ext ((Scc.Obj.valWords d.retTy).getD 0) d.body ≤ maxBlockLen) = true)
    (hx : extCallsOk (fun g => (cx.externs.find? (·.1 == g)).isSome) ext d.body = true)
    {r : Res2} (hr : lowerC2 cx (env2 d na) 0 "entry" 0 d.body = some r) (hR : RetsLe nr r) :
    blocksOk (func2 name (paramsR d na) sc hp r) = true := by
  obtain ⟨h1, h2⟩ := lowerC2_weight cx ext nr d.body (env2 d na) 0 "entry" 0 r hx hr hR
  simp only [hna, hnr, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at hb
  simp only [blocksOk, func2, blockWeight, paramsR_length, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  refine ⟨by omega, fun b hb' => ?_⟩
  have := h2 b hb'
  simp only [blockWeight] at this
  exact decide_eq_true (by omega)

/-- **`split_id` for `func2`**: under `blocksOk_func2`'s premises, the
split leaves the lowering of the code block and its trace unchanged. -/
theorem splitFuncMarks_func2 (cx : Scc.Lower.Ctx) (ext : Bool) {d : Decl} {na nr : Nat} (name : Sym)
    (sc hp : List Reg) (hna : Scc.Obj.valWords d.argTy = some na) (hnr : Scc.Obj.valWords d.retTy = some nr)
    (hb : decide ((Scc.Obj.valWords d.argTy).getD 0 + openW2 ext ((Scc.Obj.valWords d.retTy).getD 0) d.body ≤
        maxBlockLen) && decide (armsW2 ext ((Scc.Obj.valWords d.retTy).getD 0) d.body ≤ maxBlockLen) = true)
    (hx : extCallsOk (fun g => (cx.externs.find? (·.1 == g)).isSome) ext d.body = true)
    {r : Res2} (hr : lowerC2 cx (env2 d na) 0 "entry" 0 d.body = some r) (hR : RetsLe nr r) :
    splitFuncMarks (func2 name (paramsR d na) sc hp r, marks2 d na r) =
      (func2 name (paramsR d na) sc hp r, marks2 d na r) :=
  splitFuncMarks_id (blocksOk_func2 cx ext name sc hp hna hnr hb hx hr hR)

end Spike.Lib.LowerShape
