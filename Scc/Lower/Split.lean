import Scc.IR.BlockLen
import Scc.Lower.Builder

/-!
# Splitting long blocks

`splitFunc` cuts every block of a function whose weight (`Scc.IR.blockWeight`,
the first block with its function's parameters) exceeds `maxBlockLen` into
pieces within the bound, each piece but the last ended by a `jmp` to the next.
A function whose blocks are all within the bound is left as it is
(`splitFunc_id`), and the split of any function with no single instruction
or terminator over the bound is within it (`blocksOk_splitFunc`).

**Why.** The scheduler drives a thread to a safe point (a block entry) with
hardware breakpoints, so the time a thread takes to reach one is bounded by
the longest straight-line block it can be in.  Bounding every block's weight
bounds its bytes (`bytesPerWeight` per unit, on both ISAs).

**Where.** The program lowering (`lowerWithMarks`) applies the pass to the
user functions and the thread trampolines only, **never to the runtime
routines**: in the whole-program theorems (`Scc/Lower/InvProg.lean`) the
runtime functions are `rtFuncs cfg.arch cfg.layout …`, symbolic in the
layout, so `splitFunc_id` could not be discharged for them there.  For them
the bound is checked per program on the emitted bytes instead: the trusted
granule checker's `#guard`, backed by a development `#guard` at the default
layout and the emitter's own error when a routine does not fit a granule.

**Labels.** Piece `k ≥ 1` of block `l` is `l.k` (`pieceLabel`).  No label the
lowering makes contains `.` (`freshLabel`: `then3`, `deep7`, …; the runtime's
fixed and fresh labels likewise), so the new labels are fresh; `.` is valid in
an assembler label (the x64 emitter writes `.L<f>.<l>` verbatim, the AArch64
emitter maps it to `_` under a unique block-index prefix).

**Placement traces.** A call's return point `Node.ret l i` names the call by
its index in block `l`; a call that moves to piece `k` at index `j` becomes
`Node.ret (pieceLabel l k) j` (`remapNode`).  Block starts keep their labels
(piece 0 of `l` is `l`).
-/

open Scc.IR

namespace Scc.Lower

/-- The label of piece `k` of block `l`: `l` itself for the first piece. -/
def pieceLabel (l : Label) (k : Nat) : Label := if k = 0 then l else s!"{l}.{k}"

/-- Greedy cut of instructions into pieces of weight at most `cap` with room
for the closing `jmp` (one unit).  `acc` is the weight of the open piece
`cur` (reversed); returns the closed pieces, the weight of the last (open)
piece, and the last piece.  A piece is never closed empty, so an instruction
heavier than `cap` gets a piece of its own. -/
def cutInsts (cap : Nat) : Nat → List Inst → List Inst → List (List Inst) × Nat × List Inst
  | acc, cur, [] => ([], acc, cur.reverse)
  | acc, cur, i :: is =>
    if cap < acc + instWeight i + 1 && !cur.isEmpty then
      let (cs, a, last) := cutInsts cap (instWeight i) [i] is
      (cur.reverse :: cs, a, last)
    else cutInsts cap (acc + instWeight i) (i :: cur) is

/-- The pieces of block `b`'s instructions, `extra` units already in its first
piece (the parameters, for a function's first block).  A block within the
bound is one piece.  Otherwise the greedy cut, and the terminator alone in a
last, empty piece if it does not fit after the last instructions. -/
def piecesOf (extra : Nat) (b : Block) : List (List Inst) :=
  if extra + blockWeight b ≤ maxBlockLen then [b.insts]
  else
    let (cs, a, last) := cutInsts maxBlockLen extra [] b.insts
    if maxBlockLen < a + termWeight b.term && !last.isEmpty then cs ++ [last, []]
    else cs ++ [last]

/-- Each block with its pieces; `extra` units on the first block. -/
def planOf : Nat → List Block → List (Block × List (List Inst))
  | _, [] => []
  | e, b :: bs => (b, piecesOf e b) :: planOf 0 bs

/-- The split plan of a function: the first block carries the parameters. -/
def splitPlan (f : Func) : List (Block × List (List Inst)) := planOf f.params.length f.blocks

/-- The blocks of pieces `ps` of a block labelled `l` with terminator `t`,
from piece number `k`: each jumps to the next, the last ends with `t`. -/
def mkBlocks (l : Label) (t : Term) : Nat → List (List Inst) → List Block
  | _, [] => []
  | k, is :: rest => match rest with
    | [] => [⟨pieceLabel l k, is, t⟩]
    | _ :: _ => ⟨pieceLabel l k, is, .jmp (pieceLabel l (k + 1))⟩ :: mkBlocks l t (k + 1) rest

/-- **The split function**: every block replaced by the blocks of its pieces. -/
def splitFunc (f : Func) : Func :=
  { f with blocks := (splitPlan f).flatMap fun (b, ps) => mkBlocks b.label b.term 0 ps }

/-- The piece number and index within it of instruction `i` of pieces `ps`,
counting pieces from `k` (the last piece takes any index past the others). -/
def locate : Nat → Nat → List (List Inst) → Nat × Nat
  | k, i, [] => (k, i)
  | k, i, is :: rest => match rest with
    | [] => (k, i)
    | _ :: _ => if i < is.length then (k, i) else locate (k + 1) (i - is.length) rest

/-- A node of `f` as a node of `splitFunc f` (see the module docstring). -/
def remapNode (f : Func) : Node → Node
  | .block l => .block l
  | .ret l i => match (splitPlan f).find? (·.1.label == l) with
    | some (b, ps) => let (k, j) := locate 0 i ps; .ret (pieceLabel b.label k) j
    | none => .ret l i

/-- A placement trace of `f` as one of `splitFunc f`. -/
def remapMarks (f : Func) (ms : Array (Node × Point)) : Array (Node × Point) :=
  ms.map fun (n, p) => (remapNode f n, p)

/-- **Split a function with its placement trace.** -/
def splitFuncMarks (x : Func × Array (Node × Point)) : Func × Array (Node × Point) :=
  (splitFunc x.1, remapMarks x.1 x.2)

/-! ## Functions within the bound are unchanged -/

theorem piecesOf_ok {e : Nat} {b : Block} (h : e + blockWeight b ≤ maxBlockLen) :
    piecesOf e b = [b.insts] := by
  simp [piecesOf, h]

theorem planOf_ok (e : Nat) (b : Block) (bs : List Block) (h0 : e + blockWeight b ≤ maxBlockLen)
    (h : ∀ c ∈ bs, blockWeight c ≤ maxBlockLen) :
    planOf e (b :: bs) = (b :: bs).map fun c => (c, [c.insts]) := by
  induction bs generalizing e b with
  | nil => simp [planOf, piecesOf_ok h0]
  | cons c cs ih =>
    rw [planOf, piecesOf_ok h0, ih 0 c (by simpa using h c (by simp)) (fun d hd => h d (by simp [hd]))]
    simp

/-- **`blocksOk` functions are not split.** -/
theorem splitPlan_ok {f : Func} (h : blocksOk f = true) :
    splitPlan f = f.blocks.map fun c => (c, [c.insts]) := by
  unfold splitPlan
  unfold blocksOk at h
  split at h
  · next hb => simp [hb, planOf]
  · next b bs hb =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    rw [hb]
    exact planOf_ok _ b bs h.1 h.2

theorem flatMap_mkBlocks_id (bs : List Block) :
    ((bs.map fun c => (c, [c.insts])).flatMap fun (b, ps) => mkBlocks b.label b.term 0 ps) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons, List.flatMap_cons] at ih ⊢; rw [ih]; simp [mkBlocks, pieceLabel]

/-- **`split_id`**: a function whose blocks are all within the bound is its
own split. -/
theorem splitFunc_id {f : Func} (h : blocksOk f = true) : splitFunc f = f := by
  unfold splitFunc
  rw [splitPlan_ok h, flatMap_mkBlocks_id]

theorem remapNode_id {f : Func} (h : blocksOk f = true) (n : Node) : remapNode f n = n := by
  cases n with
  | block l => rfl
  | ret l i =>
    simp only [remapNode, splitPlan_ok h]
    cases hf : (f.blocks.map fun c => (c, [c.insts])).find? (·.1.label == l) with
    | none => rfl
    | some x =>
      have hm := List.mem_of_find?_eq_some hf
      have hl := List.find?_some hf
      simp only [List.mem_map] at hm
      obtain ⟨c, -, rfl⟩ := hm
      simp only [beq_iff_eq] at hl
      simp [locate, pieceLabel, hl]

theorem remapMarks_id {f : Func} (h : blocksOk f = true) (ms : Array (Node × Point)) :
    remapMarks f ms = ms := by
  unfold remapMarks
  conv => rhs; rw [← Array.map_id ms]
  congr 1
  funext ⟨n, p⟩
  simp [remapNode_id h]

/-- **`split_id` with the placement trace.** -/
theorem splitFuncMarks_id {x : Func × Array (Node × Point)} (h : blocksOk x.1 = true) :
    splitFuncMarks x = x := by
  unfold splitFuncMarks
  rw [splitFunc_id h, remapMarks_id h]

/-! ## Split functions are within the bound

`splitFunc f` is `blocksOk` whenever no single instruction (with the closing
`jmp`) or terminator is heavier than the bound minus the parameters
(`splittable`): the only case the greedy cut cannot help.  Every function
the emitters accept is `splittable`: at most `maxArgs` = 32 parameters, and
the heaviest instruction (a call with `maxArgs` arguments and `maxRets`
results) and terminator weigh 39 and 33 units, far under 512. -/

/-- No instruction or terminator of `f` is too heavy to fit a piece of its
own, counting the parameters on every block. -/
def splittable (f : Func) : Bool :=
  f.blocks.all fun b =>
    b.insts.all (fun i => decide (f.params.length + instWeight i + 1 ≤ maxBlockLen)) &&
      decide (f.params.length + termWeight b.term ≤ maxBlockLen)

/-- Blocks within the bound, the first one with `e` extra units. -/
def blocksFit : Nat → List Block → Prop
  | _, [] => True
  | e, b :: bs => e + blockWeight b ≤ maxBlockLen ∧ blocksFit 0 bs

/-- Closed pieces within the bound with their closing `jmp`, the first one
with `e` extra units. -/
def piecesFit : Nat → List (List Inst) → Prop
  | _, [] => True
  | e, p :: ps => e + instsWeight p + 1 ≤ maxBlockLen ∧ piecesFit 0 ps

/-- The pieces of a block ending with `t` within the bound: each but the last
with its `jmp`, the last with `t`; the first with `e` extra units. -/
def piecesFitT (t : Term) : Nat → List (List Inst) → Prop
  | _, [] => True
  | e, [p] => e + instsWeight p + termWeight t ≤ maxBlockLen
  | e, p :: ps@(_ :: _) => e + instsWeight p + 1 ≤ maxBlockLen ∧ piecesFitT t 0 ps

theorem instsWeight_nil : instsWeight [] = 0 := rfl

theorem instsWeight_append (xs ys : List Inst) :
    instsWeight (xs ++ ys) = instsWeight xs + instsWeight ys := by
  simp [instsWeight, List.sum_append]

theorem instsWeight_singleton (i : Inst) : instsWeight [i] = instWeight i := by
  simp [instsWeight]

theorem blocksFit_zero_iff (bs : List Block) :
    blocksFit 0 bs ↔ ∀ b ∈ bs, blockWeight b ≤ maxBlockLen := by
  induction bs with
  | nil => simp [blocksFit]
  | cons b bs ih => simp [blocksFit, ih]

theorem blocksOk_iff (f : Func) : blocksOk f = true ↔ blocksFit f.params.length f.blocks := by
  unfold blocksOk
  split
  · next h => simp [h, blocksFit]
  · next b bs h => simp [h, blocksFit, blocksFit_zero_iff]

theorem blocksFit_append {e : Nat} {xs ys : List Block} (hx : blocksFit e xs) (hne : xs ≠ [])
    (hy : blocksFit 0 ys) : blocksFit e (xs ++ ys) := by
  induction xs generalizing e with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := hx
    refine ⟨h1, ?_⟩
    cases xs with
    | nil => simpa using hy
    | cons _ _ => exact ih h2 (by simp)

/-- The cut keeps every closed piece and the open one within the bound. -/
theorem cutInsts_fit {E : Nat} : ∀ (is : List Inst) (e acc : Nat) (cur : List Inst)
    (cs : List (List Inst)) (a : Nat) (last : List Inst),
    cutInsts maxBlockLen acc cur is = (cs, a, last) →
    acc = e + instsWeight cur.reverse → acc + 1 ≤ maxBlockLen → e ≤ E →
    (∀ i ∈ is, E + instWeight i + 1 ≤ maxBlockLen) →
    piecesFit e cs ∧ a = (if cs = [] then e else 0) + instsWeight last ∧ a + 1 ≤ maxBlockLen ∧
      (last = [] → cs = [] ∧ cur = [] ∧ is = [])
  | [], e, acc, cur, cs, a, last, h, hacc, hle, _, _ => by
    simp only [cutInsts, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨trivial, by simpa using hacc, hle, fun h => ⟨rfl, by simpa using h, rfl⟩⟩
  | i :: is, e, acc, cur, cs, a, last, h, hacc, hle, heE, hw => by
    have hwi := hw i (by simp)
    have hw' : ∀ j ∈ is, E + instWeight j + 1 ≤ maxBlockLen := fun j hj => hw j (by simp [hj])
    simp only [cutInsts] at h
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
      rcases hr : cutInsts maxBlockLen (instWeight i) [i] is with ⟨cs', a', last'⟩
      rw [hr] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨f1, f2, f3, f4⟩ := cutInsts_fit is 0 (instWeight i) [i] cs' a' last' hr
        (by simp [instsWeight_singleton]) (by omega) (Nat.zero_le _) hw'
      refine ⟨⟨by omega, f1⟩, by simpa using f2, f3, fun hl => ?_⟩
      exact absurd (f4 hl).2.1 (by simp)
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        not_and] at hc
      have hle' : acc + instWeight i + 1 ≤ maxBlockLen := by
        by_cases hcur : cur = []
        · subst hcur; simp [instsWeight_nil] at hacc; omega
        · exact Nat.le_of_not_lt fun hlt => hc hlt hcur
      obtain ⟨f1, f2, f3, f4⟩ := cutInsts_fit is e (acc + instWeight i) (i :: cur) cs a last h
        (by simp [instsWeight_append, instsWeight_singleton, hacc]; omega) hle' heE hw'
      exact ⟨f1, f2, f3, fun hl => absurd (f4 hl).2.1 (by simp)⟩

theorem piecesFitT_append {t : Term} : ∀ {e : Nat} {cs rest : List (List Inst)},
    piecesFit e cs → rest ≠ [] → piecesFitT t (if cs = [] then e else 0) rest →
    piecesFitT t e (cs ++ rest)
  | _, [], _, _, _, hr => by simpa using hr
  | e, c :: cs, rest, hc, hne, hr => by
    obtain ⟨h1, h2⟩ := hc
    have ih := piecesFitT_append (t := t) h2 hne
    cases cs with
    | nil =>
      obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [List.cons_append, List.nil_append, piecesFitT]
      exact ⟨h1, by simpa using hr⟩
    | cons c' cs' =>
      simp only [List.cons_append, piecesFitT]
      refine ⟨h1, ?_⟩
      have := ih (by simpa using hr)
      simpa only [List.cons_append] using this

/-- **The pieces of a block are within the bound.** -/
theorem piecesOf_fit {E e : Nat} {b : Block} (heE : e ≤ E)
    (hi : ∀ i ∈ b.insts, E + instWeight i + 1 ≤ maxBlockLen) (ht : E + termWeight b.term ≤ maxBlockLen) :
    piecesFitT b.term e (piecesOf e b) := by
  unfold piecesOf
  split
  · next h => simpa [piecesFitT, blockWeight, Nat.add_assoc] using h
  · next h =>
    rcases hr : cutInsts maxBlockLen e [] b.insts with ⟨cs, a, last⟩
    obtain ⟨f1, f2, f3, f4⟩ := cutInsts_fit b.insts e e [] cs a last hr (by simp [instsWeight_nil])
      (by have := termWeight_pos b.term; simp only [blockWeight] at h; omega) heE hi
    simp only
    by_cases hl : last = []
    · obtain ⟨rfl, -, hb⟩ := f4 hl
      subst hl
      simp only [blockWeight, hb, instsWeight_nil] at h
      omega
    · have hne : last.isEmpty = false := by simpa using hl
      split
      · next hc =>
        refine piecesFitT_append f1 (by simp) ?_
        generalize (if cs = [] then e else 0) = x at f2 ⊢
        simp only [piecesFitT, instsWeight_nil]
        omega
      · next hc =>
        simp only [hne, Bool.not_false, Bool.and_true, decide_eq_true_eq] at hc
        refine piecesFitT_append f1 (by simp) ?_
        generalize (if cs = [] then e else 0) = x at f2 ⊢
        simp only [piecesFitT]
        omega

theorem mkBlocks_fit {l : Label} {t : Term} : ∀ {k e : Nat} {ps : List (List Inst)},
    piecesFitT t e ps → blocksFit e (mkBlocks l t k ps)
  | _, _, [], _ => by simp [mkBlocks, blocksFit]
  | _, _, [p], h => by
    simp only [piecesFitT] at h
    simp only [mkBlocks, blocksFit, blockWeight]
    exact ⟨by omega, trivial⟩
  | _, _, p :: q :: ps, h => by
    simp only [piecesFitT] at h
    simp only [mkBlocks, blocksFit, blockWeight, termWeight]
    exact ⟨by omega, mkBlocks_fit h.2⟩

theorem piecesOf_ne_nil (e : Nat) (b : Block) : piecesOf e b ≠ [] := by
  unfold piecesOf; split
  · simp
  · simp only; split <;> simp

theorem mkBlocks_ne_nil (l : Label) (t : Term) (k : Nat) :
    ∀ {ps : List (List Inst)}, ps ≠ [] → mkBlocks l t k ps ≠ []
  | [], h => absurd rfl h
  | [_], _ => by simp [mkBlocks]
  | _ :: _ :: _, _ => by simp [mkBlocks]

theorem planOf_fit {E : Nat} : ∀ {e : Nat} {bs : List Block}, e ≤ E →
    (∀ b ∈ bs, (∀ i ∈ b.insts, E + instWeight i + 1 ≤ maxBlockLen) ∧ E + termWeight b.term ≤ maxBlockLen) →
    blocksFit e ((planOf e bs).flatMap fun (b, ps) => mkBlocks b.label b.term 0 ps)
  | _, [], _, _ => trivial
  | e, b :: bs, heE, h => by
    simp only [planOf, List.flatMap_cons]
    obtain ⟨hi, ht⟩ := h b (by simp)
    exact blocksFit_append (mkBlocks_fit (piecesOf_fit heE hi ht))
      (mkBlocks_ne_nil _ _ _ (piecesOf_ne_nil _ _))
      (planOf_fit (Nat.zero_le E) fun c hc => h c (by simp [hc]))

/-- **The split of a `splittable` function is within the bound.** -/
theorem blocksOk_splitFunc {f : Func} (h : splittable f = true) : blocksOk (splitFunc f) = true := by
  rw [blocksOk_iff]
  simp only [splittable, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact planOf_fit (Nat.le_refl _) h

/-! ## Tests -/


/-- A straight-line function of `n` checked additions. -/
private def longF (params n : Nat) (t : Term := .ret [.reg "x"]) : Func :=
  { name := "f", params := (List.range params).map (s!"p{·}"),
    blocks := [⟨"entry", (List.replicate n (.addChk "x" (.reg "x") (.imm 1))), .jmp "next"⟩,
      ⟨"next", [.call ["a", "b"] "g" [.reg "x"]] ++ List.replicate n (.mov "x" (.imm 0)) ++
        [.call ["c"] "g" []], t⟩] }

/-- Every block of the split within the bound, the first with the params. -/
private def splitOk (f : Func) : Bool := blocksOk (splitFunc f)

#guard splitOk (longF 0 2000)
#guard splitOk (longF 32 2000 (.tail "g" ((List.range 32).map fun _ => .imm 0)))
#guard splitOk (longF 3 511)
#guard splitOk (longF 0 1022 (.ret ((List.range 6).map fun _ => .imm 0)))
#guard splittable (longF 0 2000) && splittable (longF 32 2000)
-- an instruction too heavy for a piece of its own: not `splittable`
#guard !splittable (longF 511 10)
#guard (splitFunc (longF 0 2000)).blocks.length == 8
#guard splitFunc (longF 0 300) == longF 0 300
-- the instructions are kept, in order, and the pieces are chained
#guard ((splitFunc (longF 5 2000)).blocks.flatMap (·.insts)) == (longF 5 2000).blocks.flatMap (·.insts)
#guard ((splitFunc (longF 0 1000)).blocks.map (·.label)) ==
  ["entry", "entry.1", "next", "next.1"]
-- the return point of the second call of `next` moves to the last piece (the
-- first piece has the first call, 4 units, and 507 moves)
#guard remapNode (longF 0 1000) (.ret "next" 1001) == .ret "next.1" (1001 - 508)
#guard remapNode (longF 0 1000) (.ret "next" 0) == .ret "next" 0
#guard ((splitFunc (longF 0 1000)).blocks.find? (·.label == "next.1")).map (·.insts.getLast?) ==
  some (some (.call ["c"] "g" []))

-- the pass reduces in the kernel (structural recursion throughout), as the
-- `decide +kernel` checks of whole lowerings need
example : (splitFunc (longF 0 600)).blocks.length = 4 := by decide +kernel
example : (remapNode (longF 0 600) (.ret "next" 601) == .ret "next.1" (601 - 508)) = true := by decide +kernel

end Scc.Lower
