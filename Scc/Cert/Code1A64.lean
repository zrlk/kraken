import Spike.Lib.LowerA64.Checks
import Scc.Cert.NeedA64

/-!
# The code of every stack-checked function (AArch64; A9's `fnCode1Ok`)

A9's first part (`Spike.Lib.LowerA64.fnCodeOk`) checks the `func0`-shaped
functions of the lowered IR only: one block of checked `+`s and a return.
The functions of an `Accepted1` program (`Scc/Lower/Spec1.lean`) have
parameters, several blocks (an `if`'s arms, the depth bracket of a call),
calls and the saturating `-`. This file checks **every** stack-checked
function of the IR (the lowered code blocks, and any runtime function with a
stack check), whatever its instructions, against the emitter's own code for
it, fail-closed:

* `segIn prog l ds`: the directive list `ds`, labels included, follows the
  first `label l` of `prog` verbatim, and every label of `ds` has its first
  occurrence of `prog` there. A block's code is one such segment: its
  instructions, with the labels the emitter puts inside it (a call's return
  label `.spK`, a halt loop's label);
* `fnOk1`, per function `f` (the `fi`th of the IR) at its context
  `c = fnCtx …` (as `emitItemsMaps` computes it):
  - its prologue at its label (`prologueIn`, with the parameters' stores),
    the frame within one immediate (`c.frame ≤ 4095`, 16-aligned);
  - every block `b` at its label: the code `FnCtx.inst` writes for each of
    its instructions and `FnCtx.term` for its terminator, numbered as the
    emitter numbers them (`blockItems`, `blocksOk`), one segment;
  - with a checked `+`, the local overflow block (`ovfBlk`);
  - its row of the stack need table: the frame `c.frame`, a need of at
    least that frame, every call (tail call) of a function without a row
    one of a runtime routine within the headroom (`rtDepth`, `rtOk`), and every
    call (tail call) of a function with a row needing at most the row's need
    less the frame (the row's need) (`needOk1`);
* `fnCode1Ok`: `fnOk1` for every stack-checked function.

The extraction lemmas give, from `segIn`, the `blockAt` of the run after
each label of a segment and the `labelGap` between the segment's labels
(`blockAt_of_segIn`, `segIn_label`, `labelGap_of_segIn`), and from
`fnCode1Ok`, each function's facts (`fnOk1_of_fnCode1Ok`, `blocksOk_block`).
-/

namespace Scc.Cert.Code1A64

open Kraken
open Scc.Emit.A64
open Scc.Cert.Rt.A64 (labelIdx run blockAt labelGap isIns labelIdx_spec)
open Spike.Lib.A64.Flow (prologueIn)
open Spike.Lib.LowerA64 (proL ovfBlk stkHead)

/-! ## Segments -/

/-- Every label of `ds` has its first occurrence of `prog` at its position,
`ds` starting at index `j` of `prog`. -/
def labelsAt (prog : List Directive) : Nat → List Directive → Bool
  | _, [] => true
  | j, .label l :: ds => labelIdx prog l == some j && labelsAt prog (j + 1) ds
  | j, _ :: ds => labelsAt prog (j + 1) ds

/-- **`ds` is the segment after the first `label l` of `prog`**: verbatim,
every label of `ds` at its first occurrence. -/
def segIn (prog : List Directive) (l : Label) (ds : List Directive) : Bool :=
  match labelIdx prog l with
  | some i => decide ((prog.drop (i + 1)).take ds.length = ds) && labelsAt prog (i + 1) ds
  | none => false

theorem labelsAt_append {prog : List Directive} :
    ∀ {j : Nat} {xs ys : List Directive},
      labelsAt prog j (xs ++ ys) = true → labelsAt prog (j + xs.length) ys = true
  | _, [], _, h => by simpa using h
  | j, a :: xs, ys, h => by
    have : labelsAt prog (j + 1) (xs ++ ys) = true := by
      cases a with
      | label l => simp only [List.cons_append, labelsAt, Bool.and_eq_true] at h; exact h.2
      | _ => simpa [labelsAt] using h
    have := labelsAt_append this
    rwa [List.length_cons, show j + (xs.length + 1) = j + 1 + xs.length by omega]

theorem labelsAt_prefix {prog : List Directive} :
    ∀ {j : Nat} {xs ys : List Directive}, labelsAt prog j (xs ++ ys) = true → labelsAt prog j xs = true
  | _, [], _, _ => rfl
  | j, a :: xs, ys, h => by
    cases a with
    | label l =>
      simp only [List.cons_append, labelsAt, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, labelsAt_prefix h.2⟩
    | _ => simpa [labelsAt] using labelsAt_prefix (xs := xs) (ys := ys) (by simpa [labelsAt] using h)

/-- The parts of `segIn`. -/
theorem segIn_iff {prog : List Directive} {l : Label} {ds : List Directive} :
    segIn prog l ds = true ↔ ∃ i, labelIdx prog l = some i ∧
      (prog.drop (i + 1)).take ds.length = ds ∧ labelsAt prog (i + 1) ds = true := by
  unfold segIn
  cases labelIdx prog l <;> simp

theorem take_drop_append {l : List Directive} {k : Nat} {xs ys : List Directive}
    (h : (l.drop k).take (xs ++ ys).length = xs ++ ys) :
    (l.drop k).take xs.length = xs ∧ (l.drop (k + xs.length)).take ys.length = ys := by
  constructor
  · have := congrArg (List.take xs.length) h
    simpa [List.take_take] using this
  · have := congrArg (List.drop xs.length) h
    simpa [List.drop_take, List.drop_drop] using this

/-- **A prefix of a segment is a segment.** -/
theorem segIn_prefix {prog : List Directive} {l : Label} {xs ys : List Directive}
    (h : segIn prog l (xs ++ ys) = true) : segIn prog l xs = true := by
  obtain ⟨i, hi, ht, hl⟩ := segIn_iff.mp h
  exact segIn_iff.mpr ⟨i, hi, (take_drop_append ht).1, labelsAt_prefix hl⟩

/-- **The segment after a label of a segment**: the rest of the segment
after an inner `label l'` is a segment of `l'`. -/
theorem segIn_label {prog : List Directive} {l l' : Label} {xs ys : List Directive}
    (h : segIn prog l (xs ++ .label l' :: ys) = true) : segIn prog l' ys = true := by
  obtain ⟨i, hi, ht, hl⟩ := segIn_iff.mp h
  have hl' := labelsAt_append hl
  simp only [labelsAt, Bool.and_eq_true, beq_iff_eq] at hl'
  refine segIn_iff.mpr ⟨i + 1 + xs.length, hl'.1, ?_, hl'.2⟩
  have h2 := (take_drop_append (xs := xs ++ [.label l']) (ys := ys) (by simpa using ht)).2
  simpa [Nat.add_assoc] using h2

theorem takeWhile_take {L P : List Directive} (h : L.take P.length = P) (hP : P.all isIns = true) :
    (L.takeWhile isIns).take P.length = P := by
  have hL : L = P ++ L.drop P.length := by
    conv => lhs; rw [← List.take_append_drop P.length L]
    rw [h]
  rw [hL, List.takeWhile_append_of_pos (by simpa using hP), List.take_left' rfl]

/-- **A run of instructions in a segment is code at its label**: `ys`, all
instructions, `xs.length` instructions after `l`, all instructions before
it. -/
theorem blockAt_of_segIn {prog : List Directive} {l : Label} {xs ys zs : List Directive}
    (h : segIn prog l (xs ++ ys ++ zs) = true) (hx : xs.all isIns = true) (hy : ys.all isIns = true) :
    blockAt prog l xs.length ys = true := by
  obtain ⟨i, hi, ht, -⟩ := segIn_iff.mp h
  have hp := (take_drop_append ht).1
  have hw := takeWhile_take hp (by simp [List.all_append, hx, hy])
  unfold blockAt run
  rw [hi]
  simp only [Option.isSome_some, Bool.true_and, decide_eq_true_eq]
  have := congrArg (fun L => (L.drop xs.length).take ys.length) hw
  simp only [List.drop_take, List.drop_left'] at this
  simpa [List.drop_take, List.take_take] using this

/-- **The label distance in a segment**: an inner `label l'` after the
instructions `xs` is `xs.length` instructions after `l`. -/
theorem labelGap_of_segIn {prog : List Directive} {l l' : Label} {xs ys : List Directive}
    (h : segIn prog l (xs ++ .label l' :: ys) = true) (hx : xs.all isIns = true) :
    labelGap prog l l' xs.length = true := by
  obtain ⟨i, hi, ht, hl⟩ := segIn_iff.mp h
  have hl' := labelsAt_append hl
  simp only [labelsAt, Bool.and_eq_true, beq_iff_eq] at hl'
  have hp := (take_drop_append ht).1
  unfold labelGap
  rw [hi, hl'.1]
  simp only [beq_self_eq_true, Bool.true_and, hp, hx]

/-! ## A function's code -/

/-- The code of the instructions `is`, the first numbered `k` (the
emitter's numbering: one per instruction and terminator, through the
function's blocks). -/
def instsItems (c : FnCtx) : Nat → List Scc.IR.Inst → Except String (List Item)
  | _, [] => .ok []
  | k, i :: is => do return (← c.inst k i) ++ (← instsItems c (k + 1) is)

/-- **A block's code** after its label, its first instruction numbered `k`:
its instructions' (`FnCtx.inst`), then its terminator's (`FnCtx.term`), as
`emitFunc` writes them. -/
def blockItems (c : FnCtx) (k : Nat) (b : Scc.IR.Block) : Except String (List Item) := do
  return (← instsItems c k b.insts) ++ (← c.term (k + b.insts.length) b.term)

/-- The number of the first instruction after the blocks `bs`. -/
def kAfter (bs : List Scc.IR.Block) : Nat := (bs.map fun b => b.insts.length + 1).sum

/-- **Every block's code at its label** (`segIn`), the blocks' first
instruction numbered `k`. -/
def blocksOk (prog : List Directive) (c : FnCtx) : Nat → List Scc.IR.Block → Bool
  | _, [] => true
  | k, b :: bs =>
    (match c.blockLabel b.label, blockItems c k b with
     | .ok l, .ok code => segIn prog l (directives code)
     | _, _ => false) &&
    blocksOk prog c (k + b.insts.length + 1) bs

/-- **A block's code at its label**, from `blocksOk`: the block `b` after
the blocks `pre`. -/
theorem blocksOk_block {prog : List Directive} {c : FnCtx} :
    ∀ {k : Nat} {pre post : List Scc.IR.Block} {b : Scc.IR.Block},
      blocksOk prog c k (pre ++ b :: post) = true →
      ∃ l code, c.blockLabel b.label = .ok l ∧ blockItems c (k + kAfter pre) b = .ok code ∧
        segIn prog l (directives code) = true
  | k, [], post, b, h => by
    simp only [List.nil_append, blocksOk, Bool.and_eq_true] at h
    revert h
    cases hl : c.blockLabel b.label <;> cases hc : blockItems c k b <;> simp
    exact fun h _ => ⟨_, by simpa [kAfter] using hc, h⟩
  | k, p :: pre, post, b, h => by
    simp only [List.cons_append, blocksOk, Bool.and_eq_true] at h
    obtain ⟨l, code, h1, h2, h3⟩ := blocksOk_block h.2
    refine ⟨l, code, h1, ?_, h3⟩
    simpa [kAfter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2

/-- The parameters' stores of the prologue (`emitFunc`'s, for at most
`argRegs.length` parameters, each `str` of its register to its slot): the
registers and the offsets. -/
def spills (c : FnCtx) (ps : List Scc.IR.Reg) : Option (List (XReg × Int64)) :=
  if ps.length ≤ argRegs.length then
    (ps.zip argRegs).mapM fun (p, r) => (c.slotOff p).toOption.map fun o => (r, Int64.ofInt o)
  else none

/-- The callees of a function's calls (`call`) and tail calls (`tail`). -/
def callees (f : Scc.IR.Func) : List Scc.IR.Sym × List Scc.IR.Sym :=
  (f.blocks.flatMap fun b => b.insts.filterMap fun | .call _ g _ => some g | _ => none,
   f.blocks.filterMap fun b => match b.term with | .tail g _ => some g | _ => none)

/-- **The runtime routines a stack-checked function may call, with their
depth** (AArch64): the most bytes each uses below the caller's stack
pointer at the `bl` until it returns, its frame and those of the runtime
routines it reaches (`scc_rt_abort`'s frame of `32`, or after its tail
branch a stub's of `48`; `scc_rt_print`'s `48` then `scc_rt_abort`'s;
`scc_rt_alloc`'s `160` then `scc_rt_abort`'s). Their code is the fixed
runtime text (A7). Every depth is within `Tcb.headroom`, the bytes below
the stack limit the runtime may use (`rtDepth_le_headroom`). Each covers
the regions of the routines' segment lemmas along the chain
(`Spike.Lib.RtDepthA64`). -/
def rtDepth : List (String × Nat) :=
  [(Scc.Lower.Names.abort, 48), (Scc.Lower.Names.print, 96), (Scc.Lower.Names.alloc, 208)]

/-- **A call (tail call) of a function without a row** is one of a runtime
routine whose depth is within `Tcb.headroom` (`rtDepth`). -/
def rtOk (g : String) : Bool :=
  match rtDepth.lookup g with
  | some d => decide (d ≤ Scc.IR.Tcb.headroom)
  | none => false

theorem rtDepth_le_headroom : ∀ e ∈ rtDepth, e.2 ≤ Scc.IR.Tcb.headroom := by decide

/-- **The function's row of the stack need table**: its frame is `frame`,
its need at least that frame, every call (tail call) of a function with a
row needs at most the row's need less the frame (at most the row's need),
and every call (tail call) of a function without a row is one of a runtime
routine within the headroom (`rtOk`). -/
def needOk1 (tbl : List NeedA64.Row) (name : String) (frame : Nat) (f : Scc.IR.Func) : Bool :=
  match NeedA64.row? tbl name with
  | some (_, fr, nf) =>
    fr == frame && decide (frame ≤ nf) &&
    (callees f).1.all (fun g => match NeedA64.row? tbl g with
      | some (_, _, ng) => decide (frame + ng ≤ nf)
      | none => rtOk g) &&
    (callees f).2.all (fun g => match NeedA64.row? tbl g with
      | some (_, _, ng) => decide (ng ≤ nf)
      | none => rtOk g)
  | none => false

/-- Whether a function has a checked `+` (and so the local overflow block). -/
def hasAddChk (f : Scc.IR.Func) : Bool :=
  f.blocks.any fun b => b.insts.any fun | .addChk .. => true | _ => false

/-- **The code of a stack-checked function `f`**, the `fi`th of `ir`, at
its context `c` (see the module docstring). -/
def fnOk1 (prog : List Directive) (tbl : List NeedA64.Row) (c : FnCtx) (f : Scc.IR.Func) : Bool :=
  match f.blocks, spills c f.params with
  | b0 :: _, some ps =>
    (match c.blockLabel b0.label with
     | .ok entry => prologueIn prog f.name (c.local "stack_check") entry (Int64.ofInt c.frame)
         (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c) ps
     | .error _ => false) &&
    decide (c.frame ≤ 4095) && decide (c.frame % 16 = 0) &&
    blocksOk prog c 0 f.blocks &&
    (!hasAddChk f || blockAt prog (c.local "abort_overflow") 0 ovfBlk) &&
    needOk1 tbl f.name c.frame f &&
    blockAt prog (proL c) 0 (stkHead c)
  | _, _ => false

/-- The context of the `fi`th function of `ir`, as `emitItemsMaps` computes it. -/
abbrev ctxOf (ir : Scc.IR.Program) (fi : Nat) (f : Scc.IR.Func) : FnCtx :=
  fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir argRegs.length) fi f

/-- **The code of every stack-checked function of `ir`** (`fnOk1`). -/
def fnCode1Ok (prog : List Directive) (tbl : List NeedA64.Row) (ir : Scc.IR.Program) : Bool :=
  ir.funcs.zipIdx.all fun (f, fi) => !f.checkStack || fnOk1 prog tbl (ctxOf ir fi f) f

/-- **`fnOk1` of a stack-checked function** of `ir`, from `fnCode1Ok`. -/
theorem fnOk1_of_fnCode1Ok {prog : List Directive} {tbl : List NeedA64.Row} {ir : Scc.IR.Program}
    (h : fnCode1Ok prog tbl ir = true) {f : Scc.IR.Func} {fi : Nat} (hf : (f, fi) ∈ ir.funcs.zipIdx)
    (hc : f.checkStack = true) : fnOk1 prog tbl (ctxOf ir fi f) f = true := by
  have := List.all_eq_true.mp h _ hf
  simpa [hc] using this

/-- **The facts of `fnOk1`** for a function with the entry block `b0`
and the parameters' stores `ps`. -/
theorem fnOk1_facts {prog : List Directive} {tbl : List NeedA64.Row} {c : FnCtx} {f : Scc.IR.Func}
    (h : fnOk1 prog tbl c f = true) {b0 : Scc.IR.Block} {bs : List Scc.IR.Block} (hb : f.blocks = b0 :: bs)
    {ps : List (XReg × Int64)} (hps : spills c f.params = some ps) :
    (∃ entry, c.blockLabel b0.label = .ok entry ∧
      prologueIn prog f.name (c.local "stack_check") entry (Int64.ofInt c.frame)
        (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c) ps = true) ∧
    c.frame ≤ 4095 ∧ c.frame % 16 = 0 ∧ blocksOk prog c 0 f.blocks = true ∧
    (hasAddChk f = true → blockAt prog (c.local "abort_overflow") 0 ovfBlk = true) ∧
    needOk1 tbl f.name c.frame f = true ∧ blockAt prog (proL c) 0 (stkHead c) = true := by
  unfold fnOk1 at h
  rw [hb, hps] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨?_, h2, h3, hb ▸ h4, fun ha => h5.resolve_left (by simp [ha]), h6, h7⟩
  revert h1
  cases c.blockLabel b0.label <;> simp

/-! ## Tests: a row's need covers its frame -/

-- A leaf's row passes with its need equal to its frame, and fails below it
-- (the frame is checked against the need, not only the calls' edges).
#guard needOk1 [("f", 16, 16)] "f" 16 { name := "f", params := [], blocks := [] }
#guard !needOk1 [("f", 16, 8)] "f" 16 { name := "f", params := [], blocks := [] }

/-! ## Tests: a call without a row is one of a runtime routine -/

-- A function calling (tail calling) `scc_rt_print` (`scc_rt_alloc`), which
-- have no row, passes; one calling (tail calling) an unknown function
-- without a row fails.
#guard needOk1 [("f", 16, 16)] "f" 16
    { name := "f", params := [], blocks := [⟨"b", [.call [] Scc.Lower.Names.print []], .ret []⟩] }
#guard needOk1 [("f", 16, 16)] "f" 16
    { name := "f", params := [], blocks := [⟨"b", [], .tail Scc.Lower.Names.alloc []⟩] }
#guard !needOk1 [("f", 16, 16)] "f" 16
    { name := "f", params := [], blocks := [⟨"b", [.call [] "foo" []], .ret []⟩] }
#guard !needOk1 [("f", 16, 16)] "f" 16
    { name := "f", params := [], blocks := [⟨"b", [], .tail "foo" []⟩] }

end Scc.Cert.Code1A64
