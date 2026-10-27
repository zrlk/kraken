import Spike.Lib.LowerX64.Checks
import Scc.Cert.NeedX64

/-!
# The code of every stack-checked function (x86-64; A12's `fnCode1Ok`)

The twin of `Scc/Cert/Code1A64.lean`. A9's first part
(`Spike.Lib.LowerX64.fnCodeOk`) checks the `func0`-shaped functions of the
lowered IR only: one block of checked `+`s and a return. This file checks
**every** stack-checked function of the IR (the lowered code blocks, and any
runtime function with a stack check), whatever its instructions, against the
emitter's own code for it, fail-closed:

* `segIn cells l ds`: the directives of the cells after the first `label l`
  of `cells` are `ds`, labels included, and every label of `ds` has its
  first occurrence of `cells` there. A block's code is one such segment: its
  instructions, with the labels the emitter puts inside it (a call's
  safepoint label `.Lf.xN`, a division's);
* `fnOk1`, per function `f` at its frame `frOf ir f`, its local labels
  numbered from `n` (`starts`):
  - the program has growth (the stack check's label `chk` is emitted);
  - its prologue at its label (`prologueIn`, with the parameters' stores,
    at the sizes the listing gives the cells after `chk`), the frame
    16-aligned and within a 32-bit immediate;
  - every block `b` at its label: the code `emitInst` writes for each of
    its instructions and `emitTerm` for its terminator, its local labels
    numbered as the emitter numbers them (`blockItems`, `blocksOk`), one
    segment;
  - with a checked `+`, the local overflow block (`ovfBlk`, which calls
    `scc_rt_abort`: the program's abort function must be it);
  - its row of the stack need table: the frame `fr.size + 8` below the
    entry stack pointer, a need of at least that frame, every call (tail
    call) of a function without a row one of a runtime routine within the
    headroom (`rtDepth`, `rtOk`), and every call (tail call) of a function with a row
    needing at most the row's need less the frame and the return address
    (the row's need) (`needOk1`);
* `fnCode1Ok`: `fnOk1` for every stack-checked function.

Where x86-64 differs from AArch64:
- the emitter numbers its local labels `.Lf.xN` with one counter through
  the whole program (`emitFuncs`); `starts` gives each function's first
  number from the IR (`fnLabs`: the labels each instruction and the grow
  stub take), and `startsOk` checks it against the emitter (by evaluation,
  in the tests);
- cells carry sizes, so the extraction lemmas give blocks at byte offsets
  (`cellOff` of the run after the label).

The extraction lemmas give, from `segIn`, the `blockAt` of the cells after
each label of a segment and the `labelGap` between the segment's labels
(`blockAt_of_segIn`, `segIn_label`, `labelGap_of_segIn`), and from
`fnCode1Ok`, each function's facts (`fnOk1_of_fnCode1Ok`, `fnOk1_facts`,
`blocksOk_block`).
-/

namespace Scc.Cert.Code1X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Emit.X64 (Frame Item E emitInst emitTerm labelOf argRegs directives)
open Scc.Cert.Rt.X64 (labelIdx run blockAt labelGap after after_eq blockAtB)
open Spike.Lib.X64 (cellOff)
open Spike.Lib.X64.Flow (prologueIn)
open Spike.Lib.LowerX64 (proL ovfL ovfBlk stkHead sizesAt frOf rsOf)

/-! ## Segments -/

/-- Every label of `ds` has its first occurrence of `cells` at its position,
`ds` starting at index `j` of `cells`. -/
def labelsAt (cells : List (Directive × Nat)) : Nat → List Directive → Bool
  | _, [] => true
  | j, .label l :: ds => labelIdx cells l == some j && labelsAt cells (j + 1) ds
  | j, _ :: ds => labelsAt cells (j + 1) ds

/-- **`ds` is the segment after the first `label l` of `cells`**: the
cells' directives verbatim, every label of `ds` at its first occurrence. -/
def segIn (cells : List (Directive × Nat)) (l : Label) (ds : List Directive) : Bool :=
  match labelIdx cells l with
  | some i => decide (((cells.drop (i + 1)).take ds.length).map (·.1) = ds) && labelsAt cells (i + 1) ds
  | none => false

theorem labelsAt_append {cells : List (Directive × Nat)} :
    ∀ {j : Nat} {xs ys : List Directive},
      labelsAt cells j (xs ++ ys) = true → labelsAt cells (j + xs.length) ys = true
  | _, [], _, h => by simpa using h
  | j, a :: xs, ys, h => by
    have : labelsAt cells (j + 1) (xs ++ ys) = true := by
      cases a with
      | label l => simp only [List.cons_append, labelsAt, Bool.and_eq_true] at h; exact h.2
      | _ => simpa [labelsAt] using h
    have := labelsAt_append this
    rwa [List.length_cons, show j + (xs.length + 1) = j + 1 + xs.length by omega]

theorem labelsAt_prefix {cells : List (Directive × Nat)} :
    ∀ {j : Nat} {xs ys : List Directive}, labelsAt cells j (xs ++ ys) = true → labelsAt cells j xs = true
  | _, [], _, _ => rfl
  | j, a :: xs, ys, h => by
    cases a with
    | label l =>
      simp only [List.cons_append, labelsAt, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, labelsAt_prefix h.2⟩
    | _ => simpa [labelsAt] using labelsAt_prefix (xs := xs) (ys := ys) (by simpa [labelsAt] using h)

/-- The parts of `segIn`. -/
theorem segIn_iff {cells : List (Directive × Nat)} {l : Label} {ds : List Directive} :
    segIn cells l ds = true ↔ ∃ i, labelIdx cells l = some i ∧
      ((cells.drop (i + 1)).take ds.length).map (·.1) = ds ∧ labelsAt cells (i + 1) ds = true := by
  unfold segIn
  cases labelIdx cells l <;> simp

theorem take_drop_append {L : List (Directive × Nat)} {k : Nat} {xs ys : List Directive}
    (h : ((L.drop k).take (xs ++ ys).length).map (·.1) = xs ++ ys) :
    ((L.drop k).take xs.length).map (·.1) = xs ∧ ((L.drop (k + xs.length)).take ys.length).map (·.1) = ys := by
  constructor
  · have := congrArg (List.take xs.length) h
    simpa [List.take_take, ← List.map_take] using this
  · have := congrArg (List.drop xs.length) h
    simpa [List.drop_take, List.drop_drop, ← List.map_drop] using this

/-- **A prefix of a segment is a segment.** -/
theorem segIn_prefix {cells : List (Directive × Nat)} {l : Label} {xs ys : List Directive}
    (h : segIn cells l (xs ++ ys) = true) : segIn cells l xs = true := by
  obtain ⟨i, hi, ht, hl⟩ := segIn_iff.mp h
  exact segIn_iff.mpr ⟨i, hi, (take_drop_append ht).1, labelsAt_prefix hl⟩

/-- **The segment after a label of a segment**: the rest of the segment
after an inner `label l'` is a segment of `l'`. -/
theorem segIn_label {cells : List (Directive × Nat)} {l l' : Label} {xs ys : List Directive}
    (h : segIn cells l (xs ++ .label l' :: ys) = true) : segIn cells l' ys = true := by
  obtain ⟨i, hi, ht, hl⟩ := segIn_iff.mp h
  have hl' := labelsAt_append hl
  simp only [labelsAt, Bool.and_eq_true, beq_iff_eq] at hl'
  refine segIn_iff.mpr ⟨i + 1 + xs.length, hl'.1, ?_, hl'.2⟩
  have h2 := (take_drop_append (xs := xs ++ [.label l']) (ys := ys) (by simpa using ht)).2
  simpa [Nat.add_assoc] using h2

/-- A prefix of label-free cells is a prefix of the run. -/
theorem takeWhile_take_of_all {p : Directive × Nat → Bool} :
    ∀ {t : List (Directive × Nat)} {m : Nat}, (t.take m).all p = true → (t.takeWhile p).take m = t.take m
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | a :: t, m + 1, h => by
    simp only [List.take_succ_cons, List.all_cons, Bool.and_eq_true] at h
    simp only [List.takeWhile_cons, h.1, ite_true, List.take_succ_cons, takeWhile_take_of_all h.2]

/-- The cells of a segment's label-free prefix are label-free. -/
theorem all_take_of_map {t : List (Directive × Nat)} {m : Nat} {ds : List Directive}
    (h : (t.take m).map (·.1) = ds) (hd : ds.all (fun d => !d.isLabel) = true) :
    (t.take m).all (fun c => !c.1.isLabel) = true := by
  rw [List.all_eq_true]
  intro c hc
  have := List.all_eq_true.mp hd c.1 (by rw [← h]; exact List.mem_map_of_mem hc)
  simpa using this

/-- Equal prefixes give equal slices. -/
theorem drop_take_of_take {T t : List (Directive × Nat)} {a b : Nat} (h : T.take (a + b) = t.take (a + b)) :
    (T.drop a).take b = (t.drop a).take b := by
  have := congrArg (fun L => (L.drop a).take b) h
  simpa [List.drop_take, List.take_take] using this

/-- **A label-free run in a segment is code at its label**: the cells
after `l`, `t`, hold `ys`, all non-labels, `xs.length` cells (all
non-labels, `cellOff t xs.length` bytes) after `l`. -/
theorem blockAt_of_segIn {cells : List (Directive × Nat)} {l : Label} {xs ys zs : List Directive}
    (h : segIn cells l (xs ++ ys ++ zs) = true) (hx : xs.all (fun d => !d.isLabel) = true)
    (hy : ys.all (fun d => !d.isLabel) = true) :
    ∃ t, after l cells = some t ∧ ((t.drop xs.length).take ys.length).map (·.1) = ys ∧
      blockAt cells l xs.length (cellOff t xs.length) ((t.drop xs.length).take ys.length) = true := by
  obtain ⟨i, hi, ht, -⟩ := segIn_iff.mp h
  have hp := (take_drop_append ht).1
  obtain ⟨hx', hy'⟩ := take_drop_append hp
  refine ⟨cells.drop (i + 1), by rw [after_eq, hi]; rfl, by simpa [List.drop_drop, Nat.add_comm] using hy', ?_⟩
  have hall : ((cells.drop (i + 1)).take (xs ++ ys).length).all (fun c => !c.1.isLabel) = true :=
    all_take_of_map hp (by simp [List.all_append, hx, hy])
  have hw := takeWhile_take_of_all hall
  simp only [List.length_append] at hw
  unfold blockAt run
  rw [hi]
  simp only [Option.isSome_some, Bool.true_and, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, cellOff]
  constructor
  · have := drop_take_of_take (a := 0) (b := xs.length) (by
      have h2 := congrArg (List.take xs.length) hw
      simpa [List.take_take, show min xs.length (xs.length + ys.length) = xs.length by omega] using h2)
    simp only [List.drop_zero] at this
    rw [this]
  · have hdt := drop_take_of_take hw
    have hle : ((List.drop xs.length (List.drop (i + 1) cells)).take ys.length).length ≤ ys.length := by
      simp only [List.length_take]; omega
    rw [show ((List.drop xs.length (List.drop (i + 1) cells)).take ys.length).length =
        min ((List.drop xs.length (List.drop (i + 1) cells)).take ys.length).length ys.length
        from (Nat.min_eq_left hle).symm, ← List.take_take, hdt, List.take_take, Nat.min_eq_left hle,
      ]
    rw [List.length_take, Nat.min_comm, ← List.take_take, List.take_of_length_le (by simp only [List.length_take, List.length_drop]; omega)]

/-- **The label distance in a segment**: an inner `label l'` after the
non-labels `xs` is `xs.length` cells, `cellOff t xs.length` bytes, after
`l`. -/
theorem labelGap_of_segIn {cells : List (Directive × Nat)} {l l' : Label} {xs ys : List Directive}
    (h : segIn cells l (xs ++ .label l' :: ys) = true) (hx : xs.all (fun d => !d.isLabel) = true) :
    ∃ t, after l cells = some t ∧ labelGap cells l l' xs.length (cellOff t xs.length) = true := by
  obtain ⟨i, hi, ht, hl⟩ := segIn_iff.mp h
  have hl' := labelsAt_append hl
  simp only [labelsAt, Bool.and_eq_true, beq_iff_eq] at hl'
  have hp := (take_drop_append ht).1
  refine ⟨cells.drop (i + 1), by rw [after_eq, hi]; rfl, ?_⟩
  unfold labelGap
  rw [hi, hl'.1]
  simp only [beq_self_eq_true, Bool.true_and, cellOff, Bool.and_eq_true, and_true]
  exact all_take_of_map hp hx

/-! ## A function's code -/

/-- **A block's code** after its label, as `emitFunc` writes it: its
instructions (`emitInst`, each with its call's stack map), then its
terminator (`emitTerm`). -/
def blockCode (fr : Frame) (b : Scc.IR.Block) (ms : List (Option Scc.IR.StackMap.Entry)) : E Unit := do
  for (i, sm) in b.insts.zip ms do emitInst fr sm i
  emitTerm fr b.term

/-- **A block's items**, its local labels numbered from `n`, and the next
free number. -/
def blockItems (fr : Frame) (n : Nat) (b : Scc.IR.Block) (ms : List (Option Scc.IR.StackMap.Entry)) :
    Except String (List Item × Nat) :=
  match (blockCode fr b ms).run { next := n } with
  | .ok ((), s) => .ok (s.out.reverse, s.next)
  | .error e => .error e

/-- **Every block's code at its label** (`segIn`), the blocks' local labels
numbered from `n` on. -/
def blocksOk (cells : List (Directive × Nat)) (fr : Frame) :
    Nat → List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) → Bool
  | _, [] => true
  | n, (b, ms) :: bs =>
    match blockItems fr n b ms with
    | .ok (code, n') => segIn cells (labelOf fr.fn b.label) (directives code) && blocksOk cells fr n' bs
    | .error _ => false

/-- The first local label number after the blocks `bs`, from `n`. -/
def nAfter (fr : Frame) : Nat → List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) → Nat
  | n, [] => n
  | n, (b, ms) :: bs =>
    match blockItems fr n b ms with
    | .ok (_, n') => nAfter fr n' bs
    | .error _ => n

/-- **A block's code at its label**, from `blocksOk`: the block `b` after
the blocks `pre`. -/
theorem blocksOk_block {cells : List (Directive × Nat)} {fr : Frame} :
    ∀ {n : Nat} {pre post : List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry))} {b : Scc.IR.Block}
      {ms : List (Option Scc.IR.StackMap.Entry)},
      blocksOk cells fr n (pre ++ (b, ms) :: post) = true →
      ∃ code n', blockItems fr (nAfter fr n pre) b ms = .ok (code, n') ∧
        segIn cells (labelOf fr.fn b.label) (directives code) = true
  | n, [], post, b, ms, h => by
    simp only [List.nil_append, blocksOk] at h
    revert h
    cases hc : blockItems fr n b ms with
    | error => simp
    | ok r =>
      obtain ⟨code, n'⟩ := r
      simp only [Bool.and_eq_true]
      exact fun h => ⟨code, n', by simpa [nAfter] using hc, h.1⟩
  | n, (p, pm) :: pre, post, b, ms, h => by
    simp only [List.cons_append, blocksOk] at h
    revert h
    cases hc : blockItems fr n p pm with
    | error => simp
    | ok r =>
      obtain ⟨code, n'⟩ := r
      simp only [Bool.and_eq_true]
      intro h
      obtain ⟨c, m, h1, h2⟩ := blocksOk_block h.2
      exact ⟨c, m, by simpa [nAfter, hc] using h1, h2⟩

/-- The parameters' stores of the prologue (`emitFunc`'s, for at most
`argRegs.length` parameters, each `movq` of its register to its slot): the
registers, the offsets and the cells' sizes `zs` (from the listing). -/
def spills (fr : Frame) (ps : List Scc.IR.Reg) (zs : List Nat) : Option (List (Reg64 × Int64 × Nat)) :=
  if ps.length ≤ argRegs.length && zs.length == ps.length then
    ((ps.zip argRegs).zip zs).mapM fun ((p, r), z) => (rsOf fr p).map fun o => (r, Int64.ofInt o, z)
  else none

/-- The callees of a function's calls (`call`) and tail calls (`tail`). -/
def callees (f : Scc.IR.Func) : List Scc.IR.Sym × List Scc.IR.Sym :=
  (f.blocks.flatMap fun b => b.insts.filterMap fun | .call _ g _ => some g | _ => none,
   f.blocks.filterMap fun b => match b.term with | .tail g _ => some g | _ => none)

/-- **The runtime routines a stack-checked function may call, with their
depth** (x86-64): the most bytes each uses below the caller's stack pointer
at the `call` until it returns, its return address and frame and those of
the runtime routines it reaches (`scc_rt_abort`'s frame of `32`, or after
its tail jump a stub's of `48`; `scc_rt_print`'s `48` then `scc_rt_abort`'s;
`scc_rt_alloc`'s `160` then `scc_rt_abort`'s). Their code is the fixed
runtime text (A7). Every depth is within `Tcb.headroom`, the bytes below
the stack limit the runtime may use (`rtDepth_le_headroom`). Each covers
the regions of the routines' segment lemmas along the chain
(`Spike.Lib.RtDepthX64`). -/
def rtDepth : List (String × Nat) :=
  [(Scc.Lower.Names.abort, 48), (Scc.Lower.Names.print, 96), (Scc.Lower.Names.alloc, 208)]

/-- **A call (tail call) of a function without a row** is one of a runtime
routine whose depth is within `Tcb.headroom` (`rtDepth`). -/
def rtOk (g : String) : Bool :=
  match rtDepth.lookup g with
  | some d => decide (d ≤ Scc.IR.Tcb.headroom)
  | none => false

theorem rtDepth_le_headroom : ∀ e ∈ rtDepth, e.2 ≤ Scc.IR.Tcb.headroom := by decide

/-- **The function's row of the stack need table**: its frame below the
entry stack pointer is `size + 8` (the frame and the saved `%rbp`), its
need at least that frame, every call (tail call) of a function with a row
needs at most the row's need less the frame and the return address (at
most the row's need), and every call (tail call) of a function without a
row is one of a runtime routine within the headroom (`rtOk`). -/
def needOk1 (tbl : List NeedX64.Row) (name : String) (size : Nat) (f : Scc.IR.Func) : Bool :=
  match NeedX64.row? tbl name with
  | some (_, fr, nf) =>
    fr == size + 8 && decide (size + 8 ≤ nf) &&
    (callees f).1.all (fun g => match NeedX64.row? tbl g with
      | some (_, _, ng) => decide (size + 8 + 8 + ng ≤ nf)
      | none => rtOk g) &&
    (callees f).2.all (fun g => match NeedX64.row? tbl g with
      | some (_, _, ng) => decide (ng ≤ nf)
      | none => rtOk g)
  | none => false

/-- Whether a function has a checked `+` (and so the local overflow block). -/
def hasAddChk (f : Scc.IR.Func) : Bool :=
  f.blocks.any fun b => b.insts.any fun | .addChk .. => true | _ => false

/-- The stack check's label (emitted with growth). -/
abbrev chkL (f : Scc.IR.Func) : String := labelOf f.name "chk"

/-- **The code of a stack-checked function `f`** of `ir`, its local labels
numbered from `n` (see the module docstring). -/
def fnOk1 (cells : List (Directive × Nat)) (tbl : List NeedX64.Row) (ir : Scc.IR.Program) (n : Nat)
    (f : Scc.IR.Func) : Bool :=
  match f.blocks, sizesAt cells (chkL f) 0 (5 + f.params.length) with
  | b0 :: _, zl :: zf :: z1 :: z2 :: zs :: zps =>
    match spills (frOf ir f) f.params zps with
    | some ps =>
      ir.growth.isSome &&
      prologueIn cells f.name (chkL f) (labelOf f.name b0.label) (Int64.ofInt (frOf ir f).size)
        (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL (frOf ir f)) zl zf z1 z2 zs ps &&
      decide ((frOf ir f).size < 2 ^ 31) && decide ((frOf ir f).size % 16 = 0) &&
      blocksOk cells (frOf ir f) n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) &&
      (!hasAddChk f || (ir.abortFn == Scc.Lower.Names.abort && blockAtB cells (ovfL (frOf ir f)) 0 ovfBlk)) &&
      needOk1 tbl f.name (frOf ir f).size f &&
      blockAtB cells (proL (frOf ir f)) 0 stkHead
    | none => false
  | _, _ => false

/-! ## The local labels' numbering -/

/-- The local labels (`freshL`) the emitter takes for an instruction, with
safepoints recorded (`maps`) or not. -/
def instLabs (maps : Bool) : Scc.IR.Inst → Nat
  | .bin .udiv _ _ _ | .bin .urem _ _ _ => 2
  | .bin .sdiv _ _ _ | .bin .srem _ _ _ => 3
  | .clone .. => 1
  | .call .. => if maps then 1 else 0
  | _ => 0

/-- The local labels the emitter takes for a function: its instructions',
and the grow stub's safepoint (a stack-checked function with growth). -/
def fnLabs (ir : Scc.IR.Program) (f : Scc.IR.Func) : Nat :=
  (f.blocks.map fun b => (b.insts.map (instLabs ir.growth.isSome)).sum).sum +
    if f.checkStack && ir.growth.isSome then 1 else 0

/-- **Each function with its first local label number**, the first of the
functions `fs` numbered from `n` (as `emitFuncs` numbers them). -/
def starts (ir : Scc.IR.Program) : Nat → List Scc.IR.Func → List (Scc.IR.Func × Nat)
  | _, [] => []
  | n, f :: fs => (f, n) :: starts ir (n + fnLabs ir f) fs

/-- `startsOk`'s walk: each function's `emitFuncAt` from `n` ends at
`n + fnLabs`. -/
def startsOkAux (ir : Scc.IR.Program) (areas : List (Scc.IR.Sym × Nat)) : Nat → List Scc.IR.Func → Bool
  | _, [] => true
  | n, f :: fs =>
    match Scc.Emit.X64.emitFuncAt ir areas f n with
    | .ok (_, n', _) => n' == n + fnLabs ir f && startsOkAux ir areas n' fs
    | .error _ => false

/-- **`starts` is the emitter's numbering** of `ir` (checked by evaluation
in the tests; A12 does not depend on it: a wrong number fails `segIn`). -/
def startsOk (ir : Scc.IR.Program) : Bool :=
  match Scc.Emit.X64.emitPre ir with
  | .ok areas => startsOkAux ir areas 0 ir.funcs
  | .error _ => false

/-- **The code of every stack-checked function of `ir`** (`fnOk1`). -/
def fnCode1Ok (cells : List (Directive × Nat)) (tbl : List NeedX64.Row) (ir : Scc.IR.Program) : Bool :=
  (starts ir 0 ir.funcs).all fun (f, n) => !f.checkStack || fnOk1 cells tbl ir n f

/-- **`fnOk1` of a stack-checked function** of `ir`, from `fnCode1Ok`. -/
theorem fnOk1_of_fnCode1Ok {cells : List (Directive × Nat)} {tbl : List NeedX64.Row} {ir : Scc.IR.Program}
    (h : fnCode1Ok cells tbl ir = true) {f : Scc.IR.Func} {n : Nat} (hf : (f, n) ∈ starts ir 0 ir.funcs)
    (hc : f.checkStack = true) : fnOk1 cells tbl ir n f = true := by
  have := List.all_eq_true.mp h _ hf
  simpa [hc] using this

/-- **The facts of `fnOk1`** for a function with the entry block `b0`,
the prologue's cells' sizes and the parameters' stores `ps`. -/
theorem fnOk1_facts {cells : List (Directive × Nat)} {tbl : List NeedX64.Row} {ir : Scc.IR.Program} {n : Nat}
    {f : Scc.IR.Func} (h : fnOk1 cells tbl ir n f = true) {b0 : Scc.IR.Block} {bs : List Scc.IR.Block}
    (hb : f.blocks = b0 :: bs) {zl zf z1 z2 zs : Nat} {zps : List Nat}
    (hz : sizesAt cells (chkL f) 0 (5 + f.params.length) = zl :: zf :: z1 :: z2 :: zs :: zps)
    {ps : List (Reg64 × Int64 × Nat)} (hps : spills (frOf ir f) f.params zps = some ps) :
    ir.growth.isSome = true ∧
    prologueIn cells f.name (chkL f) (labelOf f.name b0.label) (Int64.ofInt (frOf ir f).size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL (frOf ir f)) zl zf z1 z2 zs ps = true ∧
    (frOf ir f).size < 2 ^ 31 ∧ (frOf ir f).size % 16 = 0 ∧
    blocksOk cells (frOf ir f) n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) = true ∧
    (hasAddChk f = true → ir.abortFn = Scc.Lower.Names.abort ∧ blockAtB cells (ovfL (frOf ir f)) 0 ovfBlk = true) ∧
    needOk1 tbl f.name (frOf ir f).size f = true ∧ blockAtB cells (proL (frOf ir f)) 0 stkHead = true := by
  unfold fnOk1 at h
  rw [hb, hz] at h
  simp only [hps, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h0, h1, h2, h3, hb ▸ h4, fun ha => h5.resolve_left (by simp [ha]), h6, h7⟩

/-! ## Tests: a row's need covers its frame -/

-- A leaf's row passes with its need equal to its frame, and fails below it
-- (the frame is checked against the need, not only the calls' edges).
#guard needOk1 [("f", 24, 24)] "f" 16 { name := "f", params := [], blocks := [] }
#guard !needOk1 [("f", 24, 16)] "f" 16 { name := "f", params := [], blocks := [] }

/-! ## Tests: a call without a row is one of a runtime routine -/

-- A function calling (tail calling) `scc_rt_print` (`scc_rt_alloc`), which
-- have no row, passes; one calling (tail calling) an unknown function
-- without a row fails.
#guard needOk1 [("f", 24, 24)] "f" 16
    { name := "f", params := [], blocks := [⟨"b", [.call [] Scc.Lower.Names.print []], .ret []⟩] }
#guard needOk1 [("f", 24, 24)] "f" 16
    { name := "f", params := [], blocks := [⟨"b", [], .tail Scc.Lower.Names.alloc []⟩] }
#guard !needOk1 [("f", 24, 24)] "f" 16
    { name := "f", params := [], blocks := [⟨"b", [.call [] "foo" []], .ret []⟩] }
#guard !needOk1 [("f", 24, 24)] "f" 16
    { name := "f", params := [], blocks := [⟨"b", [], .tail "foo" []⟩] }

end Scc.Cert.Code1X64
