/-
**The placement checks of a lowered function** (x86-64); the twin of
`Spike/Lib/LowerA64/Checks.lean`: the closed Booleans `proInC` (the emitted
prologue, `Spike/Lib/LowerX64/ProIn.lean`) and `bodyIn` (the lowered body,
`Spike/Lib/LowerX64/BodyIn.lean`), apart from their soundness so that
`PlaceOK` (`Scc/Cert/PlaceOKX64.lean`) reads them without the segment
proofs; and `fnCodeOk`, the check of every lowered code block of an IR
program (A9).

Where x86-64 differs from AArch64:
- the frame is the emitter's `Frame` (`frOf`: `frameOf` at the program's
  argument areas, `maps` the program's growth), not a context with a
  function index: the labels are `labelOf f.name _`, the same for every
  index;
- the prologue's cells' sizes are parameters of `proInC`; `fnCodeOk` reads
  them off the listing (`proInS`: the sizes of the five cells after the
  stack check's label), and `fnCodeOk_func0` gives them back as witnesses;
- a body's blocks (`bodyBlks`, `InBody`) are sized cells at byte offsets,
  so they depend on the listing (AArch64: directives at instruction
  offsets, from the context alone).
-/
import Spike.Lib.LowerX64.Construct
import Spike.Lib.LowerX64.Across
import Spike.Lib.X64CodeSegs
import Scc.Cert.StartsX64

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (prologueIn)
open Scc.Emit.X64 (Item i64 i32 xm xr or_ oi rel mem labelOf frameOf argRegs)
open Scc.Cert.Rt.X64 (blockAtB after cellRun dropBytes labelGapB)

/-! ## The prologue -/

/-- The stack-limit branch's target in the emitted prologue. -/
def proL (fr : Scc.Emit.X64.Frame) : String := labelOf fr.fn "stk"

/-- **The grow stub's first cell** the emitter places at `proL` with growth:
`pushq %rdi` (the first argument register's save), at its cell size. -/
def stkHead : List (Directive × Nat) := [(i64 (.push (or_ .rdi)), 1)]

/-- **The emitted prologue of `fr`'s function is in `cells`**, `fn` its
label and `entry` its body's first label, at the cells' sizes `zl zf z1 z2
zs`. -/
def proInC (cells : List (Directive × Nat)) (fr : Scc.Emit.X64.Frame) (fn entry : String)
    (zl zf z1 z2 zs : Nat) : Bool :=
  prologueIn cells fn (labelOf fr.fn "chk") entry (Int64.ofInt fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
    (proL fr) zl zf z1 z2 zs []

/-! ## The body -/

/-- **The function's overflow abort label.** -/
def ovfL (fr : Scc.Emit.X64.Frame) : String := labelOf fr.fn "ovf"

/-- **The function-local overflow block** the emitter places at `ovfL`
when the body has an `addChk`: `movl $1, %edi; call scc_rt_abort` (the
abort's code for overflow, then the call; the `ud2` after it is dead), at
its cell sizes. -/
def ovfBlk : List (Directive × Nat) :=
  [(i32 (.mov (xr .rdi) (oi 1)), 5), (i64 (.call (rel "scc_rt_abort")), 5)]

/-- **The store of a checked `+`'s result**: `movq %rax, off(%rbp)`. -/
def stDir (off : Int) : Directive := i64 (.mov (xm (mem .rbp off)) (or_ .rax))

/-- The add construct's directives: both operands' loads, the checked add. -/
def addDirs (fr : Scc.Emit.X64.Frame) (la lb : List Item) : List Directive :=
  dirs (la ++ lb ++ addChecked (ovfL fr))

/-- The return's directives: the operand's load, the epilogue, `ret`. -/
def retDirs (l : List Item) : List Directive := dirs (l ++ epiItems)

/-- **The sizes of the `n` cells `off` bytes after `label l`** (fewer if
the run ends; none if `off` is not on a cell boundary). -/
def sizesAt (cells : List (Directive × Nat)) (l : String) (off n : Nat) : List Nat :=
  match after l cells with
  | some t =>
    match dropBytes (cellRun t) off with
    | some r => (r.take n).map (·.2)
    | none => []
  | none => []

/-- **The directives `ds` are the cells `off` bytes after `label l`**, at
the sizes the listing gives them. -/
def blkAt (cells : List (Directive × Nat)) (l : String) (off : Nat) (ds : List Directive) : Bool :=
  (sizesAt cells l off ds.length).length == ds.length && blockAtB cells l off (ds.zip (sizesAt cells l off ds.length))

/-- The return's directives before its label (P5): the operand's load and
the teardown. -/
def tearDirs (l : List Item) : List Directive := dirs (l ++ tearItems)

/-- **A lowered body's code is in `cells`** (P5). The body's blocks are
read in the label-free runs the emitter's labels delimit: the current
label `L` (the body's label, then each fresh label), `o` bytes into its run;
`n` is the next fresh label's number (`retL fr.fn n`). Each checked `+`'s
add block ends `L`'s run, its fall-through label `retL fr.fn n` follows
(`labelGapB`) and starts the store's run; the return's load and teardown
end the run and its label `retL fr.fn n` starts `[ret]`. -/
def bodyIn (cells : List (Directive × Nat)) (fr : Scc.Emit.X64.Frame) :
    String → Nat → Nat → List Scc.IR.Inst → List Scc.IR.Operand → Bool
  | L, n, o, [], [w] =>
    match getOp fr .rax w with
    | .ok lw =>
      blkAt cells L o (tearDirs lw) &&
        labelGapB cells L (retL fr.fn n) (o + (sizesAt cells L o (tearDirs lw).length).sum) &&
        blkAt cells (retL fr.fn n) 0 [i64 .ret]
    | .error _ => false
  | L, n, o, .addChk d a b :: is, ws =>
    match getOp fr .rax a, getOp fr .rcx b, rsOf fr d with
    | .ok la, .ok lb, some off =>
      blkAt cells L o (addDirs fr la lb) &&
        labelGapB cells L (retL fr.fn n) (o + (sizesAt cells L o (addDirs fr la lb).length).sum) &&
        blkAt cells (retL fr.fn n) 0 [stDir off] &&
        bodyIn cells fr (retL fr.fn n) (n + 1) (sizesAt cells (retL fr.fn n) 0 1).sum is ws
    | _, _, _ => false
  | _, _, _, _, _ => false

/-- **A lowered body's blocks** with their byte offsets after the body's
label: `bodyIn`'s blocks, in order, each at the sizes the listing gives it,
the current label `L` `e` bytes after the body's label. The return's block
is the load, the teardown and `ret`, across the return site's label (zero
bytes). -/
def bodyBlks (cells : List (Directive × Nat)) (fr : Scc.Emit.X64.Frame) :
    String → Nat → Nat → Nat → List Scc.IR.Inst → List Scc.IR.Operand → List (Nat × List (Directive × Nat))
  | L, n, e, o, [], [w] =>
    match getOp fr .rax w with
    | .ok lw => [(e + o, (tearDirs lw).zip (sizesAt cells L o (tearDirs lw).length) ++
        [i64 .ret].zip (sizesAt cells (retL fr.fn n) 0 1))]
    | .error _ => []
  | L, n, e, o, .addChk d a b :: is, ws =>
    match getOp fr .rax a, getOp fr .rcx b, rsOf fr d with
    | .ok la, .ok lb, some off =>
      (e + o, (addDirs fr la lb).zip (sizesAt cells L o (addDirs fr la lb).length)) ::
        (e + o + (sizesAt cells L o (addDirs fr la lb).length).sum,
          [stDir off].zip (sizesAt cells (retL fr.fn n) 0 1)) ::
        bodyBlks cells fr (retL fr.fn n) (n + 1) (e + o + (sizesAt cells L o (addDirs fr la lb).length).sum)
          (sizesAt cells (retL fr.fn n) 0 1).sum is ws
    | _, _, _ => []
  | _, _, _, _, _, _ => []

/-- **A block of a lowered body** at `pc`: one of `bodyBlks`' blocks, at
its byte offset after the body's label `l`, its fresh labels numbered from
`n`. -/
def InBody (lab : String → Int64) (cells : List (Directive × Nat)) (fr : Scc.Emit.X64.Frame) (l : String)
    (n : Nat) (is : List Scc.IR.Inst) (ws : List Scc.IR.Operand) (pc : Int64) (blk : List (Directive × Nat)) :
    Prop :=
  ∃ j, pc = lab l + Int64.ofNat j ∧ (j, blk) ∈ bodyBlks cells fr l n 0 0 is ws

/-! ## The lowered code blocks of a program (A9) -/

/-- An `addChk` instruction (`lower0`'s only kind). -/
def isAddChk : Scc.IR.Inst → Bool
  | .addChk .. => true
  | _ => false

/-- **The frame `f` is emitted with** in `ir` (`emitItemsMaps`, `emitFunc`):
`frameOf` at the program's argument areas, recording safepoints when the
program has growth. -/
def frOf (ir : Scc.IR.Program) (f : Scc.IR.Func) : Scc.Emit.X64.Frame :=
  { frameOf (Scc.IR.StackMap.argAreas ir argRegs.length) f with maps := ir.growth.isSome }

/-- **`proInC` at the sizes the listing gives** the five cells after the
stack check's label (`leaq`, the limit's load, `cmpq`, `jb`, `subq`). -/
def proInS (cells : List (Directive × Nat)) (fr : Scc.Emit.X64.Frame) (fn entry : String) : Bool :=
  match sizesAt cells (labelOf fr.fn "chk") 0 5 with
  | [zl, zf, z1, z2, zs] => proInC cells fr fn entry zl zf z1 z2 zs
  | _ => false

/-- **`proInS` gives `proInC`** at some sizes. -/
theorem proInC_of_proInS {cells : List (Directive × Nat)} {fr : Scc.Emit.X64.Frame} {fn entry : String}
    (h : proInS cells fr fn entry = true) : ∃ zl zf z1 z2 zs, proInC cells fr fn entry zl zf z1 z2 zs = true := by
  unfold proInS at h
  split at h
  · exact ⟨_, _, _, _, _, h⟩
  · exact absurd h Bool.false_ne_true

/-- **Every function of `fs` has its first local label number** in
`starts`: `m` (per-function numbering, `m = 0` from the checkers). -/
theorem mem_starts_self {ir : Scc.IR.Program} {f : Scc.IR.Func} :
    ∀ {fs : List Scc.IR.Func} {m : Nat}, f ∈ fs → (f, m) ∈ Scc.Cert.Code1X64.starts ir m fs
  | g :: fs, m, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_starts_self h)

/-- **`starts` numbers every function `m`.** -/
theorem eq_of_mem_starts {ir : Scc.IR.Program} {f : Scc.IR.Func} {n : Nat} :
    ∀ {fs : List Scc.IR.Func} {m : Nat}, (f, n) ∈ Scc.Cert.Code1X64.starts ir m fs → n = m
  | g :: fs, m, h => by
    rcases List.mem_cons.mp h with h | h
    · exact (Prod.mk.inj h).2
    · exact eq_of_mem_starts h

/-- **The placement of every `func0`-shaped function of `ir` in `cells`**
(the lowering's `Accepted0` code blocks: no parameters, the stack check,
one block `entry` ending in a return), each's frame `frOf` recomputed from
`ir` as `emitFunc` builds it: its prologue (`proInS`, from its name to its
entry label `labelOf f.name "entry"`), its body (`bodyIn` after the
entry label, its fresh labels numbered from the function's first local
label number, `Code1X64.starts`) and, with at least one instruction, its
local overflow block (`ovfBlk` at `ovfL`). Only the shape `lower0`'s output
has for a one-word result is checked (every instruction an `addChk`, one
returned operand); other functions (the runtime's, multi-block ones, those
returning no word or several, code blocks outside `Accepted0`) are not
checked here. -/
def fnCodeOk (cells : List (Directive × Nat)) (ir : Scc.IR.Program) : Bool :=
  (Scc.Cert.Code1X64.starts ir 0 ir.funcs).all fun (f, n) =>
    match f.params, f.checkStack, f.blocks with
    | [], true, [⟨"entry", is, .ret [w]⟩] =>
      if is.all isAddChk then
        proInS cells (frOf ir f) f.name (labelOf f.name "entry") &&
          bodyIn cells (frOf ir f) (labelOf f.name "entry") n 0 is [w] &&
          (is.isEmpty || blockAtB cells (ovfL (frOf ir f)) 0 ovfBlk)
      else true
    | _, _, _ => true

/-- **`fnCodeOk` at a lowered code block**: `func0 name r` a function of
`ir` with first local label number `n`, its instructions `addChk`s and its
result one operand, has its prologue (at some cell sizes) and body in
`cells`, at its frame recomputed from `ir`, and with an instruction its
local overflow block (`ovfBlk`). -/
theorem fnCodeOk_func0 {cells : List (Directive × Nat)} {ir : Scc.IR.Program} (h : fnCodeOk cells ir = true)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} {n : Nat}
    (hf : (Scc.Lower.Inv.func0 name r, n) ∈ Scc.Cert.Code1X64.starts ir 0 ir.funcs)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w]) :
    (∃ zl zf z1 z2 zs, proInC cells (frOf ir (Scc.Lower.Inv.func0 name r)) name (labelOf name "entry")
        zl zf z1 z2 zs = true) ∧
      bodyIn cells (frOf ir (Scc.Lower.Inv.func0 name r)) (labelOf name "entry") n 0 r.insts r.ret = true ∧
      (r.insts ≠ [] → blockAtB cells (ovfL (frOf ir (Scc.Lower.Inv.func0 name r))) 0 ovfBlk = true) := by
  have hall : r.insts.all isAddChk = true := by
    rw [List.all_eq_true]; intro i hi; obtain ⟨d, a, b, rfl⟩ := hI i hi; rfl
  have := List.all_eq_true.mp h _ hf
  obtain ⟨insts, ret, next, marked, here⟩ := r
  simp only at hw hall
  subst hw
  simp only [Scc.Lower.Inv.func0, hall, ite_true, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff] at this
  exact ⟨proInC_of_proInS this.1.1, this.1.2, fun hne => this.2.resolve_left hne⟩

/-- **`fnCodeOk` at a lowered code block, at the listing's sizes**: the
prologue at the sizes of the five cells after the check's label
(`proInS`). -/
theorem fnCodeOk_func0_proInS {cells : List (Directive × Nat)} {ir : Scc.IR.Program} (h : fnCodeOk cells ir = true)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} {n : Nat}
    (hf : (Scc.Lower.Inv.func0 name r, n) ∈ Scc.Cert.Code1X64.starts ir 0 ir.funcs)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w]) :
    proInS cells (frOf ir (Scc.Lower.Inv.func0 name r)) name (labelOf name "entry") = true := by
  have hall : r.insts.all isAddChk = true := by
    rw [List.all_eq_true]; intro i hi; obtain ⟨d, a, b, rfl⟩ := hI i hi; rfl
  have := List.all_eq_true.mp h _ hf
  obtain ⟨insts, ret, next, marked, here⟩ := r
  simp only at hw hall
  subst hw
  simp only [Scc.Lower.Inv.func0, hall, ite_true, Bool.and_eq_true] at this
  exact this.1.1

end Spike.Lib.LowerX64
