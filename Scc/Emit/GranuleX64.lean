import Scc.Emit.X64Func
import Scc.Emit.X64Size
import Scc.Emit.GranuleCore

/-!
# Granules on x64 (untrusted)

The x64 instance of the granule pass (`Scc.Emit.Granule`): the emitter's
items (`Scc.Emit.X64.Item`) sized by `Scc.Emit.X64.Size` (a `jcc`/`jmp` to a
label is relaxable, 2 or 6/5 bytes), filler `.zero k` and the word
`.quad scc_gc_desc - .` as directive lines; no instruction is inserted (a
block is never entered by fall-through).

* **Insertion points** (`pointsX64`): `_start`, every function symbol and
  IR block label (`labelOf`), and the grow trampoline with
  `IR.Program.growth`. The stub labels (`ovf`, `stk`, `chk`, child entries)
  are not points: a stub stays with the block before it.
* **The jump into the next granule** (`jmpPlanX64`, unused by the pass:
  the documented fallback of entering a moved block by a jump): from `a`, with room
  `d` to the word, its target is `d + 8` bytes past the jump's start (no
  filler after the word): gas picks the 2-byte form when
  `d + 6 ≤ 127`, the 5-byte one otherwise (its rel32 form is never relaxed:
  the short displacement `d + 6` is then out of range).
* **The tail**: the text section aligned to a granule
  (`.section .text.scc_galign,"ax",@progbits`, `.p2align 16`, `.text`)
  after the last word, which the loader skips; only data sections follow.
* **Classification**: `call` (any target) is a call; a 64-bit `jmp` to a
  label and a 64-bit `ret` end the flow (the loader's no-fall-through cases
  other than `call`); everything else (`jcc`, `syscall`, `ud2`, an indirect
  `jmp`) falls through. Alignment lines in the text must pad nothing
  (`dirSize` strict).

  `ud2` no longer ends the flow for the pass (it did before the cut set was
  narrowed to the loader's): at small test granules the runtime's abort
  tail (its stubs end in `ud2`) then glues to the first user function and is
  refused (on `hello1` at granule sizes ≤ 512 B); at the real 64 KiB granule
  nothing changes.
-/

namespace Scc.Emit.Granule
open Scc.Emit.X64

/-- Does an assembler directive line end the text (as `Scc.Cert.MapsX64`)? -/
def endsTextX64 (s : String) : Bool :=
  s == ".data" || s == ".bss" || s.startsWith ".section"

/-- The flow of an x64 instruction. Only a 64-bit `jmp` to a label and a
64-bit `ret` end the flow: exactly the instructions the loader's block check
(`Rt.X64.fallsThrough`, via `classify`) treats as not falling through, other
than `call` (proved in `Spike.Lib.GranuleAgreeX64`). Everything else,
`ud2` and indirect jumps included, counts as falling through, which only
keeps more blocks together. -/
def insX64 : Directive → Option Ins
  | .instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label _) .after_current_instruction)))) => some .term
  | .instr (.regular .W64 .W64 .ret) => some .term
  | .instr (.regular _ _ (.call _)) => some .call
  | .instr _ => some .other
  | _ => none

/-- The size of an x64 item at `a`, a relaxable branch wide when `w`. -/
def sizeAtX64 (a : Nat) (it : Item) (w : Bool) : Except String Nat :=
  match it with
  | .d d => match Size.sizeAt a d w with
    | some z => .ok z
    | none => .error s!"granule (x64): no size for {repr d}"
  | .dir s => dirSize true a s
  | .raw s => .error s!"granule (x64): raw line in the text: {s}"
  | .comment _ | .blank => .ok 0

/-- The jump into the next granule with room `d` (module docstring). -/
def jmpPlanX64 (d : Nat) : Nat × Nat := if d + 6 ≤ 127 then (2, 0) else (5, 0)

/-- The tail: the text section aligned to a granule. -/
def tailX64 : List Item :=
  [.dir ".section .text.scc_galign,\"ax\",@progbits", .dir ".p2align 16", .dir ".text"]

/-- **The x64 ISA** of the granule pass. -/
def isaX64 : Isa Item where
  label? | .d (.label l) => some l | _ => none
  mkLabel l := .d (.label l)
  ins? | .d d => insX64 d | _ => none
  target? | .d d => Size.branchTarget d | _ => none
  sizeAt := sizeAtX64
  shortLen := 2
  shortOk := Size.branchShort
  jmp l := .d (i64 (.jmp (rel l)))
  jmpMax := 5
  jmpPlan := jmpPlanX64
  zero k := .dir (zeroLine k)
  word := .dir wordLine
  ends | .dir s => endsTextX64 s | _ => false
  resumes | .dir s => s == ".text" | _ => false
  tail := tailX64

/-- **The insertion points** of a program's x64 text. -/
def pointsX64 (p : IR.Program) : List String :=
  "_start" :: p.funcs.flatMap (fun f => f.name :: f.blocks.map (labelOf f.name ·.label)) ++
    (if p.growth.isSome then [IR.StackMap.morestackSym] else [])

/-- **The x64 granule pass** on a program's items. -/
def granuleX64 (p : IR.Program) (items : List Item) : Except String (List Item) :=
  granuleWith isaX64 granule (pointsX64 p) items

/-! ## Tests (small granules) -/

namespace TestX64

/-- `n` one-byte instructions (`ret` is 1 byte; the flow does not matter for
sizes, so `nop 1` is used). -/
def nops (n : Nat) : List Item := (List.replicate n (.d (i64 (.nop 1))))

def L (l : String) : Item := .d (.label l)
def J (l : String) : Item := .d (i64 (.jmp (rel l)))
def C (l : String) : Item := .d (i64 (.call (rel l)))
def U : Item := .d (i64 .ud2)
def R : Item := .d (i64 .ret)
/-- A one-byte `nop`: `N, R` is as long as a `ud2`. -/
def N : Item := .d (i64 (.nop 1))

/-- The lines of an item list (labels with `:`). -/
def lines (xs : List Item) : List String :=
  xs.map fun | .d (.label l) => l ++ ":" | it => (it.line?.getD "?").trimAsciiStart.toString

/-- Run the pass with granule size `gs` and points `ps`, and the layout of the
result: the lines, the label offsets. -/
def run (gs : Nat) (ps : List String) (xs : List Item) : Except String (List String × List (String × Nat)) := do
  let out ← granuleWith isaX64 gs ps xs
  let zs ← layout isaX64 out
  pure (lines out, labelOffs isaX64 0 (textPart isaX64 out) zs)

def ok? {α : Type} (r : Except String α) : Option α := r.toOption

-- One granule: the word at its end, then the tail.
#guard ok? (run 64 ["a"] ([.dir ".text", L "a"] ++ nops 10 ++ [N, R, .dir ".data"])) ==
  some ([".text", "a:", "nop", "nop", "nop", "nop", "nop", "nop", "nop", "nop", "nop", "nop", "nop",
    "ret", ".zero 44", ".Lgw0:", ".quad scc_gc_desc - .", ".section .text.scc_galign,\"ax\",@progbits",
    ".p2align 16", ".text", ".data"], [("a", 0), (".Lgw0", 56)])

-- A label after an instruction that falls through is not an insertion point:
-- the block grows past it (here too large for a granule: an error, no jump is
-- inserted), or stays whole in its granule.
#guard (ok? (run 64 ["a", "b"] ([L "a"] ++ nops 40 ++ [L "b"] ++ nops 30 ++ [N, R]))).isNone
#guard (ok? (run 64 ["a", "b"] ([L "a"] ++ nops 40 ++ [L "b"] ++ nops 10 ++ [N, R]))).map (·.2) ==
  some [("a", 0), ("b", 40), (".Lgw0", 56)]

-- `place` fails closed: a block entered by fall-through that would move is an
-- error (unreachable through `segment`).
#guard (place isaX64 64 [⟨some "a", (nops 40).map (·, false)⟩, ⟨some "b", (nops 30).map (·, false)⟩]
  0 0 false).toOption.isNone

-- After a `ret` (no fall-through) the block moves with nothing inserted.
#guard (ok? (run 64 ["a", "b"] ([L "a"] ++ nops 40 ++ [N, R, L "b"] ++ nops 30 ++ [N, R]))).any
  fun (ls, _) => (ls.drop 43).take 3 == [".zero 14", ".Lgw0:", ".quad scc_gc_desc - ."]

-- A label right after a call is never an insertion point: the block grows
-- past it (here too large for a granule), so the call's return address stays
-- next to it; after a jump instead, the label is a point and its block moves.
#guard (ok? (run 64 ["a", "b", "c"] ([L "a"] ++ nops 20 ++ [C "c", L "b"] ++ nops 30 ++ [N, R, L "c", N, R]))).isNone
#guard (ok? (run 64 ["a", "b", "c"] ([L "a"] ++ nops 20 ++ [J "c", L "b"] ++ nops 40 ++ [N, R, L "c", N, R]))).any
  fun (ls, offs) => (ls.drop 21).take 5 == ["jmp c", ".zero 34", ".Lgw0:", ".quad scc_gc_desc - .", "b:"] &&
    lookup offs "b" == some 64 && lookup offs "c" == some 106

-- A block larger than a granule's code area is an error.
#guard (ok? (run 64 ["a", "b"] ([L "a", N, R, L "b"] ++ nops 60 ++ [N, R]))).isNone

-- The text resuming after data is an error.
#guard (ok? (run 64 ["a"] [L "a", N, R, .dir ".data", .dir ".text", N, R])).isNone

-- A raw line in the text is an error.
#guard (ok? (run 64 ["a"] [L "a", .raw "foo", U])).isNone

-- A jump out of short range is wide (5 bytes).
#guard (ok? (run 256 ["a", "b", "c"]
    ([L "a", J "c"] ++ nops 100 ++ [L "b"] ++ nops 100 ++ [N, R, L "c", N, R]))).any
  fun (ls, offs) => ls.take 2 == ["a:", "jmp c"] && lookup offs "b" == some 105 && lookup offs "c" == some 207

-- A block after a `ret` moves with nothing inserted before the filler.
#guard (ok? (run 256 ["a", "b"] ([L "a"] ++ nops 20 ++ [N, R, L "b"] ++ nops 240 ++ [N, R]))).any
  fun (ls, offs) => (ls.drop 23).take 4 == [".zero 226", ".Lgw0:", ".quad scc_gc_desc - .", "b:"] &&
    lookup offs "b" == some 256
-- The same text without the `ret`: one block, too large for a granule.
#guard (ok? (run 256 ["a", "b"] ([L "a"] ++ nops 20 ++ [L "b"] ++ nops 240 ++ [N, R]))).isNone

-- A `ud2` does not end the flow for the pass (the loader's block check treats
-- it as falling through): a label after it is not an insertion point, so the
-- block grows past it (here too large for a granule: an error), or stays
-- whole in its granule.
#guard (ok? (run 64 ["a", "b"] ([L "a"] ++ nops 40 ++ [U, L "b"] ++ nops 30 ++ [R]))).isNone
#guard (ok? (run 64 ["a", "b"] ([L "a"] ++ nops 40 ++ [U, L "b"] ++ nops 10 ++ [R]))).map (·.2) ==
  some [("a", 0), ("b", 42), (".Lgw0", 56)]
-- Nor does an indirect `jmp`, nor a 32-bit `ret`.
#guard (ok? (run 64 ["a", "b"] ([L "a"] ++ nops 40 ++ [.d (i64 (.jmp (.reg (.low .rax .W64)))), L "b"] ++
  nops 30 ++ [R]))).isNone
#guard (ok? (run 64 ["a", "b"] ([L "a"] ++ nops 40 ++ [.d (i32 .ret), L "b"] ++ nops 30 ++ [R]))).isNone

end TestX64

end Scc.Emit.Granule
