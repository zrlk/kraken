import Scc.Emit.A64Func
import Scc.Emit.GranuleCore

/-!
# Granules on AArch64 (untrusted)

The AArch64 instance of the granule pass (`Scc.Emit.Granule`): every
instruction is 4 bytes and no branch is relaxed (`b` reaches ±128 MiB), so
the layout is the item count; filler `.zero k` and the word
`.quad scc_gc_desc - .` are raw lines (`k` is a multiple of 4: every address
is); no instruction is inserted (a block is never entered by fall-through).

* **Insertion points** (`pointsA64`): `_start`, every function symbol and
  IR block label (`FnCtx.blockLabel`), and the grow trampoline with
  `IR.Program.growth`. The local labels (stack check, abort and halt stubs,
  child entries) are not points.
* **Classification**: `bl`/`blr` are calls; `b` to a label and `ret` end the
  flow (a halt is `l: b l`), the loader's no-fall-through cases; everything
  else, `br` included, falls through.
* Raw lines in the text are sized by `dirSize` strict: the alignment lines
  (`.p2align 2` before a function, `.p2align 4` at the start) must pad
  nothing, as the loader drops them; a data line other than the pass's own is
  an error.
* **The tail**: the text section aligned to a granule
  (`.section .text.scc_galign,"ax",%progbits`, `.p2align 16`, `.text`)
  after the last word, as on x64 (`%progbits`: `@` starts a comment in
  AArch64 assembly). Without it lld places `.text` 16-aligned only. The
  loader's `textSection` leaves the text at the `.section` line and drops
  the section lines, so the tail adds nothing to the loaded program
  (`GranuleA64Test`).

Linked check (scratch driver over `emitItems`, `scc_gc_desc` stubbed in
`.rodata`, `A64_CC` without pins, `Spike/Tools/granule_check.py --asm`):
`hello1.w`, `.text` at `0x220000`, one granule, exit 0; the `big.w` of
`Spike/Tools/gen_big.py`, `.text` at `0x220000`, 196608 bytes (3 granules,
boundaries inside `wc_line3` and `wc_mb`), exit 87 as `big.code`; checks
(a) (b) (c) pass on both. Without the tail `.text` was at `0x210410` /
`0x210500` and (a) failed.
-/

namespace Scc.Emit.Granule
open Scc.Emit.A64

/-- Does a raw line end the text (as `Scc.Cert.MapsA64`)? -/
def endsTextA64 (s : String) : Bool :=
  s == ".data" || s == ".bss" || s.startsWith ".section"

/-- The flow of an AArch64 instruction. Only `b` to a label and `ret` end the
flow: exactly the instructions the loader's block check
(`Rt.A64.fallsThrough`, via `classify`) treats as not falling through
(proved in `Spike.Lib.GranuleAgreeA64`). Everything else, `br` included,
counts as falling through, which only keeps more blocks together. -/
def insA64 : Directive → Option Ins
  | .instr ⟨.W64, .B (.label _)⟩ => some .term
  | .instr ⟨.W64, .RET _⟩ => some .term
  | .instr ⟨.W64, .BL _⟩ | .instr ⟨.W64, .BLR _⟩ => some .call
  | .instr _ => some .other
  | _ => none

/-- The size of an AArch64 item at `a`. -/
def sizeAtA64 (a : Nat) (it : Item) (_ : Bool) : Except String Nat :=
  match it with
  | .d (.instr _) => .ok 4
  | .d (.label _) => .ok 0
  | .d (.byteArray _) => .error "granule (arm): byte array in the text"
  | .d (.zeros _) => .error "granule (arm): zero cell in the text"
  | .raw s => dirSize true a s
  | .comment _ => .ok 0

/-- The tail: the text section aligned to a granule. -/
def tailA64 : List Item :=
  [.raw ".section .text.scc_galign,\"ax\",%progbits", .raw ".p2align 16", .raw ".text"]

/-- **The AArch64 ISA** of the granule pass. -/
def isaA64 : Isa Item where
  label? | .d (.label l) => some l | _ => none
  mkLabel l := .d (.label l)
  ins? | .d d => insA64 d | _ => none
  target? _ := none
  sizeAt := sizeAtA64
  shortLen := 0
  shortOk _ := true
  jmp := A64.jmp
  jmpMax := 4
  jmpPlan _ := (4, 0)
  zero k := .raw (zeroLine k)
  word := .raw wordLine
  ends | .raw s => endsTextA64 s | _ => false
  resumes | .raw s => s == ".text" | _ => false
  tail := tailA64

/-- **The insertion points** of a program's AArch64 text. -/
def pointsA64 (p : IR.Program) : List String :=
  "_start" :: p.funcs.zipIdx.flatMap (fun (f, fi) =>
      let c := fnCtx p.abortFn p.growth [] fi f
      f.name :: f.blocks.filterMap fun b => (c.blockLabel b.label).toOption) ++
    (if p.growth.isSome then [IR.StackMap.morestackSym] else [])

/-- **The AArch64 granule pass** on a program's items. -/
def granuleA64 (p : IR.Program) (items : List Item) : Except String (List Item) :=
  granuleWith isaA64 granule (pointsA64 p) items

/-! ## Tests (small granules) -/

namespace TestA64

def N : Item := ins (.NOP : Operation .W64)
def nops (n : Nat) : List Item := List.replicate n N
def L (l : String) : Item := lbl l
def J (l : String) : Item := A64.jmp l
def C (l : String) : Item := A64.call l
def R : Item := A64.ret

/-- The lines of an item list. -/
def lines (xs : List Item) : List String := xs.map fun it => it.render.trimAsciiStart.toString

/-- Run the pass with granule size `gs` and points `ps`: the lines and the
label offsets of the result. -/
def run (gs : Nat) (ps : List String) (xs : List Item) :
    Except String (List String × List (String × Nat)) := do
  let out ← granuleWith isaA64 gs ps xs
  let zs ← layout isaA64 out
  pure (lines out, labelOffs isaA64 0 (textPart isaA64 out) zs)

def ok? {α : Type} (r : Except String α) : Option α := r.toOption

-- One granule: the word at its end, then the tail.
#guard ok? (run 64 ["a"] ([.raw ".text", L "a"] ++ nops 3 ++ [R, .raw ".data"])) ==
  some ([".text", "a:", "nop", "nop", "nop", "ret", ".zero 40", ".Lgw0:", ".quad scc_gc_desc - .",
    ".section .text.scc_galign,\"ax\",%progbits", ".p2align 16", ".text", ".data"],
    [("a", 0), (".Lgw0", 56)])

-- A label after an instruction that falls through is not an insertion point:
-- its block grows past it (here too large for a granule: an error, no `b` is
-- inserted).
#guard (ok? (run 64 ["a", "b"] ([L "a"] ++ nops 10 ++ [L "b"] ++ nops 8 ++ [R]))).isNone

-- After a `ret` the block moves with nothing inserted.
#guard (ok? (run 64 ["a", "b"] ([L "a"] ++ nops 10 ++ [R, L "b"] ++ nops 8 ++ [R]))).any
  fun (ls, _) => (ls.drop 12).take 4 == [".zero 12", ".Lgw0:", ".quad scc_gc_desc - .", "b:"]

-- A label right after a call is not an insertion point.
#guard (ok? (run 64 ["a", "b", "c"] ([L "a"] ++ nops 5 ++ [C "c", L "b"] ++ nops 8 ++ [R, L "c", R]))).isNone
#guard (ok? (run 64 ["a", "b", "c"] ([L "a"] ++ nops 5 ++ [J "c", L "b"] ++ nops 8 ++ [R, L "c", R]))).any
  fun (_, offs) => lookup offs "b" == some 64 && lookup offs "c" == some 100

-- A `br` does not end the flow for the pass (the loader's block check treats
-- it as falling through): a label after it is not an insertion point.
#guard (ok? (run 64 ["a", "b"] ([L "a"] ++ nops 10 ++ [tailReg .X16, L "b"] ++ nops 8 ++ [R]))).isNone
#guard (ok? (run 64 ["a", "b"] ([L "a"] ++ nops 4 ++ [tailReg .X16, L "b"] ++ nops 3 ++ [R]))).map (·.2) ==
  some [("a", 0), ("b", 20), (".Lgw0", 56)]

-- An alignment line that pads, a byte array or a data line in the text is an error.
#guard (ok? (run 64 ["a"] [L "a", N, .raw ".p2align 3", R])).isNone
#guard (ok? (run 64 ["a"] [L "a", N, .raw ".p2align 2", R])).isSome
#guard (ok? (run 64 ["a"] [L "a", .raw ".byte 1", R])).isNone

-- The text's end label (`scc_text_end`) goes after the last word, before the
-- tail: it marks the end of the padded text; the order of scc's items is kept.
#guard ok? (run 64 ["a"] ([.raw ".text", L "a"] ++ nops 3 ++ [R, L "scc_text_end", .raw ".data"])) ==
  some ([".text", "a:", "nop", "nop", "nop", "ret", ".zero 40", ".Lgw0:", ".quad scc_gc_desc - .", "scc_text_end:",
    ".section .text.scc_galign,\"ax\",%progbits", ".p2align 16", ".text", ".data"],
    [("a", 0), (".Lgw0", 56), ("scc_text_end", 64)])
-- Not the last label of the text: not moved.
#guard (ok? (run 64 ["a"] ([.raw ".text", L "scc_text_end", L "a"] ++ nops 3 ++ [R]))).map (·.2) ==
  some [("scc_text_end", 0), ("a", 0), (".Lgw0", 56)]

end TestA64

end Scc.Emit.Granule
