import Scc.IR.StackMap

/-!
# Granules: where the collector's descriptor words go (untrusted)

The text is cut into **granules** of `granule` = 64 KiB from its start (which
the link places on a granule boundary). The last 8 bytes of every granule the
code touches hold a **descriptor word**: a label `.Lgw<n>` and the line
`.quad scc_gc_desc - .`. The bytes from the end of the code in a granule to its
word are zero filler (`.zero k`). So a word sits at an offset `≡ granule − 8`
(mod `granule`) from the start of the text, and a code address `a` finds
the word of its granule at `a − a % granule + granule − 8`.

**Blocks.** The pass never splits a *block*: the items between two
insertion points. An insertion point is a label the ISA's caller names
(`points`: the start of an IR block, a function symbol, `_start`, the grow
trampoline) that no instruction falls into: its previous instruction ends
the flow (a jump, return or trap: `Ins.term`), or no instruction precedes it
in the text. A label after a call (a return address must stay right after
its call), after any other instruction that falls through (the entry block
after its function's prologue), and every local label (`.Lsp`, fresh labels,
stub labels, which the caller does not name) is inside a block. So the code
before a block never falls into it, and a block that does not fit the rest
of its granule moves to the next one behind the filler and the word with
nothing inserted: the pass adds no instruction, and the filler and the word
are never executed. The pass **fails closed**: a block that does not fit a
whole granule's code area (`granule − 8` bytes from the granule's start) is
an error, never split or entered by an inserted jump; so is a block entered
by fall-through that would have to move (unreachable by the cut rule, but
checked: the pass has no jump to insert).

The bound this needs: every block fits `granule − 8` bytes. Every IR block
ends in a jump, return or trap on both ISAs (a `br` ends in its `jmp` to the
false target), so each IR block label but a function's entry one is a cut
and a block is one IR block, except a function's first block (the symbol,
its prologue and its entry IR block, which the prologue falls into) and its
last (its last IR block and the stubs after it, whose labels are local).
What bounds them:

* **User functions and thread trampolines**: the lowering splits every IR
  block to at most `IR.maxBlockLen` weight units, the entry block with its
  parameter moves (`Scc.Lower.Split`, `IR.blocksOk`), and an emitter writes
  at most `IR.bytesPerWeight` bytes per unit, so a first block with its
  prologue is at most `bytesPerWeight · (maxBlockLen + prologueWeight)` =
  37008 bytes (`Scc.IR.BlockLen`), under the 65528 of a granule's code area.
* **The stubs after the last IR block**: the stack-limit abort or grow stub
  and the overflow abort are fixed sequences (tens of bytes); the child
  stubs are one per `clone` site of the function, each a few instructions,
  and nothing bounds how many there are.
* **The runtime routines**: not split (the lowering never applies the
  split to them) and bounded by nothing in the lowering; they are checked
  per program on the emitted bytes (the granule checker), and here.
* **The emitter's own code**: `_start` and the grow trampoline are fixed
  sequences.

So the pass stays the check: a block over the bound is an error with its
label and size, never split or entered by an inserted jump. There is no
fallback: no option or path of the pass inserts a jump (the `Isa.jmp`
fields are unused), so scc refuses such a program rather than emit
different code.

**Worst-case filler.** Each granule gets at most one filler run: the one
in front of its word, after the last block placed in it, which ends the
flow (no instruction falls into a block). The run is shorter than the next
block (else that block would have been placed in front of it), so the
bytes a granule loses are less than the largest block, at most the bound
above; with the blocks of `IR.maxBlockLen` under 37008 bytes.

**Layout.** Instruction sizes come from the ISA (`Isa.sizeAt`): the length of
an instruction at an address, a relaxable branch short or wide as its flag
says. A layout (`layout`) is the least fixpoint of the assembler's branch
relaxation, computed as GNU `as` does: every branch starts short and is
widened, never shortened, while its target is out of the short range. The
pass places the blocks with given branch widths, lays out the result, and
repeats with the widths of that layout until they agree (`rounds`): then the
text it returns assembles exactly as it was planned. The result is checked
once more (`wordsOk`): every word label at `≡ granule − 8`, the text ending
on a granule boundary.

**The text** is the items up to the first item that ends it (`Isa.ends`: a
`.data`, `.bss` or `.section` line); the pass rejects a `.text` line after
that point. The ISA's `tail` items go at the end of the text, after its last
word (the x64 alignment of the text section to a granule).

Kernel cost: no certificate evaluates the pass; the kernel only checks that
the pass's output, with its own words and filler erased, is the input (a
comparison of item lists). The pass uses lists and structural recursion only
(no hash maps, no arrays) and classifies items by constructor; it reads a
directive line's text only to size it (`dirSize`).

Known limit: label lookups are linear in the number of labels (`lookup`
over an association list), so a layout is quadratic in the text's size; a
round on the 200 KiB `big.w` takes some seconds. Fine for the programs scc
certifies; a large input would want a sorted or tree map outside the kernel's
path.

Untrusted: the loader of the statement checks the granule placement of the
text it is given; this pass only has to produce one it accepts.
-/

namespace Scc.Emit.Granule

/-- **The granule size** in bytes. -/
def granule : Nat := 65536

/-- The control flow of an instruction, as the pass needs it. -/
inductive Ins where
  /-- A call: the next instruction is its return address. -/
  | call
  /-- No fall-through: an unconditional jump, a return, a trap. -/
  | term
  /-- Everything else (falls through). -/
  | other
  deriving BEq, Repr, Inhabited

/-- What the pass needs to know of an ISA's items `α`. -/
structure Isa (α : Type) where
  /-- The label an item defines. -/
  label? : α → Option String
  /-- A label item. -/
  mkLabel : String → α
  /-- The flow of an instruction item; `none` for every other item. -/
  ins? : α → Option Ins
  /-- The target of a relaxable branch (short or wide form). -/
  target? : α → Option String
  /-- The size of an item at an address (a relaxable branch wide when the
  flag is set); an error for an item the text cannot hold. -/
  sizeAt : Nat → α → Bool → Except String Nat
  /-- The size of a relaxable branch's short form. -/
  shortLen : Nat
  /-- Is a displacement (from the end of the short form) in short range? -/
  shortOk : Int → Bool
  /-- An unconditional jump to a label. Not used by the pass, which inserts no
  instruction (a block is never entered by fall-through); kept, with `jmpMax`
  and `jmpPlan`, for the documented fallback of entering a moved block by a
  jump. -/
  jmp : String → α
  /-- The largest size of `jmp`. -/
  jmpMax : Nat
  /-- The jump into the next granule given the room `d` from it to the word:
  its size, and the filler `x` to put after the word, before the target, so
  that the assembler picks that size (`x` is 0 except where a short jump would
  not reach and a wide one would be relaxed to short). -/
  jmpPlan : Nat → Nat × Nat
  /-- The filler line of `k` zero bytes. -/
  zero : Nat → α
  /-- The descriptor word line (8 bytes). -/
  word : α
  /-- Does the item end the text? -/
  ends : α → Bool
  /-- Does the item switch back to the text? -/
  resumes : α → Bool
  /-- The items after the text's last word. -/
  tail : List α

/-- The label prefix of the descriptor words. -/
def wordPrefix : String := ".Lgw"

/-- The label of the `n`th descriptor word. -/
def wordLabel (n : Nat) : String := wordPrefix ++ toString n

/-- The descriptor word line: the offset of `scc_gc_desc` from the word itself
(self-relative, format version 2: a reader at the word's address `w` finds the
descriptor at `w + *w`; no relocation at any load address). -/
def wordLine : String := ".quad scc_gc_desc - ."

/-- The filler line of `k` zero bytes. -/
def zeroLine (k : Nat) : String := ".zero " ++ toString k

/-- The padding of an alignment to `k` bytes at `a`. -/
def alignPad (a k : Nat) : Nat := if k = 0 then 0 else (k - a % k) % k

/-- Assembler directives that put data in the section; the text holds none of
them but the pass's own filler and words. -/
def dataDirs : List String :=
  [".byte", ".skip", ".fill", ".space", ".quad", ".long", ".word", ".short", ".int", ".value",
   ".2byte", ".4byte", ".8byte", ".octa", ".ascii", ".asciz", ".string", ".incbin", ".org", ".align"]

/-- **The size of a directive line** at `a`: `.zero k` is `k`, the word line 8,
`.p2align n` and `.balign k` their padding (which must be 0 when `strict`:
the loader drops alignment lines), any other data directive an error, every
other line (`.text`, `.globl`, `.type`, `.size`, ...) 0. -/
def dirSize (strict : Bool) (a : Nat) (s : String) : Except String Nat :=
  let alignTo (k : Nat) : Except String Nat :=
    let z := alignPad a k
    if strict && z != 0 then .error s!"granule: alignment line pads {z} bytes at {a}: {s}" else .ok z
  if s.startsWith ".zero " then
    match (s.drop 6).toNat? with
    | some k => .ok k
    | none => .error s!"granule: unreadable filler line: {s}"
  else if s == wordLine then .ok 8
  else if s.startsWith ".p2align " then
    match (s.drop 9).toNat? with
    | some n => alignTo (2 ^ n)
    | none => .error s!"granule: unreadable alignment line: {s}"
  else if s.startsWith ".balign " then
    match (s.drop 8).toNat? with
    | some k => alignTo k
    | none => .error s!"granule: unreadable alignment line: {s}"
  else if dataDirs.any (fun d => s == d || s.startsWith (d ++ " ")) then
    .error s!"granule: data directive in the text: {s}"
  else .ok 0

variable {α : Type}

/-! ## Layout -/

/-- The text: the items before the first one that ends it. -/
def textPart (isa : Isa α) (items : List α) : List α := items.takeWhile (!isa.ends ·)

/-- The sizes of `items` from address `a`, a relaxable branch wide where `ws`
says (missing flags are short). -/
def sizesWith (isa : Isa α) : Nat → List α → List Bool → Except String (List Nat)
  | _, [], _ => .ok []
  | a, x :: xs, ws => do
    let z ← isa.sizeAt a x (ws.headD false)
    let zs ← sizesWith isa (a + z) xs ws.tail
    pure (z :: zs)

/-- The labels of laid-out items with their offsets, in order. -/
def labelOffs (isa : Isa α) : Nat → List α → List Nat → List (String × Nat)
  | a, x :: xs, z :: zs =>
    let r := labelOffs isa (a + z) xs zs
    match isa.label? x with
    | some l => (l, a) :: r
    | none => r
  | _, _, _ => []

/-- The offset of the first definition of a label. -/
def lookup (offs : List (String × Nat)) (l : String) : Option Nat :=
  (offs.find? (·.1 == l)).map (·.2)

/-- One relaxation step: a branch becomes wide (and stays wide) when its
target is out of short range at the layout `zs`; a target outside the items
is out of range. -/
def widen (isa : Isa α) (offs : List (String × Nat)) : Nat → List α → List Nat → List Bool → List Bool
  | a, x :: xs, z :: zs, ws =>
    let w := ws.headD false || match isa.target? x with
      | some l => match lookup offs l with
        | some t => !isa.shortOk ((t : Int) - ((a + isa.shortLen : Nat) : Int))
        | none => true
      | none => false
    w :: widen isa offs (a + z) xs zs ws.tail
  | _, _, _, _ => []

/-- The least relaxation fixpoint from the widths `ws`, in at most `fuel`
steps. -/
def layoutFix (isa : Isa α) (items : List α) : Nat → List Bool → Except String (List Nat)
  | 0, _ => .error "granule: branch relaxation did not settle"
  | fuel + 1, ws => do
    let zs ← sizesWith isa 0 items ws
    let ws' := widen isa (labelOffs isa 0 items zs) 0 items zs ws
    if ws' == ws then pure zs else layoutFix isa items fuel ws'

/-- **The layout of a text**: the size of every item of the text part of
`items` (`textPart`; labels, comments and other lines 0), at the least
relaxation fixpoint. Each step widens a branch, so the text's length bounds
the steps. -/
def layout (isa : Isa α) (items : List α) : Except String (List Nat) :=
  let t := textPart isa items
  layoutFix isa t (t.length + 1) (t.map fun _ => false)

/-- Are the word labels of laid-out text items at `≡ gs − 8` (mod `gs`), and
does the text end on a granule boundary? -/
def wordsOk (isa : Isa α) (gs : Nat) : Nat → List α → List Nat → Bool
  | a, x :: xs, z :: zs =>
    (match isa.label? x with
     | some l => !(l.startsWith wordPrefix) || a % gs == gs - 8
     | none => true) && wordsOk isa gs (a + z) xs zs
  | a, _, _ => a % gs == 0

/-! ## Placement -/

/-- A block: the label that starts it (none for the items before the first
insertion point) and its items, each with its branch width. -/
structure Seg (α : Type) where
  label : Option String
  items : List (α × Bool)

/-- Cut the text into blocks at the insertion points: the labels in `points`
that no instruction falls into (`cut`: the previous instruction ends the flow,
or there is none yet). -/
def segment (isa : Isa α) (points : List String) :
    List (α × Bool) → Bool → Option String → List (α × Bool) → List (Seg α)
  | [], _, l, cur => [⟨l, cur.reverse⟩]
  | (x, w) :: rest, cut, l, cur =>
    match isa.label? x with
    | some m =>
      if cut && points.contains m then ⟨l, cur.reverse⟩ :: segment isa points rest cut (some m) [(x, w)]
      else segment isa points rest cut l ((x, w) :: cur)
    | none => match isa.ins? x with
      | some k => segment isa points rest (k == .term) l ((x, w) :: cur)
      | none => segment isa points rest cut l ((x, w) :: cur)

/-- The flow of the last instruction of `xs`, `acc` if it has none. -/
def lastFlow (isa : Isa α) : List (α × Bool) → Option Ins → Option Ins
  | [], acc => acc
  | (x, _) :: xs, acc => lastFlow isa xs (match isa.ins? x with | some k => some k | none => acc)

/-- Does the code end falling through after a block, given whether it did
before it (a block without instructions changes nothing)? -/
def fallsAfter (isa : Isa α) (ft : Bool) (s : Seg α) : Bool :=
  match lastFlow isa s.items none with
  | none => ft
  | some Ins.term => false
  | some _ => true

/-- The sizes of a block's items from `a`. -/
def segSizes (isa : Isa α) (a : Nat) (s : Seg α) : Except String (List Nat) :=
  sizesWith isa a (s.items.map (·.1)) (s.items.map (·.2))

/-- Laid-out items: an item, its planned size, and whether it is from the
input (not the pass's filler, word or tail). -/
abbrev Out (α : Type) := List (α × Nat × Bool)

/-- A block's items with their sizes. -/
def emitSeg (s : Seg α) (zs : List Nat) : Out α :=
  (s.items.zip zs).map fun ((x, _), z) => (x, z, true)

/-- Filler of `k` bytes (nothing for 0). -/
def filler (isa : Isa α) (k : Nat) : Out α := if k = 0 then [] else [(isa.zero k, k, false)]

/-- The `n`th word. -/
def wordItems (isa : Isa α) (n : Nat) : Out α :=
  [(isa.mkLabel (wordLabel n), 0, false), (isa.word, 8, false)]

/-- The end of the code area of the granule of `a`: where its word starts. -/
def limitOf (gs a : Nat) : Nat := (a / gs + 1) * gs - 8

/-- **Place the blocks** from address `a`, the `n`th word next, `ft` whether
the code before falls through: each block in the rest of the current granule
if it fits, otherwise after the filler and the word, at the start of the next
granule; after the last block, the filler and word of the last granule the
code touches, and the tail. A block that would move while the code before
falls into it is an error (fail closed: no jump is inserted; the cut rule of
`segment` makes this unreachable). -/
def place (isa : Isa α) (gs : Nat) : List (Seg α) → Nat → Nat → Bool → Except String (Out α)
  | [], a, n, _ =>
    let tl := isa.tail.map fun x => (x, 0, false)
    if a % gs == 0 then pure tl
    else pure (filler isa (limitOf gs a - a) ++ wordItems isa n ++ tl)
  | s :: ss, a, n, ft => do
    let lim := limitOf gs a
    let zs ← segSizes isa a s
    let ft' := fallsAfter isa ft s
    if a + zs.sum ≤ lim then
      pure (emitSeg s zs ++ (← place isa gs ss (a + zs.sum) n ft'))
    else match s.label with
      | none => throw "granule: the text before the first block does not fit a granule"
      | some l => do
        if ft then
          throw s!"granule: block {l} is entered by fall-through and does not fit the rest of its granule"
        let a1 := lim + 8
        let zs1 ← segSizes isa a1 s
        if a1 + zs1.sum > limitOf gs a1 then
          throw s!"granule: block {l} ({zs1.sum} bytes) does not fit a granule"
        let brk := filler isa (lim - a) ++ wordItems isa n
        pure (brk ++ emitSeg s zs1 ++ (← place isa gs ss (a1 + zs1.sum) (n + 1) ft'))

/-- Place the text with the branch widths `ws`, lay out the result, and
repeat with the layout's widths until they are the planned ones.

The next round's widths *replace* the planned ones rather than being OR-ed
with them: the assembler relaxes a branch to its short form whenever it fits,
so a plan with a branch wider than the layout of its own result never matches
(the comparison fails), and OR-ed widths could never shrink back to it. With
replacement, the rounds stop exactly at a plan that is its own layout. They
are not proved to converge (a moved block can shorten a branch, which can
move a block back); they are bounded by `fuel` and fail closed: the result is
returned only after the comparison and `wordsOk`, never a mismatched one. -/
def rounds (isa : Isa α) (gs : Nat) (points : List String) (text rest : List α) :
    Nat → List Bool → Except String (List α)
  | 0, _ => .error "granule: the branch widths did not settle"
  | fuel + 1, ws => do
    let out ← place isa gs (segment isa points (text.zip ws) true none []) 0 0 false
    let fin := out.map (·.1)
    let zs ← layout isa fin
    if zs == (out.map (·.2.1)).take zs.length then
      unless wordsOk isa gs 0 (textPart isa fin) zs do
        throw "granule: a descriptor word is misplaced"
      pure (fin ++ rest)
    else
      let ws' := ((out.zip zs).filter (·.1.2.2)).map fun ((x, _, _), z) =>
        (isa.target? x).isSome && z > isa.shortLen
      rounds isa gs points text rest fuel ws'

/-- The label of the end of the text (`scc_text_end`, emitted by the
emitter as the text's last label): the emitter's `IR.StackMap.textEndSym`. -/
def textEndSym : String := Scc.IR.StackMap.textEndSym

/-- **The text's end label, held back**: where the text ends in the label
`textEndSym` followed only by items that are neither labels nor instructions
(blank lines, symbol directives), the text before it and those items; the
pass places them after the last word, before the ISA's tail, so that the
label marks the end of the padded text. Otherwise the text and nothing. Only
the pass's own items (filler, word, word label) move past it: the order of
every other item is kept. -/
def splitEnd (isa : Isa α) (text : List α) : List α × List α :=
  let quiet (x : α) : Bool := (isa.label? x).isNone && (isa.ins? x).isNone
  let post := (text.reverse.takeWhile quiet).reverse
  let pre := text.take (text.length - post.length)
  match pre.getLast? with
  | some x => if isa.label? x == some textEndSym then (pre.dropLast, x :: post) else (text, [])
  | none => (text, [])

/-- **The granule pass** with granule size `gs` and insertion points
`points`: the items with the text placed in granules (see the module
docstring), the rest unchanged. -/
def granuleWith (isa : Isa α) (gs : Nat) (points : List String) (items : List α) :
    Except String (List α) := do
  let text := textPart isa items
  let rest := items.dropWhile (!isa.ends ·)
  if rest.any isa.resumes then throw "granule: the text resumes after a data section"
  let (body, fin) := splitEnd isa text
  rounds { isa with tail := fin ++ isa.tail } gs points body rest 16 (body.map fun _ => false)

#guard (dirSize true 4 ".zero 12").toOption == some 12 && (dirSize false 0 wordLine).toOption == some 8
#guard (dirSize false 13 ".p2align 4").toOption == some 3 && (dirSize false 13 ".balign 8").toOption == some 3
#guard (dirSize true 13 ".p2align 4").toOption.isNone && (dirSize true 16 ".p2align 4").toOption == some 0
#guard (dirSize true 0 ".globl f").toOption == some 0 && (dirSize true 0 ".size f, .-f").toOption == some 0
#guard (dirSize true 0 ".byte 1").toOption.isNone && (dirSize true 0 ".quad x").toOption.isNone
#guard (dirSize true 0 ".fill 4").toOption.isNone && wordLabel 3 == ".Lgw3" && zeroLine 5 == ".zero 5"

end Scc.Emit.Granule
