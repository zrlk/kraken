import Scc.Cert.GranuleExpands
import Scc.Cert.GranuleEraseA64
import Scc.Lower.SpecA64
import Scc.Sem.TextA64

/-!
# The granule pass's output as loaded cells, AArch64 (untrusted)

The cell-level bridge of the granule pass on AArch64: the loader's program
of the pass's output is the emitter's program with own cells inserted only
where nothing falls into them (`Scc.Cert.Granule.Expands`).

* **`textCells final`**: the cells the loader (`Scc.Sem.A64.textProgram`)
  reads from the `.text` sections of the pass's output, as a kernel-reducible
  function of the items: `Scc.Lower.A64.textDirectives` (Kraken directives
  of the `.text` sections) plus the pass's own lines as the loader's
  `textData` reads them: a filler line `.zero k` is one `zeros k` cell
  (none for `k = 0`), the word line `.quad scc_gc_desc - .` one 8-byte
  `byteArray` of zeros. The word label `.Lgw<n>` is a Kraken label item,
  already in `textDirectives`; the tail is a section switch (no cell). Lines
  are recognised by `Scc.Cert.Maps.startsK` and `toNatK?` (UTF-8 bytes,
  digits), never `String.startsWith`/`toNat?`. A certificate compares
  `textCells final` with the loader's parse (`parsesTo`, the existing trust
  boundary), in the kernel.
* **`cellsA64`**: the `Cells` instance: a cell's flow is
  `Scc.Emit.Granule.insA64` (the loader's no-fall-through set:
  `Spike.Lib.GranuleAgreeA64`), own cells are data cells and labels starting
  `.Lgw`. A real label taken for an own cell makes `erase` fail (it must then
  sit where the flow state is `true` and is dropped, so the erased cells are
  not the emitter's): safe, tested below.
* **`expands_of_check`**: the kernel's evaluation of
  `erase cellsA64 (textCells final) false = some (textDirectives items)`
  gives `Expands cellsA64 false (textDirectives items) (textCells final)`.

**The word's contents are not used.** The word is an own cell only; no
lemma reads its bytes (the loader's cell is zeros, and the runtime's read
of the word is outside the model: `Scc.Sem.A64.textData`).
-/

namespace Scc.Cert.Granule.A64
open Scc.Emit.A64 (Item)
open Scc.Emit.Granule (insA64 wordLine wordPrefix)
open Scc.Lower (lineStarts)

set_option autoImplicit false

/-- The size of a filler line `.zero k` (`k` decimal), `none` for any
other line. -/
def zeroK? (s : String) : Option Nat :=
  if Maps.startsK s ".zero " then Maps.toNatK? (String.ofList (s.toList.drop 6)) else none

/-- The loader's cells of one of the pass's own lines of the text: filler
`zeros k` (none for `0`), the word an 8-byte data cell of zeros; `none`
for any other line. -/
def ownCells? (s : String) : Option (List Directive) :=
  if s == wordLine then some [.byteArray ⟨Array.replicate 8 0⟩]
  else (zeroK? s).map fun k => if k = 0 then [] else [.zeros k]

/-- **The loaded cells of the `.text` sections of the pass's output**
(module docstring): `textDirectives`'s walk, with the pass's own lines read
as the loader's `textData` reads them. -/
def textCells (items : List Item) : _root_.Program :=
  let step (acc : Bool × List Directive) : Item → Bool × List Directive
    | .raw s =>
      let pre := lineStarts s
      if pre ".text" then (true, acc.2)
      else if pre ".data" || pre ".bss" || pre ".section" || pre ".rodata" then (false, acc.2)
      else if acc.1 then
        match ownCells? s with
        | some cs => (true, cs.reverse ++ acc.2)
        | none => acc
      else acc
    | .d x => if acc.1 then (true, x :: acc.2) else acc
    | .comment _ => acc
  (items.foldl step (true, [])).2.reverse

/-- Is a cell one of the pass's own (a data cell, or a label starting
`.Lgw`)? -/
def ownCell : Directive → Bool
  | .zeros _ | .byteArray _ => true
  | .label l => Maps.startsK l wordPrefix
  | .instr _ => false

/-- **The AArch64 cells** of the bridge. -/
def cellsA64 : Cells Directive where
  own := ownCell
  flow := insA64
  label | .label _ => true | _ => false
  own_flow c h := by cases c <;> simp_all [ownCell, insA64]

/-- **The check gives the relation**: if erasing the own cells of the
output's loaded cells gives the emitter's program, the output's cells are
the emitter's with own cells inserted only where nothing falls into them. -/
theorem expands_of_check {final items : List Item}
    (h : erase cellsA64 (textCells final) false = some (Scc.Lower.A64.textDirectives items)) :
    Expands cellsA64 false (Scc.Lower.A64.textDirectives items) (textCells final) :=
  expands_of_erase cellsA64 _ _ _ h

/-- The check, as a `Bool` for a certificate's `decide`. -/
def check (final items : List Item) : Bool :=
  decide (erase cellsA64 (textCells final) false = some (Scc.Lower.A64.textDirectives items))

theorem expands_of_check' {final items : List Item} (h : check final items = true) :
    Expands cellsA64 false (Scc.Lower.A64.textDirectives items) (textCells final) :=
  expands_of_check (of_decide_eq_true h)

/-! ## Tests -/

namespace Test
open Scc.Emit.A64 Scc.Emit.Granule

/-- The IR of a WeakCore source text for AArch64. -/
def compileIR (src : String) : Option IR.Program := do
  let c ← (Frontend.run src).toOption
  (Lower.lowerProgram { arch := .arm } c).toOption

def progs : List (Option IR.Program) :=
  [compileIR (w_src% "Scc/Test/hello1.w"), compileIR (w_src% "Scc/Test/hello.w"),
   compileIR (w_src% "Scc/Test/wake.w"), compileIR (w_src% "Scc/Test/call1.w"),
   compileIR (w_src% "Scc/Test/chain5.w"), compileIR (w_src% "Scc/Test/ret0.w")]

/-- The pass at granule size `gs`, then the check; `some` the number of own
cells. -/
def checkAt (p : IR.Program) (gs : Nat) : Option Nat := do
  let items ← (emitItems p).toOption
  let final ← (granuleWith isaA64 gs (pointsA64 p) items).toOption
  guard (check final items)
  pure ((textCells final).countP ownCell)

-- The loader reads the pass's output as `textCells` says (its own lines included).
#guard progs.all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some final := (granuleA64 p items).toOption | return false
  let some asm := (render final).toOption | return false
  return (Scc.Sem.A64.textProgram asm).toOption == some (textCells final)
#guard progs.all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some final := (granuleWith isaA64 1024 (pointsA64 p) items).toOption | return false
  let some asm := (render final).toOption | return false
  return (Scc.Sem.A64.textProgram asm).toOption == some (textCells final)

-- The check holds at the real granule size (filler and one word) and at 1024
-- (several words, blocks moved).
#guard progs.map (·.bind (checkAt · granule)) |>.all (·.any (· ≥ 3))
#guard progs.map (·.bind (checkAt · 1024)) |>.all (·.any (· > 6))

/-- `final` with its first `.Lgw0` renamed to `l` (a real label taken for
an own cell, or the other way round). -/
def renameWord (l : String) : List Item → List Item
  | [] => []
  | .d (.label m) :: xs => if m == wordLabel 0 then .d (.label l) :: xs else .d (.label m) :: renameWord l xs
  | x :: xs => x :: renameWord l xs

/-- `items` with a real label named `.Lgw_x` before its first `ret`. -/
def withOwnLike : List Item → List Item
  | [] => []
  | x :: xs => if x.render == Scc.Emit.A64.ret.render then .d (.label ".Lgw_x") :: x :: xs else x :: withOwnLike xs

-- Negative: a real label with the own prefix (in the emitter's items and the
-- output alike, before the first `ret`, where the flow state is `false`) makes
-- the check fail: it is never silently dropped. (The pass itself refuses such
-- items: its `wordsOk` takes the label for a word.)
#guard progs.all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some final := (granuleA64 p items).toOption | return false
  return check final items && (withOwnLike final).length == final.length + 1 &&
    !check (withOwnLike final) (withOwnLike items)
-- Negative: the word label renamed so it is not own: it is kept and clears the
-- flow state, so the word cell after it sits where code may fall: the check fails.
#guard progs.all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some final := (granuleA64 p items).toOption | return false
  return !check (renameWord "wordx" final) items
-- Negative: an inserted `b` in front of a filler line fails the check.
#guard progs.all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some final := (granuleWith isaA64 1024 (pointsA64 p) items).toOption | return false
  let final' := final.flatMap fun x => match x with
    | .raw s => if Maps.startsK s ".zero " then [Scc.Emit.A64.jmp "x", x] else [x]
    | _ => [x]
  return final'.length > final.length && !check final' items

/-- The cells after the end-of-text label `textEndSym` (none if it is absent). -/
def afterEnd (cs : List Directive) : List Directive :=
  (cs.dropWhile fun | .label l => l != textEndSym | _ => true).drop 1

/-- Have the cells the end-of-text label? -/
def hasEnd (cs : List Directive) : Bool := cs.any fun | .label l => l == textEndSym | _ => false

/-- The emitter's items with the end-of-text label as the text's last item
(before `.data`), as the emitter writes it from p5-labels on; unchanged if
they have it. -/
def withEnd (items : List Item) : List Item :=
  if items.any (fun | .d (.label l) => l == textEndSym | _ => false) then items
  else
    let (pre, post) := items.span fun | .raw ".data" => false | _ => true
    pre ++ [.d (.label textEndSym)] ++ post

-- `Cells.next` clears the flow state at every kept label, `textEndSym`
-- included (unlike `Scc.Cert.Granule.eraseG`). That is sound and enough
-- because no own cell follows the label in the loaded cells: the pass
-- places it after its last word (`splitEnd`), and its tail is in another
-- section, which `textCells` skips. If an own cell ever came after it, this
-- guard fails, and `Cells.next` needs `eraseG`'s two rules (the label keeps
-- the flow state, a branch to it is refused). Run on the items with the label
-- (`withEnd`), so the guard is not vacuous before the emitter writes it.
#guard (progs.map (·, granule) ++ (progs.take 3).map (·, 1024)).all fun (p, gs) => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let items := withEnd items
  let some final := (granuleWith isaA64 gs (pointsA64 p) items).toOption | return false
  let cs := textCells final
  return hasEnd cs && (afterEnd cs).all (!ownCell ·) && check final items

end Test

end Scc.Cert.Granule.A64
