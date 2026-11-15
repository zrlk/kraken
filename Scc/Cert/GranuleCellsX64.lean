import Scc.Cert.GranuleExpands
import Scc.Cert.GranuleEraseX64
import Scc.Lower.SpecX64
import Scc.Sem.TextX64

/-!
# The granule pass's output as loaded cells, x86-64 (untrusted)

The x86-64 twin of `Scc/Cert/GranuleCellsA64.lean`: the loader's program of
the pass's output is the emitter's program with own cells inserted only
where nothing falls into them (`Scc.Cert.Granule.Expands`).

* **`textCells final`**: the program the loader (`Scc.Sem.X64.textProgram`)
  reads from the `.text` sections of the pass's output, as a
  kernel-reducible function of the items: `Scc.Lower.X64.textDirectives`'s
  walk (alignment lines as `nopalign` cells, `none` for a raw line in the
  text) plus the pass's own lines as the loader's `textData` reads them: a
  filler line `.zero k` is one empty `byteArray` cell (none for `k = 0`),
  the word line `.quad scc_gc_desc - .` one empty `byteArray` (a data cell's
  size is its size-table entry, not its contents). The word label
  `.Lgw<n>` is a Kraken label item, already in the walk; the tail is a
  section switch (no cell). Lines are recognised by
  `Scc.Cert.Maps.startsK` and `toNatK?`. A certificate compares
  `textCells final` with the loader's parse (`parsesTo`), in the kernel.
* **`cellsX64`**: the `Cells` instance over Kraken's directives: a cell's
  flow is `Scc.Emit.Granule.insX64` (the loader's no-fall-through set but
  `call`: `Spike.Lib.GranuleAgreeX64`), own cells are data cells and labels
  starting `.Lgw`.
* **`expands_of_check`**: the kernel's evaluation of `check final items`
  gives `Expands cellsX64 false i f` for the emitter's program `i` and the
  output's `f`.

**The relation is on directives, not sized cells.** The code cells are
`Kraken.Promising.X64.sizedCells f sizes` at the assembler's sizes of the
output; a relaxable branch may change width when a block moves, so the
output's sizes are not the emitter's. `sizedCells_fst` gives back `f` from
the cells, which is all the relation needs.

**The word's contents are not used.** The word is an own cell only; the
loader's cell is empty and the runtime's read of the word is outside the
model (`Scc.Sem.X64.textData`).
-/

namespace Scc.Cert.Granule.X64
open Scc.Emit.X64 (Item)
open Scc.Emit.Granule (insX64 wordLine wordPrefix)
open Scc.Lower (lineStarts)
open Scc.Lower.X64 (alignOf lineChars)

/-- The size of a filler line `.zero k`. -/
def zeroK? (s : String) : Option Nat :=
  if Maps.startsK s ".zero " then Maps.toNatK? (String.ofList (s.toList.drop 6)) else none

/-- The loader's cells of one of the pass's own lines of the text: filler
`.zero k` one empty data cell (none for `0`), the word one; `none` for any
other line. -/
def ownCells? (s : String) : Option (List Directive) :=
  if s == wordLine then some [.byteArray (.mk #[])]
  else (zeroK? s).map fun k => if k = 0 then [] else [.byteArray (.mk #[])]

/-- **The loaded program of the `.text` sections of the pass's output**
(module docstring): `textDirectives`'s walk, with the pass's own lines read
as the loader's `textData` reads them. -/
def textCells (items : List Item) : Option _root_.Program :=
  let step (acc : Option (Bool × List Directive)) (it : Item) : Option (Bool × List Directive) :=
    acc.bind fun (txt, ds) =>
      match it with
      | .dir s =>
        let pre := lineStarts s
        if pre ".text" then some (true, ds)
        else if pre ".data" || pre ".bss" || pre ".section" || pre ".rodata" then some (false, ds)
        else if txt then
          match if pre ".p2align" || pre ".balign" then alignOf (lineChars s) else none with
          | some n => some (true, .instr (Kraken.X64.Parser.toInstr .none (w := .W64) (.nopalign n none)) :: ds)
          | none => match ownCells? s with
            | some cs => some (true, cs.reverse ++ ds)
            | none => some (true, ds)
        else some (txt, ds)
      | .d x => if txt then some (true, x :: ds) else some (txt, ds)
      | .raw _ => if txt then none else some (txt, ds)
      | .comment _ | .blank => some (txt, ds)
  (items.foldl step (some (true, []))).map (·.2.reverse)

/-- Is a cell one of the pass's own (a data cell, or a label starting
`.Lgw`)? -/
def ownCell : Directive → Bool
  | .byteArray _ => true
  | .label l => Maps.startsK l wordPrefix
  | .instr _ => false

/-- **The x86-64 cells** of the bridge. -/
def cellsX64 : Cells Directive where
  own := ownCell
  flow := insX64
  label | .label _ => true | _ => false
  own_flow c h := by cases c <;> simp_all [ownCell, insX64]

/-- The check, as a `Bool` for a certificate's `decide`: the emitter's
program exists and erasing the own cells of the output's loaded program
gives it. -/
def check (final items : List Item) : Bool :=
  (Scc.Lower.X64.textDirectives items).isSome &&
    decide ((textCells final).bind (erase cellsX64 · false) = Scc.Lower.X64.textDirectives items)

/-- **The check gives the relation**: the output's loaded program is the
emitter's with own cells inserted only where nothing falls into them. -/
theorem expands_of_check {final items : List Item} (h : check final items = true) :
    ∃ f i, textCells final = some f ∧ Scc.Lower.X64.textDirectives items = some i ∧
      Expands cellsX64 false i f := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at h
  obtain ⟨⟨i, hi⟩, he⟩ := h
  rw [hi] at he
  obtain ⟨f, hf, he⟩ := Option.bind_eq_some_iff.mp he
  exact ⟨f, i, hf, hi, expands_of_erase cellsX64 _ _ _ he⟩

/-! ## Tests -/

namespace Test
open Scc.Emit.X64 Scc.Emit.Granule
open Scc.Cert.Granule.TestX64 (progs)

/-- The pass at granule size `gs`, then the check; `some` the number of own
cells. -/
def checkAt (p : IR.Program) (gs : Nat) : Option Nat := do
  let items ← (emitItems p).toOption
  let final ← (granuleWith isaX64 gs (pointsX64 p) items).toOption
  guard (check final items)
  let f ← textCells final
  pure (f.countP ownCell)

/-- The loader's program of the pass's output at granule size `gs` is
`textCells`'s. -/
def parsesAt (p : IR.Program) (gs : Nat) : Bool := Id.run do
  let some items := (emitItems p).toOption | return false
  let some final := (granuleWith isaX64 gs (pointsX64 p) items).toOption | return false
  let some asm := (render final).toOption | return false
  let some f := textCells final | return false
  return (Scc.Sem.X64.textProgram asm).toOption == some f

-- The loader reads the pass's output as `textCells` says (its own lines included).
#guard progs.all fun p => p.any (parsesAt · granule)
#guard (progs.take 3).all fun p => p.any (parsesAt · 1024)

-- The check holds at the real granule size (filler and one word) and at 1024
-- (several words, blocks moved).
#guard progs.map (·.bind (checkAt · granule)) |>.all (·.any (· ≥ 2))
#guard (progs.take 3).map (·.bind (checkAt · 1024)) |>.all (·.any (· > 4))

/-- `final` with its first `.Lgw0` renamed to `l`. -/
def renameWord (l : String) : List Item → List Item
  | [] => []
  | .d (.label m) :: xs => if m == wordLabel 0 then .d (.label l) :: xs else .d (.label m) :: renameWord l xs
  | x :: xs => x :: renameWord l xs

/-- `items` with a real label named `.Lgw_x` before its first `ret`. -/
def withOwnLike : List Item → List Item
  | [] => []
  | x :: xs => match x with
    | .d (.instr (.regular .W64 .W64 .ret)) => .d (.label ".Lgw_x") :: x :: xs
    | _ => x :: withOwnLike xs

/-- `final` with `x` inserted after every 64-bit `jmp` to a label (between
blocks, where nothing falls). -/
def afterJmps (x : Item) (final : List Item) : List Item :=
  final.flatMap fun y => match y with
    | .d (.instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label _) .after_current_instruction))))) => [y, x]
    | _ => [y]

-- Negative: a real label with the own prefix (in the items and the output
-- alike, before the first `ret`) makes the check fail.
#guard progs.all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some final := (granuleX64 p items).toOption | return false
  return check final items && (withOwnLike final).length == final.length + 1 &&
    !check (withOwnLike final) (withOwnLike items)
-- Negative: the word label renamed so it is not own: the check fails.
#guard progs.all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some final := (granuleX64 p items).toOption | return false
  return !check (renameWord "wordx" final) items
-- Negative: an inserted `jmp` in front of a filler line fails the check.
#guard (progs.take 3).all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some final := (granuleWith isaX64 1024 (pointsX64 p) items).toOption | return false
  let final' := final.flatMap fun x => match x with
    | .dir s => if Maps.startsK s ".zero " then [.d (i64 (.jmp (rel "x"))), x] else [x]
    | _ => [x]
  return final'.length > final.length && !check final' items
-- Negative: a `nop` inserted between blocks (after a `jmp`) fails the check;
-- a word label there passes (an own cell where nothing falls).
#guard (progs.take 3).all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some final := (granuleWith isaX64 1024 (pointsX64 p) items).toOption | return false
  let f1 := afterJmps (.d (i64 (.nop 1))) final
  let f2 := afterJmps (.d (.label (wordLabel 999))) final
  return f1.length > final.length && !check f1 items && check f2 items

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
    let (pre, post) := items.span fun | .dir ".data" => false | _ => true
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
  let some final := (granuleWith isaX64 gs (pointsX64 p) items).toOption | return false
  let some cs := textCells final | return false
  return hasEnd cs && (afterEnd cs).all (!ownCell ·) && check final items

end Test

end Scc.Cert.Granule.X64
