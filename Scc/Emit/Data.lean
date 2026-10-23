import Kraken.DataImage
import Scc.IR.StackMap

/-!
# The data sections of an emitted program, as data images

Both emitters write the same data sections (`Scc.Emit.X64.emitData`,
`Scc.Emit.A64.emitData`, and the stack-map table `emitMaps` / `mapItems`):

* `.bss`: `.balign 16` (so that the section starts 16-aligned, as a
  layout's regions must), then per zero-initialised datum, `.balign a`, its
  label, `.zero n` (at least 1), with its `.type` and `.size` (symbol
  directives, no items: they give an executable's symbols their sizes);
* `.data`: `.balign 16`, then per initialised datum, `.balign a`, its label,
  its bytes as `.byte` lines of at most 16 (`.zero 1` when it has none);
* `.rodata` (only with growable stacks): `.balign 8`, `scc_stackmap`, the
  entry count, per safepoint `.quad label, #stack, #heap, first`, then every
  map offset as a `.quad`.

`Secs.ofProgram` gives the same sections as `Kraken.DataImage.Item` lists,
one item per directive (a `.quad` with several operands is one item per
operand), in the order the text has them.  The statement's loader reads the
text's data sections into the same items (`Scc.Sem.dataSections`); the run
tests check the two agree on the emitted programs.
-/

namespace Scc.Emit.Data

open Kraken.DataImage

/-- The data sections of a program, each in text order. -/
structure Secs where
  data : List Item := []
  bss : List Item := []
  rodata : List Item := []
  deriving Repr, DecidableEq, Inhabited

/-- `l` in pieces of at most 16 (the `.byte` lines). -/
def chunks16 {α : Type} (l : List α) : List (List α) :=
  (List.range ((l.length + 15) / 16)).map fun i => (l.drop (16 * i)).take 16

/-- The items of one datum: `(true, items)` for `.bss`, `(false, items)` for
`.data`. -/
def datumItems (d : IR.Data) : Bool × List Item :=
  match d.init with
  | .zero n => (true, [.align d.align, .label d.name, .zero (max n 1)])
  | .bytes bs =>
      (false, [.align d.align, .label d.name] ++
        (if bs.isEmpty then [.zero 1] else (chunks16 bs).map .bytes))

/-- The stack-map table (format in `Scc.IR.StackMap`) of the safepoints
`ms` (label, stack offsets, heap offsets), in emission order. -/
def mapItems (ms : List (String × List Int × List Int)) : List Item :=
  let entries := (ms.foldl (fun (acc, first) (l, st, hp) =>
      (acc ++ [Item.quadLabel l, .quad st.length, .quad hp.length, .quad first],
       first + st.length + hp.length)) (([] : List Item), (0 : Nat))).1
  [.align 8, .label IR.StackMap.tableSym, .quad ms.length] ++ entries ++
    ms.flatMap fun (_, st, hp) => (st ++ hp).map .quad

/-- The data sections of a program with data `ds` and, with growable stacks,
the safepoints `maps` (`.data` and `.bss` each opened with `.balign 16`). -/
def Secs.ofProgram (ds : List IR.Data) (maps : Option (List (String × List Int × List Int))) : Secs :=
  let its := ds.map datumItems
  { data := .align 16 :: its.flatMap fun (b, is) => if b then [] else is
    bss := .align 16 :: its.flatMap fun (b, is) => if b then is else []
    rodata := match maps with | some ms => mapItems ms | none => [] }

end Scc.Emit.Data
