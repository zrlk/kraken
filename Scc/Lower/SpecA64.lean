import Scc.Lower.Spec
import Scc.Emit.A64
import Scc.Cert.PlaceA64

/-!
# scc's pipeline as one function, AArch64

`lowerAll cfg p`: scc's AArch64 pipeline from a checked WeakCore program to
its output at the level of Kraken's syntax, as one total function the kernel
reduces: the lowering to the IR (`lowerIR`), the emitter's items
(`Scc.Emit.A64.emitItemsMaps`), and from them

* `prog`, the instruction list: the items of the `.text` sections, raw lines
  and comments dropped (`textDirectives`), which is what the canonical loader
  parses from the printed text (`Scc.Sem.A64.textProgram`; checked on the
  test programs);
* `secs`, the data sections as data items (`Scc.Emit.Data.Secs.ofProgram`,
  as `Scc.Emit.A64.dataSecs`; the loader reads the same items from the text);
* the stack need table (`stackNeed`), the placement data of the compiled
  functions (`Scc.Cert.Place.A64.places`) and the lowering's record
  (`Lowered`: checked program, depth limit, IR, placement trace).

`scc --arch arm` runs exactly this: `Scc.Cli.run` calls `lowerIR`, then
`emitAll` (through `Emitted.listing`, which also renders the text), so the
text it writes is `Scc.Emit.A64.render` of `items`.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower.A64

open Scc.Emit.A64 (Item Safepoint emitItemsMaps render dataSecs)

/-- The program of the `.text` sections of an item list: the Kraken
directives (instructions and labels) after a `.text` line or before any
section line, in order; a raw line starting `.data`, `.bss`, `.section` or
`.rodata` opens a data section, whose items are dropped, as the loader's
`Scc.Sem.textSection` does with the printed lines.

The prefix tests are `Scc.Lower.lineStarts`, the kernel-reducible form of
`s.trimAsciiStart.toString.startsWith`. -/
def textDirectives (items : List Item) : _root_.Program :=
  let step (acc : Bool × List Directive) : Item → Bool × List Directive
    | .raw s =>
      let pre := lineStarts s
      if pre ".text" then (true, acc.2)
      else if pre ".data" || pre ".bss" || pre ".section" || pre ".rodata" then (false, acc.2)
      else acc
    | .d x => if acc.1 then (true, x :: acc.2) else acc
    | .comment _ => acc
  (items.foldl step (true, [])).2.reverse

/-- **scc's AArch64 output** for one program (see the module docstring). -/
structure Emitted where
  /-- The lowering to the IR. -/
  low : Lowered
  /-- The emitter's items: the printed text is `Scc.Emit.A64.render items`. -/
  items : List Item
  /-- The safepoints, in code order (`Scc.Emit.A64.emitItemsMaps`). -/
  safepoints : List Safepoint
  /-- The instruction list (`textDirectives items`). -/
  prog : _root_.Program
  /-- The data sections. -/
  secs : Scc.Emit.Data.Secs
  /-- The stack need table (`stackNeed`), `none` with non-tail recursion. -/
  need : Option (List (Sym × Nat × Nat))
  /-- The placement data of the functions (`Scc.Cert.Place.A64.places`). -/
  places : Except String (List Cert.Place.FnPlace)
  /-- The frame sizes of the functions, in order (`framesOf`). -/
  frames : List Nat

instance : Inhabited Emitted :=
  ⟨{ low := default, items := [], safepoints := [], prog := [], secs := {}, need := none,
     places := .ok [], frames := [] }⟩

/-- The emitter's context of function `f`, the `fi`th of program `p`: the one
`Scc.Emit.A64.emitItemsMaps` emits it in (slots, frame, labels). -/
def ctxOf (p : IR.Program) (fi : Nat) (f : Func) : Scc.Emit.A64.FnCtx :=
  Scc.Emit.A64.fnCtx p.abortFn p.growth (StackMap.argAreas p Scc.Emit.A64.argRegs.length) fi f

/-- The emission of function `f`, the `fi`th of program `p`, as
`Scc.Emit.A64.emitItemsMaps` emits it (`emitFunc` in the context
`ctxOf p fi f`): its items and safepoints. -/
def funcItems (p : IR.Program) (fi : Nat) (f : Func) :
    Except String (List Item × List Safepoint) :=
  Scc.Emit.A64.emitFunc p.abortFn p.growth (StackMap.argAreas p Scc.Emit.A64.argRegs.length) fi f

/-- The IR registers of the main-thread runtime function: `tcb`, the setup
words, `main`'s result if it returns an `Int`, the `exit_group` result. -/
def mainSlots (entry : Frontend.Entry) (sw : Nat) : Nat :=
  1 + mainSetup entry sw + (if entry.retInt then 1 else 0) + 1

/-- The frame size of the main-thread runtime function, above an outgoing
area of `out` words. -/
def mainFrame (entry : Frontend.Entry) (sw : Nat) (out : Nat := 0) : Nat :=
  8 * out + Scc.Emit.A64.align16 (8 * mainSlots entry sw + 16)

/-- The slot offset of `main`'s result in the main-thread runtime function
(where it is kept for `exit_group`), above an outgoing area of `out` words. -/
def mainSpill (entry : Frontend.Entry) (sw : Nat) (out : Nat := 0) : Nat :=
  8 * (out + 1 + mainSetup entry sw)

/-- The frame sizes of a program's functions, in order. -/
def framesOf (p : IR.Program) : List Nat :=
  p.funcs.zipIdx.map fun (f, fi) => (ctxOf p fi f).frame

/-- **The AArch64 emission** of a lowered program. It fails only where the
emitter's items fail (`emitItemsMaps`); the other fields are computed from
the items and the IR. -/
def emitAll (l : Lowered) : Except String Emitted := do
  let (items, sps) ← emitItemsMaps l.ir
  pure { low := l, items, safepoints := sps, prog := textDirectives items,
         secs := Scc.Emit.Data.Secs.ofProgram l.ir.data (if l.ir.growth.isSome then some sps else none)
         need := (stackNeed .arm l.ir).toOption
         places := Cert.Place.A64.places l.ir
         frames := framesOf l.ir }

/-- **scc's AArch64 pipeline**, failing with the first error. -/
def lowerAll? (cfg : Config) (p : Prog) : Except String Emitted :=
  lowerIR cfg p >>= emitAll

/-- **scc's AArch64 pipeline** as a total function: an empty output (no
instructions, so no placement check holds of it) where `lowerAll?` fails. -/
def lowerAll (cfg : Config) (p : Prog) : Emitted :=
  match lowerAll? cfg p with
  | .ok e => e
  | .error _ => default

/-- The text and the other outputs of `scc` (`Scc.Cli.run`): the items
rendered (`Scc.Emit.A64.render`, which refuses an item that does not print
back), the placement data and the stack need table. -/
def Emitted.listing (e : Emitted) : Except String Listing := do
  pure { text := ← render e.items, places := some e.places, need := e.need }

/-- `emitAll`'s data sections are the emitter's (`Scc.Emit.A64.dataSecs`). -/
theorem emitAll_secs {l : Lowered} {e : Emitted} (h : emitAll l = .ok e) :
    dataSecs l.ir = .ok e.secs := by
  unfold emitAll at h
  unfold dataSecs
  cases hm : emitItemsMaps l.ir with
  | error _ => rw [hm] at h; cases h
  | ok r =>
    rw [hm] at h
    cases h
    rfl

/-- `emitAll`'s IR is the lowering's and its frame sizes are `framesOf` it. -/
theorem emitAll_frames {l : Lowered} {e : Emitted} (h : emitAll l = .ok e) :
    e.low = l ∧ e.frames = framesOf l.ir := by
  unfold emitAll at h
  cases hm : emitItemsMaps l.ir with
  | error _ => rw [hm] at h; cases h
  | ok r =>
    rw [hm] at h
    cases h
    exact ⟨rfl, rfl⟩

end Scc.Lower.A64
