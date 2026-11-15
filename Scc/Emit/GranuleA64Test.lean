import Scc.Emit.GranuleA64
import Scc.Emit.PostA64
import Scc.Emit.A64Test
import Scc.Sem.TargetA64
import Scc.Cert.MapsA64

/-!
# The AArch64 granule pass on the emitter's programs

For the IR test programs and some `Scc/Test/*.w` programs: the pass
succeeds, the input comes out in order with only the pass's filler and
words inserted, no jump (`insertsOnly`), every point label is defined exactly
once, every word sits at `≡ granule − 8` and the text ends on a granule
boundary (`wordsOk`), the output renders, and the tail and the data after
the text are unchanged.

**The tail is invisible to the readers.** The loader's text reader
(`Scc.Sem.textProgram`) and the stack-map reader (`Scc.Cert.MapsA64.itemsOf`)
read the same program from the emitter's items with and without the tail
inserted at the end of the text; and the loader reads the same program from
the pass's output with and without its tail. (`MapsA64` does not yet accept
the pass's filler and word lines in the text, so it is compared on the
emitter's items only.)
-/

namespace Scc.Emit.Granule.TestA64Progs
open Scc.Emit.A64 Scc.Emit.Granule

/-- Is an item one the pass adds (filler, a word or its label)? No
instruction is: the pass inserts no jump. -/
def added (_ps : List String) : Item → Bool
  | .d (.label l) => l.startsWith wordPrefix
  | .raw s => s.startsWith ".zero " || s == wordLine
  | _ => false

/-- The lines of items. -/
def lines (xs : List Item) : List String := xs.map Item.render

/-- Is `out` the line list `inp` with only lines of added items inserted? -/
def insertsOnly (ps : List String) : List String → List Item → Bool
  | [], out => out.all (added ps)
  | l :: ls, x :: xs =>
    if x.render == l then insertsOnly ps ls xs
    else added ps x && insertsOnly ps (l :: ls) xs
  | _ :: _, [] => false

/-- The checks above, on a program's items; `some` the number of words. -/
def check (p : IR.Program) (items : List Item) : Option Nat := do
  let out ← (granuleA64 p items).toOption
  let ps := pointsA64 p
  let text := textPart isaA64 out
  let zs ← (layout isaA64 out).toOption
  let inText := (textPart isaA64 items).length
  guard (insertsOnly ps (lines (items.take inText)) text)
  guard (ps.all fun l => (text.countP fun | .d (.label m) => m == l | _ => false) == 1)
  guard (wordsOk isaA64 granule 0 text zs)
  guard (lines (out.drop text.length) == lines (tailA64 ++ items.drop inText))
  guard (render out).toOption.isSome
  pure (text.countP fun | .d (.label l) => l.startsWith wordPrefix | _ => false)

/-- Check a program. -/
def ir (p : IR.Program) : Option Nat := do check p (← (emitItems p).toOption)

/-- The IR of a WeakCore source text for AArch64. -/
def compileIR (src : String) : Option IR.Program := do
  let c ← (Frontend.run src).toOption
  (Lower.lowerProgram { arch := .arm } c).toOption

#guard ir Test.helloIR == some 1
#guard ir Test.allOpsIR == some 1
#guard ((compileIR (w_src% "Scc/Test/hello.w")).bind ir) == some 1
#guard ((compileIR (w_src% "Scc/Test/arith.w")).bind ir) == some 1
#guard ((compileIR (w_src% "Scc/Test/handoff.w")).bind ir) == some 1
#guard ((compileIR (w_src% "Scc/Test/overflow.w")).bind ir) == some 1

-- The cert programs at the real granule size: the pass succeeds and inserts no
-- jump (`insertsOnly` admits no inserted instruction), one granule each.
#guard ((compileIR (w_src% "Scc/Test/hello1.w")).bind ir) == some 1
#guard ((compileIR (w_src% "Scc/Test/wake.w")).bind ir) == some 1
#guard ((compileIR (w_src% "Scc/Test/call1.w")).bind ir) == some 1
#guard ((compileIR (w_src% "Scc/Test/chain5.w")).bind ir) == some 1
#guard ((compileIR (w_src% "Scc/Test/ret0.w")).bind ir) == some 1

/-! ### No silent fallback

At any granule size the pass either places every block with only its own
items inserted (`insertsOnly`: no instruction, so no jump) or refuses with
"does not fit"; it never falls back to entering a block by a jump. Swept
over test granule sizes on the cert programs; the refusals are pinned so
the sweep is not vacuous. -/

/-- The pass at granule size `gs`: `.ok` the output has only the pass's own
items inserted, `.error` its refusal. -/
def atSize (p : IR.Program) (gs : Nat) : Except String Bool := do
  let items ← emitItems p
  let out ← granuleWith isaA64 gs (pointsA64 p) items
  let inText := (textPart isaA64 items).length
  pure (insertsOnly (pointsA64 p) (lines (items.take inText)) (textPart isaA64 out))

def sweep : List (Except String Bool) :=
  [compileIR (w_src% "Scc/Test/hello1.w"), compileIR (w_src% "Scc/Test/hello.w"),
   compileIR (w_src% "Scc/Test/wake.w")].flatMap fun p =>
    [256, 384, 512, 1024].map fun gs => match p with
      | some p => atSize p gs
      | none => .error "compile"

-- Every outcome is a placement with nothing but own items inserted, or a refusal.
#guard sweep.all fun
  | .ok b => b
  | .error e => (e.splitOn "does not fit").length > 1
-- Refusals happen (the sweep reaches blocks that do not fit) and placements too.
#guard sweep.any (fun | .error _ => true | .ok _ => false) && sweep.any (fun | .ok _ => true | .error _ => false)


/-- Insert the tail at the end of the text. -/
def withTail (items : List Item) : List Item :=
  textPart isaA64 items ++ tailA64 ++ items.dropWhile (!isaA64.ends ·)

/-- Drop the tail lines. -/
def dropTail (items : List Item) : List Item :=
  items.filter fun | .raw s => !(tailA64.any fun | .raw t => t == s && s != ".text" | _ => false) | _ => true

/-- The loader's program of items. -/
def loaded (items : List Item) : Option _root_.Program := do
  Scc.Sem.A64.textProgram (← (render items).toOption) |>.toOption

/-- The readers agree with and without the tail on a program. -/
def tailInvisible (p : IR.Program) : Bool := Id.run do
  let some items := (emitItems p).toOption | return false
  let some out := (granuleA64 p items).toOption | return false
  let mapsOk := match Scc.Cert.MapsA64.itemsOf items, Scc.Cert.MapsA64.itemsOf (withTail items) with
    | .ok a, .ok b => a == b
    | _, _ => false
  return (loaded items).isSome && loaded items == loaded (withTail items) && mapsOk &&
    (loaded out).isSome && loaded out == loaded (dropTail out) && (dropTail out).length + 2 == out.length

#guard tailInvisible Test.helloIR
#guard tailInvisible Test.allOpsIR

/-! ### The post-emission pipeline

`emitFinal` (`Scc/Emit/PostA64.lean`) prints the pass's output: the
granule pass on the emitter's items, rendered; no table data yet. Everything
from the first line that ends the text on (the data sections) is the
pre-pass text's, unchanged. -/

/-- The lines from the first data section header on. -/
def dataTail (t : String) : List String :=
  (t.splitOn "\n").dropWhile fun l =>
    !(l.trimAscii.toString.startsWith ".data" || l.trimAscii.toString.startsWith ".bss" ||
      l.trimAscii.toString.startsWith ".section .rodata")

/-- `emitFinal` is the rendered pass output, with no table data, and keeps the
data sections. -/
def postOk (p : IR.Program) : Bool :=
  match emitFinal p, emitItemsMaps p, emitProgram p with
  | .ok t, .ok (its, sps), .ok t0 =>
    (postEmit p its sps).toOption.map (·.2.isEmpty) == some true &&
    ((granuleA64 p its).toOption.bind fun f => (render f).toOption) == some t &&
    t != t0 && dataTail t == dataTail t0 && !(dataTail t).isEmpty
  | _, _, _ => false

#guard ((compileIR (w_src% "Scc/Test/hello1.w")).map postOk) == some true
#guard ((compileIR (w_src% "Scc/Test/overflow.w")).map postOk) == some true

end Scc.Emit.Granule.TestA64Progs
