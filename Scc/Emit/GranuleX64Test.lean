import Scc.Emit.GranuleX64
import Scc.Emit.PostX64
import Scc.Emit.X64Test

/-!
# The x64 granule pass on the emitter's programs

For the IR test programs and the `Scc/Test/*.w` programs of
`Scc.Emit.X64Test`: the pass succeeds, every item of the input comes out
in order (`insertsOnly`: the input is the output without the pass's
filler, words and tail; no jump is inserted), every point label is defined
exactly once, every word sits at `≡ granule − 8` and the text ends on a
granule boundary (`wordsOk`), the output renders, and the data after the
text is unchanged.
-/

namespace Scc.Emit.Granule.TestX64Progs
open Scc.Emit.X64 Scc.Emit.Granule

/-- Is an item one the pass adds (filler, a word or its label, the tail)? No
instruction is: the pass inserts no jump. -/
def added (_ps : List String) : Item → Bool
  | .d (.label l) => l.startsWith wordPrefix
  | .dir s => s.startsWith ".zero " || s == wordLine || tailX64.any (fun | .dir t => t == s | _ => false)
  | _ => false

/-- The lines of items. -/
def lines (xs : List Item) : List String := xs.map fun it => it.line?.getD "?"

/-- Is `out` the line list `inp` with only lines of added items inserted? -/
def insertsOnly (ps : List String) : List String → List Item → Bool
  | [], out => out.all (added ps)
  | l :: ls, x :: xs =>
    if x.line?.getD "?" == l then insertsOnly ps ls xs
    else added ps x && insertsOnly ps (l :: ls) xs
  | _ :: _, [] => false

/-- The checks above, on a program's items; `some` the number of words. -/
def check (p : IR.Program) (items : List Item) : Option Nat := do
  let out ← (granuleX64 p items).toOption
  let ps := pointsX64 p
  let text := textPart isaX64 out
  let zs ← (layout isaX64 out).toOption
  guard (insertsOnly ps (lines items) out)
  guard (ps.all fun l => (text.countP fun | .d (.label m) => m == l | _ => false) == 1)
  guard (wordsOk isaX64 granule 0 text zs)
  guard (lines (out.drop text.length) == lines (tailX64 ++ items.dropWhile (!isaX64.ends ·)))
  guard (render out).toOption.isSome
  pure (text.countP fun | .d (.label l) => l.startsWith wordPrefix | _ => false)

/-- Check a program. -/
def ir (p : IR.Program) : Option Nat := do check p (← (emitItems p).toOption)

/-- The IR of a WeakCore source text for x64. -/
def compileIR (src : String) : Option IR.Program := do
  let c ← (Frontend.run src).toOption
  (Lower.lowerProgram { arch := .x64 } c).toOption

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
  let out ← granuleWith isaX64 gs (pointsX64 p) items
  let inText := (textPart isaX64 items).length
  pure (insertsOnly (pointsX64 p) (lines (items.take inText)) (textPart isaX64 out))

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


/-! ### The post-emission pipeline

`emitFinal` (`Scc/Emit/PostX64.lean`) prints the pass's output: the
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
  match emitFinal p, emitItemsMaps p, emit p with
  | .ok t, .ok (its, sps), .ok t0 =>
    (postEmit p its sps).toOption.map (·.2.isEmpty) == some true &&
    ((granuleX64 p its).toOption.bind fun f => (render f).toOption) == some t &&
    t != t0 && dataTail t == dataTail t0 && !(dataTail t).isEmpty
  | _, _, _ => false

#guard ((compileIR (w_src% "Scc/Test/hello1.w")).map postOk) == some true
#guard ((compileIR (w_src% "Scc/Test/overflow.w")).map postOk) == some true

end Scc.Emit.Granule.TestX64Progs
