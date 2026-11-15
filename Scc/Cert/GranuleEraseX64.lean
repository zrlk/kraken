import Scc.Cert.GranuleErase
import Scc.Emit.GranuleX64
import Scc.Emit.X64Test

/-!
# Erasing the granule pass's own items on x64 (untrusted)

The x64 instance of `Scc.Cert.Granule.eraseG`: directive lines (`Item.dir`)
are the lines (filler, words, tail, and the assembler lines that place
nothing), Kraken labels the labels, Kraken instructions classified by
`Scc.Emit.Granule.insX64`. `eraseX64_no_insert`: an accepted output has the
emitter's instructions, no inserted jump.

Tests: on the cert programs, at the real granule size and at small test
granules (blocks moved, words inside the text), erasing the pass's output
gives the emitter's items back; an output with a jump inserted in front of
a word is refused.
-/

namespace Scc.Cert.Granule
open Scc.Emit.X64
open Scc.Emit.Granule (insX64 tailX64 granuleWith isaX64 pointsX64 granule)

/-- The labels of a constant expression. -/
def labelsX64 : ConstExpr → List String
  | .label l => [l]
  | .add a b | .sub a b => labelsX64 a ++ labelsX64 b
  | _ => []

/-- The labels named by an x64 directive's control transfer: a `jcc`'s label,
the expression of a direct `jmp` or `call` (an indirect one names none). -/
def targetsX64 : Directive → List String
  | .instr (.regular _ _ (.jcc _ l)) => [l]
  | .instr (.regular _ _ (.jmp (.rel e))) | .instr (.regular _ _ (.call (.rel e))) => labelsX64 e
  | _ => []

/-- **The x64 erasure ISA.** -/
def eX64 : Isa Item where
  line? | .dir s => some s | _ => none
  label? | .d (.label l) => some l | _ => none
  ins? | .d d => insX64 d | _ => none
  targets | .d d => targetsX64 d | _ => []
  tail := tailX64.filterMap fun | .dir s => some s | _ => none

theorem eX64_line (x : Item) (h : (eX64.line? x).isSome) : eX64.ins? x = none := by
  cases x <;> simp_all [eX64]

theorem eX64_label (x : Item) (h : (eX64.label? x).isSome) : eX64.ins? x = none := by
  cases x with
  | d d => cases d <;> simp_all [eX64, insX64]
  | _ => simp_all [eX64]

/-- **No inserted instruction on x64.** -/
theorem eraseX64_no_insert {final items : List Item}
    (h : eraseG eX64 final false false 0 = some items) :
    final.filter (fun x => (eX64.ins? x).isSome) = items.filter (fun x => (eX64.ins? x).isSome) :=
  eraseG_no_insert eX64 eX64_line eX64_label h

namespace TestX64

/-- The rendered lines, for comparing item lists. -/
def lines (xs : List Item) : List String := xs.map fun it => it.line?.getD "?"

/-- The pass with granule size `gs` on a program, then erasure: `some` the
number of words when erasure gives the emitter's items back. -/
def roundTrip (p : IR.Program) (gs : Nat) : Option Nat := do
  let items ← (emitItems p).toOption
  let out ← (granuleWith isaX64 gs (pointsX64 p) items).toOption
  let back ← eraseG eX64 out false false 0
  guard (lines back == lines items)
  pure (out.countP fun | .d (.label l) => l.startsWith ".Lgw" | _ => false)

/-- The IR of a WeakCore source text for x64. -/
def compileIR (src : String) : Option IR.Program := do
  let c ← (Frontend.run src).toOption
  (Lower.lowerProgram { arch := .x64 } c).toOption

def progs : List (Option IR.Program) :=
  [compileIR (w_src% "Scc/Test/hello1.w"), compileIR (w_src% "Scc/Test/hello.w"),
   compileIR (w_src% "Scc/Test/wake.w"), compileIR (w_src% "Scc/Test/call1.w"),
   compileIR (w_src% "Scc/Test/chain5.w"), compileIR (w_src% "Scc/Test/ret0.w")]

#guard progs.map (·.bind (roundTrip · granule)) == List.replicate 6 (some 1)
#guard (progs.take 3).all fun p => match p.bind (roundTrip · 1024) with
  | some n => n > 1
  | none => false

/-- Insert a `jmp` to `l` in front of the first word (as the fallback of
plain option (b) would). -/
def withJump (l : String) : List Item → List Item
  | [] => []
  | x :: xs => match xs with
    | .dir s :: _ => if s.startsWith ".zero " then x :: .d (i64 (.jmp (rel l))) :: xs
        else x :: withJump l xs
    | _ => x :: withJump l xs

-- An output with an inserted jump is refused (the jump is kept, so erasure
-- does not give the emitter's items back, or refuses the filler after it).
#guard (progs.take 3).all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some out := (granuleWith isaX64 1024 (pointsX64 p) items).toOption | return false
  let out' := withJump "x" out
  return out'.length == out.length + 1 && match eraseG eX64 out' false false 0 with
    | some back => lines back != lines items
    | none => true

/-- Insert the item `j` after the label `l`. -/
def afterLabel (l : String) (j : Item) : List Item → List Item
  | [] => []
  | x :: xs => match x with
    | .d (.label m) => if m == l then x :: j :: xs else x :: afterLabel l j xs
    | _ => x :: afterLabel l j xs

-- A branch to the end-of-text label is refused: that label keeps `pt` only
-- because nothing jumps to it. A jump to another label after `_start` is
-- kept (erasure succeeds, giving one more instruction); one to `scc_text_end`
-- makes erasure fail.
#guard (progs.take 3).all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some out := (granuleWith isaX64 1024 (pointsX64 p) items).toOption | return false
  let jmp (t : String) : Item := .d (i64 (.jmp (rel t)))
  return (eraseG eX64 (afterLabel "_start" (jmp "x") out) false false 0).isSome &&
    (eraseG eX64 (afterLabel "_start" (jmp Scc.Emit.Granule.textEndSym) out) false false 0).isNone
#guard (progs.take 3).all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some out := (granuleWith isaX64 1024 (pointsX64 p) items).toOption | return false
  let call (t : String) : Item := .d (i64 (.call (rel t)))
  return (eraseG eX64 (afterLabel "_start" (call Scc.Emit.Granule.textEndSym) out) false false 0).isNone

end TestX64

end Scc.Cert.Granule
