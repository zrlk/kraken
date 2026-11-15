import Scc.Cert.GranuleErase
import Scc.Emit.GranuleA64
import Scc.Emit.A64Test

/-!
# Erasing the granule pass's own items on AArch64 (untrusted)

The AArch64 instance of `Scc.Cert.Granule.eraseG`: raw lines (`Item.raw`)
are the lines (filler, words, tail, and the assembler lines that place
nothing), Kraken labels the labels, Kraken instructions classified by
`Scc.Emit.Granule.insA64`. `eraseA64_no_insert`: an accepted output has the
emitter's instructions, no inserted `b`.

Tests: on the cert programs, at the real granule size and at small test
granules (blocks moved, words inside the text), erasing the pass's output
gives the emitter's items back; an output with a jump inserted in front of
a word is refused.
-/

namespace Scc.Cert.Granule
open Scc.Emit.A64
open Scc.Emit.Granule (insA64 tailA64 granuleWith isaA64 pointsA64 granule)

/-- The labels of a constant expression. -/
def labelsA64 : ConstExpr → List String
  | .label l => [l]
  | .add a b | .sub a b => labelsA64 a ++ labelsA64 b
  | .pg_hi21 e | .lo12 e => labelsA64 e
  | _ => []

/-- The labels named by an AArch64 directive's control transfer: the target
expression of `b`, `b.cond`, `bl`, `cbz`, `cbnz`, `tbz`, `tbnz` (`br` and
`blr` name none). -/
def targetsA64 : Directive → List String
  | .instr ⟨_, .B t⟩ | .instr ⟨_, .B_cond _ t⟩ | .instr ⟨_, .BL t⟩ => labelsA64 t
  | .instr ⟨_, .CBZ _ t⟩ | .instr ⟨_, .CBNZ _ t⟩ => labelsA64 t
  | .instr ⟨_, .TBZ _ _ t⟩ | .instr ⟨_, .TBNZ _ _ t⟩ => labelsA64 t
  | _ => []

/-- **The AArch64 erasure ISA.** -/
def eA64 : Isa Item where
  line? | .raw s => some s | _ => none
  label? | .d (.label l) => some l | _ => none
  ins? | .d d => insA64 d | _ => none
  targets | .d d => targetsA64 d | _ => []
  tail := tailA64.filterMap fun | .raw s => some s | _ => none

theorem eA64_line (x : Item) (h : (eA64.line? x).isSome) : eA64.ins? x = none := by
  cases x <;> simp_all [eA64]

theorem eA64_label (x : Item) (h : (eA64.label? x).isSome) : eA64.ins? x = none := by
  cases x with
  | d d => cases d <;> simp_all [eA64, insA64]
  | _ => simp_all [eA64]

/-- **No inserted instruction on AArch64.** -/
theorem eraseA64_no_insert {final items : List Item}
    (h : eraseG eA64 final false false 0 = some items) :
    final.filter (fun x => (eA64.ins? x).isSome) = items.filter (fun x => (eA64.ins? x).isSome) :=
  eraseG_no_insert eA64 eA64_line eA64_label h

namespace TestA64

/-- The rendered lines, for comparing item lists. -/
def lines (xs : List Item) : List String := xs.map Item.render

/-- The pass with granule size `gs` on a program, then erasure: `some` the
number of words when erasure gives the emitter's items back. -/
def roundTrip (p : IR.Program) (gs : Nat) : Option Nat := do
  let items ← (emitItems p).toOption
  let out ← (granuleWith isaA64 gs (pointsA64 p) items).toOption
  let back ← eraseG eA64 out false false 0
  guard (lines back == lines items)
  pure (out.countP fun | .d (.label l) => l.startsWith ".Lgw" | _ => false)

/-- The IR of a WeakCore source text for AArch64. -/
def compileIR (src : String) : Option IR.Program := do
  let c ← (Frontend.run src).toOption
  (Lower.lowerProgram { arch := .arm } c).toOption

def progs : List (Option IR.Program) :=
  [compileIR (w_src% "Scc/Test/hello1.w"), compileIR (w_src% "Scc/Test/hello.w"),
   compileIR (w_src% "Scc/Test/wake.w"), compileIR (w_src% "Scc/Test/call1.w"),
   compileIR (w_src% "Scc/Test/chain5.w"), compileIR (w_src% "Scc/Test/ret0.w")]

#guard progs.map (·.bind (roundTrip · granule)) == List.replicate 6 (some 1)
#guard (progs.take 3).all fun p => match p.bind (roundTrip · 512) with
  | some n => n > 1
  | none => false

/-- Insert a `b` to `l` in front of the first filler (as the fallback of
plain option (b) would). -/
def withJump (l : String) : List Item → List Item
  | [] => []
  | x :: xs => match xs with
    | .raw s :: _ => if s.startsWith ".zero " then x :: Scc.Emit.A64.jmp l :: xs
        else x :: withJump l xs
    | _ => x :: withJump l xs

-- An output with an inserted jump is refused (the jump is kept, so erasure
-- does not give the emitter's items back, or refuses the filler after it).
#guard (progs.take 3).all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some out := (granuleWith isaA64 512 (pointsA64 p) items).toOption | return false
  let out' := withJump "x" out
  return out'.length == out.length + 1 && match eraseG eA64 out' false false 0 with
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
  let some out := (granuleWith isaA64 512 (pointsA64 p) items).toOption | return false
  let jmp (t : String) : Item := Scc.Emit.A64.jmp t
  return (eraseG eA64 (afterLabel "_start" (jmp "x") out) false false 0).isSome &&
    (eraseG eA64 (afterLabel "_start" (jmp Scc.Emit.Granule.textEndSym) out) false false 0).isNone

end TestA64

end Scc.Cert.Granule
