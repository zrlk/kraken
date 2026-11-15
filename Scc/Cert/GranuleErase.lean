import Scc.Cert.MapsCompute
import Scc.Emit.GranuleCore

/-!
# Erasing the granule pass's own items (untrusted, ISA-generic)

The granule pass (`Scc.Emit.Granule`) inserts into the emitter's text only
its own items: zero filler (`.zero k`), descriptor words (a `.Lgw<n>` label
and the line `.quad scc_gc_desc - .`) and the tail (the alignment of the text
section to a granule). A certificate does not run the pass: it is handed
the pass's output `final` and checks, by the kernel's evaluation of
`eraseG`, that erasing those items from `final` gives the emitter's items
back, `eraseG E final false false 0 = some items`. The structural facts
proved about `items` then carry to `final`.

`eraseG` walks `final` once and fails (`none`) unless every own item sits
where no instruction falls into it:

* filler only when the code before it does not fall through (`pt`: the last
  instruction before it ends the flow, `Ins.term`, with only erased items,
  assembler lines that place nothing, comments and blanks after it);
* a label immediately followed by the word line only when `pt` and its name
  starts with `wordPrefix`; it and the word are erased together; a word line
  anywhere else is refused;
* the tail (its lines in order) only when `pt`.

A kept label clears `pt` (a label can be jumped to, so the code after it is
reached), except the end-of-text label `textEndSym`, which keeps it: the pass
places that label after its last word and before the tail
(`Scc.Emit.Granule.splitEnd`), and it marks the end of the text, after the
last instruction, so control does not reach the code after it through it:
no instruction jumps to it, as the walk refuses every instruction whose branch
or call target names `textEndSym` (`Isa.targets`). A kept instruction sets
`pt` to whether it ends the flow. The first
line that ends the text (`.data`, `.bss`, `.section`, outside the tail) ends
the walk: the rest is kept verbatim.

**Every inserted jump is rejected.** `eraseG` never erases an instruction:
the instructions of its result are exactly those of `final`
(`eraseG_ins`). So when the result is the emitter's items, `final` has no
instruction the emitter did not write (`eraseG_no_insert`): an output with
a jump into a moved block, as the pass's documented fallback (plain option
(b)) would insert, is refused. The pass inserts none (option (b′):
`Scc.Emit.Granule.segment` cuts only where no instruction falls in).

Kernel cost: `eraseG` is structural on the list and reads a line only with
`==` and `Scc.Cert.Maps.startsK` (UTF-8 bytes), never `String.startsWith`
or the pass's `dirSize`.
-/

namespace Scc.Cert.Granule
open Scc.Emit.Granule (Ins wordLine wordPrefix textEndSym)

/-- What erasure needs to know of an ISA's items `α`. -/
structure Isa (α : Type) where
  /-- The text of an assembler line item (a directive line), `none` for every
  other item. -/
  line? : α → Option String
  /-- The label an item defines. -/
  label? : α → Option String
  /-- The flow of an instruction item; `none` for every other item. -/
  ins? : α → Option Ins
  /-- The labels named by an instruction item's control transfer (the target
  expression of a branch or a call); `[]` for every other item. -/
  targets : α → List String
  /-- The lines of the pass's tail, in order. -/
  tail : List String

variable {α : Type}

/-- Is the line the pass's filler? -/
def isZeroK (s : String) : Bool := Maps.startsK s ".zero "

/-- Does the line end the text? -/
def endsK (s : String) : Bool := s == ".data" || s == ".bss" || Maps.startsK s ".section"

/-- Is the head of the items the word line? -/
def headWord (E : Isa α) : List α → Bool
  | x :: _ => E.line? x == some wordLine
  | [] => false

/-- Do the items start with the lines `ls`, in order? -/
def linesPrefix (E : Isa α) : List String → List α → Bool
  | [], _ => true
  | l :: ls, x :: xs => E.line? x == some l && linesPrefix E ls xs
  | _ :: _, [] => false

/-- **The erasure walk**, structural on the list: `pt` the code before cannot
fall through, `sk` the next item is the word after an erased `.Lgw` label,
`tl` tail lines still to erase (checked at the tail's first line). See the
module docstring. -/
def eraseG (E : Isa α) : List α → Bool → Bool → Nat → Option (List α)
  | [], _, sk, tl => if !sk && tl == 0 then some [] else none
  | x :: xs, pt, sk, tl =>
    if sk then (if E.line? x == some wordLine then eraseG E xs pt false tl else none)
    else if tl > 0 then (if (E.line? x).isSome then eraseG E xs pt false (tl - 1) else none)
    else match E.line? x with
    | some s =>
      if E.tail.head? == some s then
        (if pt && linesPrefix E E.tail (x :: xs) then eraseG E xs pt false (E.tail.length - 1)
         else none)
      else if endsK s then some (x :: xs)
      else if isZeroK s then (if pt then eraseG E xs pt false 0 else none)
      else if s == wordLine then none
      else (eraseG E xs pt false 0).map (x :: ·)
    | none => match E.label? x with
      | some l =>
        if headWord E xs then
          (if pt && Maps.startsK l wordPrefix then eraseG E xs pt true 0 else none)
        else (eraseG E xs (pt && l == textEndSym) false 0).map (x :: ·)
      | none => match E.ins? x with
        | some k =>
          if (E.targets x).contains textEndSym then none
          else (eraseG E xs (k == .term) false 0).map (x :: ·)
        | none => (eraseG E xs pt false 0).map (x :: ·)

/-! ## What erasure keeps -/

/-- The result of `eraseG` is a sublist of its input. -/
theorem eraseG_sublist (E : Isa α) :
    ∀ (xs : List α) (pt sk : Bool) (tl : Nat) (ys : List α),
      eraseG E xs pt sk tl = some ys → ys.Sublist xs := by
  intro xs
  induction xs with
  | nil =>
    intro pt sk tl ys h
    simp only [eraseG] at h
    split at h <;> simp_all
  | cons x xs ih =>
    intro pt sk tl ys h
    simp only [eraseG] at h
    repeat' first
      | (split at h)
      | (obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact (ih _ _ _ _ hz).cons_cons x)
      | (cases h; exact List.Sublist.refl _)
      | exact ((ih _ _ _ _ h).cons x)
      | (cases h)

/-- **Erasure keeps every instruction**: when no line or label item is an
instruction, the instructions of `eraseG`'s result are those of its input,
in order. -/
theorem eraseG_ins (E : Isa α) (hl : ∀ x, (E.line? x).isSome → E.ins? x = none)
    (hb : ∀ x, (E.label? x).isSome → E.ins? x = none) :
    ∀ (xs : List α) (pt sk : Bool) (tl : Nat) (ys : List α),
      eraseG E xs pt sk tl = some ys →
        ys.filter (fun x => (E.ins? x).isSome) = xs.filter (fun x => (E.ins? x).isSome) := by
  intro xs
  induction xs with
  | nil =>
    intro pt sk tl ys h
    simp only [eraseG] at h
    split at h <;> simp_all
  | cons x xs ih =>
    intro pt sk tl ys h
    simp only [eraseG] at h
    repeat' split at h
    all_goals first
      | (obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
         rw [List.filter_cons, List.filter_cons, ih _ _ _ _ hz])
      | (cases h; rfl)
      | (cases h; done)
      | (have hx : E.ins? x = none := hl x ‹(E.line? x).isSome = true›
         rw [List.filter_cons_of_neg (by simp [hx]), ih _ _ _ _ h])
      | (have hx : E.ins? x = none :=
           hl x (by rw [beq_iff_eq.mp ‹(E.line? x == some wordLine) = true›]; rfl)
         rw [List.filter_cons_of_neg (by simp [hx]), ih _ _ _ _ h])
      | (have hx : E.ins? x = none := hl x (by rw [‹E.line? x = some _›]; rfl)
         rw [List.filter_cons_of_neg (by simp [hx]), ih _ _ _ _ h])
      | (have hx : E.ins? x = none := hb x (by rw [‹E.label? x = some _›]; rfl)
         rw [List.filter_cons_of_neg (by simp [hx]), ih _ _ _ _ h])

/-- **No inserted instruction**: if erasing the own items of `final` gives
`items`, `final` and `items` have the same instructions in order; in
particular `final` has no jump the emitter did not write. -/
theorem eraseG_no_insert (E : Isa α) (hl : ∀ x, (E.line? x).isSome → E.ins? x = none)
    (hb : ∀ x, (E.label? x).isSome → E.ins? x = none) {final items : List α}
    (h : eraseG E final false false 0 = some items) :
    final.filter (fun x => (E.ins? x).isSome) = items.filter (fun x => (E.ins? x).isSome) :=
  (eraseG_ins E hl hb final false false 0 items h).symm

/-! ## Tests (a toy ISA) -/

namespace Test

/-- Toy items: a label, an instruction with its flow, an assembler line, a
jump to a label. -/
inductive T where
  | lab (_ : String)
  | ins (_ : Ins)
  | ln (_ : String)
  | jmp (_ : String)
  deriving BEq

/-- The toy ISA, with a one-line tail. -/
def E : Isa T where
  line? | .ln s => some s | _ => none
  label? | .lab l => some l | _ => none
  ins? | .ins k => some k | .jmp _ => some .term | _ => none
  targets | .jmp l => [l] | _ => []
  tail := [".p2align 16"]

/-- The filler, a word and its label. -/
def own (n k : Nat) : List T := [.ln s!".zero {k}", .lab s!".Lgw{n}", .ln wordLine]

def items : List T := [.ln ".text", .lab "a", .ins .other, .ins .term, .lab "b", .ins .call, .ins .term,
  .ln ".data", .ln ".zero 4"]

/-- Own items after each `term`, the tail before `.data`. -/
def final : List T := [.ln ".text", .lab "a", .ins .other, .ins .term] ++ own 0 8 ++
  [.lab "b", .ins .call, .ins .term] ++ own 1 4 ++ [.ln ".p2align 16", .ln ".data", .ln ".zero 4"]

def ok (xs : List T) : Bool := match eraseG E xs false false 0 with
  | some ys => ys == items
  | none => false

#guard ok final
-- after `.data` the rest is kept verbatim (the `.zero 4` there is data, not filler)
#guard (eraseG E items false false 0).map List.length == some items.length
-- filler where the code falls into it is refused
#guard !ok ([.ln ".text", .lab "a", .ins .other, .ln ".zero 4", .ins .term] ++ final.drop 4)
-- filler right after a label (which can be jumped to) is refused
#guard (eraseG E [.lab "a", .ln ".zero 4", .ins .term] true false 0).isNone
-- after a call: refused
#guard (eraseG E [.ins .call, .ln ".zero 4", .ins .term] false false 0).isNone
-- a word line without its label, or a word label not named `.Lgw…`, is refused
#guard (eraseG E [.ins .term, .ln wordLine] false false 0).isNone
#guard (eraseG E [.ins .term, .lab "x", .ln wordLine] false false 0).isNone
-- an inserted jump is kept, so the result is not the emitter's items
#guard !ok ([.ln ".text", .lab "a", .ins .other, .ins .term, .ins .term] ++ final.drop 4)
-- the tail after a falling-through instruction is refused
#guard (eraseG E [.ins .other, .ln ".p2align 16", .ln ".data"] false false 0).isNone
-- the end-of-text label keeps `pt`: the tail after it is erased; any other label clears it
#guard (eraseG E [.ins .term, .lab textEndSym, .ln ".p2align 16", .ln ".data"] false false 0).map List.length
  == some 3
#guard (eraseG E [.ins .term, .lab "x", .ln ".p2align 16", .ln ".data"] false false 0).isNone
-- a jump to the end-of-text label is refused; a jump elsewhere is kept
#guard (eraseG E [.jmp textEndSym, .ins .term, .lab textEndSym, .ln ".p2align 16"] false false 0).isNone
#guard (eraseG E [.jmp "a", .ins .term, .lab textEndSym, .ln ".p2align 16"] false false 0).map List.length
  == some 3

end Test

end Scc.Cert.Granule
