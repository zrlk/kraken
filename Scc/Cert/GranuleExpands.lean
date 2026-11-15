import Scc.Emit.GranuleCore

/-!
# Own cells inserted where nothing falls into them (untrusted, generic)

The cell-level counterpart of `Scc.Cert.Granule.eraseG`: the granule pass's
output, as loaded cells `pf`, is the emitter's cells `pi` with **own cells**
(filler, word labels, words) inserted only at points no cell falls into.
Everything here is generic list reasoning over an abstract cell type `β`
(`Cells`: which cells are own, the flow of an instruction cell, which cells
are labels); the ISA instances and the link to the loader's `textCells` come
once the loader reads the pass's filler (`Directive.zeros`).

**The flow state** `pt` ("the cells before cannot fall through here") moves
over a cell as `eraseG`'s does (`Cells.next`): an own cell keeps it, an
instruction sets it to whether it ends the flow, a (kept) label clears it,
any other cell keeps it. `Cells.scan` runs it over a list. Unlike `eraseG`,
the end-of-text label (`Scc.Emit.Granule.textEndSym`) clears it too: in the
loaded cells no own cell follows that label (the pass places it after its
last word, and its tail is in another section), so nothing needs the flow
state after it. The ISA instances' tests (`GranuleCellsA64`,
`GranuleCellsX64`) guard that fact; should it change, `Cells.next` needs
`eraseG`'s two rules (the label keeps the flow state, a branch to it is
refused).

**`Expands C pt pi pf`**: `pf` is `pi` with own cells inserted, each where
the flow state is `true`; `pi` has no own cell. `erase` is a checker for it
(`expands_of_erase`).

What it gives (all for any `pt`):

* `Expands.filter_not_own`: `pi` is `pf` without its own cells, so the kept
  cells (labels included) are in the same order;
* `Expands.filter_ins`: the instruction cells of `pf` are those of `pi` (no
  inserted instruction, so no inserted jump);
* `Expands.own_pt`: before each own cell of `pf` the flow state is `true`;
  `Expands.own_not_after_fall`: an own cell never follows a cell that falls
  through (in particular a call: a return address is never an own cell);
* `Expands.seg`: a segment of `pi` that no own cell may enter
  (`noBreak`: the flow state is `false` after each of its cells but the
  last) is a segment of `pf`, contiguous; this is what carries a block of
  the emitter's cells, or a call and its return point, to the output.
-/

namespace Scc.Cert.Granule
open Scc.Emit.Granule (Ins)

set_option autoImplicit false

/-- What the relation needs to know of cells `β`. -/
structure Cells (β : Type) where
  /-- Is the cell one of the pass's own (filler, word label, word)? -/
  own : β → Bool
  /-- The flow of an instruction cell; `none` for every other cell. -/
  flow : β → Option Ins
  /-- Is the cell a label? -/
  label : β → Bool
  /-- No own cell is an instruction. -/
  own_flow : ∀ c, own c = true → flow c = none

variable {β : Type}

/-- The flow state after a cell (module docstring). -/
def Cells.next (C : Cells β) (pt : Bool) (c : β) : Bool :=
  if C.own c then pt
  else match C.flow c with
    | some k => k == .term
    | none => if C.label c then false else pt

/-- The flow state after a list of cells. -/
def Cells.scan (C : Cells β) : Bool → List β → Bool
  | pt, [] => pt
  | pt, c :: cs => C.scan (C.next pt c) cs

theorem Cells.scan_append (C : Cells β) (pt : Bool) (a b : List β) : C.scan pt (a ++ b) = C.scan (C.scan pt a) b := by
  induction a generalizing pt with
  | nil => rfl
  | cons c a ih => exact ih _

/-- **`pf` is `pi` with own cells inserted where the flow state is `true`.** -/
inductive Expands (C : Cells β) : Bool → List β → List β → Prop
  | nil (pt : Bool) : Expands C pt [] []
  | keep (pt : Bool) (c : β) {pi pf : List β} :
      C.own c = false → Expands C (C.next pt c) pi pf → Expands C pt (c :: pi) (c :: pf)
  | ins (pt : Bool) (o : β) {pi pf : List β} :
      C.own o = true → pt = true → Expands C pt pi pf → Expands C pt pi (o :: pf)

/-- **The checker**: erase the own cells of `pf`, failing at one where the
flow state is `false`. -/
def erase (C : Cells β) : List β → Bool → Option (List β)
  | [], _ => some []
  | c :: cs, pt =>
    if C.own c then (if pt then erase C cs pt else none)
    else (erase C cs (C.next pt c)).map (c :: ·)

theorem expands_of_erase (C : Cells β) : ∀ (pf : List β) (pt : Bool) (pi : List β),
    erase C pf pt = some pi → Expands C pt pi pf := by
  intro pf
  induction pf with
  | nil => intro pt pi h; cases h; exact .nil pt
  | cons c cs ih =>
    intro pt pi h
    simp only [erase] at h
    split at h
    · split at h
      · exact .ins pt c ‹_› ‹_› (ih _ _ h)
      · cases h
    · obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .keep pt c (by simpa using ‹¬C.own c = true›) (ih _ _ hz)

variable {C : Cells β}

/-- `pi` has no own cell. -/
theorem Expands.noOwn {pt : Bool} {pi pf : List β} (h : Expands C pt pi pf) :
    ∀ c ∈ pi, C.own c = false := by
  induction h with
  | nil => simp
  | keep _ c hc _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc
    · exact ih x hx
  | ins _ _ _ _ _ ih => exact ih

/-- **The kept cells**: `pi` is `pf` without its own cells. -/
theorem Expands.filter_not_own {pt : Bool} {pi pf : List β} (h : Expands C pt pi pf) :
    pf.filter (fun c => !C.own c) = pi := by
  induction h with
  | nil => rfl
  | keep _ c hc _ ih => rw [List.filter_cons_of_pos (by simp [hc]), ih]
  | ins _ o ho _ _ ih => rw [List.filter_cons_of_neg (by simp [ho]), ih]

/-- **No inserted instruction**: the instruction cells of `pf` are those of
`pi`, in order. -/
theorem Expands.filter_ins {pt : Bool} {pi pf : List β} (h : Expands C pt pi pf) :
    pf.filter (fun c => (C.flow c).isSome) = pi.filter (fun c => (C.flow c).isSome) := by
  induction h with
  | nil => rfl
  | keep _ c _ _ ih => rw [List.filter_cons, List.filter_cons, ih]
  | ins _ o ho _ _ ih => rw [List.filter_cons_of_neg (by simp [C.own_flow o ho]), ih]

/-- An own cell at the head of `pf` needs the flow state `true`. -/
theorem Expands.head_own {pt : Bool} {pi pf : List β} {o : β} (h : Expands C pt pi (o :: pf))
    (ho : C.own o = true) : pt = true := by
  cases h with
  | keep _ _ hc _ => simp [hc] at ho
  | ins _ _ _ hp _ => exact hp

/-- **Before each own cell the flow state is `true`.** -/
theorem Expands.own_pt {pt : Bool} {pi pf : List β} (h : Expands C pt pi pf) :
    ∀ (a b : List β) (o : β), pf = a ++ o :: b → C.own o = true → C.scan pt a = true := by
  induction h with
  | nil => intro a b o he; simp at he
  | keep pt c hc _ ih =>
    intro a b o he ho
    cases a with
    | nil => cases he; simp [hc] at ho
    | cons x a =>
      cases he
      exact ih a b o rfl ho
  | ins pt o' ho' hp _ ih =>
    intro a b o he ho
    cases a with
    | nil => exact hp
    | cons x a =>
      cases he
      have : C.next pt o' = pt := by simp [Cells.next, ho']
      show C.scan (C.next pt o') a = true
      rw [this]; exact ih a b o rfl ho

/-- **An own cell never follows a cell that falls through** (an instruction
other than `Ins.term`: in particular never a call's return point). -/
theorem Expands.own_not_after_fall {pt : Bool} {pi pf : List β} (h : Expands C pt pi pf)
    (a b : List β) (c o : β) (k : Ins) (he : pf = a ++ c :: o :: b) (hk : C.flow c = some k)
    (hkt : k ≠ .term) : C.own o = false := by
  cases ho : C.own o
  · rfl
  · have hs := h.own_pt (a ++ [c]) b o (by simp [he]) ho
    have hc : C.own c = false := by
      cases hoc : C.own c
      · rfl
      · simp [C.own_flow c hoc] at hk
    rw [Cells.scan_append] at hs
    simp only [Cells.scan, Cells.next, hc, hk] at hs
    cases k <;> first | exact absurd rfl hkt | cases hs

/-- No own cell may enter the segment: the flow state is `false` after each
cell of it but the last. -/
def noBreak (C : Cells β) : Bool → List β → Bool
  | _, [] | _, [_] => true
  | pt, c :: d :: cs => !C.next pt c && noBreak C (C.next pt c) (d :: cs)

/-- A prefix of `pi` no own cell may enter is a prefix of `pf` after own
cells. -/
theorem Expands.seg_prefix {pt : Bool} {pi pf : List β} (h : Expands C pt pi pf) :
    ∀ (s b : List β), pi = s ++ b → noBreak C pt s = true →
      ∃ o b', pf = o ++ s ++ b' ∧ ∀ x ∈ o, C.own x = true := by
  induction h with
  | nil =>
    intro s b he _
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp he.symm
    exact ⟨[], [], rfl, by simp⟩
  | keep pt c hc hr ih =>
    intro s b he hn
    cases s with
    | nil => exact ⟨[], c :: _, rfl, by simp⟩
    | cons x s =>
      cases he
      cases s with
      | nil => exact ⟨[], _, rfl, by simp⟩
      | cons y s =>
        simp only [noBreak, Bool.and_eq_true, Bool.not_eq_true'] at hn
        obtain ⟨o, b', hpf, ho⟩ := ih (y :: s) b rfl hn.2
        cases o with
        | nil => exact ⟨[], b', by simp [hpf], by simp⟩
        | cons z o =>
          rw [hpf] at hr
          have := hr.head_own (ho z (by simp))
          rw [hn.1] at this; cases this
  | ins pt o' ho' _ _ ih =>
    intro s b he hn
    obtain ⟨o, b', hpf, ho⟩ := ih s b he hn
    refine ⟨o' :: o, b', by simp [hpf], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ho'
    · exact ho x hx

/-- **Segments carry over**: a segment of `pi` no own cell may enter (from
the flow state before it) is a contiguous segment of `pf`. -/
theorem Expands.seg {pt : Bool} {pi pf : List β} (h : Expands C pt pi pf) :
    ∀ (a s b : List β), pi = a ++ s ++ b → noBreak C (C.scan pt a) s = true →
      ∃ a' b', pf = a' ++ s ++ b' := by
  induction h with
  | nil =>
    intro a s b he _
    refine ⟨[], [], ?_⟩
    have : a ++ s ++ b = [] := he.symm
    simp_all
  | keep pt c hc hr ih =>
    intro a s b he hn
    cases a with
    | nil =>
      obtain ⟨o, b', hpf, _⟩ := (Expands.keep pt c hc hr).seg_prefix s b (by simpa using he) hn
      exact ⟨o, b', hpf⟩
    | cons x a =>
      cases he
      obtain ⟨a', b', hpf⟩ := ih a s b rfl hn
      exact ⟨c :: a', b', by simp [hpf]⟩
  | ins pt o' ho' hp hr ih =>
    intro a s b he hn
    obtain ⟨a', b', hpf⟩ := ih a s b he hn
    exact ⟨o' :: a', b', by simp [hpf]⟩

/-! ## Tests (toy cells) -/

namespace TestCells

/-- Toy cells: a label, an instruction with its flow, an own cell. -/
inductive T where
  | lab (_ : String)
  | ins (_ : Ins)
  | own (_ : Nat)
  deriving BEq

def TC : Cells T where
  own | .own _ => true | _ => false
  flow | .ins k => some k | _ => none
  label | .lab _ => true | _ => false
  own_flow c h := by cases c <;> simp_all

def pi : List T := [.lab "a", .ins .other, .ins .term, .lab "b", .ins .call, .ins .term]

#guard (erase TC ([.lab "a", .ins .other, .ins .term, .own 0, .own 1, .lab "b", .ins .call, .ins .term, .own 2])
  false).map List.length == some pi.length
-- after a fall-through, after a call, after a label: refused
#guard (erase TC [.ins .other, .own 0] false).isNone
#guard (erase TC [.ins .call, .own 0] true).isNone
#guard (erase TC [.ins .term, .lab "x", .own 0] false).isNone
-- at the start, as the flow state says
#guard (erase TC [.own 0, .lab "a"] true).isSome && (erase TC [.own 0, .lab "a"] false).isNone
-- a block (label, falling-through instructions, a `term`) admits no own cell inside
#guard noBreak TC false [.lab "b", .ins .call, .ins .term]
#guard !noBreak TC false [.ins .term, .lab "b"]

end TestCells

end Scc.Cert.Granule
