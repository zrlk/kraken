/-
**The suspended frames' records**, independent of the ISA: a list of
per-frame records aligned with the source's frame stack `fs`, chained by a
context key, for the static stack invariant of the `Accepted2` levels
(`nodes2_of_starts`' `h1`: each suspended frame resumes from its return
node, in the caller's context its record keeps).

- `StkOkL P up k st fs`: the records `st` and the frames `fs` have the same
  length; the top record `a` (for the top frame `f`, the frames `fs'` below
  it) holds `P k a f fs'` at the running code's key `k`, and the rest are
  chained from `a`'s own key `up a` (the suspended caller's context).
- `stkOkL_cons_iff`, `StkOkL.cons`, `StkOkL.uncons`: a call pushes one
  record for the caller's frame (`a :: st` at `f :: fs`, at the callee's
  key), a return pops it (back at `up a`).
- `StkOkL.length_eq`, `StkOkL.mono`: aligned lengths; a weaker per-frame
  predicate.
- `StkOkB P up Bot k st fs`: the records above some bottom frames, those
  in `Bot` at the last key (`StkOkB.bot`, `.cons`, `.uncons`, `.mono`,
  `stkOkB_of_stkOkL`).

The ISA's records and per-frame facts are `Spike/Lib/LowerA64/Stk2.lean`'s
`StkFr`/`StkFrOk`/`StkOk` (and the x64 twin's).
-/
import WeakCore.TermRun

namespace Spike.Lib

/-- **Records aligned with the frames, chained by a key**: `st` and `fs`
have the same length; the top record `a` with its frame `f` and the frames
`fs'` below `f` in `P` at the key `k`, the rest from `up a`. -/
def StkOkL {α β : Type} (P : β → α → TermRun.Frame → List TermRun.Frame → Prop) (up : α → β) :
    β → List α → List TermRun.Frame → Prop
  | _, [], [] => True
  | k, a :: st, f :: fs => P k a f fs ∧ StkOkL P up (up a) st fs
  | _, _, _ => False

section StkOkL

variable {α β : Type} {P : β → α → TermRun.Frame → List TermRun.Frame → Prop} {up : α → β}

@[simp] theorem stkOkL_nil_nil {k : β} : StkOkL P up k [] [] := trivial

@[simp] theorem stkOkL_cons_iff {k : β} {a : α} {st : List α} {f : TermRun.Frame} {fs : List TermRun.Frame} :
    StkOkL P up k (a :: st) (f :: fs) ↔ P k a f fs ∧ StkOkL P up (up a) st fs := Iff.rfl

@[simp] theorem stkOkL_nil_cons {k : β} {f : TermRun.Frame} {fs : List TermRun.Frame} :
    ¬ StkOkL P up k [] (f :: fs) := fun h => h

@[simp] theorem stkOkL_cons_nil {k : β} {a : α} {st : List α} : ¬ StkOkL P up k (a :: st) [] := fun h => h

/-- No frames, no records. -/
theorem StkOkL.nil {k : β} : StkOkL P up k [] [] := trivial

/-- **A call pushes a record** for the caller's frame `f`, at the callee's
key `k`, the caller's records from the record's own key. -/
theorem StkOkL.cons {k : β} {a : α} {st : List α} {f : TermRun.Frame} {fs : List TermRun.Frame}
    (ha : P k a f fs) (h : StkOkL P up (up a) st fs) : StkOkL P up k (a :: st) (f :: fs) := ⟨ha, h⟩

/-- **A return pops the record**: the top frame's record and the rest at
its key. -/
theorem StkOkL.uncons {k : β} {a : α} {st : List α} {f : TermRun.Frame} {fs : List TermRun.Frame}
    (h : StkOkL P up k (a :: st) (f :: fs)) : P k a f fs ∧ StkOkL P up (up a) st fs := h

/-- The records and the frames have the same length. -/
theorem StkOkL.length_eq : ∀ {k : β} {st : List α} {fs : List TermRun.Frame},
    StkOkL P up k st fs → st.length = fs.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, h => congrArg (· + 1) (StkOkL.length_eq h.2)
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

/-- A weaker per-frame predicate. -/
theorem StkOkL.mono {Q : β → α → TermRun.Frame → List TermRun.Frame → Prop}
    (hPQ : ∀ k a f fs, P k a f fs → Q k a f fs) :
    ∀ {k : β} {st : List α} {fs : List TermRun.Frame}, StkOkL P up k st fs → StkOkL Q up k st fs
  | _, [], [], _ => trivial
  | _, _ :: _, _ :: _, h => ⟨hPQ _ _ _ _ h.1, StkOkL.mono hPQ h.2⟩
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

end StkOkL

/-! ## Records above some bottom frames -/

/-- **Records above some bottom frames**: `StkOkL` whose record list may
end above frames not run by a recorded caller (e.g. the runtime's setup
wrapper's frame below a callee), those bottom frames `fs` at the last key
`k` in `Bot k fs`. -/
def StkOkB {α β : Type} (P : β → α → TermRun.Frame → List TermRun.Frame → Prop) (up : α → β)
    (Bot : β → List TermRun.Frame → Prop) : β → List α → List TermRun.Frame → Prop
  | k, [], fs => Bot k fs
  | k, a :: st, f :: fs => P k a f fs ∧ StkOkB P up Bot (up a) st fs
  | _, _ :: _, [] => False

section StkOkB

variable {α β : Type} {P : β → α → TermRun.Frame → List TermRun.Frame → Prop} {up : α → β}
  {Bot : β → List TermRun.Frame → Prop}

@[simp] theorem stkOkB_nil {k : β} {fs : List TermRun.Frame} : StkOkB P up Bot k [] fs ↔ Bot k fs := by
  cases fs <;> exact Iff.rfl

@[simp] theorem stkOkB_cons_iff {k : β} {a : α} {st : List α} {f : TermRun.Frame} {fs : List TermRun.Frame} :
    StkOkB P up Bot k (a :: st) (f :: fs) ↔ P k a f fs ∧ StkOkB P up Bot (up a) st fs := Iff.rfl

@[simp] theorem stkOkB_cons_nil {k : β} {a : α} {st : List α} : ¬ StkOkB P up Bot k (a :: st) [] :=
  fun h => h

/-- **No records**: the bottom frames at the key. -/
theorem StkOkB.bot {k : β} {fs : List TermRun.Frame} (h : Bot k fs) : StkOkB P up Bot k [] fs :=
  stkOkB_nil.mpr h

/-- **A call pushes a record** (`StkOkL.cons` above the bottom frames). -/
theorem StkOkB.cons {k : β} {a : α} {st : List α} {f : TermRun.Frame} {fs : List TermRun.Frame}
    (ha : P k a f fs) (h : StkOkB P up Bot (up a) st fs) : StkOkB P up Bot k (a :: st) (f :: fs) := ⟨ha, h⟩

/-- **A return pops the record** (`StkOkL.uncons` above the bottom frames). -/
theorem StkOkB.uncons {k : β} {a : α} {st : List α} {f : TermRun.Frame} {fs : List TermRun.Frame}
    (h : StkOkB P up Bot k (a :: st) (f :: fs)) : P k a f fs ∧ StkOkB P up Bot (up a) st fs := h

/-- A weaker per-frame predicate and a weaker bottom. -/
theorem StkOkB.mono {Q : β → α → TermRun.Frame → List TermRun.Frame → Prop}
    {Bot' : β → List TermRun.Frame → Prop}
    (hPQ : ∀ k a f fs, P k a f fs → Q k a f fs) (hB : ∀ k fs, Bot k fs → Bot' k fs) :
    ∀ {k : β} {st : List α} {fs : List TermRun.Frame}, StkOkB P up Bot k st fs → StkOkB Q up Bot' k st fs
  | _, [], _, h => StkOkB.bot (hB _ _ (stkOkB_nil.mp h))
  | _, _ :: _, _ :: _, h => ⟨hPQ _ _ _ _ h.1, StkOkB.mono hPQ hB h.2⟩
  | _, _ :: _, [], h => h.elim

/-- **`StkOkL` is `StkOkB` at no bottom frames.** -/
theorem stkOkB_of_stkOkL :
    ∀ {k : β} {st : List α} {fs : List TermRun.Frame}, StkOkL P up k st fs →
      StkOkB P up (fun _ fs => fs = []) k st fs
  | _, [], [], _ => StkOkB.bot rfl
  | _, _ :: _, _ :: _, h => ⟨h.1, stkOkB_of_stkOkL h.2⟩
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

end StkOkB

end Spike.Lib

/-- info: 'Spike.Lib.StkOkL.length_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.StkOkL.length_eq

/-- info: 'Spike.Lib.StkOkL.mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.StkOkL.mono

/-- info: 'Spike.Lib.StkOkB.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.StkOkB.mono

/-- info: 'Spike.Lib.stkOkB_of_stkOkL' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.stkOkB_of_stkOkL
