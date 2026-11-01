/-
**hello.w's child controls placed** (the shared base; the twin of
`Wake.PlacedZ`'s environments): every control the spawned child's run pins binds its variables to sub-lists of
the packet's five words `w0 .. w4` (`a` all five, `sl`/`sl0` the slice's three, `slc` four, `c` the flag's `w3`,
`j` the `ThreadId` `w4`; `u`, `d`, `w` none). One place map, `envPk P A`, sends the packet word `i` to the place
`P i` where `A i` (the words available at the node); a control is `Placed` once each available word is
represented at its place and the control reads only available words.

- `pos`: a variable's word `k` as a packet index; `pk`: the packet's words.
- `envPk P A`: the place map; `placed_pk`: `Placed` by it, given the environment agrees with `pos` (`henv`),
  the read words available (`htot`), and the available words represented (`hrep`).
- `placed_kidH`, `placed_wcP`, `placed_wcR`, `placed_cS1`, `placed_cS2`: the child's controls (`kidH`'s and
  `wcP`'s read all five words; `wcR`'s `c`, `j`; `cS1`'s `j`; `cS2`'s none).
- `placedSE_nil`: `Placed` at no frame is `PlacedSE`; `placedSE_prW`: a `print` control (`PrW`) on placed frames
  (`PlacedSE.of_ext` at `PrW.ext`).
- `PkRep`: the representation premise at one place map; `wv`, `pkRep_of`: from `zObl_placed`'s premises
  (packet word `i` is the machine word `wv w i`: `w.w0`, `w.w2 .. w.w5`), given the places' values.
-/
import Spike.Lib.A64HelloWorkerSegR
import Spike.Lib.A64PlacedSE
import Spike.Lib.A64WakeMainW

namespace Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Place WordPlace placeVal ValRep exprFv opVars opAts atVars externModelTerms)
open Spike.Lib (Ctl)
open Spike.Lib.HelloSplit (wcP wcR envP workerCallH workerRestH)
open Spike.Lib.HelloWorkerCallSrc (PrW)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (kidH cS1 cS2)
open Spike.Lib.A64WakeMainW (M1)
open Spike.Lib.A64Consumer (Placed Lbl)
open Spike.Lib.A64ConsumerS (PlacedS FramesPlaced FramesPlacedIn PlacedSE)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {P : Nat → Place M1.I.RegId}

/-! ## The packet's place map -/

/-- **A variable's word as a packet index**: `a`'s `k < 5`, `sl`'s and `sl0`'s `k < 3`, `slc`'s `k < 4` at `k`;
`c`'s word at `3`, `j`'s at `4`. -/
def pos (x : String) (k : Nat) : Option Nat :=
  if x = "a" ∧ k < 5 then some k else if (x = "sl" ∨ x = "sl0") ∧ k < 3 then some k
  else if x = "slc" ∧ k < 4 then some k else if x = "c" ∧ k = 0 then some 3
  else if x = "j" ∧ k = 0 then some 4 else none

/-- The packet's words. -/
abbrev pk (w0 w1 w2 w3 w4 : TermRun.Word) : List TermRun.Word := [w0, w1, w2, w3, w4]

/-- **The packet's place map**: a variable's word at packet index `i` placed at `P i` where `A i`. -/
def envPk (P : Nat → Place M1.I.RegId) (A : Nat → Prop) [DecidablePred A] :
    String → Nat → Option (WordPlace M1.I.RegId) :=
  fun x k => match pos x k with
    | some i => if A i then some (.one (P i)) else none
    | none => none

/-- **The available packet words represented at their places** (`A i`: word `i` at `P i`). -/
def PkRep (lbl : Lbl) (s : State) (P : Nat → Place M1.I.RegId) (A : Nat → Prop) (w0 w1 w2 w3 w4 : TermRun.Word) :
    Prop :=
  ∀ i wd, A i → (pk w0 w1 w2 w3 w4)[i]? = some wd → ∃ v, placeVal M1 s (P i) = some v ∧ ValRep lbl wd.val v

/-- **A control placed by the packet's map**: its environment's words at `pos`'s packet indices (`henv`), its
read words available (`htot`), the available words represented (`hrep`). -/
theorem placed_pk {c : Ctl} {P : Nat → Place M1.I.RegId} {A : Nat → Prop} [DecidablePred A]
    {w0 w1 w2 w3 w4 : TermRun.Word}
    (henv : ∀ x ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k wd, ws[k]? = some wd →
      ∃ i, pos x k = some i ∧ (pk w0 w1 w2 w3 w4)[i]? = some wd)
    (htot : ∀ x ∈ exprFv c.term, ∀ ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k < ws.length,
      ∃ i, pos x k = some i ∧ A i)
    (hrep : PkRep lbl s P A w0 w1 w2 w3 w4) : Placed Λ lbl s c := by
  refine ⟨envPk P A, ?_, ?_, ?_⟩
  · intro x ty ws hl k wd wp hwd hwp
    obtain ⟨i, hi, hpk⟩ := henv x ty ws hl k wd hwd
    simp only [envPk, hi] at hwp
    split at hwp
    · cases hwp; exact hrep i wd ‹_› hpk
    · cases hwp
  · intro x hx ty ws hl k hk
    obtain ⟨i, hi, hA⟩ := htot x hx ty ws hl k hk
    exact ⟨.one (P i), by simp [envPk, hi, hA]⟩
  · intro x k n h
    simp only [envPk] at h
    split at h
    · split at h <;> cases h
    · cases h

/-- **The packet word `i`'s machine word**: the buffer's locative in `w.w0` (its offset word `w.w1`, `0`, is no
packet word), the slice's other two in `w.w2`, `w.w3`, the flag's in `w.w4`, the `ThreadId` in `w.w5`. -/
def wv (w : Child.Words) : Nat → BitVec 64
  | 0 => w.w0 | 1 => w.w2 | 2 => w.w3 | 3 => w.w4 | _ => w.w5

/-- **`PkRep` from the five words' representations** (`zObl_placed`'s premises) and each available place's
value the packet word's machine word. -/
theorem pkRep_of {w : Child.Words} {A : Nat → Prop} {w0 w1 w2 w3 w4 : TermRun.Word}
    (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat) (hv2 : ValRep lbl w2.val w.w3.toNat)
    (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat)
    (hP : ∀ i, A i → placeVal M1 s (P i) = some (wv w i).toNat) : PkRep lbl s P A w0 w1 w2 w3 w4 := by
  intro i wd hA hwd
  refine ⟨_, hP i hA, ?_⟩
  rcases i with _ | _ | _ | _ | _ | i <;> simp at hwd <;> subst hwd <;>
    first | exact hv0 | exact hv1 | exact hv2 | exact hv | exact hvu

/-! ## The child's controls -/

variable {w0 w1 w2 w3 w4 : TermRun.Word} {P : Nat → Place M1.I.RegId}

/-- A packet index witness `⟨i, pos x k = some i, rfl⟩` at `i < 5`. -/
local macro "pk_idx" : tactic => `(tactic| first
  | exact ⟨0, by simp [pos], rfl⟩
  | exact ⟨1, by simp [pos], rfl⟩
  | exact ⟨2, by simp [pos], rfl⟩
  | exact ⟨3, by simp [pos], rfl⟩
  | exact ⟨4, by simp [pos], rfl⟩)

private theorem beq_ne {y x : String} (h : y ≠ x) : (y == x) = false := by simp [h]

/-- `envP`'s words at `pos`'s indices. -/
theorem envP_pos : ∀ x ty ws, TermRun.lookupE (envP w0 w1 w2 w3 w4) x = some (ty, ws) → ∀ k wd, ws[k]? = some wd →
    ∃ i, pos x k = some i ∧ (pk w0 w1 w2 w3 w4)[i]? = some wd := by
  intro x ty ws hl k wd hwd
  simp only [envP, TermRun.lookupE, List.find?] at hl
  by_cases e1 : x = "sl"
  · subst e1; simp at hl; obtain ⟨-, rfl⟩ := hl
    rcases k with _ | _ | _ | k <;> simp at hwd <;> subst hwd <;> pk_idx
  by_cases e2 : x = "c"
  · subst e2; simp at hl; obtain ⟨-, rfl⟩ := hl
    rcases k with _ | k <;> simp at hwd; subst hwd; exact ⟨3, by simp [pos], rfl⟩
  by_cases e3 : x = "sl0"
  · subst e3; simp at hl; obtain ⟨-, rfl⟩ := hl
    rcases k with _ | _ | _ | k <;> simp at hwd <;> subst hwd <;> pk_idx
  by_cases e4 : x = "j"
  · subst e4; simp at hl; obtain ⟨-, rfl⟩ := hl
    rcases k with _ | k <;> simp at hwd; subst hwd; exact ⟨4, by simp [pos], rfl⟩
  by_cases e5 : x = "slc"
  · subst e5; simp at hl; obtain ⟨-, rfl⟩ := hl
    rcases k with _ | _ | _ | _ | k <;> simp at hwd <;> subst hwd <;> pk_idx
  by_cases e6 : x = "a"
  · subst e6; simp at hl; obtain ⟨-, rfl⟩ := hl
    rcases k with _ | _ | _ | _ | _ | k <;> simp at hwd <;> subst hwd <;> pk_idx
  simp [beq_ne (Ne.symm e1), beq_ne (Ne.symm e2), beq_ne (Ne.symm e3), beq_ne (Ne.symm e4), beq_ne (Ne.symm e5),
    beq_ne (Ne.symm e6)] at hl

/-- **`kidH` placed** (reads `a`, all five words). -/
theorem placed_kidH (T : Ty) {A : Nat → Prop} [DecidablePred A] (hA : ∀ i < 5, A i)
    (hrep : PkRep lbl s P A w0 w1 w2 w3 w4) : Placed Λ lbl s (kidH T w0 w1 w2 w3 w4) := by
  refine placed_pk (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) ?_ ?_ hrep
  · intro x ty ws hl k wd hwd
    simp only [kidH, TermRun.lookupE, List.find?] at hl
    by_cases e : x = "a"
    · subst e; simp at hl; obtain ⟨-, rfl⟩ := hl
      rcases k with _ | _ | _ | _ | _ | k <;> simp at hwd <;> subst hwd <;> pk_idx
    · simp [beq_ne (Ne.symm e)] at hl
  · intro x hx ty ws hl k hk
    have e : x = "a" := by simpa [kidH, exprFv, atVars] using hx
    subst e
    simp [kidH, TermRun.lookupE] at hl
    obtain ⟨-, rfl⟩ := hl
    simp at hk
    exact ⟨k, by simp [pos, hk], hA k hk⟩

/-- **`wcP` placed** (reads `sl`, `c`, `j`: all five words). -/
theorem placed_wcP {A : Nat → Prop} [DecidablePred A] (hA : ∀ i < 5, A i)
    (hrep : PkRep lbl s P A w0 w1 w2 w3 w4) : Placed Λ lbl s (wcP w0 w1 w2 w3 w4) := by
  refine placed_pk envP_pos ?_ hrep
  intro x hx ty ws hl k hk
  obtain ⟨i, hi, hpk⟩ := envP_pos x ty ws hl k _ (List.getElem?_eq_getElem hk)
  exact ⟨i, hi, hA i (by have := (List.getElem?_eq_some_iff.1 hpk).1; simpa using this)⟩

/-- **`wcR` placed** (reads `c`, `j`: words `3`, `4`). -/
theorem placed_wcR {A : Nat → Prop} [DecidablePred A] (h3 : A 3) (h4 : A 4)
    (hrep : PkRep lbl s P A w0 w1 w2 w3 w4) : Placed Λ lbl s (wcR w0 w1 w2 w3 w4) := by
  refine placed_pk (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) ?_ ?_ hrep
  · intro x ty ws hl k wd hwd
    by_cases e : x = "u"
    · subst e; simp [wcR, TermRun.lookupE] at hl; obtain ⟨-, rfl⟩ := hl; simp at hwd
    · exact envP_pos x ty ws (by simpa [wcR, TermRun.lookupE, List.find?, beq_ne (Ne.symm e)] using hl) k wd hwd
  · intro x hx ty ws hl k hk
    have e : x = "c" ∨ x = "j" := by
      simpa [wcR, workerRestH, exprFv, opVars, opAts, atVars] using hx
    rcases e with rfl | rfl
    · simp [wcR, envP, TermRun.lookupE] at hl; obtain ⟨-, rfl⟩ := hl
      obtain rfl : k = 0 := by simpa using hk
      exact ⟨3, by simp [pos], h3⟩
    · simp [wcR, envP, TermRun.lookupE] at hl; obtain ⟨-, rfl⟩ := hl
      obtain rfl : k = 0 := by simpa using hk
      exact ⟨4, by simp [pos], h4⟩

/-- **`cS1` placed** (reads `j`: word `4`). -/
theorem placed_cS1 {A : Nat → Prop} [DecidablePred A] (h4 : A 4)
    (hrep : PkRep lbl s P A w0 w1 w2 w3 w4) : Placed Λ lbl s (cS1 w0 w1 w2 w3 w4) := by
  refine placed_pk (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) ?_ ?_ hrep
  · intro x ty ws hl k wd hwd
    by_cases e : x = "d"
    · subst e; simp [cS1, TermRun.lookupE] at hl; obtain ⟨-, rfl⟩ := hl; simp at hwd
    by_cases e' : x = "u"
    · subst e'; simp [cS1, wcR, TermRun.lookupE] at hl; obtain ⟨-, rfl⟩ := hl; simp at hwd
    · have hl' : TermRun.lookupE (envP w0 w1 w2 w3 w4) x = some (ty, ws) := by
        simpa [cS1, wcR, TermRun.lookupE, List.find?, beq_ne (Ne.symm e), beq_ne (Ne.symm e')] using hl
      exact envP_pos x ty ws hl' k wd hwd
  · intro x hx ty ws hl k hk
    have e : x = "j" := by simpa [cS1, exprFv, opVars, opAts, atVars] using hx
    subst e
    simp [cS1, wcR, envP, TermRun.lookupE] at hl; obtain ⟨-, rfl⟩ := hl
    obtain rfl : k = 0 := by simpa using hk
    exact ⟨4, by simp [pos], h4⟩

/-- **`cS2` placed** (reads nothing). -/
theorem placed_cS2 : Placed Λ lbl s (cS2 w0 w1 w2 w3 w4) :=
  ⟨fun _ _ => none, fun _ _ _ _ _ _ _ _ h => (by cases h), fun _ hy => (by simp [cS2, exprFv, atVars] at hy),
    fun _ _ _ h => (by cases h)⟩

/-! ## `PlacedSE` -/

/-- **`Placed` at no frame is `PlacedSE`.** -/
theorem placedSE_nil {c : Ctl} (h : Placed Λ lbl s c) : PlacedSE Λ lbl s c [] :=
  .inl (PlacedS.ofFrames h (FramesPlacedIn.nil (fun _ => False)).toFramesPlaced)

/-- **A `print` control on placed frames is `PlacedSE`** (`PrW.ext`: a model term or closed). -/
theorem placedSE_prW {pw wn : TermRun.Word} {n m k : Nat} {c : Ctl} {fs : List TermRun.Frame}
    (h : PrW pw wn n m k c) (hf : FramesPlaced Λ lbl s fs) : PlacedSE Λ lbl s c fs :=
  PlacedSE.of_ext h.ext hf

end Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.placed_pk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.placed_pk

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.placed_kidH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.placed_kidH

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.placed_wcP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.placed_wcP

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.placed_wcR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.placed_wcR

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.placed_cS1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.placed_cS1

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.pkRep_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.pkRep_of
