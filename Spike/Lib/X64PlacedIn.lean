/-
**Every frame placed in kept stack cells** (x86-64, the write abort's
stub): `PlacedS` (`Spike/Lib/X64ConsumerS.lean`) with every place of every
frame's words a stack slot in `A` (immediates allowed: they have no
place), so that a run keeping the private memory on `A` keeps the whole
placement. The stub's footprint lemma: the write abort's stub and
`scc_rt_abort` write only scratch registers and their own frames below the
caller's, and `scc` spills every live word to its frame's slots, so
`PlacedS` at the call into the stub gives `PlacedS` at every stub state.

- `PlacesIn A wp`: every place of `wp` a slot of `A`.
- `PlacedSIn`: `PlacedS` with every place in `A`; `.toPlacedS`, `.of_eq`
  (kept by a state whose private memory agrees on `A`).
- `KeptA R kb lo' hi'`: the slots of `R`'s cells outside the callee's
  region at `kb` (`CKept`'s cells); `PlacedSIn.of_cKept`: kept across
  `CKept`.
-/
import Spike.Lib.X64PlacedS
import Spike.Lib.X64Call

namespace Spike.Lib.X64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.X64Consumer
open Spike.Lib (Region)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s s' : State} {c : Ctl} {fs : List TermRun.Frame}

/-- **Every place of a word place a slot of `A`** (an immediate has none). -/
def PlacesIn (A : Nat → Prop) (wp : WordPlace (machine (kernel 1)).I.RegId) : Prop :=
  ∀ pl ∈ wp.places, ∃ a, pl = .slot a ∧ A a

/-- **Every frame placed, every place a slot of `A`**: `PlacedS`'s clauses
at one witness whose places are all slots of `A`. -/
def PlacedSIn (Λ : Scc.Sem.Layout) (lbl : Lbl) (s : State) (c : Ctl) (fs : List TermRun.Frame) (A : Nat → Prop) :
    Prop :=
  ∃ envm : Nat → String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId),
    (∀ d env, (envsOf c fs)[d]? = some env → ∀ x ty ws, TermRun.lookupE env x = some (ty, ws) →
      ∀ k wd wp, ws[k]? = some wd → envm d x k = some wp → WordPlaceRep (machine (kernel 1)) lbl s wp wd.val) ∧
    (∀ d env xs, (envsOf c fs)[d]? = some env → (fvOf c fs)[d]? = some xs → ∀ x ∈ xs, ∀ ty ws,
      TermRun.lookupE env x = some (ty, ws) → ∀ k < ws.length, ∃ pl, envm d x k = some pl) ∧
    (∀ d e x k n, (termsOf c fs)[d]? = some e → envm d x k = some (.imm n) → Λ.imms e x k = some n) ∧
    (∀ d x k wp, envm d x k = some wp → PlacesIn A wp)

/-- **Placed in `A` is placed.** -/
theorem PlacedSIn.toPlacedS {A : Nat → Prop} (h : PlacedSIn Λ lbl s c fs A) : PlacedS Λ lbl s c fs :=
  let ⟨envm, hrep, htot, himm, _⟩ := h
  ⟨envm, hrep, htot, himm⟩

/-- A word whose places are slots of `A` is represented alike in two states
whose private memory agrees on `A`. -/
theorem wordPlaceRep_of_placesIn {A : Nat → Prop}
    (hA : ∀ a, A a → (machine (kernel 1)).privLoad s' (BitVec.ofNat 64 a) =
      (machine (kernel 1)).privLoad s (BitVec.ofNat 64 a))
    {wp : WordPlace (machine (kernel 1)).I.RegId} (hwp : PlacesIn A wp) {v : WeakMem.Val}
    (h : WordPlaceRep (machine (kernel 1)) lbl s wp v) : WordPlaceRep (machine (kernel 1)) lbl s' wp v := by
  have hpv : ∀ pl ∈ wp.places, placeVal (machine (kernel 1)) s' pl = placeVal (machine (kernel 1)) s pl := by
    intro pl hm
    obtain ⟨a, rfl, ha⟩ := hwp pl hm
    simp only [placeVal, hA a ha]
  match wp, hpv, h with
  | .one pl, hpv, ⟨w, hw, hr⟩ => exact ⟨w, by rw [hpv pl (by simp [WordPlace.places]), hw], hr⟩
  | .loc pb (.at po), hpv, ⟨vb, vo, hb, ho, hr⟩ =>
    refine ⟨vb, vo, by rw [hpv pb (by simp [WordPlace.places]), hb], ?_, hr⟩
    show placeVal _ _ po = _
    rw [hpv po (by simp [WordPlace.places])]; exact ho
  | .loc pb (.imm n), hpv, ⟨vb, vo, hb, ho, hr⟩ =>
    exact ⟨vb, vo, by rw [hpv pb (by simp [WordPlace.places]), hb], ho, hr⟩
  | .imm n, _, h => exact h

/-- **Placed in `A` is kept** by a state whose private memory agrees on `A`
(a callee's run keeping the caller's cells). -/
theorem PlacedSIn.of_eq {A : Nat → Prop} (h : PlacedSIn Λ lbl s c fs A)
    (hA : ∀ a, A a → (machine (kernel 1)).privLoad s' (BitVec.ofNat 64 a) =
      (machine (kernel 1)).privLoad s (BitVec.ofNat 64 a)) :
    PlacedSIn Λ lbl s' c fs A :=
  let ⟨envm, hrep, htot, himm, hin⟩ := h
  ⟨envm, fun d env hd x ty ws hx k wd wp hwd hwp =>
    wordPlaceRep_of_placesIn hA (hin d x k wp hwp) (hrep d env hd x ty ws hx k wd wp hwd hwp), htot, himm, hin⟩

/-- **The slots of `R`'s cells outside the callee's region** at `kb` from
`lo'` to `hi'`: the cells `CKept` keeps. -/
def KeptA (R : Region) (kb lo' hi' : Int) (a : Nat) : Prop :=
  ∃ k, R.Off k ∧ ¬ (R.callee kb lo' hi').Off (k - kb) ∧ a = (R.addr k).toNat

/-- **Placed in the kept cells is kept across `CKept`**: a state whose
memory keeps `R`'s cells outside the callee's region (`CKept`) keeps every
frame placed in them. -/
theorem PlacedSIn.of_cKept {R : Region} {kb lo' hi' : Int} (h : PlacedSIn Λ lbl s c fs (KeptA R kb lo' hi'))
    (hk : Spike.Lib.X64.CKept R kb lo' hi' s.st.1 s'.st.1) : PlacedSIn Λ lbl s' c fs (KeptA R kb lo' hi') :=
  h.of_eq fun a ⟨k, hko, hkc, ha⟩ => by
    subst ha
    show privLoad s' _ = privLoad s _
    simp only [privLoad, BitVec.ofNat_toNat, BitVec.setWidth_eq, hk k hko hkc]

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.X64ConsumerS.PlacedSIn.of_cKept' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PlacedSIn.of_cKept

end Spike.Lib.X64ConsumerS
