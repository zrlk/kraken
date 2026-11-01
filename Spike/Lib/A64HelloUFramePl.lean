/-
**hello's worker frame placed at `print`'s call** (AArch64; row 5j-wit-W, class 3 part 1): the caller's frame
`⟨"u", workerRestH, env, [], .unit⟩` that `print`'s states suspend is placed in `wc_worker`'s frame slots of `c`
(cell `-64`) and `j` (cell `-56`), at the call node (`Body.wCall`, `sp` at `-96`). The worker's segment invariant
carries this placement at the call's pairs; `print`'s states keep the two slots (the call gate's frame condition),
so `FramesPlacedInI.of_eq` moves it to them and `PlacedSE.of_ext` places them.

- `wkSlots s`: the two slots at `s`'s `sp + 32`, `sp + 40`; `wkSlots_addr`: at a state of the call node (`sp` at
  `-96`) they are the region's cells `-64`, `-56`.
- `UPlH Λ lbl s env`: the frame placed in `wkSlots s`.
- `envmU`, `placeVal_cell`: the place map (`c`, `j` at the two cells) and a cell's word at an `Abs` state.
- `uPlH_of`: `UPlH` at the call node's states from the two cells' words representing `c`'s and `j`'s.
-/
import Spike.Lib.A64PlacedFr
import Spike.Lib.HelloSplit
import Spike.Lib.A64Flow

namespace Spike.Lib.A64.HelloPh.UFramePl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.HelloSplit (workerRestH envP)

/-- **`wc_worker`'s slots of `c` and `j`** at a state whose `sp` is the call node's: `sp + 32` (cell `-64`) and
`sp + 40` (cell `-56`). -/
def wkSlots (s : State) (a : Nat) : Prop :=
  a = (s.st.1.regs.SP.toBitVec + 32#64).toNat ∨ a = (s.st.1.regs.SP.toBitVec + 40#64).toNat

/-- **`print`'s caller frame placed in `wc_worker`'s slots** at `s`. -/
def UPlH (Λ : Scc.Sem.Layout) (lbl : Lbl) (s : State) (env : TermRun.Env) : Prop :=
  FramesPlacedInI Λ lbl s [⟨"u", workerRestH, env, [], .unit⟩] (wkSlots s)

/-- **At the call node the slots are the region's cells `-64`, `-56`.** -/
theorem wkSlots_addr {R : Region} {rs : List (XReg × Int)} {s : State}
    {σ : Spike.Lib.A64.Flow.AS} (hA : Spike.Lib.A64.Flow.Abs R ⟨-96, rs⟩ s.st.1 σ) (a : Nat) :
    wkSlots s a ↔ a = (R.addr (-64)).toNat ∨ a = (R.addr (-56)).toNat := by
  have hsp : s.st.1.regs.SP.toBitVec = R.addr (-96) := by
    have := hA.so .SP _ rfl
    rw [← hA.regs] at this
    exact this
  have h64 : R.addr (-64) = R.addr (-96) + 32#64 := by
    rw [show (-64 : Int) = -96 + 32 by omega, Region.addr_add]; rfl
  have h56 : R.addr (-56) = R.addr (-96) + 40#64 := by
    rw [show (-56 : Int) = -96 + 40 by omega, Region.addr_add]; rfl
  simp only [wkSlots, hsp, h64, h56]

/-- The place map: `c` at cell `-64`, `j` at cell `-56` of the current frame. -/
def envmU (R : Region) : Nat → String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId) := fun d y k =>
  if d = 0 ∧ k = 0 then
    if y = "c" then some (.one (.slot (R.addr (-64)).toNat))
    else if y = "j" then some (.one (.slot (R.addr (-56)).toNat)) else none
  else none

/-- A region cell's word as the private load of its slot. -/
theorem placeVal_cell {R : Region} {rs : List (XReg × Int)} {s : State} {σ : Spike.Lib.A64.Flow.AS}
    (hA : Spike.Lib.A64.Flow.Abs R ⟨-96, rs⟩ s.st.1 σ) {k : Int} (hk : R.Off k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σ.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  show ((s.st.1.dmem.loadInt (BitVec.ofNat 64 (R.addr k).toNat) 8).map (BitVec.ofInt 64)).map (·.toNat) = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hj]
  simp [hv]

/-- **`print`'s caller frame placed at the call node**: at a state of `Abs R ⟨-96, _⟩` (the region holding the
cells `-64`, `-56`), the frame in `envP`'s environment is placed in `wc_worker`'s slots when the two cells' words
represent `c`'s word `w3` and `j`'s word `w4`. -/
theorem uPlH_of {Λ : Scc.Sem.Layout} {lbl : Lbl} {R : Region} (hlo : R.lo ≤ -64) (hhi : -48 ≤ R.hi)
    {rs : List (XReg × Int)} {s : State} {σ : Spike.Lib.A64.Flow.AS}
    (hA : Spike.Lib.A64.Flow.Abs R ⟨-96, rs⟩ s.st.1 σ) {w0 w1 w2 w3 w4 : TermRun.Word}
    (h3 : ValRep lbl w3.val (σ.slot (-64)).toNat) (h4 : ValRep lbl w4.val (σ.slot (-56)).toNat) :
    UPlH Λ lbl s (envP w0 w1 w2 w3 w4) := by
  have o64 : R.Off (-64) := ⟨by decide, hlo, by omega⟩
  have o56 : R.Off (-56) := ⟨by decide, by omega, by omega⟩
  refine ⟨envmU R, ?_, ?_, ?_, ?_⟩
  · intro d f hf y ty ws hy k wd wp hwd hwp
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      simp only [envmU, true_and] at hwp
      by_cases hk : k = 0
      · subst hk
        by_cases hc : y = "c"
        · subst hc
          simp only [ite_true, Option.some.injEq] at hwp
          subst hwp
          simp only [envP, TermRun.lookupE] at hy
          simp at hy
          obtain ⟨-, rfl⟩ := hy
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hwd
          subst hwd
          exact ⟨_, placeVal_cell hA o64, h3⟩
        · by_cases hj : y = "j"
          · subst hj
            simp only [ite_true, Option.some.injEq, show ("j" : String) ≠ "c" by decide, ite_false] at hwp
            subst hwp
            simp only [envP, TermRun.lookupE] at hy
            simp at hy
            obtain ⟨-, rfl⟩ := hy
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hwd
            subst hwd
            exact ⟨_, placeVal_cell hA o56, h4⟩
          · simp [hc, hj] at hwp
      · simp [hk] at hwp
    · simp at hf
  · intro d f hf y hy ty ws hl k hk
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      have e : (exprFv workerRestH).filter (· != "u") = ["c", "j"] := rfl
      rw [e] at hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · simp [envP, TermRun.lookupE] at hl
        obtain ⟨-, rfl⟩ := hl
        obtain rfl : k = 0 := by simpa using hk
        exact ⟨.one (.slot (R.addr (-64)).toNat), by simp [envmU]⟩
      · simp [envP, TermRun.lookupE] at hl
        obtain ⟨-, rfl⟩ := hl
        obtain rfl : k = 0 := by simpa using hk
        exact ⟨.one (.slot (R.addr (-56)).toNat), by simp [envmU]⟩
    · simp at hf
  · intro d y k wp hwp pl hpl
    simp only [envmU] at hwp
    by_cases h1 : d = 0 ∧ k = 0
    · by_cases hc : y = "c"
      · simp only [h1, hc, and_self, ite_true, Option.some.injEq] at hwp
        subst hwp
        simp only [WordPlace.places, List.mem_singleton] at hpl
        exact ⟨_, hpl, (wkSlots_addr hA _).2 (.inl rfl)⟩
      · by_cases hj : y = "j"
        · simp only [h1, hj, and_self, ite_true, Option.some.injEq, show ("j" : String) ≠ "c" by decide,
            ite_false] at hwp
          subst hwp
          simp only [WordPlace.places, List.mem_singleton] at hpl
          exact ⟨_, hpl, (wkSlots_addr hA _).2 (.inr rfl)⟩
        · simp [h1, hc, hj] at hwp
    · simp [h1] at hwp
  · intro d f y k n _ hwp
    simp only [envmU] at hwp
    by_cases h1 : d = 0 ∧ k = 0
    · by_cases hc : y = "c"
      · simp [h1, hc] at hwp
      · by_cases hj : y = "j"
        · simp [h1, hj] at hwp
        · simp [h1, hc, hj] at hwp
    · simp [h1] at hwp

end Spike.Lib.A64.HelloPh.UFramePl

/-- info: 'Spike.Lib.A64.HelloPh.UFramePl.uPlH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.UFramePl.uPlH_of
