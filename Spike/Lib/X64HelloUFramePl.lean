/-
**hello's worker frame placed at `print`'s call** (x86-64; the twin of `Spike/Lib/A64HelloUFramePl.lean`): the
caller's frame `⟨"u", workerRestH, env, [], .unit⟩` that `print`'s states suspend is placed in `wc_worker`'s frame
slots of `c` (cell `-48`, `-40(%rbp)`) and `j` (cell `-56`, `-48(%rbp)`), at the call state (the return address
pushed, `%rsp` at `-96`). The worker's segment invariant carries this placement at the call's pairs; `print`'s
states keep the two slots (the call gate's frame condition, `X64HelloUFrameKeep`), so the placement moves to them.

- `wkSlots_addr`: at a state of the call node (`%rsp` at `-96`) the slots `UFrameKeep.WkSlotsK` are the region's
  cells `-56`, `-48`.
- `UPlH Λ lbl s env`: the frame placed in `WkSlotsK s`.
- `envmU`, `placeVal_cell`: the place map (`c`, `j` at the two cells) and a cell's word at an `Abs` state.
- `uPlH_of`: `UPlH` at the call node's states from the two cells' words representing `c`'s and `j`'s.

Unlike AArch64 (slots `sp + 32`, `sp + 40`, cells `-64`, `-56`, `sp` at `-96` with no return address on the
stack), the call state's `%rsp` is below the pushed return address and the slots are `%rsp + 40` (`j`) and
`%rsp + 48` (`c`), cells `-56`, `-48` with `%rbp` at `-8`; `%rsp` is `regs.get64 .rsp`, equal to `R.addr (-96)` by
`Abs`'s `so` at `.rsp`; the slots are the shared `UFrameKeep.WkSlotsK` (AArch64 defines its own `wkSlots`).
-/
import Spike.Lib.X64PlacedFr
import Spike.Lib.X64HelloSplit
import Spike.Lib.X64HelloUFrameKeep
import Spike.Lib.X64Block

namespace Spike.Lib.X64.HelloPh.UFramePl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib (Region)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64HelloSplit (workerRestH envP)
open Spike.Lib.X64.HelloPh.UFrameKeep (WkSlotsK)

/-- **`print`'s caller frame placed in `wc_worker`'s slots** at `s`. -/
def UPlH (Λ : Scc.Sem.Layout) (lbl : Lbl) (s : State) (env : TermRun.Env) : Prop :=
  FramesPlacedInI Λ lbl s [⟨"u", workerRestH, env, [], .unit⟩] (WkSlotsK s)

/-- **At the call node the slots are the region's cells `-56`, `-48`.** -/
theorem wkSlots_addr {R : Region} {rs : List (Reg64 × Int)} {s : State} {σ : Spike.Lib.X64.AS}
    (hA : Spike.Lib.X64.Abs R ⟨-96, rs⟩ s.st.1 σ) (a : Nat) :
    WkSlotsK s a ↔ a = (R.addr (-56)).toNat ∨ a = (R.addr (-48)).toNat := by
  have hsp : s.st.1.regs.get64 .rsp = R.addr (-96) := by
    have := hA.so .rsp (-96) rfl
    rw [← hA.regs] at this
    exact this
  have h56 : R.addr (-56) = R.addr (-96) + 40#64 := by
    rw [show (-56 : Int) = -96 + 40 by omega, Region.addr_add]; rfl
  have h48 : R.addr (-48) = R.addr (-96) + 48#64 := by
    rw [show (-48 : Int) = -96 + 48 by omega, Region.addr_add]; rfl
  simp only [WkSlotsK, hsp, h56, h48]

/-- The place map: `c` at cell `-48`, `j` at cell `-56` of the current frame. -/
def envmU (R : Region) : Nat → String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId) := fun d y k =>
  if d = 0 ∧ k = 0 then
    if y = "c" then some (.one (.slot (R.addr (-48)).toNat))
    else if y = "j" then some (.one (.slot (R.addr (-56)).toNat)) else none
  else none

/-- A region cell's word as the private load of its slot. -/
theorem placeVal_cell {R : Region} {o : Spike.Lib.X64.SO} {s : State} {σ : Spike.Lib.X64.AS}
    (hA : Spike.Lib.X64.Abs R o s.st.1 σ) {k : Int} (hk : R.Off k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σ.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.X64.privLoad, hj, hv]

/-- **`print`'s caller frame placed at the call node**: at a state of `Abs R ⟨-96, _⟩` (the region holding the
cells `-56`, `-48`), the frame in `envP`'s environment is placed in `wc_worker`'s slots when the two cells' words
represent `c`'s word `w3` (cell `-48`) and `j`'s word `w4` (cell `-56`). -/
theorem uPlH_of {Λ : Scc.Sem.Layout} {lbl : Lbl} {R : Region} (hlo : R.lo ≤ -56) (hhi : -40 ≤ R.hi)
    {rs : List (Reg64 × Int)} {s : State} {σ : Spike.Lib.X64.AS}
    (hA : Spike.Lib.X64.Abs R ⟨-96, rs⟩ s.st.1 σ) {w0 w1 w2 w3 w4 : TermRun.Word}
    (h3 : ValRep lbl w3.val (σ.slot (-48)).toNat) (h4 : ValRep lbl w4.val (σ.slot (-56)).toNat) :
    UPlH Λ lbl s (envP w0 w1 w2 w3 w4) := by
  have o48 : R.Off (-48) := ⟨by decide, by omega, by omega⟩
  have o56 : R.Off (-56) := ⟨by decide, hlo, by omega⟩
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
          exact ⟨_, placeVal_cell hA o48, h3⟩
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
        exact ⟨.one (.slot (R.addr (-48)).toNat), by simp [envmU]⟩
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
        exact ⟨_, hpl, (wkSlots_addr hA _).2 (.inr rfl)⟩
      · by_cases hj : y = "j"
        · simp only [h1, hj, and_self, ite_true, Option.some.injEq, show ("j" : String) ≠ "c" by decide,
            ite_false] at hwp
          subst hwp
          simp only [WordPlace.places, List.mem_singleton] at hpl
          exact ⟨_, hpl, (wkSlots_addr hA _).2 (.inl rfl)⟩
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

end Spike.Lib.X64.HelloPh.UFramePl

/-- info: 'Spike.Lib.X64.HelloPh.UFramePl.uPlH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.UFramePl.uPlH_of
