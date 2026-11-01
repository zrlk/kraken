/-
**hello.w's cell off the child's first memory** (AArch64; `ChildPrem.hdm`): the worker's
pointer word `cA` (main's `x13` at the clone, `HelloChildWords.words_clone`) is a placed label's word with a
source message (`PreRH.hlsz`), so it lies in the heap, data or pinned area of a well-formed layout and off the stack
pool, hence off the handed stack `r1`. The child's first memory (`childAfter`) copies only `r1` of main's private
memory, so it, and every memory agreeing with it outside the child's region (`DFrame (childR top (-272))`), has
no word at `cA` (wake's `seg_childPre` `hdm` step).

- `cell_out`: a placed label with a word is below `2^64` and off any range inside the stack pool.
- `hdm_cell`: `ChildPrem.hdm` at the child's frame `DFrame (childR top (-272)) (childAfter …)`.
- `hdm_preRH`: both at main's clone (`PreRH`, at the cell label `l`'s placed address).
-/
import Spike.Lib.A64WakeChildAt
import Spike.Lib.A64HelloCloneMem

namespace Spike.Lib.HelloCellOff

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.A64.Flow (DFrame)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.HelloSpawnR (PreRH)

/-- **A placed label holding a word is off the stack pool**: below `2^64`, and outside any range inside the pool. -/
theorem cell_out {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) {l : WeakMem.AllocLabel} {cA : Nat}
    (hl : lbl l = some cA) (hsz : 0 < lsize l) {r1 : Range} (hsub : r1.Sub Λ.stackPool) :
    cA + 8 ≤ 2 ^ 64 ∧ (cA + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ cA) := by
  have hx : wordAddr lbl ⟨l, 0⟩ = some (cA + 8 * 0) := by simp [wordAddr, hl]
  have h8 := hm.addr_lt hwf hx hsz
  obtain ⟨-, -, -, -, hDS, hHS, -, -, -, hSP⟩ := hwf.disjoint
  simp only [Range.Disjoint] at hDS hHS hSP
  simp only [Range.Sub] at hsub
  refine ⟨by omega, ?_⟩
  rcases (hm.lbl_range _ _ hl).2 with hs | hs | ⟨h0, -⟩
  · simp only [lrange, Range.Sub] at hs; omega
  · simp only [lrange, Range.Sub] at hs; omega
  · omega

/-- **`ChildPrem.hdm` at the child's frame**: a word off `r1` is unmapped in the child's first memory, and so in
every memory agreeing with it outside `childR top (-272)` (inside `r1`). -/
theorem hdm_cell {x : KState} {t : Thread isaLSE2} {r1 : Range} {tls : Nat}
    (hh : handed x 0 (r1.lo + r1.size) = some (0, r1)) (htop : r1.lo + r1.size < 2 ^ 64) (hsz : 272 ≤ r1.size)
    {cA : Nat} (hc8 : cA + 8 ≤ 2 ^ 64) (hout : cA + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ cA) :
    ∀ m, DFrame (childR (r1.lo + r1.size) (-272)) (childAfter abi x 0 t (r1.lo + r1.size) tls).st.st.1 m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 cA) 8 = none := by
  intro m hm
  have hcA : cA < 2 ^ 64 := by omega
  rw [hm _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]; exact hc8)
    (by simp only [childR, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA, Nat.mod_eq_of_lt htop]; omega),
    Spike.Lib.A64.Rt.childAfter_dmem hh]
  exact Spike.Lib.A64.Rt.loadInt_copyRange_none (by omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]; unfold Range.contains; omega) (by decide)

section Pre

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : WakeM0.MSide ι} {D : HelloW1.WSideH ι}
  {r0 r1 : ι → Range} {Λ : Scc.Sem.Layout} {w : ι} {d : Cfg} {th : Thread isaLSE2} {stack : Nat}
  {s s' : TermRun.Cfg} {s0 s1 : TermRun.TTh} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {j : Nat} {own₀ : List (Loc × Val)}
  {l : WeakMem.AllocLabel}

/-- (row B8-seg-words, `hdm`) **The cell is off the child's frame at main's clone**: at `PreRH` over a well-formed
layout, with `r1 w` inside the stack pool and handed at the clone, `c`'s placed word `cA` is unmapped in every
memory of the child's frame condition. -/
theorem hdm_preRH
    (h : PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l)
    (hwf : Λ.WF) (hsub : (r1 w).Sub Λ.stackPool)
    (hh : handed d.2 0 ((r1 w).lo + (r1 w).size) = some (0, r1 w)) (htop : (r1 w).lo + (r1 w).size < 2 ^ 64)
    (hsz : 272 ≤ (r1 w).size) {cA : Nat} (hl : lbl l = some cA) {tls : Nat} :
    ∀ m, DFrame (childR ((r1 w).lo + (r1 w).size) (-272))
        (childAfter abi d.2 0 th ((r1 w).lo + (r1 w).size) tls).st.st.1 m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 cA) 8 = none := by
  obtain ⟨hm, hlb⟩ := Spike.Lib.HelloCloneMem.memRelP_preRH h
  have hls : (SR w).lsize = lsize := congrArg SpawnRec.lsize h.pre.SR
  rw [hlb, hls] at hm
  obtain ⟨hc8, hout⟩ := cell_out hm hwf hl h.hlsz hsub
  exact hdm_cell hh htop hsz hc8 hout

end Pre

/-- `hdm_cell`'s off-range premise is met by a word below a range (its premises are not vacuous). -/
example : ∃ (r1 : Range) (cA : Nat), cA + 8 ≤ 2 ^ 64 ∧ (cA + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ cA) ∧ 272 ≤ r1.size ∧
    r1.lo + r1.size < 2 ^ 64 := ⟨⟨4096, 4096⟩, 0, by decide, by decide, by decide, by decide⟩

end Spike.Lib.HelloCellOff

/-- info: 'Spike.Lib.HelloCellOff.cell_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloCellOff.cell_out

/-- info: 'Spike.Lib.HelloCellOff.hdm_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloCellOff.hdm_cell

/-- info: 'Spike.Lib.HelloCellOff.hdm_preRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloCellOff.hdm_preRH
