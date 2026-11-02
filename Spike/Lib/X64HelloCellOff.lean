/-
**hello.w's cell off the child's first memory** (x86-64; the twin of `Spike/Lib/A64HelloCellOff.lean`,
`ChildPrem.hdm`): the worker's pointer word `cA` (main's `%r12` at the clone, `X64HelloCloneMem.r12_fit_preRH`)
is a placed label's word with a source message (`PreRH.hlsz`), so it lies in the heap, data or pinned area of a
well-formed layout and off the stack pool, hence off the handed stack `r1`. The child's first memory
(`childAfter`) copies only `r1` of main's private memory, so it, and every memory agreeing with it outside the
child's region (`DFrame (childR top lo)`), has no word at `cA`.

- `cell_out`: a placed label with a word is below `2^64` and off any range inside the stack pool.
- `hdm_cell`: `ChildPrem.hdm` at the child's frame `DFrame (childR top lo) (childAfter …)`.
- `hdm_preRH`: both at main's clone (`PreRH`, at the cell label `l`'s placed address).

## Differences from the AArch64 version

- The child's region is `childR top lo` for any `lo` with `-lo ≤ r1.size` (x86-64's hello keeps `lo` generic;
  AArch64 fixes `-272` with `272 ≤ r1.size`).
- `hdm_cell` is `X64HelloChildSt.unmapped_child` at the clone's thread `0`.
-/
import Spike.Lib.X64HelloChildSt
import Spike.Lib.X64HelloCloneMem

namespace Spike.Lib.X64HelloCellOff

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64 (DFrame)
open Spike.Lib.X64.WakePh.Child (childR)
open Spike.Lib.X64HelloSpawnR (PreRH)

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
every memory agreeing with it outside `childR top lo` (inside `r1`). -/
theorem hdm_cell {x : KState} {t : Thread isa} {r1 : Range} {tls : Nat} {lo : Int}
    (hh : handed x 0 (r1.lo + r1.size) = some (0, r1)) (htop : r1.lo + r1.size < 2 ^ 64) (hlo : -lo ≤ r1.size)
    {cA : Nat} (hc8 : cA + 8 ≤ 2 ^ 64) (hout : cA + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ cA) :
    ∀ m, DFrame (childR (r1.lo + r1.size) lo) (childAfter Scc.Sem.X64.abi x 0 t (r1.lo + r1.size) tls).st.st.1 m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 cA) 8 = none := by
  have hcA : (BitVec.ofNat 64 cA).toNat = cA := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ha8 : (BitVec.ofNat 64 cA).toNat + 8 ≤ 2 ^ 64 := by rw [hcA]; exact hc8
  have hoff : (BitVec.ofNat 64 cA).toNat + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ (BitVec.ofNat 64 cA).toNat := by
    rw [hcA]; exact hout
  exact Spike.Lib.X64HelloChildSt.unmapped_child (a := BitVec.ofNat 64 cA) (lo := lo) (tls := tls) (th := t)
    hh htop hlo ha8 hoff

section Pre

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {D : X64HelloW1.WSideH ι}
  {r0 r1 : ι → Range} {Λ : Scc.Sem.Layout} {w : ι} {d : Cfg} {th : Thread isa} {stack : Nat}
  {s s' : TermRun.Cfg} {s0 s1 : TermRun.TTh} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {j : Nat} {own₀ : List (Loc × Val)}
  {l : WeakMem.AllocLabel}

/-- **The cell is off the child's frame at main's clone**: at `PreRH` over a well-formed layout, with `r1 w`
inside the stack pool and handed at the clone, `c`'s placed word `cA` is unmapped in every memory of the child's
frame condition. -/
theorem hdm_preRH
    (h : PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l)
    (hwf : Λ.WF) (hsub : (r1 w).Sub Λ.stackPool)
    (hh : handed d.2 0 ((r1 w).lo + (r1 w).size) = some (0, r1 w)) (htop : (r1 w).lo + (r1 w).size < 2 ^ 64)
    {lo : Int} (hlo : -lo ≤ (r1 w).size) {cA : Nat} (hl : lbl l = some cA) {tls : Nat} :
    ∀ m, DFrame (childR ((r1 w).lo + (r1 w).size) lo)
        (childAfter Scc.Sem.X64.abi d.2 0 th ((r1 w).lo + (r1 w).size) tls).st.st.1 m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 cA) 8 = none := by
  obtain ⟨hm, hlb⟩ := Spike.Lib.X64HelloCloneMem.memRelP_preRH h
  have hls : (SR w).lsize = lsize := congrArg SpawnRec.lsize h.pre.SR
  rw [hlb, hls] at hm
  obtain ⟨hc8, hout⟩ := cell_out hm hwf hl h.hlsz hsub
  exact hdm_cell hh htop hlo hc8 hout

end Pre

/-- `hdm_cell`'s off-range premise is met by a word below a range (its premises are not vacuous). -/
example : ∃ (r1 : Range) (cA : Nat), cA + 8 ≤ 2 ^ 64 ∧ (cA + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ cA) ∧
    -(-264 : Int) ≤ r1.size ∧ r1.lo + r1.size < 2 ^ 64 := ⟨⟨4096, 4096⟩, 0, by decide, by decide, by decide, by decide⟩

end Spike.Lib.X64HelloCellOff

/-- info: 'Spike.Lib.X64HelloCellOff.cell_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCellOff.cell_out

/-- info: 'Spike.Lib.X64HelloCellOff.hdm_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCellOff.hdm_cell

/-- info: 'Spike.Lib.X64HelloCellOff.hdm_preRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCellOff.hdm_preRH
