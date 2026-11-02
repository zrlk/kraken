/-
**hello.w on x86-64: the frozen buffer's instance data** (the ISA-generic, live part of
`Spike/Lib/A64HelloInst.lean`). hello's location sets are wake's (`WakeP.wakeP`, every word placed at the spawn
but `c` frozen) at location data whose placement also holds rodata's buffer (label `lB`, base `b0`); the buffer's
target words are frozen.

- `helloP`: hello's `Inv2Params`, wake's `wakeP` (no new location set).
- `BufPl lbl lsize cS lB b0`: the buffer placed at the spawn (`lbl lB = some b0`), at least two words
  (`2 ≤ lsize lB`), off `c`'s label.
- `lrange_fit`: a placed label's range fits below `2^64` (`MemRelP`, `Λ.WF`).
- `frz_buf`: the buffer's target words `wordLoc (b0 + 8 i)`, `i < 2`, are frozen (`WCompat.cT`'s shape of `cT`
  and `MemRelP.lbl_disj`).

**Where this differs from AArch64**: nothing in the statements or proofs, which are ISA-generic (`I : ISA`). The
module is a separate file in namespace `Spike.Lib.X64HelloInst` (beside `X64HelloInst`'s `bufW`, `BufAtSpawn`)
whose closure is `WakeP`, `MemRelP` and `MemRel` only: A64's file also imports `WakeW1`, `A64HelloWriteK` and
`A64HelloClonePreHOf`, which reach the AArch64 syntax. A64's `frzS_buf`, `buf_ne_cS`, `HelloProtB` and the
content facts are not used by the hello proof and are not restated.
-/
import Spike.Lib.WakeP
import Scc.Sem.MemRelP

namespace Spike.Lib.X64HelloInst

open Kraken.Promising Scc.Sem Spike.Lib.WakeP

/-- **hello's `Inv2Params`**: wake's. -/
abbrev helloP {I : ISA} (K : Kernel.Abi I) (μ : Marks) (W : WakeLocs) : Spike.Lib.Inv2Core.Inv2Params I :=
  wakeP K μ W

/-- **The buffer's placement at the spawn**: label `lB` at `b0`, at least
two words, off `c`'s label. -/
def BufPl (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (cS : WeakMem.Address)
    (lB : WeakMem.AllocLabel) (b0 : Nat) : Prop :=
  lbl lB = some b0 ∧ 2 ≤ lsize lB ∧ lB ≠ cS.label

/-- `BufPl` is inhabited: label `2` placed at `8`, two words, `c` at label `4`. -/
example : BufPl (fun l => if l = 2 then some 8 else none) (fun _ => 2) ⟨4, 0⟩ 2 8 := by
  exact ⟨rfl, Nat.le_refl _, by decide⟩

section Frz

variable {I : ISA} {K : Kernel.Abi I} {μ : Marks} {W : WakeLocs} {lB : WeakMem.AllocLabel} {b0 : Nat}

/-- **A placed label's range fits below `2^64`.** -/
theorem lrange_fit {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) {l : WeakMem.AllocLabel} {b : Nat}
    (hl : lbl l = some b) : b + 8 * lsize l ≤ 2 ^ 64 := by
  have hpin := hwf.inSpace Λ.pinned (by simp [Layout.regions])
  have hheap := hwf.inSpace Λ.heap (by simp [Layout.regions])
  have hdata := hwf.inSpace Λ.data (by simp [Layout.regions])
  simp only [Range.InSpace] at hpin hheap hdata
  rcases (h.lbl_range l b hl).2 with hs | hs | ⟨-, hs⟩ <;> simp only [lrange, Range.Sub] at hs <;> omega

/-- **The buffer's target words are frozen**: placed (`BufPl`), and not
`cT`, the word placed for `cS` (`WCompat.cT`'s shape), whose label's range
is disjoint from the buffer's (`MemRelP.lbl_disj`). -/
theorem frz_buf {Λ : Scc.Sem.Layout} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat}
    (h : MemRelP Λ W.lbl W.lsize ts tm sm tp tq sp) (hwf : Λ.WF) (hB : BufPl W.lbl W.lsize W.cS lB b0)
    (hcT : ∃ a, W.cT = wordLoc a ∧ wordAddr W.lbl W.cS = some a ∧ W.cS.offset < W.lsize W.cS.label)
    {i : Nat} (hi : i < 2) : (helloP K μ W).frz (wordLoc (b0 + 8 * i)) := by
  have hfit := lrange_fit h hwf hB.1
  have h2 := hB.2.1
  have hb : b0 + 8 * i < 2 ^ 64 := by omega
  refine ⟨⟨lB, b0, hB.1, ?_⟩, fun heq => ?_⟩
  · simp only [wordLoc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, lrange, Range.contains]
    omega
  · obtain ⟨a, hca, hwa, ho⟩ := hcT
    simp only [wordAddr, Option.map_eq_some_iff] at hwa
    obtain ⟨bc, hbc, rfl⟩ := hwa
    have hfc := lrange_fit h hwf hbc
    have hd := h.lbl_disj _ _ _ _ hB.2.2 hB.1 hbc
    simp only [lrange, Range.Disjoint] at hd
    rw [hca] at heq
    obtain ⟨f, hf⟩ : ∃ f : Nat, W.cS.offset = f := ⟨_, rfl⟩
    rw [hf] at heq ho
    have ho' : f + 1 ≤ W.lsize W.cS.label := ho
    have ha : bc + 8 * f < 2 ^ 64 := by omega
    have := MemRel.wordLoc_inj hb ha heq
    omega

end Frz

end Spike.Lib.X64HelloInst

/-- info: 'Spike.Lib.X64HelloInst.lrange_fit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloInst.lrange_fit

/-- info: 'Spike.Lib.X64HelloInst.frz_buf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloInst.frz_buf
