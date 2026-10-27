/-
**The switched stack's frame loads no heap or image word** (AArch64): after
`scc_rt_start`'s stack switch (`startSwitchU_segW`, `Spike/Lib/Rt/A64Segs.lean`)
the segments run in `swR v (-L) 0` under `swFSL L rS top a v`. With the
switch's premises (`hok`, the cells of the new region in the taken range
`rS`, `hsub`; the limit word off it, `hfit`, `hout`; `hfitS`) and the taken
range in the stack pool:

- `cellsR_swR_sub`: the new region's cells lie in `rS` (`hsub` at its
  lowest and highest cells; the depth `L` a positive multiple of `8`);
- `wordsNone_swFSL_fstable`: the frame `WordsNone Λ ∧ swFSL L rS top a v` is
  `FStable` in `swR v (-L) 0` (for `v ≠ top`, `swFSL` is empty).
-/
import Spike.Lib.Rt.A64Segs
import Spike.Lib.A64WordsNone
import Spike.Lib.RegionCells

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0 Spike.Lib.DmemPriv

/-- **The new region's cells lie in the taken range.** -/
theorem cellsR_swR_sub {top : BitVec 64} {L : Int} {rS : Scc.Sem.Range} (hok : (swR top (-L) 0).OK)
    (hL : 8 ≤ L) (hL8 : L % 8 = 0)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7)) :
    (cellsR (swR top (-L) 0)).Sub rS := by
  have h1 := hsub (-L) ⟨by omega, by simp [swR], by simp [swR]; omega⟩
  have h2 := hsub (-8) ⟨by decide, by simp [swR]; omega, by simp [swR]⟩
  have e1 : (((swR top (-L) 0).addr (-L)).toNat : Int) = top.toNat + -L :=
    Region.addr_toNat_of hok (by simp [swR]) (by simp [swR]; omega)
  have e2 : (((swR top (-L) 0).addr (-8)).toNat : Int) = top.toNat + -8 :=
    Region.addr_toNat_of hok (by simp [swR]; omega) (by simp [swR])
  have h0 : (0 : Int) ≤ top.toNat + -L := hok.lo
  unfold Scc.Sem.Range.contains at h1 h2
  show Scc.Sem.Range.Sub ⟨((top.toNat : Int) + -L).toNat, ((0 : Int) - -L).toNat⟩ rS
  unfold Scc.Sem.Range.Sub
  generalize ((swR top (-L) 0).addr (-L)).toNat = x1 at e1 h1
  generalize ((swR top (-L) 0).addr (-8)).toNat = x2 at e2 h2
  simp only
  omega

/-- **The frame after the switch, with `WordsNone`, is `FStable`.** -/
theorem wordsNone_swFSL_fstable {Λ : Scc.Sem.Layout} {top a v : BitVec 64} {L : Int} {rS : Scc.Sem.Range}
    (hwf : Λ.WF) (hrS : rS.Sub Λ.stackPool) (hok : (swR top (-L) 0).OK) (hL : 8 ≤ L) (hL8 : L % 8 = 0)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hfit : a.toNat + 8 ≤ 2 ^ 64)
    (hout : (a.toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ a.toNat)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64) :
    FStable (swR v (-L) 0) (fun m => WordsNone Λ m.dmem ∧ swFSL L rS top a v m) := by
  by_cases hv : v = top
  · subst hv
    have hc := sub_trans (cellsR_swR_sub hok hL hL8 hsub) hrS
    obtain ⟨-, -, -, -, hdp, hhp, -⟩ := hwf.disjoint
    have hh : (cellsR (swR v (-L) 0)).Disjoint Λ.heap := by
      unfold Scc.Sem.Range.Disjoint at *; unfold Scc.Sem.Range.Sub at hc; omega
    have hd : (cellsR (swR v (-L) 0)).Disjoint Λ.data := by
      unfold Scc.Sem.Range.Disjoint at *; unfold Scc.Sem.Range.Sub at hc; omega
    exact Alloc.fstable_and (Alloc.wordsNone_fstable hwf hok hh hd) fun m m' h hd' =>
      ⟨swF_stableL hfit hout m m' h.1 hd', stackOff_stable hfitS m m' h.2 hd'⟩
  · exact fun m _ h _ => absurd h.2.1.1 hv

/-- **`WordsNone` survives the stack take** (`startU_segW`'s `hFt`): the
taken range lies in the stack pool, off the heap and the static image, so
no word of either changes. -/
theorem wordsNone_takeMem {Λ : Scc.Sem.Layout} {rS : Scc.Sem.Range} {pm : _root_.Mem 64} {m : MachineData}
    (hwf : Λ.WF) (hrS : rS.Sub Λ.stackPool) (h : WordsNone Λ m.dmem) :
    WordsNone Λ (takeMem pm rS m).dmem := by
  intro a ha
  rw [loadInt_takeMem ?_]
  · exact h a ha
  intro i hi hm
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
  have hj := List.mem_range.mp hj
  have h1 := (hwf.inSpace Λ.heap (by simp [Scc.Sem.Layout.regions])).2
  have h2 := (hwf.inSpace Λ.data (by simp [Scc.Sem.Layout.regions])).2
  have h3 := (hwf.inSpace Λ.stackPool (by simp [Scc.Sem.Layout.regions])).2
  obtain ⟨-, -, -, -, hdp, hhp, -⟩ := hwf.disjoint
  unfold WordIn Scc.Sem.Range.contains at ha
  unfold Scc.Sem.Range.Disjoint at hdp hhp
  unfold Scc.Sem.Range.Sub at hrS
  have hlt : a.toNat + 7 < 2 ^ 64 := by rcases ha with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  rcases ha with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> omega

end Spike.Lib.A64.Rt
