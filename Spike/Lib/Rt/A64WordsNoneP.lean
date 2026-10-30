/-
**No private word of the heap, the static image or the pinned region**
(AArch64): `WordsNoneP Λ d`, the frame `WordsNone` widened to the pinned
region, word by word over the union (a word whose eight bytes each lie in
the heap, `.data` or `pinned` loads none; its bytes may straddle two of
them). Wake's start frame and `MainGlue.FS` carry it, so the runtime's
pinned words (the second TCB's header and id word) are unmapped in every
frame memory.

- `WordsNoneP.wn`: it gives `WordsNone`.
- `wordsNoneP_of_keys`, `wordsNoneP_stackMem`: from private keys (the entry
  stack, the pool), as `wordsNone_of_keys`; the entry stack's memory.
- `wordsNoneP_fstable`, `wordsNoneP_and_fstable`, `wordsNoneP_swFSL_fstable`,
  `wordsNoneP_takeMem`: the `WordsNone` stability facts, same shape.
-/
import Spike.Lib.Rt.A64SwWordsNone
import Spike.Lib.A64DmemPrivPlace

namespace Spike.Lib.DmemPriv

open Kraken Kraken.Promising Scc.Sem

/-- A byte of the heap, the static image or the pinned region. -/
def PrivB (Λ : Scc.Sem.Layout) (x : Nat) : Prop := Λ.heap.contains x ∨ Λ.data.contains x ∨ Λ.pinned.contains x

/-- **No word of the heap, the image or the pinned region loads** from `d`:
none whose eight bytes each lie in one of them. -/
def WordsNoneP (Λ : Scc.Sem.Layout) (d : _root_.Mem 64) : Prop :=
  ∀ a : BitVec 64, (∀ j < 8, PrivB Λ (a.toNat + j)) → Mem.loadInt d a 8 = none

theorem WordsNoneP.wn {Λ : Scc.Sem.Layout} {d : _root_.Mem 64} (h : WordsNoneP Λ d) : WordsNone Λ d :=
  fun a ha => h a fun j hj => by unfold WordIn Range.contains at ha; unfold PrivB Range.contains; omega

/-- A range inside the entry stack or the pool is off the three regions. -/
theorem disjoint3_of_sub {Λ : Scc.Sem.Layout} {Ent : Entry} (hwf : Λ.WF) (hE : Ent.clear Λ = true) {r : Range}
    (hS : r.Sub Ent.stack ∨ r.Sub Λ.stackPool) :
    r.Disjoint Λ.heap ∧ r.Disjoint Λ.data ∧ r.Disjoint Λ.pinned := by
  have hs := (Entry.clear_disjoint hE).2
  have hhs := hs Λ.heap (by simp [Scc.Sem.Layout.regions])
  have hds := hs Λ.data (by simp [Scc.Sem.Layout.regions])
  have hps := hs Λ.pinned (by simp [Scc.Sem.Layout.regions])
  obtain ⟨-, -, -, -, hdp, hhp, -, -, -, hpp⟩ := hwf.disjoint
  unfold Range.Disjoint at *
  unfold Range.Sub at hS
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- **Private keys give `WordsNoneP`**: the word's first byte is not a key. -/
theorem wordsNoneP_of_keys {Λ : Scc.Sem.Layout} {Ent : Entry} {d : _root_.Mem 64}
    (hd : ∀ a, a ∈ d → Ent.stack.contains a.toNat ∨ Λ.stackPool.contains a.toNat)
    (hwf : Λ.WF) (hE : Ent.clear Λ = true) : WordsNoneP Λ d := by
  intro a ha
  have hn : a ∉ d := by
    intro hm
    have h0 := ha 0 (by decide)
    have hs := (Entry.clear_disjoint hE).2
    have hhs := hs Λ.heap (by simp [Scc.Sem.Layout.regions])
    have hds := hs Λ.data (by simp [Scc.Sem.Layout.regions])
    have hps := hs Λ.pinned (by simp [Scc.Sem.Layout.regions])
    obtain ⟨-, -, -, -, hdp, hhp, -, -, -, hpp⟩ := hwf.disjoint
    unfold Range.Disjoint at hhs hds hps hdp hhp hpp
    unfold PrivB Range.contains at h0
    rcases hd a hm with h | h <;> unfold Range.contains at h <;> omega
  have h0 : d[a]? = none := Std.ExtHashMap.getElem?_eq_none hn
  simp [Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ_eq_map, h0]

/-- **The entry state's memory** (its keys the entry stack's). -/
theorem wordsNoneP_stackMem {Λ : Scc.Sem.Layout} {Ent : Entry} (hwf : Λ.WF) (hE : Ent.clear Λ = true) :
    WordsNoneP Λ Ent.stackMem :=
  wordsNoneP_of_keys (fun a ha => .inl ((mem_stackMem (Entry.clear_disjoint hE).1 a).mp ha)) hwf hE

end Spike.Lib.DmemPriv

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0 Spike.Lib.DmemPriv

variable {Λ : Scc.Sem.Layout}

/-- **`WordsNoneP` is `FStable`** in a non-empty region off the three regions. -/
theorem wordsNoneP_fstable {R : Spike.Lib.Region} (hwf : Λ.WF) (hR : R.OK) (hne : R.lo < R.hi)
    (hh : Scc.Sem.Range.Disjoint ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩ Λ.heap)
    (hd : Scc.Sem.Range.Disjoint ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩ Λ.data)
    (hp : Scc.Sem.Range.Disjoint ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩ Λ.pinned) :
    FStable R (fun m => WordsNoneP Λ m.dmem) := by
  intro m m' h hf a ha
  have h7 := ha 7 (by decide)
  have i1 := (hwf.inSpace Λ.heap (by simp [Scc.Sem.Layout.regions])).2
  have i2 := (hwf.inSpace Λ.data (by simp [Scc.Sem.Layout.regions])).2
  have i3 := (hwf.inSpace Λ.pinned (by simp [Scc.Sem.Layout.regions])).2
  have hRl := hR.lo
  unfold PrivB Scc.Sem.Range.contains at h7
  by_cases hc : (a.toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a.toNat
  · rw [hf a (by omega) hc]; exact h a ha
  · exfalso
    have hz := ha ((R.base.toNat + R.lo).toNat - a.toNat) (by omega)
    unfold PrivB Scc.Sem.Range.contains at hz
    unfold Scc.Sem.Range.Disjoint at hh hd hp
    simp only at hh hd hp
    omega

/-- **The frame `WordsNoneP ∧ F₀`** for a non-empty region in the entry
stack or the pool (as `Alloc.wordsNone_and_fstable`). -/
theorem wordsNoneP_and_fstable {Ent : Scc.Sem.Entry} {R : Spike.Lib.Region} {F₀ : MachineData → Prop}
    (hwf : Λ.WF) (hE : Ent.clear Λ = true) (hR : R.OK) (hne : R.lo < R.hi)
    (hS : Scc.Sem.Range.Sub ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩ Ent.stack ∨
      Scc.Sem.Range.Sub ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩ Λ.stackPool)
    (h₀ : FStable R F₀) :
    FStable R (fun m => WordsNoneP Λ m.dmem ∧ F₀ m) ∧ ∀ m, WordsNoneP Λ m.dmem ∧ F₀ m → WordsNoneP Λ m.dmem :=
  have hd := disjoint3_of_sub hwf hE hS
  ⟨Alloc.fstable_and (wordsNoneP_fstable hwf hR hne hd.1 hd.2.1 hd.2.2) h₀, fun _ h => h.1⟩

/-- **The frame after the switch, with `WordsNoneP`, is `FStable`**
(as `wordsNone_swFSL_fstable`). -/
theorem wordsNoneP_swFSL_fstable {top a v : BitVec 64} {L : Int} {rS : Scc.Sem.Range}
    (hwf : Λ.WF) (hrS : rS.Sub Λ.stackPool) (hok : (swR top (-L) 0).OK) (hL : 8 ≤ L) (hL8 : L % 8 = 0)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hfit : a.toNat + 8 ≤ 2 ^ 64)
    (hout : (a.toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ a.toNat)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64) :
    FStable (swR v (-L) 0) (fun m => WordsNoneP Λ m.dmem ∧ swFSL L rS top a v m) := by
  by_cases hv : v = top
  · subst hv
    have hc := sub_trans (cellsR_swR_sub hok hL hL8 hsub) hrS
    obtain ⟨-, -, -, -, hdp, hhp, -, -, -, hpp⟩ := hwf.disjoint
    have hh : (cellsR (swR v (-L) 0)).Disjoint Λ.heap := by
      unfold Scc.Sem.Range.Disjoint at *; unfold Scc.Sem.Range.Sub at hc; omega
    have hd : (cellsR (swR v (-L) 0)).Disjoint Λ.data := by
      unfold Scc.Sem.Range.Disjoint at *; unfold Scc.Sem.Range.Sub at hc; omega
    have hp : (cellsR (swR v (-L) 0)).Disjoint Λ.pinned := by
      unfold Scc.Sem.Range.Disjoint at *; unfold Scc.Sem.Range.Sub at hc; omega
    exact Alloc.fstable_and (wordsNoneP_fstable hwf hok (by simp [swR]; omega) hh hd hp) fun m m' h hd' =>
      ⟨swF_stableL hfit hout m m' h.1 hd', stackOff_stable hfitS m m' h.2 hd'⟩
  · exact fun m _ h _ => absurd h.2.1.1 hv

/-- **`WordsNoneP` survives the stack take**: the taken range lies in the
pool, off the three regions (as `wordsNone_takeMem`). -/
theorem wordsNoneP_takeMem {rS : Scc.Sem.Range} {pm : _root_.Mem 64} {m : MachineData}
    (hwf : Λ.WF) (hrS : rS.Sub Λ.stackPool) (h : WordsNoneP Λ m.dmem) :
    WordsNoneP Λ (takeMem pm rS m).dmem := by
  intro a ha
  rw [loadInt_takeMem ?_]
  · exact h a ha
  intro i hi hm
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
  have hj := List.mem_range.mp hj
  have h1 := (hwf.inSpace Λ.heap (by simp [Scc.Sem.Layout.regions])).2
  have h2 := (hwf.inSpace Λ.data (by simp [Scc.Sem.Layout.regions])).2
  have h3 := (hwf.inSpace Λ.stackPool (by simp [Scc.Sem.Layout.regions])).2
  have h4 := (hwf.inSpace Λ.pinned (by simp [Scc.Sem.Layout.regions])).2
  obtain ⟨-, -, -, -, hdp, hhp, -, -, -, hpp⟩ := hwf.disjoint
  have hb := ha i hi
  have h7 := ha 7 (by decide)
  unfold PrivB Scc.Sem.Range.contains at hb h7
  unfold Scc.Sem.Range.Disjoint at hdp hhp hpp
  unfold Scc.Sem.Range.Sub at hrS
  have hlt : a.toNat + 7 < 2 ^ 64 := by omega
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

-- Non-vacuity: the entry stack's memory at any admissible layout.
example {Ent : Scc.Sem.Entry} (hwf : Λ.WF) (hE : Ent.clear Λ = true) : WordsNoneP Λ Ent.stackMem :=
  wordsNoneP_stackMem hwf hE

end Spike.Lib.A64.Rt

/-- info: 'Spike.Lib.DmemPriv.wordsNoneP_stackMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.DmemPriv.wordsNoneP_stackMem

/-- info: 'Spike.Lib.A64.Rt.wordsNoneP_and_fstable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.wordsNoneP_and_fstable

/-- info: 'Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable

/-- info: 'Spike.Lib.A64.Rt.wordsNoneP_takeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.wordsNoneP_takeMem
