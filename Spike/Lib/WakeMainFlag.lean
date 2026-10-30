/-
**wake.w on AArch64: the flag's word off main's private memory and frame**: `frames_unit`'s premises on the flag's word
`A` (a shared word: `LocIn Λ.shared ⟨A, 8⟩`, e.g. `GhOK`'s `cT`).

Private memory only gains keys at the kernel's transfers of held ranges, so
under `DmemPriv.PrivInv` (every key in the entry stack or a held range of the
pool; `A64DmemPriv.privInv_run`) no shared byte is a key (`key_not_shared`,
from `Entry.clear` and `Layout.WF.disjoint` only):

- `hA0_of`: `A` does not load from main's private memory after the clone
  (`parentPre` only erases, `retThread` keeps it);
- `hAoff_of`: `A` fits (`Layout.WF.inSpace` on its last byte's region) and
  is off a region whose cells load from private memory (`Abs`, as `hat`'s).
-/
import Spike.Lib.WakeMainFrames
import Spike.Lib.DmemPriv

namespace Spike.Lib.WakeMainFlag

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.Handover
open Spike.Lib.DmemPriv (PrivInv)

/-- **A loaded word's bytes are keys.** -/
theorem mem_of_loadInt {d : _root_.Mem 64} {a : BitVec 64} {n : Nat} {j : Int} (h : Mem.loadInt d a n = some j)
    {i : Nat} (hi : i < n) : a + BitVec.ofNat 64 i ∈ d := by
  have key : ∀ (l : List (Option UInt8)) (v : List UInt8), List.mapM id l = some v → ∀ o ∈ l, o.isSome := by
    intro l; induction l with
    | nil => simp
    | cons x l ih =>
      intro v hv o ho
      cases x with
      | none => simp at hv
      | some y =>
        simp only [List.mapM_cons, id] at hv
        cases hl : List.mapM id l with
        | none => simp [hl] at hv
        | some w =>
          rcases List.mem_cons.mp ho with rfl | ho
          · rfl
          · exact ih w hl o ho
  obtain ⟨v, hv, -⟩ := Option.map_eq_some_iff.mp h
  have := key _ v hv _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  exact Std.ExtHashMap.mem_iff_isSome_getElem?.mpr (by simpa [Std.ExtHashMap.get?_eq_getElem?] using this)

/-- **No shared byte is a private key** under `PrivInv`. -/
theorem key_not_shared {P : State → Prop} {Λ : Scc.Sem.Layout} {Ent : Entry} {d : Config isaLSE2 × KState}
    (hc : PrivInv abi P Λ Ent d) (hE : Ent.clear Λ = true) (hwf : Λ.WF) {tid : Nat} {th : Thread isaLSE2}
    (hth : d.1.threads[tid]? = some th) {a : BitVec 64} (ha : a ∈ th.st.st.1.dmem) : ¬ Λ.shared a.toNat := by
  have hEs := (Entry.clear_disjoint hE).2
  have h1 := hEs Λ.data (by simp [Scc.Sem.Layout.regions]); have h2 := hEs Λ.heap (by simp [Scc.Sem.Layout.regions])
  have h3 := hEs Λ.pinned (by simp [Scc.Sem.Layout.regions])
  obtain ⟨-, -, -, -, h4, h5, -, -, -, h6⟩ := hwf.disjoint
  unfold Range.Disjoint at h1 h2 h3 h4 h5 h6
  intro hsh
  unfold Scc.Sem.Layout.shared Range.contains at hsh
  rcases (hc.own.dom tid th hth a).mp ha with ⟨-, hs⟩ | ⟨r, hr, hrc⟩
  · unfold Range.contains at hs
    rcases hsh with hsh | hsh | hsh <;> omega
  · obtain ⟨-, hsub, -⟩ := hc.own.held_ok _ hr
    rw [hc.pool] at hsub
    change r.Sub Λ.stackPool at hsub
    unfold Range.contains at hrc; unfold Range.Sub at hsub
    rcases hsh with hsh | hsh | hsh <;> omega

/-- **`hA0`**: the shared word `A` does not load from main's private memory
after the clone. -/
theorem hA0_of {P : State → Prop} {Λ : Scc.Sem.Layout} {Ent : Entry} {d : Config isaLSE2 × KState}
    (hc : PrivInv abi P Λ Ent d) (hE : Ent.clear Λ = true) (hwf : Λ.WF) {th : Thread isaLSE2}
    (hth : d.1.threads[0]? = some th) {A : BitVec 64} (hA : Spike.Lib.Consumer1.LocIn Λ.shared ⟨A, 8⟩)
    (stack : Nat) (r : BitVec 64) :
    Mem.loadInt (retThread abi (parentPre abi d.2 0 th stack) r).st.st.1.dmem A 8 = none := by
  have hn : A ∉ th.st.st.1.dmem := fun hm => key_not_shared hc hE hwf hth hm hA.addr
  have hn' : A ∉ (parentPre abi d.2 0 th stack).st.st.1.dmem := by
    unfold parentPre; split
    · exact hn
    · intro hm
      exact hn ((Scc.Sem.Kernel.mem_eraseRange _ _ A).mp hm).2
  cases hl : Mem.loadInt (retThread abi (parentPre abi d.2 0 th stack) r).st.st.1.dmem A 8 with
  | none => rfl
  | some j =>
    have := mem_of_loadInt hl (i := 0) (by decide)
    rw [BitVec.add_zero] at this
    rw [retThread_st] at this
    exact (hn' this).elim

/-- **`hA8`, `hAoff`**: the shared word `A` fits and is off a region every
cell of which loads from the private memory of a thread under `PrivInv`. -/
theorem hAoff_of {P : State → Prop} {Λ : Scc.Sem.Layout} {Ent : Entry} {d : Config isaLSE2 × KState}
    (hc : PrivInv abi P Λ Ent d) (hE : Ent.clear Λ = true) (hwf : Λ.WF) {tid : Nat} {th : Thread isaLSE2}
    (hth : d.1.threads[tid]? = some th) {R : Region} (hR : R.OK) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hlh : R.lo < R.hi)
    {o : SO} {σ : AS}
    (hAbs : Abs R o th.st.st.1 σ) {A : BitVec 64} (hA : Spike.Lib.Consumer1.LocIn Λ.shared ⟨A, 8⟩) :
    A.toNat + 8 ≤ 2 ^ 64 ∧
      ((A.toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ A.toNat) := by
  have hb : ∀ i < 8, Λ.shared (A.toNat + i) := fun i hi => hA i (by simp [Kernel.locBytes]; omega)
  refine ⟨?_, ?_⟩
  · have h7 := hb 7 (by decide)
    have hs := hwf.inSpace
    have s1 := (hs Λ.data (by simp [Scc.Sem.Layout.regions])).2; have s2 := (hs Λ.heap (by simp [Scc.Sem.Layout.regions])).2
    have s3 := (hs Λ.pinned (by simp [Scc.Sem.Layout.regions])).2
    unfold Scc.Sem.Layout.shared Range.contains at h7; omega
  · refine Classical.byContradiction fun hov => ?_
    have hx : ∃ x : Int, (A.toNat : Int) ≤ x ∧ x < A.toNat + 8 ∧ R.base.toNat + R.lo ≤ x ∧
        x < R.base.toNat + R.hi :=
      if hle : (A.toNat : Int) ≤ R.base.toNat + R.lo then
        ⟨R.base.toNat + R.lo, by omega, by omega, by omega, by omega⟩
      else ⟨A.toNat, by omega, by omega, by omega, by omega⟩
    obtain ⟨x, hx1, hx2, hx3, hx4⟩ := hx
    have hk : R.Off ((x - R.base.toNat) - (x - R.base.toNat) % 8) := by
      refine ⟨by omega, ?_, ?_⟩ <;> omega
    obtain ⟨j, hj, -⟩ := hAbs.slot _ hk
    have ht := R.addr_toNat hR hk
    have hf := R.addr_fit hR hk
    have hm := mem_of_loadInt hj (i := ((x - R.base.toNat) % 8).toNat) (by omega)
    have hn := key_not_shared hc hE hwf hth hm
    apply hn
    have e : ((R.addr ((x - R.base.toNat) - (x - R.base.toNat) % 8) +
        BitVec.ofNat 64 ((x - R.base.toNat) % 8).toNat).toNat : Int) = x := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have h8 : ((x - R.base.toNat) % 8).toNat < 8 := by omega
      rw [Nat.mod_eq_of_lt (a := ((x - R.base.toNat) % 8).toNat) (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    have := hb (x - A.toNat).toNat (by omega)
    rw [show A.toNat + (x - A.toNat).toNat = (R.addr ((x - R.base.toNat) - (x - R.base.toNat) % 8) +
        BitVec.ofNat 64 ((x - R.base.toNat) % 8).toNat).toNat by omega] at this
    exact this

/-- info: 'Spike.Lib.WakeMainFlag.mem_of_loadInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mem_of_loadInt

/-- info: 'Spike.Lib.WakeMainFlag.key_not_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms key_not_shared

/-- info: 'Spike.Lib.WakeMainFlag.hA0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hA0_of

/-- info: 'Spike.Lib.WakeMainFlag.hAoff_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hAoff_of

end Spike.Lib.WakeMainFlag
