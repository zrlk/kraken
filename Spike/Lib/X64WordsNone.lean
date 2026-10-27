/-
**Frames that load no word of the heap or the static image** (x86-64):
`WordsNone` (`Spike/Lib/DmemPriv.lean`) as a segment's frame condition, and
the allocator's word premises from it.

- `wordsNone_fstable`, `fstable_and`, `wordsNone_and_fstable`: `WordsNone`
  is `FStable` for a region off the heap and the image (one inside the entry
  stack or the stack pool), and so is its conjunction with another frame;
- `hmem_of_wordsNone`, `hbuf_of_wordsNone`: the setups' `hmem`, `hbuf` (no
  word loads at the allocation counter, an allocation's header or the
  buffer's words), given the counter in the heap or the image and the arena
  of `ms.cells` units at `ms.heap` inside the heap.

`WordsNone` holds of every thread along every run from load
(`PrivInv.dmemPriv`, `PrivKeys.wordsNone`). The arena's placement (`hH`,
`hHi`) is the memory side's (`ms.heap = Λ.heap.lo` and `16 · ms.cells ≤
Λ.heap.size` at the consumer's `ms`).
-/
import Spike.Lib.DmemPriv
import Spike.Lib.X64Alloc


namespace Spike.Lib.X64.Alloc

open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib.DmemPriv

variable {Λ : Scc.Sem.Layout} {F : MachineData → Prop} {ms : MemSide isa} {lab : Label → Int64}

/-- **`WordsNone` is kept by a frame step** whose region's cells are off
the heap and the static image (`disjoint_of_sub`: a region inside the entry
stack or the stack pool). -/
theorem wordsNone_fstable {R : Spike.Lib.Region} (hwf : Λ.WF) (hR : R.OK)
    (hh : Scc.Sem.Range.Disjoint ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩ Λ.heap)
    (hd : Scc.Sem.Range.Disjoint ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩ Λ.data) :
    Spike.Lib.X64.FStable R (fun m => WordsNone Λ m.dmem) := by
  intro m m' h hf a ha
  have h1 := (hwf.inSpace Λ.heap (by simp [Scc.Sem.Layout.regions])).2
  have h2 := (hwf.inSpace Λ.data (by simp [Scc.Sem.Layout.regions])).2
  have hRl := hR.lo
  have hRh := hR.hi
  unfold Scc.Sem.Range.Disjoint at hh hd
  unfold WordIn Scc.Sem.Range.contains at ha
  simp only at hh hd
  rw [hf a (by rcases ha with h | h <;> omega) (by rcases ha with h | h <;> omega)]
  exact h a ha

/-- **`FStable` of a conjunction.** -/
theorem fstable_and {R : Spike.Lib.Region} {F₁ F₂ : MachineData → Prop} (h₁ : Spike.Lib.X64.FStable R F₁)
    (h₂ : Spike.Lib.X64.FStable R F₂) :
    Spike.Lib.X64.FStable R (fun m => F₁ m ∧ F₂ m) := fun m m' h hf => ⟨h₁ m m' h.1 hf, h₂ m m' h.2 hf⟩

/-- **The frame `WordsNone ∧ F₀`** for a region whose cells lie in the entry
stack or the stack pool: `FStable` when `F₀` is, and it gives `hwn`. -/
theorem wordsNone_and_fstable {Ent : Scc.Sem.Entry} {R : Spike.Lib.Region} {F₀ : MachineData → Prop}
    (hwf : Λ.WF) (hE : Ent.clear Λ = true) (hR : R.OK)
    (hS : Scc.Sem.Range.Sub ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩ Ent.stack ∨
      Scc.Sem.Range.Sub ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩ Λ.stackPool)
    (h₀ : Spike.Lib.X64.FStable R F₀) :
    Spike.Lib.X64.FStable R (fun m => WordsNone Λ m.dmem ∧ F₀ m) ∧
      ∀ m, WordsNone Λ m.dmem ∧ F₀ m → WordsNone Λ m.dmem :=
  have hd := disjoint_of_sub hwf hE hS
  ⟨fstable_and (wordsNone_fstable hwf hR hd.1 hd.2) h₀, fun _ h => h.1⟩

/-- **`hmem` from `WordsNone`.** -/
theorem hmem_of_wordsNone (hwf : Λ.WF) (hwn : ∀ m, F m → WordsNone Λ m.dmem) (hH : Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ Λ.heap.lo + Λ.heap.size)
    (hctr : WordIn Λ.heap ms.ctr ∨ WordIn Λ.data ms.ctr)
    (hoff : ∀ q : Call, q.OK ms lab → ms.off q.n q.τ ≤ 16 * ms.units q.n q.τ) :
    ∀ q : Call, q.OK ms lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none := by
  intro q hq a ha m hm
  rcases ha with rfl | ⟨o, ho, ha⟩
  · have h1 := (hwf.inSpace Λ.heap (by simp [Scc.Sem.Layout.regions])).2
    have h2 := (hwf.inSpace Λ.data (by simp [Scc.Sem.Layout.regions])).2
    have e : (BitVec.ofNat 64 ms.ctr).toNat = ms.ctr := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      unfold WordIn Scc.Sem.Range.contains at hctr
      rcases hctr with h | h <;> omega
    exact hwn m hm _ (by rw [e]; exact hctr)
  · have h1 := hoff q hq
    have hroom := hq.room
    have hcells := hq.cells
    rw [hq.off] at h1
    rw [Call.hdrAt] at ha
    generalize q.n * (mOf q.h).toNat = k at h1 ha
    refine hwn m hm a (.inl ?_)
    unfold WordIn Scc.Sem.Range.contains
    omega

/-- **`hbuf` from `WordsNone`**, for an allocation of `n` elements of `τ`
whose words at `0` and `8` past the offset lie inside its units. -/
theorem hbuf_of_wordsNone {n : Nat} {τ : CoreLang.Ty} (hwn : ∀ m, F m → WordsNone Λ m.dmem)
    (hH : Λ.heap.lo ≤ ms.heap) (hHi : ms.heap + 16 * ms.cells ≤ Λ.heap.lo + Λ.heap.size)
    (hroom : ms.heap + 16 * ms.cells ≤ 2 ^ 64) (ho : ms.off n τ + 16 ≤ 16 * ms.units n τ) :
    ∀ old : Nat, old + ms.units n τ ≤ ms.cells → ∀ i : Nat, (i = 0 ∨ i = 8) → ∀ m, F m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off n τ + i)) 8 = none := by
  intro old hold i hi m hm
  have e : (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off n τ + i)).toNat = ms.heap + 16 * old + ms.off n τ + i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine hwn m hm _ (.inl ?_)
  rw [e]
  unfold WordIn Scc.Sem.Range.contains
  omega

end Spike.Lib.X64.Alloc
