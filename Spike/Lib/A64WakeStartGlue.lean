/-
**The start's glue facts** (AArch64): the pieces that join
`StartWf.startEW_W0S`, `Rt.startEF_segW` and `MainWf.mainPreWW_W0S` with
`WakeWc.wake_wc_entry_segJm`, the frame after the switch strengthened by
`DmemPriv.WordsNone` (the cell set) through `Rt.startEF_segW`'s `Fw`.

- `StartEW.toF`: `StartEW` gives `StartEWF` at any `Fw` (only the block
  after the switch sees the frame, narrowed).
- `hmemB_of_wordsNone`, `hcellB_of_wordsNone`: `wake_wc_entry_segJm`'s
  `hmem0`/`hcell0` at a box call (`Call.OKB`) from `WordsNone` (as
  `Alloc.hmem_of_wordsNone`/`hbuf_of_wordsNone`), the cells' mapping a
  premise.
- `x0W_of_freeN`: `X0W` at a free pc, the take pc the site's.
- `room_gW`: the first TCB's limit word under wake's value invariant
  `wakeG (GOf2 L m0) cT` is at most any bound past the guard.
-/
import Spike.Lib.A64WakeMainWf
import Spike.Lib.A64WakeJ0
import Spike.Lib.A64WakeX0
import Spike.Lib.A64WakeWcPreWI
import Spike.Lib.Rt.A64StartEF
import Spike.Lib.Rt.A64SwWordsNone
import Spike.Lib.WakeGOf2

namespace Spike.Lib.A64.WakePh.StartGlue

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.DmemPriv (WordsNone WordIn)
open Spike.Lib.A64.WakePh.WcW (freeN)

/-! ## The frame after the switch -/

/-- **`StartEW` is `StartEWF` at any `Fw`**: the block after the switch,
inside `W` under `swFSL …`, is so under `Fw ∧ swFSL …`. -/
theorem StartEW.toF {W : Spike.Lib.Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop} {rS : Scc.Sem.Range} {n0 k0 : BitVec 64}
    {c0 : Spike.Lib.Ctl} {L : Int} {Fw : _root_.Mem 64 → Prop} {P : MachineData → Prop}
    (h : Spike.Lib.A64.Rt.StartEW W K exe endPc R F rS n0 k0 c0 L P) :
    Spike.Lib.A64.Rt.StartEWF W K exe endPc R F Fw rS n0 k0 c0 L P :=
  ⟨h.e, h.s1, h.s2, ⟨h.s3.sw, fun v s σ c a1 a2 a3 a4 a5 a6 a7 => h.s3.blk v s σ c a1 a2 a3 a4 a5 a6.2 a7⟩⟩

/-! ## `hmem0`, `hcell0` from `WordsNone` -/

section Cells

variable {Λ : Scc.Sem.Layout} {F : MachineData → Prop} {ms : Spike.Lib.MemSide isaLSE2} {lab : Label → Int64}

/-- **`hmem0` at a box call from `WordsNone`** (`Alloc.hmem_of_wordsNone`
at `Call.OKB`): the counter in the heap or the image (`hctr`), the headers
inside the heap's cells (`hH`, `hHi`, `hoff`). -/
theorem hmemB_of_wordsNone (hwf : Λ.WF) (hwn : ∀ m, F m → WordsNone Λ m.dmem) (hH : Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ Λ.heap.lo + Λ.heap.size)
    (hctr : WordIn Λ.heap ms.ctr ∨ WordIn Λ.data ms.ctr)
    (hoff : ∀ q : Call, q.OKB ms lab → ms.off q.n q.τ ≤ 16 * ms.units q.n q.τ) :
    ∀ q : Call, q.OKB ms lab → ∀ a : BitVec 64,
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
    have hroom := hq.toS.room
    have hcells := hq.toS.cells
    rw [hq.toS.off] at h1
    rw [Call.hdrAt] at ha
    generalize q.n * (Spike.Lib.A64.Alloc.mOf q.h).toNat = k at h1 ha
    refine hwn m hm a (.inl ?_)
    unfold WordIn Scc.Sem.Range.contains
    omega

/-- **`hcell0` from `WordsNone`**: the box's cell unmapped in private
memory (`Alloc.hbuf_of_wordsNone` at `0`), its mapping (`hmp`, a memory
side fact) given. -/
theorem hcellB_of_wordsNone (hwn : ∀ m, F m → WordsNone Λ m.dmem) (hH : Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ Λ.heap.lo + Λ.heap.size) (hroom : ms.heap + 16 * ms.cells ≤ 2 ^ 64)
    {P : Call → Prop}
    (hoB : ∀ q : Spike.Lib.A64.Flow.WakeWc.AGB ms lab, P q.1 → ms.off 1 q.1.τ + 16 ≤ 16 * ms.units 1 q.1.τ)
    (hmp : ∀ q : Spike.Lib.A64.Flow.WakeWc.AGB ms lab, P q.1 → ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true) :
    ∀ q : Spike.Lib.A64.Flow.WakeWc.AGB ms lab, P q.1 → ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none :=
  fun q hP o h1 h2 => ⟨hmp q hP o h1 h2, fun m hm => by
    simpa using Spike.Lib.A64.Alloc.hbuf_of_wordsNone hwn hH hHi hroom (hoB q hP) o h2 0 (.inl rfl) m hm⟩

end Cells

/-! ## `X0W` at a free pc -/

/-- **`X0W` at a free pc** (`StartWf`'s `hX0`): off the `clone`'s pc and
off the take pc `a`, the take site's. -/
theorem x0W_of_freeN {L : RuntimeLayout} {a : Int64}
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (ha : a.toBitVec.toNat = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    ∀ s, freeN (pcOf s) = true → Spike.Lib.A64.WakeWf.X0W L a s :=
  fun _ h => ⟨Spike.Lib.A64.WakePh.WcW.ne_clonePc_of_freeN hlab h,
    fun he => absurd (he.trans ha) (Spike.Lib.A64.WakePh.WcW.site_ne_of_freeN hlab h)⟩

/-! ## The limit word's room -/

/-- **The first TCB's limit word under wake's value invariant** is at most
any `b` past the first stack's guard (`hb`): it holds the limit
`stacksA + 4096` or its initial `0` (`hinit`), the root's word `cT` being
another (`hcT`). -/
theorem room_gW {L : RuntimeLayout} {m0 : Memory} {cT : Loc} {b : Nat}
    (hcT : cT ≠ ⟨L.pinA + 16#64, 8⟩) (hinit : m0.initVal ⟨L.pinA + 16#64, 8⟩ = 0)
    (hb : L.stacksA.toNat + 4096 ≤ b) :
    ∀ v : Val, Spike.Lib.WakeG.wakeG (Spike.Lib.WakeGOf2.GOf2 L m0) cT
      ⟨Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64)), 8⟩ v → (v.setWidth 64).toNat ≤ b := by
  intro v hv
  rw [Spike.Lib.A64.Rt.limA_tcb0 L] at hv
  rcases (show Spike.Lib.WakeG.wakeG (Spike.Lib.WakeGOf2.GOf2 L m0) cT ⟨L.pinA + 16#64, 8⟩ v from hv) with h | h
  · exact absurd h.symm hcT
  rcases Spike.Lib.A64.PhRec.gOf_lim (Spike.Lib.WakeGOf2.gOf_of_gOf2 h) with rfl | rfl
  · have := L.pool_fit
    obtain ⟨h1, h2⟩ := L.stacks_sub
    simp only at h1 h2
    simp only [Spike.Lib.A64.PhRec.limV, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128),
      BitVec.setWidth_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [hinit]
    simp

/-- **The room at `scc_rt_main`'s entry** at the first stack's top less
`Z` (`Z ≤ 12288`): `room_gW` at `b = (stacksA + 16384 - Z).toNat`. -/
theorem room_gW_top {L : RuntimeLayout} {m0 : Memory} {cT : Loc} {Z : Int64}
    (hcT : cT ≠ ⟨L.pinA + 16#64, 8⟩) (hinit : m0.initVal ⟨L.pinA + 16#64, 8⟩ = 0)
    (hZ : Z.toBitVec.toNat ≤ 12288) :
    ∀ v : Val, Spike.Lib.WakeG.wakeG (Spike.Lib.WakeGOf2.GOf2 L m0) cT
      ⟨Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Spike.Lib.A64.Flow.Ret0.stacksA L.lab + 0#64 + 16384#64 - Z.toBitVec).toNat := by
  refine room_gW hcT hinit ?_
  have := L.pool_fit
  obtain ⟨h1, h2⟩ := L.stacks_sub
  simp only at h1 h2
  rw [L.lab_stacks, BitVec.add_zero, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end Spike.Lib.A64.WakePh.StartGlue

/-- info: 'Spike.Lib.A64.WakePh.StartGlue.StartEW.toF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartGlue.StartEW.toF

/-- info: 'Spike.Lib.A64.WakePh.StartGlue.hmemB_of_wordsNone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartGlue.hmemB_of_wordsNone

/-- info: 'Spike.Lib.A64.WakePh.StartGlue.hcellB_of_wordsNone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartGlue.hcellB_of_wordsNone

/-- info: 'Spike.Lib.A64.WakePh.StartGlue.x0W_of_freeN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartGlue.x0W_of_freeN

/-- info: 'Spike.Lib.A64.WakePh.StartGlue.room_gW_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartGlue.room_gW_top
