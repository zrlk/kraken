/-
**The start's glue facts** (x86-64; twin of `Spike/Lib/A64WakeStartGlue.lean`): the pieces that
join `StartWf.startEW_W0S`, `Rt.startEF_segW`
and `MainWf.mainPreWW_W0S` with `WakeWc.wake_wc_entry_segJm`, the frame
after the switch strengthened by `DmemPriv.WordsNone` (the cell set)
through `Rt.startEF_segW`'s `Fw`.

- `StartEW.toF`: `StartEW` gives `StartEWF` at any `Fw` (only the nodes
  after the switch see the frame, narrowed).
- `hmemB_of_wordsNone`, `hcellB_of_wordsNone`: `wake_wc_entry_segJm`'s
  `hmem0`/`hcell0` at a box call (`Call.OKB`) from `WordsNone` (as
  `Alloc.hmem_of_wordsNone`/`hbuf_of_wordsNone`), the cells' mapping a
  premise.
- `x0W_of_freeN`: `X0W` at a free pc, the take pc the site's.
- `room_gW`: the first TCB's limit word under wake's value invariant
  `wakeG (GOf2 L m0) cT` is at most any bound past the guard.

**Unlike AArch64**: `SwEWF` narrows both nodes after the switch
(`xorl %ebp, %ebp` and the call block) to `Fw ∧ swFSL …`, so `StartEW.toF`
narrows both (AArch64: the call block only); `StartEW`'s `scc_rt_start`
part is stated for every frame condition of its callee region
(`StartEW.s`), and `toF` maps it pointwise. `X0W` also asks, at the take pc,
the site's range and main's stack not taken: vacuous at a free pc as on
AArch64. The limit word's thread pointer is `tpOf` (AArch64:
`UInt64.ofBitVec`).
-/
import Spike.Lib.X64WakeMainWf
import Spike.Lib.X64WakeJ0
import Spike.Lib.X64WakeX0
import Spike.Lib.X64WakeWcPreWI
import Spike.Lib.Rt.X64StartEF
import Spike.Lib.Rt.X64SwWordsNone
import Spike.Lib.X64WakeGOf2
import Spike.Lib.WakeG

namespace Spike.Lib.X64.WakePh.StartGlue

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.DmemPriv (WordsNone WordIn)
open Spike.Lib.X64.WakePh.WcW (freeN)

/-! ## The frame after the switch -/

/-- **`StartEW` is `StartEWF` at any `Fw`**: the nodes after the switch,
inside `W` under `swFSL …`, are so under `Fw ∧ swFSL …`. -/
theorem StartEW.toF {W : Spike.Lib.Frag isa} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop} {rS : Scc.Sem.Range} {n0 k0 : BitVec 64}
    {c0 : Spike.Lib.Ctl} {L : Int} {Fw : _root_.Mem 64 → Prop} {xr : Label}
    (h : Spike.Lib.X64.Rt.StartEW W K exe endPc R F rS n0 k0 c0 L xr) :
    Spike.Lib.X64.Rt.StartEWF W K exe endPc R F Fw rS n0 k0 c0 L xr :=
  ⟨h.e, fun F' hFs hKs hF' =>
    ⟨(h.s F' hFs hKs hF').s1, (h.s F' hFs hKs hF').s2,
      ⟨(h.s F' hFs hKs hF').s3.sw,
        fun v s c ⟨a1, a2, a3, a4, σ, a5, a6, a7⟩ => (h.s F' hFs hKs hF').s3.xor v s c
          ⟨a1, a2, a3, a4, σ, a5, a6.2, a7⟩,
        fun v s σ c a1 a2 a3 a4 a5 a6 => (h.s F' hFs hKs hF').s3.blk v s σ c a1 a2 a3 a4 a5 a6.2⟩⟩⟩

/-! ## `hmem0`, `hcell0` from `WordsNone` -/

section Cells

variable {Λ : Scc.Sem.Layout} {F : MachineData → Prop} {ms : Spike.Lib.MemSide isa} {lab : Label → Int64}

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
    generalize q.n * (Spike.Lib.X64.Alloc.mOf q.h).toNat = k at h1 ha
    refine hwn m hm a (.inl ?_)
    unfold WordIn Scc.Sem.Range.contains
    omega

/-- **`hcell0` from `WordsNone`**: the box's cell unmapped in private
memory (`Alloc.hbuf_of_wordsNone` at `0`), its mapping (`hmp`, a memory
side fact) given. -/
theorem hcellB_of_wordsNone (hwn : ∀ m, F m → WordsNone Λ m.dmem) (hH : Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ Λ.heap.lo + Λ.heap.size) (hroom : ms.heap + 16 * ms.cells ≤ 2 ^ 64)
    {P : Call → Prop}
    (hoB : ∀ q : Spike.Lib.X64.Flow.WakeWc.AGB ms lab, P q.1 → ms.off 1 q.1.τ + 16 ≤ 16 * ms.units 1 q.1.τ)
    (hmp : ∀ q : Spike.Lib.X64.Flow.WakeWc.AGB ms lab, P q.1 → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true) :
    ∀ q : Spike.Lib.X64.Flow.WakeWc.AGB ms lab, P q.1 → ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none :=
  fun q hP o h1 h2 => ⟨hmp q hP o h1 h2, fun m hm => by
    simpa using Spike.Lib.X64.Alloc.hbuf_of_wordsNone hwn hH hHi hroom (hoB q hP) o h2 0 (.inl rfl) m hm⟩

end Cells

/-! ## `X0W` at a free pc -/

/-- **`X0W` at a free pc** (`StartWf`'s `hX0`): off the `clone`'s pc and
off the take pc `a`, the take site's. -/
theorem x0W_of_freeN {L : RuntimeLayout} {a : Int64}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (ha : a.toBitVec.toNat = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    ∀ s, freeN (pcOf s) = true → Spike.Lib.X64.WakeWf.X0W L a s :=
  fun _ h => ⟨Spike.Lib.X64.Flow.WakeWc.ne_clonePc_of_freeN hlab h,
    fun he => absurd (he.trans ha) (Spike.Lib.X64.WakePh.WcW.site_ne_of_freeN hlab h)⟩

/-! ## The limit word's room -/

/-- **The first TCB's limit word under wake's value invariant** is at most
any `b` past the first stack's guard (`hb`): it holds the limit
`stacksA + 4096` or its initial `0` (`hinit`), the root's word `cT` being
another (`hcT`). -/
theorem room_gW {L : RuntimeLayout} {m0 : Memory} {cT : Loc} {b : Nat}
    (hcT : cT ≠ ⟨L.pinA + 16#64, 8⟩) (hinit : m0.initVal ⟨L.pinA + 16#64, 8⟩ = 0)
    (hb : L.stacksA.toNat + 4096 ≤ b) :
    ∀ v : Val, Spike.Lib.WakeG.wakeG (Spike.Lib.X64WakeGOf2.GOf2 L m0) cT
      ⟨Spike.Lib.X64.Flow.Ret0.limA (Spike.Lib.X64.Flow.Ret0.tpOf (L.pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ b := by
  intro v hv
  rw [Spike.Lib.X64.Rt.limA_tcb0 L] at hv
  rcases (show Spike.Lib.WakeG.wakeG (Spike.Lib.X64WakeGOf2.GOf2 L m0) cT ⟨L.pinA + 16#64, 8⟩ v from hv) with h | h
  · exact absurd h.symm hcT
  rcases Spike.Lib.X64.PhRec.gOf_lim (Spike.Lib.X64WakeGOf2.gOf_of_gOf2 h) with rfl | rfl
  · have := L.pool_fit
    obtain ⟨h1, h2⟩ := L.stacks_sub
    simp only at h1 h2
    simp only [Spike.Lib.X64.PhRec.limV, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128),
      BitVec.setWidth_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [hinit]
    simp

/-- **The room at `scc_rt_main`'s entry** at the first stack's top less
`Z` (`Z ≤ 12288`): `room_gW` at `b = (stacksA + 16384 - Z).toNat`. -/
theorem room_gW_top {L : RuntimeLayout} {m0 : Memory} {cT : Loc} {Z : Int64}
    (hcT : cT ≠ ⟨L.pinA + 16#64, 8⟩) (hinit : m0.initVal ⟨L.pinA + 16#64, 8⟩ = 0)
    (hZ : Z.toBitVec.toNat ≤ 12288) :
    ∀ v : Val, Spike.Lib.WakeG.wakeG (Spike.Lib.X64WakeGOf2.GOf2 L m0) cT
      ⟨Spike.Lib.X64.Flow.Ret0.limA (Spike.Lib.X64.Flow.Ret0.tpOf (L.pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + 0#64 + 16384#64 - Z.toBitVec).toNat := by
  refine room_gW hcT hinit ?_
  have := L.pool_fit
  obtain ⟨h1, h2⟩ := L.stacks_sub
  simp only at h1 h2
  rw [L.lab_stacks, BitVec.add_zero, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end Spike.Lib.X64.WakePh.StartGlue

/-- info: 'Spike.Lib.X64.WakePh.StartGlue.StartEW.toF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartGlue.StartEW.toF

/-- info: 'Spike.Lib.X64.WakePh.StartGlue.hmemB_of_wordsNone'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.X64.WakePh.StartGlue.hmemB_of_wordsNone

/-- info: 'Spike.Lib.X64.WakePh.StartGlue.hcellB_of_wordsNone'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.X64.WakePh.StartGlue.hcellB_of_wordsNone

/-- info: 'Spike.Lib.X64.WakePh.StartGlue.x0W_of_freeN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartGlue.x0W_of_freeN

/-- info: 'Spike.Lib.X64.WakePh.StartGlue.room_gW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartGlue.room_gW

/-- info: 'Spike.Lib.X64.WakePh.StartGlue.room_gW_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartGlue.room_gW_top
