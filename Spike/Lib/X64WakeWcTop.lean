/-
**`wc_main`'s frame at the top of the first stack and the allocator's free
pcs** (wake.w, x86-64): the layout-generic facts the top case of `hWp`/`hWs`
(`hTopP_R`, `hTopS_R`) needs besides the root's choices.

- `freeN_alloc`, `allocW_free`: every state of `scc_rt_alloc` is at a free
  pc (`WcW.freeN`), so `X0` holds there (`hX0a`).
- `not_ownW`: a word off the arena's cells and its counter, given the
  owned words off them, is owned at no phase of `ownW`.
- `top_addr`, `top_al`, `top_band`, `top_bandA`: `wc_main`'s region at the
  top `wR (RS wcLsw (topS L 0)) wcD` lies `56` bytes below the first
  stack's top, its base 8-aligned, its band `[-240, 8]` (and the
  allocator's `[-160, 8]`) on the stack pool (`BandOnP`, `ownGXW`'s
  producers' `hb`).
- `top_ok`: the region is a region and its frame condition is stable.

x86-64 twin of `Spike/Lib/A64WakeWcWfR.lean`'s `allocW_free`, `not_ownW`
and `rw_top` (namespace `Spike.Lib.X64.WakePh.WcWfR`). **Where this differs
from AArch64**: the allocator's states are free by one range check
(`freeN_alloc`: `scc_rt_alloc` lies in `[4198629, 4198992)`, below every
range `freeN` excludes; A64 per node by `free_dec`); the region is
`wR (RS wcLsw v) wcD` (A64 `wR (swR v (-384) 0) 336`), its facts from
`mainEF_ok` and `WakeM.wR_ok` with `hwf` a premise (A64 at the root);
its base is 8-aligned (A64 16, `hal`); the band facts are new (A64's owned
words are `ownG`, needing none).
-/
import Spike.Lib.X64WakeWcWfRT
import Spike.Lib.X64WakeOwnAllocX
import Spike.Lib.X64WakeOwnWcMidX
import Spike.Lib.X64WakeMainGlue
import Spike.Lib.X64WakeStartFacts
import Spike.Lib.Rt.X64StartEF

namespace Spike.Lib.X64.WakePh.WcWfR

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (FStable swR)
open Spike.Lib.X64.WakePh.MainGlue (FS RS topS tcbS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw wcD_eq)
open Spike.Lib.X64.Flow.WakeM (wR wF)
open Spike.Lib.X64.Flow.WakeWc (wAR)
open Spike.Lib.X64.WakePh.WcW (freeN inCv cv)
open Spike.Lib.X64.Alloc (Call AllocW)
open Spike.Lib (Region)

/-! ## The allocator's free pcs -/

/-- **A pc of `scc_rt_alloc` is free**: `[4198629, 4198992)` lies below
every range `freeN` excludes and the take site. -/
theorem freeN_alloc {x : Nat} (h : 4198629 ≤ x ∧ x < 4198992) : freeN x = true := by
  have hc : 4198992 ≤ cv "scc_rt_alloc_tcb" ∧ 4198992 ≤ cv "scc_rt_thread_init" ∧
      4198992 ≤ cv ".Lwc_main.x20" ∧ 4198992 ≤ cv "scc_rt_abort" ∧
      4198992 ≤ cv Spike.Lib.X64.Flow.Ret0.StackTake.siteL := by
    unfold cv; rw [← codeT_eq]; decide +kernel
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  simp only [freeN, inCv, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Nat.not_le, Nat.not_lt, bne_iff_ne, ne_eq]
  omega

section Free

variable {L : RuntimeLayout} {R : Region} {F : MachineData → Prop}
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
include hlab

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1600000 in
/-- **Every state of `scc_rt_alloc` is at a free pc** (`freeN_alloc` at
each node's pcs, decided from the allocator's labels). -/
theorem allocW_free {ms : Spike.Lib.MemSide isa} {q : Call} :
    AllocW ms q (fun s _ => freeN (pcOf s) = true) (fun _ _ => False) L.exe L.endPc R F := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, -⟩ := Spike.Lib.X64.WakePh.OwnAlloc.alloc_labs hlab (L := L)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
  first
    | exact Spike.Lib.X64.AllocG.blkW_pc (P := fun p => freeN p = true) fun k hk => freeN_alloc (by
        revert k; dsimp only [Spike.Lib.X64.Alloc.N]; simp only [e0, e1, e2, e3, e4, e5, e6]; decide +kernel)
    | exact Spike.Lib.X64.AllocG.nodeW_pc (P := fun p => freeN p = true) (freeN_alloc (by
        dsimp only [Spike.Lib.X64.Alloc.N]; simp only [e0, e1, e2, e3, e4, e5, e6]; decide +kernel))

end Free

/-! ## The owned words off the arena -/

/-- **A word off the arena's cells and its counter is owned at no phase**
of `ownW`: given the four counters and `a` off them, neither the counter
word nor a word in the cells is owned. -/
theorem not_ownW {L : RuntimeLayout} {a : BitVec 64} {heap cells ctr : Nat}
    (hoff : ∀ w', (w' = L.pnA ∨ w' = L.lockA ∨ w' = L.freeNA ∨ w' = L.nextA ∨ w' = a) →
      ¬ (heap ≤ w'.toNat ∧ w'.toNat < heap + 16 * cells) ∧ w' ≠ BitVec.ofNat 64 ctr)
    {w : BitVec 64} (hw : w = BitVec.ofNat 64 ctr ∨ (heap ≤ w.toNat ∧ w.toNat < heap + 16 * cells)) :
    ∀ j v, (⟨w, 8⟩, v) ∉ Spike.Lib.X64.WakePh.ownW L a j := by
  intro j v hm
  simp only [Spike.Lib.X64.WakePh.ownW, Spike.Lib.X64.PhRec.ownOf, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq, Loc.mk.injEq, and_true] at hm
  have key : ∀ w', (w' = L.pnA ∨ w' = L.lockA ∨ w' = L.freeNA ∨ w' = L.nextA ∨ w' = a) → w = w' → False :=
    fun w' hw' he => by
      subst he
      obtain ⟨h1, h2⟩ := hoff _ hw'
      rcases hw with h | h
      · exact h2 h
      · exact h1 h
  rcases hm with (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩
  · exact key _ (.inl rfl) h
  · exact key _ (.inr (.inl rfl)) h
  · exact key _ (.inr (.inr (.inl rfl))) h
  · exact key _ (.inr (.inr (.inr (.inl rfl)))) h
  · exact key _ (.inr (.inr (.inr (.inr rfl)))) h

/-! ## `wc_main`'s region at the top of the first stack -/

section Top

variable (L : RuntimeLayout)

/-- **An address of `wc_main`'s region at the top**: `56` bytes below the
first stack's top, plus the offset. -/
theorem top_addr {k : Int} (h1 : -328 ≤ k) (h2 : k < 56) :
    (((wR (RS wcLsw (topS L 0#64)) wcD).addr k).toNat : Int) = L.stacksA.toNat + 16384 - 56 + k := by
  obtain ⟨eD, eL⟩ := wcD_eq
  have hok : (swR (L.stacksA + 0#64 + 16384#64) (-wcLsw) 0).OK :=
    Spike.Lib.X64.Rt.rt_hokD L (by rw [eL]; decide) (by rw [eL]; decide)
  have e : (wR (RS wcLsw (topS L 0#64)) wcD).addr k =
      (swR (L.stacksA + 0#64 + 16384#64) (-wcLsw) 0).addr (-8 - 0 + (-48 + k)) := by
    simp only [wR, RS, Region.callee_addr, topS]; rw [Spike.Lib.X64.Rt.stacksA_lab0]
  rw [e, Region.addr_toNat_of hok (by simp only [swR]; rw [eL]; omega) (by simp only [swR]; omega)]
  show (((L.stacksA + 0#64 + 16384#64).toNat : Nat) : Int) + _ = _
  rw [Spike.Lib.X64.Rt.top0_toNat]
  omega

/-- **`wc_main`'s region at the top has an 8-aligned base.** -/
theorem top_al : (wR (RS wcLsw (topS L 0#64)) wcD).base.toNat % 8 = 0 := by
  have h := top_addr L (k := 0) (by decide) (by decide)
  have e : ∀ R : Region, R.addr 0 = R.base := fun R => by simp [Region.addr]
  rw [e] at h
  have := L.stacks_al
  omega

/-- **`wc_main`'s band `[-240, 8]` at the top is on the stack pool.** -/
theorem top_band : BandOnP L (wR (RS wcLsw (topS L 0#64)) wcD) (-240) 8 := by
  intro k h1 h2
  have h := top_addr L (k := k) (by omega) (by omega)
  obtain ⟨hs1, hs2⟩ := L.stacks_sub
  simp only at hs1 hs2
  omega

/-- **The allocator's band `[-160, 8]` at the top is on the stack pool.** -/
theorem top_bandA : BandOnP L (wAR (wR (RS wcLsw (topS L 0#64)) wcD)) (-160) 8 := by
  intro k h1 h2
  rw [show (wAR (wR (RS wcLsw (topS L 0#64)) wcD)).addr k = (wR (RS wcLsw (topS L 0#64)) wcD).addr (-80 + k) from
    Region.callee_addr _ _ _ _ _]
  exact top_band L (-80 + k) (by omega) (by omega)

set_option linter.unusedSimpArgs false in
/-- **`wc_main`'s region at the top is a region, its frame condition
stable** (`mainEF_ok`, `WakeM.wR_ok`; the switch's frame condition stable
by `wordsNoneP_swFSL_fstable`). -/
theorem top_ok (hwf : L.Λ.WF) (m0 : MachineData) (σC : Spike.Lib.X64.AS) :
    (wR (RS wcLsw (topS L 0#64)) wcD).OK ∧
      FStable (wR (RS wcLsw (topS L 0#64)) wcD)
        (wF (RS wcLsw (topS L 0#64)) wcD (FS L (Spike.Lib.X64.Rt.rS0 L) wcLsw 0#64 (topS L 0#64)) m0 σC) := by
  have hsub := Spike.Lib.X64.Rt.rS0_sub L
  have hok : (swR (topS L 0#64) (-wcLsw) 0).OK := by
    (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]
    exact Spike.Lib.X64.Rt.rt_hokD _ (by decide) (by decide)
  have hFwS := Spike.Lib.X64.Rt.wordsNoneP_swFSL_fstable
    (a := Spike.Lib.X64.Flow.Ret0.limA (Spike.Lib.X64.Flow.Ret0.tpOf (tcbS L))) (v := topS L 0#64) hwf hsub hok
    (by decide) (by decide)
    (by (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]
        exact Spike.Lib.X64.Rt.rS0_subRD _ (by decide) (by decide))
    (by (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _)
    (by (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
        exact Spike.Lib.X64.Rt.rt_houtD _ (by decide) (by decide))
    (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
  have hR2 := Spike.Lib.X64.Rt.mainEF_ok (tcb := tcbS L) (by decide) (by decide) hok hFwS
  exact Spike.Lib.X64.Flow.WakeM.wR_ok (D := wcD) (by decide) (by decide) hR2.1 hR2.2
    (by show (8 : Int) - wcLsw ≤ -48 - wcD; decide) (by show (0 : Int) ≤ 8; decide) m0 σC

end Top

end Spike.Lib.X64.WakePh.WcWfR

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.allocW_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.allocW_free

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.not_ownW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.not_ownW

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.top_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.top_band

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.top_bandA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.top_bandA

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.top_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.top_ok
