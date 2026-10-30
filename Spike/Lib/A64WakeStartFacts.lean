/-
**What `wake_start_wc_segW`'s landing gives `wc_main`'s entry** (AArch64): read off its post (the heap abort inside `wc_main`, reached
from `wc_main`'s entry invariant `wJ0 (wNC _ (JS _ _ _)).J σC`).

- `startPost_facts`: the base `v` of the new stack is the top of stack
  `k0` (`swF`). So `wc_main`'s region `wR (swR top (-Lsw) 0) D` is based
  48 below the top (b), and its depth is `D` (c). At every entry state
  of `wc_main`, `x0` is the first TCB `pinA + 0 + 8` (a): `scc_rt_main`
  saved its `x0` (`mainE0`) at slot `-48`, and `wNC` passes that slot in
  `x0`.
- `wcEntry_x0`: (a) alone, for any caller state `σC`.
- `dLsw_ok`: `D = 336`, `Lsw = 384` meet `wake_start_wc_segW`'s depth
  premises. With them `wc_main`'s region has `lo = -336`, and the new
  stack's region (`384` deep) fits stack `k0` (`16384`).
-/
import Spike.Lib.A64WakeMainGlue

namespace Spike.Lib.A64.WakePh.StartFacts

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Ret0 (pinA stacksA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (wX)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)

/-- **(a) `x0` at `wc_main`'s entry is the first TCB**: `pinA + 0 + 8`,
for every entry state of `wJ0 (wNC _ (JS L k0 c0)).J σC`. -/
theorem wcEntry_x0 {L : RuntimeLayout} {k0 : BitVec 64} {c0 : Ctl} {σC σe : Spike.Lib.A64.Flow.AS} {c : Ctl}
    (h : wJ0 (wNC L.lab (JS L k0 c0)).J σC σe c) : σe.regs.X0.toBitVec = pinA L.lab + 0#64 + 8#64 := by
  obtain ⟨rfl, ⟨σm, hm, -, -, h48, -⟩, hx0, -⟩ := h
  exact hx0.trans (h48.trans hm.2)

/-- **The landing's facts**: at `wake_start_wc_segW`'s post, the new stack's
base is the top of stack `k0`. `wc_main`'s region is based 48 below it (b)
and is `D` deep (c). Every entry state of `wc_main` has `x0` the first
TCB (a). -/
theorem startPost_facts {L : RuntimeLayout} {rS : Scc.Sem.Range} {Lsw D : Int} {k0 : BitVec 64} {c0 : Ctl}
    {ms : Spike.Lib.MemSide isaLSE2} {s : State} {c : Ctl}
    (h : ∃ v m0 σC,
      Spike.Lib.A64.Flow.At L.exe L.endPc (wR (swR v (-Lsw) 0) D) (wF (swR v (-Lsw) 0) D (FS L rS Lsw k0 v) m0 σC)
        (wX ms L.lab (wJ0 (wNC L.lab (JS L k0 c0)).J σC) .abort) s c ∧
      TP (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)) s) :
    ∃ m0 σC,
      Spike.Lib.A64.Flow.At L.exe L.endPc (wR (swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0) D)
        (wF (swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0) D (FS L rS Lsw k0 (stacksA L.lab + k0 + 16384#64)) m0 σC)
        (wX ms L.lab (wJ0 (wNC L.lab (JS L k0 c0)).J σC) .abort) s c ∧
      TP (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)) s ∧
      (∀ σe c', wJ0 (wNC L.lab (JS L k0 c0)).J σC σe c' → σe.regs.X0.toBitVec = pinA L.lab + 0#64 + 8#64) ∧
      (wR (swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0) D).base + 48#64 = stacksA L.lab + k0 + 16384#64 ∧
      (wR (swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0) D).lo = -D := by
  obtain ⟨v, m0, σC, hA, hT⟩ := h
  have hv : v = stacksA L.lab + k0 + 16384#64 := hA.2.2.2.2.choose_spec.2.1.1.2.1.1
  subst hv
  refine ⟨m0, σC, hA, hT, fun _ _ h => wcEntry_x0 h, ?_, rfl⟩
  simp only [Spike.Lib.Region.callee, Spike.Lib.Region.addr, swR]
  bv_decide

/-- **`D = 336`, `Lsw = 384`** meet `wake_start_wc_segW`'s depth premises,
and the new stack's region fits stack `k0`. -/
theorem dLsw_ok : (336 : Int) % 16 = 0 ∧ 240 ≤ (336 : Int) ∧ 48 + (336 : Int) ≤ 384 ∧ (384 : Int) % 8 = 0 ∧
    (384 : Int) ≤ 16384 := by decide

end Spike.Lib.A64.WakePh.StartFacts

/-- info: 'Spike.Lib.A64.WakePh.StartFacts.startPost_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartFacts.startPost_facts
