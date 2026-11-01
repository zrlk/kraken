/-
**`wc_rodata`'s saved return address at `.sp0`** (AArch64): `MainWcP.hra` /
`hello_main_post_segW`'s `hra` (`.sp0`'s `slot (-8)` is `scc_rt_main`'s `.sp0`) at both kinds of `.sp0` states
`hello_start_wc_segW` hands `Jp`: the allocator's return exit (`rX .sp0`, through `hret`) and the fresh-label
landing left to `wc_rodata`'s region (`leave (aR (mR R)) (-48) σ σx` at `rN .call`, through `hJp`). Both read
the prologue's saved `x30` (`rdJ`), which is `scc_rt_main`'s call's return address once the entry block's
invariant `J1` keeps the call's `x30` (`x30_mRdJ0`: the call node `mNC` has it).

- `x30_mRdJ0`: the call node's states (`mRdJ0 (mNC lab J).J σC`) have `x30 = .L1_scc_rt_main.sp0`.
- `hra_ret`: at `rX .sp0`, `slot (-8)` is the saved `x30`.
- `hra_land`: at the landing left to `wc_rodata`'s region, the same.
-/
import Spike.Lib.A64HelloMain

namespace Spike.Lib.A64.HelloPh.RdRa

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (MemSide Region)
open Spike.Lib.A64.Flow (leave)
open Spike.Lib.A64.Flow.Hello1 (mR mRdJ0 mNC aR rdJ)
open Spike.Lib.A64.Flow.HelloRd (rN rX)

/-- `Flow`'s abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {lab : Label → Int64}

/-- **The call node's `x30`** is `scc_rt_main`'s return point `.L1_scc_rt_main.sp0`, kept by `enter`. -/
theorem x30_mRdJ0 {J : FAS → Spike.Lib.Ctl → Prop} {σC σ : FAS} {c : Spike.Lib.Ctl}
    (h : mRdJ0 (mNC lab J).J σC σ c) : σ.regs.X30.toBitVec = (lab ".L1_scc_rt_main.sp0").toBitVec := by
  obtain ⟨rfl, -, hx⟩ := h
  exact hx

/-- **`hra` at the allocator's return exit**: `rX .sp0`'s `slot (-8)` is the prologue's saved `x30`, the call's
return point when the entry block's invariant keeps it (`hx`). -/
theorem hra_ret {ms : MemSide isaLSE2} {lbl : WeakMem.AllocLabel → Option Nat} {J1 : FAS → Spike.Lib.Ctl → Prop}
    (hx : ∀ σe c, J1 σe c → σe.regs.X30.toBitVec = (lab ".L1_scc_rt_main.sp0").toBitVec)
    {σ : FAS} {c : Spike.Lib.Ctl} (h : (rX ms lab lbl J1 .sp0).J σ c) :
    lab ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ.slot (-8)) := by
  obtain ⟨_, ⟨σe, hJ, -, h8⟩, -⟩ := h
  rw [h8, hx σe _ hJ]
  rfl

/-- **`hra` at the fresh-label landing** left to `wc_rodata`'s region: the cell `-8` is outside the allocator's
region `aR (mR R)` (`leave` keeps the caller's), the caller's at `rN .call` the saved `x30`. -/
theorem hra_land {R : Region} {J0 J1 : FAS → Spike.Lib.Ctl → Prop}
    (hx : ∀ σe c, J1 σe c → σe.regs.X30.toBitVec = (lab ".L1_scc_rt_main.sp0").toBitVec)
    {σ σx : FAS} {c0 : Spike.Lib.Ctl} (h : (rN lab J0 J1 .call).J σ c0) :
    lab ".L1_scc_rt_main.sp0" = Int64.ofBitVec ((leave (aR (mR R)) (-48) σ σx).slot (-8)) := by
  obtain ⟨⟨σe, hJ, -, h8⟩, -⟩ := h
  have hoff : ¬ (aR (mR R)).Off (-8 - -48) := by
    simp only [Spike.Lib.Region.Off, aR, Spike.Lib.Region.callee]; omega
  show _ = Int64.ofBitVec (@ite _ ((aR (mR R)).Off (-8 - -48)) (Classical.propDecidable _) _ _)
  rw [ite_eq_right_of_eq_false _ _ (eq_false hoff), h8, hx σe _ hJ]
  rfl

end Spike.Lib.A64.HelloPh.RdRa

/-- info: 'Spike.Lib.A64.HelloPh.RdRa.x30_mRdJ0' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdRa.x30_mRdJ0

/-- info: 'Spike.Lib.A64.HelloPh.RdRa.hra_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdRa.hra_ret

/-- info: 'Spike.Lib.A64.HelloPh.RdRa.hra_land' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdRa.hra_land
