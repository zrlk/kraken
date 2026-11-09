/-
**`wc_rodata`'s return address at the fresh-label landing** (x86-64; twin of `Spike/Lib/A64HelloRdRa.lean`):
the return address `wc_rodata`'s states hand `Jp` is `scc_rt_main`'s `.x2` at the fresh-label landing left to
`wc_rodata`'s region (`leave (aR (mR R)) (-48) σ σx` at `rN .call`, through `hJp`). It reads the return address
`call wc_rodata` pushed (`rdJ`: slot `0` kept from the entry), which is `.x2` once the entry block's invariant
`J1` keeps the call's (`x30_mRdJ0`: the call node `mNC` has it at slot `-80`, `enter`'s slot `0`).

- `x30_mRdJ0`: the call node's states (`mRdJ0 (mNC lab R J).J σC`) have slot `0` `= .Lscc_rt_main.x0`.
- `hra_land`: at the landing left to `wc_rodata`'s region, slot `0` is the same.

## Differences from the AArch64 version

- `call` pushes the return address, so it is read at the stack top (slot `0`) rather than from `x30` and the
  prologue's saved `x30` at `-8`; the name `x30_mRdJ0` is kept for the twin. The return label is
  `.Lscc_rt_main.x0` (AArch64's `.L1_scc_rt_main.sp0`), and the nodes take the region (`mNC lab R J`,
  `rN lab R J0 J1`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `hra_ret`.
-/
import Spike.Lib.X64HelloMain

namespace Spike.Lib.X64.HelloPh.RdRa

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (MemSide Region)
open Spike.Lib.X64 (leave enter)
open Spike.Lib.X64.Flow.Hello1 (mR mRdJ0 mNC aR rdJ)
open Spike.Lib.X64.Flow.HelloRd (rN)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {lab : Label → Int64}

/-- **The call node's return address** is `scc_rt_main`'s return point `.Lscc_rt_main.x0`, at slot `0` past
`enter`. -/
theorem x30_mRdJ0 {R : Region} {J : FAS → Spike.Lib.Ctl → Prop} {σC σ : FAS} {c : Spike.Lib.Ctl}
    (h : mRdJ0 (mNC lab R J).J σC σ c) : σ.slot 0 = (lab ".Lscc_rt_main.x0").toBitVec := by
  obtain ⟨rfl, -, -, -, -, -, -, -, -, h80⟩ := h
  exact h80

/-- **`hra` at the fresh-label landing** left to `wc_rodata`'s region: the cell `0` is outside the allocator's
region `aR (mR R)` (`leave` keeps the caller's), the caller's at `rN .call` the return address kept from the
entry. -/
theorem hra_land {R : Region} {J0 J1 : FAS → Spike.Lib.Ctl → Prop}
    (hx : ∀ σe c, J1 σe c → σe.slot 0 = (lab ".Lscc_rt_main.x0").toBitVec)
    {σ σx : FAS} {c0 : Spike.Lib.Ctl} (h : (rN lab (mR R) J0 J1 .call).J σ c0) :
    lab ".Lscc_rt_main.x0" = Int64.ofBitVec ((leave (aR (mR R)) (-48) σ σx).slot 0) := by
  obtain ⟨⟨σe, hJ, h0, -⟩, -⟩ := h
  have hoff : ¬ (aR (mR R)).Off (0 - -48) := by
    simp only [Spike.Lib.Region.Off, aR, Spike.Lib.Region.callee]; omega
  show _ = Int64.ofBitVec (@ite _ ((aR (mR R)).Off (0 - -48)) (Classical.propDecidable _) _ _)
  rw [ite_eq_right_of_eq_false _ _ (eq_false hoff), h0, hx σe _ hJ]
  rfl

end Spike.Lib.X64.HelloPh.RdRa

/-- info: 'Spike.Lib.X64.HelloPh.RdRa.x30_mRdJ0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdRa.x30_mRdJ0

/-- info: 'Spike.Lib.X64.HelloPh.RdRa.hra_land' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdRa.hra_land
