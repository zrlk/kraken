/-
**The abort frame's band on or off the pool stacks** (AArch64, wake's code-5
aborts): the 48 bytes below a caller's `sp` (`R.callee kc (-48) 0` of
`Abort.Disp.seg_jabort5W`) lie on a pool stack when the caller's `sp` does
with 48 bytes of room above the stack's base (`bandIn_of`), and off the pool
when the caller runs on the entry stack (`bandOut_of`: the entry stack is
clear of the pool, `RuntimeLayout.pool_clear`).

- `callee_addr_toNat`: an address of the callee band.
- `bandIn_of`: `BandIn` from a range of the pool holding the band.
- `bandOut_of`: `BandOut` for a band inside the entry stack's region.
-/
import Spike.Lib.A64WakeOwnGAb

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout entryR)

variable {L : RuntimeLayout}

/-- **An address of the callee band**: `kc + k` of a non-wrapping `R`, with
`kc − 48` and `kc` inside `R`. -/
theorem callee_addr_toNat {R : Region} (hR : R.OK) {kc : Int} (hlo : R.lo ≤ kc + -48) (hhi : kc < R.hi)
    {k : Int} (h1 : -48 ≤ k) (h2 : k ≤ 0) :
    (((R.callee kc (-48) 0).addr k).toNat : Int) = R.base.toNat + kc + k := by
  have he : (R.callee kc (-48) 0).addr k = R.addr (kc + k) := by
    simp only [Region.callee, Region.addr_add]; rfl
  rw [he, Region.addr_toNat_of hR (by omega) (by omega), Int.add_assoc]

/-- **The band on a pool stack**: a range `rS` of the pool holding the
caller's `sp` with 48 bytes of room above its base. -/
theorem bandIn_of {R : Region} (hR : R.OK) {kc : Int} (hlo : R.lo ≤ kc + -48) (hhi : kc < R.hi)
    {rS : Scc.Sem.Range} (hsub : rS.Sub L.Λ.stackPool) (hroom : (rS.lo : Int) + 48 < R.base.toNat + kc)
    (htop : (R.base.toNat : Int) + kc ≤ rS.lo + rS.size) : BandIn L (R.callee kc (-48) 0) := by
  intro k h1 h2
  have ha := callee_addr_toNat hR hlo hhi h1 h2
  unfold Scc.Sem.Range.Sub at hsub
  omega

/-- **The band off the pool on the entry stack**: the band strictly above the
entry region's base (`hlo`) and at most its top. -/
theorem bandOut_of {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) {kc : Int} (hlo : (entryR E).lo < kc + -48)
    (hhi : kc < (entryR E).hi + 1) : BandOut L ((entryR E).callee kc (-48) 0) := by
  intro k h1 h2
  have hR := Spike.Lib.A64.Rt.entryR_ok hE
  have hb := Spike.Lib.A64.Rt.entryR_base hE
  have hs := Spike.Lib.A64.Rt.entryR_sub hE
  have hp := Spike.Lib.A64.Rt.pool_clear L hE.1
  have hlo' : (entryR E).lo = -65536 := rfl
  have hhi' : (entryR E).hi = 0 := rfl
  rw [hlo'] at hlo
  rw [hhi'] at hhi
  have he : ((entryR E).callee kc (-48) 0).addr k = (entryR E).addr (kc + k) := by
    simp only [Region.callee, Region.addr_add]; rfl
  have hsp := Spike.Lib.A64.Rt.entry_sp hE
  have ha : ((((entryR E).callee kc (-48) 0).addr k).toNat : Int) = E.sp + (kc + k) := by
    rw [he]
    have he2 : (entryR E).addr (kc + k) = BitVec.ofInt 64 (((entryR E).base.toNat : Int) + (kc + k)) := by
      simp only [Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [hb] at he2
    rw [he2, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
      Int.emod_eq_of_lt (by omega) (by omega)]
  have hspd : E.sp = E.stack.lo + E.stack.size := rfl
  simp only [Scc.Sem.Range.Sub, Scc.Sem.Range.Disjoint] at hs hp
  omega

/-- info: 'Spike.Lib.A64.WakePh.bandIn_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.bandIn_of

/-- info: 'Spike.Lib.A64.WakePh.bandOut_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.bandOut_of

end Spike.Lib.A64.WakePh
