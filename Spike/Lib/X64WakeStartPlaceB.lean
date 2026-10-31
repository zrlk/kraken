/-
**`scc_rt_start`'s band off the stack pool at the entry stack** (x86-64):
the premise `hband : BandOffP L R (-240) (-48)` of `OwnSt.startTcbX` (the
first `scc_rt_alloc_tcb` call inside `WSX`) at `scc_rt_start`'s region
`R := entryR E`, for an admissible entry `E` of the layout: the region's
words at offsets `[-240, -48]` lie in the entry stack (`entryR_sub`), which
the pool is clear of (`pool_clear`). The part of
`Spike/Lib/A64WakeStartPlace.lean` that reduces the callee frame's band to
the entry region (A64's private `offE`, used there for `BandT`).

- `offE`: a word `-k` bytes below the entry `sp` (`-65536 < k < 0`) is off the
  stack pool.
- `bandOffP_entry`: `BandOffP L (entryR E) (-240) (-48)`.

Where x86-64 differs from AArch64: the callee frame's band is the caller's
`BandOffP L R (-240) (-48)` (`OwnSt.bandT_of`; A64 states `BandT` of the
callee region directly from `offE` at `-240`, `-304`); `offE` is public here
and its `x` is `R.addr k` (A64's `base + ofInt (-d)`). The segment
`wake_start_wc_place` itself is not twinned here: it instantiates
`MainGlue.wake_start_wc_segW`, which has no x86-64 twin yet.
-/
import Spike.Lib.X64WakeOwnStartG

namespace Spike.Lib.X64.WakePh.StartPlace

open Spike.Lib.X64.Rt (RuntimeLayout entryR)
open Spike.Lib (Region)

/-- **A word `-k` below the entry `sp` is off the stack pool** (`k` within
the entry region; the pool is clear of the entry stack, `pool_clear`). -/
theorem offE {L : RuntimeLayout} {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) {k : Int} (h0 : -65536 < k) (h1 : k < 0) :
    ¬ (L.Λ.stackPool.lo < ((entryR E).addr k).toNat ∧
      ((entryR E).addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size) := by
  have hb := Spike.Lib.X64.Rt.entryR_base hE
  have := Spike.Lib.X64.Rt.entry_sp hE
  have hd := Spike.Lib.X64.Rt.pool_clear L hE.1
  have hs := Spike.Lib.X64.Rt.entryR_sub hE
  have ha := Region.addr_toNat_of (Spike.Lib.X64.Rt.entryR_ok hE) (k := k) (by show (-65536 : Int) ≤ k; omega)
    (by show k < 0; omega)
  have hspd : E.sp = E.stack.lo + E.stack.size := rfl
  simp only [Scc.Sem.Range.Disjoint, Scc.Sem.Range.Sub] at hd hs
  rw [hb] at ha
  omega

/-- **`startTcbX`'s `hband` at the entry region**: `scc_rt_start`'s words
at offsets `[-240, -48]` of `entryR E` are off the stack pool. -/
theorem bandOffP_entry {L : RuntimeLayout} {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) :
    Spike.Lib.X64.WakePh.BandOffP L (entryR E) (-240) (-48) :=
  fun _ h1 h2 => offE hE (by omega) (by omega)

end Spike.Lib.X64.WakePh.StartPlace

/-- info: 'Spike.Lib.X64.WakePh.StartPlace.bandOffP_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlace.bandOffP_entry
