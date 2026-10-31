/-
**The second `scc_rt_thread_init` call's frame facts from the box's region**
(x86-64; twin of `Spike/Lib/A64WakeTi2Box.lean`, `hti_W`'s premises):
`wc_main`'s region `R` has its base 56 below the first stack's top
(`R.base + 56 = stacksA + 16384`: `wc_main` entered at `v - 56`,
`X64WakeFrame`), so the frames below it down to `-wcD = -328` and up to the
return address at `8` lie in the first stack, inside the pool
(`bandP_box`), and the second stack `r1Of` lies above the callee's region
`R.callee (-80) (-248) 8` (`hout_box`, `hRS_box`, the premises of
`Rt.threadInit_segWAt`).

- `addr_box`: `R`'s addresses in `[-328, 8]` without wrap;
- `bandP_box`: `BandP L R (-328)`;
- `r1_lo`: the second stack's base `stacksA + 16384`;
- `hout_box`, `hRS_box`: `r1Of` off the callee's region.

**Unlike AArch64**: the base is `v - 56` (A64's `v - 48`, `hb`'s `+ 56`);
the band is `[-328, 8]` (`wcD = 328`, `callK - tiD`, and the return
address; A64's `[-336, 0]`); the callee's region is
`R.callee (-80) (-248) 8` (A64's `R.callee (-80) (-256) 0`).
-/
import Spike.Lib.X64WakeTi2G
import Spike.Lib.Rt.X64RtPreChild

namespace Spike.Lib.X64.WakePh.Ti2

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)

variable {L : RuntimeLayout} {R : Spike.Lib.Region}

/-- **`R`'s addresses in `[-328, 8]`** are `base + k`, without wrap. -/
theorem addr_box (hb : R.base.toNat + 56 = L.stacksA.toNat + 16384) {k : Int} (h1 : -328 ≤ k) (h2 : k ≤ 8) :
    ((R.addr k).toNat : Int) = R.base.toNat + k := by
  have hf := L.pool_fit
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  have he : R.addr k = BitVec.ofInt 64 ((R.base.toNat : Int) + k) := by
    rw [Spike.Lib.Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [he, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.emod_eq_of_lt (by omega) (by omega)]

/-- **The frames `[-328, 8]` around `wc_main`'s entry are on the pool**:
in the first stack, below its top. -/
theorem bandP_box (hb : R.base.toNat + 56 = L.stacksA.toNat + 16384) : BandP L R (-328) := by
  intro k h1 h2
  have ha := addr_box hb h1 h2
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  obtain ⟨s1, s2⟩ := hs
  omega

/-- **The second stack's base** is the first's top. -/
theorem r1_lo : (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).lo = L.stacksA.toNat + 16384 := by
  show (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + 16384#64).toNat = _
  rw [L.lab_stacks]
  have := L.pool_fit
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  obtain ⟨h1, h2⟩ := hs
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 16384) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **The second stack is above the callee's region** `R.callee (-80) (-248) 8`
(word by word, `threadInit_segWAt`'s `hout`). -/
theorem hout_box (hb : R.base.toNat + 56 = L.stacksA.toNat + 16384) :
    ∀ a, a % 8 = 0 → (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).contains a →
      (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-80) (-248) 8).base.toNat + (R.callee (-80) (-248) 8).lo ∨
        ((R.callee (-80) (-248) 8).base.toNat : Int) + (R.callee (-80) (-248) 8).hi ≤ a := by
  intro a _ ha _
  have hc := addr_box hb (k := -80) (by decide) (by decide)
  have hl := r1_lo (L := L)
  simp only [Scc.Sem.Range.contains] at ha
  refine .inr ?_
  show ((R.addr (-80)).toNat : Int) + 8 ≤ a
  omega

/-- **The callee's region's cells are off the second stack**
(`threadInit_segWAt`'s `hRS`). -/
theorem hRS_box (hb : R.base.toNat + 56 = L.stacksA.toNat + 16384) :
    ∀ k, (R.callee (-80) (-248) 8).Off k → ∀ j < 8,
      (R.callee (-80) (-248) 8).addr k + BitVec.ofNat 64 j ∉
        Scc.Sem.Kernel.addrs (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) := by
  intro k hk j hj hm
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
  have hx := List.mem_range.mp hx
  obtain ⟨-, h3, h4⟩ := hk
  simp only [Spike.Lib.Region.callee] at h3 h4
  rw [Spike.Lib.Region.callee_addr] at he
  have ha := addr_box hb (k := -80 + k) (by omega) (by omega)
  have hl := r1_lo (L := L)
  have hf := L.pool_fit
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  obtain ⟨s1, s2⟩ := hs
  have hsz : (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).size = 16384 := rfl
  have h1 := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega)] at h1
  have hlt : (R.addr (-80 + k)).toNat + j < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt] at h1
  rw [hsz] at hx
  have hlt2 : (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).lo + x < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt2] at h1
  omega

end Spike.Lib.X64.WakePh.Ti2

/-- info: 'Spike.Lib.X64.WakePh.Ti2.addr_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.addr_box

/-- info: 'Spike.Lib.X64.WakePh.Ti2.bandP_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.bandP_box

/-- info: 'Spike.Lib.X64.WakePh.Ti2.r1_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.r1_lo

/-- info: 'Spike.Lib.X64.WakePh.Ti2.hout_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.hout_box

/-- info: 'Spike.Lib.X64.WakePh.Ti2.hRS_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.hRS_box
