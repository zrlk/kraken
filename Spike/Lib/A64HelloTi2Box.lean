/-
**The second `scc_rt_thread_init` call's frame facts from hello's box
region** (AArch64; the hello twin of `Spike/Lib/A64WakeTi2Box.lean`, the
`hti` premises at hello's `wc_main`): `wc_main`'s region `R` has its base 80
below the first stack's top (`HelloHMid.BoxPureH`'s
`R.base + 80 = stacksA + 16384`). So the frames below it down to `-400`
(`wc_main`'s call at `-144`, `scc_rt_thread_init`'s frame of 256) lie in the
first stack, inside the pool (`bandP_boxH`), and the second stack `r1Of`
lies above the callee's region `R.callee (-144) (-256) 0` (`hout_boxH`,
`hRS_boxH`).

- `addr_boxH`: `R`'s addresses in `[-400, 0]` without wrap;
- `bandP_boxH`: `BandP L R (-400)`;
- `hout_boxH`, `hRS_boxH`: `r1Of` off the callee's region.

The second stack's base is wake's layout-generic `Ti2.r1_lo`.
-/
import Spike.Lib.A64WakeTi2Box

namespace Spike.Lib.A64.HelloPh.Ti2

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh.Ti2 (BandP r1_lo)

variable {L : RuntimeLayout} {R : Spike.Lib.Region}

/-- **`R`'s addresses in `[-400, 0]`** are `base + k`, without wrap. -/
theorem addr_boxH (hb : R.base.toNat + 80 = L.stacksA.toNat + 16384) {k : Int} (h1 : -400 ≤ k) (h2 : k ≤ 0) :
    ((R.addr k).toNat : Int) = R.base.toNat + k := by
  have hB := R.base.isLt
  have he : R.addr k = BitVec.ofInt 64 ((R.base.toNat : Int) + k) := by
    rw [Spike.Lib.Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [he, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.emod_eq_of_lt (by omega) (by omega)]

/-- **The frames `[-400, 0]` below `wc_main`'s entry are on the pool**: in
the first stack, below its top. -/
theorem bandP_boxH (hb : R.base.toNat + 80 = L.stacksA.toNat + 16384) : BandP L R (-400) := by
  intro k h1 h2
  have ha := addr_boxH hb h1 h2
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  obtain ⟨s1, s2⟩ := hs
  omega

/-- **The second stack is above the callee's region** `R.callee (-144) (-256) 0`
(word by word, `threadInit_segWA`'s `hout`). -/
theorem hout_boxH (hb : R.base.toNat + 80 = L.stacksA.toNat + 16384) :
    ∀ a, a % 8 = 0 → (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).contains a →
      (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-144) (-256) 0).base.toNat + (R.callee (-144) (-256) 0).lo ∨
        ((R.callee (-144) (-256) 0).base.toNat : Int) + (R.callee (-144) (-256) 0).hi ≤ a := by
  intro a _ ha _
  have hc := addr_boxH hb (k := -144) (by decide) (by decide)
  have hl := r1_lo (L := L)
  simp only [Scc.Sem.Range.contains] at ha
  refine .inr ?_
  show ((R.addr (-144)).toNat : Int) + 0 ≤ a
  omega

/-- **The callee's region's cells are off the second stack** (`threadInit_segWA`'s
`hRS`). -/
theorem hRS_boxH (hb : R.base.toNat + 80 = L.stacksA.toNat + 16384) :
    ∀ k, (R.callee (-144) (-256) 0).Off k → ∀ j < 8,
      (R.callee (-144) (-256) 0).addr k + BitVec.ofNat 64 j ∉
        Scc.Sem.Kernel.addrs (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) := by
  intro k hk j hj hm
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
  have hx := List.mem_range.mp hx
  obtain ⟨-, h3, h4⟩ := hk
  simp only [Spike.Lib.Region.callee] at h3 h4
  rw [Spike.Lib.Region.callee_addr] at he
  have ha := addr_boxH hb (k := -144 + k) (by omega) (by omega)
  have hl := r1_lo (L := L)
  have hf := L.pool_fit
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  obtain ⟨s1, s2⟩ := hs
  have hsz : (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).size = 16384 := rfl
  have h1 := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega)] at h1
  have hlt : (R.addr (-144 + k)).toNat + j < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt] at h1
  rw [hsz] at hx
  have hlt2 : (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).lo + x < 2 ^ 64 := by
    have := (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).lo
    omega
  rw [Nat.mod_eq_of_lt hlt2] at h1
  omega

end Spike.Lib.A64.HelloPh.Ti2

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.addr_boxH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.addr_boxH

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.bandP_boxH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.bandP_boxH

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.hout_boxH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.hout_boxH

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.hRS_boxH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.hRS_boxH
