/-
**`scc_rt_start`'s layout arithmetic at any main-thread depth** (H2): the
premises of `startU_segW` (`Spike/Lib/Rt/A64Segs.lean`) about the switch
region `[top - d, top)`, stated as lemmas of a `RuntimeLayout` for every depth
`0 ≤ d ≤ 16384`. `rt_hok`, `rS0_subR` and `rt_hout` (`Spike/Lib/Rt/A64Layout.lean`)
are the case `d = 80`, which is `ret0`'s; `scc_rt_main`'s frame plus its user
function's (`mc.Z + D`) depends on the program.

- `rt_hokD`: the region does not wrap.
- `rS0_subRD`: the region lies in the first stack, word by word.
- `rt_houtD`: the first TCB's limit word lies off the region. It is a runtime
  word clear of the pool, and the pool holds the region.
- `stacksA_lab0`, `pinA_lab0`: the label forms the segments use
  (`Ret0.stacksA lab + 0#64`) are the record's addresses.
- **Oracle**: at `d = 80` these are `rt_hok`, `rS0_subR` and `rt_hout`
  (`d80` below).
-/
import Spike.Lib.Rt.A64Layout

namespace Spike.Lib.A64.Rt

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (limA)

section StartD

variable (L : RuntimeLayout)

/-- The segments' form of the first stack's base is the record's. -/
theorem stacksA_lab0 : Ret0.stacksA L.lab + 0#64 = L.stacksA + 0#64 := by
  rw [L.lab_stacks]

/-- The segments' form of the first TCB's header is the record's. -/
theorem pinA_lab0 : Ret0.pinA L.lab + 0#64 = L.pinA + 0#64 := by
  rw [L.lab_pin]

/-- **`hok` at depth `d`**: the switch region does not wrap. -/
theorem rt_hokD {d : Int} (hd0 : 0 ≤ d) (hd : d ≤ 16384) : (swR (L.stacksA + 0#64 + 16384#64) (-d) 0).OK := by
  have := L.pool_fit
  obtain ⟨h1, h2⟩ := L.stacks_sub
  simp only at h1 h2
  refine ⟨?_, ?_⟩ <;> simp only [swR, top0_toNat] <;> omega

/-- **`hsub` at depth `d`**: the switch region lies in `rS0`, word by word. -/
theorem rS0_subRD {d : Int} (hd0 : 0 ≤ d) (hd : d ≤ 16384) :
    ∀ k, (swR (L.stacksA + 0#64 + 16384#64) (-d) 0).Off k →
      ((swR (L.stacksA + 0#64 + 16384#64) (-d) 0).addr k).toNat % 8 = 0 ∧
      (rS0 L).contains ((swR (L.stacksA + 0#64 + 16384#64) (-d) 0).addr k).toNat ∧
      (rS0 L).contains (((swR (L.stacksA + 0#64 + 16384#64) (-d) 0).addr k).toNat + 7) := by
  intro k hk
  have ha := Region.addr_toNat (rt_hokD L hd0 hd) hk
  have h16 := L.stacks_al
  obtain ⟨h8, h1, h2⟩ := hk
  simp only [swR] at h1 h2
  rw [show (swR (L.stacksA + 0#64 + 16384#64) (-d) 0).base = L.stacksA + 0#64 + 16384#64 from rfl,
    top0_toNat] at ha
  have h0 : (L.stacksA + 0#64).toNat = L.stacksA.toNat := by rw [BitVec.add_zero]
  simp only [Scc.Sem.Range.contains, h0]
  omega

/-- **`hout` at depth `d`**: the first TCB's limit word lies off the switch
region. -/
theorem rt_houtD {d : Int} (hd0 : 0 ≤ d) (hd : d ≤ 16384) :
    ((limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64))).toNat : Int) + 8 ≤
        (L.stacksA + 0#64 + 16384#64).toNat + -d ∨
      ((L.stacksA + 0#64 + 16384#64).toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64))).toNat := by
  rw [limA_tcb0, top0_toNat]
  have hp := L.words_pool _ (L.fld_mem (i := 1) (by decide))
  obtain ⟨h1, h2⟩ := L.stacks_sub
  simp only [Clear] at hp
  simp only at h1 h2
  omega

/-! ## Oracle: depth 80 -/

example : rt_hok L = rt_hokD L (d := 80) (by decide) (by decide) := rfl
example : rS0_subR L = rS0_subRD L (d := 80) (by decide) (by decide) := rfl
example : rt_hout L = rt_houtD L (d := 80) (by decide) (by decide) := rfl

end StartD

end Spike.Lib.A64.Rt
