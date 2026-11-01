/-
**hello.w's global owned-words map at each instance** (AArch64;
twin of `A64WakeOwnGEq`): with the labels resolved at hello's base
(`hlab`), `ownGH` is an instance's owned words wherever that instance's
states are.

- `labs_eqH`: the labels `ownGH` reads, resolved in `helloProg`.
- `Good2aH`, `Good2bH`, `GoodWH`: where `ownGH` picks `own2aH`, `own2bH`,
  `ownH` (wake's `Good2a` … at `.L22_wc_main`, the spawn failure `.sp15`).
- `ownGH_2a`, `ownGH_2b`, `ownGH_W`: `ownGH` there.
-/
import Spike.Lib.A64HelloOwnG

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh (inPc spPool x30At)

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

private theorem labNH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {l : Label} {x : Nat}
    (h : codeOf lo SccCode.helloProg l = some x) (hx : x < 2 ^ 64) : (L.lab l).toBitVec.toNat = x := by
  rw [hlab l x h]
  show (BitVec.ofNat 64 x).toNat = x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- **The labels `ownGH` reads**, resolved at the hello's base `lo`. -/
theorem labs_eqH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    (L.lab "scc_rt_alloc_tcb").toBitVec.toNat = 2164748 ∧
    (L.lab "scc_rt_thread_reserve").toBitVec.toNat = 2165168 ∧
    (L.lab "scc_rt_thread_init").toBitVec.toNat = 2165280 ∧
    (L.lab "scc_rt_stack_release").toBitVec.toNat = 2166000 ∧
    (L.lab ".L22_wc_main.sp4").toBitVec.toNat = 2169716 ∧
    (L.lab ".L22_wc_main.sp6").toBitVec.toNat = 2169740 ∧
    (L.lab ".L22_wc_main.stack_grow").toBitVec.toNat = 2169904 ∧
    (L.lab "scc_rt_abort").toBitVec.toNat = 2168032 ∧
    (L.lab "scc_rt_thr_worker").toBitVec.toNat = 2168596 := by
  refine ⟨labNH hlab ?_ (by decide), labNH hlab ?_ (by decide), labNH hlab ?_ (by decide), labNH hlab ?_ (by decide),
    labNH hlab ?_ (by decide), labNH hlab ?_ (by decide), labNH hlab ?_ (by decide), labNH hlab ?_ (by decide),
    labNH hlab ?_ (by decide)⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- **Where `ownGH` picks `own2a`**: `scc_rt_alloc_tcb` on a pool stack,
`wc_main` from `.sp4` to `.sp6`, the abort path from
`scc_rt_alloc_tcb`'s abort on a pool stack. -/
def Good2aH (L : RuntimeLayout) (s : State) : Prop :=
  (inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∧ spPool L s) ∨
    inPc L ".L22_wc_main.sp4" ".L22_wc_main.sp6" s ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ x30At L ".L3_scc_rt_alloc_tcb.sp13" s ∧ spPool L s)

/-- **Where `ownGH` picks `own2b`**: `scc_rt_thread_init` and
`scc_rt_stack_take` on a pool stack, `wc_main` from `.sp6` to
`.stack_grow`, the abort path from `wc_main`'s spawn failure, off
`scc_rt_alloc_tcb`'s abort on a pool stack. -/
def Good2bH (L : RuntimeLayout) (s : State) : Prop :=
  (inPc L "scc_rt_thread_init" "scc_rt_stack_release" s ∧ spPool L s) ∨
    inPc L ".L22_wc_main.sp6" ".L22_wc_main.stack_grow" s ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ x30At L ".L22_wc_main.sp15" s ∧
      ¬ (x30At L ".L3_scc_rt_alloc_tcb.sp13" s ∧ spPool L s))

/-- **Where `ownGH` picks `ownH`**: the runtime calls off a pool stack, the
abort path from neither of the second instances' callers, every pc off
`ownGH`'s ranges. -/
def GoodWH (L : RuntimeLayout) (s : State) : Prop :=
  ((inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∨ inPc L "scc_rt_thread_init" "scc_rt_stack_release" s) ∧
      ¬ spPool L s) ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ ¬ (x30At L ".L3_scc_rt_alloc_tcb.sp13" s ∧ spPool L s) ∧
      ¬ x30At L ".L22_wc_main.sp15" s) ∨
    (¬ inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∧ ¬ inPc L "scc_rt_thread_init" "scc_rt_stack_release" s ∧
      ¬ inPc L ".L22_wc_main.sp4" ".L22_wc_main.stack_grow" s ∧ ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s)

/-- **`ownGH` is `own2a`** where it picks it. -/
theorem ownGH_2a (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (h : Good2aH L s) :
    ownGH L a s = own2aH L a (ph2aH (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eqH hlab
  unfold Good2aH at h
  unfold ownGH
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h, hp⟩ | h | ⟨h, hx, hp⟩
  · rw [ite_eq_left h, ite_eq_left hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h, ite_eq_left ⟨hx, hp⟩]

/-- **`ownGH` is `own2b`** where it picks it. -/
theorem ownGH_2b (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (h : Good2bH L s) :
    ownGH L a s = own2bH L a (ph2bH (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eqH hlab
  unfold Good2bH at h
  unfold ownGH
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h, hp⟩ | h | ⟨h, hx, hn⟩
  · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_left hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h, ite_eq_right hn,
      ite_eq_left hx]

/-- **`ownGH` is `ownH`** where it picks it. -/
theorem ownGH_W (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (h : GoodWH L s) :
    ownGH L a s = ownH L a (phH (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eqH hlab
  unfold GoodWH at h
  unfold ownGH
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h | h, hp⟩ | ⟨h, hn, hx⟩ | ⟨h1, h2, h3, h4⟩
  · rw [ite_eq_left h, ite_eq_right hp]
  · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_right hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h, ite_eq_right hn,
      ite_eq_right hx]
  · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h4]

/-- info: 'Spike.Lib.A64.HelloPh.ownGH_2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ownGH_2b

end Spike.Lib.A64.HelloPh
