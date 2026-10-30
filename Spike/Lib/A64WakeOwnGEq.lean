/-
**wake.w's global owned-words map at each instance** (AArch64): with the
labels resolved at the canonical base (`hlab`), `ownG` is an instance's
owned words wherever that instance's states are.

- `labs_eq`: the labels `ownG` reads, resolved.
- `Good2a`, `Good2b`, `GoodW`: where `ownG` picks `own2a`, `own2b`, `ownW`.
- `ownG_2a`, `ownG_2b`, `ownG_W`: `ownG` there.
-/
import Spike.Lib.A64WakeOwnG

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

private theorem labN (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {l : Label} {x : Nat}
    (h : codeOf lo wakeProg l = some x) (hx : x < 2 ^ 64) : (L.lab l).toBitVec.toNat = x := by
  rw [hlab l x h]
  show (BitVec.ofNat 64 x).toNat = x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- **The labels `ownG` reads**, resolved at the canonical base. -/
theorem labs_eq (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) :
    (L.lab "scc_rt_alloc_tcb").toBitVec.toNat = 2164712 ∧
    (L.lab "scc_rt_thread_reserve").toBitVec.toNat = 2165132 ∧
    (L.lab "scc_rt_thread_init").toBitVec.toNat = 2165244 ∧
    (L.lab "scc_rt_stack_release").toBitVec.toNat = 2165964 ∧
    (L.lab ".L21_wc_main.sp4").toBitVec.toNat = 2169268 ∧
    (L.lab ".L21_wc_main.sp6").toBitVec.toNat = 2169292 ∧
    (L.lab ".L21_wc_main.stack_grow").toBitVec.toNat = 2169408 ∧
    (L.lab "scc_rt_abort").toBitVec.toNat = 2167996 ∧
    (L.lab "scc_rt_thr_worker").toBitVec.toNat = 2168560 := by
  refine ⟨labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide),
    labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide),
    labN hlab ?_ (by decide)⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- **Where `ownG` picks `own2a`**: `scc_rt_alloc_tcb` on a pool stack,
`wc_main` from `.sp4` to `.sp6`, the abort path from
`scc_rt_alloc_tcb`'s abort on a pool stack. -/
def Good2a (L : RuntimeLayout) (s : State) : Prop :=
  (inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∧ spPool L s) ∨
    inPc L ".L21_wc_main.sp4" ".L21_wc_main.sp6" s ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ x30At L ".L3_scc_rt_alloc_tcb.sp13" s ∧ spPool L s)

/-- **Where `ownG` picks `own2b`**: `scc_rt_thread_init` and
`scc_rt_stack_take` on a pool stack, `wc_main` from `.sp6` to
`.stack_grow`, the abort path from `wc_main`'s spawn failure, off
`scc_rt_alloc_tcb`'s abort on a pool stack. -/
def Good2b (L : RuntimeLayout) (s : State) : Prop :=
  (inPc L "scc_rt_thread_init" "scc_rt_stack_release" s ∧ spPool L s) ∨
    inPc L ".L21_wc_main.sp6" ".L21_wc_main.stack_grow" s ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ x30At L ".L21_wc_main.sp11" s ∧
      ¬ (x30At L ".L3_scc_rt_alloc_tcb.sp13" s ∧ spPool L s))

/-- **Where `ownG` picks `ownW`**: the runtime calls off a pool stack, the
abort path from neither of the second instances' callers, every pc off
`ownG`'s ranges. -/
def GoodW (L : RuntimeLayout) (s : State) : Prop :=
  ((inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∨ inPc L "scc_rt_thread_init" "scc_rt_stack_release" s) ∧
      ¬ spPool L s) ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ ¬ (x30At L ".L3_scc_rt_alloc_tcb.sp13" s ∧ spPool L s) ∧
      ¬ x30At L ".L21_wc_main.sp11" s) ∨
    (¬ inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∧ ¬ inPc L "scc_rt_thread_init" "scc_rt_stack_release" s ∧
      ¬ inPc L ".L21_wc_main.sp4" ".L21_wc_main.stack_grow" s ∧ ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s)

/-- **`ownG` is `own2a`** where it picks it. -/
theorem ownG_2a (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (h : Good2a L s) :
    ownG L a s = own2a L a (ph2a (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eq hlab
  unfold Good2a at h
  unfold ownG
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h, hp⟩ | h | ⟨h, hx, hp⟩
  · rw [ite_eq_left h, ite_eq_left hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h, ite_eq_left ⟨hx, hp⟩]

/-- **`ownG` is `own2b`** where it picks it. -/
theorem ownG_2b (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (h : Good2b L s) :
    ownG L a s = own2b L a (ph2b (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eq hlab
  unfold Good2b at h
  unfold ownG
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h, hp⟩ | h | ⟨h, hx, hn⟩
  · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_left hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h, ite_eq_right hn,
      ite_eq_left hx]

/-- **`ownG` is `ownW`** where it picks it. -/
theorem ownG_W (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (h : GoodW L s) :
    ownG L a s = ownW L a (phW (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eq hlab
  unfold GoodW at h
  unfold ownG
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h | h, hp⟩ | ⟨h, hn, hx⟩ | ⟨h1, h2, h3, h4⟩
  · rw [ite_eq_left h, ite_eq_right hp]
  · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_right hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h, ite_eq_right hn,
      ite_eq_right hx]
  · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h4]

/-- info: 'Spike.Lib.A64.WakePh.ownG_2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.ownG_2b

end Spike.Lib.A64.WakePh
