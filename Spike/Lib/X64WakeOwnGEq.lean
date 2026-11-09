/-
**wake.w's global owned-words map at each instance** (x86-64; the twin of
`Spike/Lib/A64WakeOwnGEq.lean`): with the labels resolved at the canonical
base (`hlab`), `ownG` is an instance's owned words wherever that instance's
states are.

- `labs_eq`: the labels `ownG` reads, resolved.
- `Good2a`, `Good2b`, `GoodW`: where `ownG` picks `own2a`, `own2b`, `ownW`.
- `ownG_2a`, `ownG_2b`, `ownG_W`: `ownG` there.

Where x86-64 differs from AArch64: the abort path's selection is by
`raAt` (the return address word, `Spike/Lib/X64WakeOwnG.lean`) for A64's
`x30At`; the labels are x86-64's (`.x20`, `.x21`, `.stk`, `.x5`, `.x23` for
A64's `.sp4`, `.sp6`, `.stack_grow`, `.sp13`, `.sp11`).
-/
import Spike.Lib.X64WakeOwnG

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

private theorem labN (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {x : Nat} (h : codeLabel lo wakeCells l = some x) (hx : x < 2 ^ 64) : (L.lab l).toBitVec.toNat = x := by
  rw [hlab l x h]
  show (BitVec.ofNat 64 x).toNat = x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- **The labels `ownG` reads**, resolved at the canonical base. -/
theorem labs_eq (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (L.lab "scc_rt_alloc_tcb").toBitVec.toNat = 4198992 ∧
    (L.lab "scc_rt_thread_reserve").toBitVec.toNat = 4199447 ∧
    (L.lab "scc_rt_thread_init").toBitVec.toNat = 4199545 ∧
    (L.lab "scc_rt_stack_release").toBitVec.toNat = 4200290 ∧
    (L.lab ".Lwc_main.x2").toBitVec.toNat = 4203410 ∧
    (L.lab ".Lwc_main.x3").toBitVec.toNat = 4203435 ∧
    (L.lab ".Lwc_main.stk").toBitVec.toNat = 4203552 ∧
    (L.lab "scc_rt_abort").toBitVec.toNat = 4202487 ∧
    (L.lab "scc_rt_thr_worker").toBitVec.toNat = 4202973 := by
  refine ⟨labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide),
    labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide),
    labN hlab ?_ (by decide)⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- **Where `ownG` picks `own2a`**: `scc_rt_alloc_tcb` on a pool stack,
`wc_main` from `.x20` to `.x21`, the abort path from
`scc_rt_alloc_tcb`'s abort on a pool stack. -/
def Good2a (L : RuntimeLayout) (s : State) : Prop :=
  (inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∧ spPool L s) ∨
    inPc L ".Lwc_main.x2" ".Lwc_main.x3" s ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ raAt L ".Lscc_rt_alloc_tcb.x0" s ∧ spPool L s)

/-- **Where `ownG` picks `own2b`**: `scc_rt_thread_init` and
`scc_rt_stack_take` on a pool stack, `wc_main` from `.x21` to `.stk`, the
abort path from `wc_main`'s spawn failure, off `scc_rt_alloc_tcb`'s abort on
a pool stack. -/
def Good2b (L : RuntimeLayout) (s : State) : Prop :=
  (inPc L "scc_rt_thread_init" "scc_rt_stack_release" s ∧ spPool L s) ∨
    inPc L ".Lwc_main.x3" ".Lwc_main.stk" s ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ raAt L ".Lwc_main.x5" s ∧
      ¬ (raAt L ".Lscc_rt_alloc_tcb.x0" s ∧ spPool L s))

/-- **Where `ownG` picks `ownW`**: the runtime calls off a pool stack, the
abort path from neither of the second instances' callers, every pc off
`ownG`'s ranges. -/
def GoodW (L : RuntimeLayout) (s : State) : Prop :=
  ((inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∨ inPc L "scc_rt_thread_init" "scc_rt_stack_release" s) ∧
      ¬ spPool L s) ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ ¬ (raAt L ".Lscc_rt_alloc_tcb.x0" s ∧ spPool L s) ∧
      ¬ raAt L ".Lwc_main.x5" s) ∨
    (¬ inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∧ ¬ inPc L "scc_rt_thread_init" "scc_rt_stack_release" s ∧
      ¬ inPc L ".Lwc_main.x2" ".Lwc_main.stk" s ∧ ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s)

/-- **`ownG` is `own2a`** where it picks it. -/
theorem ownG_2a (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (h : Good2a L s) :
    ownG L a s = own2a L a (ph2a (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eq hlab
  unfold Good2a at h
  unfold ownG
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h, hp⟩ | h | ⟨h, hx, hp⟩
  · rw [ite_eq_left h, ite_eq_left hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left h, ite_eq_left ⟨hx, hp⟩]

/-- **`ownG` is `own2b`** where it picks it. -/
theorem ownG_2b (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (h : Good2b L s) :
    ownG L a s = own2b L a (ph2b (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eq hlab
  unfold Good2b at h
  unfold ownG
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h, hp⟩ | h | ⟨h, hx, hn⟩
  · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_left hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left h, ite_eq_right hn, ite_eq_left hx]

/-- **`ownG` is `ownW`** where it picks it. -/
theorem ownG_W (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (h : GoodW L s) :
    ownG L a s = ownW L a (phW (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eq hlab
  unfold GoodW at h
  unfold ownG
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h | h, hp⟩ | ⟨h, hn, hx⟩ | ⟨h1, h2, h3, h4⟩
  · rw [ite_eq_left h, ite_eq_right hp]
  · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_right hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left h, ite_eq_right hn, ite_eq_right hx]
  · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h4]

/-- info: 'Spike.Lib.X64.WakePh.labs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.labs_eq

/-- info: 'Spike.Lib.X64.WakePh.ownG_2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownG_2a

/-- info: 'Spike.Lib.X64.WakePh.ownG_2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownG_2b

/-- info: 'Spike.Lib.X64.WakePh.ownG_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownG_W

end Spike.Lib.X64.WakePh
