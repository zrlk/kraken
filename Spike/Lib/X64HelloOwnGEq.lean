/-
**hello.w's global owned-words map at each instance** (x86-64; the twin of
`Spike/Lib/A64HelloOwnGEq.lean`): with the labels resolved at the canonical
base (`hlab`), `ownGH` is an instance's owned words wherever that
instance's states are.

- `labs_eqH`: the labels `ownGH` reads, resolved.
- `Good2aH`, `Good2bH`, `GoodWH`: where `ownGH` picks `own2aH`, `own2bH`,
  `ownH`.
- `ownGH_2a`, `ownGH_2b`, `ownGH_W`: `ownGH` there.

## Differences from the AArch64 version

- `hlab` resolves labels by `Scc.Sem.X64.codeLabel lo helloCells` (A64:
  `codeOf lo helloProg`).
- The abort path's selection is by `raAt` (the return address word,
  `Spike/Lib/X64WakeOwnG.lean`) for A64's `x30At`; the labels are hello's
  x86-64 ones (`.x24`, `.x25`, `.stk`, `.x6`, `.x27` for A64's
  `.L22_wc_main.sp4`, `.sp6`, `.stack_grow`, `.L3_scc_rt_alloc_tcb.sp13`,
  `.L22_wc_main.sp15`).
- The proofs are `X64WakeOwnGEq`'s at hello's addresses.
-/
import Spike.Lib.X64HelloOwnG

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (inPc spPool raAt)

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

private theorem labN (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {x : Nat} (h : codeLabel lo helloCells l = some x) (hx : x < 2 ^ 64) : (L.lab l).toBitVec.toNat = x := by
  rw [hlab l x h]
  show (BitVec.ofNat 64 x).toNat = x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- **The labels `ownGH` reads**, resolved at the canonical base. -/
theorem labs_eqH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (L.lab "scc_rt_alloc_tcb").toBitVec.toNat = 4199029 ∧
    (L.lab "scc_rt_thread_reserve").toBitVec.toNat = 4199484 ∧
    (L.lab "scc_rt_thread_init").toBitVec.toNat = 4199582 ∧
    (L.lab "scc_rt_stack_release").toBitVec.toNat = 4200327 ∧
    (L.lab ".Lwc_main.x2").toBitVec.toNat = 4203787 ∧
    (L.lab ".Lwc_main.x3").toBitVec.toNat = 4203812 ∧
    (L.lab ".Lwc_main.stk").toBitVec.toNat = 4203986 ∧
    (L.lab "scc_rt_abort").toBitVec.toNat = 4202524 ∧
    (L.lab "scc_rt_thr_worker").toBitVec.toNat = 4203010 := by
  refine ⟨labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide),
    labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide), labN hlab ?_ (by decide),
    labN hlab ?_ (by decide)⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- **Where `ownGH` picks `own2aH`**: `scc_rt_alloc_tcb` on a pool stack,
`wc_main` from `.x24` to `.x25`, the abort path from
`scc_rt_alloc_tcb`'s abort on a pool stack. -/
def Good2aH (L : RuntimeLayout) (s : State) : Prop :=
  (inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∧ spPool L s) ∨
    inPc L ".Lwc_main.x2" ".Lwc_main.x3" s ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ raAt L ".Lscc_rt_alloc_tcb.x0" s ∧ spPool L s)

/-- **Where `ownGH` picks `own2bH`**: `scc_rt_thread_init` and
`scc_rt_stack_take` on a pool stack, `wc_main` from `.x25` to `.stk`, the
abort path from `wc_main`'s spawn failure, off `scc_rt_alloc_tcb`'s abort on
a pool stack. -/
def Good2bH (L : RuntimeLayout) (s : State) : Prop :=
  (inPc L "scc_rt_thread_init" "scc_rt_stack_release" s ∧ spPool L s) ∨
    inPc L ".Lwc_main.x3" ".Lwc_main.stk" s ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ raAt L ".Lwc_main.x5" s ∧
      ¬ (raAt L ".Lscc_rt_alloc_tcb.x0" s ∧ spPool L s))

/-- **Where `ownGH` picks `ownH`**: the runtime calls off a pool stack, the
abort path from neither of the second instances' callers, every pc off
`ownGH`'s ranges. -/
def GoodWH (L : RuntimeLayout) (s : State) : Prop :=
  ((inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∨ inPc L "scc_rt_thread_init" "scc_rt_stack_release" s) ∧
      ¬ spPool L s) ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ ¬ (raAt L ".Lscc_rt_alloc_tcb.x0" s ∧ spPool L s) ∧
      ¬ raAt L ".Lwc_main.x5" s) ∨
    (¬ inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∧ ¬ inPc L "scc_rt_thread_init" "scc_rt_stack_release" s ∧
      ¬ inPc L ".Lwc_main.x2" ".Lwc_main.stk" s ∧ ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s)

/-- **`ownGH` is `own2aH`** where it picks it. -/
theorem ownGH_2a (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (h : Good2aH L s) :
    ownGH L a s = own2aH L a (ph2aH (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eqH hlab
  unfold Good2aH at h
  unfold ownGH
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h, hp⟩ | h | ⟨h, hx, hp⟩
  · rw [ite_eq_left h, ite_eq_left hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left h, ite_eq_left ⟨hx, hp⟩]

/-- **`ownGH` is `own2bH`** where it picks it. -/
theorem ownGH_2b (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (h : Good2bH L s) :
    ownGH L a s = own2bH L a (ph2bH (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eqH hlab
  unfold Good2bH at h
  unfold ownGH
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h, hp⟩ | h | ⟨h, hx, hn⟩
  · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_left hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left h, ite_eq_right hn, ite_eq_left hx]

/-- **`ownGH` is `ownH`** where it picks it. -/
theorem ownGH_W (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (h : GoodWH L s) :
    ownGH L a s = ownH L a (phH (pcOf s)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := labs_eqH hlab
  unfold GoodWH at h
  unfold ownGH
  simp only [inPc, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h ⊢
  rcases h with ⟨h | h, hp⟩ | ⟨h, hn, hx⟩ | ⟨h1, h2, h3, h4⟩
  · rw [ite_eq_left h, ite_eq_right hp]
  · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_right hp]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left h, ite_eq_right hn, ite_eq_right hx]
  · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h4]

/-- info: 'Spike.Lib.X64.HelloPh.labs_eqH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.labs_eqH

/-- info: 'Spike.Lib.X64.HelloPh.ownGH_2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ownGH_2a

/-- info: 'Spike.Lib.X64.HelloPh.ownGH_2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ownGH_2b

/-- info: 'Spike.Lib.X64.HelloPh.ownGH_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ownGH_W

end Spike.Lib.X64.HelloPh
