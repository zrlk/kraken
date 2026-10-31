/-
**wake.w's global owned-words map** (x86-64; the twin of
`Spike/Lib/A64WakeOwnG.lean`): the three instances' owned words (`ownW` at
`phW`, `own2a` at `ph2a`, `own2b` at `ph2b`) picked from the thread state,
by registers and pc, and on the abort path by the return address word.

- `inPc L l₁ l₂ s`: the pc lies in `[lab l₁, lab l₂)`.
- `spPool L s`: `%rsp` lies in `(pool.lo, pool.lo + pool.size]`: on a stack
  taken from the pool (main's after `scc_rt_start`), not on the entry
  stack, which the pool is clear of (`RuntimeLayout.pool_clear`).
- `raAddr L s`, `raAt L l s`: the return address word of the abort path
  (the dispatcher `scc_rt_abort` and the stubs) is `lab l`.
- `ownG L a s`:
  * `scc_rt_alloc_tcb`: `own2a` on a pool stack (`wc_main`'s second call),
    else `ownW` (`scc_rt_start`'s);
  * `scc_rt_thread_init`, `scc_rt_stack_take`: `own2b` on a pool stack,
    else `ownW`;
  * `wc_main` from `.x20` to `.x21`: `own2a`; from `.x21` to `.stk`:
    `own2b`;
  * the abort dispatcher and stubs (`scc_rt_abort` up to
    `scc_rt_thr_worker`): by the caller's return address, `own2a` for
    `scc_rt_alloc_tcb`'s (`.x5`) on a pool stack, `own2b` for `wc_main`'s
    spawn failure (`.x23`), else `ownW`;
  * elsewhere `ownW`.

Where x86-64 differs from AArch64: A64 picks on the abort path by `x30`
(`x30At`), a register. On x86-64 the return address is the word the
caller's `call` pushed, so `raAt` reads the thread's private memory at
`raAddr`, which follows the return address through the abort path's frames
(both the dispatcher and the stubs push `%rbp` at the same frame base `b`,
the return address at `b + 8`): `%rsp` at a function's first instruction
and at each dispatcher `jmp` to a stub (after the `popq %rbp`), `%rsp + 8`
after the `pushq %rbp`, `%rbp + 8` everywhere else. It is read only on the
abort range, which holds no take site, so the take's rewrite of the private
memory leaves `ownG` alone (`SFactsSt2.ownTake`). The other branches are
A64's with the labels renamed.
-/
import Spike.Lib.X64WakeTake2

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (pcOf privLoad)
open Spike.Lib.X64.Rt (RuntimeLayout)

/-- **The pc lies in `[lab l₁, lab l₂)`.** -/
def inPc (L : RuntimeLayout) (l₁ l₂ : Label) (s : State) : Prop :=
  (L.lab l₁).toBitVec.toNat ≤ pcOf s ∧ pcOf s < (L.lab l₂).toBitVec.toNat

instance (L : RuntimeLayout) (l₁ l₂ : Label) (s : State) : Decidable (inPc L l₁ l₂ s) := by
  unfold inPc; infer_instance

/-- **`%rsp` lies on a stack taken from the pool**: in
`(pool.lo, pool.lo + pool.size]`. -/
def spPool (L : RuntimeLayout) (s : State) : Prop :=
  L.Λ.stackPool.lo < s.st.1.regs.rsp.toBitVec.toNat ∧
    s.st.1.regs.rsp.toBitVec.toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

instance (L : RuntimeLayout) (s : State) : Decidable (spPool L s) := by
  unfold spPool; infer_instance

/-- The abort path's functions: the dispatcher and the five stubs. -/
def abFns : List Label :=
  ["scc_rt_abort", "scc_rt_abort_overflow", "scc_rt_abort_heap", "scc_rt_abort_stack", "scc_rt_abort_write",
    "scc_rt_abort_threads"]

/-- The dispatcher's taken tests, whose `jmp` to a stub is 4 bytes in
(`movq %rbp, %rsp; popq %rbp`). -/
def abGos : List Label :=
  [".Lscc_rt_abort.is0", ".Lscc_rt_abort.is2", ".Lscc_rt_abort.is4", ".Lscc_rt_abort.is6", ".Lscc_rt_abort.is8"]

/-- **The pcs where the return address is at `%rsp`**: the functions' first
instructions and the dispatcher's `jmp`s to the stubs. -/
def raSp (L : RuntimeLayout) : List Nat :=
  abFns.map (fun l => (L.lab l).toBitVec.toNat) ++ abGos.map (fun l => (L.lab l + 4).toBitVec.toNat)

/-- **The pcs where the return address is at `%rsp + 8`**: after the
functions' `pushq %rbp`. -/
def raSp8 (L : RuntimeLayout) : List Nat :=
  abFns.map (fun l => (L.lab l + 1).toBitVec.toNat)

/-- **The abort path's return address word.** -/
def raAddr (L : RuntimeLayout) (s : State) : BitVec 64 :=
  if pcOf s ∈ raSp L then s.st.1.regs.rsp.toBitVec
  else if pcOf s ∈ raSp8 L then s.st.1.regs.rsp.toBitVec + 8#64
  else s.st.1.regs.rbp.toBitVec + 8#64

/-- **The abort path's return address is `lab l`** (the word at `raAddr`
in the thread's private memory). -/
def raAt (L : RuntimeLayout) (l : Label) (s : State) : Prop :=
  privLoad s (raAddr L s) = some (L.lab l).toBitVec

instance (L : RuntimeLayout) (l : Label) (s : State) : Decidable (raAt L l s) := by
  unfold raAt; infer_instance

/-- **`raAt` reads the registers, the pc and the private word at `raAddr`
only.** -/
theorem raAt_congr {L : RuntimeLayout} {l : Label} {s s' : State} (hpc : pcOf s' = pcOf s)
    (hr : s'.st.1.regs = s.st.1.regs) (hm : privLoad s' (raAddr L s) = privLoad s (raAddr L s)) :
    raAt L l s' ↔ raAt L l s := by
  have ha : raAddr L s' = raAddr L s := by unfold raAddr; rw [hpc, hr]
  unfold raAt; rw [ha, hm]

/-- **wake.w's global owned-words map.** -/
def ownG (L : RuntimeLayout) (a : BitVec 64) (s : State) : List (Loc × Val) :=
  if inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s then
    if spPool L s then own2a L a (ph2a (pcOf s)) else ownW L a (phW (pcOf s))
  else if inPc L "scc_rt_thread_init" "scc_rt_stack_release" s then
    if spPool L s then own2b L a (ph2b (pcOf s)) else ownW L a (phW (pcOf s))
  else if inPc L ".Lwc_main.x20" ".Lwc_main.x21" s then own2a L a (ph2a (pcOf s))
  else if inPc L ".Lwc_main.x21" ".Lwc_main.stk" s then own2b L a (ph2b (pcOf s))
  else if inPc L "scc_rt_abort" "scc_rt_thr_worker" s then
    if raAt L ".Lscc_rt_alloc_tcb.x5" s ∧ spPool L s then own2a L a (ph2a (pcOf s))
    else if raAt L ".Lwc_main.x23" s then own2b L a (ph2b (pcOf s))
    else ownW L a (phW (pcOf s))
  else ownW L a (phW (pcOf s))

/-- **Off the abort range `ownG` reads the registers and the pc only.** -/
theorem ownG_congr_off {L : RuntimeLayout} {a : BitVec 64} {s s' : State} (hpc : pcOf s' = pcOf s)
    (hr : s'.st.1.regs = s.st.1.regs) (hab : ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s) :
    ownG L a s' = ownG L a s := by
  have hi : ∀ l₁ l₂, inPc L l₁ l₂ s' ↔ inPc L l₁ l₂ s := fun _ _ => by unfold inPc; rw [hpc]
  have hp : spPool L s' ↔ spPool L s := by unfold spPool; rw [hr]
  unfold ownG
  simp only [hi, hp, hpc, hab, ↓reduceIte]

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.raAt_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.raAt_congr

/-- info: 'Spike.Lib.X64.WakePh.ownG_congr_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownG_congr_off
