/-
**wake.w's global owned-words map** (AArch64): the three instances' owned
words (`ownW` at `phW`, `own2a` at `ph2a`, `own2b` at `ph2b`) picked from the
thread state, by registers and pc only (the take rewrites the private memory
arbitrarily, `SFactsSt2.ownTake`, so no part of the private memory can pick).

- `inPc L l₁ l₂ s`: the pc lies in `[lab l₁, lab l₂)`.
- `spPool L s`: `sp` lies in `(pool.lo, pool.lo + pool.size]`: on a stack
  taken from the pool (main's `r0` after `scc_rt_start`), not on the entry
  stack, which the pool is clear of (`RuntimeLayout.pool_clear`).
- `x30At L l s`: `x30` is `lab l` (the return address a `bl` left).
- `ownG L a s`:
  * `scc_rt_alloc_tcb`: `own2a` on a pool stack (`wc_main`'s second call),
    else `ownW` (`scc_rt_start`'s);
  * `scc_rt_thread_init`, `scc_rt_stack_take`: `own2b` on a pool stack,
    else `ownW`;
  * `wc_main` from `.sp4` to `.sp6`: `own2a`; from `.sp6` to `.stack_grow`:
    `own2b`;
  * the abort dispatcher and stubs (`scc_rt_abort` up to
    `scc_rt_thr_worker`): by the caller's return address, `own2a` for
    `scc_rt_alloc_tcb`'s on a pool stack, `own2b` for `wc_main`'s spawn
    failure, else `ownW`;
  * elsewhere `ownW`.
-/
import Spike.Lib.A64WakeTake2

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout)

/-- **The pc lies in `[lab l₁, lab l₂)`.** -/
def inPc (L : RuntimeLayout) (l₁ l₂ : Label) (s : State) : Prop :=
  (L.lab l₁).toBitVec.toNat ≤ pcOf s ∧ pcOf s < (L.lab l₂).toBitVec.toNat

instance (L : RuntimeLayout) (l₁ l₂ : Label) (s : State) : Decidable (inPc L l₁ l₂ s) := by
  unfold inPc; infer_instance

/-- **`sp` lies on a stack taken from the pool**: in
`(pool.lo, pool.lo + pool.size]`. -/
def spPool (L : RuntimeLayout) (s : State) : Prop :=
  L.Λ.stackPool.lo < s.st.1.regs.SP.toBitVec.toNat ∧
    s.st.1.regs.SP.toBitVec.toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

instance (L : RuntimeLayout) (s : State) : Decidable (spPool L s) := by
  unfold spPool; infer_instance

/-- **`x30` is `lab l`.** -/
def x30At (L : RuntimeLayout) (l : Label) (s : State) : Prop :=
  s.st.1.regs.X30.toBitVec = (L.lab l).toBitVec

instance (L : RuntimeLayout) (l : Label) (s : State) : Decidable (x30At L l s) := by
  unfold x30At; infer_instance

/-- **wake.w's global owned-words map.** -/
def ownG (L : RuntimeLayout) (a : BitVec 64) (s : State) : List (Loc × Val) :=
  if inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s then
    if spPool L s then own2a L a (ph2a (pcOf s)) else ownW L a (phW (pcOf s))
  else if inPc L "scc_rt_thread_init" "scc_rt_stack_release" s then
    if spPool L s then own2b L a (ph2b (pcOf s)) else ownW L a (phW (pcOf s))
  else if inPc L ".L21_wc_main.sp4" ".L21_wc_main.sp6" s then own2a L a (ph2a (pcOf s))
  else if inPc L ".L21_wc_main.sp6" ".L21_wc_main.stack_grow" s then own2b L a (ph2b (pcOf s))
  else if inPc L "scc_rt_abort" "scc_rt_thr_worker" s then
    if x30At L ".L3_scc_rt_alloc_tcb.sp13" s ∧ spPool L s then own2a L a (ph2a (pcOf s))
    else if x30At L ".L21_wc_main.sp11" s then own2b L a (ph2b (pcOf s))
    else ownW L a (phW (pcOf s))
  else ownW L a (phW (pcOf s))

end Spike.Lib.A64.WakePh
