/-
**hello.w's global owned-words map** (x86-64; the twin of
`Spike/Lib/A64HelloOwnG.lean`): the three instances' owned words (`ownH` at
`phH`, `own2aH` at `ph2aH`, `own2bH` at `ph2bH`) picked from the thread
state, by registers and pc, and on the abort path by the return address
word, with wake's x86-64 tests `WakePh.inPc`, `WakePh.spPool`, `WakePh.raAt`
at hello's labels.

- `ownGH L a s`:
  * `scc_rt_alloc_tcb`: `own2aH` on a pool stack (`wc_main`'s second call),
    else `ownH` (`scc_rt_start`'s);
  * `scc_rt_thread_init`, `scc_rt_stack_take`: `own2bH` on a pool stack,
    else `ownH`;
  * `wc_main` from `.x24` to `.x25`: `own2aH`; from `.x25` to `.stk`:
    `own2bH`;
  * the abort dispatcher and stubs (`scc_rt_abort` up to
    `scc_rt_thr_worker`): by the caller's return address, `own2aH` for
    `scc_rt_alloc_tcb`'s (`.x6`) on a pool stack, `own2bH` for `wc_main`'s
    spawn failure (`.x27`), else `ownH`;
  * elsewhere `ownH`.

## Differences from the AArch64 version

- On the abort path the map tests the return address word (`WakePh.raAt`,
  read from the thread's private memory) instead of `x30` (`x30At`), as in
  `X64WakeOwnG`.
- The labels are those of hello's x86-64 listing: `wc_main`'s `.x24`,
  `.x25`, `.stk`, `.x27` (A64's `.L22_wc_main.sp4`, `.sp6`, `.stack_grow`,
  `.sp15`) and `scc_rt_alloc_tcb`'s `.x6` (A64's `.sp13`).
- A64's `ownGH_labs` (dead) is not twinned; the resolved labels are pinned
  by `ownGH_labs` here, stated over `codeLabel` at `helloCells`, which the
  equation lemmas of `X64HelloOwnGEq` build on.
- `ownGH_congr_off` (the twin of `WakePh.ownG_congr_off`) is added.
-/
import Spike.Lib.X64HelloOwn2
import Spike.Lib.X64WakeOwnG

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (inPc spPool raAt)

/-- **hello.w's global owned-words map.** -/
def ownGH (L : RuntimeLayout) (a : BitVec 64) (s : State) : List (Loc × Val) :=
  if inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s then
    if spPool L s then own2aH L a (ph2aH (pcOf s)) else ownH L a (phH (pcOf s))
  else if inPc L "scc_rt_thread_init" "scc_rt_stack_release" s then
    if spPool L s then own2bH L a (ph2bH (pcOf s)) else ownH L a (phH (pcOf s))
  else if inPc L ".Lwc_main.x24" ".Lwc_main.x25" s then own2aH L a (ph2aH (pcOf s))
  else if inPc L ".Lwc_main.x25" ".Lwc_main.stk" s then own2bH L a (ph2bH (pcOf s))
  else if inPc L "scc_rt_abort" "scc_rt_thr_worker" s then
    if raAt L ".Lscc_rt_alloc_tcb.x6" s ∧ spPool L s then own2aH L a (ph2aH (pcOf s))
    else if raAt L ".Lwc_main.x27" s then own2bH L a (ph2bH (pcOf s))
    else ownH L a (phH (pcOf s))
  else ownH L a (phH (pcOf s))

/-- **The labels `ownGH` tests, at `lo` in `helloCells`** (in the order of
the map; each range nonempty). -/
theorem ownGH_labs :
    ["scc_rt_alloc_tcb", "scc_rt_thread_reserve", "scc_rt_thread_init", "scc_rt_stack_release",
      ".Lwc_main.x24", ".Lwc_main.x25", ".Lwc_main.stk", "scc_rt_abort", "scc_rt_thr_worker",
      ".Lscc_rt_alloc_tcb.x6", ".Lwc_main.x27"].map (Scc.Sem.X64.codeLabel lo SccCode.helloCells) =
    [some 4199029, some 4199484, some 4199582, some 4200327, some 4203749, some 4203774, some 4203948,
      some 4202486, some 4202972, some 4199282, some 4203909] := by
  decide +kernel

/-- **Off the abort range `ownGH` reads the registers and the pc only.** -/
theorem ownGH_congr_off {L : RuntimeLayout} {a : BitVec 64} {s s' : State} (hpc : pcOf s' = pcOf s)
    (hr : s'.st.1.regs = s.st.1.regs) (hab : ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s) :
    ownGH L a s' = ownGH L a s := by
  have hi : ∀ l₁ l₂, inPc L l₁ l₂ s' ↔ inPc L l₁ l₂ s := fun _ _ => by unfold inPc; rw [hpc]
  have hp : spPool L s' ↔ spPool L s := by unfold spPool; rw [hr]
  unfold ownGH
  simp only [hi, hp, hpc, hab, ↓reduceIte]

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.ownGH_labs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ownGH_labs

/-- info: 'Spike.Lib.X64.HelloPh.ownGH_congr_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ownGH_congr_off
