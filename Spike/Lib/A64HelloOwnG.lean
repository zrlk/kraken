/-
**hello.w's global owned-words map** (AArch64; twin of
`A64WakeOwnG`): the three instances' owned words (`ownH` at `phH`, `own2aH`
at `ph2aH`, `own2bH` at `ph2bH`) picked from the thread state, by registers
and pc only, with wake's tests `WakePh.inPc`, `WakePh.spPool`,
`WakePh.x30At` at hello's labels (`wc_main` is `.L22_wc_main` in hello's
listing; the runtime's labels are wake's).

- `ownGH L a s`:
  * `scc_rt_alloc_tcb`: `own2aH` on a pool stack (`wc_main`'s second call),
    else `ownH` (`scc_rt_start`'s);
  * `scc_rt_thread_init`, `scc_rt_stack_take`: `own2bH` on a pool stack,
    else `ownH`;
  * `wc_main` from `.sp4` to `.sp6`: `own2aH`; from `.sp6` to
    `.stack_grow`: `own2bH`;
  * the abort dispatcher and stubs (`scc_rt_abort` up to
    `scc_rt_thr_worker`): by the caller's return address, `own2aH` for
    `scc_rt_alloc_tcb`'s on a pool stack, `own2bH` for `wc_main`'s spawn
    failure (`.sp15`, wake's `.sp11`), else `ownH`;
  * elsewhere `ownH`.
- `ownGH_labs`: the labels the map tests, resolved at `lo` in `helloProg`
  (in the order of wake's map; each range nonempty).
-/
import Spike.Lib.A64HelloOwn2
import Spike.Lib.A64WakeOwnG

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh (inPc spPool x30At)

/-- **hello.w's global owned-words map.** -/
def ownGH (L : RuntimeLayout) (a : BitVec 64) (s : State) : List (Loc × Val) :=
  if inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s then
    if spPool L s then own2aH L a (ph2aH (pcOf s)) else ownH L a (phH (pcOf s))
  else if inPc L "scc_rt_thread_init" "scc_rt_stack_release" s then
    if spPool L s then own2bH L a (ph2bH (pcOf s)) else ownH L a (phH (pcOf s))
  else if inPc L ".L22_wc_main.sp4" ".L22_wc_main.sp6" s then own2aH L a (ph2aH (pcOf s))
  else if inPc L ".L22_wc_main.sp6" ".L22_wc_main.stack_grow" s then own2bH L a (ph2bH (pcOf s))
  else if inPc L "scc_rt_abort" "scc_rt_thr_worker" s then
    if x30At L ".L3_scc_rt_alloc_tcb.sp13" s ∧ spPool L s then own2aH L a (ph2aH (pcOf s))
    else if x30At L ".L22_wc_main.sp15" s then own2bH L a (ph2bH (pcOf s))
    else ownH L a (phH (pcOf s))
  else ownH L a (phH (pcOf s))

/-- **The labels `ownGH` tests, at `lo` in `helloProg`.** -/
theorem ownGH_labs :
    ["scc_rt_alloc_tcb", "scc_rt_thread_reserve", "scc_rt_thread_init", "scc_rt_stack_release",
      ".L22_wc_main.sp4", ".L22_wc_main.sp6", ".L22_wc_main.stack_grow", "scc_rt_abort", "scc_rt_thr_worker",
      ".L3_scc_rt_alloc_tcb.sp13", ".L22_wc_main.sp15"].map (codeOf lo SccCode.helloProg) =
    [some 2164748, some 2165172, some 2165284, some 2166004, some 2169748, some 2169772, some 2169936,
      some 2168064, some 2168628, some 2164996, some 2169912] := by
  decide +kernel

end Spike.Lib.A64.HelloPh
