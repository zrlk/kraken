/-
**hello.w's owned words for the second thread's allocations on x86-64**: the owned words around `wc_main`'s
second `scc_rt_alloc_tcb` and `scc_rt_thread_init` calls at hello.w's extended phase `phH`
(`Spike/Lib/X64HelloPh.lean`), as wake's (`Spike/Lib/X64WakeOwn2.lean`) at hello's header.

The four counters and `scc_rt_nthreads` take one value before and one after their write, chosen by the phase
index's bits (`X64WakePh.ownV`). Three instances, switched where both give the same list:

- `ownH` (`own1`, wake's `ownW`): `scc_rt_start` and `wc_main` up to the second `call scc_rt_alloc_tcb`.
- `own2aH`: the second `scc_rt_alloc_tcb` call and `wc_main` up to the second `call scc_rt_thread_init`;
  `scc_rt_pinned_next` `80 → 208` (`80 + lenOf h` at hello's header `h = 0xc00c03`).
- `own2bH`: the second `scc_rt_thread_init` call and after; `scc_rt_stack_next` `16384 → 32768`.

- `hdr2H`, `own2aH`, `own2bH`: the values and the instances.
- `ph2aH`, `ph2aHC`, `ph2aH_eq`, `ph2bH`, `ph2bHC`, `ph2bH_eq`: the phase projections (bits `0`-`1`, `0`-`3`
  of `phH`) and their resolved forms; `own2aH_mod4`: `own2aH` reads bits `0`-`1` only.
- `allocTcb2H_ph`: the second `call scc_rt_alloc_tcb` (`.x23 + 18`), its return point `.x24` and the callee's
  entry, decided.
- `own2a_own2bH`, `own1_own2aH_ph`: the switches.

## Differences from the AArch64 version

`Spike/Lib/A64HelloOwn2.lean`.

- The pcs are x86-64's at `lo = 0x401000` (the 5-byte `call` at `.Lwc_main.x23 + 18`, `.x24`,
  `scc_rt_alloc_tcb`); the phases are the same (`16`, `16`, `13`).
- `ownV`/`ownW_eq` are `Spike/Lib/X64WakeOwn2.lean`'s.
- Only the live constants are twinned: `pn2H_eq`, `switch_pcs`, `threadInit2H_ph`, `own1_own2aH`,
  `own2a_own2bH_ph`, `own2bH_mod16`, `instOkVH`, `instOk2aH` and `instOk2bH` are not.
-/
import Spike.Lib.X64HelloPh
import Spike.Lib.X64WakeOwn2

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (ownV ownW ownW_eq)

/-! ## The values -/

/-- `wc_main`'s header for the second TCB in hello.w (`movq $12585987, %rdi`). -/
abbrev hdr2H : BitVec 64 := 12585987#64

/-- **The second `scc_rt_alloc_tcb` call's instance**: `scc_rt_pinned_next`
`80 → 208`, `scc_rt_stack_next` `16384`, `scc_rt_nthreads` `1`. -/
def own2aH (L : RuntimeLayout) (a : BitVec 64) : Nat → List (Loc × Val) :=
  ownV L a 80#64 208#64 16384#64 16384#64 1#64 1#64

/-- **The second `scc_rt_thread_init` call's instance**: `scc_rt_pinned_next`
`208`, `scc_rt_stack_next` `16384 → 32768`, `scc_rt_nthreads` `1`. -/
def own2bH (L : RuntimeLayout) (a : BitVec 64) : Nat → List (Loc × Val) :=
  ownV L a 208#64 208#64 16384#64 32768#64 1#64 1#64

/-! ## The phase projections -/

/-- **The second `scc_rt_alloc_tcb` call's phase projection**: the canonical
bits `0` and `1` of `phH`. -/
def ph2aH (pc : Nat) : Nat := phH pc % 4

/-- The projection through the resolved tables. -/
def ph2aHC (pc : Nat) : Nat := phC pc % 4

theorem ph2aH_eq : ph2aH = ph2aHC := by
  funext pc; unfold ph2aH ph2aHC; rw [phH_eq]

/-- **The second `scc_rt_thread_init` call's phase projection**: the
canonical bits `0`-`3` of `phH`. -/
def ph2bH (pc : Nat) : Nat := phH pc % 16

/-- The projection through the resolved tables. -/
def ph2bHC (pc : Nat) : Nat := phC pc % 16

theorem ph2bH_eq : ph2bH = ph2bHC := by
  funext pc; unfold ph2bH ph2bHC; rw [phH_eq]

/-- **`own2aH` reads the phase's bits `0` and `1` only.** -/
theorem own2aH_mod4 (L : RuntimeLayout) (a : BitVec 64) (i : Nat) : own2aH L a (i % 4) = own2aH L a i := by
  have h1 : i % 4 % 2 = i % 2 := by omega
  have h2 : i % 4 / 2 % 2 = i / 2 % 2 := by omega
  unfold own2aH ownV
  rw [h1, h2]
  simp

/-! ## The switches -/

/-- `wc_main`'s second `call scc_rt_alloc_tcb` (`.x23 + 18`) and its return
point `.x24` are at phase `16`, the callee's entry at `13`. -/
theorem allocTcb2H_ph : phC 4203744 = 16 ∧ phC 4203749 = 16 ∧ phC 4199029 = 13 := by decide +kernel

/-- **The second switch**: past `wc_main`'s second `call scc_rt_thread_init`
(phase `16`, the second instance) at the callee's entry (`12`, the third)
the lists agree. -/
theorem own2a_own2bH (L : RuntimeLayout) (a : BitVec 64) : own2aH L a 16 = own2bH L a 12 := by
  unfold own2aH own2bH ownV; simp

/-- **The first switch at the two phase maps**: `ownH` through `phH` at the
`call`, `own2aH` through `ph2aH` at the callee's entry. -/
theorem own1_own2aH_ph (L : RuntimeLayout) (a : BitVec 64) :
    ownH L a (phH 4203744) = own2aH L a (ph2aH 4199029) := by
  have h1 : phH 4203744 = 16 := by rw [phH_eq]; exact allocTcb2H_ph.1
  have h2 : ph2aH 4199029 = 1 := by rw [ph2aH_eq]; unfold ph2aHC; rw [allocTcb2H_ph.2.2]
  rw [h1, h2, ownH, ownW_eq]; unfold own2aH ownV; simp

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.own1_own2aH_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.own1_own2aH_ph

/-- info: 'Spike.Lib.X64.HelloPh.own2a_own2bH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.own2a_own2bH
