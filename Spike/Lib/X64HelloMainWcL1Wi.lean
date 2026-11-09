/-
**`MainWcPS.hWp`, `hWs` at the root's context `Land.CtxR1H`: `wc_rodata`'s return's control facts** (x86-64;
the twin of `Spike/Lib/A64HelloMainWcL1Wi.lean`): AArch64's `hWp_L1`/`hWs_L1` are `MainWcL1Wp.hWp_L1GX`/`hWs_L1GX`
at `Level1I`'s choices (the context `Land.CtxR1H … E rd ls`, the marks of `E` at `asm`, the level's sizes
`ls0T ls`), the level's context discharged:
- `hctx` by `Land.hctx_main1H` (the level's memory side is `ref1H … []` but for `xa`);
- `hwr` by `Land.hwr_stH` at `Land.GsH1` (`Land.hctx_st1H`), the box's word and cell by `MainWcL1Q.hbox_L1`,
  `hcell0_L1`, the counter below the heap by `HrdArena.hlt_U`/`h64_U`; `GsH1`'s pin is the caller's slot `-16`
  (`hslot`).

Left: the placement `hpl`. `wc_main`'s entry is at `Level1I`'s `Jr` (`JrRL`; its control facts `hJr_RL`) and the
caller's slot `-16` holds main's TCB (`hslot`), the call `Land.GcM1H` pins.

- `hJr_RL`: the control facts at `JrRL lbl env l` (`X64HelloRdCf.cont_ctl`).

The statements are at `ownGHXW` only (`X64HelloMainWcL1WiX`'s `hWp_L1X`, `hWs_L1X`; the root's level owns main's
and the worker's TCB words); this module keeps their control facts.

## Unlike AArch64

- main's TCB is at the caller's slot `-16` (`mWC`'s `%r8`; AArch64 `-80`), as `Land.GcM1H`/`GsH1` pin it.
- The regions are x86-64's (`wcR (RS helloLsw TOP) helloD`, `MainWcL1Wp`), the outside-move guard `NoSetFsW`, the
  thread pointer `tpOf (tcbS Ly)`; the loader's facts are the two parses `cellsOf asm` beside `hp`.
-/
import Spike.Lib.X64HelloMainWcL1Wp
import Spike.Lib.X64HelloLand3
import Spike.Lib.X64HelloJr1L

namespace Spike.Lib.X64.HelloPh.MainWcL1Wi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Flow.HelloJr1 (JrRL)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- **`hWp_L1GX`'s `hJr` at `Level1I`'s `JrRL`**: `wc_rodata`'s return's controls are the wrapper's continuation
(`X64HelloRdCf.cont_ctl`). -/
theorem hJr_RL (lbl : WeakMem.AllocLabel → Option Nat) (env : TermRun.Env) (l : WeakMem.AllocLabel) :
    ∀ σ c, JrRL lbl env l σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf helloSrc c [] := by
  rintro σ c ⟨rfl, -⟩
  exact Spike.Lib.X64HelloRdCf.cont_ctl _ none

end Spike.Lib.X64.HelloPh.MainWcL1Wi

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wi.hJr_RL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wi.hJr_RL
