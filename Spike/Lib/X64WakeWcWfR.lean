/-
**`wc_main`'s `hWp`/`hWs` off the top of the first stack** (wake.w,
x86-64): `StartPlace.wake_start_wc_place`'s premises on `wc_main` before
the box's landing (`hWp : WcPreW …`, `hWs : WcSp0W …`) at every base `v` of
the switch, from their case at the top.

The frame condition `wF … (FS … v)` pins the switch's base `v` to the top
of the first stack (`swF`): at any other `v` no memory satisfies it and both
obligations hold vacuously (`wcPreW_vac`, `wcSp0W_vac`), whatever the
fragment, the move, the memory side and the entry invariant.

- `blkW_vac`, `nodeW_vac`, `allocW_vac`, `wcPreW_vac`, `wcSp0W_vac`: at a
  frame condition holding for no memory.
- `v_top`, `fw_vac`: the frame condition at the base `v` pins `v` to the
  top `topS L 0`.
- `hWp_W`, `hWs_W`: every base from the top's case (`hTop`).

x86-64 twin of the first part of `Spike/Lib/A64WakeWcWfR.lean` (namespace
`Spike.Lib.X64.WakePh.WcWfR`, same names). **Where this differs from
AArch64**: `hWp_W`/`hWs_W` are stated generic in the fragment `W`, the move
`K`, the memory side and `wc_main`'s entry invariant (A64 at the root's
`NoMsrW (tpG TW WSE)`, `msOfA`, `wJ0 (wNC (JS …))`), so they serve the
start's level at `ownG` as well as at any other owned-words map; the region
is `wR (MainGlue.RS wcLsw v) wcD` at `wcD = 328`, `wcLsw = 384` (A64
`wR (swR v (-384) 0) 336`), the frame condition `MainGlue.FS L rS wcLsw 0 v`
(its `swF` one conjunct deeper than A64's), the top `MainGlue.topS L 0`; no
`hE`-style unused entry argument. The top case (A64 `hTopP_R`/`hTopS_R`,
from `WcWfS` and `WcPl`) is not twinned here.
-/
import Spike.Lib.X64WakeWcNoMsr
import Spike.Lib.X64WakeMainGlue
import Spike.Lib.X64WakeStartFacts

namespace Spike.Lib.X64.WakePh.WcWfR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (ND BlkW NodeW At)
open Spike.Lib.X64.WakePh.MainGlue (FS RS topS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64.Flow.WakeM (wR wF)
open Spike.Lib.X64.Flow.WakeWc (WcPreW WcSp0W)
open Spike.Lib.X64.Alloc (Call AllocW)

/-! ## At a frame condition holding for no memory -/

section Vac

variable {W : Spike.Lib.Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {ms : Spike.Lib.MemSide isa}

/-- A block at a frame condition holding for no memory. -/
theorem blkW_vac (hF : ∀ m, ¬ F m) {n : ND} {blk : List (Directive × Nat)} : BlkW W K exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ hF' => (hF _ hF').elim

/-- A node at a frame condition holding for no memory. -/
theorem nodeW_vac (hF : ∀ m, ¬ F m) {n : ND} : NodeW W K exe endPc R F n :=
  fun _ _ ⟨_, _, _, _, _, _, hF', _⟩ => (hF _ hF').elim

/-- `scc_rt_alloc` at a frame condition holding for no memory. -/
theorem allocW_vac (hF : ∀ m, ¬ F m) {q : Call} : AllocW ms q W K exe endPc R F := by
  constructor <;> first | exact blkW_vac hF | exact nodeW_vac hF

/-- **`WcPreW` at a frame condition holding for no memory.** -/
theorem wcPreW_vac (hF : ∀ m, ¬ F m) {J0 Jc : Spike.Lib.X64.AS → Ctl → Prop} :
    WcPreW W K exe endPc R F ms J0 Jc :=
  ⟨⟨blkW_vac hF, blkW_vac hF, nodeW_vac hF, blkW_vac hF, blkW_vac hF⟩, blkW_vac hF,
    fun _ _ _ => allocW_vac fun m h => hF m h.1⟩

/-- **`WcSp0W` at a frame condition holding for no memory.** -/
theorem wcSp0W_vac (hF : ∀ m, ¬ F m) {J0 : Spike.Lib.X64.AS → Ctl → Prop} :
    WcSp0W W K exe endPc R F ms J0 :=
  ⟨blkW_vac hF, nodeW_vac hF⟩

end Vac

/-! ## Every base from the top's case -/

section Top

variable {L : RuntimeLayout} {rS : Scc.Sem.Range}

/-- **The frame condition pins the switch's base to the top of the first
stack** (`swF`). -/
theorem v_top {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.X64.AS} {m : MachineData}
    (h : wF (RS wcLsw v) wcD (FS L rS wcLsw 0#64 v) m0 σC m) : v = topS L 0#64 :=
  h.1.1.2.1.1

/-- At a base other than the top no memory satisfies the frame condition. -/
theorem fw_vac {v : BitVec 64} (hv : v ≠ topS L 0#64) (m0 : MachineData) (σC : Spike.Lib.X64.AS) :
    ∀ m, ¬ wF (RS wcLsw v) wcD (FS L rS wcLsw 0#64 v) m0 σC m :=
  fun _ h => hv (v_top h)

variable {W : Spike.Lib.Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {ms : Spike.Lib.MemSide isa} {J : Spike.Lib.X64.AS → Spike.Lib.X64.AS → Ctl → Prop}

/-- **`hWp` at every base** from its case at the top of the first stack
(`hTop`). -/
theorem hWp_W
    (hTop : ∀ m0 σC, WcPreW W K exe endPc (wR (RS wcLsw (topS L 0#64)) wcD)
      (wF (RS wcLsw (topS L 0#64)) wcD (FS L rS wcLsw 0#64 (topS L 0#64)) m0 σC) ms (J σC) (J σC)) :
    ∀ v m0 σC, WcPreW W K exe endPc (wR (RS wcLsw v) wcD) (wF (RS wcLsw v) wcD (FS L rS wcLsw 0#64 v) m0 σC)
      ms (J σC) (J σC) := by
  intro v m0 σC
  by_cases hv : v = topS L 0#64
  · subst hv; exact hTop m0 σC
  · exact wcPreW_vac (fw_vac hv m0 σC)

/-- **`hWs` at every base** from its case at the top of the first stack
(`hTop`). -/
theorem hWs_W
    (hTop : ∀ m0 σC, WcSp0W W K exe endPc (wR (RS wcLsw (topS L 0#64)) wcD)
      (wF (RS wcLsw (topS L 0#64)) wcD (FS L rS wcLsw 0#64 (topS L 0#64)) m0 σC) ms (J σC)) :
    ∀ v m0 σC, WcSp0W W K exe endPc (wR (RS wcLsw v) wcD) (wF (RS wcLsw v) wcD (FS L rS wcLsw 0#64 v) m0 σC)
      ms (J σC) := by
  intro v m0 σC
  by_cases hv : v = topS L 0#64
  · subst hv; exact hTop m0 σC
  · exact wcSp0W_vac (fw_vac hv m0 σC)

end Top

end Spike.Lib.X64.WakePh.WcWfR

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.hWp_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.hWp_W

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.hWs_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.hWs_W
