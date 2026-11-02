/-
**hello.w's box ghost pinned to the real run** (x86-64; the definition part of `Spike/Lib/A64HelloRootHP.lean`):
`GJ1RH`, the box's ghost `GJ1H` with the region and frame condition pinned. `R` is `wc_main`'s frame based at the
saved `%rbp`, `(wcR (RS helloLsw v) helloD).fp (-8)` (where the box's landing `bXH` is stated), and `F` its
frame condition at the call over the start's `FS` at `v`, from the caller's state `m1`, `σ1`. The rest of `RootHP`
(the landing at the pinned ghost, `H1GAH0`, `hP_of`) is in `X64HelloRootHP`, which imports this module.

- `RbpPinH`: the caller's invariant's `%rbp` pinned at `scc_rt_main`'s saved `%rbp`, `(RS helloLsw v).addr (-8)`.
- `GJ1RH`: the pinned ghost (with `RbpPinH` at its switch base).
- `hpin_RH`: the pin with its region at one switch base (`X64HelloHfp`'s `hpin`).
- `gj1RH_R`, `gj1RH_lo`: its region is `(wcR (RS helloLsw v) helloD).fp (-8)`, with bounds `-helloD + 8` and
  `16`, its base `96` below the switch base.

Unlike AArch64, the box's landing is stated on the frame based at the saved `%rbp` (`R.fp (-8)`, x86-64's
`bXRH_rebase`; AArch64 `wcR …` itself, `sp`-based), so `R`'s base is `8 + 80 + 8 = 96` below `v` (`BoxPureH`'s
`+ 96`; AArch64 `80`). `scc_rt_main` is entered by a `call`, so the caller's region is `MainGlue.RS helloLsw v =
(swR v (-helloLsw) 0).callee (-8) (8 - helloLsw) 8` (AArch64: `swR v (-helloLsw) 0`; as x86-64 wake's
`wR (RS Lsw v) D`); `wcR R D` is `R.callee (-80) (-D) 8` (the callee's region reaches the pushed return address
above, AArch64's `hi' = 0`), the depths are `X64HelloFrameD`'s, and the start's region is
`Rt.rS0 L`.
-/
import Spike.Lib.X64HelloH2G
import Spike.Lib.X64HelloFrameD
import Spike.Lib.X64WakeMainGlue

namespace Spike.Lib.X64.HelloPh.RootHP

open CoreLang CoreTerm
open Spike.Lib (Region Ctl)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.HelloM (wcR wcF)
open Spike.Lib.X64.WakePh.MainGlue (FS RS)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64HelloH2G (GJ1H)

/-- **The caller's `%rbp` pinned at the switch base** `v`: `J1` is `wc_main`'s entry `mWC σC Jr` past its `call`
for a caller's invariant `Jr` whose states hold `scc_rt_main`'s saved `%rbp`, `(RS helloLsw v).addr (-8)`, in
`%rbp` (what the segment end's frame-pointer fact `hfp` reads). -/
def RbpPinH (L : RuntimeLayout) (J1 : Spike.Lib.X64.AS → Ctl → Prop) (v : BitVec 64) : Prop :=
  ∃ (σC σ1 : Spike.Lib.X64.AS) (Jr : Spike.Lib.X64.AS → Ctl → Prop),
    J1 = Spike.Lib.X64.Flow.HelloM.wcJ0 (Spike.Lib.X64.Flow.Hello1.mWC L.lab σC Jr).J σ1 ∧
      ∀ σx c, Jr σx c → σx.regs.get64 .rbp = (RS helloLsw v).addr (-8)

/-- **The box's ghost at the real run** (`GJ1H` with the region and frame condition pinned): `R` is `wc_main`'s
frame based at the saved `%rbp`, `(wcR (RS helloLsw v) helloD).fp (-8)`, and `F` its frame condition at the call
over the start's `FS` at `v`, from the caller's state `m1`, `σ1`. -/
def GJ1RH (L : RuntimeLayout) (lbl1 : Lbl) (lr : WeakMem.AllocLabel) (R : Region) (F : MachineData → Prop)
    (J1 : Spike.Lib.X64.AS → Ctl → Prop) (t : UInt64) : Prop :=
  GJ1H L lbl1 lr R F J1 t ∧ ∃ (v : BitVec 64) (m1 : MachineData) (σ1 : Spike.Lib.X64.AS),
    R = (wcR (RS helloLsw v) helloD).fp (-8) ∧
      F = wcF (RS helloLsw v) helloD (FS L (Spike.Lib.X64.Rt.rS0 L) helloLsw 0#64 v) m1 σ1 ∧ RbpPinH L J1 v

/-- **The pinned ghost's region** is `wc_main`'s at some switch base `v`. -/
theorem gj1RH_R {L : RuntimeLayout} {lbl1 : Lbl} {lr : WeakMem.AllocLabel} {R : Region} {F : MachineData → Prop}
    {J1 : Spike.Lib.X64.AS → Ctl → Prop} {t : UInt64} (h : GJ1RH L lbl1 lr R F J1 t) :
    ∃ v : BitVec 64, R = (wcR (RS helloLsw v) helloD).fp (-8) :=
  let ⟨_, v, _, _, hR, _⟩ := h; ⟨v, hR⟩

/-- **The pinned ghost's region's bounds**: `-helloD + 8` (`-392`) and `16`. -/
theorem gj1RH_lo {L : RuntimeLayout} {lbl1 : Lbl} {lr : WeakMem.AllocLabel} {R : Region}
    {F : MachineData → Prop} {J1 : Spike.Lib.X64.AS → Ctl → Prop} {t : UInt64} (h : GJ1RH L lbl1 lr R F J1 t) :
    R.lo = -helloD + 8 ∧ R.hi = 16 := by
  obtain ⟨v, rfl⟩ := gj1RH_R h
  simp [Spike.Lib.Region.fp, Spike.Lib.Region.callee]

/-- **The pinned ghost's `%rbp` pin with its region** (`X64HelloHfp.hfp_of_parts`'s `hpin`): `J1` is `wc_main`'s
entry `mWC σC Jr` for a caller's invariant `Jr` holding `(RS helloLsw v).addr (-8)` in `%rbp`, at the switch base
`v` of `R`. -/
theorem hpin_RH {L : RuntimeLayout} {lbl1 : Lbl} {lr : WeakMem.AllocLabel} :
    ∀ R F J1 t, GJ1RH L lbl1 lr R F J1 t → ∃ (σC σ1 : Spike.Lib.X64.AS) (Jr : Spike.Lib.X64.AS → Ctl → Prop)
      (v : BitVec 64), J1 = Spike.Lib.X64.Flow.HelloM.wcJ0 (Spike.Lib.X64.Flow.Hello1.mWC L.lab σC Jr).J σ1 ∧
        R = (wcR (RS helloLsw v) helloD).fp (-8) ∧
        ∀ σx c, Jr σx c → σx.regs.get64 .rbp = (RS helloLsw v).addr (-8) :=
  fun _ _ _ _ ⟨_, v, _, _, hR, _, σC, σ1, Jr, hJ, hp⟩ => ⟨σC, σ1, Jr, v, hJ, hR, hp⟩

/-- `GJ1RH` is inhabited at every layout, switch base and caller's memory (non-vacuity): the caller's state with
main's TCB in every slot, a caller's invariant holding nowhere (so its `%rbp` pin `RbpPinH` too). -/
example (L : RuntimeLayout) (lbl1 : Lbl) (lr : WeakMem.AllocLabel) (σ0 : Spike.Lib.X64.AS) (v : BitVec 64)
    (m1 : MachineData) (t : UInt64) : ∃ R F J1, GJ1RH L lbl1 lr R F J1 t :=
  ⟨_, _, _, ⟨{ σ0 with slot := fun _ => Spike.Lib.X64.Flow.Ret0.pinA L.lab + 0#64 + 8#64 }, σ0,
    fun _ _ => False, rfl, fun _ _ h => h.elim, rfl⟩, v, m1, σ0, rfl, rfl,
    _, σ0, fun _ _ => False, rfl, fun _ _ h => h.elim⟩

end Spike.Lib.X64.HelloPh.RootHP

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.RootHP.gj1RH_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootHP.gj1RH_lo

/-- info: 'Spike.Lib.X64.HelloPh.RootHP.hpin_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootHP.hpin_RH
