import Kraken.X64.Examples.Sbr.SessionBin.WitMemShared

/-!
# Memory witnesses: the element at the init state

The element at `cheW` with the values `σInit wI` (what a successful `ff_aac_sbr_ctx_alloc_init`
leaves), in the witness environment `WitEnv.wEnv`: its whole allocation `[cheW, cheW + 0x88ba0)`,
the cell `ac->fdsp`, the `float_dsp` slots at `fdspW`, the transform and PS tables and the logging
state, the constants and the parser's static data. Given the environment's contracts
(`EnvOK wS wEnv`), it is `SbrReady` (and so `SbrInitialized`): `SReach.init` reaches `σInit wI`
with the flag `true`, with no run of init.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init
open Kraken.Examples.Sbr.SessionBin
open Kraken.Examples.Sbr.Witness (SatIn InL DisjL)
open Kraken.Examples.Sbr.WitEnv

namespace Kraken.Examples.Sbr.WitMem

/-- A memory of `P` is one of `Q` when `P` implies `Q`. -/
theorem SatIn.imp {P Q : Mem 64 → Prop} {L : List (Nat × Nat)} (h : SatIn P L)
    (hPQ : ∀ m, P m → Q m) : SatIn Q L := by
  obtain ⟨m, hm, hk⟩ := h
  exact ⟨m, hPQ m hm, hk⟩

attribute [local instance] wCE

/-- The intervals of the element and what it owns besides its allocation. -/
abbrev elemL : List (Nat × Nat) :=
  [(0x500000000, 0x500088ba0), (0x200200000, 0x200200040), (0x200102550, 0x200102558),
   (0x300200000, 0x300202040), (0x400000, 0x48a000), (0x300000000, 0x300014000),
   (0x300100000, 0x300114000)]

theorem sat_fnW : SatIn (FnW wEnv (σInit wI).1 (tAt cheW acW))
    [(0x500028920 + 0x601c0, 0x500028920 + 0x601e0), (0x500028920 + 0x60250, 0x500028920 + 0x60270),
     (0x200200000, 0x200200040), (0x300200000, 0x300202040)] := by
  unfold FnW
  simp only [sbrA_tAt]
  exact SatIn.cover (by msat) (by decide +kernel)

theorem sat_fdspCell : SatIn (c8 (acW + 0x2550#64) (σInit wI).1.fdsp) [(0x200102550, 0x200102558)] :=
  Witness.SatIn.val (Int.toBytes_length _ _) (by decide +kernel)

/-- The element's memory at the init state. -/
theorem sat_elemAt : SatIn (ElemAt wEnv wS.vs wS.vp (σInit wI) cheW acW ⋆ InitGap cheW) elemL := by
  unfold ElemAt
  simp only [sbrA_tAt]
  exact SatIn.cover (Witness.SatIn.sep (Witness.SatIn.sep sat_sbrF (Witness.SatIn.sep sat_psRest
    (Witness.SatIn.sep sat_arrW (Witness.SatIn.sep (sat_dspW wEnv) (Witness.SatIn.sep sat_fnW
      (Witness.SatIn.sep sat_fdspCell sat_cstP (by decide +kernel)) (by decide +kernel))
      (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))
    sat_gap (by decide +kernel)) (by decide +kernel)

/-- The element at the init state is ready. -/
theorem elem_ready (hE : EnvOK wS wEnv) {m : Mem 64}
    (h : (ElemAt wEnv wS.vs wS.vp (σInit wI) cheW acW ⋆ InitGap cheW) m) :
    SbrReady wS cheW acW m :=
  ⟨elemOK_cheW, wEnv, wI, σInit wI, hE, SReach.init, h⟩

theorem sat_ready (hE : EnvOK wS wEnv) : SatIn (SbrReady wS cheW acW) elemL :=
  SatIn.imp sat_elemAt fun _ h => elem_ready hE h

theorem sat_initialized (hE : EnvOK wS wEnv) : SatIn (SbrInitialized wS cheW acW) elemL :=
  SatIn.imp (sat_ready hE) fun _ h => SbrReady.initialized h

end Kraken.Examples.Sbr.WitMem
