import Kraken.X64.Examples.Sbr.SessionBin.WitMemBase
import Kraken.X64.Examples.Sbr.SessionBin.WitEnvLabs

/-!
# Memory witnesses: the read-only data

Under the witness code `WitEnv.wCE`: the constants `CstW` and the parser's static data `PStat`
(jump table, `ceil_log2`, FFmpeg's SBR and PS Huffman tables with their pointer arrays, the PS
constants, `sbr_reset`'s constants, the limiter table). The constants sit at their labels
(`0x400000 + 0x2000 * k`, below `0x500000`), the Huffman tables at `WitEnv.wSbrTab k`,
`WitEnv.wPsTab k`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init
open Kraken.Examples.Sbr.SessionBin
open Kraken.Examples.Sbr.Witness (SatIn InL DisjL)
open Kraken.Examples.Sbr.WitEnv

namespace Kraken.Examples.Sbr.WitMem

/-- `sat_tac` with one more leaf: a Huffman table's bytes (`natBytes`). -/
syntax "msat" : tactic
macro_rules
  | `(tactic| msat) => `(tactic| first
      | (apply Witness.SatIn.val; exact Int.toBytes_length _ _; decide +kernel)
      | (apply Witness.SatIn.val; exact VlcWit.natBytes_length _ _; decide +kernel)
      | (apply Witness.SatIn.val; rfl; decide +kernel)
      | (apply Witness.SatIn.block; exact Nat.le_refl _; decide +kernel)
      | exact Witness.SatIn.emp
      | assumption
      | (apply Witness.SatIn.sep; msat; msat; decide +kernel))

attribute [local instance] wCE

theorem sat_cstW : SatIn CstW [(0x400000, 0x454000)] := by
  unfold CstW
  simp only [wlab_LCPI14_0, wlab_LCPI14_5, wlab_LCPI14_6, wlab_LCPI14_9, wlab_LCPI14_10,
    wlab_LCPI14_11, wlab_LCPI14_12, wlab_LCPI14_13, wlab_LCPI14_14, wlab_LCPI14_15,
    wlab_LCPI14_16, wlab_LCPI14_17, wlab_LCPI14_3, wlab_LCPI14_1, wlab_LCPI14_2, wlab_LCPI14_8,
    wlab_exp2_tab, wlab_bw_tab, wlab_limgain, wlab_sbr_qmf_window_ds, wlab_ff_ps_neg,
    wlab_ps_mask, wlab_LCPI19_0, wlab_LCPI19_1, wlab_LCPI19_2, wlab_ps_mask3,
    wlab_sbr_qmf_window_us, wlab_LCPI15_1, wlab_ps_mask2, wlab_ff_sbr_noise_table,
    wlab_ps_noise0, wlab_ps_noise13, wlab_ps_noise2, wlab_LCPI17_6, wlab_LCPI17_7,
    wlab_LCPI17_8, wlab_LCPI17_9, wlab_LCPI17_10, wlab_LCPI17_12, wlab_LCPI14_4,
    wlab_LCPI17_11, wlab_pd_reverse]
  exact Witness.SatIn.widen _ _ (by msat) (by decide +kernel)

theorem sat_jt : SatIn Grid.JtW [(0x454000, 0x456000)] := by
  unfold Grid.JtW Grid.JT
  simp only [wlab_read_sbr_grid_jt]
  exact Witness.SatIn.widen _ _ (by msat) (by decide +kernel)

theorem sat_ceil : SatIn (Blocks [(lab "ceil_log2", 6)]) [(0x456000, 0x458000)] := by
  simp only [wlab_ceil_log2]
  exact Witness.SatIn.widen _ _ (Witness.SatIn.block (Nat.le_refl _) (by decide +kernel))
    (by decide +kernel)

theorem sat_vptrs : SatIn (Vlc.VPtrs Vlc.VA wS.vs 10) [(0x458000, 0x45a000)] := by
  simp only [Vlc.VA, wlab_ff_aac_sbr_vlc, Vlc.VPtrs]
  exact Witness.SatIn.widen _ _ (by msat) (by decide +kernel)

/-- A Huffman table of `E` entries at `p`. -/
theorem sat_nb (N E : Nat) (p : BitVec 64) (h : p.toNat + 4 * E ≤ 2 ^ 64) :
    SatIn (VlcWit.natBytes N (4 * E) =@ p) [(p.toNat, p.toNat + 4 * E)] :=
  Witness.SatIn.val (VlcWit.natBytes_length _ _) h

theorem sat_vt (k : Nat) (hk : k < 10) :
    SatIn ((wS.vs k).es =@ (wS.vs k).p)
    [(0x300000000 + 0x2000 * k, 0x300000000 + 0x2000 * k + 0x2000)] := by
  refine SatIn.cover (sat_nb _ _ _ ?_) ?_ <;>
  · revert k; decide +kernel

theorem sat_vtabs : SatIn (Vlc.VTabs wS.vs 10) [(0x300000000, 0x300014000)] := by
  simp only [Vlc.VTabs]
  exact SatIn.cover (Witness.SatIn.sep (sat_vt 9 (by decide)) (Witness.SatIn.sep (sat_vt 8 (by decide)) (Witness.SatIn.sep (sat_vt 7 (by decide)) (Witness.SatIn.sep (sat_vt 6 (by decide)) (Witness.SatIn.sep (sat_vt 5 (by decide)) (Witness.SatIn.sep (sat_vt 4 (by decide)) (Witness.SatIn.sep (sat_vt 3 (by decide)) (Witness.SatIn.sep (sat_vt 2 (by decide)) (Witness.SatIn.sep (sat_vt 1 (by decide)) (Witness.SatIn.sep (sat_vt 0 (by decide)) Witness.SatIn.emp (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))
    (by decide +kernel)

theorem sat_pptrs : SatIn (Ps.VPtrs wS.vp 10) [(0x45a000, 0x45c000)] := by
  simp only [wlab_vlc_ps, Ps.VPtrs]
  exact Witness.SatIn.widen _ _ (by msat) (by decide +kernel)

theorem sat_pt (k : Nat) (hk : k < 10) :
    SatIn ((wS.vp k).es =@ (wS.vp k).p)
    [(0x300100000 + 0x2000 * k, 0x300100000 + 0x2000 * k + 0x2000)] := by
  refine SatIn.cover (sat_nb _ _ _ ?_) ?_ <;>
  · revert k; decide +kernel

theorem sat_ptabs : SatIn (Ps.VTabs wS.vp 10) [(0x300100000, 0x300114000)] := by
  simp only [Ps.VTabs]
  exact SatIn.cover (Witness.SatIn.sep (sat_pt 9 (by decide)) (Witness.SatIn.sep (sat_pt 8 (by decide)) (Witness.SatIn.sep (sat_pt 7 (by decide)) (Witness.SatIn.sep (sat_pt 6 (by decide)) (Witness.SatIn.sep (sat_pt 5 (by decide)) (Witness.SatIn.sep (sat_pt 4 (by decide)) (Witness.SatIn.sep (sat_pt 3 (by decide)) (Witness.SatIn.sep (sat_pt 2 (by decide)) (Witness.SatIn.sep (sat_pt 1 (by decide)) (Witness.SatIn.sep (sat_pt 0 (by decide)) Witness.SatIn.emp (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))
    (by decide +kernel)

theorem sat_constW : SatIn Ps.ConstW [(0x45c000, 0x46c000)] := by
  unfold Ps.ConstW
  simp only [wlab_num_env_tab, wlab_nr_iidicc_par_tab, wlab_nr_iidopd_par_tab, wlab_huff_iid,
    wlab_ff_log2_tab_got, wlab_ff_log2_tab, wlab_LCPI0_28, wlab_LCPI0_30]
  exact Witness.SatIn.widen _ _ (by msat) (by decide +kernel)

theorem sat_cstR : SatIn Reset.CstR [(0x46c000, 0x488000)] := by
  unfold Reset.CstR
  simp only [wlab_sbr_offset_0, wlab_sbr_offset_1, wlab_sbr_offset_2, wlab_sbr_offset_3,
    wlab_sbr_offset_4, wlab_sbr_offset_5, wlab_LCPI5_0, wlab_LCPI5_1, wlab_LCPI5_2, wlab_LCPI5_3,
    wlab_LCPI5_4, wlab_LCPI5_6, wlab_LCPI5_8, wlab_LCPI5_9]
  exact Witness.SatIn.widen _ _ (by msat) (by decide +kernel)

theorem sat_bwR : SatIn Reset.BwR [(0x488000, 0x48a000)] := by
  simp only [Reset.BwR, wlab_sbr_make_f_tablelim_bw]
  exact Witness.SatIn.widen _ _ (Witness.SatIn.block (Nat.le_refl _) (by decide +kernel))
    (by decide +kernel)

/-- The parser's static data. -/
theorem sat_pstat : SatIn (PStat wS.vs wS.vp)
    [(0x454000, 0x48a000), (0x300000000, 0x300014000), (0x300100000, 0x300114000)] := by
  unfold PStat Vlc.VlcW Ps.PsTabs
  exact SatIn.cover (Witness.SatIn.sep sat_jt (Witness.SatIn.sep sat_ceil
    (Witness.SatIn.sep (Witness.SatIn.sep sat_vptrs sat_vtabs (by decide +kernel))
    (Witness.SatIn.sep (Witness.SatIn.sep sat_pptrs (Witness.SatIn.sep sat_ptabs sat_constW
      (by decide +kernel)) (by decide +kernel))
    (Witness.SatIn.sep sat_cstR sat_bwR (by decide +kernel)) (by decide +kernel))
    (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)

/-- The constants and the parser's static data (the tail of `ElemAt` and of `SharedData`). -/
theorem sat_cstP : SatIn (CstW ⋆ PStat wS.vs wS.vp)
    [(0x400000, 0x48a000), (0x300000000, 0x300014000), (0x300100000, 0x300114000)] :=
  SatIn.cover (Witness.SatIn.sep sat_cstW sat_pstat (by decide +kernel)) (by decide +kernel)

end Kraken.Examples.Sbr.WitMem
