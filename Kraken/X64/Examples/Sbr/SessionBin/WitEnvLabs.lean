import Kraken.X64.Examples.Sbr.SessionBin.WitEnvDefs

/-!
# The witness environment: the constants' addresses

Under the ambient code `wCE`, the `k`-th read-only constant of `dataLabels` sits at
`0x400000 + 0x2000 * k` (labels take no bytes, every data cell 8192). Read off the data prefix
of the laid-out image; the rest of the image is not evaluated.
-/

open Kraken Kraken.X64.Parser
open Kraken.Examples.Sbr.GridJtWit (sz notLab layout_snd)

namespace Kraken.Examples.Sbr.WitEnv

attribute [local instance] wCE

/-- A label's address, at its position `n` in the laid-out image. -/
theorem labAt (l : Label) (n : Nat)
    (hn : (img.map fun d => (d, sz d))[n]? = some (.label l, 0))
    (hf : ((img.map fun d => (d, sz d)).take n).all (notLab l) = true) :
    lab l = ((0x400000 : Int64)
      + Int64.ofNat ((((img.map fun d => (d, sz d)).take n).map (·.2)).sum)).toBitVec := by
  have hs : (wLayout img).2 = img.map fun d => (d, sz d) := layout_snd img
  have h1 : (wLayout img).2[n]? = some (.label l, 0) := by rw [hs]; exact hn
  have h2 : ∀ dz ∈ (wLayout img).2.take n, dz.1 ≠ Directive.label l := by
    rw [hs]
    intro dz hdz heq
    have := List.all_eq_true.mp hf dz hdz
    obtain ⟨d, z⟩ := dz
    simp only at heq
    subst heq
    simp [notLab] at this
  unfold lab
  rw [Executable.label_addrOf _ l n h1 h2]
  show ((0x400000 : Int64) + Int64.ofNat ((((wLayout img).2.take n).map (·.2)).sum)).toBitVec = _
  rw [hs]

theorem wlab_LCPI14_0 : lab "LCPI14_0" = 0x400000#64 :=
  (labAt _ 0 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_5 : lab "LCPI14_5" = 0x402000#64 :=
  (labAt _ 2 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_6 : lab "LCPI14_6" = 0x404000#64 :=
  (labAt _ 4 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_9 : lab "LCPI14_9" = 0x406000#64 :=
  (labAt _ 6 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_10 : lab "LCPI14_10" = 0x408000#64 :=
  (labAt _ 8 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_11 : lab "LCPI14_11" = 0x40a000#64 :=
  (labAt _ 10 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_12 : lab "LCPI14_12" = 0x40c000#64 :=
  (labAt _ 12 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_13 : lab "LCPI14_13" = 0x40e000#64 :=
  (labAt _ 14 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_14 : lab "LCPI14_14" = 0x410000#64 :=
  (labAt _ 16 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_15 : lab "LCPI14_15" = 0x412000#64 :=
  (labAt _ 18 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_16 : lab "LCPI14_16" = 0x414000#64 :=
  (labAt _ 20 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_17 : lab "LCPI14_17" = 0x416000#64 :=
  (labAt _ 22 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_3 : lab "LCPI14_3" = 0x418000#64 :=
  (labAt _ 24 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_1 : lab "LCPI14_1" = 0x41a000#64 :=
  (labAt _ 26 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_2 : lab "LCPI14_2" = 0x41c000#64 :=
  (labAt _ 28 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_8 : lab "LCPI14_8" = 0x41e000#64 :=
  (labAt _ 30 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_exp2_tab : lab "exp2_tab" = 0x420000#64 :=
  (labAt _ 32 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_bw_tab : lab "bw_tab" = 0x422000#64 :=
  (labAt _ 34 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_limgain : lab "limgain" = 0x424000#64 :=
  (labAt _ 36 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_sbr_qmf_window_ds : lab "sbr_qmf_window_ds" = 0x426000#64 :=
  (labAt _ 38 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ff_ps_neg : lab "ff_ps_neg" = 0x428000#64 :=
  (labAt _ 40 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ps_mask : lab "ps_mask" = 0x42a000#64 :=
  (labAt _ 42 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI19_0 : lab "LCPI19_0" = 0x42c000#64 :=
  (labAt _ 44 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI19_1 : lab "LCPI19_1" = 0x42e000#64 :=
  (labAt _ 46 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI19_2 : lab "LCPI19_2" = 0x430000#64 :=
  (labAt _ 48 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ps_mask3 : lab "ps_mask3" = 0x432000#64 :=
  (labAt _ 50 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_sbr_qmf_window_us : lab "sbr_qmf_window_us" = 0x434000#64 :=
  (labAt _ 52 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI15_1 : lab "LCPI15_1" = 0x436000#64 :=
  (labAt _ 54 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ps_mask2 : lab "ps_mask2" = 0x438000#64 :=
  (labAt _ 56 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ff_sbr_noise_table : lab "ff_sbr_noise_table" = 0x43a000#64 :=
  (labAt _ 58 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ps_noise0 : lab "ps_noise0" = 0x43c000#64 :=
  (labAt _ 60 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ps_noise13 : lab "ps_noise13" = 0x43e000#64 :=
  (labAt _ 62 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ps_noise2 : lab "ps_noise2" = 0x440000#64 :=
  (labAt _ 64 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI17_6 : lab "LCPI17_6" = 0x442000#64 :=
  (labAt _ 66 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI17_7 : lab "LCPI17_7" = 0x444000#64 :=
  (labAt _ 68 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI17_8 : lab "LCPI17_8" = 0x446000#64 :=
  (labAt _ 70 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI17_9 : lab "LCPI17_9" = 0x448000#64 :=
  (labAt _ 72 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI17_10 : lab "LCPI17_10" = 0x44a000#64 :=
  (labAt _ 74 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI17_12 : lab "LCPI17_12" = 0x44c000#64 :=
  (labAt _ 76 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI14_4 : lab "LCPI14_4" = 0x44e000#64 :=
  (labAt _ 78 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI17_11 : lab "LCPI17_11" = 0x450000#64 :=
  (labAt _ 80 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_pd_reverse : lab "pd_reverse" = 0x452000#64 :=
  (labAt _ 82 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_read_sbr_grid_jt : lab "read_sbr_grid_jt" = 0x454000#64 :=
  (labAt _ 84 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ceil_log2 : lab "ceil_log2" = 0x456000#64 :=
  (labAt _ 86 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ff_aac_sbr_vlc : lab "ff_aac_sbr_vlc" = 0x458000#64 :=
  (labAt _ 88 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_vlc_ps : lab "vlc_ps" = 0x45a000#64 :=
  (labAt _ 90 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_num_env_tab : lab "num_env_tab" = 0x45c000#64 :=
  (labAt _ 92 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_nr_iidicc_par_tab : lab "nr_iidicc_par_tab" = 0x45e000#64 :=
  (labAt _ 94 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_nr_iidopd_par_tab : lab "nr_iidopd_par_tab" = 0x460000#64 :=
  (labAt _ 96 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_huff_iid : lab "huff_iid" = 0x462000#64 :=
  (labAt _ 98 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ff_log2_tab_got : lab "ff_log2_tab_got" = 0x464000#64 :=
  (labAt _ 100 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_ff_log2_tab : lab "ff_log2_tab" = 0x466000#64 :=
  (labAt _ 102 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI0_28 : lab "LCPI0_28" = 0x468000#64 :=
  (labAt _ 104 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI0_30 : lab "LCPI0_30" = 0x46a000#64 :=
  (labAt _ 106 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_sbr_offset_0 : lab "sbr_offset_0" = 0x46c000#64 :=
  (labAt _ 108 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_sbr_offset_1 : lab "sbr_offset_1" = 0x46e000#64 :=
  (labAt _ 110 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_sbr_offset_2 : lab "sbr_offset_2" = 0x470000#64 :=
  (labAt _ 112 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_sbr_offset_3 : lab "sbr_offset_3" = 0x472000#64 :=
  (labAt _ 114 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_sbr_offset_4 : lab "sbr_offset_4" = 0x474000#64 :=
  (labAt _ 116 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_sbr_offset_5 : lab "sbr_offset_5" = 0x476000#64 :=
  (labAt _ 118 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI5_0 : lab "LCPI5_0" = 0x478000#64 :=
  (labAt _ 120 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI5_1 : lab "LCPI5_1" = 0x47a000#64 :=
  (labAt _ 122 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI5_2 : lab "LCPI5_2" = 0x47c000#64 :=
  (labAt _ 124 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI5_3 : lab "LCPI5_3" = 0x47e000#64 :=
  (labAt _ 126 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI5_4 : lab "LCPI5_4" = 0x480000#64 :=
  (labAt _ 128 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI5_6 : lab "LCPI5_6" = 0x482000#64 :=
  (labAt _ 130 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI5_8 : lab "LCPI5_8" = 0x484000#64 :=
  (labAt _ 132 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_LCPI5_9 : lab "LCPI5_9" = 0x486000#64 :=
  (labAt _ 134 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wlab_sbr_make_f_tablelim_bw : lab "sbr_make_f_tablelim_bw" = 0x488000#64 :=
  (labAt _ 136 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

end Kraken.Examples.Sbr.WitEnv
