/-
**X64 validation: the x64 pilot's `push`/`pop` specifications
as placement-independent fragment specifications** (`Lower/FragSpecX64.lean`).
ISA: x64; environment: the x64 pilot's `EWV P w`, counted;
machine: the executable machine's per-thread environment semantics, partial
correctness.

- `pushFragX_spec`, `popFragX_spec`: `PilotX.push_specX`/`pop_specX`
  (`Lower/PilotX64Specs.lean`) as `FragSpecEnv` facts, proved once by
  `FragSpecEnv.of_cfg`: the same tables and the same per-block proofs, with
  the ambient code and the placement abstract (the only placement-dependent
  term of the x64 pilot proofs was `PlacedIn.of_placedE pilotX_placed _`).
- `push_specX_viaFrag`, `pop_specX_viaFrag`: the two pilot theorems
  re-derived at `pilotX`, one line each; `example : @X_viaFrag = @X := rfl`
  checks that the statements coincide.
-/
import Kraken.Promising.Lower.FragSpecX64
import Kraken.Promising.Lower.PilotX64Specs

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.PilotX

open Kraken.Promising.X64.EnvG.Treiber2X
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The fragment specifications, once -/

/-- **`push`'s specification, placement-independent**: `PilotX.push_specX` in
every ambient code that places `pushFragX`. -/
theorem pushFragX_spec (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FragSpecEnv (SharedEnv.counted (EWV P w)) pushFragX "push" (PushPre P w) (PushPost P w) := by
  refine FragSpecEnv.of_cfg (pushTable P w) rfl (by decide)
    (fun ra t g ⟨h1, h2, _, _, h5⟩ => ⟨rfl, h1, h2, Saved.refl t, rfl, h5⟩) ?_
  intro _
  rintro ra t g ⟨-, -, ⟨v0, hv0, hra⟩, hH, -⟩
  have ea : ∀ s : MachineData, s.regs.get64 .rdi = P.t → s.regs.get64 .rdi + Int64.toBitVec 0 = P.t :=
    fun s h => by simp [h]
  cfg_cases_env [pushFragX]
  intro s₀ g₀
  vcgen
  all_goals obtain ⟨⟨-, hdi, hsi, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hsp, hT⟩, rfl, rfl⟩ :=
    ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX, fenceMonoX_le_valsEnv,
    SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.within_step, SharedEnv.within_ok_load,
    SharedEnv.within_ok_store, SharedEnv.within_ok_rmw, valsEnv_ok, valsEnv_step_load, valsEnv_step_store,
    valsEnv_step_rmw] at *
  all_goals rw [← fdm] at hH; rw [← fdm, ← hsp] at hv0
  all_goals have hdi' := hdi; have hsi' := hsi; have hv0' := hv0; simp only [Reg64s.get64] at hdi' hsi' hv0'
  case vc1 => exact ⟨trivial, by simp [SharedEnv.AccessIn, hdi, hdi']⟩
  case vc2 =>
    rename_i v σ1 _ hld _
    obtain ⟨v, hs, -, -, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hP := vc_push_load _ hT v σ1.1 hs
    have h := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).1
    exact ⟨by simpa [hsi, hsi', Params.nd] using h, by simpa [SharedEnv.AccessIn, hsi, hsi'] using sl_n P hw⟩
  case vc3 =>
    rename_i v σ1 dm σ2 hld hst _
    obtain ⟨rfl, -, -⟩ := stH hH (by simpa [hsi, hsi'] using hp_n P hw) hst
    exact hH.loadInt_none (by simpa [hdi, hdi'] using hp_t P) (by decide)
  case vc4 =>
    rename_i v σ1 dm σ2 hld hst _
    obtain ⟨v, hs, -, -, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, -⟩ := stH hH (by simpa [hsi, hsi'] using hp_n P hw) hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hsi, hsi', Params.nd]) (by simp))
    have h := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).1
    exact ⟨okR h (by simp [hdi, hdi', Params.top]) (by simp [hsi, hsi', cmpxOp64]), by simp [SharedEnv.AccessIn, hdi, hdi']⟩
  case vc5 =>
    rename_i v σ1 dm σ2 old σ3 heq hz σ4 hld hst hcas hf _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result, heq] at hz
  case vc6 =>
    rename_i v σ1 dm σ2 old σ3 heq hz σ4 hnone hld hst hcas hf _
    obtain ⟨rfl, -, -⟩ := stH hH (by simpa [hsi, hsi'] using hp_n P hw) hst
    simp [hv0, hv0'] at hnone
  case vc7 =>
    rename_i v σ1 dm σ2 old σ3 heq hz σ4 ra σ5 hld hst hcas hf hret _
    obtain ⟨v, hs, -, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, l2⟩ := stH hH (by simpa [hsi, hsi'] using hp_n P hw) hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hsi, hsi', Params.nd]) (by simp))
    have hc := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).2 old σ3.1
      (stepR hcas.1.1 (by simp [hdi, hdi', Params.top]) (by simp [hsi, hsi', cmpxOp64]))
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hPo⟩
    · exact absurd heq hne
    obtain ⟨u, hu, rfl, rfl⟩ := private_of_mapped_load (hc := hret) (by simp [hv0, hv0'])
    have e : u = v0 := by simp [hv0, hv0'] at hu; omega
    subst e
    refine .inr ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_, hPo.fence hf.1⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
  case vc8 =>
    rename_i v σ1 dm σ2 old σ3 hne hz σ4 hld hst hcas hf _
    obtain ⟨v, hs, -, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, l2⟩ := stH hH (by simpa [hsi, hsi'] using hp_n P hw) hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hsi, hsi', Params.nd]) (by simp))
    have hc := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).2 old σ3.1
      (stepR hcas.1.1 (by simp [hdi, hdi', Params.top]) (by simp [hsi, hsi', cmpxOp64]))
    simp at hne
    rcases hc with ⟨-, hPu⟩ | ⟨heq', -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨rfl, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_,
        Pu.fence hPu.pu hf.1⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
      rotate_left 9
      · subst hg
        have h3 := hcas.2; have h4 := hf.2
        simp only [SharedAccess.tick] at h3
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
    · exact absurd heq' hne
  case vc9 =>
    rename_i v σ1 dm σ2 old σ3 hne hz σ4 hnone hld hst hcas hf _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm hne
      | exact absurd hz.symm hne
      | exact absurd hz hne
  case vc10 =>
    rename_i v σ1 dm σ2 old σ3 hne hz σ4 ra σ5 hld hst hcas hf hret _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm hne
      | exact absurd hz.symm hne
      | exact absurd hz hne

/-- **`pop`'s specification, placement-independent**: `PilotX.pop_specX` in
every ambient code that places `popFragX`. -/
theorem popFragX_spec (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FragSpecEnv (SharedEnv.counted (EWV P w)) popFragX "pop" (PopPre P w) (PopPost P w) := by
  refine FragSpecEnv.of_cfg (popTable P w) rfl (by decide)
    (fun ra t g ⟨h1, _, _, h4⟩ => ⟨rfl, h1, Saved.refl t, rfl, h4⟩) ?_
  intro _
  rintro ra t g ⟨-, ⟨v0, hv0, hra⟩, hH, -⟩
  have ea : ∀ s : MachineData, s.regs.get64 .rdi = P.t → s.regs.get64 .rdi + Int64.toBitVec 0 = P.t :=
    fun s h => by simp [h]
  cfg_cases_env [popFragX]
  intro s₀ g₀
  vcgen
  all_goals obtain ⟨⟨-, hdi, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hsp, hT⟩, rfl, rfl⟩ :=
    ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX, fenceMonoX_le_valsEnv,
    SharedEnv.counted_step, SharedEnv.counted_ok, valsEnv_ok, valsEnv_step_load, valsEnv_step_rmw] at *
  all_goals rw [← fdm] at hH; rw [← fdm, ← hsp] at hv0
  all_goals have hdi' := hdi; have hv0' := hv0; simp only [Reg64s.get64] at hdi' hv0'
  case vc1 => exact ⟨trivial, by simp [SharedEnv.AccessIn, hdi, hdi']⟩
  case vc2 =>
    rename_i v σ1 af σ2 hz σ3 hld hf1 hf2 _
    obtain ⟨v, hs, hg, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (stepL hs (by simp [hdi, hdi', Params.top]))).fence
      hf1.1).fence hf2.1
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_, hPl.po⟩,
      .inr fun ⟨_, hg'⟩ => ?_⟩)
    rotate_left 8
    · subst hg'
      have := hf1.2; have := hf2.2
      omega
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
  case vc3 =>
    rename_i v σ1 af σ2 hz σ3 hnone hld hf1 hf2 _
    obtain ⟨v, hs, hg, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hz' : BitVec.setWidth 64 v ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    obtain ⟨w', hw', hn'⟩ := gv_node hg hz'
    exact ⟨trivial, by simpa [SharedEnv.AccessIn, hn'] using sl_n P hw'⟩
  case vc4 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 hld hf1 hf2 hld2 _
    exact hH.loadInt_none (by simpa [hdi, hdi'] using hp_t P) (by decide)
  case vc5 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 hld hf1 hf2 hld2 _
    obtain ⟨v, hs, hg, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (stepL hs (by simp [hdi, hdi', Params.top]))).fence
      hf1.1).fence hf2.1
    have hz' : BitVec.setWidth 64 v ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    obtain ⟨w', hw', hn'⟩ := gv_node hg hz'
    obtain ⟨u, hs2, -, l2, rfl⟩ := ldH hH (by simp [hn']; exact hp_n P hw') hld2
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ4.1 (stepL hs2 (by simp))
    have h := (vc_pop_cas hw _ hPr hz').1
    exact ⟨okR h (by simp [hdi, hdi', Params.top]) (by simp [cmpxOp64]), by simp [SharedEnv.AccessIn, hdi, hdi']⟩
  case vc6 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 heq hz2 σ6 hld hf1 hf2 hld2 hcas hf3 _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result, heq] at hz2
  case vc7 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 heq hz2 σ6 hnone hld hf1 hf2 hld2 hcas hf3 _
    simp [hv0, hv0'] at hnone
  case vc8 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 heq hz2 σ6 ra σ7 hld hf1 hf2 hld2 hcas hf3 hret _
    obtain ⟨v, hs, hg, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (stepL hs (by simp [hdi, hdi', Params.top]))).fence
      hf1.1).fence hf2.1
    have hz' : BitVec.setWidth 64 v ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    obtain ⟨w', hw', hn'⟩ := gv_node hg hz'
    obtain ⟨u, hs2, -, l2, rfl⟩ := ldH hH (by simp [hn']; exact hp_n P hw') hld2
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ4.1 (stepL hs2 (by simp))
    have hc := (vc_pop_cas hw _ hPr hz').2 old σ5.1
      (stepR hcas.1.1 (by simp [hdi, hdi', Params.top]) (by simp [cmpxOp64]))
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hDn⟩
    · exact absurd heq hne
    obtain ⟨u', hu, rfl, rfl⟩ := private_of_mapped_load (hc := hret) (by simp [hv0, hv0'])
    have e : u' = v0 := by simp [hv0, hv0'] at hu; omega
    subst e
    refine .inr ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_, ?_⟩
    rotate_left 7
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact hDn.fence hf3.1
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
  case vc9 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 hne hz2 σ6 hld hf1 hf2 hld2 hcas hf3 _
    obtain ⟨v, hs, hg, l1, rfl⟩ := ldH hH (by rw [ea _ hdi]; exact hp_t P) hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (stepL hs (by simp [hdi, hdi', Params.top]))).fence
      hf1.1).fence hf2.1
    have hz' : BitVec.setWidth 64 v ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    obtain ⟨w', hw', hn'⟩ := gv_node hg hz'
    obtain ⟨u, hs2, -, l2, rfl⟩ := ldH hH (by simp [hn']; exact hp_n P hw') hld2
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ4.1 (stepL hs2 (by simp))
    have hc := (vc_pop_cas hw _ hPr hz').2 old σ5.1
      (stepR hcas.1.1 (by simp [hdi, hdi', Params.top]) (by simp [cmpxOp64]))
    simp at hne
    rcases hc with ⟨-, hPo⟩ | ⟨heq', -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_,
        hPo.fence hf3.1⟩, .inr fun ⟨_, hg'⟩ => ?_⟩)
      rotate_left 8
      · subst hg'
        have := hf1.2; have := hf2.2; have := hf3.2; have h3 := hcas.2
        simp only [SharedAccess.tick] at h3
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
    · exact absurd heq' hne
  case vc10 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 hne hz2 σ6 hnone hld hf1 hf2 hld2 hcas hf3 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz2).symm hne
      | exact absurd hz2.symm hne
      | exact absurd hz2 hne
  case vc11 =>
    rename_i v σ1 af σ2 hz σ3 u σ4 old σ5 hne hz2 σ6 ra σ7 hld hf1 hf2 hld2 hcas hf3 hret _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz2).symm hne
      | exact absurd hz2.symm hne
      | exact absurd hz2 hne

/-! ## `pilotX`: the two specifications, one line each -/

section PilotX

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilotX)]

attribute [local instance] pilotX.env

theorem push_specX_viaFrag (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EWV P w)) ((_root_.Executable.labels cenv).label "push")
      (PushPre P w) (PushPost P w) :=
  (pushFragX_spec P w hL hw).of_placed pilotX_placed (by decide)

theorem pop_specX_viaFrag (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EWV P w)) ((_root_.Executable.labels cenv).label "pop")
      (PopPre P w) (PopPost P w) :=
  (popFragX_spec P w hL hw).of_placed pilotX_placed (by decide)

end PilotX

example : @push_specX_viaFrag = @push_specX := rfl
example : @pop_specX_viaFrag = @pop_specX := rfl

end Kraken.Promising.Lower.PilotX
