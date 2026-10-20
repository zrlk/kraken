/-
**Validation part 1: the first lowering pilot's `push`/`pop`
specifications as placement-independent fragment specifications**
(`Lower/FragSpec.lean`). ISA: AArch64; machine: the
executable machine's per-thread environment semantics, partial correctness.

- `pushFrag_spec`, `popFrag_spec`: `Pilot.push_spec`/`pop_spec`
  (`Lower/PilotSpecs.lean`) as `FragSpecEnv` facts, proved once by
  `FragSpecEnv.of_cfg`: the same tables and the same per-block proofs, with
  the ambient code and the placement abstract.
- `pushFrag_pure`, `popFrag_pure`: the purity twins (`Lower/PilotPure.lean`),
  the same at `RP rel`.
- `push_spec_viaFrag`, `pop_spec_viaFrag`, `push_pure_viaFrag`,
  `pop_pure_viaFrag`: the four pilot theorems re-derived at `pilot`, one line
  each; `example : @X_viaFrag = @X := rfl` checks that the statements coincide.
-/
import Kraken.Promising.Lower.FragSpec
import Kraken.Promising.Lower.PilotPure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Pilot

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.SLR.EnvG.Treiber (casOp64)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The fragment specifications, once -/

/-- **`push`'s specification, placement-independent**: `Pilot.push_spec` in
every ambient code that places `pushFrag`. -/
theorem pushFrag_spec (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FragSpecEnv (SharedEnv.counted (EW P w)) pushFrag "push" (PushPre P w) (PushPost P w) := by
  refine FragSpecEnv.of_cfg (fun ra t _ => pushTable P w ra t) rfl (by decide)
    (fun ra t g ⟨hlr, hx0, hx1, ⟨hd8, hd4⟩, hPu⟩ => ⟨hx0, hx1, hd8, hd4, hlr, by simp [CalleeSaved], rfl, hPu⟩) ?_
  intro _ ra t g _
  cfg_cases_env [pushFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hd4, hlr, hfr, -, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hd8]; done)
  case vc5 =>
    rename_i s σ0 v σ1 rng hnone hld _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1]
    exact (vc_push_str hL hw _ hP _).1
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    simp [hx1, hd8] at hst
    obtain ⟨hdm, -, -⟩ := hst
    subst hdm
    simp [hx0, hd8]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have h := (vc_push_cas hL hw _ (hP2.fence hf.1) (BitVec.setWidth 64 v) (by simp)).1
    simp [hx0, hx1]
    simpa [casOp64, Params.top] using h
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 hld hst hf1 hcas hf2 hf3 _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8] at hst
    obtain ⟨hdm, hso, htk⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    have hs2 : σ1.2 ≤ σ2.2 := by omega
    rcases hc with ⟨-, hPu⟩ | ⟨heq, -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
        by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, rfl,
        Pu.fence (Pu.fence hPu.pu hf2.1) hf3.1⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 σ7 hld hst hf1 hcas hf2 hf3 hf4 _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hPo⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    · refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr,
        Po.fence (Po.fence (Po.fence hPo hf2.1) hf3.1) hf4.1⟩
  all_goals done

/-- **`pop`'s specification, placement-independent**: `Pilot.pop_spec` in
every ambient code that places `popFrag`. -/
theorem popFrag_spec (P : Params) (w : Nat) (hw : w < 2) :
    FragSpecEnv (SharedEnv.counted (EW P w)) popFrag "pop" (PopPre P w) (PopPost P w) := by
  refine FragSpecEnv.of_cfg (fun ra t _ => popTable P w ra t) rfl (by decide)
    (fun ra t g ⟨hlr, hx0, ⟨hd8, hd4⟩, hPo⟩ => ⟨hx0, hd8, hd4, hlr, by simp [CalleeSaved], .inl ⟨rfl, hPo⟩⟩) ?_
  intro _ ra t g _
  cfg_cases_env [popFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd8, hd4, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hd8, hd4]; done)
  case vc4 =>
    rename_i s σ0 v σ1 hz σ2 hld hf _
    simp at hz
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hd8], by simp [hd4],
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, .inr ⟨rfl, .inl ⟨by simpa using hz,
        fun a b => DnD.fence (vc_pop_cbz_d _ (vc_pop_ldar (xcl := false) _ hT v σ1.1
          (by simpa [hx0, Params.top] using hld.1)) hz a b) hf.1⟩⟩⟩, .inl (by decide)⟩)
  case vc9 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 hld hf1 hld2 hf2 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 :=
      (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have h := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).1
    simp [hx0]
    simpa [casOp64, Params.top] using h
  case vc10 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 hld hf1 hld2 hf2 hcas hf3 hf4 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 :=
      (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have hc := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).2 old σ5.1
      (by simpa [hx0, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨-, hPo⟩ | ⟨heq, -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hd8], by simp [hd4],
        by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr,
        .inl ⟨rfl, Po.fence (Po.fence hPo hf3.1) hf4.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      have h6 := hf4.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc11 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 hld hf1 hld2 hf2 hcas hf3 hf4 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 :=
      (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have hc := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).2 old σ5.1
      (by simpa [hx0, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hDn⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    refine ⟨by simp [hx0], by simp [hd8], by simp [hd4], by simpa [MachineData.lr] using hlr,
      by simpa [CalleeSaved] using hfr, .inr ⟨trivial, .inr ⟨by simpa using hnz, ?_⟩⟩⟩
    simpa using (hDn.fence hf3.1).fence hf4.1
  case vc1 =>
    rename_i s σ0 σ1 σ2 hf1 hf2 _
    refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, ?_⟩
    simpa using (hT.fence hf1.1).fence hf2.1
  all_goals done

/-- **`push` is pure, placement-independent** (`Pilot.push_pure`). -/
theorem pushFrag_pure (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FragSpecEnv (RP rel) pushFrag "push"
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s') := by
  have hn' : ∀ v : Val, Pred.Pure (rel ⟨n + 8#64, 8⟩) v := hn
  refine FragSpecEnv.of_cfg (fun ra t0 _ => pushPTable rel t n ra t0) rfl (by decide)
    (fun ra t0 g ⟨hlr, hx0, hx1, ⟨hd8, hd4⟩⟩ => ⟨hx0, hx1, hd8, hd4, hlr, by simp [CalleeSaved], rfl⟩) ?_
  intro _ ra t0 g _
  cfg_cases_env [pushFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hd4, hlr, hfr, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hd8, SharedEnv.relPureQ, Arch.storeKind, hn',
    show Arch.armv8.plainStore = .plain from rfl]; done)
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hd8]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hx1, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, hst2⟩ := hst
    have h12 : σ1.2 ≤ σ2.2 := by omega
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩
  all_goals done

/-- **`pop` is pure, placement-independent** (`Pilot.pop_pure`). -/
theorem popFrag_pure (rel : Loc → Pred) (t : BitVec 64) :
    FragSpecEnv (RP rel) popFrag "pop"
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') := by
  refine FragSpecEnv.of_cfg (fun ra t0 _ => popPTable rel t ra t0) rfl (by decide)
    (fun ra t0 g ⟨hlr, hx0, ⟨hd8, hd4⟩⟩ => ⟨hx0, hd8, hd4, hlr, by simp [CalleeSaved], .inl rfl⟩) ?_
  intro _ ra t0 g _
  cfg_cases_env [popFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd8, hd4, hlr, hfr, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hd8, SharedEnv.relPureQ]; done)
  case vc4 =>
    exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hd8], by simp [hd4],
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, .inr rfl⟩, .inl (by decide)⟩)
  case vc9 =>
    simp [hx0, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc10 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp [hd8] at hld2
    have h12 : σ1.2 ≤ σ2.2 := by
      obtain ⟨_, ⟨_, h⟩, _⟩ := hld2
      omega
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hd8], by simp [hd4],
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, .inl rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc11 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp [hd8] at hld2
    obtain ⟨_, ⟨_, -⟩, rfl⟩ := hld2
    exact ⟨by simp [hx0], by simp [hd8], by simp [hd4], by simpa [MachineData.lr] using hlr,
      by simpa [CalleeSaved] using hfr, .inr trivial⟩
  case vc1 =>
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩
  all_goals done

/-! ## `pilot`: the four specifications, one line each -/

section Pilot

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot)]

attribute [local instance] pilot.env

theorem push_spec_viaFrag (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "push") (PushPre P w)
      (PushPost P w) :=
  (pushFrag_spec P w hL hw).of_placed pilot_placed (by decide)

theorem pop_spec_viaFrag (P : Params) (w : Nat) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "pop") (PopPre P w)
      (PopPost P w) :=
  (popFrag_spec P w hw).of_placed pilot_placed (by decide)

theorem push_pure_viaFrag (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "push")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s') :=
  (pushFrag_pure rel t n hn).of_placed pilot_placed (by decide)

theorem pop_pure_viaFrag (rel : Loc → Pred) (t : BitVec 64) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "pop")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') :=
  (popFrag_pure rel t).of_placed pilot_placed (by decide)

end Pilot

example : @push_spec_viaFrag = @push_spec := rfl
example : @pop_spec_viaFrag = @pop_spec := rfl
example : @push_pure_viaFrag = @push_pure := rfl
example : @pop_pure_viaFrag = @pop_pure := rfl

end Kraken.Promising.Lower.Pilot
