/-
**AArch64 validation: the MS queue pilot's `enq`/`deq`
specifications and their purity twins as placement-independent fragment
specifications** (`Lower/FragSpec.lean`, `Lower/FragSpecRank.lean`). ISA:
AArch64; environments: msqueue2's `EE2 P`/`ED2 P` counted, and
`RP rel`; machine: the executable machine's per-thread environment semantics,
partial correctness.

- `enqFrag_spec`, `enqFrag_pure`: `MsqPilot.enq_spec`/`enq_pure` by
  `FragSpecEnv.of_cfg`.
- `deqFrag_spec`, `deqFrag_pure`: `MsqPilot.deq_spec`/`deq_pure` by
  `FragSpecEnv.of_cfgRank` (the rank `deqRank`: `deq`'s zero-step back edge).
- The same tables, local tactics and per-block proofs as
  `Lower/MsqPilotSpecs.lean`/`MsqPilotPure.lean` (the tactics are local there,
  so they are repeated here), with the ambient code and the placement abstract.
- `enq_spec_viaFrag`, `enq_pure_viaFrag` at `progE` and `deq_spec_viaFrag`,
  `deq_pure_viaFrag` at `progD`, one line each, with
  `example : @X_viaFrag = @X := rfl`.
-/
import Kraken.Promising.Lower.FragSpecRank
import Kraken.Promising.Lower.MsqPilotPure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.MsqPilot

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.SLR.EnvG.Treiber (casOp64)
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## `enq` -/

set_option hygiene false in
/-- Jump to a table row (selected by `decide`) with its facts `t`, the frame
kept; leaves the edge condition. -/
local macro "eland" t:term : tactic => `(tactic| (
  first
  | refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hd8, by simpa using hd4,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, ?_⟩, ?_⟩)
    · simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true]
      exact $t
  | refine ⟨by simpa using hd8, by simpa using hd4, by simpa [MachineData.lr] using hlr,
      by simpa [CalleeSaved] using hfr, ?_⟩
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true]
    exact $t))


set_option hygiene false in
/-- The two reads of a loop iteration (`h2`: `EL2'` after them), as
`MsQueue2VCGen`'s `e_reads`. -/
local macro "e_reads" : tactic => `(tactic| (
  obtain ⟨hx1, hx2, hE⟩ := hT
  have h1 := (vc_e_ldar_tail2 (xcl := false) hph _ hE v3 σ1.1 (by simpa [hx1, Params.tail] using hld1.1)).fence
    hph hf1.1
  have h2 := (vc_e_ldar_link2 hph _ h1 v4 σ3.1 (by simpa using hld2.1)).fence hph hf2.1))


/-- **`enq`'s specification, placement-independent**: `MsqPilot.enq_spec` in
every ambient code that places `enqFrag`. -/
theorem enqFrag_spec (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (ph : Ph) (hph : PhOk P ph) :
    FragSpecEnv (SharedEnv.counted (EE2 P)) enqFrag "enq" (EnqPre P ph) (EnqPost P ph) := by
  refine FragSpecEnv.of_cfg (fun ra t _ => enqTable P ph ra t) rfl (by decide)
    (fun ra t g ⟨hlr, hx0, hx1, ⟨hd8, hd4⟩, hEL⟩ => ⟨hd8, hd4, hlr, by simp [CalleeSaved], .inl ⟨rfl, hx0, hx1, hEL⟩⟩) ?_
  intro _ ra t g _
  cfg_cases_env [enqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd8, hd4, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hd8, hd4]; done)
  case vc1 =>
    rename_i s σ0 σ1 σ2 hf1 hf2 _
    obtain ⟨hx0, hx1, hE⟩ := hT
    eland ⟨by simp [hx0, ht], by simp [hx1], (hE.fence hph hf1.1).fence hph hf2.1⟩
  case vc7 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hnz σ4 hld1 hf1 hld2 hf2 _
    e_reads
    simp at hnz
    eland ⟨by simp [hx1], by simp [hx2], v3, v4, by simp, by simp, hnz, h2⟩
    exact .inl (by decide)
  case vc10 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 hld1 hf1 hld2 hf2 hf3 _
    e_reads
    have h := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).1
    simp [hx2]
    simpa [casOp64] using h
  case vc11 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hnz5 σ7 hld1 hf1 hld2 hf2 hf3 hcas hf4 _
    e_reads
    have hc := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hx2, casOp64] using hcas.1)
    simp at hnz5
    rcases hc with ⟨-, hEL⟩ | ⟨h0, -⟩
    · eland ⟨by simp [hx1], by simp [hx2], hEL.fence hph hf4.1⟩
      refine .inr fun ⟨_, hg⟩ => ?_
      subst hg
      have e1 := hld1.2; have e2 := hld2.2; have e3 := hcas.2; have e4 := hf1.2; have e5 := hf2.2
      have e6 := hf3.2; have e7 := hf4.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at e1 e2 e3
      omega
    · exact absurd (by simpa using h0) hnz5
  case vc14 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hz5 σ7 σ8 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5 _
    e_reads
    have hc := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hx2, casOp64] using hcas.1)
    simp at hz5
    rcases hc with ⟨hne, -⟩ | ⟨-, hC⟩
    · exact absurd (by simpa using hz5) hne
    have h := (vc_e_swing2 hL hph _ ((hC.fence hph hf4.1).fence hph hf5.1) (BitVec.setWidth 64 v3)).1
    simp [hx1, hx2]
    simpa [casOp64, Params.tail] using h
  case vc15 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hz5 σ7 σ8 old2 σ9 σ10 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5 hcas2 hf6 _
    e_reads
    have hc := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hx2, casOp64] using hcas.1)
    simp at hz5
    rcases hc with ⟨hne, -⟩ | ⟨-, hC⟩
    · exact absurd (by simpa using hz5) hne
    have hC2 := (vc_e_swing2 hL hph _ ((hC.fence hph hf4.1).fence hph hf5.1) (BitVec.setWidth 64 v3)).2 old2 σ9.1
      (by simpa [hx1, hx2, casOp64, Params.tail] using hcas2.1)
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, hC2.fence hph hf6.1⟩
  case vc3 =>
    rename_i s σ0 σ1 hf1 _
    obtain ⟨hx1, hx2, y3, y4, hy3, hy4, hnz, h2⟩ := hT
    have h := (vc_e_fix2 hL hph _ (h2.fence hph hf1.1) hnz).1
    simp [hx1, hy3, hy4]
    simpa [casOp64, Params.tail] using h
  case vc4 =>
    rename_i s σ0 σ1 old σ2 σ3 hf1 hcas hf2 _
    obtain ⟨hx1, hx2, y3, y4, hy3, hy4, hnz, h2⟩ := hT
    have hEL := (vc_e_fix2 hL hph _ (h2.fence hph hf1.1) hnz).2 old σ2.1
      (by simpa [hx1, hy3, hy4, casOp64, Params.tail] using hcas.1)
    eland ⟨by simp [hx1], by simp [hx2], hEL.fence hph hf2.1⟩
    refine .inr fun ⟨_, hg⟩ => ?_
    subst hg
    have e1 := hcas.2; have e2 := hf1.2; have e3 := hf2.2
    simp only [SharedEnv.tick_rmw] at e1
    omega
  all_goals done

/-! ## `deq` -/

set_option hygiene false in
/-- Jump to `deq`'s table row of the target label with its facts `t`. -/
local macro "dland" t:term : tactic => `(tactic| (
  refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4,
    by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, ?_⟩, ?_⟩)
  · (simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true])
    exact $t))


set_option hygiene false in
/-- The three reads of an iteration (`h3`: `DQ3` after them), as
`MsQueue2VCGen`'s `d_reads`. -/
local macro "d_reads" : tactic => `(tactic| (
  have hY := yok_kept P g.1
  have h1 := vc_d_ldar_head2 (xcl := false) hY _ (hT.1.fence hfa.1) (hY.fence hT.2 hfa.1) v3 σ1.1 (by simpa [hx0, Params.head] using hld1.1)
  have h2 := (vc_d_load2 hY _ h1 v4 σ2.1 hld2.1).fence hY hf1.1
  have h3 := ((vc_d_ldar_link2 hY _ h2 v5 σ4.1 (by simpa using hld3.1)).fence hY hf2.1).fence hY hf3.1))


set_option hygiene false in
/-- The edge back to `deq` (the variant decreased). -/
local macro "d_back" : tactic => `(tactic| (
  refine .inr (.inr fun ⟨_, hg⟩ => ?_)
  subst hg
  simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *
  omega))


/-- **`deq`'s specification, placement-independent**: `MsqPilot.deq_spec` in
every ambient code that places `deqFrag`. -/
theorem deqFrag_spec (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) :
    FragSpecEnv (SharedEnv.counted (ED2 P)) deqFrag "deq" (DeqPre P) (DeqPost P) := by
  refine FragSpecEnv.of_cfgRank (fun ra t g => deqTable P ra t g.1) deqRank rfl (by decide)
    (fun ra t g ⟨hlr, hx0, ⟨hd8, hd4⟩, hC⟩ => ⟨hx0, hd8, hd4, hlr, by simp [CalleeSaved], .inl ⟨rfl, hC, fun _ h => h⟩⟩) ?_
  intro _ ra t g _
  cfg_cases_env_rank [deqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd8, hd4, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hd8]; done)
  case vc10 =>
    rename_i s σ0 σa v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hfa hld1 hld2 hf1 hld3 hf2 hf3 _
    d_reads
    dland ⟨v3, v5, by simp, by simp, h3⟩
    have e0 := hfa.2; have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    d_back
  case vc11 =>
    rename_i s σ0 σa v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hz σ7 hfa hld1 hld2 hf1 hld3 hf2 hf3 hf4 _
    d_reads
    dland ⟨(h3.fence hY hf4.1).1, (h3.fence hY hf4.1).2.1⟩
    have e0 := hfa.2; have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    have e7 := hf4.2
    d_back
  case vc14 =>
    rename_i s σ0 σa v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hnz σ7 σ8 hfa hld1 hld2 hf1 hld3 hf2 hf3 hf4 hf5 _
    d_reads
    simp at hnz
    have h := (vc_d_help2 hL hY _ ((h3.fence hY hf4.1).fence hY hf5.1) hnz).1
    simp [hx0]
    simpa [casOp64, Params.tail, ht] using h
  case vc15 =>
    rename_i s σ0 σa v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hnz σ7 σ8 old σ9 σ10 hfa hld1 hld2 hf1 hld3 hf2 hf3 hf4 hf5 hcas hf6 _
    d_reads
    simp at hnz
    have hc := (vc_d_help2 hL hY _ ((h3.fence hY hf4.1).fence hY hf5.1) hnz).2 old σ9.1
      (by simpa [hx0, ht, casOp64, Params.tail] using hcas.1)
    dland ⟨hc.1.fence hf6.1, hY.fence hc.2 hf6.1⟩
    have e0 := hfa.2; have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    have e7 := hf4.2; have e8 := hf5.2; have e9 := hcas.2; have e10 := hf6.2
    d_back
  case vc1 =>
    rename_i s σ0 hz σ1 hf _
    have hY := yok_kept P g.1
    obtain ⟨y3, y5, -, -, hD3⟩ := hT
    dland ⟨(hD3.fence hY hf.1).1, (hD3.fence hY hf.1).2.1⟩
    exact .inl (by decide)
  case vc6 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 hf1 hld hf2 _
    have hY := yok_kept P g.1
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr2 hY _ (hD3.fence hY hf1.1) hnz' u σ2.1 hu.1).fence hY hf2.1
    have h := (vc_d_cas2 hL hY _ hD4).1
    simp [hx0, hy3, hy5]
    simpa [casOp64, Params.head] using h
  case vc7 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 old σ4 σ5 hne σ6 hf1 hld hf2 hcas hf3 hf4 _
    have hY := yok_kept P g.1
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr2 hY _ (hD3.fence hY hf1.1) hnz' u σ2.1 hu.1).fence hY hf2.1
    have hc := (vc_d_cas2 hL hY _ hD4).2 old σ4.1 (by simpa [hx0, hy3, hy5, casOp64, Params.head] using hcas.1)
    dland ⟨(hc.1.fence hf3.1).fence hf4.1, hY.fence (hY.fence hc.2.1 hf3.1) hf4.1⟩
    exact .inl (by decide)
  case vc8 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 old σ4 σ5 heq σ6 σ7 σ8 hf1 hld hf2 hcas hf3 hf4 hf5 hf6 _
    have hY := yok_kept P g.1
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr2 hY _ (hD3.fence hY hf1.1) hnz' u σ2.1 hu.1).fence hY hf2.1
    have hc := (vc_d_cas2 hL hY _ hD4).2 old σ4.1 (by simpa [hx0, hy3, hy5, casOp64, Params.head] using hcas.1)
    simp [hy3] at heq
    obtain ⟨hF, hD⟩ := hc.2.2 (TreiberCommon.bv64_eq_of_sub_eq_zero heq)
    have hY1 := yok_first (P := P) (BitVec.setWidth 64 (BitVec.setWidth 32 u))
    refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr,
      (((hc.1.fence hf3.1).fence hf4.1).fence hf5.1).fence hf6.1, ?_, ?_⟩
    · simpa using hY1.fence (hY1.fence (hY1.fence (hY1.fence hF hf3.1) hf4.1) hf5.1) hf6.1
    · intro x0 h0
      have := hD x0 (hD4.2.1 x0 h0)
      simpa [hf3.1.snap, hf4.1.snap, hf5.1.snap, hf6.1.snap] using this
  all_goals done


/-! ## The purity twins -/

set_option hygiene false in
/-- The purity VCs of a function: `casal`s unconstrained, jumps into the
table (forward, down the rank, or after a step), `ret` into the frame. -/
local macro "pure_vcs" : tactic => `(tactic| (
  all_goals try (simp [hd8, SharedEnv.relPureQ]; done)
  all_goals try (simp [SharedEnv.relPureQ]; exact fun h => (h (by decide)).elim)
  all_goals try (exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩)
  all_goals try (exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4,
    by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩, by simp (config := { decide := true })⟩,
    by first | exact .inl (by decide) | exact .inr (.inl ⟨by decide, by decide⟩)⟩))
  all_goals try (exact ⟨⟨by simpa using hd8, by simpa using hd4, by simpa [MachineData.lr] using hlr,
    by simpa [CalleeSaved] using hfr⟩, by simp (config := { decide := true })⟩)
  all_goals (
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩,
      by simp (config := { decide := true })⟩, ?_⟩)
    first
    | exact .inr fun ⟨_, hg⟩ => by subst hg; simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *; omega
    | exact .inr (.inr fun ⟨_, hg⟩ => by
        subst hg; simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *; omega))))

/-- **`enq` is pure, placement-independent** (`MsqPilot.enq_pure`). -/
theorem enqFrag_pure (rel : Loc → Pred) :
    FragSpecEnv (RP rel) enqFrag "enq" (fun ra s _ => s.lr = ra ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') := by
  refine FragSpecEnv.of_cfg
    (fun ra t0 _ lb s (_ : (RP rel).State) => PFrame ra t0 s ∧ (lb = "enq" ∨ lb = "enq_loop" ∨ lb = "enq_fix"))
    rfl (by decide) (fun ra t0 g ⟨hlr, ⟨hd8, hd4⟩⟩ => ⟨⟨hd8, hd4, hlr, by simp [CalleeSaved]⟩, .inl rfl⟩) ?_
  intro _ ra t0 g _
  cfg_cases_env [enqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hd8, hd4, hlr, hfr⟩, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  pure_vcs

/-- **`deq` is pure, placement-independent** (`MsqPilot.deq_pure`). -/
theorem deqFrag_pure (rel : Loc → Pred) :
    FragSpecEnv (RP rel) deqFrag "deq" (fun ra s _ => s.lr = ra ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') := by
  refine FragSpecEnv.of_cfgRank
    (fun ra t0 _ lb s (_ : (RP rel).State) => PFrame ra t0 s ∧ (lb = "deq" ∨ lb = "deq_ne")) deqRank
    rfl (by decide) (fun ra t0 g ⟨hlr, ⟨hd8, hd4⟩⟩ => ⟨⟨hd8, hd4, hlr, by simp [CalleeSaved]⟩, .inl rfl⟩) ?_
  intro _ ra t0 g _
  cfg_cases_env_rank [deqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hd8, hd4, hlr, hfr⟩, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  pure_vcs

/-! ## `progE`, `progD`: the four specifications, one line each -/

section E

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progE)]

attribute [local instance] progE.env

theorem enq_spec_viaFrag (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (ph : Ph) (hph : PhOk P ph) :
    FunSpecPartialEnv (SharedEnv.counted (EE2 P)) ((_root_.Executable.labels cenv).label "enq") (EnqPre P ph)
      (EnqPost P ph) :=
  (enqFrag_spec P hL ht ph hph).of_placed progE_placed (by decide)

theorem enq_pure_viaFrag (rel : Loc → Pred) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "enq")
      (fun ra s _ => s.lr = ra ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') :=
  (enqFrag_pure rel).of_placed progE_placed (by decide)

end E

section D

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progD)]

attribute [local instance] progD.env

theorem deq_spec_viaFrag (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) :
    FunSpecPartialEnv (SharedEnv.counted (ED2 P)) ((_root_.Executable.labels cenv).label "deq") (DeqPre P)
      (DeqPost P) :=
  (deqFrag_spec P hL ht).of_placed progD_placed (by decide)

theorem deq_pure_viaFrag (rel : Loc → Pred) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "deq")
      (fun ra s _ => s.lr = ra ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') :=
  (deqFrag_pure rel).of_placed progD_placed (by decide)

end D

example : @enq_spec_viaFrag = @enq_spec := rfl
example : @enq_pure_viaFrag = @enq_pure := rfl
example : @deq_spec_viaFrag = @deq_spec := rfl
example : @deq_pure_viaFrag = @deq_pure := rfl

end Kraken.Promising.Lower.MsqPilot
