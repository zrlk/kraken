/-
**The specifications of WeakCore's `enq`**
(`WcMsq.wcEnqFrag`), placement-independent (`FragSpecEnv`,
`Lower/FragSpec.lean`). ISA: AArch64; machine: the
executable machine's per-thread environment semantics, partial correctness.

- `wcEnqFrag_spec`: in msqueue2's enqueuer environment `counted (EE2 P)`,
  from `MsqPilot`'s `EnqPre` to `EnqPost` (the same pre/post as
  `MsqPilot.enqFrag_spec`): one `vcgen` call per block with
  `Lower/WcEnqVC.lean`'s VCs for the two plain reads and msqueue2's
  `vc_e_swing2` for the swing; `MsqPilot`'s table with `EL2w` for `EL2'`.
- `wcEnqFrag_pure`: its purity twin in `RP rel` (`MsqPilot`'s `enqFrag_pure`;
  its writes are release `casal`s).
-/
import Kraken.Promising.Lower.WcEnqVC
import Kraken.Promising.Lower.FragSpecMsq

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.WcMsq

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.SLR.EnvG.Treiber (casOp64)
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP)
open Kraken.Promising.Lower.MsqPilot (EnqPre EnqPost PFrame)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- `enq`'s table: `MsqPilot`'s `enqTable` with `EL2w` at `enq_fix`. -/
abbrev wenqTable (P : Params2) (ph : Ph) (ra : Int64) (t : MachineData) :
    Label → MachineData → (SharedEnv.counted (EE2 P)).State → Prop :=
  fun lb s σ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.lr = ra ∧
    CalleeSaved t s ∧
    ((lb = "enq" ∧ s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = ph.n ∧ EL' P ph σ.1) ∨
      (lb = "enq_loop" ∧ s.regs.X1.toBitVec = P.t ∧ s.regs.X2.toBitVec = ph.n ∧ EL' P ph σ.1) ∨
      (lb = "enq_fix" ∧ s.regs.X1.toBitVec = P.t ∧ s.regs.X2.toBitVec = ph.n ∧ ∃ y3 y4 : Val,
        s.regs.X3.toBitVec = BitVec.setWidth 64 y3 ∧ s.regs.X4.toBitVec = BitVec.setWidth 64 y4 ∧
        BitVec.setWidth 64 y4 ≠ 0 ∧ EL2w P ph y3 y4 σ.1))

set_option hygiene false in
/-- Jump to a table row (selected by `decide`) with its facts `t`, the frame
kept; leaves the edge condition (`MsqPilot`'s `eland`). -/
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
/-- The two plain reads of a loop iteration (`h2`: `EL2w` after them). -/
local macro "e_readsw" : tactic => `(tactic| (
  obtain ⟨hx1, hx2, hE⟩ := hT
  simp [hd8] at hld1 hld2
  obtain ⟨u3, hu3, rfl⟩ := hld1
  obtain ⟨u4, hu4, rfl⟩ := hld2
  rw [hx1] at hu3
  have h1 := (vc_e_ldr_tail hph _ hE u3 σ1.1 (by simpa [Params.tail] using hu3.1)).fence hph hf1.1
  have h2 := (vc_e_ldr_link hph _ h1 u4 σ3.1 (by simpa using hu4.1)).fence hph hf2.1))

/-- **WeakCore's `enq`, specified**, placement-independent, for both phases. -/
theorem wcEnqFrag_spec (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (ph : Ph) (hph : PhOk P ph) :
    FragSpecEnv (SharedEnv.counted (EE2 P)) wcEnqFrag "enq" (EnqPre P ph) (EnqPost P ph) := by
  refine FragSpecEnv.of_cfg (fun ra t _ => wenqTable P ph ra t) rfl (by decide)
    (fun ra t g ⟨hlr, hx0, hx1, ⟨hd8, hd4⟩, hEL⟩ => ⟨hd8, hd4, hlr, by simp [CalleeSaved], .inl ⟨rfl, hx0, hx1, hEL⟩⟩) ?_
  intro _ ra t g _
  cfg_cases_env [wcEnqFrag]
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
  case vc5 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v4 σ3 hnz σ4 hld1 hf1 hld2 hf2 _
    e_readsw
    simp at hnz
    eland ⟨by simp [hx1], by simp [hx2], u3, u4, by simp, by simp, hnz, h2⟩
    exact .inl (by decide)
  case vc8 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v4 σ3 hz σ4 σ5 hld1 hf1 hld2 hf2 hf3 _
    e_readsw
    have h := (vc_e_linkw hL hph _ (h2.fence hph hf3.1)).1
    simp [hx2]
    simpa [casOp64] using h
  case vc9 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v4 σ3 hz σ4 σ5 old σ6 hnz5 σ7 hld1 hf1 hld2 hf2 hf3 hcas hf4 _
    e_readsw
    have hc := (vc_e_linkw hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hx2, casOp64] using hcas.1)
    simp at hnz5
    rcases hc with ⟨-, hEL⟩ | ⟨h0, -⟩
    · eland ⟨by simp [hx1], by simp [hx2], hEL.fence hph hf4.1⟩
      refine .inr fun ⟨_, hg⟩ => ?_
      subst hg
      have e1 := hu3.2; have e2 := hu4.2; have e3 := hcas.2; have e4 := hf1.2; have e5 := hf2.2
      have e6 := hf3.2; have e7 := hf4.2
      simp only [SharedEnv.tick_rmw] at e1 e2 e3
      omega
    · exact absurd (by simpa using h0) hnz5
  case vc12 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v4 σ3 hz σ4 σ5 old σ6 hz5 σ7 σ8 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5 _
    e_readsw
    have hc := (vc_e_linkw hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hx2, casOp64] using hcas.1)
    simp at hz5
    rcases hc with ⟨hne, -⟩ | ⟨-, hC⟩
    · exact absurd (by simpa using hz5) hne
    have h := (vc_e_swing2 hL hph _ ((hC.fence hph hf4.1).fence hph hf5.1) (BitVec.setWidth 64 u3)).1
    simp [hx1, hx2]
    simpa [casOp64, Params.tail] using h
  case vc13 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v4 σ3 hz σ4 σ5 old σ6 hz5 σ7 σ8 old2 σ9 σ10 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5
      hcas2 hf6 _
    e_readsw
    have hc := (vc_e_linkw hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hx2, casOp64] using hcas.1)
    simp at hz5
    rcases hc with ⟨hne, -⟩ | ⟨-, hC⟩
    · exact absurd (by simpa using hz5) hne
    have hC2 := (vc_e_swing2 hL hph _ ((hC.fence hph hf4.1).fence hph hf5.1) (BitVec.setWidth 64 u3)).2 old2 σ9.1
      (by simpa [hx1, hx2, casOp64, Params.tail] using hcas2.1)
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, hC2.fence hph hf6.1⟩
  case vc3 =>
    rename_i s σ0 σ1 hf1 _
    obtain ⟨hx1, hx2, y3, y4, hy3, hy4, hnz, h2⟩ := hT
    have h := (vc_e_fixw hL hph _ (h2.fence hph hf1.1) hnz).1
    simp [hx1, hy3, hy4]
    simpa [casOp64, Params.tail] using h
  case vc4 =>
    rename_i s σ0 σ1 old σ2 σ3 hf1 hcas hf2 _
    obtain ⟨hx1, hx2, y3, y4, hy3, hy4, hnz, h2⟩ := hT
    have hEL := (vc_e_fixw hL hph _ (h2.fence hph hf1.1) hnz).2 old σ2.1
      (by simpa [hx1, hy3, hy4, casOp64, Params.tail] using hcas.1)
    eland ⟨by simp [hx1], by simp [hx2], hEL.fence hph hf2.1⟩
    refine .inr fun ⟨_, hg⟩ => ?_
    subst hg
    have e1 := hcas.2; have e2 := hf1.2; have e3 := hf2.2
    simp only [SharedEnv.tick_rmw] at e1
    omega
  all_goals done

set_option hygiene false in
/-- The purity VCs of `enq` (`MsqPilot`'s `pure_vcs`, local there). -/
local macro "pure_vcs" : tactic => `(tactic| (
  all_goals try (simp [hd8, hd4, SharedEnv.relPureQ]; done)
  all_goals try (simp [SharedEnv.relPureQ]; exact fun h => (h (by decide)).elim)
  all_goals try (exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩)
  all_goals try (exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4,
    by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩, by simp (config := { decide := true })⟩,
    .inl (by decide)⟩))
  all_goals try (exact ⟨⟨by simpa using hd8, by simpa using hd4, by simpa [MachineData.lr] using hlr,
    by simpa [CalleeSaved] using hfr⟩, by simp (config := { decide := true })⟩)
  all_goals (
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩,
      by simp (config := { decide := true })⟩, ?_⟩)
    exact .inr fun ⟨_, hg⟩ => by
      subst hg; simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *
      grind)))

/-- **WeakCore's `enq` is pure** (no plain store), placement-independent. -/
theorem wcEnqFrag_pure (rel : Loc → Pred) :
    FragSpecEnv (RP rel) wcEnqFrag "enq" (fun ra s _ => s.lr = ra ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') := by
  refine FragSpecEnv.of_cfg
    (fun ra t0 _ lb s (_ : (RP rel).State) => PFrame ra t0 s ∧ (lb = "enq" ∨ lb = "enq_loop" ∨ lb = "enq_fix"))
    rfl (by decide) (fun ra t0 g ⟨hlr, ⟨hd8, hd4⟩⟩ => ⟨⟨hd8, hd4, hlr, by simp [CalleeSaved]⟩, .inl rfl⟩) ?_
  intro _ ra t0 g _
  cfg_cases_env [wcEnqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hd8, hd4, hlr, hfr⟩, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  pure_vcs

end Kraken.Promising.Lower.WcMsq
