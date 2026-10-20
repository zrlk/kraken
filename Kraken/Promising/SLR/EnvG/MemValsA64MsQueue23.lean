/-
**`msqueue2.kl` and `msqueue3.kl` (AArch64) never fault at the runner's
declarations**: `msqueue2_envG_runner_faultFree`,
`msqueue3_envG_runner_faultFree` and their `_concrete` instances,
program-level `Config.FaultFree` from the runner's start states under any
architecture (promises included).

`MemValsA64MsQueue`'s value condition `msqGA h t d n1 n2` and layout
`msqSA h t d n1 n2` (the null node's link included), with the runs of the
two-node enqueuer `enq2Prog`, the two-round dequeuer `deq2Prog` and the
second dequeuer `deqBProg` (`enq2_val_at`, `deq2_val_at`, `deqB_val_at`:
the MS queue proof's purity scripts in the counted `inv S G`, register tables only),
each in the whole image from its entry label to its exit label.

Phase-1 limit: single-access trees (`msq2Image_dirs`, `msq3Image_dirs`).
-/
import Kraken.Promising.SLR.EnvG.MemValsA64MsQueue
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue2Runner
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue3Runner

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.MsQueue

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The runs -/

section Enq2At

variable [CodeEnv]

/-- The two-node enqueuer's value table: `x1 = t`, `x12`, `x13` nodes,
`dmem` maps no 8- or 4-byte word; `x2` a node inside a round, and `x4` a `V`
value at the `fix` labels. -/
abbrev enq2ValTable (h t d n1 n2 : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (msqEnvA h t d n1 n2)).State → Prop :=
  fun lb s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    s.regs.X1.toBitVec = t ∧ MsqNodeA d n1 n2 s.regs.X12.toBitVec ∧ MsqNodeA d n1 n2 s.regs.X13.toBitVec ∧
    (lb = "enq1" ∨ lb = "enq2" ∨
      ((lb = "enq1_loop" ∨ lb = "enq1_end" ∨ lb = "enq2_loop" ∨ lb = "enq2_end" ∨ lb = "pdone") ∧
        MsqNodeA d n1 n2 s.regs.X2.toBitVec) ∨
      ((lb = "enq1_fix" ∨ lb = "enq2_fix") ∧ MsqNodeA d n1 n2 s.regs.X2.toBitVec ∧
        (s.regs.X4.toBitVec = 0 ∨ MsqNodeA d n1 n2 s.regs.X4.toBitVec)))

/-- **The two-node enqueuer in the value environment**, in any ambient code
in which `enq2Prog` is `PlacedIn`, from `enq1` to the end address `endA` of
its last block. -/
theorem enq2_val_at (h t d n1 n2 : BitVec 64) (hpl : Program.PlacedIn enq2Prog) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt enq2Prog l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (enq2ValTable h t d n1 n2) "enq1" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (msqEnvA h t d n1 n2)))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "enq1"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (msqEnvA h t d n1 n2)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (enq2ValTable h t d n1 n2) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [enq2Prog]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd8, hd4, hx1, hx12, hx13, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, MsqValLA, MsqValVA, MsqNodeA]; done)
  -- forward jumps
  all_goals try (refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx1],
    by simpa using hx12, by simpa using hx13, ?_⟩, .inl (by decide)⟩; simp (config := { decide := true }) [hT]; done)
  case vc7 =>
    rename_i s σ0 v3 σ1 v4 σ2 hnz hld1 hld2 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx1, MsqValLA] using hld1.1
    have hv4 : MsqValVA d n1 n2 v4 := by
      have h2 := hld2.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h2
      exact h2 (msqValLA_link hv3)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx1], by simpa using hx12, by simpa using hx13, ?_⟩, .inl (by decide)⟩
    simpa [MsqValVA] using ⟨hT, hv4⟩
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 hz hld1 hld2 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx1, MsqValLA] using hld1.1
    simp only [MsqValVA, MsqNodeA] at hv3
    rcases hv3 with h0 | h0 | h0 | h0 <;> simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, h0] <;>
      exact fun old _ => msqValA_cas (.inr hT) old
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 hz old σ3 hnz hld1 hld2 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx1], by simpa using hx12, by simpa using hx13, ?_⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp (config := { decide := true }) [hT]
    · subst hg
      have h1 := hld1.2; have h2 := hld2.2; have h3 := hcas.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2 h3
      omega
  case vc14 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx1]
    exact fun old _ => msqValA_cas (.inr hT) old
  case vc3 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx1]
    exact fun old _ => msqValA_cas hT.2 old
  case vc4 =>
    rename_i s σ0 old σ1 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx1], by simpa using hx12, by simpa using hx13, ?_⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp (config := { decide := true }) [hT.1]
    · subst hg
      have h3 := hcas.2
      simp only [SharedEnv.tick_rmw] at h3
      omega
  case vc7 =>
    rename_i s σ0 v3 σ1 v4 σ2 hnz hld1 hld2 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx1, MsqValLA] using hld1.1
    have hv4 : MsqValVA d n1 n2 v4 := by
      have h2 := hld2.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h2
      exact h2 (msqValLA_link hv3)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx1], by simpa using hx12, by simpa using hx13, ?_⟩, .inl (by decide)⟩
    simpa [MsqValVA] using ⟨hT, hv4⟩
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 hz hld1 hld2 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx1, MsqValLA] using hld1.1
    simp only [MsqValVA, MsqNodeA] at hv3
    rcases hv3 with h0 | h0 | h0 | h0 <;> simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, h0] <;>
      exact fun old _ => msqValA_cas (.inr hT) old
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 hz old σ3 hnz hld1 hld2 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx1], by simpa using hx12, by simpa using hx13, ?_⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp (config := { decide := true }) [hT]
    · subst hg
      have h1 := hld1.2; have h2 := hld2.2; have h3 := hcas.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2 h3
      omega
  case vc14 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx1]
    exact fun old _ => msqValA_cas (.inr hT) old
  case vc3 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx1]
    exact fun old _ => msqValA_cas hT.2 old
  case vc4 =>
    rename_i s σ0 old σ1 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx1], by simpa using hx12, by simpa using hx13, ?_⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp (config := { decide := true }) [hT.1]
    · subst hg
      have h3 := hcas.2
      simp only [SharedEnv.tick_rmw] at h3
      omega
  all_goals done

end Enq2At

section Deq2At

variable [CodeEnv]

/-- The two-round dequeuer's value table: `x0 = h`, `x1 = t`, `dmem` maps no 8- or 4-byte
word; `x5` a `V` value at the `_ne` labels. -/
abbrev deq2ValTable (h t d n1 n2 : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (msqEnvA h t d n1 n2)).State → Prop :=
  fun lb s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    s.regs.X0.toBitVec = h ∧ s.regs.X1.toBitVec = t ∧
    (lb = "deq1a" ∨ lb = "deq1b" ∨ lb = "ddone1" ∨
      ((lb = "deq1a_ne" ∨ lb = "deq1b_ne") ∧ (s.regs.X5.toBitVec = 0 ∨ MsqNodeA d n1 n2 s.regs.X5.toBitVec)))

/-- **The two-round dequeuer in the value environment**, in any ambient code in which
`deq2Prog` is `PlacedIn`, from `deq1a` to the end address `endA` of its last
block. -/
theorem deq2_val_at (h t d n1 n2 : BitVec 64) (hpl : Program.PlacedIn deq2Prog) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt deq2Prog l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (deq2ValTable h t d n1 n2) "deq1a" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (msqEnvA h t d n1 n2)))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "deq1a"), g) := by
  refine cfgEnv_partial_rank_at (env := SharedEnv.counted (msqEnvA h t d n1 n2)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (deq2ValTable h t d n1 n2) deqRank2 ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env_rank [deq2Prog]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd8, hd4, hx0, hx1, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, MsqValLA, MsqValVA, MsqNodeA]; done)
  -- jumps down the rank
  all_goals try (refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0],
    by simp [hx1], ?_⟩, .inl (by decide)⟩; simp (config := { decide := true }); done)
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hld1 hld2 hld3 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx0, MsqValLA] using hld1.1
    have hv5 : MsqValVA d n1 n2 v5 := by
      have h3 := hld3.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h3
      exact h3 (msqValLA_link hv3)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], ?_⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    · simpa [MsqValVA] using hv5
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3
    omega
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hz hld1 hld2 hld3 _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], by simp⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3
    omega
  case vc14 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hnz hld1 hld2 hld3 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx0, MsqValLA] using hld1.1
    have hv5 : MsqValVA d n1 n2 v5 := by
      have h3 := hld3.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h3
      exact h3 (msqValLA_link hv3)
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx1]
    exact fun old _ => msqValA_cas hv5 old
  case vc15 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hnz old σ4 hld1 hld2 hld3 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], by simp⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2; have h4 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2 h3 h4
    omega
  case vc6 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx0]
    exact fun old _ => msqValA_cas hT old
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hld1 hld2 hld3 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx0, MsqValLA] using hld1.1
    have hv5 : MsqValVA d n1 n2 v5 := by
      have h3 := hld3.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h3
      exact h3 (msqValLA_link hv3)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], ?_⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    · simpa [MsqValVA] using hv5
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3
    omega
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hz hld1 hld2 hld3 _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], by simp⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3
    omega
  case vc14 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hnz hld1 hld2 hld3 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx0, MsqValLA] using hld1.1
    have hv5 : MsqValVA d n1 n2 v5 := by
      have h3 := hld3.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h3
      exact h3 (msqValLA_link hv3)
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx1]
    exact fun old _ => msqValA_cas hv5 old
  case vc15 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hnz old σ4 hld1 hld2 hld3 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], by simp⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2; have h4 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2 h3 h4
    omega
  case vc6 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx0]
    exact fun old _ => msqValA_cas hT old
  -- `deq1a_ne` falls through to `deq1b`
  all_goals simp (config := { decide := true }) [hd8, hd4, hx0, hx1]

end Deq2At

section DeqBAt

variable [CodeEnv]

/-- The second dequeuer's value table: `x0 = h`, `x1 = t`, `dmem` maps no 8- or 4-byte
word; `x5` a `V` value at the `_ne` labels. -/
abbrev deqBValTable (h t d n1 n2 : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (msqEnvA h t d n1 n2)).State → Prop :=
  fun lb s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    s.regs.X0.toBitVec = h ∧ s.regs.X1.toBitVec = t ∧
    (lb = "deq2a" ∨ lb = "ddone2" ∨
      ((lb = "deq2a_ne") ∧ (s.regs.X5.toBitVec = 0 ∨ MsqNodeA d n1 n2 s.regs.X5.toBitVec)))

/-- **The second dequeuer in the value environment**, in any ambient code in which
`deqBProg` is `PlacedIn`, from `deq2a` to the end address `endA` of its last
block. -/
theorem deqB_val_at (h t d n1 n2 : BitVec 64) (hpl : Program.PlacedIn deqBProg) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt deqBProg l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (deqBValTable h t d n1 n2) "deq2a" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (msqEnvA h t d n1 n2)))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "deq2a"), g) := by
  refine cfgEnv_partial_rank_at (env := SharedEnv.counted (msqEnvA h t d n1 n2)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (deqBValTable h t d n1 n2) (deqRank3 "deq2a_ne") ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env_rank [deqBProg]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd8, hd4, hx0, hx1, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, MsqValLA, MsqValVA, MsqNodeA]; done)
  -- jumps down the rank
  all_goals try (refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0],
    by simp [hx1], ?_⟩, .inl (by decide)⟩; simp (config := { decide := true }); done)
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hld1 hld2 hld3 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx0, MsqValLA] using hld1.1
    have hv5 : MsqValVA d n1 n2 v5 := by
      have h3 := hld3.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h3
      exact h3 (msqValLA_link hv3)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], ?_⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    · simpa [MsqValVA] using hv5
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3
    omega
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hz hld1 hld2 hld3 _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], by simp⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3
    omega
  case vc14 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hnz hld1 hld2 hld3 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx0, MsqValLA] using hld1.1
    have hv5 : MsqValVA d n1 n2 v5 := by
      have h3 := hld3.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h3
      exact h3 (msqValLA_link hv3)
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx1]
    exact fun old _ => msqValA_cas hv5 old
  case vc15 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hnz old σ4 hld1 hld2 hld3 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], by simp⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2; have h4 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2 h3 h4
    omega
  case vc6 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx0]
    exact fun old _ => msqValA_cas hT old
  all_goals done

end DeqBAt

/-! ## `msqueue2.kl` -/

open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

section Msq2

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq2Image)]

/-- The enqueuer (thread `0`, to `pdone`) and the dequeuer (to `ddone1`). -/
def msq2ValSpecA (h t d n1 n2 : BitVec 64) : Nat → ValSpecA (msqGA h t d n1 n2)
  | 0 => ValSpecA.ofImageA _ (msqSA h t d n1 n2) (layout msq2Image) (labQ2 "pdone") msq2Image_noPairs
      msq2Image_rmwLive msq2Image_noFault (phase1TreeF_of_dirs (dirsPhase1F_layout msq2Image_dirs))
  | _ + 1 => ValSpecA.ofImageA _ (msqSA h t d n1 n2) (layout msq2Image) (labQ2 "ddone1") msq2Image_noPairs
      msq2Image_rmwLive msq2Image_noFault (phase1TreeF_of_dirs (dirsPhase1F_layout msq2Image_dirs))

/-- The enqueuer's start state holds its specification. -/
theorem msq2_enq_holdsD {h t d n1 n2 : BitVec 64} {ds : Decls} {s : isa.State}
    (hS : WithDeclsD ds (StartEQ2 t n1 n2) s) : (msq2ValSpecA h t d n1 n2 0).HoldsD ds s := by
  obtain ⟨hds, hS⟩ := hS
  refine holdsD_ofImageA (hph := phase1TreeF_of_dirs (dirsPhase1F_layout msq2Image_dirs)) hS.exe hds hS.endPc ?_
  rw [show s.st = (s.st.1, labQ2 "enq1") from Prod.ext rfl (hS.pc.trans labQ2_enq)]
  letI : CodeEnv := ⟨layout msq2Image⟩
  exact enq2_val_at h t d n1 n2 (Program.PlacedIn.of_placedE msq2Image_placed (by decide))
    (Program.last_of_check (lx := "pdone") (by decide)) _ ((), 0)
    ⟨hS.d8, hS.d4, hS.x1, .inr (.inl hS.x12), .inr (.inr hS.x13), .inl rfl⟩

/-- The dequeuer's start state holds its specification. -/
theorem msq2_deq_holdsD {h t d n1 n2 : BitVec 64} {ds : Decls} {s : isa.State}
    (hS : WithDeclsD ds (StartDQ2 h t) s) : (msq2ValSpecA h t d n1 n2 1).HoldsD ds s := by
  obtain ⟨hds, hS⟩ := hS
  refine holdsD_ofImageA (hph := phase1TreeF_of_dirs (dirsPhase1F_layout msq2Image_dirs)) hS.exe hds hS.endPc ?_
  rw [show s.st = (s.st.1, labQ2 "deq1a") from Prod.ext rfl (hS.pc.trans labQ2_deq1)]
  letI : CodeEnv := ⟨layout msq2Image⟩
  exact deq2_val_at h t d n1 n2 (Program.PlacedIn.of_placedE msq2Image_placed (by decide))
    (Program.last_of_check (lx := "ddone1") (by decide)) _ ((), 0) ⟨hS.d8, hS.d4, hS.x0, hS.x1, .inl rfl⟩

end Msq2

/-- **No reachable configuration of the verbatim `msqueue2.kl` threads with
the runner's declarations has a faulting step** (one layout `l` for both),
for strict sized `ds` agreeing on `msqSA h t d n1 n2`, and an initial memory
with a `V` value at every `L` word. -/
theorem msqueue2_envG_runner_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l msq2Image)] {ds : Decls} (hsz : ds.StrictSized) (h t d n1 n2 : BitVec 64)
    (hag : ds.AgreesOnA (msqSA h t d n1 n2)) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartEQ2 (layout := l) t n1 n2) s0) (h1 : WithDeclsD ds (StartDQ2 (layout := l) h t) s1)
    (hi : ∀ lc, MsqValLA h t d n1 n2 lc → MsqValVA d n1 n2 ((Config.init [s0, s1] initMem).mem.initVal lc)) :
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  a64_faultFree_of_valSpecs (fun _ _ => Iff.rfl) (msq2ValSpecA (layout := l) h t d n1 n2) (fun _ => ds)
    (fun _ => hsz) (fun | 0 => hag | _ + 1 => hag) (memValsA_msq_init hi)
    (init_threads_of2 (msq2_enq_holdsD h0) (msq2_deq_holdsD h1))

set_option maxRecDepth 8192 in
/-- **`msqueue2.kl` never faults**, from the runner's exact configuration
(`[enqDQ2, deqDQ2]` with the runner's declarations, initial memory
`msq2InitMemD`), under any architecture. -/
theorem msqueue2_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [enqDQ2, deqDQ2] msq2InitMemD) :=
  msqueue2_envG_runner_faultFree wLayoutQ2 msq2DeclsD_sized 0x1000 0x1200 0x1100 0x1300 0x1400
    (by decls_agrees_on_a) (withDeclsD_of rfl enqWQ2_start) (withDeclsD_of rfl deqWQ2_start)
    (fun lc hl => by
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Config.init, MsqValVA, MsqNodeA] <;> decide)

/-! ## `msqueue3.kl` -/

section Msq3

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq3Image)]

/-- The image's specification at `msqueue3`'s layout, ending at `endPc`. -/
abbrev msq3SpecA (h t d n1 n2 : BitVec 64) (endPc : Int64) : ValSpecA (msqGA h t d n1 n2) :=
  ValSpecA.ofImageA _ (msqSA h t d n1 n2) (layout msq3Image) endPc msq3Image_noPairs msq3Image_rmwLive
    msq3Image_noFault (phase1TreeF_of_dirs (dirsPhase1F_layout msq3Image_dirs))

/-- The enqueuer (thread `0`, to `pdone`), the first dequeuer (thread `1`,
to `ddone1`) and the second (to `ddone2`). -/
def msq3ValSpecA (h t d n1 n2 : BitVec 64) : Nat → ValSpecA (msqGA h t d n1 n2)
  | 0 => msq3SpecA h t d n1 n2 (labQ3 "pdone")
  | 1 => msq3SpecA h t d n1 n2 (labQ3 "ddone1")
  | _ + 2 => msq3SpecA h t d n1 n2 (labQ3 "ddone2")

/-- The enqueuer's start state holds its specification. -/
theorem msq3_enq_holdsD {h t d n1 n2 : BitVec 64} {ds : Decls} {s : isa.State}
    (hS : WithDeclsD ds (StartEQ3 t n1 n2) s) : (msq3ValSpecA h t d n1 n2 0).HoldsD ds s := by
  obtain ⟨hds, hS⟩ := hS
  refine holdsD_ofImageA (hph := phase1TreeF_of_dirs (dirsPhase1F_layout msq3Image_dirs)) hS.exe hds hS.endPc ?_
  rw [show s.st = (s.st.1, labQ3 "enq1") from Prod.ext rfl (hS.pc.trans labQ3_enq)]
  letI : CodeEnv := ⟨layout msq3Image⟩
  exact enq2_val_at h t d n1 n2 (Program.PlacedIn.of_placedE msq3Image_placed (by decide))
    (Program.last_of_check (lx := "pdone") (by decide)) _ ((), 0)
    ⟨hS.d8, hS.d4, hS.x1, .inr (.inl hS.x12), .inr (.inr hS.x13), .inl rfl⟩

/-- The first dequeuer's start state holds its specification. -/
theorem msq3_deqA_holdsD {h t d n1 n2 : BitVec 64} {ds : Decls} {s : isa.State}
    (hS : WithDeclsD ds (StartDQ3 "deq1" "ddone1" h t) s) : (msq3ValSpecA h t d n1 n2 1).HoldsD ds s := by
  obtain ⟨hds, hS⟩ := hS
  refine holdsD_ofImageA (hph := phase1TreeF_of_dirs (dirsPhase1F_layout msq3Image_dirs)) hS.exe hds hS.endPc ?_
  rw [show s.st = (s.st.1, labQ3 "deq1a") from Prod.ext rfl (hS.pc.trans labQ3_deq1)]
  letI : CodeEnv := ⟨layout msq3Image⟩
  exact deq_val_at h t d n1 n2 (Program.PlacedIn.of_placedE msq3Image_placed (by decide))
    (Program.last_of_check (lx := "ddone1") (by decide)) _ ((), 0) ⟨hS.d8, hS.d4, hS.x0, hS.x1, .inl rfl⟩

/-- The second dequeuer's start state holds its specification. -/
theorem msq3_deqB_holdsD {h t d n1 n2 : BitVec 64} {ds : Decls} {s : isa.State}
    (hS : WithDeclsD ds (StartDQ3 "deq2" "ddone2" h t) s) : (msq3ValSpecA h t d n1 n2 2).HoldsD ds s := by
  obtain ⟨hds, hS⟩ := hS
  refine holdsD_ofImageA (hph := phase1TreeF_of_dirs (dirsPhase1F_layout msq3Image_dirs)) hS.exe hds hS.endPc ?_
  rw [show s.st = (s.st.1, labQ3 "deq2a") from Prod.ext rfl (hS.pc.trans labQ3_deq2)]
  letI : CodeEnv := ⟨layout msq3Image⟩
  exact deqB_val_at h t d n1 n2 (Program.PlacedIn.of_placedE msq3Image_placed (by decide))
    (Program.last_of_check (lx := "ddone2") (by decide)) _ ((), 0) ⟨hS.d8, hS.d4, hS.x0, hS.x1, .inl rfl⟩

end Msq3

/-- **No reachable configuration of the verbatim `msqueue3.kl` threads with
the runner's declarations has a faulting step** (one layout `l` for all
three), for strict sized `ds` agreeing on `msqSA h t d n1 n2`, and an
initial memory with a `V` value at every `L` word. -/
theorem msqueue3_envG_runner_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l msq3Image)] {ds : Decls} (hsz : ds.StrictSized) (h t d n1 n2 : BitVec 64)
    (hag : ds.AgreesOnA (msqSA h t d n1 n2)) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartEQ3 (layout := l) t n1 n2) s0)
    (h1 : WithDeclsD ds (StartDQ3 (layout := l) "deq1" "ddone1" h t) s1)
    (h2 : WithDeclsD ds (StartDQ3 (layout := l) "deq2" "ddone2" h t) s2)
    (hi : ∀ lc, MsqValLA h t d n1 n2 lc → MsqValVA d n1 n2 ((Config.init [s0, s1, s2] initMem).mem.initVal lc)) :
    Config.FaultFree A fuel (Config.init [s0, s1, s2] initMem) :=
  a64_faultFree_of_valSpecs (fun _ _ => Iff.rfl) (msq3ValSpecA (layout := l) h t d n1 n2) (fun _ => ds)
    (fun _ => hsz) (fun | 0 => hag | 1 => hag | _ + 2 => hag) (memValsA_msq_init hi)
    (init_threads_of3 (msq3_enq_holdsD h0) (msq3_deqA_holdsD h1) (msq3_deqB_holdsD h2))

set_option maxRecDepth 8192 in
/-- **`msqueue3.kl` never faults**, from the runner's exact configuration
(`[enqDQ3, deqADQ3, deqBDQ3]` with the runner's declarations, initial memory
`msq3InitMemD`), under any architecture. -/
theorem msqueue3_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [enqDQ3, deqADQ3, deqBDQ3] msq3InitMemD) :=
  msqueue3_envG_runner_faultFree wLayoutQ3 msq3DeclsD_sized 0x1000 0x1200 0x1100 0x1300 0x1400
    (by decls_agrees_on_a) (withDeclsD_of rfl enqWQ3_start) (withDeclsD_of rfl deqAWQ3_start)
    (withDeclsD_of rfl deqBWQ3_start)
    (fun lc hl => by
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Config.init, MsqValVA, MsqNodeA] <;> decide)

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue2_envG_runner_faultFree
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue2_envG_runner_faultFree_concrete
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue3_envG_runner_faultFree
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue3_envG_runner_faultFree_concrete
