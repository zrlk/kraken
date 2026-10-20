/-
Part 5: **the two dequeuers of `msqueue3.kl` on
`EnvGCAdj` by `vcgen`**: `deqA3_envGCAdj` (`deqProg`, thread `1`) and
`deqB3_envGCAdj` (`deqBProg`, thread `2`), partial triples in the counted
environments with the tid-generic VCs of `EnvG/MsQueue3VC.lean`
(`cfgEnv_partial_rank`: `deqNa_ne`'s `cbz x5, deqNa` jumps back in zero
steps). One proof script (`deq3_script`) serves both programs; the table
`deqTable3` takes the thread id and the three labels. The enqueuer is
msqueue2's `enq2_envGCAdj`, unchanged.

The whole-image AArch64 proofs (name-preserving): each run is stated once as `…_at`, over any
ambient code (`[CodeEnv]`) in which the text is `Program.PlacedIn`, from its
entry label to the end address of its last block; the per-thread theorem is
`PartialTripleEnv.of_runAtT` of it (`EnvG/A64MaskRunAt.lean`), and the
whole-image theorems (`EnvG/A64WholeMsQueue*.lean`) run it in the image or a
mask of it.
-/
import Kraken.Promising.SLR.EnvG.MsQueue3VC
import Kraken.Promising.SLR.EnvG.MsQueue3Smoke
import Kraken.Promising.SLR.EnvG.MsQueue2VCGen

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken.Promising.SLR.EnvG.Treiber (casOp64)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- Dequeuer `k`'s table, at its labels `la` (the loop), `lne` (the
non-empty branch) and `ld` (the end): `x0 = head`, `x1 = tail`, `dmem` maps
no 8- or 4-byte word. -/
abbrev deqTable3 (P : Params2) (k : Nat) (la lne ld : Label) :
    Label → MachineData → (SharedEnv.counted (ED3 P k)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    ((lb = la ∧ ComD3 P k σ.1) ∨
      (lb = lne ∧ ∃ y3 y5 : Val, s.regs.X3.toBitVec = BitVec.setWidth 64 y3 ∧
        s.regs.X5.toBitVec = BitVec.setWidth 64 y5 ∧ DQ3' P k y3 y5 σ.1) ∨
      (lb = ld ∧ Dn3 P k s.regs.X10.toBitVec σ.1))

/-- The label rank: the non-empty branch `lne` above the others. -/
def deqRank3 (lne : Label) (l : Label) : Nat := if l = lne then 1 else 0

set_option hygiene false in
/-- Jump to the table entry of the target label with its facts `t`; leaves
the edge condition. -/
local macro "dland3" t:term : tactic => `(tactic| (
  refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4], ?_⟩, ?_⟩
  · (simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true])
    exact $t))

set_option hygiene false in
/-- The three reads of an iteration (`h3`: `DQ3'` after them). -/
local macro "d3_reads" : tactic => `(tactic| (
  have h1 := vc_d3_ldar_head (xcl := false) _ hT v3 σ1.1 (by simpa [hx0, Params.head] using hld1.1)
  have h2 := (vc_d3_load _ h1 v4 σ2.1 hld2.1).fence hf1.1
  have h3 := ((vc_d3_ldar_link _ h2 v5 σ4.1 (by simpa using hld3.1)).fence hf2.1).fence hf3.1))

set_option hygiene false in
/-- The edge back to the iteration's head (the variant decreased). -/
local macro "d3_back" : tactic => `(tactic| (
  refine .inr (.inr fun ⟨_, hg⟩ => ?_)
  subst hg
  simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *
  omega))

set_option hygiene false in
/-- **The dequeuer's proof script**, after `cfg_cases_env_rank`. -/
local macro "deq3_script" : tactic => `(tactic| (
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hd8]; done)
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hld1 hld2 hf1 hld3 hf2 hf3 _
    d3_reads
    dland3 ⟨v3, v5, by simp, by simp, h3⟩
    have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    d3_back
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hz σ7 hld1 hld2 hf1 hld3 hf2 hf3 hf4 _
    d3_reads
    dland3 (h3.fence hf4.1).1
    have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    have e7 := hf4.2
    d3_back
  case vc14 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hnz σ7 σ8 hld1 hld2 hf1 hld3 hf2 hf3 hf4 hf5 _
    d3_reads
    simp at hnz
    have h := (vc_d3_help hL _ ((h3.fence hf4.1).fence hf5.1) hnz).1
    simp [hx1]
    simpa [casOp64, Params.tail] using h
  case vc15 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hnz σ7 σ8 old σ9 σ10 hld1 hld2 hf1 hld3 hf2 hf3 hf4 hf5 hcas hf6 _
    d3_reads
    simp at hnz
    have hc := (vc_d3_help hL _ ((h3.fence hf4.1).fence hf5.1) hnz).2 old σ9.1
      (by simpa [hx1, casOp64, Params.tail] using hcas.1)
    dland3 hc.fence hf6.1
    have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    have e7 := hf4.2; have e8 := hf5.2; have e9 := hcas.2; have e10 := hf6.2
    d3_back
  case vc1 =>
    rename_i s σ0 hz σ1 hf _
    obtain ⟨y3, y5, -, -, hD3⟩ := hT
    dland3 (hD3.fence hf.1).1
    exact .inl (by decide)
  case vc6 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 hf1 hld hf2 _
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d3_ldr _ (hD3.fence hf1.1) hnz' u σ2.1 hu.1).fence hf2.1
    have h := (vc_d3_cas hL _ hD4).1
    simp [hx0, hy3, hy5]
    simpa [casOp64, Params.head] using h
  case vc7 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 old σ4 σ5 hne σ6 hf1 hld hf2 hcas hf3 hf4 _
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d3_ldr _ (hD3.fence hf1.1) hnz' u σ2.1 hu.1).fence hf2.1
    have hc := (vc_d3_cas hL _ hD4).2 old σ4.1 (by simpa [hx0, hy3, hy5, casOp64, Params.head] using hcas.1)
    dland3 (hc.1.fence hf3.1).fence hf4.1
    exact .inl (by decide)
  case vc8 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 old σ4 σ5 heq σ6 σ7 σ8 hf1 hld hf2 hcas hf3 hf4 hf5 hf6 _
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d3_ldr _ (hD3.fence hf1.1) hnz' u σ2.1 hu.1).fence hf2.1
    have hc := (vc_d3_cas hL _ hD4).2 old σ4.1 (by simpa [hx0, hy3, hy5, casOp64, Params.head] using hcas.1)
    simp [hy3] at heq
    have hD := hc.2 (TreiberCommon.bv64_eq_of_sub_eq_zero heq)
    have hDn : Dn3 P _ (BitVec.setWidth 64 (BitVec.setWidth 32 u)) σ8.1 :=
      Dn3.fence (Dn3.fence (Dn3.fence (Dn3.fence ⟨hc.1, hD⟩ hf3.1) hf4.1) hf5.1) hf6.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4], ?_⟩,
      .inl (by decide)⟩
    simp (config := { decide := true })
    exact hDn
  case vc1 => exact hT
  all_goals done))

section DeqAAt

variable [CodeEnv]

/-- **`deqA3_envGCAdj` in any ambient code** in which `deqProg` is `PlacedIn`, from `deq1a` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem deqA3_envGCAdj_at (P : Params2) (hL : QLocs2 P)
    (hpl : Program.PlacedIn deqProg) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt deqProg l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (deqTable3 P 1 "deq1a" "deq1a_ne" "ddone1") "deq1a" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (ED3 P 1)))
      (fun x => (x.1.2 = endA ∧ Dn3 P 1 x.1.1.regs.X10.toBitVec x.2.1) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "deq1a"), g) := by
  refine cfgEnv_partial_rank_at (env := SharedEnv.counted (ED3 P 1))
    (Q := fun s σ => Dn3 P 1 s.regs.X10.toBitVec σ.1)
    (E := fun _ _ _ => False) (deqTable3 P 1 "deq1a" "deq1a_ne" "ddone1") (deqRank3 "deq1a_ne") ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env_rank [deqProg]
  deq3_script

end DeqAAt

section DeqA

variable [layout : _root_.Layout] [Executable.ValidLayout (layout deqProg)]

local instance deqProg.envG3 : CodeEnv := ⟨layout deqProg⟩

/-- **The first dequeuer** (`deqProg`, thread `1`). -/
theorem deqA3_envGCAdj (P : Params2) (hL : QLocs2 P) :
    PartialTripleEnv (SharedEnv.counted (ED3 P 1))
      (fun s σ => s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ ComD3 P 1 σ.1)
      deqProg (fun s σ => Dn3 P 1 s.regs.X10.toBitVec σ.1) (fun _ _ _ => False) :=
  have hpl : Program.Placed deqProg "deq1a" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [deqTable3]) fun _ hlast =>
    deqA3_envGCAdj_at P hL hpl.toPlacedIn hlast

end DeqA

section DeqBAt

variable [CodeEnv]

/-- **`deqB3_envGCAdj` in any ambient code** in which `deqBProg` is `PlacedIn`, from `deq2a` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem deqB3_envGCAdj_at (P : Params2) (hL : QLocs2 P)
    (hpl : Program.PlacedIn deqBProg) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt deqBProg l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (deqTable3 P 2 "deq2a" "deq2a_ne" "ddone2") "deq2a" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (ED3 P 2)))
      (fun x => (x.1.2 = endA ∧ Dn3 P 2 x.1.1.regs.X10.toBitVec x.2.1) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "deq2a"), g) := by
  refine cfgEnv_partial_rank_at (env := SharedEnv.counted (ED3 P 2))
    (Q := fun s σ => Dn3 P 2 s.regs.X10.toBitVec σ.1)
    (E := fun _ _ _ => False) (deqTable3 P 2 "deq2a" "deq2a_ne" "ddone2") (deqRank3 "deq2a_ne") ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env_rank [deqBProg]
  deq3_script

end DeqBAt

section DeqB

variable [layout : _root_.Layout] [Executable.ValidLayout (layout deqBProg)]

local instance deqBProg.envG3 : CodeEnv := ⟨layout deqBProg⟩

/-- **The second dequeuer** (`deqBProg`, thread `2`). -/
theorem deqB3_envGCAdj (P : Params2) (hL : QLocs2 P) :
    PartialTripleEnv (SharedEnv.counted (ED3 P 2))
      (fun s σ => s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ ComD3 P 2 σ.1)
      deqBProg (fun s σ => Dn3 P 2 s.regs.X10.toBitVec σ.1) (fun _ _ _ => False) :=
  have hpl : Program.Placed deqBProg "deq2a" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [deqTable3]) fun _ hlast =>
    deqB3_envGCAdj_at P hL hpl.toPlacedIn hlast

end DeqB

end Kraken.Promising.SLR.EnvG.MsQueue
