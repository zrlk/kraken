/-
Part 6: **the two threads of `msqueue1.kl` on
`EnvGCAdj` by `vcgen`**: `enq_envGCAdj` (`cfgEnv_partial`) and
`deq_envGCAdj` (`cfgEnv_partial_rank`, `EnvG/MsQueueCfg.lean`), partial
triples in the counted environments with the VCs of `EnvG/MsQueueVC.lean`.

The whole-image AArch64 proofs (name-preserving): each run is stated once as `…_at`, over any
ambient code (`[CodeEnv]`) in which the text is `Program.PlacedIn`, from its
entry label to the end address of its last block; the per-thread theorem is
`PartialTripleEnv.of_runAtT` of it (`EnvG/A64MaskRunAt.lean`), and the
whole-image theorems (`EnvG/A64WholeMsQueue*.lean`) run it in the image or a
mask of it.
-/
import Kraken.Promising.SLR.EnvG.MsQueueVC
import Kraken.Promising.SLR.EnvG.MsQueueSmoke
import Kraken.Promising.SLR.EnvG.MsQueueCfg
import Kraken.Promising.SLR.EnvG.A64MaskRunAt
import Kraken.Promising.SLR.EnvG.A64VCGen
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken.Promising.SLR.EnvG.Treiber (casOp64)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The enqueuer's table: `x1 = tail`, `dmem` maps no 8- or 4-byte word;
`x12 = n1` at `enq1`, `x2 = n1` in the loop. -/
abbrev enqTable (P : Params) : Label → MachineData → (SharedEnv.counted (EE P)).State → Prop :=
  fun lb s σ => s.regs.X1.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    ((lb = "enq1" ∧ s.regs.X12.toBitVec = P.n1 ∧ E0 P σ.1) ∨
      (lb = "enq1_loop" ∧ s.regs.X2.toBitVec = P.n1 ∧ EL P σ.1) ∨
      (lb = "enq1_fix" ∧ s.regs.X2.toBitVec = P.n1 ∧ ∃ y3 y4 : Val, s.regs.X3.toBitVec = BitVec.setWidth 64 y3 ∧
        s.regs.X4.toBitVec = BitVec.setWidth 64 y4 ∧ BitVec.setWidth 64 y4 ≠ 0 ∧ EL2 P y3 y4 σ.1) ∨
      (lb = "enq1_end" ∧ ComE P σ.1) ∨ (lb = "pdone" ∧ ComE P σ.1))

section EnqAt

variable [CodeEnv]

/-- **The enqueuer's run, in any ambient code** in which `enqProg` is
`PlacedIn`, from `enq1` to the end address `endA` of its last block (the
script of `enq_envGCAdj`, `EnvG/A64MaskRunAt.lean`). -/
theorem enq_envGCAdj_at (P : Params) (hL : QLocs P) (hpl : Program.PlacedIn enqProg) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt enqProg l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, enqTable P "enq1" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (EE P)))
      (fun x => (x.1.2 = endA ∧ ComE P x.2.1) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "enq1"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EE P)) (Q := fun _ σ => ComE P σ.1) (E := fun _ _ _ => False) (enqTable P) ?_
    (by rfl) (by decide) hpl hlast
  cfg_cases_env [enqProg]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx1, hd8, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx1, hd8]; done)
  case vc2 =>
    rename_i s σ0 σ1 σ2 rng hnone hf1 hf2 _
    have hE := (hT.2.fence hf1.1).fence hf2.1
    simp [hT.1]
    refine (vc_e_str _ hE _ ?_).1
    simp [D]
  case vc3 =>
    rename_i s σ0 σ1 σ2 rng dm σ3 hf1 hf2 hst _
    have hE := (hT.2.fence hf1.1).fence hf2.1
    simp [hT.1, hd4] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hEL : EL P σ3.1 := by
      rcases hso with h | h <;>
        (refine (vc_e_str _ hE _ ?_).2 _ σ3.1 (by simpa [Params.dat] using h); simp [D])
    simp (config := { decide := true }) [hx1, hd8, hd4, hT.1]
    exact hEL
  case vc7 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hnz σ4 hld1 hf1 hld2 hf2 _
    have h1 := (vc_e_ldar_tail (xcl := false) _ hT.2 v3 σ1.1 (by simpa [hx1, Params.tail] using hld1.1)).fence hf1.1
    have h2 := (vc_e_ldar_link _ h1 v4 σ3.1 (by simpa using hld2.1)).fence hf2.1
    simp at hnz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inr (.inl ⟨rfl, by simp [hT.1], v3, v4, by simp, by simp, hnz, h2⟩))⟩, .inl (by decide)⟩
  case vc10 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 hld1 hf1 hld2 hf2 hf3 _
    have h1 := (vc_e_ldar_tail (xcl := false) _ hT.2 v3 σ1.1 (by simpa [hx1, Params.tail] using hld1.1)).fence hf1.1
    have h2 := ((vc_e_ldar_link _ h1 v4 σ3.1 (by simpa using hld2.1)).fence hf2.1).fence hf3.1
    have h := (vc_e_link hL _ h2).1
    simp [hT.1]
    simpa [casOp64] using h
  case vc11 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hnz5 σ7 hld1 hf1 hld2 hf2 hf3 hcas hf4 _
    have h1 := (vc_e_ldar_tail (xcl := false) _ hT.2 v3 σ1.1 (by simpa [hx1, Params.tail] using hld1.1)).fence hf1.1
    have h2 := ((vc_e_ldar_link _ h1 v4 σ3.1 (by simpa using hld2.1)).fence hf2.1).fence hf3.1
    have hc := (vc_e_link hL _ h2).2 old σ6.1 (by simpa [hT.1, casOp64] using hcas.1)
    simp at hnz5
    rcases hc with ⟨-, hEL⟩ | ⟨h0, -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx1], by simp [hd8], by simp [hd4],
        .inr (.inl ⟨rfl, by simp [hT.1], hEL.fence hf4.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have e1 := hld1.2; have e2 := hld2.2; have e3 := hcas.2; have e4 := hf1.2; have e5 := hf2.2
      have e6 := hf3.2; have e7 := hf4.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at e1 e2 e3
      omega
    · exact absurd (by simpa using h0) hnz5
  case vc14 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hz5 σ7 σ8 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5 _
    have h1 := (vc_e_ldar_tail (xcl := false) _ hT.2 v3 σ1.1 (by simpa [hx1, Params.tail] using hld1.1)).fence hf1.1
    have h2 := ((vc_e_ldar_link _ h1 v4 σ3.1 (by simpa using hld2.1)).fence hf2.1).fence hf3.1
    have hc := (vc_e_link hL _ h2).2 old σ6.1 (by simpa [hT.1, casOp64] using hcas.1)
    simp at hz5
    rcases hc with ⟨hne, -⟩ | ⟨-, hC⟩
    · exact absurd (by simpa using hz5) hne
    have h := (vc_e_swing hL _ ((hC.fence hf4.1).fence hf5.1) (BitVec.setWidth 64 v3)).1
    simp [hx1, hT.1]
    simpa [casOp64, Params.tail] using h
  case vc15 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hz5 σ7 σ8 old2 σ9 σ10 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5 hcas2 hf6 _
    have h1 := (vc_e_ldar_tail (xcl := false) _ hT.2 v3 σ1.1 (by simpa [hx1, Params.tail] using hld1.1)).fence hf1.1
    have h2 := ((vc_e_ldar_link _ h1 v4 σ3.1 (by simpa using hld2.1)).fence hf2.1).fence hf3.1
    have hc := (vc_e_link hL _ h2).2 old σ6.1 (by simpa [hT.1, casOp64] using hcas.1)
    simp at hz5
    rcases hc with ⟨hne, -⟩ | ⟨-, hC⟩
    · exact absurd (by simpa using hz5) hne
    have hC2 := (vc_e_swing hL _ ((hC.fence hf4.1).fence hf5.1) (BitVec.setWidth 64 v3)).2 old2 σ9.1
      (by simpa [hx1, hT.1, casOp64, Params.tail] using hcas2.1)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inr (.inr (.inl ⟨rfl, hC2.fence hf6.1⟩)))⟩, .inl (by decide)⟩
  case vc3 =>
    rename_i s σ0 σ1 hf1 _
    obtain ⟨hx2, y3, y4, hy3, hy4, hnz, h2⟩ := hT
    have h := (vc_e_fix hL _ (h2.fence hf1.1) hnz).1
    simp [hx1, hy3, hy4]
    simpa [casOp64, Params.tail] using h
  case vc4 =>
    rename_i s σ0 σ1 old σ2 σ3 hf1 hcas hf2 _
    obtain ⟨hx2, y3, y4, hy3, hy4, hnz, h2⟩ := hT
    have hEL := (vc_e_fix hL _ (h2.fence hf1.1) hnz).2 old σ2.1
      (by simpa [hx1, hy3, hy4, casOp64, Params.tail] using hcas.1)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inl ⟨rfl, by simp [hx2], hEL.fence hf2.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have e1 := hcas.2; have e2 := hf1.2; have e3 := hf2.2
    simp only [SharedEnv.tick_rmw] at e1
    omega
  case vc1 =>
    rename_i s σ0 σ1 hf _
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inr (.inr (.inr ⟨rfl, hT.fence hf.1⟩)))⟩, .inl (by decide)⟩
  case vc1 => exact hT
  all_goals done

end EnqAt

section Enq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout enqProg)]

local instance enqProg.envG : CodeEnv := ⟨layout enqProg⟩

theorem enq_envGCAdj (P : Params) (hL : QLocs P) :
    PartialTripleEnv (SharedEnv.counted (EE P))
      (fun s σ => s.regs.X1.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.regs.X12.toBitVec = P.n1 ∧ E0 P σ.1)
      enqProg (fun _ σ => ComE P σ.1) (fun _ _ _ => False) :=
  have hpl : Program.Placed enqProg "enq1" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAt hpl fun _ hlast s g h =>
    enq_envGCAdj_at P hL hpl.toPlacedIn hlast s g ⟨h.1, h.2.1, h.2.2.1, .inl ⟨rfl, h.2.2.2⟩⟩

end Enq

/-- The dequeuer's table: `x0 = head`, `x1 = tail`, `dmem` maps no 8- or
4-byte word. -/
abbrev deqTable (P : Params) : Label → MachineData → (SharedEnv.counted (ED P)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    ((lb = "deq1a" ∧ ComD P σ.1) ∨
      (lb = "deq1a_ne" ∧ ∃ y3 y5 : Val, s.regs.X3.toBitVec = BitVec.setWidth 64 y3 ∧
        s.regs.X5.toBitVec = BitVec.setWidth 64 y5 ∧ D3 P y3 y5 σ.1) ∨
      (lb = "ddone1" ∧ Dn P s.regs.X10.toBitVec σ.1))

/-- The dequeuer's label rank: `deq1a_ne` above the others (its `cbz x5,
deq1a` may jump back in zero steps). -/
def deqRank (l : Label) : Nat := if l = "deq1a_ne" then 1 else 0

section DeqAt

variable [CodeEnv]

/-- **The dequeuer's run, in any ambient code** in which `deqProg` is
`PlacedIn`, from `deq1a` to the end address `endA` of its last block (the
script of `deq_envGCAdj`). -/
theorem deq_envGCAdj_at (P : Params) (hL : QLocs P) (hpl : Program.PlacedIn deqProg) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt deqProg l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, deqTable P "deq1a" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (ED P)))
      (fun x => (x.1.2 = endA ∧ Dn P x.1.1.regs.X10.toBitVec x.2.1) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "deq1a"), g) := by
  refine cfgEnv_partial_rank_at (env := SharedEnv.counted (ED P)) (Q := fun s σ => Dn P s.regs.X10.toBitVec σ.1)
    (E := fun _ _ _ => False) (deqTable P) deqRank ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env_rank [deqProg]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hd8]; done)
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hld1 hld2 hf1 hld3 hf2 hf3 _
    have h1 := vc_d_ldar_head (xcl := false) _ hT v3 σ1.1 (by simpa [hx0, Params.head] using hld1.1)
    have h2 := (vc_d_load _ h1 v4 σ2.1 hld2.1).fence hf1.1
    have h3 := ((vc_d_ldar_link _ h2 v5 σ4.1 (by simpa using hld3.1)).fence hf2.1).fence hf3.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inl ⟨rfl, v3, v5, by simp, by simp, h3⟩)⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    simp only [SharedEnv.tick_load] at e1 e2 e3
    omega
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hz σ7 hld1 hld2 hf1 hld3 hf2 hf3 hf4 _
    have h1 := vc_d_ldar_head (xcl := false) _ hT v3 σ1.1 (by simpa [hx0, Params.head] using hld1.1)
    have h2 := (vc_d_load _ h1 v4 σ2.1 hld2.1).fence hf1.1
    have h3 := ((vc_d_ldar_link _ h2 v5 σ4.1 (by simpa using hld3.1)).fence hf2.1).fence hf3.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inl ⟨rfl, (h3.fence hf4.1).1⟩⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    have e7 := hf4.2
    simp only [SharedEnv.tick_load] at e1 e2 e3
    omega
  case vc14 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hnz σ7 σ8 hld1 hld2 hf1 hld3 hf2 hf3 hf4 hf5 _
    have h1 := vc_d_ldar_head (xcl := false) _ hT v3 σ1.1 (by simpa [hx0, Params.head] using hld1.1)
    have h2 := (vc_d_load _ h1 v4 σ2.1 hld2.1).fence hf1.1
    have h3 := ((vc_d_ldar_link _ h2 v5 σ4.1 (by simpa using hld3.1)).fence hf2.1).fence hf3.1
    simp at hnz
    have h := (vc_d_help hL _ ((h3.fence hf4.1).fence hf5.1) hnz).1
    simp [hx1]
    simpa [casOp64, Params.tail] using h
  case vc15 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hnz σ7 σ8 old σ9 σ10 hld1 hld2 hf1 hld3 hf2 hf3 hf4 hf5 hcas hf6 _
    have h1 := vc_d_ldar_head (xcl := false) _ hT v3 σ1.1 (by simpa [hx0, Params.head] using hld1.1)
    have h2 := (vc_d_load _ h1 v4 σ2.1 hld2.1).fence hf1.1
    have h3 := ((vc_d_ldar_link _ h2 v5 σ4.1 (by simpa using hld3.1)).fence hf2.1).fence hf3.1
    simp at hnz
    have hc := (vc_d_help hL _ ((h3.fence hf4.1).fence hf5.1) hnz).2 old σ9.1
      (by simpa [hx1, casOp64, Params.tail] using hcas.1)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inl ⟨rfl, hc.fence hf6.1⟩⟩, .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    have e7 := hf4.2; have e8 := hf5.2; have e9 := hcas.2; have e10 := hf6.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at e1 e2 e3 e9
    omega
  case vc1 =>
    rename_i s σ0 hz σ1 hf _
    obtain ⟨y3, y5, -, -, hD3⟩ := hT
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inl ⟨rfl, (hD3.fence hf.1).1⟩⟩, .inl (by decide)⟩
  case vc6 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 hf1 hld hf2 _
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr _ (hD3.fence hf1.1) hnz' u σ2.1 hu.1).fence hf2.1
    have h := (vc_d_cas hL _ hD4).1
    simp [hx0, hy3, hy5]
    simpa [casOp64, Params.head] using h
  case vc7 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 old σ4 σ5 hne σ6 hf1 hld hf2 hcas hf3 hf4 _
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr _ (hD3.fence hf1.1) hnz' u σ2.1 hu.1).fence hf2.1
    have hc := (vc_d_cas hL _ hD4).2 old σ4.1 (by simpa [hx0, hy3, hy5, casOp64, Params.head] using hcas.1)
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inl ⟨rfl, ((hc.fence hf3.1).fence hf4.1).1⟩⟩, .inl (by decide)⟩
  case vc8 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 old σ4 σ5 heq σ6 σ7 σ8 hf1 hld hf2 hcas hf3 hf4 hf5 hf6 _
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr _ (hD3.fence hf1.1) hnz' u σ2.1 hu.1).fence hf2.1
    have hc := (vc_d_cas hL _ hD4).2 old σ4.1 (by simpa [hx0, hy3, hy5, casOp64, Params.head] using hcas.1)
    have hDn := ((((hc.fence hf3.1).fence hf4.1).fence hf5.1).fence hf6.1).dn
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inr ⟨rfl, ?_⟩)⟩, .inl (by decide)⟩
    simp
    exact hDn
  case vc1 => exact hT
  all_goals done

end DeqAt

section Deq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout deqProg)]

local instance deqProg.envG : CodeEnv := ⟨layout deqProg⟩

theorem deq_envGCAdj (P : Params) (hL : QLocs P) :
    PartialTripleEnv (SharedEnv.counted (ED P))
      (fun s σ => s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ ComD P σ.1)
      deqProg (fun s σ => Dn P s.regs.X10.toBitVec σ.1) (fun _ _ _ => False) :=
  have hpl : Program.Placed deqProg "deq1a" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAt hpl fun _ hlast s g h =>
    deq_envGCAdj_at P hL hpl.toPlacedIn hlast s g ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, .inl ⟨rfl, h.2.2.2.2⟩⟩

end Deq

end Kraken.Promising.SLR.EnvG.MsQueue
