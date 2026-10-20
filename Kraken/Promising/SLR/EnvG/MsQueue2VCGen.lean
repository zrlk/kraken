/-
Msqueue2 part 5: **the two threads of `msqueue2.kl`
on `EnvGCAdj` by `vcgen`**: `enq2_envGCAdj` (`cfgEnv_partial`) and
`deq2_envGCAdj` (`cfgEnv_partial_rank`), partial triples in the counted
environments with the VCs of `EnvG/MsQueue2VC.lean`.

The whole-image AArch64 proofs (name-preserving): each run is stated once as `…_at`, over any
ambient code (`[CodeEnv]`) in which the text is `Program.PlacedIn`, from its
entry label to the end address of its last block; the per-thread theorem is
`PartialTripleEnv.of_runAtT` of it (`EnvG/A64MaskRunAt.lean`), and the
whole-image theorems (`EnvG/A64WholeMsQueue*.lean`) run it in the image or a
mask of it.
-/
import Kraken.Promising.SLR.EnvG.MsQueue2VC
import Kraken.Promising.SLR.EnvG.MsQueue2Smoke
import Kraken.Promising.SLR.EnvG.MsQueueVCGen

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken.Promising.SLR.EnvG.Treiber (casOp64)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## Phases and fences -/

section PhFence

variable {P : Params2} {ph : Ph} {σ σ' : State isa}

theorem ph1_ok (hL : QLocs2 P) : PhOk P (ph1 P) := ⟨.inl ⟨rfl, rfl, rfl⟩, xok_fresh2 hL⟩
theorem ph2_ok (P : Params2) : PhOk P (ph2 P) := ⟨.inr ⟨rfl, rfl, rfl, fun _ h => h⟩, xok_link1 P⟩

theorem Start.fence (hph : PhOk P ph) (h : Start P ph σ) (hf : FenceLe σ σ') : Start P ph σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.fence hf, by unfold Fresh; rw [hf.r]; exact h2, hph.2.fence h3 hf⟩

theorem EL'.fence (hph : PhOk P ph) (h : EL' P ph σ) (hf : FenceLe σ σ') : EL' P ph σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.fence hf, by unfold Written; rw [hf.r, hf.vwOld]; exact h2, hph.2.fence h3 hf⟩

theorem EL2'.fence (hph : PhOk P ph) {y3 y4 : Val} (h : EL2' P ph y3 y4 σ) (hf : FenceLe σ σ') :
    EL2' P ph y3 y4 σ' := by
  obtain ⟨h1, a, b, h2, h3, h4⟩ := h
  exact ⟨h1.fence hph hf, a, b, hf.snap ▸ h2, Nat.le_trans h3 hf.vwNew, hf.snap ▸ h4⟩

theorem EL1'.fence (hph : PhOk P ph) {y3 : Val} (h : EL1' P ph y3 σ) (hf : FenceLe σ σ') : EL1' P ph y3 σ' := by
  obtain ⟨h1, a, h2, h3⟩ := h
  exact ⟨h1.fence hph hf, a, hf.snap ▸ h2, Nat.le_trans h3 hf.vwNew⟩

theorem Linked.fence (hph : PhOk P ph) (h : Linked P ph σ) (hf : FenceLe σ σ') : Linked P ph σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.fence hf, hph.2.fence h2 hf, by unfold LinkS; rw [hf.snap]; exact h3⟩

end PhFence

section EnqAt

variable [CodeEnv]

/-- The enqueuer's table: `x1 = tail`, `x13 = n2`, `dmem` maps no 8- or
4-byte word; per phase its node's register (`x12`/`x13` at the start, `x2`
in the loop). `enq1_end` (= `enq2`) is `Linked` of phase 1, which is `Start`
of phase 2. -/
abbrev enqTable2 (P : Params2) : Label → MachineData → (SharedEnv.counted (EE2 P)).State → Prop :=
  fun lb s σ => s.regs.X1.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.regs.X13.toBitVec = P.n2 ∧
    ((lb = "enq1" ∧ s.regs.X12.toBitVec = P.n1 ∧ Start P (ph1 P) σ.1) ∨
      (lb = "enq1_loop" ∧ s.regs.X2.toBitVec = P.n1 ∧ EL' P (ph1 P) σ.1) ∨
      (lb = "enq1_fix" ∧ s.regs.X2.toBitVec = P.n1 ∧ ∃ y3 y4 : Val, s.regs.X3.toBitVec = BitVec.setWidth 64 y3 ∧
        s.regs.X4.toBitVec = BitVec.setWidth 64 y4 ∧ BitVec.setWidth 64 y4 ≠ 0 ∧ EL2' P (ph1 P) y3 y4 σ.1) ∨
      ((lb = "enq1_end" ∨ lb = "enq2") ∧ s.regs.X13.toBitVec = P.n2 ∧ Start P (ph2 P) σ.1) ∨
      (lb = "enq2_loop" ∧ s.regs.X2.toBitVec = P.n2 ∧ EL' P (ph2 P) σ.1) ∨
      (lb = "enq2_fix" ∧ s.regs.X2.toBitVec = P.n2 ∧ ∃ y3 y4 : Val, s.regs.X3.toBitVec = BitVec.setWidth 64 y3 ∧
        s.regs.X4.toBitVec = BitVec.setWidth 64 y4 ∧ BitVec.setWidth 64 y4 ≠ 0 ∧ EL2' P (ph2 P) y3 y4 σ.1) ∨
      ((lb = "enq2_end" ∨ lb = "pdone") ∧ ComE2 P σ.1))

set_option hygiene false in
/-- Jump to the table entry of the target label (selected by `decide`) with
its facts `t`; leaves the edge condition. -/
local macro "land" t:term : tactic => `(tactic| (
  refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx1], by simp [hd8], by simp [hd4], by simp [hx13], ?_⟩, ?_⟩
  · simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true]
    exact $t))

set_option hygiene false in
/-- `land` with a tactic for the facts. -/
local macro "land_by" t:tactic : tactic => `(tactic| (
  refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx1], by simp [hd8], by simp [hd4], by simp [hx13], ?_⟩, ?_⟩
  · (simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true])
    $t))

set_option hygiene false in
/-- The two reads of a loop iteration (`h2`: `EL2'` after them). -/
local macro "e_reads" : tactic => `(tactic| (
  have h1 := (vc_e_ldar_tail2 (xcl := false) hph _ hT.2 v3 σ1.1 (by simpa [hx1, Params.tail] using hld1.1)).fence
    hph hf1.1
  have h2 := (vc_e_ldar_link2 hph _ h1 v4 σ3.1 (by simpa using hld2.1)).fence hph hf2.1))

set_option hygiene false in
/-- The enqueuer's VCs of a phase (`hph`), in `vcgen`'s order. -/
local macro "e_phase" h:term : tactic => `(tactic| (
  case vc2 =>
    have hph := $h
    rename_i s σ0 σ1 σ2 rng hnone hf1 hf2 _
    have hE := (hT.2.fence hph hf1.1).fence hph hf2.1
    simp [hT.1]
    refine (vc_e_str2 hph _ hE _ ?_).1
    simp [ph1, ph2, D, D2]
  case vc3 =>
    have hph := $h
    rename_i s σ0 σ1 σ2 rng dm σ3 hf1 hf2 hst _
    have hE := (hT.2.fence hph hf1.1).fence hph hf2.1
    simp [hT.1, hd4] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    simp (config := { decide := true }) [hx1, hd8, hd4, hx13, hT.1]
    rcases hso with h | h <;>
      (refine (vc_e_str2 hph _ hE _ ?_).2 _ σ3.1 (by simpa [ph1, ph2, Params.dat, Params2.dat2] using h)
       simp [ph1, ph2, D, D2])
  case vc7 =>
    have hph := $h
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hnz σ4 hld1 hf1 hld2 hf2 _
    e_reads
    simp at hnz
    land ⟨by simp [hT.1], v3, v4, by simp, by simp, hnz, h2⟩
    exact .inl (by decide)
  case vc10 =>
    have hph := $h
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 hld1 hf1 hld2 hf2 hf3 _
    e_reads
    have h := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).1
    simp [hT.1]
    simpa [casOp64, ph1, ph2] using h
  case vc11 =>
    have hph := $h
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hnz5 σ7 hld1 hf1 hld2 hf2 hf3 hcas hf4 _
    e_reads
    have hc := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hT.1, casOp64, ph1, ph2] using hcas.1)
    simp at hnz5
    rcases hc with ⟨-, hEL⟩ | ⟨h0, -⟩
    · land ⟨by simp [hT.1], hEL.fence hph hf4.1⟩
      refine .inr fun ⟨_, hg⟩ => ?_
      subst hg
      have e1 := hld1.2; have e2 := hld2.2; have e3 := hcas.2; have e4 := hf1.2; have e5 := hf2.2
      have e6 := hf3.2; have e7 := hf4.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at e1 e2 e3
      omega
    · exact absurd (by simpa using h0) hnz5
  case vc14 =>
    have hph := $h
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hz5 σ7 σ8 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5 _
    e_reads
    have hc := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hT.1, casOp64, ph1, ph2] using hcas.1)
    simp at hz5
    rcases hc with ⟨hne, -⟩ | ⟨-, hC⟩
    · exact absurd (by simpa using hz5) hne
    have h := (vc_e_swing2 hL hph _ ((hC.fence hph hf4.1).fence hph hf5.1) (BitVec.setWidth 64 v3)).1
    simp [hx1, hT.1]
    simpa [casOp64, Params.tail, ph1, ph2] using h
  case vc15 =>
    have hph := $h
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 old σ6 hz5 σ7 σ8 old2 σ9 σ10 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5 hcas2 hf6 _
    e_reads
    have hc := (vc_e_link2 hL hph _ (h2.fence hph hf3.1)).2 old σ6.1 (by simpa [hT.1, casOp64, ph1, ph2] using hcas.1)
    simp at hz5
    rcases hc with ⟨hne, -⟩ | ⟨-, hC⟩
    · exact absurd (by simpa using hz5) hne
    have hC2 := (vc_e_swing2 hL hph _ ((hC.fence hph hf4.1).fence hph hf5.1) (BitVec.setWidth 64 v3)).2 old2 σ9.1
      (by simpa [hx1, hT.1, casOp64, Params.tail, ph1, ph2] using hcas2.1)
    land_by (first | exact ⟨hx13, hC2.fence hph hf6.1⟩ | exact (hC2.fence hph hf6.1).1)
    exact .inl (by decide)
  case vc3 =>
    have hph := $h
    rename_i s σ0 σ1 hf1 _
    obtain ⟨hx2, y3, y4, hy3, hy4, hnz, h2⟩ := hT
    have h := (vc_e_fix2 hL hph _ (h2.fence hph hf1.1) hnz).1
    simp [hx1, hy3, hy4]
    simpa [casOp64, Params.tail] using h
  case vc4 =>
    have hph := $h
    rename_i s σ0 σ1 old σ2 σ3 hf1 hcas hf2 _
    obtain ⟨hx2, y3, y4, hy3, hy4, hnz, h2⟩ := hT
    have hEL := (vc_e_fix2 hL hph _ (h2.fence hph hf1.1) hnz).2 old σ2.1
      (by simpa [hx1, hy3, hy4, casOp64, Params.tail] using hcas.1)
    land ⟨by simp [hx2], hEL.fence hph hf2.1⟩
    refine .inr fun ⟨_, hg⟩ => ?_
    subst hg
    have e1 := hcas.2; have e2 := hf1.2; have e3 := hf2.2
    simp only [SharedEnv.tick_rmw] at e1
    omega))

/-- **`enq2_envGCAdj` in any ambient code** in which `enq2Prog` is `PlacedIn`, from `enq1` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem enq2_envGCAdj_at (P : Params2) (hL : QLocs2 P)
    (hpl : Program.PlacedIn enq2Prog) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt enq2Prog l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (enqTable2 P) "enq1" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (EE2 P)))
      (fun x => (x.1.2 = endA ∧ ComE2 P x.2.1) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "enq1"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EE2 P))
    (Q := fun _ σ => ComE2 P σ.1)
    (E := fun _ _ _ => False) (enqTable2 P) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [enq2Prog]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx1, hd8, hd4, hx13, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx1, hd8]; done)
  e_phase (ph1_ok hL)
  e_phase (ph2_ok P)
  case vc1 => simp (config := { decide := true }) [hx1, hd8, hd4, hx13, hT.2]
  case vc1 =>
    rename_i s σ0 σ1 hf _
    land hT.fence hf.1
    exact .inl (by decide)
  case vc1 => exact hT
  all_goals done

end EnqAt

section Enq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout enq2Prog)]

local instance enq2Prog.envG : CodeEnv := ⟨layout enq2Prog⟩

theorem enq2_envGCAdj (P : Params2) (hL : QLocs2 P) :
    PartialTripleEnv (SharedEnv.counted (EE2 P))
      (fun s σ => s.regs.X1.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.regs.X13.toBitVec = P.n2 ∧ s.regs.X12.toBitVec = P.n1 ∧
        Start P (ph1 P) σ.1)
      enq2Prog (fun _ σ => ComE2 P σ.1) (fun _ _ _ => False) :=
  have hpl : Program.Placed enq2Prog "enq1" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [enqTable2]) fun _ hlast =>
    enq2_envGCAdj_at P hL hpl.toPlacedIn hlast

end Enq

section DeqAt

variable [CodeEnv]

/-- The dequeuer's table: `x0 = head`, `x1 = tail`, `dmem` maps no 8- or
4-byte word; the second dequeue's frame `First x10`. -/
abbrev deqTable2 (P : Params2) : Label → MachineData → (SharedEnv.counted (ED2 P)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    ((lb = "deq1a" ∧ ComD2 P σ.1 ∧ True) ∨
      (lb = "deq1a_ne" ∧ ∃ y3 y5 : Val, s.regs.X3.toBitVec = BitVec.setWidth 64 y3 ∧
        s.regs.X5.toBitVec = BitVec.setWidth 64 y5 ∧ DQ3 P (fun _ => True) y3 y5 σ.1) ∨
      (lb = "deq1b" ∧ ComD2 P σ.1 ∧ First P s.regs.X10.toBitVec σ.1) ∨
      (lb = "deq1b_ne" ∧ ∃ y3 y5 : Val, s.regs.X3.toBitVec = BitVec.setWidth 64 y3 ∧
        s.regs.X5.toBitVec = BitVec.setWidth 64 y5 ∧ DQ3 P (First P s.regs.X10.toBitVec) y3 y5 σ.1) ∨
      (lb = "ddone1" ∧ Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1))

/-- The dequeuer's label rank: the `*_ne` labels above the others. -/
def deqRank2 (l : Label) : Nat := if l = "deq1a_ne" ∨ l = "deq1b_ne" then 1 else 0

set_option hygiene false in
/-- Jump to the dequeuer's table entry of the target label with its facts
`t`; leaves the edge condition. -/
local macro "dland" t:term : tactic => `(tactic| (
  refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4], ?_⟩, ?_⟩
  · (simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true])
    exact $t))

set_option hygiene false in
/-- The three reads of an iteration (`h3`: `DQ3` after them). -/
local macro "d_reads" : tactic => `(tactic| (
  have h1 := vc_d_ldar_head2 (xcl := false) hY _ hT.1 hT.2 v3 σ1.1 (by simpa [hx0, Params.head] using hld1.1)
  have h2 := (vc_d_load2 hY _ h1 v4 σ2.1 hld2.1).fence hY hf1.1
  have h3 := ((vc_d_ldar_link2 hY _ h2 v5 σ4.1 (by simpa using hld3.1)).fence hY hf2.1).fence hY hf3.1))

set_option hygiene false in
/-- The edge back to the iteration's head (the variant decreased). -/
local macro "d_back" : tactic => `(tactic| (
  refine .inr (.inr fun ⟨_, hg⟩ => ?_)
  subst hg
  simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *
  omega))

set_option hygiene false in
/-- The dequeuer's VCs of one dequeue (frame `hY`), but the success edge,
in `vcgen`'s order. -/
local macro "d_iter" y:term : tactic => `(tactic| (
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hld1 hld2 hf1 hld3 hf2 hf3 _
    have hY := $y
    d_reads
    dland ⟨v3, v5, by simp, by simp, h3⟩
    have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    d_back
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hz σ7 hld1 hld2 hf1 hld3 hf2 hf3 hf4 _
    have hY := $y
    d_reads
    dland ⟨(h3.fence hY hf4.1).1, (h3.fence hY hf4.1).2.1⟩
    have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    have e7 := hf4.2
    d_back
  case vc14 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hnz σ7 σ8 hld1 hld2 hf1 hld3 hf2 hf3 hf4 hf5 _
    have hY := $y
    d_reads
    simp at hnz
    have h := (vc_d_help2 hL hY _ ((h3.fence hY hf4.1).fence hY hf5.1) hnz).1
    simp [hx1]
    simpa [casOp64, Params.tail] using h
  case vc15 =>
    rename_i s σ0 v3 σ1 v4 σ2 σ3 v5 σ4 σ5 hne σ6 hnz σ7 σ8 old σ9 σ10 hld1 hld2 hf1 hld3 hf2 hf3 hf4 hf5 hcas hf6 _
    have hY := $y
    d_reads
    simp at hnz
    have hc := (vc_d_help2 hL hY _ ((h3.fence hY hf4.1).fence hY hf5.1) hnz).2 old σ9.1
      (by simpa [hx1, casOp64, Params.tail] using hcas.1)
    dland ⟨hc.1.fence hf6.1, hY.fence hc.2 hf6.1⟩
    have e1 := hld1.2; have e2 := hld2.2; have e3 := hld3.2; have e4 := hf1.2; have e5 := hf2.2; have e6 := hf3.2
    have e7 := hf4.2; have e8 := hf5.2; have e9 := hcas.2; have e10 := hf6.2
    d_back
  case vc1 =>
    rename_i s σ0 hz σ1 hf _
    have hY := $y
    obtain ⟨y3, y5, -, -, hD3⟩ := hT
    dland ⟨(hD3.fence hY hf.1).1, (hD3.fence hY hf.1).2.1⟩
    exact .inl (by decide)
  case vc6 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 hf1 hld hf2 _
    have hY := $y
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
    have hY := $y
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr2 hY _ (hD3.fence hY hf1.1) hnz' u σ2.1 hu.1).fence hY hf2.1
    have hc := (vc_d_cas2 hL hY _ hD4).2 old σ4.1 (by simpa [hx0, hy3, hy5, casOp64, Params.head] using hcas.1)
    dland ⟨(hc.1.fence hf3.1).fence hf4.1, hY.fence (hY.fence hc.2.1 hf3.1) hf4.1⟩
    exact .inl (by decide)))

/-- **`deq2_envGCAdj` in any ambient code** in which `deq2Prog` is `PlacedIn`, from `deq1a` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem deq2_envGCAdj_at (P : Params2) (hL : QLocs2 P)
    (hpl : Program.PlacedIn deq2Prog) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt deq2Prog l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (deqTable2 P) "deq1a" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (ED2 P)))
      (fun x => (x.1.2 = endA ∧ Dn2 P x.1.1.regs.X10.toBitVec x.1.1.regs.X11.toBitVec x.2.1) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "deq1a"), g) := by
  refine cfgEnv_partial_rank_at (env := SharedEnv.counted (ED2 P))
    (Q := fun s σ => Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1)
    (E := fun _ _ _ => False) (deqTable2 P) deqRank2 ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env_rank [deq2Prog]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hd8]; done)
  d_iter (yok_true (P := P))
  case vc8 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 old σ4 σ5 heq σ6 σ7 hf1 hld hf2 hcas hf3 hf4 hf5 _
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr2 yok_true _ (hD3.fence yok_true hf1.1) hnz' u σ2.1 hu.1).fence yok_true hf2.1
    have hc := (vc_d_cas2 hL yok_true _ hD4).2 old σ4.1
      (by simpa [hx0, hy3, hy5, casOp64, Params.head] using hcas.1)
    simp [hy3] at heq
    have hY1 := yok_first (P := P) (BitVec.setWidth 64 (BitVec.setWidth 32 u))
    have hF := hY1.fence (hY1.fence (hY1.fence (hc.2.2 (TreiberCommon.bv64_eq_of_sub_eq_zero heq)).1 hf3.1) hf4.1) hf5.1
    have hC := ((hc.1.fence hf3.1).fence hf4.1).fence hf5.1
    simp (config := { decide := true }) [hx0, hx1, hd8, hd4]
    exact ⟨hC, hF⟩
  d_iter (yok_first (P := P) s.regs.X10.toBitVec)
  case vc8 =>
    rename_i s σ0 hnz σ1 rng u0 σ2 σ3 old σ4 σ5 heq σ6 σ7 σ8 hf1 hld hf2 hcas hf3 hf4 hf5 hf6 _
    have hY := yok_first (P := P) s.regs.X10.toBitVec
    obtain ⟨y3, y5, hy3, hy5, hD3⟩ := hT
    have hnz' : BitVec.setWidth 64 y5 ≠ 0 := by simpa [hy5] using hnz
    simp [hd4, hy5] at hld
    obtain ⟨u, hu, rfl⟩ := hld
    have hD4 := (vc_d_ldr2 hY _ (hD3.fence hY hf1.1) hnz' u σ2.1 hu.1).fence hY hf2.1
    have hc := (vc_d_cas2 hL hY _ hD4).2 old σ4.1 (by simpa [hx0, hy3, hy5, casOp64, Params.head] using hcas.1)
    simp [hy3] at heq
    have hD := (hc.2.2 (TreiberCommon.bv64_eq_of_sub_eq_zero heq)).2 _ hD4.2.1
    have hDn : Dn2 P s.regs.X10.toBitVec (BitVec.setWidth 64 (BitVec.setWidth 32 u)) σ8.1 :=
      Dn2.fence (Dn2.fence (Dn2.fence (Dn2.fence ⟨hc.1, hD⟩ hf3.1) hf4.1) hf5.1) hf6.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4], ?_⟩,
      .inl (by decide)⟩
    simp (config := { decide := true })
    exact hDn
  case vc1 => exact hT
  all_goals done

end DeqAt

section Deq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout deq2Prog)]

local instance deq2Prog.envG : CodeEnv := ⟨layout deq2Prog⟩

theorem deq2_envGCAdj (P : Params2) (hL : QLocs2 P) :
    PartialTripleEnv (SharedEnv.counted (ED2 P))
      (fun s σ => s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ ComD2 P σ.1 ∧ True)
      deq2Prog (fun s σ => Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) (fun _ _ _ => False) :=
  have hpl : Program.Placed deq2Prog "deq1a" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [deqTable2]) fun _ hlast =>
    deq2_envGCAdj_at P hL hpl.toPlacedIn hlast

end Deq

end Kraken.Promising.SLR.EnvG.MsQueue
