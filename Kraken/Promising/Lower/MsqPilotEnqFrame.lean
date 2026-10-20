/-
The Michael–Scott queue's `enq` with a private-memory frame, AArch64: one
general fragment specification for clients that keep their own data in
`dmem`.

The existing `enq` specifications (`MsqPilot.enqFrag_spec`, `enqFrag_pure`)
require `NoDmem`: no 8- or 4-byte word mapped anywhere in `dmem`. A thread
that keeps private data in `dmem` (a table, a stack frame) cannot meet that.
Mapped addresses are served from `dmem` (`MachineData.loadK`), so a weaker
frame has to say that `enq`'s shared accesses miss `dmem`. `enq` reads and
CASes `tail` and `[y + 8]` for a value `y` it read from `tail`, so the frame
needs a bound on `tail`'s values. The protocol does not give one at `enq`'s
load, so the bound comes from a value restriction on load answers, as for the
Treiber fragments (`Lower/FragSpecUni.lean`):

* **The environment** `EQG P G`: msqueue2's enqueuer environment
  (`EnvGCAdj` on `planE2 P`, thread `0`) with load answers restricted to `G`
  (`Pilot2.EnvGCAdjV`). At `G = ⊤` it is `EE2 P` (`FragSpecEnv.of_vals_top`).
* **The frame** `F : Mem 64 → Prop`, kept unchanged, under `QFrameOK P G F`:
  an `F` memory maps no 8-byte word at `tail` or at the link `[y + 8]` of a
  `G`-value `y` of `tail`. `NoDmem` satisfies it for every `G`
  (`qFrameOK_noDmem`).
* `enqFrag_specF`: `enq` from `EL'` to `Linked` for either phase, frame `F`,
  post `CalleeSaved` (which keeps `dmem`). `enqFrag_spec_viaF` derives the
  existing `MsqPilot.enqFrag_spec` from it.
* `enqFrag_pureF`: the purity twin, in `RPG rel G` (the purity environment
  `counted (relPure …)` with load answers restricted to `G`) under the same
  frame. Without a value restriction it cannot be stated for a non-empty
  `dmem`: `vcgen` has only the shared rules for `ldar`/`casal`
  (`ldar_shared_spec`, `cas_shared_spec`, side condition "unmapped"), and in
  `relPure` the link address `[y + 8]` is arbitrary.

Machine: the executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness (`Safely`).
-/
import Kraken.Promising.Lower.FragSpecMsq
import Kraken.Promising.Lower.FragSpecUni
import Kraken.Promising.Lower.EnvSubstep

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.MsqPilot

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.SLR.EnvG.Treiber (casOp64)
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP)
open Kraken.Promising.Lower.Pilot2 (valsEnv LoadVal EnvGCAdjV)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The environment and the frame -/

/-- msqueue2's enqueuer environment with load answers restricted to `G`. -/
noncomputable abbrev EQG (P : Params2) (G : Loc → Val → Prop) : SharedEnv :=
  EnvGCAdjV Arch.armv8 0 (planE2 P) G

/-- **The frame condition** of `enq` at value restriction `G`: an `F` memory
maps no 8-byte word at `tail` or at the link of a `G`-value of `tail`. -/
def QFrameOK (P : Params2) (G : Loc → Val → Prop) (F : Mem 64 → Prop) : Prop :=
  ∀ d, F d → Mem.loadInt d P.t 8 = none ∧
    ∀ v : Val, G ⟨P.t, 8⟩ v → Mem.loadInt d (BitVec.setWidth 64 v + 8#64) 8 = none

theorem qFrameOK_noDmem (P : Params2) (G : Loc → Val → Prop) : QFrameOK P G Uni.NoDmemD :=
  fun _ hd => ⟨hd.1 _, fun _ _ => hd.1 _⟩

/-! ## `enq` -/

/-- `enq`'s general precondition. -/
def EnqPreF (P : Params2) (G : Loc → Val → Prop) (F : Mem 64 → Prop) (ph : Ph) (ra : Int64) (t : MachineData)
    (σ : (SharedEnv.counted (EQG P G)).State) : Prop :=
  t.lr = ra ∧ t.regs.X0.toBitVec = P.h ∧ t.regs.X1.toBitVec = ph.n ∧ F t.dmem ∧ EL' P ph σ.1

/-- `enq`'s general postcondition (`CalleeSaved` keeps `dmem`). -/
def EnqPostF (P : Params2) (G : Loc → Val → Prop) (ph : Ph) (_ : Int64) (t : MachineData)
    (_ : (SharedEnv.counted (EQG P G)).State) (t' : MachineData) (σ' : (SharedEnv.counted (EQG P G)).State) :
    Prop :=
  CalleeSaved t t' ∧ Linked P ph σ'.1

/-- `enq`'s table (`MsqPilot.enqTable` with the frame `F`). -/
abbrev enqTableF (P : Params2) (G : Loc → Val → Prop) (F : Mem 64 → Prop) (ph : Ph) (ra : Int64)
    (t : MachineData) : Label → MachineData → (SharedEnv.counted (EQG P G)).State → Prop :=
  fun lb s σ => F s.dmem ∧ s.lr = ra ∧ CalleeSaved t s ∧
    ((lb = "enq" ∧ s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = ph.n ∧ EL' P ph σ.1) ∨
      (lb = "enq_loop" ∧ s.regs.X1.toBitVec = P.t ∧ s.regs.X2.toBitVec = ph.n ∧ EL' P ph σ.1) ∨
      (lb = "enq_fix" ∧ s.regs.X1.toBitVec = P.t ∧ s.regs.X2.toBitVec = ph.n ∧ ∃ y3 y4 : Val,
        s.regs.X3.toBitVec = BitVec.setWidth 64 y3 ∧ s.regs.X4.toBitVec = BitVec.setWidth 64 y4 ∧
        BitVec.setWidth 64 y4 ≠ 0 ∧ G ⟨P.t, 8⟩ y3 ∧ EL2' P ph y3 y4 σ.1))

set_option hygiene false in
/-- Jump to a table row (selected by `decide`) with its facts `t`, the frame
kept; leaves the edge condition. -/
local macro "eland" t:term : tactic => `(tactic| (
  first
  | refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hd,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, ?_⟩, ?_⟩)
    · simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true]
      exact $t
  | refine ⟨by simpa using hd, by simpa [MachineData.lr] using hlr,
      by simpa [CalleeSaved] using hfr, ?_⟩
    simp (config := { decide := true }) only [true_and, false_and, or_false, false_or, true_or, or_true]
    exact $t))

set_option hygiene false in
/-- The two reads of a loop iteration (`h2`: `EL2'` after them). -/
local macro "e_reads" : tactic => `(tactic| (
  obtain ⟨hx1, hx2, hE⟩ := hT
  have h1 := (vc_e_ldar_tail2 (xcl := false) hph _ hE v3 σ1.1 (by simpa [hx1, Params.tail] using hld1.1.1)).fence
    hph hf1.1
  have h2 := (vc_e_ldar_link2 hph _ h1 v4 σ3.1 (by simpa using hld2.1.1)).fence hph hf2.1))

/-- **`enq`'s general specification**: for either phase, value restriction
`G` and frame `F` with `QFrameOK P G F`. -/
theorem enqFrag_specF (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (ph : Ph) (hph : PhOk P ph)
    (G : Loc → Val → Prop) (F : Mem 64 → Prop) (hF : QFrameOK P G F) :
    FragSpecEnv (SharedEnv.counted (EQG P G)) enqFrag "enq" (EnqPreF P G F ph) (EnqPostF P G ph) := by
  refine FragSpecEnv.of_cfg (fun ra t _ => enqTableF P G F ph ra t) rfl (by decide)
    (fun ra t g ⟨hlr, hx0, hx1, hd, hEL⟩ => ⟨hd, hlr, by simp [CalleeSaved], .inl ⟨rfl, hx0, hx1, hEL⟩⟩) ?_
  intro _ ra t g _
  cfg_cases_env [enqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals obtain ⟨ht8, hl8⟩ := hF _ hd
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, Pilot2.fenceMono_le_valsEnv, fenceMono_le_envGCAdj,
    SharedEnv.counted_step, SharedEnv.counted_ok, and_true] at *
  all_goals try (simp [ht]; done)
  all_goals try (simp [hT.1, ht8]; done)
  case vc5 =>
    rename_i s σ0 v3 σ1 σ2 hld1 hf1 _
    simpa using hl8 _ (by simpa [hT.1, LoadVal] using hld1.1.2)
  case vc9 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hz σ4 σ5 hld1 hf1 hld2 hf2 hf3 _
    simpa using hl8 _ (by simpa [hT.1, LoadVal] using hld1.1.2)
  case vc1 =>
    rename_i s σ0 σ1 σ2 hf1 hf2 _
    obtain ⟨hx0, hx1, hE⟩ := hT
    eland ⟨by simp [hx0, ht], by simp [hx1], (hE.fence hph hf1.1).fence hph hf2.1⟩
  case vc7 =>
    rename_i s σ0 v3 σ1 σ2 v4 σ3 hnz σ4 hld1 hf1 hld2 hf2 _
    e_reads
    simp at hnz
    eland ⟨by simp [hx1], by simp [hx2], v3, v4, by simp, by simp, hnz, by simpa [hx1, LoadVal] using hld1.1.2, h2⟩
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
    obtain ⟨hx1, hx2, y3, y4, hy3, hy4, hnz, -, h2⟩ := hT
    have h := (vc_e_fix2 hL hph _ (h2.fence hph hf1.1) hnz).1
    simp [hx1, hy3, hy4]
    simpa [casOp64, Params.tail] using h
  case vc4 =>
    rename_i s σ0 σ1 old σ2 σ3 hf1 hcas hf2 _
    obtain ⟨hx1, hx2, y3, y4, hy3, hy4, hnz, -, h2⟩ := hT
    have hEL := (vc_e_fix2 hL hph _ (h2.fence hph hf1.1) hnz).2 old σ2.1
      (by simpa [hx1, hy3, hy4, casOp64, Params.tail] using hcas.1)
    eland ⟨by simp [hx1], by simp [hx2], hEL.fence hph hf2.1⟩
    refine .inr fun ⟨_, hg⟩ => ?_
    subst hg
    have e1 := hcas.2; have e2 := hf1.2; have e3 := hf2.2
    simp only [SharedEnv.tick_rmw] at e1
    omega
  all_goals done


/-- **The existing `enq` specification from the general one** (`G = ⊤`,
`F = NoDmemD`). -/
theorem enqFrag_spec_viaF (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (ph : Ph) (hph : PhOk P ph) :
    FragSpecEnv (SharedEnv.counted (EE2 P)) enqFrag "enq" (EnqPre P ph) (EnqPost P ph) :=
  Uni.FragSpecEnv.of_vals_top ((enqFrag_specF P hL ht ph hph _ _ (qFrameOK_noDmem P _)).mono
    (fun _ _ _ ⟨hlr, hx0, hx1, hd, hEL⟩ => ⟨hlr, hx0, hx1, hd, hEL⟩) (fun _ _ _ _ _ _ h => h))

/-! ## The purity twin -/

/-- Fences of `valsEnv E G` are `E`'s: they skip if `E`'s do
(`Pilot2.valsEnv_skips`, `Lower/EnvSubstep.lean`; kept as an alias). -/
instance valsEnv_skips (E : SharedEnv) [E.Skips] (G : Loc → Val → Prop) : (valsEnv E G).Skips :=
  Pilot2.valsEnv_skips E G

/-- The purity environment with load answers restricted to `G`. -/
noncomputable abbrev RPG (rel : Loc → Pred) (G : Loc → Val → Prop) : SharedEnv :=
  SharedEnv.counted (valsEnv (SharedEnv.relPure Arch.armv8 rel) G)

/-- **`enq` is pure** in `RPG rel G`, frame `F` with `QFrameOK P G F`: every
access is shared, the `casal`s are release RMWs, unconstrained by `relPure`. -/
theorem enqFrag_pureF (P : Params2) (ht : P.t = P.h + 8) (rel : Loc → Pred) (G : Loc → Val → Prop)
    (F : Mem 64 → Prop) (hF : QFrameOK P G F) :
    FragSpecEnv (RPG rel G) enqFrag "enq" (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.h ∧ F s.dmem)
      (fun _ s _ s' _ => CalleeSaved s s') := by
  refine FragSpecEnv.of_cfg
    (fun ra t0 _ lb s (_ : (RPG rel G).State) => F s.dmem ∧ s.lr = ra ∧ CalleeSaved t0 s ∧
      ((lb = "enq" ∧ s.regs.X0.toBitVec = P.h) ∨ (lb = "enq_loop" ∧ s.regs.X1.toBitVec = P.t) ∨
        (lb = "enq_fix" ∧ s.regs.X1.toBitVec = P.t)))
    rfl (by decide) (fun ra t0 g ⟨hlr, hx0, hd⟩ => ⟨hd, hlr, by simp [CalleeSaved], .inl ⟨rfl, hx0⟩⟩) ?_
  intro _ ra t0 g _
  cfg_cases_env [enqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals obtain ⟨ht8, hl8⟩ := hF _ hd
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hT, ht8, SharedEnv.relPureQ]; done)
  -- the `casal`s are release RMWs: unconstrained
  all_goals try (simp [SharedEnv.relPureQ]; exact fun h => (h (by decide)).elim)
  case vc5 =>
    rename_i s σ0 v3 σ1 hld1 _
    simpa using hl8 _ (by simpa [hT, LoadVal] using hld1.1.2)
  case vc9 =>
    rename_i s σ0 v3 σ1 v4 σ2 hz hld1 hld2 _
    simpa using hl8 _ (by simpa [hT, LoadVal] using hld1.1.2)
  all_goals try (exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩)
  all_goals first
    | exact ⟨by simpa using hd, by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr,
        by simp (config := { decide := true }) [hT, ht]⟩
    | (refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hd, by simpa [MachineData.lr] using hlr,
          by simpa [CalleeSaved] using hfr, by simp (config := { decide := true }) [hT, ht]⟩, ?_⟩)
       first
       | exact .inl (by decide)
       | exact .inr fun ⟨_, hg⟩ => by subst hg; simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *; omega)

end Kraken.Promising.Lower.MsqPilot
