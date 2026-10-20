/-
**The specification of WeakCore's `deq`**
(`wcDeqFrag` in shape A's text `progD`). ISA: AArch64;
environment: msqueue2's dequeuer environment `ED2 P` (`EnvGCAdj` on
`planD2`, thread `1`), counted.

`wdeq_spec`: from `MsqPilot`'s `DeqPre` (`x30 = ra`, `x0 = q = &head`, no
`dmem` word, `ComD2`) to `WDeqPost`: the callee-saved frame, `ComD2`, every
`First` of the entry state kept (`Kept`), and either the tag `x0 = 1`
(`inr ()`, the queue was seen empty) or the tag `x0 = 0` with the payload
`x1` dequeued by its own swing of `head` (`First`), above every earlier
dequeue (`DoneD2`). One `vcgen` call per block, with `Lower/WcMsqVC.lean`'s
VCs; `deq`'s only back edge (`b.ne deq`, a failed `casal`) follows shared
accesses, so the plain `cfgEnv_partial_fun` applies (no rank).
-/
import Kraken.Promising.Lower.WcMsqVC
import Kraken.Promising.Lower.MsqPilotSpecs

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.WcMsq

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.SLR.EnvG.Treiber (casOp64)
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem)
open Kraken.Promising.Lower.MsqPilot (DeqPre Kept yok_kept)

set_option mvcgen.warning false
set_option experimental.vcgen true

section Deq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progD)]

local instance progD.env : CodeEnv := ⟨layout progD⟩

omit layout [Executable.ValidLayout (layout progD)] in
theorem progD_wf : Program.WF progD := by decide

/-- Where `progD`'s blocks sit. -/
theorem progD_placed : Program.Placed progD "main_d" :=
  Program.placed_of_layout progD_wf rfl (by decide)

/-- `deq`'s postcondition: the frame, `ComD2`, `Kept`, and the result: tag
`1` (empty), or tag `0` with the payload's `First` and `DoneD2` after every
`First` of the entry state. -/
def WDeqPost (P : Params2) (_ : Int64) (t : MachineData) (σ : (SharedEnv.counted (ED2 P)).State)
    (t' : MachineData) (σ' : (SharedEnv.counted (ED2 P)).State) : Prop :=
  CalleeSaved t t' ∧ ComD2 P σ'.1 ∧ Kept P σ.1 σ'.1 ∧
    (t'.regs.X0.toBitVec = 1 ∨ (t'.regs.X0.toBitVec = 0 ∧ First P t'.regs.X1.toBitVec σ'.1 ∧
      ∀ x0, First P x0 σ.1 → DoneD2 σ'.1.snap.mem P x0 t'.regs.X1.toBitVec))

/-- `deq`'s table: `q` in `x0`, the frame, `ComD2` and `Kept`, at `deq` and
at `deq_empty`. -/
abbrev wdeqTable (P : Params2) (ra : Int64) (t : MachineData) (σ₀ : State isa) :
    Label → MachineData → (SharedEnv.counted (ED2 P)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.h ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.lr = ra ∧ CalleeSaved t s ∧ ComD2 P σ.1 ∧ Kept P σ₀ σ.1 ∧
    (lb = "deq" ∨ lb = "deq_empty")

set_option hygiene false in
/-- The two plain reads of `deq` (`h3`: `DQ3w` after them). -/
local macro "w_reads" : tactic => `(tactic| (
  have hY := yok_kept P g.1
  simp [hd8] at hld1 hld2
  obtain ⟨u3, hu3, rfl⟩ := hld1
  obtain ⟨u5, hu5, rfl⟩ := hld2
  rw [hx0] at hu3
  have h1 := (vc_d_ldr_head hY _ hC hK u3 σ1.1 hu3.1).fence hY hf1.1
  have h3 := (vc_d_ldr_link hY _ h1 u5 σ3.1 hu5.1).fence hY hf2.1))

/-- **WeakCore's `deq`, specified**, once for both calls. -/
theorem wdeq_spec (P : Params2) (hL : QLocs2 P) :
    FunSpecPartialEnv (SharedEnv.counted (ED2 P)) ((_root_.Executable.labels cenv).label "deq") (DeqPre P)
      (WDeqPost P) := by
  rintro ra t g ⟨hlr, hx0, ⟨hd8, hd4⟩, hC⟩
  refine cfgEnv_partial_fun (p := wcDeqFrag) (wdeqTable P ra t g.1)
    (E := fun a s σ => a = ra ∧ WDeqPost P ra t g s σ) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE progD_placed (by decide)) t g
    ⟨hx0, hd8, hd4, hlr, by simp [CalleeSaved], hC, fun _ h => h, .inl rfl⟩
  cfg_cases_env [wcDeqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd8, hd4, hlr, hfr, hC, hK, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hd8]; done)
  case vc5 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v5 σ3 hz σ4 hld1 hf1 hld2 hf2 _
    w_reads
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, h3.1, h3.2.1, by decide⟩, ?_⟩)
    exact .inl (by decide)
  case vc8 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v5 σ3 hnz σ4 σ5 hld1 hf1 hld2 hf2 hf3 _
    w_reads
    replace h3 := h3.fence hY hf3.1
    simp at hnz
    have h := (vc_d_casw hL hY _ h3 hnz).1
    simp [hx0]
    simpa [casOp64, Params.head] using h
  case vc9 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v5 σ3 hnz σ4 σ5 old σ6 σ7 hne σ8 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5 _
    w_reads
    replace h3 := h3.fence hY hf3.1
    simp at hnz
    have hc := (vc_d_casw hL hY _ h3 hnz).2 old σ6.1 (by simpa [hx0, casOp64, Params.head] using hcas.1)
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, (hc.1.fence hf4.1).fence hf5.1,
      hY.fence (hY.fence hc.2.1 hf4.1) hf5.1, by decide⟩, ?_⟩)
    refine .inr fun ⟨_, hg⟩ => ?_
    subst hg
    have e1 := hu3.2; have e2 := hu5.2; have e3 := hcas.2; have e4 := hf1.2; have e5 := hf2.2
    have e6 := hf3.2; have e7 := hf4.2; have e8 := hf5.2
    simp only [SharedEnv.tick_rmw] at e3
    omega
  case vc12 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v5 σ3 hnz σ4 σ5 old σ6 σ7 heq σ8 r3 u σ9 σ10 σ11 hld1 hf1 hld2 hf2 hf3 hcas
      hf4 hf5 hld3 hf6 hf7 _
    w_reads
    replace h3 := h3.fence hY hf3.1
    simp at hnz
    have hc := (vc_d_casw hL hY _ h3 hnz).2 old σ6.1 (by simpa [hx0, casOp64, Params.head] using hcas.1)
    simp at heq
    have hsw := ((hc.2.2 (TreiberCommon.bv64_eq_of_sub_eq_zero heq)).fence hf4.1).fence hf5.1
    simp [hd4] at hld3
    obtain ⟨u1, hu1, rfl⟩ := hld3
    have hp := vc_d_ldr_payload hY _ hsw (hY.fence (hY.fence hc.2.1 hf4.1) hf5.1) u1 σ9.1 hu1.1
    have hF := yok_first (P := P) (BitVec.setWidth 64 (BitVec.setWidth 32 u1))
    refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr,
      (hp.1.fence hf6.1).fence hf7.1, hY.fence (hY.fence hp.2.1 hf6.1) hf7.1, .inr ⟨by simp, ?_, ?_⟩⟩
    · simpa using hF.fence (hF.fence hp.2.2.1 hf6.1) hf7.1
    · intro x0 h0
      have := hp.2.2.2 x0 (h3.2.1 x0 h0)
      simpa [hf6.1.snap, hf7.1.snap] using this
  case vc1 =>
    rename_i s σ0 σ1 σ2 hf1 hf2 _
    have hY := yok_kept P g.1
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr,
      (hC.fence hf1.1).fence hf2.1, hY.fence (hY.fence hK hf1.1) hf2.1, .inl (by simp)⟩
  all_goals done

end Deq

end Kraken.Promising.Lower.WcMsq
