/-
**`treiber_aba_tagged.kl`, part 7: purity and the
image's per-cell facts.**

- `p0V_noNT`, `p1V_noNT`: both threads' runs make only release writes
  (counted, partial, in `relPureQ Arch.tso False`; every shared write is a
  TSO plain store or a `lock cmpxchg16b`, both release). The table is the
  private stack `Stk` alone.
-/
import Kraken.Promising.SLR.EnvG.X64VecTreiberABARun1
import Kraken.Promising.SLR.EnvG.X64VecDeclsLinkAdj

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.VecABA

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The purity environment of the runs. -/
abbrev EnvP : SharedEnv := SharedEnv.relPureQ Arch.tso fun _ _ => False

variable [layout : _root_.Layout] [Executable.ValidLayout (layout abaImageV)]

local instance abaImageV.envP : CodeEnv := ⟨layout abaImageV⟩


set_option hygiene false in
/-- The `head` load and the slot round trip, then a branch: the table goal
(the counter grew by the load's tick). -/
local macro "ld_tab" : tactic => `(tactic| (
  rename_i s1 g0 v g1 r1 g2 r2 g3 af hz hld hm1 hm2 _
  obtain ⟨-, rfl⟩ := rd_lo hm1
  simp only [Reg64s.get64_set64] at hm2
  obtain ⟨-, rfl⟩ := rd_hi hm2
  refine Table.ofLabelsEnv_at ⟨by decide, Stk.slot hstk (by simp) rfl, ?_⟩
  first
    | exact .inl (by decide)
    | (refine .inr fun ⟨_, hg⟩ => ?_
       subst hg
       have h1 := hld.2
       simp only [SharedAccess.tick] at h1
       omega)))

set_option hygiene false in
/-- A pop's run to its `cmpxchg16b`, then a branch: the table goal. -/
local macro "pop_tab" : tactic => `(tactic| (
  rename_i s1 g0 v g1 r1 g2 r2 g3 af hz u g4 old g5 heq hnz hld hm1 hm2 hnode hcas _
  obtain ⟨-, rfl⟩ := rd_lo hm1
  simp only [Reg64s.get64_set64] at hm2
  obtain ⟨-, rfl⟩ := rd_hi hm2
  obtain ⟨-, hc⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
  refine Table.ofLabelsEnv_at ⟨by decide, Stk.slot hstk (by simp) rfl, ?_⟩
  first
    | exact .inl (by decide)
    | (refine .inr fun ⟨_, hg⟩ => ?_
       subst hg
       have h1 := hld.2; have h3 := hcas.2
       simp only [SharedAccess.tick] at h1 h3
       omega)))

set_option hygiene false in
/-- A pop's run to its `cmpxchg16b`, then a fallthrough: the stack. -/
local macro "pop_stk" : tactic => `(tactic| (
  rename_i s1 g0 v g1 r1 g2 r2 g3 af hz u g4 old g5 heq hnz hld hm1 hm2 hnode hcas _
  exact Stk.slot hstk (by simp) rfl))

set_option hygiene false in
/-- The push's run to its `cmpxchg16b`, then a branch: the table goal. -/
local macro "push_tab" : tactic => `(tactic| (
  rename_i s1 g0 v g1 r1 g2 r2 g3 dm g4 old g5 heq hnz hld hm1 hm2 hst hcas _
  obtain ⟨-, rfl⟩ := rd_lo hm1
  simp only [Reg64s.get64_set64] at hm2
  obtain ⟨-, rfl⟩ := rd_hi hm2
  obtain ⟨-, hcnt, hD, hmono⟩ := stCase (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 rfl rfl hst
  refine Table.ofLabelsEnv_at ⟨by decide, Stk.ofDom hstk (by simp) hD
    (hmono _ _ (Stk.store hstk.1 hstk.2.1 hstk.2.1).2), ?_⟩
  first
    | exact .inl (by decide)
    | (refine .inr fun ⟨_, hg⟩ => ?_
       subst hg
       have h1 := hld.2; have h3 := hcas.2
       simp only [SharedAccess.tick] at h1 h3
       omega)))

set_option maxHeartbeats 4000000 in
/-- **Thread `0`'s verbatim run makes only release writes** (counted,
partial). -/
theorem p0V_noNT (S : BitVec 64 → Prop) (hal : isAligned 16 (symV "head") = true) :
    ∀ s g, Stk S (symV "head") s →
      Safely (cenv.instrStepEnv (SharedEnv.counted EnvP))
        (fun x => (x.1.2 = labV "done" ∧ True) ∨ False) ((s, labV "p0"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted EnvP)
    (Q := fun _ _ => True) (E := fun _ _ _ => False)
    (fun lb s _ => Stk S (symV "head") s ∧ (lb = "p0" ∨ lb = "done")) ?_ rfl (by decide) abaCodeV_placedIn
    abaCodeV_last s g ⟨hsg, .inl rfl⟩
  cfg_cases_env [abaCodeV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hstk, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [or_false, false_or, or_true, true_or] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => trivial
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 => trivial
  case vc7 => trivial
  case vc8 =>
    rename_i s1 g0 v g1 r1 g2 r2 g3 af hz hld hm1 hm2 _
    obtain ⟨-, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨-, rfl⟩ := rd_hi hm2
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨Stk.slot hstk (by simp) rfl, .inl rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2
    simp only [SharedAccess.tick] at h1
    omega
  case vc9 => trivial
  case vc10 => exact hal
  case vc11 => exact (Stk.store hstk.1 hstk.2.1 hstk.2.1).1.loadInt_none hstk.2.2.2 (by decide)
  case vc12 => simp [SharedEnv.relPureQ]; rfl
  all_goals
    rename_i s1 g0 v g1 r1 g2 r2 g3 af hz u g4 old g5 heq hnz hld hm1 hm2 hnode hcas _
    obtain ⟨-, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨-, rfl⟩ := rd_hi hm2
    obtain ⟨-, hc⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨Stk.slot hstk (by simp) rfl, by decide⟩, ?_⟩
    first
      | exact .inl (by decide)
      | (refine .inr fun ⟨_, hg⟩ => ?_
         subst hg
         have h1 := hld.2; have h3 := hcas.2
         simp only [SharedAccess.tick] at h1 h3
         omega)

set_option maxHeartbeats 8000000 in
/-- **Thread `1`'s verbatim run makes only release writes** (counted,
partial). -/
theorem p1V_noNT (S : BitVec 64 → Prop) (hal : isAligned 16 (symV "head") = true) :
    ∀ s g, Stk S (symV "head") s →
      Safely (cenv.instrStepEnv (SharedEnv.counted EnvP))
        (fun x => (x.1.2 = labV "done" ∧ True) ∨ False) ((s, labV "p1"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted EnvP)
    (Q := fun _ _ => True) (E := fun _ _ _ => False)
    (fun _ s _ => Stk S (symV "head") s) ?_ abaCode1_eq abaCode1_wf abaCode1_placedIn
    abaCode1_last s g hsg
  cfg_cases_env [abaCode1]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hstk, rfl, rfl⟩ := ‹Stk _ _ _ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  case vc1 => exact hstk
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => trivial
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 => trivial
  case vc7 => trivial
  case vc8 => ld_tab
  case vc9 => trivial
  case vc10 => exact hal
  case vc11 => exact (Stk.store hstk.1 hstk.2.1 hstk.2.1).1.loadInt_none hstk.2.2.2 (by decide)
  case vc12 => simp [SharedEnv.relPureQ]; rfl
  case vc13 => pop_tab
  case vc14 => pop_stk
  case vc15 => pop_tab
  case vc16 => pop_stk
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => trivial
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 => trivial
  case vc7 => trivial
  case vc8 => ld_tab
  case vc9 => trivial
  case vc10 => exact hal
  case vc11 => exact (Stk.store hstk.1 hstk.2.1 hstk.2.1).1.loadInt_none hstk.2.2.2 (by decide)
  case vc12 => simp [SharedEnv.relPureQ]; rfl
  case vc13 => pop_tab
  case vc14 => pop_stk
  case vc15 => pop_tab
  case vc16 => pop_stk
  case vc1 => exact Table.ofLabelsEnv_at ⟨by decide, hstk, .inl (by decide)⟩
  case vc2 => exact hstk
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => trivial
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 => trivial
  case vc7 => trivial
  case vc8 => simp [SharedEnv.relPureQ]; rfl
  case vc9 => exact hal
  case vc10 =>
    rename_i s1 g0 v g1 r1 g2 r2 g3 dm g4 hld hm1 hm2 hst _
    obtain ⟨-, -, hD, -⟩ := stCase (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 rfl rfl hst
    exact hD.loadInt_none hstk.2.2.2 (by decide)
  case vc11 => simp [SharedEnv.relPureQ]; rfl
  case vc12 => push_tab
  case vc13 => push_tab
  case vc14 => push_tab
  case vc15 => push_tab

end Kraken.Promising.X64.EnvG.VecABA
