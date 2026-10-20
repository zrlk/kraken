/-
**Part 3: smoke test of the x64 adjacency
link** (`EnvG/X64AdjLink.lean`): one x64 thread running a single
`lock cmpxchgq %rbx, (%rdi)` on `top = ⟨t, 8⟩`, through
`ThreadRuleRXF.ofSafelyEnvGFCAdjX` to `NPSafeF` and its no-fault rule.

The thread has the empty plan (its write is not a release) and the
location's release predicate is `Pred.emp` (pure), so `RmwOkCAdj` holds from
a share of `top` alone. The run is by `vcgen` (`cfgEnv_partial` in the counted
`EnvGCAdjX`), the static checks by `dirs_phase1FX` / `dirs_no_fault`; the
start by `qx64CAdj_of_partialTripleEnv` and `invGFCAdjX_init`.
-/
import Kraken.Promising.SLR.EnvG.X64AdjVCGen
import Kraken.X64.Parser
import Kraken.EnvCfg
import Kraken.Promising.SLR.SpinInit

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.AdjSmoke

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- **The smoke thread**: one `lock cmpxchgq` on `(%rdi)`. -/
def smokeX : Program := parse("
smoke:
  lock cmpxchgq %rbx,(%rdi)
  jmp sdone
sdone:
")

/-- info: 4 -/
#guard_msgs in
#eval smokeX.length

/-- The empty plan: no write is a release. -/
def plan0 : Plan := ⟨[]⟩

theorem plan0_valid : plan0.Valid := by intro e he; cases he

theorem plan0_rel (l : Loc) (v : Val) : plan0.rel l v = false := rfl

/-- The smoke thread's environment (thread `0`, layout `[(t, 8)]`). -/
abbrev ES (t : BitVec 64) : SharedEnv := EnvGCAdjX Arch.tso 0 plan0 [(t, 8)]

/-- A share of `top`, whose release predicate is `Pred.emp`. -/
def SmP (t : BitVec 64) (σ : EStateX) : Prop := 0 < (σ.r.wr ⟨t, 8⟩).q ∧ σ.g.rel ⟨t, 8⟩ = Pred.emp

/-- **The `lock cmpxchgq` is permitted** in `EnvGCAdjX` (pure write). -/
theorem smoke_ok (t : BitVec 64) (σ : EStateX) (h : SmP t σ) (op : Val → Option Val) {a : BitVec 64}
    (ha : a = t) : (ES t).ok (.rmw .acqRel a 8 op) σ := by
  subst ha
  exact ⟨⟨h.1, fun _ _ _ _ new _ _ _ => ⟨fun _ => by rw [h.2]; exact Pred.emp_pure new,
    fun hr => by rw [plan0_rel] at hr; cases hr⟩⟩, by simp [SharedEnv.AccessIn]⟩

variable [layout : _root_.Layout]

theorem smokeX_phase1FX [Executable.ValidLayout (layout smokeX)] : Phase1TreeFX (layout smokeX) := by
  refine phase1TreeFX_of_dirs ?_
  dirs_phase1FX smokeX
  all_goals try simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS2]

theorem smokeX_noFault : DirsNoFault (layout smokeX) := by
  dirs_no_fault smokeX

section Run

variable [Executable.ValidLayout (layout smokeX)]

local instance smokeX.env : CodeEnv := ⟨layout smokeX⟩

/-- The smoke thread's table. -/
abbrev smokeTable (t : BitVec 64) : Label → MachineData → (SharedEnv.counted (ES t)).State → Prop :=
  fun lb s σ => s.regs.get64 .rdi = t ∧ Mem.loadInt s.dmem t 8 = none ∧
    ((lb = "smoke" ∧ SmP t σ.1) ∨ lb = "sdone")

/-- **The smoke thread by `vcgen`** in the counted `EnvGCAdjX`. -/
theorem smokeX_envGCAdj (t : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (ES t))
      (fun s σ => s.regs.get64 .rdi = t ∧ Mem.loadInt s.dmem t 8 = none ∧ SmP t σ.1)
      smokeX (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (smokeTable t) (hP := by funext s g; simp [smokeTable])
  cfg_cases_env [smokeX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hdt, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, or_false] at hT
  all_goals simp only [Reg64s.get64] at hx0
  all_goals first
    | (simp [hx0, hdt]; done)
    | (simp only [SharedEnv.counted_ok]; exact smoke_ok t _ hT _ (by simp [Reg64s.get64, hx0]))
    | (refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa [hx0] using hdt, .inr rfl⟩, .inl (by decide)⟩)
    | trivial

end Run

/-! ## Through the link -/

/-- The smoke thread's postcondition. -/
abbrev postS : MachineState × EStateX → Prop := postOfX smokeX fun _ _ => ∃ _ : Nat, True

/-- **The smoke thread's rule** (any shared postcondition holding of every
configuration). -/
noncomputable def smokeRule (t : BitVec 64) [Executable.ValidLayout (layout smokeX)] :
    ThreadRuleRXF (I := isa) Arch.tso (fun _ _ _ => True) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjX (S := [(t, 8)]) (post := postS) plan0_valid
    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; simp) smokeX_phase1FX postOfX_end
    (not_instrStepEnv_of_end_labels _ 1) fun _ _ _ _ _ _ _ _ _ _ => trivial

theorem smokeRule_noFault (t : BitVec 64) [Executable.ValidLayout (layout smokeX)] :
    NoFaultRuleF (smokeRule t) :=
  noFaultRuleF_ofSafelyEnvGFCAdjX_struct _ _ _ _ _ _ smokeX_noFault

/-- **`NPSafeF` of the smoke thread at the initial configuration** (a share
of `top` in its initial resource, `Pred.emp` at `top`, `rdi = t`, `top` not in
the private memory). -/
theorem smoke_npSafeF (t : BitVec 64) [Executable.ValidLayout (layout smokeX)] {s : isa.State}
    {m : List (Loc × Val)} {r : Res} {g : Ghost} (hpend : g.pend = [])
    (he : s.exe = layout smokeX) (hds : s.decls = {}) (hend : s.endPc = (layout smokeX).addrOf smokeX.length)
    (hpc : s.st.2 = (layout smokeX).addrOf 0) (hs : Split [(t, 8)] s.st.1.dmem)
    (hrdi : s.st.1.regs.get64 .rdi = t) (hq : 0 < (r.wr ⟨t, 8⟩).q) (hg : g.rel ⟨t, 8⟩ = Pred.emp) (n k : Nat) :
    NPSafeF (model isa) Arch.tso (fun _ _ _ => True) 0 n k True (Config.init [s] m) r g := by
  letI : CodeEnv := ⟨layout smokeX⟩
  exact NPSafeF.of_ruleRXF (smokeRule t) n k _ _ _ _ (invGFCAdjX_init (s := s) rfl hpend
    (qx64CAdj_of_partialTripleEnv (smokeX_envGCAdj t).uncount rfl he hds hend hpc hs
      ⟨0, hrdi, hs.loadInt_none (by simp) (by decide) (by decide), hq, hg⟩))

end Kraken.Promising.X64.EnvG.AdjSmoke

#print axioms Kraken.Promising.X64.EnvG.AdjSmoke.smoke_npSafeF
#print axioms Kraken.Promising.X64.EnvG.AdjSmoke.smokeRule_noFault
