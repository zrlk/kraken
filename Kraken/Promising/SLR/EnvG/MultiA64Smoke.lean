/-
Whole-thread environment (`EnvG`), phase 2: **the `ldp` smoke test**.

- `ldpProg` (`ldp x1, x2, [x0]`, two relaxed loads in one instruction) fails
  the phase-1 check (`dirs_phase1`) and passes the phase-2 one
  (`dirs_phase2`); so does a program mixing it with a planned `stlr`
  (`ldpStlrProg`), whose `stlr` takes the phase-1 branch. `stpProg` (two
  writes) fails the phase-2 check.
- `ldp_envG`: its VC on a toy plan by `vcgen` (`ldp_shared_spec`): under a
  resource `r₀`, both loads keep it.
- `ldpRule`: the `ThreadRuleRX` of `ofSafelyEnvG2`; `ldp_npSafe`: `NPSafe`
  from the initial configuration (`invG_init`, `qa64_of_partialTripleEnv`).
-/
import Kraken.Promising.SLR.EnvG.MultiA64
import Kraken.Promising.SLR.EnvG.A64VCGen
import Kraken.AArch64.Parser
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.SLR.EnvG.MultiA64Smoke

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- One `ldp`: two plain 8-byte loads, lower address first. -/
def ldpProg : Program := parseAArch64("
    ldp x1, x2, [x0]
")

/-- An `ldp` and a planned release store. -/
def ldpStlrProg : Program := parseAArch64("
    ldp x1, x2, [x0]
    stlr w3, [x4]
")

/-- One `stp`: two plain stores (a multi-write tree, not phase-2). -/
def stpProg : Program := parseAArch64("
    stp x1, x2, [x0]
")

/-- The toy plan: no release. -/
def toyPlan : Plan := ⟨[]⟩

theorem toyPlan_valid : toyPlan.Valid := by decide

variable [layout : _root_.Layout]

/-! ## The static checks -/

/-- `ldp` is not phase-1 code. -/
example : True := by
  fail_if_success have _h : DirsPhase1 Arch.armv8 (layout ldpProg) := by dirs_phase1 ldpProg
  trivial

/-- `stp` (two writes) is neither phase-1 nor phase-2 code. -/
example : True := by
  fail_if_success have _h : DirsPhase2 Arch.armv8 (layout stpProg) := by dirs_phase2 stpProg
  trivial

theorem ldpProg_phase2 : DirsPhase2 Arch.armv8 (layout ldpProg) := by dirs_phase2 ldpProg

theorem ldpStlrProg_phase2 : DirsPhase2 Arch.armv8 (layout ldpStlrProg) := by dirs_phase2 ldpStlrProg

/-! ## The VC on the toy plan -/

/-- The toy thread's environment. -/
abbrev E (tid : Nat) : SharedEnv := EnvG isa Arch.armv8 tid toyPlan

section VC

local instance ldpProg.env : CodeEnv := ⟨layout ldpProg⟩

/-- **The `ldp` VC**: from a resource `r₀` (and `x0` at an unmapped slot
pair) the two loads keep `r₀`. -/
theorem ldp_envG (tid : Nat) (a : BitVec 64) (r₀ : Res) :
    TripleEnv (E tid)
      (fun s σ => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 8 = none ∧
        Mem.loadInt s.dmem (a + 8) 8 = none ∧ σ.r = r₀)
      ldpProg (fun _ σ => σ.r = r₀) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold ldpProg
  vcgen [ldp_shared_spec]
  all_goals (try simp_all)
  case vc4 => trivial
  case vc5 => trivial
  case vc6 =>
    rename_i hpre h1 h2
    obtain ⟨-, hr1, -⟩ := step_loadFacts h1
    obtain ⟨-, hr2, -⟩ := step_loadFacts h2
    rw [hr2, hr1, hpre.2.2.2]

end VC

/-! ## The rule and `NPSafe` -/

section Rule

variable [Executable.ValidLayout (layout ldpProg)]

omit [Executable.ValidLayout (layout ldpProg)] in
theorem ldpProg_rmwLive : (layout ldpProg).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

/-- The toy thread's postcondition: the end of its text and `r₀`. -/
abbrev postL (r₀ : Res) : MachineState × EStateA → Prop := postOf ldpProg fun _ σ => σ.r = r₀

omit [Executable.ValidLayout (layout ldpProg)] in
/-- **`hB`**: with no promise the actual resource is the env's. -/
theorem hB_L (tid : Nat) (r₀ : Res) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postL r₀ (t.st.st, σ) → t.prom = [] → EnvRel tid toyPlan σ c t r g cl → cl → r = r₀ := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hr⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact hr
  · rw [hp] at hts; cases hts

/-- **The `ldp` thread's rule** (`ofSafelyEnvG2`; not phase-1 code). -/
def ldpRule (tid : Nat) (r₀ : Res) : ThreadRuleRX (I := isa) Arch.armv8 (fun _ r _ => r = r₀) tid :=
  ThreadRuleRX.ofSafelyEnvG2 (post := postL r₀) toyPlan_valid ldpProg_rmwLive
    (phase2Tree_of_dirs ldpProg_phase2) postOf_end (not_instrStepEnv_of_end_labels _ 0) (hB_L tid r₀)

/-- **`NPSafe` for the `ldp` thread** from the initial configuration: the
thread at the start of `ldpProg`, `x0 = a` with both slots unmapped. -/
theorem ldp_npSafe (tid : Nat) (a : BitVec 64) (r₀ : Res) (n m : Nat) {ss : List isa.State}
    {m₀ : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s) {g : Ghost} (hpend : g.pend = [])
    (he : s.exe = layout ldpProg) (hds : s.decls = {}) (hend : s.endPc = (layout ldpProg).addrOf ldpProg.length)
    (hpc : s.st.2 = (layout ldpProg).addrOf 0) (hx0 : s.st.1.regs.X0.toBitVec = a)
    (hd₁ : Mem.loadInt s.st.1.dmem a 8 = none) (hd₂ : Mem.loadInt s.st.1.dmem (a + 8) 8 = none) :
    NPSafe (model isa) Arch.armv8 (fun _ r _ => r = r₀) tid n m True (Config.init ss m₀) r₀ g :=
  letI : CodeEnv := ⟨layout ldpProg⟩
  npSafe_of_safelyEnvG2 toyPlan_valid ldpProg_rmwLive (phase2Tree_of_dirs ldpProg_phase2) postOf_end
    (not_instrStepEnv_of_end_labels _ 0) (hB_L tid r₀) n m
    (invG_init hs hpend (qa64_of_partialTripleEnv (ldp_envG tid a r₀).partial rfl he hds hend hpc
      ⟨hx0, hd₁, hd₂, rfl⟩))

end Rule

end Kraken.Promising.SLR.EnvG.MultiA64Smoke
