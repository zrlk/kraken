/-
Whole-thread environment (`EnvG`), phase 3: **the `stp` smoke
test**.

- `stpProg` (`stp x1, x2, [x0]`, two plain stores in one instruction) fails
  the phase-2 check (`dirs_phase2`) and passes the phase-3 one
  (`dirs_phase3`); so does a program mixing it with an `ldp` and a planned
  `stlr` (`ldpStpStlrProg`), which take the phase-2 and phase-1 branches.
  An `stp` followed by nothing else passes `dirs_no_fault`.
- `stp_envG`: its VC on the toy plan by `vcgen` (`stp_shared_spec`): from
  positive write shares of both slots with pure predicates, both stores are
  permitted and keep them.
- `stpRule`: the `ThreadRuleRX` of `ofSafelyEnvG3`; `stp_npSafe`: `NPSafe`
  from the initial configuration (`invG_init`, `qa64_of_partialTripleEnv`);
  `stpRule_noFault`: its no-fault rule (`noFaultRule_ofSafelyEnvG3_struct`).
- `ldpRule_noFault`: the phase-2 no-fault rule (`noFaultRule_ofSafelyEnvG2_struct`,
  `MultiNoFault.lean`) for `MultiA64Smoke`'s `ldp` thread.
-/
import Kraken.Promising.SLR.EnvG.MultiWriteA64
import Kraken.Promising.SLR.EnvG.MultiNoFault
import Kraken.Promising.SLR.EnvG.MultiA64Smoke
import Kraken.Promising.SLR.EnvG.A64VCGen
import Kraken.Promising.SLR.EnvG.Simp
import Kraken.AArch64.Parser
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.SLR.EnvG.MultiWriteA64Smoke

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- One `stp`: two plain 8-byte stores, lower address first. -/
def stpProg : Program := parseAArch64("
    stp x1, x2, [x0]
")

/-- An `ldp`, an `stp` and a planned release store. -/
def ldpStpStlrProg : Program := parseAArch64("
    ldp x5, x6, [x7]
    stp x1, x2, [x0]
    stlr w3, [x4]
")

/-- The toy plan: no release. -/
def toyPlan : Plan := ⟨[]⟩

theorem toyPlan_valid : toyPlan.Valid := by decide

variable [layout : _root_.Layout]

/-! ## The static checks -/

/-- `stp` is not phase-2 code. -/
example : True := by
  fail_if_success have _h : DirsPhase2 Arch.armv8 (layout stpProg) := by dirs_phase2 stpProg
  trivial

theorem stpProg_phase3 : DirsPhase3 Arch.armv8 (layout stpProg) := by dirs_phase3 stpProg

theorem ldpStpStlrProg_phase3 : DirsPhase3 Arch.armv8 (layout ldpStpStlrProg) := by dirs_phase3 ldpStpStlrProg

theorem stpProg_noFault : DirsNoFault (layout stpProg) := by dirs_no_fault' stpProg

/-! ## The VC on the toy plan -/

/-- The toy thread's environment. -/
abbrev E (tid : Nat) : SharedEnv := EnvG isa Arch.armv8 tid toyPlan

/-- The thread may write `l`, with pure values only (no release protocol on
`l`). -/
def Own (σ : State isa) (l : Loc) : Prop := 0 < (σ.r.wr l).q ∧ ∀ v, Pred.Pure (σ.g.rel l) v

/-- **A toy store** is permitted on an owned location, and keeps every owned
location owned. -/
theorem toy_store (tid : Nat) {σ : State isa} {addr : BitVec 64} {n : Nat} {v : Val} (h : Own σ ⟨addr, n⟩) :
    (E tid).ok (.store .plain false addr n v) σ ∧
      ∀ b (σ' : State isa), (E tid).step (.store .plain false addr n v) σ b σ' → ∀ l, Own σ l → Own σ' l := by
  refine ⟨⟨rfl, h.1, fun _ => h.2 v, fun hr => by simp [toyPlan, Plan.rel, Plan.find?] at hr⟩, ?_⟩
  intro b σ' hs l hl
  obtain ⟨c, tw, hanc, -, -, -, -, hr, -⟩ := step_storeFacts hs
  obtain ⟨_, -, hr⟩ := hr
  have hr' : σ'.r = σ.r.addW ⟨addr, n⟩ (v, tw) := by
    simpa [toyPlan, Plan.after, Plan.rel, Plan.find?] using hr
  exact ⟨by rw [hr', Res.addW_q]; exact hl.1, by rw [hanc.rel]; exact hl.2⟩

section VC

local instance stpProg.env : CodeEnv := ⟨layout stpProg⟩

/-- **The `stp` VC**: from owned slots (and `x0 = a` at an unmapped slot
pair), both stores are permitted and keep the slots owned. -/
theorem stp_envG (tid : Nat) (a : BitVec 64) :
    TripleEnv (E tid)
      (fun s σ => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 8 = none ∧
        Mem.loadInt s.dmem (a + 8) 8 = none ∧ Own σ ⟨a, 8⟩ ∧ Own σ ⟨a + 8, 8⟩)
      stpProg (fun _ σ => Own σ ⟨a, 8⟩ ∧ Own σ ⟨a + 8, 8⟩) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold stpProg
  vcgen [stp_shared_spec]
  all_goals (try simp_all)
  case vc4 =>
    rename_i hpre
    exact (toy_store tid hpre.2.2.2.1).1
  case vc5 =>
    rename_i hpre h1
    exact (toy_store tid ((toy_store tid hpre.2.2.2.1).2 _ _ h1 _ hpre.2.2.2.2)).1
  case vc6 =>
    rename_i hpre h1 h2
    have k1 := (toy_store tid hpre.2.2.2.1).2 _ _ h1
    have k2 := (toy_store tid (k1 _ hpre.2.2.2.2)).2 _ _ h2
    exact ⟨k2 _ (k1 _ hpre.2.2.2.1), k2 _ (k1 _ hpre.2.2.2.2)⟩

end VC

/-! ## The rule, `NPSafe` and no fault -/

section Rule

variable [Executable.ValidLayout (layout stpProg)]

omit [Executable.ValidLayout (layout stpProg)] in
theorem stpProg_rmwLive : (layout stpProg).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

/-- The toy thread's postcondition: the end of its text, both slots owned. -/
abbrev postS (a : BitVec 64) : MachineState × EStateA → Prop :=
  postOf stpProg fun _ σ => Own σ ⟨a, 8⟩ ∧ Own σ ⟨a + 8, 8⟩

/-- The toy thread's final resource condition: write shares of both slots. -/
abbrev BS (a : BitVec 64) : Config isa → Res → Ghost → Prop :=
  fun _ r _ => 0 < (r.wr ⟨a, 8⟩).q ∧ 0 < (r.wr ⟨a + 8, 8⟩).q

omit [Executable.ValidLayout (layout stpProg)] in
/-- **`hB`**: with no promise the actual resource is the env's. -/
theorem hB_S (tid : Nat) (a : BitVec 64) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postS a (t.st.st, σ) → t.prom = [] → EnvRel tid toyPlan σ c t r g cl → cl → BS a c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, h1, h2⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨h1.1, h2.1⟩
  · rw [hp] at hts; cases hts

/-- **The `stp` thread's rule** (`ofSafelyEnvG3`; not phase-2 code). -/
def stpRule (tid : Nat) (a : BitVec 64) : ThreadRuleRX (I := isa) Arch.armv8 (BS a) tid :=
  ThreadRuleRX.ofSafelyEnvG3 (post := postS a) toyPlan_valid stpProg_rmwLive
    (phase3Tree_of_dirs stpProg_phase3) postOf_end (not_instrStepEnv_of_end_labels _ 0) (hB_S tid a)

/-- **No fault for the `stp` thread**, with or without promises. -/
theorem stpRule_noFault (tid : Nat) (a : BitVec 64) : NoFaultRule (stpRule tid a) :=
  noFaultRule_ofSafelyEnvG3_struct _ _ _ _ _ _ stpProg_noFault

/-- **`NPSafe` for the `stp` thread** from the initial configuration: the
thread at the start of `stpProg`, `x0 = a` with both slots unmapped, the
resource owning both slots with pure predicates. -/
theorem stp_npSafe (tid : Nat) (a : BitVec 64) (n m : Nat) {ss : List isa.State}
    {m₀ : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s) {r₀ : Res} {g : Ghost} (hpend : g.pend = [])
    (he : s.exe = layout stpProg) (hds : s.decls = {}) (hend : s.endPc = (layout stpProg).addrOf stpProg.length)
    (hpc : s.st.2 = (layout stpProg).addrOf 0) (hx0 : s.st.1.regs.X0.toBitVec = a)
    (hd₁ : Mem.loadInt s.st.1.dmem a 8 = none) (hd₂ : Mem.loadInt s.st.1.dmem (a + 8) 8 = none)
    (hq₁ : 0 < (r₀.wr ⟨a, 8⟩).q) (hq₂ : 0 < (r₀.wr ⟨a + 8, 8⟩).q)
    (hp₁ : ∀ v, Pred.Pure (g.rel ⟨a, 8⟩) v) (hp₂ : ∀ v, Pred.Pure (g.rel ⟨a + 8, 8⟩) v) :
    NPSafe (model isa) Arch.armv8 (BS a) tid n m True (Config.init ss m₀) r₀ g :=
  letI : CodeEnv := ⟨layout stpProg⟩
  npSafe_of_safelyEnvG3 toyPlan_valid stpProg_rmwLive (phase3Tree_of_dirs stpProg_phase3) postOf_end
    (not_instrStepEnv_of_end_labels _ 0) (hB_S tid a) n m
    (invG_init hs hpend (qa64_of_partialTripleEnv (stp_envG tid a).partial rfl he hds hend hpc
      ⟨hx0, hd₁, hd₂, ⟨hq₁, hp₁⟩, ⟨hq₂, hp₂⟩⟩))

end Rule

/-! ## Phase-2 no fault: the `ldp` thread of `MultiA64Smoke` -/

section Ldp

open MultiA64Smoke in
theorem ldpProg_noFault : DirsNoFault (layout MultiA64Smoke.ldpProg) := by dirs_no_fault' ldpProg

variable [Executable.ValidLayout (layout MultiA64Smoke.ldpProg)]

/-- **No fault for the `ldp` thread** (`MultiA64Smoke.ldpRule`, phase 2):
`noFaultRule_ofSafelyEnvG2_struct`. -/
theorem ldpRule_noFault (tid : Nat) (r₀ : Res) : NoFaultRule (MultiA64Smoke.ldpRule tid r₀) :=
  noFaultRule_ofSafelyEnvG2_struct _ _ _ _ _ _ ldpProg_noFault

end Ldp

end Kraken.Promising.SLR.EnvG.MultiWriteA64Smoke

#print axioms Kraken.Promising.SLR.EnvG.MultiWriteA64Smoke.stp_npSafe
#print axioms Kraken.Promising.SLR.EnvG.MultiWriteA64Smoke.stpRule_noFault
#print axioms Kraken.Promising.SLR.EnvG.MultiWriteA64Smoke.ldpStpStlrProg_phase3
#print axioms Kraken.Promising.SLR.EnvG.MultiWriteA64Smoke.ldpRule_noFault
