/-
**Part 9: the skipping reader's rule,
no-fault rule and `NPSafeP`** (the reader half of `TakeMpPublic`, on the
cumulative take route `ofSafelyEnvGTU`).

- `SPost P rd`: the reader `rd`, if its `W3` is `2`, holds all of `Dt` with
  maximal write `(43, tw)` (`Own43`) and has `W4 = 43`.
- `skipRuleR : ThreadRuleRXGS G₀ Arch.armv8 (SPost P tid) tid`
  (`ThreadRuleRXGS.ofSafelyEnvGTU` from `skipReader_envGTU`), and its no-fault
  rule `skipRuleR_noFault` (`noFaultRule_ofSafelyEnvGTU_struct`).
- **`skipReader_npSafeP`**: `NPSafeP (model isa) Arch.armv8 (SPost P tid) tid
  G₀ (K2Scope (model isa) AllocIds)` at the initial configuration, for any
  initial resource and ghost in which the flag's release predicate is
  `skipPred`, `Dt` is pure, and the reader holds an acquire id of `Fl` with
  `skipPred` — the per-thread input of `final_of_relWritesJS` /
  `final_of_relPureSafelyS`.
-/
import Kraken.Promising.SLR.EnvG.TakeUSkipVCGen

namespace Kraken.Promising.SLR.EnvG.TakeUSkip

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp
open Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp

/-- **The reader's postcondition** (`NPSafe`'s `B`): if `W3 = 2`, all of
`Dt` with maximal write `(43, tw)` and `W4 = 43`. -/
def SPost (P : Params) (rd : Nat) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  ∃ t, c.threads[rd]? = some t ∧ (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec = 2 →
    Own43 P r ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43)

section Reader

variable [layout : _root_.Layout] [Executable.ValidLayout (layout skipReader)]

omit [Executable.ValidLayout (layout skipReader)] in
theorem skipReader_rmwLive : (layout skipReader).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem skipReader_phase1 : Phase1Tree Arch.armv8 (layout skipReader) :=
  phase1Tree_of_dirs (by dirs_phase1 skipReader)

omit [Executable.ValidLayout (layout skipReader)] in
theorem skipReader_noFault : DirsNoFault (layout skipReader) := by dirs_no_fault' skipReader

/-- The reader's postcondition at the end of its text (the counter of
`skipReader_envGTU` projected away). -/
abbrev postS (P : Params) : MachineState × EStateA → Prop :=
  postOf skipReader fun s σ =>
    ∃ _ : Nat, SkipDone P (s.regs.X3.toBitVec.setWidth 32) (s.regs.X4.toBitVec.setWidth 32) σ.cl σ.r

omit [Executable.ValidLayout (layout skipReader)] in
/-- **`hB` for the reader**: with no promise its resource is the env's. -/
theorem hB_S (P : Params) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postS P (t.st.st, σ) → t.prom = [] → EnvRel tid rdPlan σ c t r g cl → cl → SPost P tid c r g := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, hd⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact ⟨t, hrel.ht, fun h3 => ⟨(hd h3).1, (hd h3).2 (hrel.cl hcl)⟩⟩

/-- **The skipping reader's rule** on the cumulative take route. -/
def skipRuleR (P : Params) (tid : Nat) : ThreadRuleRXGS G₀ Arch.armv8 (SPost P tid) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTU (e := layout skipReader) (post := postS P) rdPlan_valid skipReader_rmwLive
    skipReader_phase1 postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_S P tid)

/-- **The reader's no-fault rule.** -/
theorem skipRuleR_noFault (P : Params) (tid : Nat) : NoFaultRuleS (skipRuleR P tid) :=
  noFaultRule_ofSafelyEnvGTU_struct _ _ _ _ _ _ skipReader_noFault

end Reader

section Start

variable [layout : _root_.Layout]

/-- The skipping reader at its start (the label `start`). -/
structure StartS (f d : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout skipReader
  decls : s.decls = {}
  endPc : s.endPc = (layout skipReader).addrOf 8
  pc : s.st.2 = (layout skipReader).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = f
  x1 : s.st.1.regs.X1.toBitVec = d
  df : Mem.loadInt s.st.1.dmem f 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none

/-- **`NPSafeP` for the skipping reader** (frame `K2Scope AllocIds`): at the
initial configuration, for any initial resource `r` and ghost `g` with the
flag's release predicate `skipPred`, `Dt` pure, no pending mark, and an
acquire id `ι` of `Fl` held by the reader with predicate `skipPred`. -/
theorem skipReader_npSafeP [Executable.ValidLayout (layout skipReader)] (P : Params) {tid : Nat}
    {ss : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    (hS : StartS P.f P.d s) {r : Res} {g : Ghost} (hpend : g.pend = []) (hrel : g.rel P.Fl = skipPred P)
    (hd : ∀ v, Pred.Pure (g.rel P.Dt) v) {ι : PredId} (hι : ι < g.acqTab.length) (hacq : r.acq P.Fl ι = 1)
    (hp : g.acqPred ι = skipPred P) (n m : Nat) :
    NPSafeP (model isa) Arch.armv8 (SPost P tid) tid G₀ (K2Scope (model isa) AllocIds) n m True
      (Config.init ss initMem) r g := by
  letI : CodeEnv := ⟨layout skipReader⟩
  refine npSafeP_of_safelyEnvGTU (e := layout skipReader) (post := postS P) rdPlan_valid skipReader_rmwLive
    skipReader_phase1 postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_S P tid) n m
    (invGTU_init hs hpend (qa64TU_of_partialTripleEnv (skipReader_envGTU P tid).uncount rfl hS.exe hS.decls
      hS.endPc hS.pc ⟨0, hS.x0, hS.x1, hS.df, hS.dd, hrel, hd, ?_, ι, hι, Nat.le_of_eq hacq.symm, hp⟩))
  simp [σInit, Views.getFwd]

end Start

end Kraken.Promising.SLR.EnvG.TakeUSkip

#print axioms Kraken.Promising.SLR.EnvG.TakeUSkip.skipReader_npSafeP
#print axioms Kraken.Promising.SLR.EnvG.TakeUSkip.skipRuleR_noFault
