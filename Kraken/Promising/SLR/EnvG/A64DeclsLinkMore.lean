/-
**More AArch64 rule links for threads with strict sized declarations**
. The D forms (`…MD`) of the three
link families the lock theorems use that `EnvG/A64DeclsLink.lean` does not
cover, built in the same way: `QA64MD ds E e e'` with the family's
environment `E`, `QA64MD.link` for the link and `QA64MD.shape` for the
phase-1 shape (closed under `EvTree.map` and `EvTree.reresolve`).

- **`EnvGC`, claim-conditional RMW** (`ThreadRuleRX.ofSafelyEnvGRC`,
  `EnvG/RmwGhostA64.lean`; `swpl_counter_envG`):
  `linkHypsRC_QA64MD`, `ThreadRuleRX.ofSafelyEnvGRCMD`, `invGRCMD_init`.
- **`EnvGTD`, the ticket environment** (`ThreadRuleRXGSXE.ofSafelyEnvGTD`,
  `EnvG/TicketA64Link.lean`; `ticket_counter_envG`):
  `linkHypsTD_QA64MD`, `ThreadRuleRXGSXE.ofSafelyEnvGTDMD`,
  `npSafeP_of_safelyEnvGTDMD`, `invGTDMD_init`.
- **`EnvGTDR`, the ticket environment with a release-kind ticket RMW**
  (`ThreadRuleRXGSXE.ofSafelyEnvGTDR`, `EnvG/TicketRA64Link.lean`;
  `ticket_al_counter_envG`): `linkHypsTDR_QA64MD`,
  `ThreadRuleRXGSXE.ofSafelyEnvGTDRMD`, `npSafeP_of_safelyEnvGTDRMD`,
  `invGTDRMD_init`.

Every D link takes `(hsz : ds.StrictSized)` and `(hnp : e.noPairs = true)`
and a mask `(hm : MaskOf e e')` (`MaskOf.refl` for the unmasked existing
links, whose invariants `QA64C`/`QA64TD`/`QA64TDR` are `QA64MD {}` at
`e' = e`). Not covered, as in `A64DeclsLink`: the no-fault side.
-/
import Kraken.Promising.SLR.EnvG.A64DeclsLink
import Kraken.Promising.SLR.EnvG.RmwGhostA64
import Kraken.Promising.SLR.EnvG.TicketA64Link
import Kraken.Promising.SLR.EnvG.TicketRA64Link

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

section Families

variable {ds : Decls} {A : Arch} {tid : Nat} {pl : Plan} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateA → Prop}

/-! ### `EnvGC`: the claim-conditional RMW (`RC`) -/

theorem linkHypsRC_QA64MD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsRC (I := isa) A tid pl (QA64MD ds (EnvGCA A tid pl) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1ShapeR A t) hnp hm hpost
    (fun f _ ht => phase1ShapeR_map f ht) (fun _ ht => phase1ShapeR_reresolve hsz ht) hshape h hex
  link J _ _ _ h hex hJ := QA64MD.link hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRX.ofSafelyEnvGRCMD`**: `ofSafelyEnvGRC` for a thread with
strict sized declarations `ds` (over a mask). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGRCMD
    {B : Config isa → (model isa).R → (model isa).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCA A tid pl) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid :=
  ThreadRuleRX.ofEnvGRC (linkHypsRC_QA64MD (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ hh) hp hrel hcl

omit [Kraken.Executable.ValidLayout e] in
theorem invGRCMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MD ds (EnvGCA A tid pl) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGR (I := isa) tid pl (QA64MD ds (EnvGCA A tid pl) e e' endPc post) True (Config.init ss m) r g :=
  ⟨σInit (Config.init ss m) r g, Thread.init s, coreAtR_init hs hpend, hQ⟩

/-! ### `EnvGTD`: the ticket environment -/

section TD

variable {D : Dispenser}

theorem linkHypsTD_QA64MD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTD (I := isa) A tid pl D (QA64MD ds (EnvGTDA A tid pl D) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1Shape A t) hnp hm hpost
    (fun f _ ht => phase1Shape_map f ht) (fun _ ht => phase1Shape_reresolve hsz ht) hshape h hex
  link J _ _ _ h hex hJ := QA64MD.link hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGSXE.ofSafelyEnvGTDMD`**: `ofSafelyEnvGTD` for a thread
with strict sized declarations `ds` (over a mask). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTDMD
    {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTDA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGSXE G₀ D.TX A B tid :=
  ThreadRuleRXGSXE.ofEnvGTD (linkHypsTD_QA64MD (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` from a `Safely` judgment of `EnvGTD` with declarations**
(`npSafeP_of_safelyEnvGTD` at `ofSafelyEnvGTDMD`). -/
theorem npSafeP_of_safelyEnvGTDMD {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1Tree A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTDA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGTD (I := isa) A tid pl D (QA64MD ds (EnvGTDA A tid pl D) e e' endPc post) cl c r g) :
    NPSafeP (modelX isa D.TX) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGSXE (ThreadRuleRXGSXE.ofSafelyEnvGTDMD hsz hnp hm hpl hlive hshape hpost hstuck hB) n m cl c r g h

omit [Kraken.Executable.ValidLayout e] in
theorem invGTDMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MD ds (EnvGTDA A tid pl D) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGTD (I := isa) A tid pl D (QA64MD ds (EnvGTDA A tid pl D) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAt_init hs hpend, hQ, fun _ => by simp [Thread.init, Views.getCoh]⟩

/-! ### `EnvGTDR`: the ticket environment with a release-kind ticket RMW -/

theorem linkHypsTDR_QA64MD (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e')
    (hpl : pl.Valid) (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc) :
    LinkHypsTDR (I := isa) A tid pl D (QA64MD ds (EnvGTDRA A tid pl D) e e' endPc post) where
  valid := hpl
  shape _ _ h _ hex := QA64MD.shape (Φ := fun t => Phase1ShapeR A t) hnp hm hpost
    (fun f _ ht => phase1ShapeR_map f ht) (fun _ ht => phase1ShapeR_reresolve hsz ht) hshape h hex
  link J _ _ _ h hex hJ := QA64MD.link hsz hnp hm hlive hpost J h hex hJ

/-- **`ThreadRuleRXGSXE.ofSafelyEnvGTDRMD`**: `ofSafelyEnvGTDR` for a thread
with strict sized declarations `ds` (over a mask). -/
def _root_.Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTDRMD
    {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTDRA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXGSXE G₀ D.TX A B tid :=
  ThreadRuleRXGSXE.ofEnvGTDR (linkHypsTDR_QA64MD (tid := tid) hsz hnp hm hpl hlive hshape hpost)
    fun c t r g cl σ hQ hh hp hrel hcl => hB c t r g cl σ (post_of_halted_QA64MD hm hstuck hQ hh) hp hrel hcl

/-- **`NPSafeP` from a `Safely` judgment of `EnvGTDR` with declarations**
(`npSafeP_of_safelyEnvGTDR` at `ofSafelyEnvGTDRMD`). -/
theorem npSafeP_of_safelyEnvGTDRMD {B : Config isa → (modelX isa D.TX).R → (modelX isa D.TX).Ghost → Prop}
    (hsz : ds.StrictSized) (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hpl : pl.Valid)
    (hlive : e.rmwLive = true) (hshape : Phase1TreeR A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTDRA A tid pl D) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvGTDR (I := isa) tid pl D (QA64MD ds (EnvGTDRA A tid pl D) e e' endPc post) cl c r g) :
    NPSafeP (modelX isa D.TX) A B tid G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGSXE (ThreadRuleRXGSXE.ofSafelyEnvGTDRMD hsz hnp hm hpl hlive hshape hpost hstuck hB)
    n m cl c r g h

omit [Kraken.Executable.ValidLayout e] in
theorem invGTDRMD_init {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    {r : Res} {g : Ghost} (hpend : g.pend = [])
    (hQ : QA64MD ds (EnvGTDRA A tid pl D) e e' endPc post s (σInit (Config.init ss m) r g)) :
    InvGTDR (I := isa) tid pl D (QA64MD ds (EnvGTDRA A tid pl D) e e' endPc post) True (Config.init ss m) r g :=
  ⟨_, _, coreAtR_init hs hpend, hQ, fun _ => by simp [Thread.init, Views.getCoh]⟩

end TD

end Families

end Kraken.Promising.AArch64.EnvG

#print axioms Kraken.Promising.SLR.ThreadRuleRX.ofSafelyEnvGRCMD
#print axioms Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTDMD
#print axioms Kraken.Promising.SLR.ThreadRuleRXGSXE.ofSafelyEnvGTDRMD
#print axioms Kraken.Promising.AArch64.EnvG.npSafeP_of_safelyEnvGTDMD
#print axioms Kraken.Promising.AArch64.EnvG.npSafeP_of_safelyEnvGTDRMD
