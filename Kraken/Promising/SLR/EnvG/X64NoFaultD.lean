/-
**No fault at the runner's declarations (`decls = ds`)**. Generic, x64.

`X64VecDeclsFault` reads a thread with strict sized declarations `ds` as its
`decls = {}` thread with every access `ds` does not resolve to its own
footprint turned into a fault (`exec_underDecls`). Safety transfers (a fault
is a `W` law), but no-fault does not: the `_noFault` rules
(`noFaultRule…_struct` with `DirsNoFaultCode`) are at `decls = {}`.

The missing fact is dynamic for code that accesses memory through
registers, which is almost all of the corpus (`movl $1,(%rsi)`), so a
per-directive static check against `ds` (`CellsDeclsAgree`) fails. But every
`QX64MD` invariant already carries it: its `Safely` judgment is over
`E.within S`, whose `ok` asks that **every access be exactly a location of
`S`** (`SharedEnv.AccessIn`). So the root access of every tree a `QX64MD`
thread runs is an `S`-location (`exec_rootInS`, through the x64 run lemma
`exec_treeJLive_of_instrStepEnv` with the judgment `rootInJ`), and for the
phase-1 single-access trees (`RootOnlyD`, from `SingleAccessS(2)`) that is
every access. If `ds` resolves each `S`-location to itself
(`Decls.AgreesOn ds S`, a static fact about the runner's declarations and
the proof's layout), re-resolving against `ds` changes nothing and the tree
is fault-free whenever its `decls = {}` tree is (`noFault_underDecls_rootD`).

- `EvTree.RootInS S t`, `EvTree.RootOnlyD t`, `SharedEnv.FenceTotal E`
  (every EnvG variant: `FenceOut` is a function);
- `rootInJ`: the live judgment of `E.within S` whose `W` is `RootInS S`;
- `noFault_underDecls_rootD`;
- **`noFault_QX64MD_rootD`**: the `HS` argument of the `noFaultRule…_struct`
  lemmas at `QX64MD ds`, for `Decls.AgreesOn ds S`, `DirsNoFaultCode e` and a
  single-access mask.
- The same-location generalisation (moved here from
  `EnvG/X64NoFaultDMpIncl.lean`, same names): `EvTree.AtLocD`,
  `EvTree.RootSameD`, `noFault_underDecls_rootSameD`,
  `noFault_QX64MD_rootSameD`. The single-access forms above are their
  instances (`rootSameD_of_rootOnlyD`).

The ISA-neutral part (`Decls.AgreesOn`, `EvTree.RootInS`,
`EvTree.RootOnlyD`, `accessFree_mapD`, `rootOnlyD_map`,
`rootOnlyD_of_singleAccessS(2)`, `atLocD_of_accessFree`,
`rootSameD_of_rootOnlyD`) moved, same names, to `EnvG/NoFaultDCommon.lean`,
which AArch64 shares; `noFault_underDecls_accessFreeD`,
`noFault_underDecls_atLocD` and `noFault_underDecls_rootSameD` are instances
of its generic `reresolve` forms.

Phase-1 limit: single-access trees (`RootOnlyD`). A multi-access tree's
later accesses sit behind environment answers, about which `Safely` says
nothing on unanswered values, while `EvTree.NoFault` is structural.
-/
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64NoFaultDSame
import Kraken.Promising.SLR.EnvG.NoFaultDCommon

namespace Kraken.SharedEnv

/-- **Every fence has an outcome** (the EnvG variants: `FenceOut` is a
function of the state). -/
def FenceTotal (E : SharedEnv) : Prop := ∀ (k : FenceKind) (g : E.State), ∃ g', E.step (.fence k) g () g'

end Kraken.SharedEnv

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {σ : Type}

/-- **The judgment "root accesses in `S`"** of `E.within S`. -/
def rootInJ (E : SharedEnv) (S : SharedEnv.Layout) (hft : E.FenceTotal) : TreeJLive (E.within S) σ where
  W t _ := t.RootInS S
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose h := fun i => h i
  load h₁ _ := h₁.2
  store h₁ _ := h₁.2
  rmw h₁ _ := h₁.2
  fence {k _ g} _ h₂ := by
    obtain ⟨g', hg⟩ := hft k g
    exact h₂ g' hg

/-- An access-free fault-free tree stays fault-free re-resolved
(`NoFaultDCommon.noFault_reresolve_accessFree`). -/
theorem noFault_underDecls_accessFreeD (ds : Decls) :
    ∀ t : EvTree σ, AccessFree t → t.NoFault → (t.underDecls ds).NoFault :=
  noFault_reresolve_accessFree ds

theorem atLocD_map {τ : Type} (f : σ → τ) (l : Loc) : ∀ t : EvTree σ, t.AtLocD l → (t.map f).AtLocD l
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => atLocD_map f l (k i) (h i)
  | .fence _ ret, h => atLocD_map f l (ret ()) h
  | .load _ _ _ ret, h => ⟨h.1, fun v => atLocD_map f l (ret v) (h.2 v)⟩
  | .store _ _ _ _ ret, h => ⟨h.1, fun b => atLocD_map f l (ret b) (h.2 b)⟩
  | .rmw _ _ _ _ ret, h => ⟨h.1, fun v => atLocD_map f l (ret v) (h.2 v)⟩

theorem rootSameD_map {τ : Type} (f : σ → τ) : ∀ t : EvTree σ, t.RootSameD → (t.map f).RootSameD
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => rootSameD_map f (k i) (h i)
  | .fence _ ret, h => rootSameD_map f (ret ()) h
  | .load _ _ l ret, h => fun v => atLocD_map f l (ret v) (h v)
  | .store _ _ l _ ret, h => fun b => atLocD_map f l (ret b) (h b)
  | .rmw _ _ l _ ret, h => fun v => atLocD_map f l (ret v) (h v)

/-- A fault-free tree all of whose accesses are at an agreeing location
stays fault-free re-resolved (`NoFaultDCommon.noFault_reresolve_atLocD`). -/
theorem noFault_underDecls_atLocD {ds : Decls} {l : Loc} (hl : ds.AgreesAt l.addr l.bytes) :
    ∀ t : EvTree σ, t.AtLocD l → t.NoFault → (t.underDecls ds).NoFault :=
  noFault_reresolve_atLocD hl

/-- **`noFault_underDecls_rootD` for trees whose later accesses repeat the
root's location** (`NoFaultDCommon.noFault_reresolve_rootSameD`). -/
theorem noFault_underDecls_rootSameD {ds : Decls} {S : SharedEnv.Layout} (hag : ds.AgreesOn S) :
    ∀ t : EvTree σ, t.RootInS S → t.RootSameD → t.NoFault → (t.underDecls ds).NoFault :=
  noFault_reresolve_rootSameD hag

/-- **A fault-free single-access tree whose root accesses are `S`-locations
stays fault-free re-resolved against declarations agreeing on `S`**
(`noFault_underDecls_rootSameD` through `rootSameD_of_rootOnlyD`). -/
theorem noFault_underDecls_rootD {ds : Decls} {S : SharedEnv.Layout} (hag : ds.AgreesOn S)
    (t : EvTree σ) (hi : t.RootInS S) (ho : t.RootOnlyD) (h : t.NoFault) : (t.underDecls ds).NoFault :=
  noFault_underDecls_rootSameD hag t hi (rootSameD_of_rootOnlyD t ho) h

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {ds : Decls} {E : SharedEnv} {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive} {endPc : Int64}
  {post : MachineState × E.State → Prop}

/-- **`noFault_QX64MD_rootD` for a mask whose trees repeat the root's
location** (`RootSameD` in place of `RootOnlyD`). -/
theorem noFault_QX64MD_rootSameD [Kraken.Executable.ValidLayout e] (hag : ds.AgreesOn S) (hft : E.FenceTotal)
    (hm : MaskOf e e') (hS : Le16 S) (hnf : DirsNoFaultCode e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hro : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootSameD) :
    ∀ st σ tree, QX64MD ds E S e e' endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, hs, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · have hR' := (instrStepEnv_of_mask hm hR).1
    rw [exec_underDecls] at hex
    obtain ⟨t₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hex
    refine (EvTree.noFault_map _ _).mpr ?_
    have hnf₀ := noFault_of_exec_step (st := st.noDecls) he rfl hnf hR' t₀ h₀
    have hin : t₀.RootInS S :=
      exec_treeJLive_of_instrStepEnv (rootInJ E S hft) (within_fit E S) hS (st := st.noDecls) he rfl hs hR'
        (fun _ _ _ _ => trivial) t₀ h₀
    obtain ⟨tree', hex', rfl⟩ :=
      QX64M.tree hm hpost (⟨he, rfl, hend, hs, hsafe⟩ : QX64M E S e e' endPc post st.noDecls σ) h₀
    rw [hds]
    exact noFault_underDecls_rootSameD hag _ hin (rootSameD_map _ _ (hro _ rfl rfl _ hex')) hnf₀

/-- **Every tree from a `QX64MD`-state is fault-free**, for declarations that
agree on the layout, fault-free non-data cells and a single-access mask
(`noFault_QX64MD_rootSameD` through `rootSameD_of_rootOnlyD`). -/
theorem noFault_QX64MD_rootD [Kraken.Executable.ValidLayout e] (hag : ds.AgreesOn S) (hft : E.FenceTotal)
    (hm : MaskOf e e') (hS : Le16 S) (hnf : DirsNoFaultCode e) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hro : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyD) :
    ∀ st σ tree, QX64MD ds E S e e' endPc post st σ → isa.exec st = some tree → tree.NoFault :=
  noFault_QX64MD_rootSameD hag hft hm hS hnf hpost fun st he hd tree hex =>
    rootSameD_of_rootOnlyD tree (hro st he hd tree hex)

end Kraken.Promising.X64.EnvG

/-! ## The link families at `decls = ds`

Each `…XMD` rule constructor of `X64DeclsLink` excludes faults when its
declarations agree on its layout: the family's `noFault…_struct` at
`noFault_QX64MD_rootD`, the single-access shape read off the family's
phase-1 hypothesis. -/

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

section Families

variable {ds : Decls} {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop} {rel₀ : Loc → Pred}
  {B : Config isa → (model isa).R → (model isa).Ghost → Prop}

theorem rootOnlyD_of_phase1TreeX (hshape : Phase1TreeX A e') :
    ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyD :=
  fun st he hd tree hex => rootOnlyD_of_singleAccessS _ (hshape st he hd tree hex).2

theorem rootOnlyD_of_phase1TreeRX (hshape : Phase1TreeRX A e') :
    ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyD :=
  fun st he hd tree hex => rootOnlyD_of_singleAccessS2 _ (hshape st he hd tree hex).2

theorem rootOnlyD_of_phase1TreeFX (hshape : Phase1TreeFX e') :
    ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyD :=
  fun st he hd tree hex => rootOnlyD_of_singleAccessS2 _ (hshape st he hd tree hex).2

/-- **No fault for `ofSafelyEnvGXMD`** (plain `EnvG`). -/
theorem noFaultRule_ofSafelyEnvGXMD_rootD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeX A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) (hag : ds.AgreesOn S) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGXMD hsz hm hpl hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvG_struct _ _ (noFault_QX64MD_rootD (E := Kraken.Promising.SLR.EnvG isa A tid pl) hag
    (fun _ _ => ⟨_, rfl⟩) hm hS hnf hpost (rootOnlyD_of_phase1TreeX hshape))

/-- **No fault for `ofSafelyEnvGRXMD`** (release-kind RMWs). -/
theorem noFaultRule_ofSafelyEnvGRXMD_rootD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeRX A e') (hG : RelRmwGiveOk isa pl rel₀) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) (hag : ds.AgreesOn S) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGRXMD hsz hm hpl hS hshape hG hpost hstuck hB) :=
  noFaultRule_ofEnvGR_structX _ _ fun st σ tree hQ hex =>
    noFault_QX64MD_rootD (E := Kraken.Promising.SLR.EnvG isa A tid pl) hag (fun _ _ => ⟨_, rfl⟩) hm hS hnf hpost
      (rootOnlyD_of_phase1TreeRX hshape) st σ tree hQ.1 hex

/-- **No fault for `ofSafelyEnvGFXMD`** (failing release RMWs). -/
theorem noFaultRuleF_ofSafelyEnvGFXMD_rootD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeFX e') (hG : RelRmwGiveOk isa pl rel₀) (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) (hag : ds.AgreesOn S) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFXMD hsz hm hpl hS hshape hG hpost hstuck hB) :=
  noFaultRuleF_ofEnvGF_struct _ _ fun st σ tree hQ hex =>
    noFault_QX64MD_rootD (E := Kraken.Promising.SLR.EnvG isa A tid pl) hag (fun _ _ => ⟨_, rfl⟩) hm hS hnf hpost
      (rootOnlyD_of_phase1TreeFX hshape) st σ tree hQ.1 hex

/-- **No fault for `ofSafelyEnvGFCXMD`** (claim-conditional RMWs). -/
theorem noFaultRuleF_ofSafelyEnvGFCXMD_rootD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeFX e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) (hag : ds.AgreesOn S) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFCXMD hsz hm hpl hS hshape hpost hstuck hB) :=
  noFaultRuleF_ofEnvGFC_struct _ _ (noFault_QX64MD_rootD (E := Kraken.Promising.SLR.EnvGC isa A tid pl) hag
    (fun _ _ => ⟨_, rfl⟩) hm hS hnf hpost (rootOnlyD_of_phase1TreeFX hshape))

/-- **No fault for `ofSafelyEnvGFCAdjXMD`** (adjacency ghost). -/
theorem noFaultRuleF_ofSafelyEnvGFCAdjXMD_rootD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid)
    (hS : Le16 S) (hshape : Phase1TreeFX e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGCAdjX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) (hag : ds.AgreesOn S) :
    NoFaultRuleF (ThreadRuleRXF.ofSafelyEnvGFCAdjXMD hsz hm hpl hS hshape hpost hstuck hB) :=
  noFaultRuleF_ofEnvGFCAdj_struct _ _ (noFault_QX64MD_rootD (E := Kraken.Promising.SLR.EnvGCAdj isa A tid pl) hag
    (fun _ _ => ⟨_, rfl⟩) hm hS hnf hpost (rootOnlyD_of_phase1TreeFX hshape))

/-- **No fault for `ofSafelyEnvGTXMD`** (take route). -/
theorem noFaultRule_ofSafelyEnvGTXMD_rootD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeX A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) (hag : ds.AgreesOn S) :
    NoFaultRuleSX (ThreadRuleRXGS.ofSafelyEnvGTXMD hsz hm hpl hS hshape hpost hstuck hB) :=
  NoFaultRuleSX.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp
    exact noFault_QX64MD_rootD (E := Kraken.Promising.SLR.EnvGT isa A tid pl) hag (fun _ _ => ⟨_, rfl⟩) hm hS hnf
      hpost (rootOnlyD_of_phase1TreeX hshape) t.st σ tree hQ hex

/-- **No fault for `ofSafelyEnvGTRCXMD`** (take route, claim-conditional
RMW). -/
theorem noFaultRule_ofSafelyEnvGTRCXMD_rootD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid) (hS : Le16 S)
    (hshape : Phase1TreeRX A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGTCX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) (hag : ds.AgreesOn S) :
    NoFaultRuleSX (ThreadRuleRXGS.ofSafelyEnvGTRCXMD hsz hm hpl hS hshape hpost hstuck hB) :=
  NoFaultRuleSX.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGR.q_atX rF t h he hg ht E hnp
    exact noFault_QX64MD_rootD (E := EnvGTCI isa A tid pl) hag (fun _ _ => ⟨_, rfl⟩) hm hS hnf hpost
      (rootOnlyD_of_phase1TreeRX hshape) t.st σ tree hQ hex

end Families

end Kraken.Promising.X64.EnvG

set_option hygiene false in
/-- `decls_agrees_on` proves a concrete `Decls.AgreesOn ds S` (a literal
layout and declarations, symbol addresses rewritten to numerals first): one
`rfl` per location of `S`. -/
macro "decls_agrees_on" : tactic => `(tactic| (
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' (rcases hp with rfl | hp)
  all_goals rfl))
