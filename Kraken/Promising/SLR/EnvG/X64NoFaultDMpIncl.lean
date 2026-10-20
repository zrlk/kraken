/-
**No fault at the runner's declarations for `mp_incl.kl`'s writer**
The same-location generalisation of
`X64NoFaultD`.

`noFault_QX64MD_rootD` covers single-access trees: the `Safely` judgment
over `E.within S` pins the root access to an `S`-location, but says nothing
about accesses behind an environment answer, since an unanswered value is
not covered while `EvTree.NoFault` is structural. The writer's
`incl (%rdi)` (not `lock`ed) is a load and then a store, a multi-access
tree. Both accesses are at the same location, `⟨rdi, 4⟩`, which a static
per-cell check sees (`EvTree.RootSameD`). The later access is then at the
root's location, which is an `S`-location.

- `EvTree.AtLocD l t` (every access of `t` at `l`) and `EvTree.RootSameD t`
  (every access after the root access at the root's location);
  `noFault_underDecls_rootSameD`, **`noFault_QX64MD_rootSameD`** (moved these,
  with `atLocD_map`, `rootSameD_map` and
  `noFault_underDecls_atLocD`, to `EnvG/X64NoFaultD.lean`, same names: the
  single-access forms there are now their instances);
- `DirsRootSameX`, `rootSameTreeX_of_dirs`, the tactic `cells_root_same`;
- `noFaultRule_ofSafelyEnvGLRVXMD_rootSameD` (the `EnvGLRV` family);
- `x64_mp_incl_envGV_runner_noFault` (writer and reader) and its
  `_concrete` instance.
-/
import Kraken.Promising.SLR.EnvG.X64NoFaultDMp

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The per-cell check -/

/-- Every tree of the directive `d` at `z` in `e` repeats its root's
location. -/
def DirRootSameX (e : _root_.Executable) (d : Directive) (z : Nat) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    (toEv {} (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc')))).RootSameD

/-- From the cells to the trees (`tree_of_codeAt`). -/
theorem rootSameTreeX_of_dirs {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (h : ∀ d z, (d, z) ∈ e.2 → DirRootSameX e d z) :
    ∀ st : State, st.exe = e → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootSameD :=
  fun _ he hds _ htree => tree_of_codeAt (Φ := fun t => EvTree.RootSameD t)
    (fun f t ht => rootSameD_map f t ht) (fun d z hm => h d z hm) he hds htree

/-- The directives of a laid-out program (`dirsLRX_layout`). -/
theorem dirsRootSameX_layout [layout : _root_.Layout] {p : Program}
    (h : ∀ d ∈ p, ∀ (e : _root_.Executable) z, DirRootSameX e d z) :
    ∀ d z, (d, z) ∈ (layout p).2 → DirRootSameX (layout p) d z := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _

set_option hygiene false in
/-- `cells_root_same p hd` proves `RootSameD` of every cell of a member `hd`
of the program `p` (the `cells_lrX` unfolding). -/
macro "cells_root_same " p:ident hd:ident : tactic => `(tactic| (
  simp only [$p:ident, List.mem_cons, List.not_mem_nil, or_false] at $hd:ident
  repeat' (rcases $hd:ident with rfl | $hd:ident)
  all_goals simp only [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    _root_.MachineData.load, _root_.MachineData.store, _root_.MachineData.rmwPlain,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, _root_.RelRegOrMem.interp]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.RootSameD, Kraken.Promising.EvTree.AtLocD,
      Kraken.Promising.EvTree.access_empty]))))

/-! ## The `EnvGLRV` family -/

section Families

variable {ds : Decls} {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive}
  [Kraken.Executable.ValidLayout e] {endPc : Int64} {post : MachineState × EStateX → Prop}
  {B : Config isa → (model isa).R → (model isa).Ghost → Prop}

/-- **No fault for `ofSafelyEnvGLRVXMD`**, for a mask whose trees repeat
their root's location. -/
theorem noFaultRule_ofSafelyEnvGLRVXMD_rootSameD (hsz : ds.Sized) (hm : MaskOf e e') (hpl : pl.Valid)
    (hwhole : ∀ e ∈ pl.entries, e.split = none) (hS : Le16 S)
    (hshape : LRTreeX A e') (hpost : ∀ y, post y → y.1.2 = endPc)
    (hstuck : ∀ x R, x.1.2 = endPc → ¬ e'.instrStepEnv (EnvGLRVX A tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g)
    (hnf : DirsNoFaultCode e) (hag : ds.AgreesOn S)
    (hsame : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootSameD) :
    NoFaultRule (ThreadRuleRX.ofSafelyEnvGLRVXMD hsz hm hpl hwhole hS hshape hpost hstuck hB) :=
  noFaultRule_ofEnvGLRV_struct _ _ (noFault_QX64MD_rootSameD (E := Kraken.Promising.SLR.EnvGLRV isa A tid pl) hag
    (fun _ _ => ⟨_, rfl⟩) hm hS hnf hpost hsame)

end Families

end Kraken.Promising.X64.EnvG

/-! ## `mp_incl.kl` -/

namespace Kraken.Promising.X64.EnvG.MpInclAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic
open Kraken.Promising.X64.EnvG.MpInc Kraken.Promising.X64.EnvG.MpIncV

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpInclImageV)]

omit layout [Executable.ValidLayout (layout mpInclImageV)] in
/-- The writer's cells repeat their root's location (`incl` loads and
stores `⟨rdi, 4⟩`). -/
theorem writerFragV_rootSame : ∀ d ∈ writerFragV, ∀ (e : _root_.Executable) z, DirRootSameX e d z := by
  intro d hd e z s pc
  cells_root_same writerFragV hd

/-- **The writer's mask repeats its trees' root locations.** -/
theorem mpInclImageW_rootSame :
    ∀ st : State, st.exe = layout mpInclImageW → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootSameD := by
  haveI := mpInclImageW_valid (layout := layout)
  refine rootSameTreeX_of_dirs (dirsRootSameX_layout (mem_maskKeep_range
    (Φd := fun d => ∀ (e : _root_.Executable) z, DirRootSameX e d z) ?_ ?_ ?_))
  · rw [show (mpInclImageV.drop 0).take (5 - 0) = writerFragV by decide]
    exact writerFragV_rootSame
  · intro l e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, EvTree.RootSameD]
  · intro e z s pc
    simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, EvTree.RootSameD]

/-- **Both of `mp_incl.kl`'s rules at `decls = ds` exclude faults**
(`mpInclRuleWMD`, `mpInclRuleRMD`), for `ds` agreeing on `f` and `d`. -/
theorem x64_mp_incl_envGV_runner_noFault {ds : Decls} (hsz : ds.Sized) (P : Params) (hL : MpLocs P)
    (hag : ds.AgreesOn (mpS P)) (tW tR rd : Nat) :
    NoFaultRule (mpInclRuleWMD hsz P hL tW rd) ∧ NoFaultRule (mpInclRuleRMD hsz P hL tR) :=
  ⟨noFaultRule_ofSafelyEnvGLRVXMD_rootSameD _ _ _ _ _ _ _ _ _ mpInclImageV_noFaultCode hag mpInclImageW_rootSame,
    x64_mp_incl_reader_runner_noFault hsz P hL tR hag⟩

end Kraken.Promising.X64.EnvG.MpInclAbs

namespace Kraken.Promising.X64.EnvG.MpInclAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.MpInclAbs Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG.Mp
open Kraken.Promising.X64.EnvG.MpPublic

section
attribute [local instance] mpInclLayoutV

/-- **No fault for `mp_incl.kl`'s writer (thread 0) and reader (thread 1) at
the runner's declarations** (`mpInclDeclsD`). -/
theorem x64_mp_incl_envGV_runner_noFault_concrete (hL : MpLocs (ghostParams (symM "f") (symM "d"))) :
    NoFaultRule (mpInclRuleWMD mpInclDeclsD_sized (ghostParams (symM "f") (symM "d")) hL 0 1) ∧
      NoFaultRule (mpInclRuleRMD mpInclDeclsD_sized (ghostParams (symM "f") (symM "d")) hL 1) :=
  x64_mp_incl_envGV_runner_noFault mpInclDeclsD_sized _ hL (by
    show mpInclDeclsD.AgreesOn [(symM "f", 4), (symM "d", 4)]
    rw [symM_f, symM_d]; decls_agrees_on) 0 1 1

end

end Kraken.Promising.X64.EnvG.MpInclAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.Concrete.x64_mp_incl_envGV_runner_noFault_concrete
