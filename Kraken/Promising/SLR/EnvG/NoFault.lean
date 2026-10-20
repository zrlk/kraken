/-
Whole-thread environment (`EnvG`): the **no-fault track** for
`EnvG`. ISA-neutral.

The abstract no-fault link (`TreeLink.lean`: `NodeSimNF`) asks the
environment to answer every actual outcome of an access with a related
state; `EnvG` cannot, since `StoreOut`/`RmwOut` offer no outcome that
overtakes an own promise. This file uses a weaker requirement: after the
single access the tree is access-free, and whether an access-free tree can
fault does not depend on the context (`FaultFreeAF.noFaultRun`). So an
actual write outcome needs only *some* env step with the same return value,
related to nothing.

- `FaultFreeAF`: no fault leaf on any path of an access-free tree.
- `EnvGAnswers` (**the missing fact**, stated as a `Prop`): at a
  `NodeRel`-related state, a permitted store (RMW) with an actual write
  outcome has some env write outcome (returning the same value).
- `envGAnswers_of_promFree`: the fact holds for a thread without outstanding
  promises (the env's counterpart of the actual write overtakes nothing).
- `TreeJLiveNF.envG`, `treeJ_envG_noFaultRun`: no faulting run from every
  `NodeRel`-related context, for a single-access tree, under `EnvGAnswers`.
-/
import Kraken.Promising.SLR.EnvG.Link

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-! ## Access-free trees fault independently of the context -/

/-- No fault leaf on any path (meant for access-free trees; the access nodes
are not inspected). Unlike `EvTree.NoFault`, a `choose` may be empty. -/
def FaultFreeAF {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => False
  | .choose _ k => ∀ i, FaultFreeAF (k i)
  | .fence _ ret => FaultFreeAF (ret ())
  | .load .. => True
  | .store .. => True
  | .rmw .. => True

/-- An access-free tree with no fault leaf has no faulting run, from any
context. -/
theorem FaultFreeAF.noFaultRun (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} {tree : EvTree σ}
    (ha : AccessFree tree) (hf : FaultFreeAF tree) : ∀ cx, tree.NoFaultRun A tid iv cx := by
  induction tree with
  | done _ => intro cx m hm; simp [runTree] at hm
  | fault _ => exact hf.elim
  | choose n k ih =>
    intro cx m hm
    simp only [runTree, List.mem_flatMap] at hm
    obtain ⟨i, -, hi⟩ := hm
    exact ih i (ha i) (hf i) cx m hi
  | fence k ret ih =>
    intro cx m hm
    simp only [runTree] at hm
    exact ih () ha hf _ m hm
  | load => exact ha.elim
  | store => exact ha.elim
  | rmw => exact ha.elim

/-! ## The missing fact -/

/-- **The missing fact of the no-fault track** (for the rule link and live trees). At a state
related to the actual context by `NodeRel` (actual context satisfying
`Ctx.Inv`), a permitted store with an actual write outcome has some env
outcome, and a permitted RMW whose actual read returns `old` and writes has
some env outcome returning `old`. (`EnvG` offers no write outcome that
overtakes an own promise; when every write the env could make overtakes
one, it has none.) Holds for a promise-free thread
(`envGAnswers_of_promFree`). Believed **false** for a thread with a pure own
non-pending promise `ts` at `l` whose next store writes another value to `l`
(every actual write overtakes `ts`). It is not needed for `NoFaultRule` on fault-free code:
see `noFaultRule_ofEnvG_struct` (`EnvG/Answers.lean`). -/
def EnvGAnswers (A : Arch) (tid : Nat) (pl : Plan) (iv : InstrViews) (rF : Nat → Res) (c : Config I)
    (t : Thread I) : Prop :=
  ∀ (rv₀ : Res) (g₀ : Ghost) (cl₀ : Prop) (σ : State I) (r : Res) (g : Ghost) (cx : Ctx),
    NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx → cx.Inv tid →
    (∀ (k : StoreKind) (l : Loc) (v : Val) (cx' : Ctx), StoreOk A tid pl σ k false l v →
      cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      ∃ σ', StoreOut A tid pl σ σ' k false l v true) ∧
    (∀ (k : RmwKind) (l : Loc) (op : Val → Option Val) (x : Time × Val × Ctx) (new : Val) (cx' : Ctx),
      RmwOk A tid pl σ k l op → x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false l false →
      op x.2.1 = some new →
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      ∃ σ', RmwOut A tid pl σ σ' k l op x.2.1)

/-- **`EnvGAnswers` for a promise-free thread**: the env's counterpart of the
actual write (`CtxLe.write`) has no promise to overtake. -/
theorem envGAnswers_of_promFree {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res}
    {c : Config I} {t : Thread I} (hp : t.prom = []) : EnvGAnswers A tid pl iv rF c t := by
  intro rv₀ g₀ cl₀ σ r g cx h hi
  have hnov : ∀ cxe : Ctx, cxe.prom = [] → ¬ cxe.Overtaken := fun cxe he ⟨p, hp', _⟩ => by
    rw [he] at hp'; exact absurd hp' List.not_mem_nil
  have hown : ownProm tid c = [] := by rw [ownProm_eq h.ht, hp]
  refine ⟨fun k l v cx' _ hc => ?_, fun k l op x new cx' _ hx hop hc => ?_⟩
  · obtain ⟨cxe₂, tw, hc', -, hev', hcl⟩ := h.ctx.write (A := A) hi (ivLe_envIv _ (iv.forStore cx.stores))
      (h.ctx.sim.ivb.forStore cx.stores) (Nat.le_refl 0) (Nat.zero_le _) hc
    have hpe : cxe₂.prom = [] := by
      rw [hev'.prom]; simp only [envCtx_prom, hown, List.erase_nil]
    exact ⟨storeState pl σ tid c g l v tw σ.cl cxe₂, rfl, rfl, c, cxe₂, tw, h.anchorOk, hc', hev', hnov _ hpe,
      fun _ => .inl (by rw [hown]; exact List.not_mem_nil), rfl, rfl, ⟨σ.cl, id, rfl⟩, rfl, rfl, rfl, rfl⟩
  · obtain ⟨tr, old, cx₁⟩ := x
    obtain ⟨cxe₁, hx', hc1⟩ := (h.ctx.fenceOpt (A := A)).read hx
    have hi1 : cx₁.Inv tid := (readSuccs_inv A tid iv hx (fenceOpt_inv tid hi A.rmwFence .sy).1).1
    have hex : cxe₁.loadViews.getLastD 0 ≤ cx₁.loadViews.getLastD 0 :=
      Nat.le_trans (Rel2.getLastD hc1.sim.rel.loadViews 0 0 (Nat.zero_le _)) (idUpTo_fv_le _ _)
    obtain ⟨cxe₂, tw, hc', hev, hev', -⟩ :=
      hc1.write hi1 (ivLe_envIv _ iv) hc1.sim.ivb hex (getLastD_le' hc1.sim.bnd.loadViews) hc
    obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
    obtain ⟨hm0, hp0⟩ := fenceOptCtx_memProm (A := A) cx
    obtain ⟨-, -, hrd, hseen⟩ := rmw_event A tid iv hx hi hc
    have hun : ¬ g.Claimed (l, tr) :=
      ErAt.not_claimed_rmw (h.erAt.congr (hm1.trans hm0) (hp1.trans hp0)) (lt_size_of_get? h.ht) hi1 hev hrd
        hseen fun p hp' => absurd (hp1.trans (hp0.trans (h.prom.trans hp)) ▸ hp') List.not_mem_nil
    have hpe1 : cxe₁.prom = [] := by
      rw [(readSuccs_memProm A _ hx').2, (fenceOptCtx_memProm (A := A) _).2]
      simp only [envCtx_prom, hown]
    have hpe : cxe₂.prom = [] := by rw [hev'.prom, hpe1, List.erase_nil]
    exact ⟨{ σ with
        snap := snapAfter tid c cxe₂, vs := (rmwAfter A k false l cxe₂).views
        r := pl.afterRmw l new tr tw g σ.cl σ.r, g := g
        seen := seenAfter A (A.rmwKind k).loadKind σ g l tr, fencedR := false, fencedW := false },
      c, (tr, old, cxe₁), h.anchorOk, hx', rfl, rfl, rfl, rfl, rfl,
      .inr ⟨new, cxe₂, tw, hop, hc', hev', hnov _ hpe, fun _ => .inl (by rw [hown]; exact List.not_mem_nil),
        rfl, rfl, ⟨σ.cl, id, rfl⟩, hun⟩⟩

/-! ## The no-fault judgment and link -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **No faulting run is a no-fault live judgment of `EnvG`** (a judgment
with no `fault` law), under `EnvGAnswers`: `W tree σ` says that a
single-access tree has no faulting run from any `NodeRel`-related context,
and an access-free tree has no fault leaf. -/
def TreeJLiveNF.envG (hans : EnvGAnswers A tid pl iv rF c t) (σT : Type) : TreeJLiveNF (EnvG I A tid pl) σT where
  W tree s :=
    (∀ r g cx, NodeRel tid pl iv rF c t rv₀ g₀ cl₀ s r g cx → cx.Inv tid → SingleAccess tree →
      tree.NoFaultRun A tid iv cx) ∧
    (AccessFree tree → FaultFreeAF tree)
  Post _ _ := True
  done _ := ⟨fun _ _ _ _ _ _ m hm => by simp [runTree] at hm, fun _ => trivial⟩
  choose h := by
    refine ⟨fun r g cx hp hi ha m hm => ?_, fun ha i => (h i).2 (ha i)⟩
    simp only [runTree, List.mem_flatMap] at hm
    obtain ⟨i, -, hm⟩ := hm
    exact (h i).1 r g cx hp hi (ha i) m hm
  fence := by
    intro k ret s _ h
    refine ⟨fun r g cx hp hi ha m hm => ?_, fun ha => (h _ (fenceOut_fenceState s k)).2 ha⟩
    simp only [runTree] at hm
    exact (h _ (fenceOut_fenceState s k)).1 r g _ (hp.fence k) (fenceStep_inv tid hi k).1 ha m hm
  load := by
    intro k xcl addr n ret s _ h
    refine ⟨fun r g cx hp _ ha m hm => ?_, fun ha => ha.elim⟩
    simp only [runTree, List.mem_flatMap] at hm
    obtain ⟨x, hx, hm⟩ := hm
    obtain ⟨σ', hst, -⟩ := hp.load hx
    exact FaultFreeAF.noFaultRun A tid iv (ha _) ((h _ σ' hst).2 (ha _)) _ m hm
  store := by
    intro k xcl addr n v ret s hok h
    refine ⟨fun r g cx hp hi ha m hm => ?_, fun ha => ha.elim⟩
    obtain rfl : xcl = false := hok.1
    simp only [runTree, List.mem_append] at hm
    rcases hm with hm | hm
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at hm
      obtain ⟨-, c', hc, hm⟩ := hm
      simp only [Bool.false_eq_true, ↓reduceIte] at hc
      obtain ⟨σ', hst⟩ := (hans rv₀ g₀ cl₀ s r g cx hp hi).1 k _ v c' hok hc
      exact FaultFreeAF.noFaultRun A tid iv (ha true) ((h true σ' hst).2 (ha true)) _ m hm
    · rw [List.mem_ite_nil_right] at hm
      exact absurd hm.1 Bool.false_ne_true
  rmw := by
    intro k addr n op ret s hok h
    refine ⟨fun r g cx hp hi ha m hm => ?_, fun ha => ha.elim⟩
    simp only [runTree] at hm
    change (.error m : Except String _) ∈ (readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false
      ⟨addr, n⟩ false).flatMap _ at hm
    rw [List.mem_flatMap] at hm
    obtain ⟨x, hx, hm⟩ := hm
    obtain ⟨tr, old, c3⟩ := x
    simp only at hm
    split at hm
    · next hop =>
      obtain ⟨σ', hst, -⟩ := hp.rmwFail (op := op) hx hop
      exact FaultFreeAF.noFaultRun A tid iv (ha _) ((h _ σ' hst).2 (ha _)) _ m hm
    · next new hop =>
      rw [List.mem_flatMap] at hm
      obtain ⟨c4, hc4, hm⟩ := hm
      obtain ⟨σ', hst⟩ := (hans rv₀ g₀ cl₀ s r g cx hp hi).2 k _ op (tr, old, c3) new c4 hok hx hop hc4
      exact FaultFreeAF.noFaultRun A tid iv (ha _) ((h _ σ' hst).2 (ha _)) _ m hm

/-- **The no-fault link for `EnvG`**: under `EnvGAnswers`, a no-fault live
judgment of the tree (`TreeJLiveNF.envG`) gives no faulting run from every
`NodeRel`-related context satisfying `Ctx.Inv` (at an instruction's start:
`EnvRel.toNodeRel` and `Thread.Inv.ctx`), for a single-access tree. -/
theorem treeJ_envG_noFaultRun (hans : EnvGAnswers A tid pl iv rF c t) {σT : Type} {tree : EvTree σT}
    {σ : State I} (hW : (TreeJLiveNF.envG (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀) hans σT).W tree σ) {r : Res}
    {g : Ghost} {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ r g cx) (hi : cx.Inv tid)
    (ha : SingleAccess tree) : tree.NoFaultRun A tid iv cx :=
  hW.1 r g cx h hi ha

end Link

end Kraken.Promising.SLR.EnvG
