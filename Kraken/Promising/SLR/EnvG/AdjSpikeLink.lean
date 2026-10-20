/-
Part 2: **the per-tree link of the
sibling environment `EnvGCAdj`** (`EnvG/AdjCore.lean`: `EnvGC` whose release
obligation assumes own-message adjacency `AdjAt`), with failing in-flight
release RMWs (F × C). ISA-neutral.

The transports `NodeRel.rmwCAdj'`/`NodeRel.rmwRelCAdj` to
`EnvG/RmwGhostLink.lean` and `nodeSimS2F_envGCAdj` to
`EnvG/RmwFailGhostLink.lean` (same names and statements), where the `EnvGC`
versions are now their instances.

Contents: `treeJ_envGCAdj_eraseWPRDSF(_start)`.
-/
import Kraken.Promising.SLR.EnvG.AdjSpike

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **Link theorem 1 for `EnvGC` with failing in-flight RMWs** (as
`treeJ_envGC_eraseWPRDSR`, with `RokF` and `PostSF`). -/
theorem treeJ_envGCAdj_eraseWPRDSF {rS : Res} {gS : Ghost} {pf : Option (Loc × Val)} (hst : StartS tid c t gS pf)
    {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDS2 (nodeSimS2F_envGCAdj (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀)
      (g₀ := g₀) (cl₀ := cl₀) (rS := rS) hst) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokF pf) (LokS pf) tree) :
    tree.EraseWPRD A tid iv rF (fun _ => True) c t
      (PostOf (E := EnvGCAdj I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostSF tid pl iv c t rv₀ g₀ cl₀ pf rS gS σ' r' g' cx')) rS gS cx :=
  treeJ_eraseWPRDS2 _ hW ⟨h, rfl, rfl⟩ ha

/-- **Link theorem 1 for `EnvGC` with failing in-flight RMWs at an
instruction's start.** -/
theorem treeJ_envGCAdj_eraseWPRDSF_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) {pf : Option (Loc × Val)}
    (hst : StartS tid c t g pf)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDS2 (nodeSimS2F_envGCAdj (A := A) (pl := pl) (iv := instrViews t d) (rF := rF)
      (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hst) Q).W tree σ)
    (ha : SingleAccessS2 (LokS pf) (SokS pf) (RokF pf) (LokS pf) tree) :
    tree.EraseWPRD A tid (instrViews t d) rF (fun _ => True) c t
      (PostOf (E := EnvGCAdj I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostSF tid pl (instrViews t d) c t σ.r g cl pf r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envGCAdj_eraseWPRDSF hst hW (hrel.toNodeRel rF d E hm) ha

end Link

end Kraken.Promising.SLR.EnvG
