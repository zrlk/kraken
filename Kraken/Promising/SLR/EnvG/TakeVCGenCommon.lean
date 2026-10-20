/-
**`vcgen` over `EnvGT`, ISA-neutral part**.

- **`@[simp]` `ok`/`step`** at states typed `(EnvGT I A tid pl).State` (as
  `vcgen` goals carry them): `ok` is `EnvG`'s (`StoreOk`/`RmwOk`, trivial
  for loads and fences); a load step is `LoadOutT`, the others are
  `StoreOut`/`RmwOut`/`FenceOut`. So every `EnvG` store/RMW/fence fact
  (`step_storeFacts`, …) applies to an `EnvGT` goal after `simp`.
- **`SharedEnv.FenceMono (EnvGT I A tid pl)`** with `le = FenceLe`
  (`EnvG/VCGenCommon.lean`): fences are `EnvG`'s, so `fenceInv_fenceLe` is
  the proof; the per-ISA `envMono_lift_spec` (`@[spec 40]`, AArch64
  `EnvG/A64VCGen.lean`; x64 `envMonoX_lift_spec`, `EnvG/X64VCGen.lean`, whose
  class `SharedEnv.FenceMonoX` is an alias of `SharedEnv.FenceMono`) then
  runs silent instructions, also under `SharedEnv.counted`.
- `takeEff_of_not_acq`: a non-acquire load takes nothing (the resource and
  ghost of the anchor), the form a plain `ldr` VC uses.
- `takeEff_q_ge`, `takeEff_wr_fullG` (from the x64 ticket lock proof): a load, take
  or no take, only adds to the write permissions, and keeps a full one.

The x64 copies (`EnvG/TakeX64VCGen.lean`, `X` suffix) are aliases of these.

Phase-1 limits as `EnvG/TakeEnv.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeEnv
import Kraken.Promising.SLR.EnvG.Simp
import Kraken.Promising.SLR.EnvG.VCGenCommon
import Kraken.Promising.SLR.EnvG.TakeAllWr

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## `ok` and `step` -/

@[simp] theorem envGT_ok_load_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGT I A tid pl).State) (k : LoadKind)
    (xcl : Bool) (addr : BitVec 64) (n : Nat) : (EnvGT I A tid pl).ok (.load k xcl addr n) σ := trivial

@[simp] theorem envGT_ok_fence_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGT I A tid pl).State) (k : FenceKind) :
    (EnvGT I A tid pl).ok (.fence k) σ := trivial

@[simp] theorem envGT_ok_store (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGT I A tid pl).State) (k : StoreKind)
    (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGT I A tid pl).ok (.store k xcl addr n v) σ = StoreOk A tid pl σ k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGT_ok_rmw (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGT I A tid pl).State) (k : RmwKind)
    (addr : BitVec 64) (n : Nat) (op : Val → Option Val) :
    (EnvGT I A tid pl).ok (.rmw k addr n op) σ = RmwOk A tid pl σ k ⟨addr, n⟩ op := rfl

@[simp] theorem envGT_step_load (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGT I A tid pl).State) (k : LoadKind)
    (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGT I A tid pl).step (.load k xcl addr n) σ v σ' = LoadOutT A tid σ σ' k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGT_step_store' (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGT I A tid pl).State) (k : StoreKind)
    (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) (b : Bool) :
    (EnvGT I A tid pl).step (.store k xcl addr n v) σ b σ' = StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b := rfl

@[simp] theorem envGT_step_rmw' (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGT I A tid pl).State) (k : RmwKind)
    (addr : BitVec 64) (n : Nat) (op : Val → Option Val) (old : Val) :
    (EnvGT I A tid pl).step (.rmw k addr n op) σ old σ' = RmwOut A tid pl σ σ' k ⟨addr, n⟩ op old := rfl

@[simp] theorem envGT_step_fence' (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGT I A tid pl).State) (k : FenceKind)
    (u : Unit) : (EnvGT I A tid pl).step (.fence k) σ u σ' = FenceOut σ σ' k := rfl

/-! ## Fences -/

/-- Every `EnvGT` fence is permitted and stays in `FenceLe σ` (its fences
are `EnvG`'s). -/
theorem fenceInv_fenceLeT (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) :
    (EnvGT I A tid pl).FenceInv (FenceLe σ) :=
  fenceInv_fenceLe A tid pl σ

instance (A : Arch) (tid : Nat) (pl : Plan) : (EnvGT I A tid pl).FenceMono :=
  ⟨FenceLe, FenceLe.refl, fenceInv_fenceLeT A tid pl⟩

@[simp] theorem fenceMono_le_envGT (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMono.le (env := EnvGT I A tid pl)) = FenceLe := rfl

/-! ## Loads that do not take -/

/-- A non-acquire load takes nothing. -/
theorem takeEff_of_not_acq {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (h : TakeEff A k vs l tr r ga a) (hk : (A.loadKind k).isAcquire = false) : a = ⟨r, ga, []⟩ :=
  h.2 fun hc => absurd hc.1 (by rw [hk]; decide)

/-! ## Loads that may take -/

/-- **A load's resource effect only adds to the thread's write permissions**
(moved from the x64 ticket lock proof's `TicketX.takeEffX_q_ge`, which is now this). -/
theorem takeEff_q_ge {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (ha : TakeEff A k vs l tr r ga a) (x : Loc) : (r.wr x).q ≤ (a.r.wr x).q := by
  by_cases hc : TakeCond A k vs l tr
  · rw [ha.1 hc]; exact takeAll_q_ge _ _ _ _ x
  · rw [ha.2 hc]; exact Rat.le_refl

/-- **A load keeps a full write permission** (the ISA-neutral form
of `X64.EnvG.takeEff_wr_full`, moved here from `EnvG/TakeX64VCGen.lean`): if
the thread holds all of `x` (and erasure at the load's anchor ghost holds),
the load's resource effect, take or no take, leaves the thread's permission
of `x` unchanged. -/
theorem takeEff_wr_fullG {rF : Nat → Res} {c : Config I} {tid : Nat} {A : Arch} {k : LoadKind} {vs : Views}
    {l : Loc} {tr : Time} {r : Res} {ga : Ghost} {a : TakeAcc} (hn : tid < c.threads.size)
    (E : Erase (setRes rF tid r) ga (fun _ => True) c) (ha : TakeEff A k vs l tr r ga a) {x : Loc}
    (hq : (r.wr x).q = 1) : (a.r.wr x).q = 1 ∧ ∀ p, (a.r.wr x).X p ↔ (r.wr x).X p := by
  by_cases hc : TakeCond A k vs l tr
  · obtain rfl := ha.1 hc
    obtain ⟨d, hd, hXd⟩ := takeFold_wr l tr x (ga.acqIds r.acq l) ⟨r, ga, []⟩
    have hle := (takeAll_erase (l := l) (tr := tr) hn E).thread_q_le hn x
    change ((takeAll l tr r ga).r.wr x).q = (r.wr x).q + d.q at hd
    change ∀ p, ((takeAll l tr r ga).r.wr x).X p ↔ (r.wr x).X p ∨ d.X p at hXd
    have h1 := d.nonneg
    have hd0 : d.q = 0 := by grind
    refine ⟨by grind, fun p => ?_⟩
    rw [hXd]
    exact ⟨fun h => h.elim id fun h' => absurd h' (d.zero hd0 p), .inl⟩
  · obtain rfl := ha.2 hc
    exact ⟨hq, fun _ => Iff.rfl⟩

end Kraken.Promising.SLR.EnvG
