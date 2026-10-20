/-
**Message passing on `EnvG`: the start and `NPSafe`**.

- `invW_envG_init`, `invR_envG_init`: the rules' invariants at
  `Config.init [sW, sR] initMem` from `StartW`/`StartR`: `invG_init` at
  `σInit` with the initial resources and ghost (`mpRes`, `mpGhost`,
  `SLR/MpSpec.lean`), `QA64` from the `vcgen` proofs (`mpWriter_envG`,
  `mpReader_envGP`) by `qa64_of_partialTripleEnv`.
- `mp_envG_npSafe`: `NPSafe.of_ruleRX` at the two EnvG rules
  (`EnvG/MpLink.lean`).

Imports only the specification side of MP (`SLR/MpSpec.lean`), not the old
hand-proved rules.
-/
import Kraken.Promising.SLR.EnvG.MpLink
import Kraken.Promising.SLR.MpSpec

namespace Kraken.Promising.SLR.EnvG.MpLink

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpSmoke Kraken.Promising.SLR.MpPublic

/-! ## The start -/

section Start

variable [layout : _root_.Layout] {f d : BitVec 64} {sW sR : isa.State} {initMem : List (Loc × Val)}

/-- **The writer's initial invariant** (thread `0`). -/
theorem invW_envG_init [Executable.ValidLayout (layout mpWriter)] (hfd : f ≠ d) (hW : StartW f d sW) :
    (mpRuleW_envG (ghostParams f d) (ghostParams_mpLocs hfd) 0 1).Inv True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) 0) (mpGhost (ghostParams f d)) := by
  letI : CodeEnv := ⟨layout mpWriter⟩
  have hL := ghostParams_mpLocs hfd
  refine invG_init (s := sW) rfl rfl (qa64_of_partialTripleEnv (mpWriter_envG _ hL 0).partial rfl hW.exe
    hW.decls hW.endPc hW.pc ⟨hW.x0, hW.x1, hW.df, hW.dd, ⟨mpGhost_rel_Fl, fun v => ?_⟩, ?_⟩)
  · show Pred.Pure ((mpGhost _).rel _) v
    rw [mpGhost_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v
  · simp only [σInit, Own0, mpRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
    exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

/-- **The reader's initial invariant** (thread `1`). -/
theorem invR_envG_init [Executable.ValidLayout (layout mpReader)] (hfd : f ≠ d) (hR : StartR f d sR) :
    (mpRuleR_envG (ghostParams f d) (ghostParams_mpLocs hfd) 1).Inv True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) 1) (mpGhost (ghostParams f d)) := by
  letI : CodeEnv := ⟨layout mpReader⟩
  refine invG_init (s := sR) rfl rfl (qa64_of_partialTripleEnv (mpReader_envGP _ 1).uncount rfl hR.exe
    hR.decls hR.endPc hR.pc ⟨0, hR.x0, hR.x1, hR.df, hR.dd, ⟨mpGhost_rel_Fl, 0, Nat.zero_lt_one, rfl, ?_⟩, ?_⟩)
  · simp [σInit, mpRes, readerRes]
  · simp [σInit, Views.getFwd]

end Start

/-! ## `NPSafe` and the theorem -/

/-- **The `NPSafe` side of Theorem 1′ for MP on `EnvG`**: both threads at
the initial configuration, through the EnvG rules. -/
theorem mp_envG_npSafe (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR mpReader)] {f d : BitVec 64} (hfd : f ≠ d) {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartW (layout := lW) f d sW) (hR : StartR (layout := lR) f d sR) :
    ∀ tid, tid < [sW, sR].length → ∀ n m, NPSafe (model isa) Arch.armv8 (MpPost (ghostParams f d) 1) tid n m True
      (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) tid)
      (mpGhost (ghostParams f d)) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invW_envG_init (layout := lW) hfd hW)
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invR_envG_init (layout := lR) hfd hR)
  · simp only [List.length_cons, List.length_nil] at htid; omega

end Kraken.Promising.SLR.EnvG.MpLink
