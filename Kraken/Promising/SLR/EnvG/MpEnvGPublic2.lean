/-
**Message passing on `EnvG` with purity by `vcgen`**:
`mp_envG'`, the statement of `MpPublic.mp_public`, proved as `mp_envG`
(`EnvG/MpEnvGPublic.lean`: the EnvG rules, `NPSafe`, initial erasure, final
argument) except for purity: `final_of_relPureSafely`
(`EnvG/RelPureEnvA64.lean`) with one `RelPureSpec` per thread from the
`vcgen` proofs of `EnvG/MpRelPure.lean`, in place of `MpPure`'s
`MpReach`/`mpReach_reachable`/`mp_cell`.

Imports: `EnvG/MpEnvGStart.lean` and `SLR/MpSpec.lean` only, not
`EnvG/MpEnvGPublic.lean`/`SLR/MpPublic.lean` and the old MP proofs behind
them. The check that `mp_envG'` has the statement of `mp_public` is in the
leaf `EnvG/MpEnvGCheck.lean`.
-/
import Kraken.Promising.SLR.EnvG.MpEnvGStart
import Kraken.Promising.SLR.EnvG.MpRelPure

namespace Kraken.Promising.SLR.EnvG.MpLink

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpRelPure Kraken.Promising.SLR.MpPublic

/-- The MP threads' purity specifications: the writer (layout `lW`) at
thread `0`, the reader (layout `lR`) elsewhere. -/
def mpPureSpec (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR mpReader)] (rel : Loc → Pred) : Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := lW) mpWriter fun _ _ => True
  | _ + 1 => RelPureSpec.ofProgram (layout := lR) mpReader fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the MP start states.** -/
theorem mpPureSpec_init (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR mpReader)] {f d : BitVec 64} (hfd : f ≠ d) {sW sR : isa.State}
    (hW : StartW (layout := lW) f d sW) (hR : StartR (layout := lR) f d sR) :
    ∀ tid s, [sW, sR][tid]? = some s → (mpPureSpec lW lR (mpGhost (ghostParams f d)).rel tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hdf, hdd⟩ := hW
    letI : CodeEnv := ⟨lW mpWriter⟩
    refine RelPureSpec.holds_of_partialTripleEnv (layout := lW)
      (mpWriter_relPure (layout := lW) _ f d fun v => ?_).partial rfl he hds hend hpc ⟨hx0, hx1, hdf, hdd⟩
    rw [show (⟨d, 4⟩ : Loc) = (ghostParams f d).Dt from rfl,
      mpGhost_rel_ne (Ne.symm (ghostParams_mpLocs hfd).fl_dt)]
    exact Pred.emp_pure v
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, -, hdf, -⟩ := hR
    letI : CodeEnv := ⟨lR mpReader⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lR) (mpReader_relPure (layout := lR) _ f).uncount rfl
      he hds hend hpc ⟨0, hx0, hdf⟩
  | _ + 2, _, hs => by cases hs

/-- **Message passing for AArch64 under `Arch.armv8`, on `EnvG`, purity by
`vcgen`**: the statement of `MpPublic.mp_public`; as `mp_envG`, with the
purity hypotheses of `final_of_relWrites` from `final_of_relPureSafely`. -/
theorem mp_envG' {fuel : Nat} (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR mpReader)] (f d : BitVec 64) (hfd : f ≠ d) {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartW (layout := lW) f d sW) (hR : StartR (layout := lR) f d sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 1#128 :=
  final_of_relPureSafely Arch.armv8 fuel (B := MpPost (ghostParams f d) 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal ⟨d, 4⟩ = 1#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_mpInit _ _ hF0) pend_mpGhost
    (mpPureSpec lW lR _) (mpPureSpec_init lW lR hfd hW hR) (mp_envG_npSafe lW lR hfd hW hR) hc hf
    fun _ _ E' hle hsize hB => mp_final E' hf hsize (by rw [hle.rel]; exact mpGhost_rel_Fl) hB

end Kraken.Promising.SLR.EnvG.MpLink
