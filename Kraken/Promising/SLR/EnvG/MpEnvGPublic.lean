/-
**Message passing on `EnvG`, the public theorem**:
`mp_envG`, the statement of `MpPublic.mp_public` proved by the EnvG route
(the old theorem and `SLR/Mp*.lean` are unchanged).

- **Start**: the rules' invariants at `Config.init [sW, sR] initMem` from
  `StartW`/`StartR` (`invW_envG_init`, `invR_envG_init`): `invG_init` at
  `σInit` with the initial resources and ghost of `SLR/MpInit.lean`
  (`mpRes`, `mpGhost`), `QA64` from the `vcgen` proofs
  (`mpWriter_envG`, `mpReader_envGP`) by `qa64_of_partialTripleEnv`.
- **`NPSafe`** (`mp_envG_npSafe`): `NPSafe.of_ruleRX` at the two EnvG rules
  (`EnvG/MpLink.lean`). No no-fault hypothesis: Theorem 1′'s chain
  (`final_of_relWrites`) does not take `NoFaultRule`; the rules' no-fault
  facts are `mpRuleW_envG_noFault`/`mpRuleR_envG_noFault`.
- **Assembly** as `Mp.mp_armv8`: purity (`MpReach`, `mpReach_reachable`,
  `mp_cell`, `SLR/MpPure.lean`), initial erasure (`erase_mpInit`) and the
  final argument (`mp_final`) are reused unchanged: they are about the
  program, the initial state and the postcondition, not the rules.

The start and `NPSafe` (`invW_envG_init`, `invR_envG_init`, `mp_envG_npSafe`)
are in `EnvG/MpEnvGStart.lean` (moved unchanged, so that
`EnvG/MpEnvGPublic2.lean` need not import this file and the old MP proofs).
-/
import Kraken.Promising.SLR.EnvG.MpEnvGStart
import Kraken.Promising.SLR.MpPublic

namespace Kraken.Promising.SLR.EnvG.MpLink

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpSmoke Kraken.Promising.SLR.MpPublic

/-- **Message passing for AArch64 under `Arch.armv8`, proved on `EnvG`**: the
statement of `MpPublic.mp_public` (see there for what is and is not covered),
with the rules from `ThreadRuleRX.ofSafelyEnvG`. -/
theorem mp_envG {fuel : Nat} (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR mpReader)] (f d : BitVec 64) (hfd : f ≠ d) {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartW (layout := lW) f d sW) (hR : StartR (layout := lR) f d sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 1#128 :=
  final_of_relWrites (I := isa) Arch.armv8 fuel (B := MpPost (ghostParams f d) 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal ⟨d, 4⟩ = 1#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_mpInit _ _ hF0) pend_mpGhost (MpReach lW lR _)
    (fun _ hc' _ _ ht => mpReach_reachable lW lR _ (StartW.frame (layout := lW) hW)
      (StartR.frame (layout := lR) hR) hc' ht)
    (mp_cell lW lR _ (ghostParams_mpLocs hfd) Arch.armv8) (mp_envG_npSafe lW lR hfd hW hR) hc hf
    fun _ _ E' hle hsize hB => mp_final E' hf hsize (by rw [hle.rel]; exact mpGhost_rel_Fl) hB

/-- `mp_envG` has exactly the statement of `mp_public`. -/
example : type_of% @mp_envG = type_of% @mp_public := rfl

/-- **Message passing** for the concrete writer and reader, derived from
`mp_envG` (the statement of `MpConcrete.mp_concrete`). -/
theorem mp_concrete_envG {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [MpConcrete.writer0, MpConcrete.reader0] MpConcrete.initMemMp) c)
    (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal MpConcrete.Pmp.Dt = 1#128 :=
  mp_envG MpConcrete.wLayout MpConcrete.rLayout MpConcrete.flagAddr MpConcrete.dataAddr (by decide) writer0_start
    reader0_start (by decide) hc hf

end Kraken.Promising.SLR.EnvG.MpLink
