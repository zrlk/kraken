/-
**x64 message passing with an unlocked `incl` release, proved on `EnvGLR`**
`x64_mp_incl_envG`, the shape of
`MpPublic.x64_mp_public` for the writer `movl $42, (%rsi); incl (%rdi)`
(`mp_incl.kl`) and the reader `spin: movl (%rdi), %eax; cmpl $0, %eax;
je spin; movl (%rsi), %ebx`, for all layouts. The first end-to-end use of the
load-then-release link `ofSafelyEnvGLRX`.

- **Start**: `StartWIX` (as `StartWX`, for `mpIncWriterX`) and
  `MpPublic.StartRX`; parameters `MpPublic.ghostParams`.
- **The rules' invariants at the start** (`invWIX_init`, `invRIX_init`):
  `invGLRX_init` (writer, from `mpIncWriterX_envG` by
  `qx64LR_of_partialTripleEnv`) and `invGX_init` (reader, from
  `mpReaderIX_envGP`), at `σInitX` with `mpRes`/`mpGhostI`.
- **`NPSafe`** (`x64_mp_incl_npSafe`): `NPSafe.of_ruleRX` at the two rules.
- **Scope and purity**: `final_of_relPureSafelyQX_tso` with the writer's
  all-release specification `mpIncWriterX_noNT` and the reader's
  `mpReaderX_noNT`.
- **Initial erasure and final argument**: `erase_mpIncInit`, `mp_finalI`
  (`X64MpIncSpec.lean`; the initial flag message is in release mode).
-/
import Kraken.Promising.SLR.EnvG.X64MpIncLink
import Kraken.Promising.SLR.EnvG.X64MpIncRelPure
import Kraken.Promising.SLR.EnvG.X64MpPublic

namespace Kraken.Promising.X64.EnvG.MpInc

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic

/-! ## The start -/

section Start

variable [layout : _root_.Layout]

/-- The x64 `incl` writer at its start, with flag address `f` and data
address `d` (`StartWX` for `mpIncWriterX`). -/
structure StartWIX (f d : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout mpIncWriterX
  decls : s.decls = {}
  endPc : s.endPc = (layout mpIncWriterX).addrOf mpIncWriterX.length
  pc : s.st.2 = (layout mpIncWriterX).addrOf 0
  rdi : s.st.1.regs.get64 .rdi = f
  rsi : s.st.1.regs.get64 .rsi = d
  split : Split [(f, 4), (d, 4)] s.st.1.dmem

variable {f d : BitVec 64} {sW sR : isa.State} {initMem : List (Loc × Val)}

/-- **The `incl` writer's initial invariant** (thread `0`). -/
theorem invWIX_init [Executable.ValidLayout (layout mpIncWriterX)] (hfd : f ≠ d) (hW : StartWIX f d sW) :
    (mpIncRuleW (ghostParams f d) (ghostParams_mpLocs hfd) 0 1).Inv True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) 0) (mpGhostI (ghostParams f d)) := by
  letI : CodeEnv := ⟨layout mpIncWriterX⟩
  have hL := ghostParams_mpLocs hfd
  refine invGLRX_init (s := sW) rfl rfl (qx64LR_of_partialTripleEnv (mpIncWriterX_envG _ hL 0).partial rfl hW.exe
    hW.decls hW.endPc hW.pc hW.split
    ⟨hW.rdi, hW.rsi, split_df hW.split, split_dd hW.split, ⟨mpGhostI_rel_Fl, fun v => ?_⟩, ?_⟩)
  · show Pred.Pure ((mpGhostI _).rel _) v
    rw [mpGhostI_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v
  · simp only [σInitX, Own0, mpRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
    exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

/-- **The reader's initial invariant** (thread `1`). -/
theorem invRIX_init [Executable.ValidLayout (layout mpReaderX)] (hfd : f ≠ d) (hR : StartRX f d sR) :
    (mpIncRuleR (ghostParams f d) (ghostParams_mpLocs hfd) 1).Inv True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) 1) (mpGhostI (ghostParams f d)) := by
  letI : CodeEnv := ⟨layout mpReaderX⟩
  refine invGX_init (s := sR) rfl rfl (qx64_of_partialTripleEnv (mpReaderIX_envGP _ 1).uncount rfl hR.exe
    hR.decls hR.endPc hR.pc hR.split
    ⟨0, ⟨hR.rdi, hR.rsi, split_df hR.split, split_dd hR.split⟩, ⟨mpGhostI_rel_Fl, 0, Nat.zero_lt_one, rfl, ?_⟩, ?_⟩)
  · simp [σInitX, mpRes, readerRes]
  · simp [σInitX, Views.getFwd]

end Start

/-! ## `NPSafe` -/

/-- **The `NPSafe` side of Theorem 1′ for x64 MP with the `incl` writer.** -/
theorem x64_mp_incl_npSafe (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpIncWriterX)]
    [Executable.ValidLayout (lR mpReaderX)] {f d : BitVec 64} (hfd : f ≠ d) {sW sR : isa.State}
    {initMem : List (Loc × Val)} (hW : StartWIX (layout := lW) f d sW) (hR : StartRX (layout := lR) f d sR) :
    ∀ tid, tid < [sW, sR].length → ∀ n m, NPSafe (model isa) Arch.tso (MpPostI (ghostParams f d) 1) tid n m True
      (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) tid)
      (mpGhostI (ghostParams f d)) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invWIX_init (layout := lW) hfd hW)
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invRIX_init (layout := lR) hfd hR)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-! ## Scope and purity -/

/-- The threads' all-release specifications: the `incl` writer (layout `lW`)
at thread `0`, the reader (layout `lR`) elsewhere. -/
def mpIncNoNTSpec (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpIncWriterX)]
    [Executable.ValidLayout (lR mpReaderX)] (f d : BitVec 64) :
    Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 => RelPureSpecQX.ofProgram (layout := lW) [(f, 4), (d, 4)] (mpS_le16 ⟨f, d, ⟨0, 5⟩⟩) mpIncWriterX
      fun _ _ => True
  | _ + 1 => RelPureSpecQX.ofProgram (layout := lR) [(f, 4), (d, 4)] (mpS_le16 ⟨f, d, ⟨0, 5⟩⟩) mpReaderX
      fun _ _ => ∃ _ : Nat, True

/-- **The all-release specifications hold at the start states.** -/
theorem mpIncNoNTSpec_init (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpIncWriterX)]
    [Executable.ValidLayout (lR mpReaderX)] {f d : BitVec 64} {sW sR : isa.State}
    (hW : StartWIX (layout := lW) f d sW) (hR : StartRX (layout := lR) f d sR) :
    ∀ tid s, [sW, sR][tid]? = some s → (mpIncNoNTSpec lW lR f d tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hsp⟩ := hW
    letI : CodeEnv := ⟨lW mpIncWriterX⟩
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lW) (mpIncWriterX_noNT (layout := lW) f d).partial
      rfl he hds hend hpc hsp ⟨hx0, hx1, split_df hsp, split_dd hsp⟩
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hsp⟩ := hR
    letI : CodeEnv := ⟨lR mpReaderX⟩
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lR) (mpReaderX_noNT (layout := lR) f d).uncount rfl
      he hds hend hpc hsp ⟨0, hx0, hx1, split_df hsp⟩
  | _ + 2, _, hs => by cases hs

/-! ## The theorem -/

/-- **Message passing for x64 under `Arch.tso` with an unlocked `incl`
release, proved on `EnvGLR`** (the shape and conclusion of
`MpPublic.x64_mp_public`).

For valid layouts `lW` of `mpIncWriterX` (`movl $42, (%rsi); incl (%rdi)`)
and `lR` of `mpReaderX` and addresses `f ≠ d`: if thread `0` is the writer
and thread `1` the reader, each at its start with `rdi = f`, `rsi = d` and
neither word in its private memory (`StartWIX`, `StartRX`), and the initial
memory has the flag word `⟨f, 4⟩` at `0`, then every configuration
`Reachable` under `Arch.tso` that is final has the reader's `ebx` at `42`
and the data word `⟨d, 4⟩` at `42`.

As for `x64_mp_public`: only final configurations are constrained (no
fairness), `f ≠ d` does not exclude overlapping words, and faults are not
covered by this statement (`mpIncRuleW_noFault`, `mpIncRuleR_noFault` are
the rules' no-fault facts). The flag's final value is not stated (the
writer's plan is value-agnostic: every store to the flag is its release). -/
theorem x64_mp_incl_envG {fuel : Nat} (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpIncWriterX)]
    [Executable.ValidLayout (lR mpReaderX)] (f d : BitVec 64) (hfd : f ≠ d)
    {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartWIX (layout := lW) f d sW) (hR : StartRX (layout := lR) f d sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 42#128 :=
  final_of_relPureSafelyQX_tso fuel (B := MpPostI (ghostParams f d) 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal ⟨d, 4⟩ = 42#128)
    (erase_mpIncInit _ _ hF0) pend_mpGhostI (mpIncNoNTSpec lW lR f d) (mpIncNoNTSpec_init lW lR hW hR)
    (x64_mp_incl_npSafe lW lR hfd hW hR) hc hf
    fun _ _ E' hle hsize hB => mp_finalI E' hf hsize (by rw [hle.rel]; exact mpGhostI_rel_Fl) hB

end Kraken.Promising.X64.EnvG.MpInc
