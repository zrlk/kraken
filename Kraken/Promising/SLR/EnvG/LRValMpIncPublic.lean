/-
**x64 message passing with an unlocked `incl` release, with the flag's final
value**: `x64_mp_incl_envGV`, the statement of
`MpInc.x64_mp_incl_envG` plus **`[f]=1`** (`mp_incl.kl`'s full `forall`), for
all layouts. The writer runs on `EnvGLRV` (`LRValMpInc.lean`), the reader is
unchanged (`MpInc.mpIncRuleR`'s judgment).

- **Postcondition** `MpPostF`: the writer's token and `FlFin` (all of `Fl`,
  maximal write `(1, tw)`), or the reader's result with its acquire id.
  `MpPostF → MpPostI`, so `MpInc.mp_finalI` still gives `ebx = 42` and
  `[d] = 42`.
- **Final flag value** (`flag_finalF`): some done thread is in the writer
  case (two reader cases contradict erasure: the same id held twice, or two
  slots of the seen flag message, for distinct ids, each holding all of
  `Dt`), and its `FlFin` is the total's maximal write of `Fl`
  (`total_max_of_thread`, `Erase.finalVal_of_max`).
- **Start**: `MpInc.StartWIX`/`MpPublic.StartRX`; the writer's initial
  invariant `invWIXV_init` from `mpIncWriterXV_envG` (`FlInit` from
  `writerRes` and `initVal f = 0`), the reader's `MpInc.invRIX_init`.
-/
import Kraken.Promising.SLR.EnvG.LRValMpInc
import Kraken.Promising.SLR.EnvG.X64MpIncPublic

namespace Kraken.Promising.X64.EnvG.MpIncV

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic
open Kraken.Promising.X64.EnvG.MpInc

/-! ## The postcondition and the final argument -/

/-- **The shared postcondition with the flag**: the writer's token and
`FlFin`, or the reader's result with its acquire id. -/
def MpPostF (P : Params) (rd : Nat) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  (1 ≤ (r.wr P.W).q ∧ FlFin P r) ∨
    (ReaderDone P rd c ∧ ∃ ι, ι < g.acqTab.length ∧ g.acqPred ι = φI P ∧ r.acq P.Fl ι = 1)

theorem MpPostF.toI {P : Params} {rd : Nat} {c : Config isa} {r : Res} {g : Ghost} (h : MpPostF P rd c r g) :
    MpPostI P rd c r g :=
  h.imp (fun h => h.1) id

/-- **The flag's final value**: from erasure at a final configuration of two
threads whose final resources satisfy `MpPostF P 1`, `[f] = 1`. -/
theorem flag_finalF {P : Params} {c : Config isa} {rF : Nat → Res} {g : Ghost}
    (E : Erase rF g (fun _ => False) c) (hf : c.final = true) (hsize : c.threads.size = 2)
    (hrel : g.rel P.Fl = φI P) (hB : ∀ tid, c.Done tid → MpPostF P 1 c (rF tid) g) :
    c.mem.finalVal P.Fl = 1#128 := by
  have h0 : (0 : Nat) < c.threads.size := by rw [hsize]; decide
  have h1 : (1 : Nat) < c.threads.size := by rw [hsize]; decide
  have hacqT : ∀ {j : Nat} {ι : PredId}, j < c.threads.size → (rF j).acq P.Fl ι = 1 →
      (total rF g c).acq P.Fl ι = 1 :=
    fun {j} {ι} hj ha => by
      have h1 := sub_acq_le (sub_total_thread (rF := rF) (g := g) hj) P.Fl ι
      have h2 := E.valid.2 P.Fl ι
      omega
  have hW : ∃ j, j < c.threads.size ∧ FlFin P (rF j) := by
    rcases hB 0 (Config.final_done hf h0) with ⟨-, hF⟩ | hr0
    · exact ⟨0, h0, hF⟩
    rcases hB 1 (Config.final_done hf h1) with ⟨-, hF⟩ | hr1
    · exact ⟨1, h1, hF⟩
    exfalso
    obtain ⟨⟨-, ts, v, hrd, hv⟩, ι₀, -, hp₀, ha₀⟩ := hr0
    obtain ⟨-, ι₁, -, hp₁, ha₁⟩ := hr1
    by_cases e : ι₀ = ι₁
    · subst e
      have h2 := sub_acq_le (sub_total_pair (rF := rF) (g := g) h0 h1 (by decide)) P.Fl ι₀
      have h3 := E.valid.2 P.Fl ι₀
      change (rF 0).acq P.Fl ι₀ + (rF 1).acq P.Fl ι₀ ≤ _ at h2
      omega
    · obtain ⟨s₀, hs₀, -, hid₀, hq₀, -⟩ := slot_of_seenI E hrel hp₀ (hacqT h0 ha₀) hrd hv
      obtain ⟨s₁, hs₁, -, hid₁, hq₁, -⟩ := slot_of_seenI E hrel hp₁ (hacqT h1 ha₁) hrd hv
      have hne : s₁ ≠ s₀ := fun h => e (by rw [← hid₀, ← hid₁, h])
      have := E.q_add_le_one_slots hs₀ hs₁ hne P.Dt
      rw [hq₀, hq₁] at this
      grind
  obtain ⟨j, hj, hq, tw, hX, hmax⟩ := hW
  obtain ⟨hpos, hXT, hmaxT⟩ := Kraken.Promising.SLR.total_max_of_thread E hj hq hX hmax
  exact E.finalVal_of_max hf hpos hXT hmaxT

/-! ## The two rules with `MpPostF` -/

section Rules

variable [layout : _root_.Layout]

/-- **`hB` for the writer** (`MpPostF`). -/
theorem hB_WF (P : Params) (tid rd : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postWV P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpIncPlan P) σ c t r g cl → cl → MpPostF P rd c r g := by
  intro c t r g cl σ hpost hp hrel hcl
  obtain ⟨h1, h2⟩ := hB_WV P tid rd c t r g cl σ hpost hp hrel hcl
  rcases h1 with h1 | h1
  · exact .inl ⟨h1, h2⟩
  · exact .inr h1

/-- **`hB` for the reader** (`MpPostF`; `hB_RG`'s proof). -/
theorem hB_RF (P : Params) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postRI P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan P) σ c t r g cl → cl → MpPostF P tid c r g := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, ⟨hw, tsF, vF, hrd, hv⟩, hx⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inr ⟨⟨⟨t, hrel.ht, hx (hrel.cl hcl)⟩, tsF, vF, hrel.snap.read? hrd, hv⟩, (hw.mono hrel.ghost).2⟩

/-- **The writer's rule on `EnvGLRV`** with `MpPostF`. -/
def mpIncRuleWF [Executable.ValidLayout (layout mpIncWriterX)] (P : Params) (hL : MpLocs P) (tid rd : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (MpPostF P rd) tid :=
  ThreadRuleRX.ofSafelyEnvGLRVX (S := mpS P) (post := postWV P) (mpIncPlan_valid hL) (mpIncPlan_whole P)
    (mpS_le16 P) mpIncWriterX_lr postOfX_end (not_instrStepEnv_of_end_labels _ 0) (hB_WF P tid rd)

/-- **The reader's rule on `EnvG`** with `MpPostF` (`mpIncRuleR`'s judgment). -/
def mpIncRuleRF [Executable.ValidLayout (layout mpReaderX)] (P : Params) (hL : MpLocs P) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (MpPostF P tid) tid :=
  ThreadRuleRX.ofSafelyEnvGX (S := mpS P) (post := postRI P) (mpPlan_valid hL) (mpS_le16 P) mpReaderX_phase1
    postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_RF P tid)

end Rules

/-! ## The start -/

section Start

variable {f d : BitVec 64} {sW sR : isa.State} {initMem : List (Loc × Val)}

section Layout

variable [layout : _root_.Layout]

/-- **The `incl` writer's initial invariant on `EnvGLRV`** (thread `0`). -/
theorem invWIXV_init [Executable.ValidLayout (layout mpIncWriterX)] (hfd : f ≠ d) (hW : StartWIX f d sW)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0) :
    (mpIncRuleWF (ghostParams f d) (ghostParams_mpLocs hfd) 0 1).Inv True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) 0) (mpGhostI (ghostParams f d)) := by
  letI : CodeEnv := ⟨layout mpIncWriterX⟩
  have hL := ghostParams_mpLocs hfd
  refine invGLRVX_init (s := sW) rfl rfl (qx64LRV_of_partialTripleEnv (mpIncWriterXV_envG _ hL 0).partial rfl hW.exe
    hW.decls hW.endPc hW.pc hW.split
    ⟨hW.rdi, hW.rsi, split_df hW.split, split_dd hW.split, ⟨⟨⟨mpGhostI_rel_Fl, fun v => ?_⟩, ?_⟩, ?_⟩⟩)
  · show Pred.Pure ((mpGhostI _).rel _) v
    rw [mpGhostI_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v
  · simp only [σInitX, Own0, mpRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
    exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩
  · simp only [σInitX, FlInit, mpRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
    refine ⟨by simp, fun p hp => ?_⟩
    rw [hp.2]
    simp only [Prod.mk.injEq, and_true]
    exact hF0

end Layout

/-- **The `NPSafe` side** with `MpPostF`. -/
theorem x64_mp_incl_npSafeV (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpIncWriterX)]
    [Executable.ValidLayout (lR mpReaderX)] (hfd : f ≠ d) (hW : StartWIX (layout := lW) f d sW)
    (hR : StartRX (layout := lR) f d sR) (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0) :
    ∀ tid, tid < [sW, sR].length → ∀ n m, NPSafe (model isa) Arch.tso (MpPostF (ghostParams f d) 1) tid n m True
      (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) tid)
      (mpGhostI (ghostParams f d)) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invWIXV_init (layout := lW) hfd hW hF0)
  · exact NPSafe.of_ruleRX (mpIncRuleRF (layout := lR) (ghostParams f d) (ghostParams_mpLocs hfd) 1) n m _ _ _ _
      (invRIX_init (layout := lR) hfd hR)
  · simp only [List.length_cons, List.length_nil] at htid; omega

end Start

/-! ## The theorem -/

/-- **Message passing for x64 under `Arch.tso` with an unlocked `incl`
release, with the flag's final value** (`x64_mp_incl_envG` plus `[f] = 1`).

For valid layouts `lW` of `mpIncWriterX` and `lR` of `mpReaderX` and
addresses `f ≠ d`: if thread `0` is the writer and thread `1` the reader,
each at its start (`StartWIX`, `StartRX`), and the initial memory has the
flag word at `0`, then every final configuration `Reachable` under
`Arch.tso` has the reader's `ebx` at `42`, the data word at `42` and the
flag word `⟨f, 4⟩` at `1`. -/
theorem x64_mp_incl_envGV {fuel : Nat} (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpIncWriterX)]
    [Executable.ValidLayout (lR mpReaderX)] (f d : BitVec 64) (hfd : f ≠ d)
    {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartWIX (layout := lW) f d sW) (hR : StartRX (layout := lR) f d sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 42#128 ∧ cfg.mem.finalVal ⟨f, 4⟩ = 1#128 :=
  final_of_relPureSafelyQX_tso fuel (B := MpPostF (ghostParams f d) 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal ⟨d, 4⟩ = 42#128 ∧ c.mem.finalVal ⟨f, 4⟩ = 1#128)
    (erase_mpIncInit _ _ hF0) pend_mpGhostI (mpIncNoNTSpec lW lR f d) (mpIncNoNTSpec_init lW lR hW hR)
    (x64_mp_incl_npSafeV lW lR hfd hW hR hF0) hc hf
    fun _ _ E' hle hsize hB =>
      have hrel : _ := by rw [hle.rel]; exact mpGhostI_rel_Fl
      have h := mp_finalI E' hf hsize hrel fun tid hd => (hB tid hd).toI
      ⟨h.1, h.2, flag_finalF E' hf hsize hrel hB⟩

end Kraken.Promising.X64.EnvG.MpIncV
