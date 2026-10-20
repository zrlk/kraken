/-
**`msqueue2.kl` from the runner's exact configuration**: `x64_msqueue2_envG_runner`, `x64_msqueue2_envG_verbatim` for threads
that carry the `.kl` runner's declarations (the header types `s`, `n1`,
`n2`, `head`, `tail` `uint64_t`: strict sized, `Decls.Sized`), and its
concrete instance `x64_msqueue2_envG_runner_concrete` (`runnerMatchesD`:
declarations and initial memory included).

The proof is `X64MsQueue2Public`'s with the D forms of
`EnvG/X64DeclsLink.lean`: the enqueuer over its mask and the dequeuer at the
whole image, both `ThreadRuleRXF.ofSafelyEnvGFCAdjXMD`, `invGFCAdjXMD_init`,
`RelPureSpecQX.HoldsD`, `final_of_relPureSafelyQX_tsoFD`. The old theorems
are unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue2Public
import Kraken.Promising.SLR.EnvG.X64MsQueue2Concrete
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64RunnerCommon

namespace Kraken.Promising.X64.EnvG.MsQueueX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 mem_sAll8 split_sAll)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq2ImageV)]

/-! ## The rules and the start, with declarations -/

/-- **The verbatim enqueuer's rule with strict sized declarations `ds`**
(`enqRuleV` through `ofSafelyEnvGFCAdjXMD`, over the mask `msq2ImageM`). -/
noncomputable def enqRuleVD {ds : Decls} (hsz : ds.Sized) (P : Params) :
    ThreadRuleRXF (I := isa) Arch.tso (MQX P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjXMD (S := sAll) (post := postEV P) hsz msq2ImageM_mask (planE_valid P) sAll_le16
    msq2ImageM_phase1FX (postEV_end P) (enqM_stuck _) (hB_EV P)

/-- **The verbatim dequeuer's rule with strict sized declarations `ds`**
(`deqRuleV` through `ofSafelyEnvGFCAdjXMD` at the whole image). -/
noncomputable def deqRuleVD {ds : Decls} (hsz : ds.Sized) (P : Params) :
    ThreadRuleRXF (I := isa) Arch.tso (MQX P) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjXMD (S := sAll) (post := postDV P) hsz (MaskOf.refl _) (planD_valid P) sAll_le16
    msq2ImageV_phase1FX (postDV_end P) (deqV_stuck _) (hB_DV P)

/-- **The verbatim enqueuer at its start with declarations `ds`** (`StartEV`
with `decls = ds`). -/
structure StartEVD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout msq2ImageV
  decls : s.decls = ds
  pc : s.st.2 = labV "enqueuer"
  endPc : s.endPc = labV "edone"
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **The verbatim dequeuer at its start with declarations `ds`** (`StartDV`
with `decls = ds`). -/
structure StartDVD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout msq2ImageV
  decls : s.decls = ds
  pc : s.st.2 = labV "dequeuer"
  endPc : s.endPc = labV "ddone"
  r12 : s.st.1.regs.get64 .r12 = 0
  dmem : ∀ k, s.st.1.dmem.get? k = none

section Start

variable {ds : Decls} {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim enqueuer's initial invariant with declarations.** -/
theorem invEV_initD (hsz : ds.Sized) (hL : QLocs paramsV) (hS : StartEVD ds s0) :
    (enqRuleVD hsz paramsV).Inv True (Config.init [s0, s1] initMem)
      (tRes (Config.init [s0, s1] initMem).mem paramsV 0) (ghost₀ paramsV) := by
  have hst : s0.st = (s0.st.1, labV "enqueuer") := Prod.ext rfl hS.pc
  refine invGFCAdjXMD_init (s := s0) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, split_sAll hS.dmem, ?_⟩
  rw [hst]
  exact TreiberAbs.Safely.uncountT (enqM_envGCAdj paramsV hL rfl rfl rfl rfl s0.st.1 (_, 0)
    ⟨d8_of_dmem hS.dmem, e0_init paramsV _⟩)

/-- **The verbatim dequeuer's initial invariant with declarations.** -/
theorem invDV_initD (hsz : ds.Sized) (hL : QLocs paramsV) (hS : StartDVD ds s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem paramsV) :
    (deqRuleVD hsz paramsV).Inv True (Config.init [s0, s1] initMem)
      (tRes (Config.init [s0, s1] initMem).mem paramsV 1) (ghost₀ paramsV) := by
  have hst : s1.st = (s1.st.1, labV "dequeuer") := Prod.ext rfl hS.pc
  refine invGFCAdjXMD_init (s := s1) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, split_sAll hS.dmem, ?_⟩
  rw [hst]
  exact TreiberAbs.Safely.uncountT (deqV_envGCAdj' paramsV hL rfl rfl rfl s1.st.1 (_, 0)
    ⟨d8_of_dmem hS.dmem, comD_init paramsV _ hi, hS.r12⟩)

end Start

/-- **The all-release specifications hold at the start states with
declarations.** -/
theorem msq2NoNTSpecV_initD {ds : Decls} {s0 s1 : State} (h0 : StartEVD ds s0) (h1 : StartDVD ds s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (msq2NoNTSpecV tid).HoldsD ds s
  | 0, s, hs => by
    cases hs
    refine ⟨h0.exe, h0.endPc, h0.decls, split_sAll h0.dmem, ?_⟩
    rw [show s0.st = (s0.st.1, labV "enqueuer") from Prod.ext rfl h0.pc]
    exact TreiberAbs.Safely.uncountT (enqV_noNT _ ((), 0) (d8_of_dmem h0.dmem))
  | 1, s, hs => by
    cases hs
    refine ⟨h1.exe, h1.endPc, h1.decls, split_sAll h1.dmem, ?_⟩
    rw [show s1.st = (s1.st.1, labV "dequeuer") from Prod.ext rfl h1.pc]
    exact TreiberAbs.Safely.uncountT (deqV_noNT _ ((), 0) (d8_of_dmem h1.dmem))
  | _ + 2, s, hs => by simp at hs

/-- **The `NPSafeF` side for the verbatim `msqueue2` with declarations.** -/
theorem msq2V_npSafeFD {ds : Decls} (hsz : ds.Sized) (hL : QLocs paramsV) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartEVD ds s0) (h1 : StartDVD ds s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem paramsV) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.tso (MQX paramsV) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem paramsV tid) (ghost₀ paramsV) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invEV_initD hsz hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDV_initD hsz hL h1 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The two-node Michael–Scott queue `msqueue2.kl` for x64 under
`Arch.tso`, the `.kl`'s code verbatim, with the runner's declarations**:
`x64_msqueue2_envG_verbatim` for threads whose declarations are strict sized
(`ds.Sized`: the `.kl` runner's, from the typed header). -/
theorem x64_msqueue2_envG_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (hht : symV "head" ≠ symV "tail")
    (hhs : symV "head" ≠ symV "s") (hh1 : symV "head" ≠ symV "n1") (hh2 : symV "head" ≠ symV "n2")
    (hts : symV "tail" ≠ symV "s") (ht1 : symV "tail" ≠ symV "n1") (ht2 : symV "tail" ≠ symV "n2")
    (hs1 : symV "s" ≠ symV "n1") (hs2 : symV "s" ≠ symV "n2") (h12 : symV "n1" ≠ symV "n2")
    (hn1 : symV "n1" ≠ 0) (hn2 : symV "n2" ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEVD ds s0) (h1 : StartDVD ds s1) (hi : InitV (Config.init [s0, s1] initMem).mem paramsV)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th1, cfg.threads[1]? = some th1 ∧ th1.st.st.1.regs.get64 .r12 = symV "n1" ∧
      th1.st.st.1.regs.get64 .r13 = symV "n2" := by
  have hL := qLocs_paramsV hht hhs hh1 hh2 hts ht1 ht2 hs1 hs2 h12 hn1 hn2
  refine final_of_relPureSafelyQX_tsoFD (theorem1FChain Arch.tso fuel) (B := MQX paramsV)
    (Φ := MsQueue2FinalX (symV "n1") (symV "n2"))
    (erase_init hL _) (ghost₀_pend _) msq2NoNTSpecV (fun _ => ds) (fun _ => hsz) (msq2NoNTSpecV_initD h0 h1)
    (msq2V_npSafeFD hsz hL h0 h1 hi) hc hf fun rF' g' E' hle hsize hB => ?_
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw paramsV).mono hle
  have fin : ∀ i, i < cfg.threads.size → (∃ th, cfg.threads[1]? = some th ∧
      DoneD2 cfg.mem paramsV (th.st.st.1.regs.get64 .r12) (th.st.st.1.regs.get64 .r13) ∧
      InitV cfg.mem paramsV ∧ ∀ x, paramsV.IsW x → 1 ≤ (rF' i).acq x 0) →
      MsQueue2FinalX (symV "n1") (symV "n2") cfg := by
    rintro i hi ⟨th, hth, hd, hiv, hacq⟩
    exact ⟨th, hth, final_values E' hW hL hiv
      (fun x hx => TreiberCommon.total_acq_of_ge E' hi (hacq x hx)) hd⟩
  rcases hB 0 (Config.final_done hf hi0) with hd0 | hq0
  · exact fin 0 hi0 hd0
  rcases hB 1 (Config.final_done hf hi1) with hd1 | hq1
  · exact fin 1 hi1 hd1
  exact (tokH_pair_false E' hi0 hi1 (by decide) hq0 hq1).elim

end Kraken.Promising.X64.EnvG.MsQueueX

/-! ## The runner's configuration -/

namespace Kraken.Promising.X64.EnvG.MsQueueX.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.MsQueueX Kraken.Promising.SLR.EnvG

set_option maxRecDepth 8000

/-- The runner's declarations for the typed `msqueue2.kl`: `s`, `n1`, `n2`,
`head`, `tail`, 8-byte words (strict). -/
def msq2DeclsD : Decls :=
  { locs := [⟨0x1000000, 8⟩, ⟨0x1000100, 8⟩, ⟨0x1000200, 8⟩, ⟨0x1000300, 8⟩, ⟨0x1000400, 8⟩],
    unsizedDefault := false }

theorem msq2DeclsD_sized : msq2DeclsD.Sized := ⟨rfl, by decide⟩

/-- The threads as the runner prepares them, declarations included. -/
def msq2P0D : X64.State := { msq2P0 with decls := msq2DeclsD }
def msq2P1D : X64.State := { msq2P1 with decls := msq2DeclsD }

/-- The runner's configuration is `Config.init [msq2P0D, msq2P1D] msq2InitMemV`
in everything the theorem reads (declarations and initial memory included). -/
def runnerMatchesD (src : String) : Bool :=
  runnerMatchesDL src [msq2P0D, msq2P1D] msq2InitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD msq2Kl

section
attribute [local instance] msq2LayoutV

theorem msq2P0D_start : StartEVD msq2DeclsD msq2P0D :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labV "enqueuer"; rw [labV_at 0]; decide,
    by show (0x100000 + 20 : Int64) = labV "edone"; rw [labV_at 23]; decide,
    fun _ => by simp [msq2P0D, msq2P0]⟩

theorem msq2P1D_start : StartDVD msq2DeclsD msq2P1D :=
  ⟨rfl, rfl, by show (0x100000 + 20 : Int64) = labV "dequeuer"; rw [labV_at 24]; decide,
    by show (0x100000 + 42 : Int64) = labV "ddone"; rw [labV_at 50]; decide,
    by simp [msq2P1D, msq2P1, Reg64s.get64], fun _ => by simp [msq2P1D, msq2P1]⟩

theorem msq2D_initV : InitV (Config.init (I := isa) [msq2P0D, msq2P1D] msq2InitMemV).mem paramsV := by
  simp only [paramsV, symV_s, symV_n1, symV_n2, symV_head, symV_tail]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Params.head, Params.tail, Params.ls, Params.l1, Params.l2, Config.init_mem] <;> decide

end

/-- **The two-node Michael–Scott queue, `msqueue2.kl`'s code verbatim, from
the runner's exact configuration**: every final configuration under
`Arch.tso` has `r12 = n1` and `r13 = n2` in the dequeuer. -/
theorem x64_msqueue2_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [msq2P0D, msq2P1D] msq2InitMemV) c)
    (hf : c.final = true) :
    ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.get64 .r12 = 0x1000100 ∧
      th1.st.st.1.regs.get64 .r13 = 0x1000200 := by
  have h := x64_msqueue2_envG_runner (layout := msq2LayoutV) msq2DeclsD_sized
    (by rw [symV_head, symV_tail]; decide) (by rw [symV_head, symV_s]; decide)
    (by rw [symV_head, symV_n1]; decide) (by rw [symV_head, symV_n2]; decide)
    (by rw [symV_tail, symV_s]; decide) (by rw [symV_tail, symV_n1]; decide)
    (by rw [symV_tail, symV_n2]; decide) (by rw [symV_s, symV_n1]; decide)
    (by rw [symV_s, symV_n2]; decide) (by rw [symV_n1, symV_n2]; decide)
    (by rw [symV_n1]; decide) (by rw [symV_n2]; decide)
    msq2P0D_start msq2P1D_start msq2D_initV hc hf
  rwa [symV_n1, symV_n2] at h

end Kraken.Promising.X64.EnvG.MsQueueX.Concrete

#print axioms Kraken.Promising.X64.EnvG.MsQueueX.x64_msqueue2_envG_runner
#print axioms Kraken.Promising.X64.EnvG.MsQueueX.Concrete.x64_msqueue2_envG_runner_concrete
