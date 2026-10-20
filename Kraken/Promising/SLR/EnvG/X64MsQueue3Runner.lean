/-
**`msqueue3.kl` from the runner's exact configuration**: `x64_msqueue3_envG_runner`, `x64_msqueue3_envG_verbatim` for threads
that carry the `.kl` runner's declarations (the header types `s`, `n1`,
`n2`, `head`, `tail` `uint64_t`: strict sized, `Decls.Sized`), and its
concrete instance `x64_msqueue3_envG_runner_concrete` (`runnerMatchesD`:
declarations and initial memory included).

The proof is `X64MsQueue3Public`'s with the D forms of
`EnvG/X64DeclsLink.lean`: the enqueuer over its mask and the dequeuers at
the whole image, all `ThreadRuleRXF.ofSafelyEnvGFCAdjXMD`,
`invGFCAdjXMD_init`, `RelPureSpecQX.HoldsD`,
`final_of_relPureSafelyQX_tsoFD`. The old theorems are unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue3Public
import Kraken.Promising.SLR.EnvG.X64MsQueue3Concrete
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64RunnerCommon

namespace Kraken.Promising.X64.EnvG.MsQueue3X

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 mem_sAll8 split_sAll)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq3ImageV)]

/-! ## The rules and the start, with declarations -/

/-- **The verbatim enqueuer's rule with strict sized declarations `ds`**
(`enqRule3` through `ofSafelyEnvGFCAdjXMD`, over the mask `msq3ImageM`). -/
noncomputable def enqRule3D {ds : Decls} (hsz : ds.Sized) (P : Params) :
    ThreadRuleRXF (I := isa) Arch.tso (MQ3 P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjXMD (S := sAll) (post := postEV3 P) hsz msq3ImageM_mask (planE_valid P) sAll_le16
    msq3ImageM_phase1FX (postEV3_end P) (enq3M_stuck _) (hB_EV3 P)

/-- **The verbatim dequeuers' rule with strict sized declarations `ds`**
(`deqRule3` through `ofSafelyEnvGFCAdjXMD` at the whole image). -/
noncomputable def deqRule3D {ds : Decls} (hsz : ds.Sized) (P : Params) (w : Nat) (hw : w = 1 ∨ w = 2) :
    ThreadRuleRXF (I := isa) Arch.tso (MQ3 P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjXMD (S := sAll) (post := postDV3 P w) hsz (MaskOf.refl _) (planD3_valid P w)
    sAll_le16 msq3ImageV_phase1FX (postDV3_end P w) (deq3V_stuck _) (hB_DV3 P hw)

/-- **The verbatim enqueuer at its start with declarations `ds`**
(`StartEV3` with `decls = ds`). -/
structure StartEV3D (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout msq3ImageV
  decls : s.decls = ds
  pc : s.st.2 = labV3 "enqueuer"
  endPc : s.endPc = labV3 "edone"
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **A verbatim dequeuer at its start with declarations `ds`** (`StartDV3`
with `decls = ds`). -/
structure StartDV3D (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout msq3ImageV
  decls : s.decls = ds
  pc : s.st.2 = labV3 "dequeuer"
  endPc : s.endPc = labV3 "ddone"
  dmem : ∀ k, s.st.1.dmem.get? k = none

section Start

variable {ds : Decls} {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim enqueuer's initial invariant with declarations.** -/
theorem invEV3_initD (hsz : ds.Sized) (hL : QLocs params3V) (hS : StartEV3D ds s0) :
    (enqRule3D hsz params3V).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem params3V 0) (ghost₀ params3V) := by
  have hst : s0.st = (s0.st.1, labV3 "enqueuer") := Prod.ext rfl hS.pc
  refine invGFCAdjXMD_init (s := s0) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, split_sAll hS.dmem, ?_⟩
  rw [hst]
  exact TreiberAbs.Safely.uncountT (enq3M_envGCAdj params3V hL rfl rfl rfl rfl s0.st.1 (_, 0)
    ⟨d8_of_dmem hS.dmem, e0_init3 params3V _⟩)

/-- **A verbatim dequeuer's initial invariant with declarations.** -/
theorem invDV3_initD (hsz : ds.Sized) (hL : QLocs params3V) {w : Nat} (hw : w = 1 ∨ w = 2) {s : isa.State}
    (hs : [s0, s1, s2][w]? = some s) (hS : StartDV3D ds s)
    (hi : InitV (Config.init [s0, s1, s2] initMem).mem params3V) :
    (deqRule3D hsz params3V w hw).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem params3V w) (ghost₀ params3V) := by
  have htr : tRes3 (Config.init [s0, s1, s2] initMem).mem params3V w =
      resD3 (Config.init [s0, s1, s2] initMem).mem params3V w := by
    rcases hw with rfl | rfl <;> rfl
  rw [htr]
  have hst : s.st = (s.st.1, labV3 "dequeuer") := Prod.ext rfl hS.pc
  refine invGFCAdjXMD_init (s := s) hs rfl ⟨hS.exe, hS.decls, hS.endPc, split_sAll hS.dmem, ?_⟩
  rw [hst]
  exact TreiberAbs.Safely.uncountT (deq3V_envGCAdj' params3V hL hw rfl rfl s.st.1 (_, 0)
    ⟨d8_of_dmem hS.dmem, l0_init3 params3V w (by omega) _ hi⟩)

end Start

/-- **The all-release specifications hold at the start states with
declarations.** -/
theorem msq3NoNTSpecV_initD {ds : Decls} {s0 s1 s2 : State} (h0 : StartEV3D ds s0) (h1 : StartDV3D ds s1)
    (h2 : StartDV3D ds s2) :
    ∀ tid s, [s0, s1, s2][tid]? = some s → (msq3NoNTSpecV tid).HoldsD ds s := by
  have H : ∀ {s : State}, StartDV3D ds s → ∀ i, (msq3NoNTSpecV (i + 1)).HoldsD ds s := fun {s} hS i => by
    refine ⟨hS.exe, hS.endPc, hS.decls, split_sAll hS.dmem, ?_⟩
    rw [show s.st = (s.st.1, labV3 "dequeuer") from Prod.ext rfl hS.pc]
    exact TreiberAbs.Safely.uncountT (deq3V_noNT _ ((), 0) (d8_of_dmem hS.dmem))
  intro tid s hs
  rcases tid with _ | _ | _ | i
  · cases hs
    refine ⟨h0.exe, h0.endPc, h0.decls, split_sAll h0.dmem, ?_⟩
    rw [show s0.st = (s0.st.1, labV3 "enqueuer") from Prod.ext rfl h0.pc]
    exact TreiberAbs.Safely.uncountT (enq3V_noNT _ ((), 0) (d8_of_dmem h0.dmem))
  · cases hs; exact H h1 0
  · cases hs; exact H h2 1
  · simp at hs

/-- **The `NPSafeF` side for the verbatim `msqueue3` with declarations.** -/
theorem msq3V_npSafeFD {ds : Decls} (hsz : ds.Sized) (hL : QLocs params3V) {s0 s1 s2 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartEV3D ds s0) (h1 : StartDV3D ds s1) (h2 : StartDV3D ds s2)
    (hi : InitV (Config.init [s0, s1, s2] initMem).mem params3V) :
    ∀ tid, tid < [s0, s1, s2].length → ∀ k j, NPSafeF (model isa) Arch.tso (MQ3 params3V) tid k j True
      (Config.init [s0, s1, s2] initMem) (tRes3 (Config.init [s0, s1, s2] initMem).mem params3V tid)
      (ghost₀ params3V) := by
  intro tid htid k j
  rcases tid with _ | _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invEV3_initD hsz hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDV3_initD hsz hL (.inl rfl) rfl h1 hi)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDV3_initD hsz hL (.inr rfl) rfl h2 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The Michael–Scott queue `msqueue3.kl` for x64 under `Arch.tso`, the
`.kl`'s code verbatim, with the runner's declarations**:
`x64_msqueue3_envG_verbatim` for threads whose declarations are strict sized
(`ds.Sized`: the `.kl` runner's, from the typed header). -/
theorem x64_msqueue3_envG_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (hht : symV3 "head" ≠ symV3 "tail")
    (hhs : symV3 "head" ≠ symV3 "s") (hh1 : symV3 "head" ≠ symV3 "n1") (hh2 : symV3 "head" ≠ symV3 "n2")
    (hts : symV3 "tail" ≠ symV3 "s") (ht1 : symV3 "tail" ≠ symV3 "n1") (ht2 : symV3 "tail" ≠ symV3 "n2")
    (hs1 : symV3 "s" ≠ symV3 "n1") (hs2 : symV3 "s" ≠ symV3 "n2") (h12 : symV3 "n1" ≠ symV3 "n2")
    (hn1 : symV3 "n1" ≠ 0) (hn2 : symV3 "n2" ≠ 0) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEV3D ds s0) (h1 : StartDV3D ds s1) (h2 : StartDV3D ds s2)
    (hi : InitV (Config.init [s0, s1, s2] initMem).mem params3V)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1, s2] initMem) cfg)
    (hf : cfg.final = true) :
    MsQueue3FinalX (symV3 "n1") (symV3 "n2") cfg := by
  have hL := qLocs_params3V hht hhs hh1 hh2 hts ht1 ht2 hs1 hs2 h12 hn1 hn2
  refine final_of_relPureSafelyQX_tsoFD (theorem1FChain Arch.tso fuel) (B := MQ3 params3V)
    (Φ := MsQueue3FinalX (symV3 "n1") (symV3 "n2"))
    (erase_init3 hL _) (ghost₀_pend _) msq3NoNTSpecV (fun _ => ds) (fun _ => hsz) (msq3NoNTSpecV_initD h0 h1 h2)
    (msq3V_npSafeFD hsz hL h0 h1 h2 hi) hc hf fun rF' g' E' hle hsize hB => ?_
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi2 : (2 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw params3V).mono hle
  have fin : ∀ k1 k2, k1 < cfg.threads.size → k2 < cfg.threads.size →
      (∃ th, cfg.threads[1]? = some th ∧ DoneD3 cfg.mem params3V 1 (rF' k1) (th.st.st.1.regs.get64 .r12) ∧
        InitV cfg.mem params3V ∧ ∀ x, params3V.IsW x → 1 ≤ (rF' k1).acq x 0) →
      (∃ th, cfg.threads[2]? = some th ∧ DoneD3 cfg.mem params3V 2 (rF' k2) (th.st.st.1.regs.get64 .r12) ∧
        InitV cfg.mem params3V) →
      MsQueue3FinalX (symV3 "n1") (symV3 "n2") cfg := by
    rintro k1 k2 hk1 hk2 ⟨th1, hth1, hd1, hiv, hacq⟩ ⟨th2, hth2, hd2, -⟩
    exact ⟨th1, th2, hth1, hth2, final_values3 E' hW hL hiv
      (fun x hx => TreiberCommon.total_acq_of_ge E' hk1 (hacq x hx)) rfl hk1 hk2 hd1 hd2⟩
  have hb0 := hB 0 (Config.final_done hf hi0)
  have hb1 := hB 1 (Config.final_done hf hi1)
  have hb2 := hB 2 (Config.final_done hf hi2)
  rcases hb0 with m0 | ⟨m0, d0⟩ | ⟨m0, d0⟩ <;> rcases hb1 with m1 | ⟨m1, d1⟩ | ⟨m1, d1⟩ <;>
    rcases hb2 with m2 | ⟨m2, d2⟩ | ⟨m2, d2⟩
  all_goals first
    | exact (mark_pair_false E' hi0 hi1 (by decide) m0 m1).elim
    | exact (mark_pair_false E' hi0 hi2 (by decide) m0 m2).elim
    | exact (mark_pair_false E' hi1 hi2 (by decide) m1 m2).elim
    | exact fin _ _ hi0 hi1 d0 d1
    | exact fin _ _ hi0 hi2 d0 d2
    | exact fin _ _ hi1 hi0 d1 d0
    | exact fin _ _ hi1 hi2 d1 d2
    | exact fin _ _ hi2 hi0 d2 d0
    | exact fin _ _ hi2 hi1 d2 d1

end Kraken.Promising.X64.EnvG.MsQueue3X

/-! ## The runner's configuration -/

namespace Kraken.Promising.X64.EnvG.MsQueue3X.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.MsQueueX Kraken.Promising.X64.EnvG.MsQueue3X Kraken.Promising.SLR.EnvG

/-- The runner's declarations for the typed `msqueue3.kl`: `s`, `n1`, `n2`,
`head`, `tail`, 8-byte words (strict). -/
def msq3DeclsD : Decls :=
  { locs := [⟨0x1000000, 8⟩, ⟨0x1000100, 8⟩, ⟨0x1000200, 8⟩, ⟨0x1000300, 8⟩, ⟨0x1000400, 8⟩],
    unsizedDefault := false }

theorem msq3DeclsD_sized : msq3DeclsD.Sized := ⟨rfl, by decide⟩

/-- The threads as the runner prepares them, declarations included. -/
def msq3P0D : X64.State := { msq3P0 with decls := msq3DeclsD }
def msq3PDD : X64.State := { msq3PD with decls := msq3DeclsD }

/-- The runner's configuration is `Config.init [msq3P0D, msq3PDD, msq3PDD]
msq3InitMemV` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesD (src : String) : Bool :=
  runnerMatchesDL src [msq3P0D, msq3PDD, msq3PDD] msq3InitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD msq3Kl

section
attribute [local instance] msq3LayoutV

set_option maxRecDepth 8000

theorem msq3P0D_start : StartEV3D msq3DeclsD msq3P0D :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labV3 "enqueuer"; rw [labV3_at 0]; decide,
    by show (0x100000 + 20 : Int64) = labV3 "edone"; rw [labV3_at 23]; decide,
    fun _ => by simp [msq3P0D, msq3P0]⟩

theorem msq3PDD_start : StartDV3D msq3DeclsD msq3PDD :=
  ⟨rfl, rfl, by show (0x100000 + 20 : Int64) = labV3 "dequeuer"; rw [labV3_at 24]; decide,
    by show (0x100000 + 39 : Int64) = labV3 "ddone"; rw [labV3_at 47]; decide,
    fun _ => by simp [msq3PDD, msq3PD]⟩

theorem msq3D_initV : InitV (Config.init (I := isa) [msq3P0D, msq3PDD, msq3PDD] msq3InitMemV).mem params3V := by
  simp only [params3V, symV3_s, symV3_n1, symV3_n2, symV3_head, symV3_tail]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Params.head, Params.tail, Params.ls, Params.l1, Params.l2, Config.init_mem] <;> decide

/-- **The Michael–Scott queue, `msqueue3.kl`'s code verbatim, from the
runner's exact configuration**: every final configuration under `Arch.tso`
has `(1:r12, 2:r12)` among `(n1,n2)`, `(n2,n1)`, `(n1,0)`, `(0,n1)`,
`(0,0)`. -/
theorem x64_msqueue3_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [msq3P0D, msq3PDD, msq3PDD] msq3InitMemV) c)
    (hf : c.final = true) :
    MsQueue3FinalX 0x1000100 0x1000200 c := by
  have h := x64_msqueue3_envG_runner (layout := msq3LayoutV) msq3DeclsD_sized
    (by rw [symV3_head, symV3_tail]; decide) (by rw [symV3_head, symV3_s]; decide)
    (by rw [symV3_head, symV3_n1]; decide) (by rw [symV3_head, symV3_n2]; decide)
    (by rw [symV3_tail, symV3_s]; decide) (by rw [symV3_tail, symV3_n1]; decide)
    (by rw [symV3_tail, symV3_n2]; decide) (by rw [symV3_s, symV3_n1]; decide)
    (by rw [symV3_s, symV3_n2]; decide) (by rw [symV3_n1, symV3_n2]; decide)
    (by rw [symV3_n1]; decide) (by rw [symV3_n2]; decide)
    msq3P0D_start msq3PDD_start msq3PDD_start msq3D_initV hc hf
  rwa [symV3_n1, symV3_n2] at h

end

end Kraken.Promising.X64.EnvG.MsQueue3X.Concrete

#print axioms Kraken.Promising.X64.EnvG.MsQueue3X.x64_msqueue3_envG_runner
#print axioms Kraken.Promising.X64.EnvG.MsQueue3X.Concrete.x64_msqueue3_envG_runner_concrete
