/-
**`treiber2.kl` from the runner's exact configuration**: `x64_treiber2_envG_runner`, `x64_treiber2_envG_verbatim` for threads
that carry the `.kl` runner's declarations (the header types `top`, `n1`,
`n2` `uint64_t`: strict sized, `Decls.Sized`), and its concrete instance
`x64_treiber2_envG_runner_concrete` (`runnerMatchesD`: declarations and
initial memory included).

The proof is `X64Treiber2Public`'s with the D forms of
`EnvG/X64DeclsLink.lean`: `wRuleVD` (`ThreadRuleRXF.ofSafelyEnvGFCAdjXMD`
at `MaskOf.refl`), `invWV_initD` (`invGFCAdjXMD_init`),
`RelPureSpecQX.HoldsD`, `final_of_relPureSafelyQX_tsoFD`. The old theorems
are unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64Treiber2Public
import Kraken.Promising.SLR.EnvG.X64Treiber2Concrete
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64RunnerCommon

namespace Kraken.Promising.X64.EnvG.Treiber2X

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (initVal_eq)
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 mem_sAll8 split_sAll)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2ImageV)]

/-! ## The rule and the start, with declarations -/

/-- **Thread `w`'s rule with strict sized declarations `ds`** (`wRuleV`
through `ofSafelyEnvGFCAdjXMD`). -/
noncomputable def wRuleVD {ds : Decls} (hsz : ds.Sized) (P : Params) (w : Nat) (hw : w < 2) :
    ThreadRuleRXF (I := isa) Arch.tso (TB2X P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjXMD (S := sAll) (post := postWV P w) hsz (MaskOf.refl _) (plan_valid P w) sAll_le16
    treiber2ImageV_phase1FX (postWV_end P w) (workerV_stuck _) (hB_wV P hw)

/-- **Thread `w` at its start with declarations `ds`** (`StartWV` with
`decls = ds`). -/
structure StartWVD (ds : Decls) (n : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout treiber2ImageV
  decls : s.decls = ds
  pc : s.st.2 = labT2 "worker"
  endPc : s.endPc = labT2 "done"
  rbx : s.st.1.regs.get64 .rbx = n
  dmem : ∀ k, s.st.1.dmem.get? k = none

omit [Executable.ValidLayout (layout treiber2ImageV)] in
theorem StartWVD.d8 {ds : Decls} {n : BitVec 64} {s : State} (h : StartWVD ds n s) :
    ∀ a, Mem.loadInt s.st.1.dmem a 8 = none :=
  fun a => (split_sAll h.dmem).loadInt_none (mem_sAll8 a) (by decide) (by decide)

section Start

variable {ds : Decls} {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **Thread `w`'s initial invariant with declarations.** -/
theorem invWV_initD (hsz : ds.Sized) (hL : TLocs tPV) {w : Nat} (hw : w < 2) {s : isa.State}
    (hs : [s0, s1][w]? = some s) (hS : StartWVD ds (tPV.n w) s)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal tPV.top = 0) :
    (wRuleVD hsz tPV w hw).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem tPV w)
      (ghost₀ tPV) := by
  have htr : tRes (Config.init [s0, s1] initMem).mem tPV w = thrRes (Config.init [s0, s1] initMem).mem tPV w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  rw [htr]
  have hst : s.st = (s.st.1, labT2 "worker") := Prod.ext rfl hS.pc
  refine invGFCAdjXMD_init (s := s) hs rfl ⟨hS.exe, hS.decls, hS.endPc, split_sAll hS.dmem, ?_⟩
  rw [hst]
  exact TreiberAbs.Safely.uncountT (workerV_envGCAdj tPV w hL hw rfl s.st.1 (_, 0)
    ⟨hS.rbx, hS.d8, pu_init tPV hL hw _ hT0⟩)

end Start

/-- **The all-release specifications hold at the start states with
declarations.** -/
theorem treiber2NoNTSpecV_initD {ds : Decls} {s0 s1 : State} (h0 : StartWVD ds (tPV.n 0) s0)
    (h1 : StartWVD ds (tPV.n 1) s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (treiber2NoNTSpecV tid).HoldsD ds s := by
  have H : ∀ {n : BitVec 64} {s : State}, StartWVD ds n s → (treiber2NoNTSpecV 0).HoldsD ds s := fun {_ s} hS => by
    refine ⟨hS.exe, hS.endPc, hS.decls, split_sAll hS.dmem, ?_⟩
    rw [show s.st = (s.st.1, labT2 "worker") from Prod.ext rfl hS.pc]
    exact TreiberAbs.Safely.uncountT (workerV_noNT _ ((), 0) hS.d8)
  intro tid s hs
  rcases tid with _ | _ | i
  · cases hs; exact H h0
  · cases hs; exact H h1
  · simp at hs

/-- **The `NPSafeF` side for the verbatim `treiber2` with declarations.** -/
theorem treiber2V_npSafeFD {ds : Decls} (hsz : ds.Sized) (hL : TLocs tPV) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartWVD ds (tPV.n 0) s0) (h1 : StartWVD ds (tPV.n 1) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal tPV.top = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.tso (TB2X tPV) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem tPV tid) (ghost₀ tPV) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invWV_initD hsz hL (by decide) rfl h0 hT0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invWV_initD hsz hL (by decide) rfl h1 hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The two-thread Treiber stack `treiber2.kl` for x64 under `Arch.tso`,
the `.kl`'s code verbatim, with the runner's declarations**:
`x64_treiber2_envG_verbatim` for threads whose declarations are strict sized
(`ds.Sized`: the `.kl` runner's, from the typed header). -/
theorem x64_treiber2_envG_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (h1 : symT2 "top" ≠ symT2 "n1")
    (h2 : symT2 "top" ≠ symT2 "n2") (hn : symT2 "n1" ≠ symT2 "n2") (hn1 : symT2 "n1" ≠ 0) (hn2 : symT2 "n2" ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartWVD ds (symT2 "n1") s0)
    (h1' : StartWVD ds (symT2 "n2") s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨symT2 "top", 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th0 th1, cfg.threads[0]? = some th0 ∧ cfg.threads[1]? = some th1 ∧
      ((th0.st.st.1.regs.get64 .r12 = symT2 "n1" ∧ th1.st.st.1.regs.get64 .r12 = symT2 "n2") ∨
        (th0.st.st.1.regs.get64 .r12 = symT2 "n2" ∧ th1.st.st.1.regs.get64 .r12 = symT2 "n1")) := by
  have hL := tLocs_tPV h1 h2 hn hn1 hn2
  refine final_of_relPureSafelyQX_tsoFD (theorem1FChain Arch.tso fuel) (B := TB2X tPV)
    (Φ := Treiber2FinalX (symT2 "n1") (symT2 "n2"))
    (erase_init hL _) (ghost₀_pend _) treiber2NoNTSpecV (fun _ => ds) (fun _ => hsz) (treiber2NoNTSpecV_initD h0 h1')
    (treiber2V_npSafeFD hsz hL h0 h1' hT0) hc hf fun rF' g' E' hle hsize hB => ?_
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw tPV).mono hle
  have hno := Config.final_not_outstanding hf
  obtain ⟨w0, hw0, th, hth, hd0⟩ := hB 0 (Config.final_done hf hi0)
  obtain ⟨w1, hw1, th', hth', hd1⟩ := hB 1 (Config.final_done hf hi1)
  by_cases hww : w0 = w1
  · subst hww
    exact (TreiberCommon.acq_pair_false E' hi0 hi1 (by decide) hd0.1 hd1.1).elim
  rcases w0 with _ | _ | w0
  · rcases w1 with _ | _ | w1
    · exact absurd rfl hww
    · exact ⟨th, th', hth, hth', final_values E' hW hL hno hi0 hi1 hd0 hd1⟩
    · omega
  · rcases w1 with _ | _ | w1
    · have := final_values E' hW hL hno hi1 hi0 hd1 hd0
      exact ⟨th', th, hth', hth, this⟩
    · exact absurd rfl hww
    · omega
  · omega

end Kraken.Promising.X64.EnvG.Treiber2X

/-! ## The runner's configuration -/

namespace Kraken.Promising.X64.EnvG.Treiber2X.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.Treiber2X Kraken.Promising.SLR.EnvG

/-- The runner's declarations for the typed `treiber2.kl`: `top`, `n1`, `n2`,
8-byte words (strict). -/
def treiber2DeclsD : Decls := { locs := [⟨0x1000000, 8⟩, ⟨0x1000100, 8⟩, ⟨0x1000200, 8⟩], unsizedDefault := false }

theorem treiber2DeclsD_sized : treiber2DeclsD.Sized := ⟨rfl, by decide⟩

/-- The threads as the runner prepares them, declarations included. -/
def treiber2P0D : X64.State := { treiber2P0 with decls := treiber2DeclsD }
def treiber2P1D : X64.State := { treiber2P1 with decls := treiber2DeclsD }

/-- The runner's configuration is `Config.init [treiber2P0D, treiber2P1D]
treiber2InitMemV` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesD (src : String) : Bool :=
  runnerMatchesDL src [treiber2P0D, treiber2P1D] treiber2InitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD treiber2Kl

section
attribute [local instance] treiber2LayoutV

theorem treiber2P0D_start : StartWVD treiber2DeclsD (symT2 "n1") treiber2P0D :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labT2 "worker"; rw [labT2_at 0]; decide,
    by show (0x100000 + 12 : Int64) = labT2 "done"; rw [labT2_at 15]; decide,
    by rw [symT2_n1]; simp [treiber2P0D, treiber2P0, Reg64s.get64, Reg64s.set64],
    fun _ => by simp [treiber2P0D, treiber2P0]⟩

theorem treiber2P1D_start : StartWVD treiber2DeclsD (symT2 "n2") treiber2P1D :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labT2 "worker"; rw [labT2_at 0]; decide,
    by show (0x100000 + 12 : Int64) = labT2 "done"; rw [labT2_at 15]; decide,
    by rw [symT2_n2]; simp [treiber2P1D, treiber2P1, Reg64s.get64, Reg64s.set64],
    fun _ => by simp [treiber2P1D, treiber2P1]⟩

end

/-- **The two-thread Treiber stack, `treiber2.kl`'s code verbatim, from the
runner's exact configuration**: every final configuration under `Arch.tso`
has `(0:r12 = n1 ∧ 1:r12 = n2) ∨ (0:r12 = n2 ∧ 1:r12 = n1)`. -/
theorem x64_treiber2_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [treiber2P0D, treiber2P1D] treiber2InitMemV) c)
    (hf : c.final = true) :
    ∃ th0 th1, c.threads[0]? = some th0 ∧ c.threads[1]? = some th1 ∧
      ((th0.st.st.1.regs.get64 .r12 = 0x1000100 ∧ th1.st.st.1.regs.get64 .r12 = 0x1000200) ∨
        (th0.st.st.1.regs.get64 .r12 = 0x1000200 ∧ th1.st.st.1.regs.get64 .r12 = 0x1000100)) := by
  have h := x64_treiber2_envG_runner (layout := treiber2LayoutV) treiber2DeclsD_sized
    (by rw [symT2_top, symT2_n1]; decide) (by rw [symT2_top, symT2_n2]; decide)
    (by rw [symT2_n1, symT2_n2]; decide) (by rw [symT2_n1]; decide) (by rw [symT2_n2]; decide)
    treiber2P0D_start treiber2P1D_start (by rw [symT2_top]; simp only [Config.init_mem]; decide) hc hf
  rwa [symT2_n1, symT2_n2] at h

end Kraken.Promising.X64.EnvG.Treiber2X.Concrete

#print axioms Kraken.Promising.X64.EnvG.Treiber2X.x64_treiber2_envG_runner
#print axioms Kraken.Promising.X64.EnvG.Treiber2X.Concrete.x64_treiber2_envG_runner_concrete
