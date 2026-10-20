/-
**`treiber_pp.kl` from the runner's exact configuration**: `x64_treiber_pp_envG_runner`, `x64_treiber_pp_envG_verbatim` for
threads that carry the `.kl` runner's declarations (the header types `top`
`uint64_t` and `n1` `uint32_t`, the node's 4-byte value; its 8-byte `next`
at `n1 + 8` is undeclared, its own footprint in strict mode: `Decls.Sized`),
and its concrete instance `x64_treiber_pp_envG_runner_concrete`
(`runnerMatchesD`: declarations and initial memory included).

The proof is `X64TreiberAbsPublic`'s with the D forms of
`EnvG/X64DeclsLink.lean`: the pusher over the mask
(`ThreadRuleRXF.ofSafelyEnvGFCXMD` at `treiberImageM_mask`), the popper at
the whole image (`ofSafelyEnvGFCXMD` at `MaskOf.refl`), `invGFCXMD_init`,
`RelPureSpecQX.HoldsD`, `final_of_relPureSafelyQX_tsoFD`. The old theorems
are unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64TreiberAbsPublic
import Kraken.Promising.SLR.EnvG.X64TreiberAbsConcrete
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64RunnerCommon

namespace Kraken.Promising.X64.EnvG.TreiberAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.TreiberCommon
open Kraken.Promising.X64.EnvG.TreiberX

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberImageV)]

/-! ## The rules with declarations -/

/-- **The verbatim pusher's rule with strict sized declarations `ds`**
(`pushRuleV` through `ofSafelyEnvGFCXMD`, over the mask `treiberImageM`). -/
noncomputable def pushRuleVD {ds : Decls} (hsz : ds.Sized) (t n : BitVec 64) (hL : TLocs (tPX t n)) :
    ThreadRuleRXF (I := isa) Arch.tso (TBX (tPX t n) n) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCXMD (S := pushS t n) (post := postPushV (tPX t n)) hsz treiberImageM_mask
    (pushPlan_valid hL) (pushS_le16 t n) treiberImageM_phase1FX (postPushV_end _) (pusherM_stuck _) (hB_pushV _ n)

/-- **The verbatim popper's rule with strict sized declarations `ds`**
(`popRuleV` through `ofSafelyEnvGFCXMD` at the whole image). -/
noncomputable def popRuleVD {ds : Decls} (hsz : ds.Sized) (t n : BitVec 64) (hL : TLocs (tPX t n)) :
    ThreadRuleRXF (I := isa) Arch.tso (TBX (tPX t n) n) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCXMD (S := sAll) (post := postPopV n) hsz (MaskOf.refl _) (popPlan_valid hL) sAll_le16
    treiberImageV_phase1FX (postPopV_end n) (popperV_stuck _) (hB_popV _ n)

/-! ## The start with declarations -/

/-- **The verbatim pusher at its start with declarations `ds`**
(`StartPushV` with `decls = ds`). -/
structure StartPushVD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout treiberImageV
  decls : s.decls = ds
  pc : s.st.2 = labT "pusher"
  endPc : s.endPc = labT "pdone"
  rdi : s.st.1.regs.get64 .rdi = symT "top"
  rbx : s.st.1.regs.get64 .rbx = symT "n1"
  split : Split (pushS (symT "top") (symT "n1")) s.st.1.dmem

/-- **The verbatim popper at its start with declarations `ds`**
(`StartPopV` with `decls = ds`). -/
structure StartPopVD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout treiberImageV
  decls : s.decls = ds
  pc : s.st.2 = labT "popper"
  endPc : s.endPc = labT "qdone"
  rdi : s.st.1.regs.get64 .rdi = symT "top"
  dmem : ∀ k, s.st.1.dmem.get? k = none

omit [Executable.ValidLayout (layout treiberImageV)] in
theorem StartPushVD.frame {ds : Decls} {s : State} (h : StartPushVD ds s) :
    PFrameX (symT "top") (symT "n1") s.st.1 :=
  ⟨h.rdi, h.rbx, h.split.loadInt_none (by simp) (by decide) (by decide),
    h.split.loadInt_none (by simp) (by decide) (by decide), h.split.loadInt_none (by simp) (by decide) (by decide)⟩

omit [Executable.ValidLayout (layout treiberImageV)] in
theorem StartPopVD.frame {ds : Decls} {s : State} (h : StartPopVD ds s) : QFrameX (symT "top") s.st.1 :=
  ⟨h.rdi, fun a => (split_sAll h.dmem).loadInt_none (mem_sAll8 a) (by decide) (by decide),
    fun a => (split_sAll h.dmem).loadInt_none (mem_sAll4 a) (by decide) (by decide)⟩

section Start

variable {ds : Decls} {sP sQ : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim pusher's initial invariant with declarations.** -/
theorem invPushV_initD (hsz : ds.Sized) (htn : symT "top" ≠ symT "n1" + 8) (hP : StartPushVD ds sP) :
    (pushRuleVD hsz (symT "top") (symT "n1") (tLocs_tPX htn)).Inv True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tPX (symT "top") (symT "n1")) 0)
      (ghost₀ (tPX (symT "top") (symT "n1"))) := by
  have hL := tLocs_tPX htn
  have hst : sP.st = (sP.st.1, labT "pusher") := Prod.ext rfl hP.pc
  refine invGFCXMD_init (s := sP) rfl rfl ⟨hP.exe, hP.decls, hP.endPc, hP.split, ?_⟩
  rw [hst]
  refine Safely.uncountT (pusherM_envGC _ _ ⟨symT "top", 1⟩ hL sP.st.1 (_, 0) ⟨hP.frame, ghost₀_gw _, ?_⟩)
  have htd := hL.top_d; have htn' := hL.top_n; have hdn := hL.d_n
  simp only [tRes, ↓reduceIte, pushRes, Res.initOf, Perm.init, pushFrac]
  simp only [Ne.symm htd, Ne.symm htn', ↓reduceIte, true_or, or_true, true_and]
  refine ⟨by grind, fun p hp => by rw [hp.2]⟩

/-- **The verbatim popper's initial invariant with declarations.** -/
theorem invPopV_initD (hsz : ds.Sized) (htn : symT "top" ≠ symT "n1" + 8) (hQ : StartPopVD ds sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "top", 8⟩ = 0) :
    (popRuleVD hsz (symT "top") (symT "n1") (tLocs_tPX htn)).Inv True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tPX (symT "top") (symT "n1")) 1)
      (ghost₀ (tPX (symT "top") (symT "n1"))) := by
  have hL := tLocs_tPX htn
  have hst : sQ.st = (sQ.st.1, labT "popper") := Prod.ext rfl hQ.pc
  refine invGFCXMD_init (s := sQ) rfl rfl ⟨hQ.exe, hQ.decls, hQ.endPc, split_sAll hQ.dmem, ?_⟩
  rw [hst]
  refine Safely.uncountT (popperV_envGC _ _ ⟨symT "top", 1⟩ hL sQ.st.1 (_, 0) ⟨hQ.frame, ghost₀_gw _, ?_⟩)
  have htt := hL.top_t
  simp only [tRes, popRes, Res.initOf, Perm.init, popFrac]
  simp [Ne.symm htt, Views.getFwd]
  exact ⟨by grind, hT0⟩

end Start

set_option maxRecDepth 8000 in
/-- **The all-release specifications hold at the start states with
declarations.** -/
theorem treiberNoNTSpecV_initD {ds : Decls} {sP sQ : State} (hP : StartPushVD ds sP) (hQ : StartPopVD ds sQ) :
    ∀ tid s, [sP, sQ][tid]? = some s → (treiberNoNTSpecV tid).HoldsD ds s
  | 0, s, hs => by
    cases hs
    refine ⟨hP.exe, hP.endPc, hP.decls, hP.split, ?_⟩
    rw [show sP.st = (sP.st.1, labT "pusher") from Prod.ext rfl hP.pc]
    exact Safely.uncountT (pusherV_noNT _ _ sP.st.1 ((), 0) hP.frame)
  | 1, s, hs => by
    cases hs
    refine ⟨hQ.exe, hQ.endPc, hQ.decls, split_sAll hQ.dmem, ?_⟩
    rw [show sQ.st = (sQ.st.1, labT "popper") from Prod.ext rfl hQ.pc]
    exact Safely.uncountT (popperV_noNT _ sQ.st.1 ((), 0) hQ.frame)

/-- **The `NPSafeF` side for the verbatim `treiber_pp` with declarations.** -/
theorem treiberV_npSafeFD {ds : Decls} (hsz : ds.Sized) (htn : symT "top" ≠ symT "n1" + 8) {sP sQ : isa.State}
    {initMem : List (Loc × Val)} (hP : StartPushVD ds sP) (hQ : StartPopVD ds sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "top", 8⟩ = 0) :
    ∀ tid, tid < [sP, sQ].length → ∀ k j, NPSafeF (model isa) Arch.tso (TBX (tPX (symT "top") (symT "n1")) (symT "n1"))
      tid k j True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tPX (symT "top") (symT "n1")) tid)
      (ghost₀ (tPX (symT "top") (symT "n1"))) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPushV_initD hsz htn hP)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPopV_initD hsz htn hQ hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The Treiber stack `treiber_pp.kl` for x64 under `Arch.tso`, the
`.kl`'s code verbatim, with the runner's declarations**:
`x64_treiber_pp_envG_verbatim` for threads whose declarations are strict
sized (`ds.Sized`: the `.kl` runner's, from the typed header). -/
theorem x64_treiber_pp_envG_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (htn : symT "top" ≠ symT "n1" + 8)
    {sP sQ : isa.State} {initMem : List (Loc × Val)} (hP : StartPushVD ds sP) (hQ : StartPopVD ds sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "top", 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sP, sQ] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ th.st.st.1.regs.get64 .r10 = symT "n1" ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r11) = 1 := by
  have hL := tLocs_tPX htn
  refine final_of_relPureSafelyQX_tsoFD (theorem1FChain Arch.tso fuel)
    (B := TBX (tPX (symT "top") (symT "n1")) (symT "n1")) (Φ := PopperFinalX (symT "n1"))
    (erase_init hL _) (ghost₀_pend _) treiberNoNTSpecV (fun _ => ds) (fun _ => hsz) (treiberNoNTSpecV_initD hP hQ)
    (treiberV_npSafeFD hsz htn hP hQ hT0) hc hf fun rF' g' E' _ hsize hB => ?_
  have h0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have h1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  rcases hB 1 (Config.final_done hf h1) with hfin | hq1
  · exact hfin
  rcases hB 0 (Config.final_done hf h0) with hfin | hq0
  · exact hfin
  have := E'.q_add_le_one h0 h1 (by decide) (tPX (symT "top") (symT "n1")).top
  exfalso
  grind

end Kraken.Promising.X64.EnvG.TreiberAbs

/-! ## The runner's configuration -/

namespace Kraken.Promising.X64.EnvG.TreiberAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TreiberAbs Kraken.Promising.SLR.EnvG

/-- The runner's declarations for the typed `treiber_pp.kl`: `top` an 8-byte
word, `n1` a 4-byte word (strict). -/
def treiberDeclsD : Decls := { locs := [⟨0x1000000, 8⟩, ⟨0x1000100, 4⟩], unsizedDefault := false }

theorem treiberDeclsD_sized : treiberDeclsD.Sized := ⟨rfl, by decide⟩

/-- The threads as the runner prepares them, declarations included. -/
def treiberP0D : X64.State := { treiberP0 with decls := treiberDeclsD }
def treiberP1D : X64.State := { treiberP1 with decls := treiberDeclsD }

/-- The runner's configuration is `Config.init [treiberP0D, treiberP1D]
treiberInitMemV` in everything the theorem reads (declarations and initial
memory included). -/
def runnerMatchesD (src : String) : Bool :=
  runnerMatchesDL src [treiberP0D, treiberP1D] treiberInitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD treiberKl

section
attribute [local instance] treiberLayoutV

theorem treiberP0D_start : StartPushVD treiberDeclsD treiberP0D :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labT "pusher"; rw [labT_at 0]; decide,
    by show (0x100000 + 6 : Int64) = labT "pdone"; rw [labT_at 8]; decide,
    by rw [symT_top]; simp [treiberP0D, treiberP0, Reg64s.get64, Reg64s.set64],
    by rw [symT_n1]; simp [treiberP0D, treiberP0, Reg64s.get64, Reg64s.set64], Split.empty _⟩

theorem treiberP1D_start : StartPopVD treiberDeclsD treiberP1D :=
  ⟨rfl, rfl, by show (0x100000 + 7 : Int64) = labT "popper"; rw [labT_at 10]; decide,
    by show (0x100000 + 16 : Int64) = labT "qdone"; rw [labT_at 20]; decide,
    by rw [symT_top]; simp [treiberP1D, treiberP1, Reg64s.get64, Reg64s.set64], fun _ => by simp [treiberP1D, treiberP1]⟩

end

/-- **Treiber push/pop, `treiber_pp.kl`'s code verbatim, from the runner's
exact configuration**: in every final configuration under `Arch.tso` the
popper holds `n1` in `%r10` and its data `1` in `%r11d`. -/
theorem x64_treiber_pp_envG_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [treiberP0D, treiberP1D] treiberInitMemV) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ th.st.st.1.regs.get64 .r10 = 0x1000100 ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r11) = 1 := by
  have h := x64_treiber_pp_envG_runner (layout := treiberLayoutV) treiberDeclsD_sized
    (by rw [symT_top, symT_n1]; decide)
    treiberP0D_start treiberP1D_start (by rw [symT_top]; simp only [Config.init_mem]; decide) hc hf
  rwa [symT_n1] at h

end Kraken.Promising.X64.EnvG.TreiberAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.TreiberAbs.x64_treiber_pp_envG_runner
#print axioms Kraken.Promising.X64.EnvG.TreiberAbs.Concrete.x64_treiber_pp_envG_runner_concrete
