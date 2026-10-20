/-
**`spinlock_cmpxchg2.kl` from the runner's exact configuration**: `x64_cmpx_counter_envG_runner`, `x64_cmpx_counter_envG_verbatim`
for threads that carry the `.kl` runner's declarations (`spinlock_cmpxchg2.kl`'s
header types `lock` and `counter` `uint32_t`, so the runner's declarations
are the two 4-byte words: strict sized, `Decls.Sized`), and its concrete
instances `x64_cmpx_counter_envG_runner_concrete2`/`_concrete3` at the
runner's own threads and initial memory for `spinlock_cmpxchg2.kl` and
`spinlock_cmpxchg3.kl` (`runnerMatchesD`, which compares the declarations and the
initial memory too).

The proof is `X64CmpxAbsPublic`'s with the D forms of `EnvG/X64DeclsLink.lean`:
the rule `cmpxRuleV_envGD` (`ThreadRuleRXF.ofSafelyEnvGFXMD` at `MaskOf.refl`),
the start `cmpxInvV_initD` (`invGFXMD_init`), the purity
`cmpxNoNTSpecV_holdsD` (`RelPureSpecQX.HoldsD`) and the assembly
`final_of_relPureSafelyQX_tsoFD`. The old theorems are unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64CmpxAbsPublic
import Kraken.Promising.SLR.EnvG.X64CmpxAbsConcrete
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64RunnerCommon

namespace Kraken.Promising.X64.EnvG.CmpxAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.SpinLink
open Kraken.Promising.X64.EnvG.SpinRelPure Kraken.Promising.X64.EnvG.SpinPublicG
open Kraken.Promising.X64.EnvG.CmpxPublic Kraken.Promising.X64.EnvG.SpinAbs
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

variable [layout : _root_.Layout] [Executable.ValidLayout (layout cmpxImageV)]

/-! ## The rule and the start, with declarations -/

/-- **The verbatim x64 spinlock worker's rule on `EnvG` with strict sized
declarations `ds`** (`cmpxRuleV_envGF` through `ofSafelyEnvGFXMD`). -/
noncomputable def cmpxRuleV_envGD {ds : Decls} (hsz : ds.Sized) (P : Sys) (tid : Nat) (l c : BitVec 64)
    (rel₀ : Loc → Pred) : ThreadRuleRXF (I := isa) Arch.tso (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRXF.ofSafelyEnvGFXMD (S := spinS l c) (post := postCmpxV P) (rel₀ := rel₀) hsz (MaskOf.refl _)
    (xlockPlan_valid P tid) (spinS_le16 l c) cmpxImageV_phase1 (RelRmwGiveOk.of_gives_nil (xlockPlan_gives P tid))
    (postCmpxV_end P) (cmpxImageV_stuck _) (hB_cmpxV P tid)

/-- **A verbatim spinlock worker at its start with declarations `ds`**
(`StartStateCV` with `decls = ds`): as the `.kl` runner sets it up. -/
structure StartStateCVD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout cmpxImageV
  decls : s.decls = ds
  pc : s.st.2 = (_root_.Executable.labels s.exe).label "worker"
  endPc : s.endPc = (_root_.Executable.labels s.exe).label "done"
  split : Split [(symC "lock", 4), (symC "counter", 4)] s.st.1.dmem

omit [Executable.ValidLayout (layout cmpxImageV)] in
theorem StartStateCVD.frame {ds : Decls} {s : State} (h : StartStateCVD ds s) :
    FrameV (symC "lock") (symC "counter") s.st.1 :=
  ⟨split_dl h.split, split_dc h.split⟩

omit [Executable.ValidLayout (layout cmpxImageV)] in
theorem StartStateCVD.st {ds : Decls} {s : State} (h : StartStateCVD ds s) : s.st = (s.st.1, labC "worker") := by
  refine Prod.ext rfl ?_; rw [h.pc, h.exe]

/-- **The verbatim worker's initial invariant with declarations** (thread
`tid` of `N`; `cmpxInvV_init` through `invGFXMD_init`). -/
theorem cmpxInvV_initD {ds : Decls} (hsz : ds.Sized) {N : Nat} (hlc : symC "lock" ≠ symC "counter")
    (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N) {states : List isa.State} {initMem : List (Loc × Val)}
    {s : isa.State} (hs : states[tid]? = some s) (hst : StartStateCVD ds s)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨symC "lock", 4⟩ = 0) :
    (cmpxRuleV_envGD hsz (ghostSys N (symC "lock") (symC "counter")) tid (symC "lock") (symC "counter")
      (ghost0 N (symC "lock") (symC "counter") (Config.init states initMem).mem).rel).Inv True
      (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨symC "lock", 4⟩ (ghostSys N (symC "lock") (symC "counter")).K
        (ghostSys N (symC "lock") (symC "counter")).F tid)
      (ghost0 N (symC "lock") (symC "counter") (Config.init states initMem).mem) := by
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  have hend : s.endPc = labC "done" := by rw [hst.endPc, hst.exe]
  have hFr : Fr (ghostSys N (symC "lock") (symC "counter")) tid (σInitX (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨symC "lock", 4⟩ (ghostSys N (symC "lock") (symC "counter")).K
        (ghostSys N (symC "lock") (symC "counter")).F tid)
      (ghost0 N (symC "lock") (symC "counter") (Config.init states initMem).mem)) := by
    refine ⟨world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_, threadRes_lkLe hLk0 _⟩
    intro f hf
    simp [σInitX, Views.getFwd] at hf
  have hsafe := Safely.uncountV
    (cmpxWorkerV_envG (ghostSys N (symC "lock") (symC "counter")) tid _ _ rfl rfl rfl rfl hL hN0 htid hN32
      s.st.1 (_, 0) ⟨hst.frame, hFr⟩)
  rw [← hst.st] at hsafe
  exact invGFXMD_init (S := spinS (symC "lock") (symC "counter")) (e := layout cmpxImageV) (e' := layout cmpxImageV)
    (endPc := labC "done") (post := postCmpxV (ghostSys N (symC "lock") (symC "counter"))) hs rfl
    ⟨hst.exe, hst.decls, hend, hst.split, hsafe⟩

/-- **The all-release specification holds at a start state with
declarations.** -/
theorem cmpxNoNTSpecV_holdsD {ds : Decls} {s : isa.State} (h : StartStateCVD ds s) : cmpxNoNTSpecV.HoldsD ds s := by
  refine ⟨h.exe, by rw [h.endPc, h.exe]; rfl, h.decls, h.split, ?_⟩
  rw [h.st]
  exact Safely.uncountV (cmpxWorkerV_noNT _ _ rfl rfl s.st.1 ((), 0) h.frame)

/-! ## The theorem -/

/-- **`counter = N` for `N` x64 `lock cmpxchg` spinlock workers running `spinlock_cmpxchg2.kl`'s
code verbatim, with the runner's declarations, under `Arch.tso`**:
`x64_cmpx_counter_envG_verbatim` for threads whose declarations are strict
sized (`ds.Sized`: the `.kl` runner's, from the typed header). -/
theorem x64_cmpx_counter_envG_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (N : Nat)
    (hdisj : Decls.overlaps (symC "lock") 4 (symC "counter") 4 = false)
    (hN32 : N < 2 ^ 32) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateCVD ds s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symC "counter", 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨symC "lock", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨symC "counter", 4⟩ = BitVec.ofNat 128 N :=
  CasSmoke.spin_counter_core N hdisj hN hC0 hc hf fun hlc hN0 hfin =>
    final_of_relPureSafelyQX_tsoFD (theorem1FChain Arch.tso fuel)
      (B := fun _ r _ => Post N ⟨symC "lock", 4⟩ (ghostSys N (symC "lock") (symC "counter")).K r)
      (Φ := fun cfg => cfg.mem.finalVal ⟨symC "counter", 4⟩ = BitVec.ofNat 128 N)
      (erase_init_lockPred (C := ⟨symC "counter", 4⟩) _ (ghostSys_spinLocs hlc) hN hN0 hC0 hLk0) pend_init
      (fun _ => cmpxNoNTSpecV) (fun _ => ds) (fun _ => hsz)
      (fun _ s hs => cmpxNoNTSpecV_holdsD (hst s (List.mem_of_getElem? hs)))
      (fun tid htid n m => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact NPSafeF.of_ruleRXF _ n m _ _ _ _
          (cmpxInvV_initD hsz hlc hN32 (hN ▸ htid) hs (hst s (List.mem_of_getElem? hs)) hLk0))
      hc hf hfin

end Kraken.Promising.X64.EnvG.CmpxAbs

/-! ## The runner's configuration -/

namespace Kraken.Promising.X64.EnvG.CmpxAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.CmpxAbs Kraken.Promising.X64.EnvG.CmpxAbs.Concrete Kraken.Promising.SLR.EnvG

/-- The runner's declarations for the typed `spinlock_cmpxchg2.kl`: `lock` and
`counter`, 4-byte words (strict). -/
def cmpxDeclsD : Decls := { locs := [⟨0x1000000, 4⟩, ⟨0x1000100, 4⟩], unsizedDefault := false }

theorem cmpxDeclsD_sized : cmpxDeclsD.Sized := ⟨rfl, by decide⟩

/-- A worker as the runner prepares it: `cmpxWorkerV0` with the runner's
declarations. -/
def cmpxWorkerD0 : X64.State := { cmpxWorkerV0 with decls := cmpxDeclsD }

/-- The runner's configuration is `Config.init (List.replicate n cmpxWorkerD0)
cmpxInitMemV` in everything the theorem reads: per thread the executable,
end, pc, registers, private memory, **declarations** and no promise; the
initial memory (`lock = 0`, `counter = 0`, 4-byte words) and no message. -/
def runnerMatchesD (src : String) (n : Nat) : Bool :=
  runnerMatchesDN src n cmpxWorkerD0 cmpxInitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD spinlockCmpxchg2Kl 2

/-- `spinlock_cmpxchg3.kl`: the same worker, three threads. -/
def spinlockCmpxchg3Kl : String := include_str "../../../Examples/LockFree/X64/spinlock_cmpxchg3.kl"

/-- info: true -/
#guard_msgs in
#eval codeMatches spinlockCmpxchg3Kl

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD spinlockCmpxchg3Kl 3

section
attribute [local instance] cmpxLayoutV

theorem cmpxWorkerD0_start : StartStateCVD cmpxDeclsD cmpxWorkerD0 :=
  ⟨rfl, rfl, by show _ = labC "worker"; rw [labC_at 0]; decide,
    by show _ = labC "done"; rw [labC_at 10]; decide, Split.empty _⟩

end

/-- **`counter = N`** for `N < 2 ^ 32` workers of `spinlock_cmpxchg2.kl`'s code, from
the runner's exact thread state and initial memory (declarations included). -/
theorem x64_cmpx_counter_envG_runner_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init (List.replicate N cmpxWorkerD0) cmpxInitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000100, 4⟩ = BitVec.ofNat 128 N := by
  have h := x64_cmpx_counter_envG_runner (layout := cmpxLayoutV) cmpxDeclsD_sized N
    (by rw [symC_lock, symC_counter]; decide) hN32
    (fun s hs => (List.eq_of_mem_replicate hs) ▸ cmpxWorkerD0_start) List.length_replicate
    (by rw [symC_counter]; simp only [Config.init_mem]; decide)
    (by rw [symC_lock]; simp only [Config.init_mem]; decide) hc hf
  rwa [symC_counter] at h

/-- **`counter = 2` for the two workers of `spinlock_cmpxchg2.kl`, from the runner's
exact configuration** (declarations and initial memory included). -/
theorem x64_cmpx_counter_envG_runner_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [cmpxWorkerD0, cmpxWorkerD0] cmpxInitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000100, 4⟩ = 2 :=
  x64_cmpx_counter_envG_runner_concreteN 2 (by decide) hc hf

/-- **`counter = 3` for the three workers of `spinlock_cmpxchg3.kl`**, from the
runner's exact configuration. -/
theorem x64_cmpx_counter_envG_runner_concrete3 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [cmpxWorkerD0, cmpxWorkerD0, cmpxWorkerD0] cmpxInitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000100, 4⟩ = 3 :=
  x64_cmpx_counter_envG_runner_concreteN 3 (by decide) hc hf

end Kraken.Promising.X64.EnvG.CmpxAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.CmpxAbs.x64_cmpx_counter_envG_runner
#print axioms Kraken.Promising.X64.EnvG.CmpxAbs.Concrete.x64_cmpx_counter_envG_runner_concrete2
#print axioms Kraken.Promising.X64.EnvG.CmpxAbs.Concrete.x64_cmpx_counter_envG_runner_concrete3
