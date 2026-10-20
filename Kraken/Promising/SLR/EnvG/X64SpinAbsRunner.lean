/-
**`spinlock2.kl` from the runner's exact configuration**: `x64_spin_counter_envG_runner`, `x64_spin_counter_envG_verbatim`
for threads that carry the `.kl` runner's declarations (`spinlock2.kl`'s
header types `lock` and `counter` `uint32_t`, so the runner's declarations
are the two 4-byte words: strict sized, `Decls.Sized`), and its concrete
instances `x64_spin_counter_envG_runner_concrete2`/`_concrete3` at the
runner's own threads and initial memory for `spinlock2.kl` and
`spinlock3.kl` (`runnerMatchesD`, which compares the declarations and the
initial memory too).

The proof is `X64SpinAbsPublic`'s with the D forms of `EnvG/X64DeclsLink.lean`:
the rule `spinRuleV_envGD` (`ThreadRuleRX.ofSafelyEnvGRXMD` at `MaskOf.refl`),
the start `spinInvV_initD` (`invGRXMD_init`), the purity
`spinNoNTSpecV_holdsD` (`RelPureSpecQX.HoldsD`) and the assembly
`final_of_relPureSafelyQX_tsoD`. The old theorems are unchanged.
-/
import Kraken.Promising.SLR.EnvG.X64SpinAbsPublic
import Kraken.Promising.SLR.EnvG.X64SpinAbsConcrete
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64RunnerCommon

namespace Kraken.Promising.X64.EnvG.SpinAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.SpinLink
open Kraken.Promising.X64.EnvG.SpinRelPure Kraken.Promising.X64.EnvG.SpinPublicG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spinImageV)]

/-! ## The rule and the start, with declarations -/

/-- **The verbatim x64 spinlock worker's rule on `EnvG` with strict sized
declarations `ds`** (`spinRuleV_envG` through `ofSafelyEnvGRXMD`). -/
noncomputable def spinRuleV_envGD {ds : Decls} (hsz : ds.Sized) (P : Sys) (tid : Nat) (l c : BitVec 64)
    (rel₀ : Loc → Pred) : ThreadRuleRX (I := isa) Arch.tso (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.ofSafelyEnvGRXMD (S := spinS l c) (post := postSpinV P) (rel₀ := rel₀) hsz (MaskOf.refl _)
    (xlockPlan_valid P tid) (spinS_le16 l c) spinImageV_phase1 (RelRmwGiveOk.of_gives_nil (xlockPlan_gives P tid))
    (postSpinV_end P) (spinImageV_stuck _) (hB_spinV P tid)

/-- **A verbatim spinlock worker at its start with declarations `ds`**
(`StartStateV` with `decls = ds`): as the `.kl` runner sets it up. -/
structure StartStateVD (ds : Decls) (s : State) : Prop where
  exe : s.exe = layout spinImageV
  decls : s.decls = ds
  pc : s.st.2 = (_root_.Executable.labels s.exe).label "worker"
  endPc : s.endPc = (_root_.Executable.labels s.exe).label "done"
  split : Split [(symV "lock", 4), (symV "counter", 4)] s.st.1.dmem

omit [Executable.ValidLayout (layout spinImageV)] in
theorem StartStateVD.frame {ds : Decls} {s : State} (h : StartStateVD ds s) :
    FrameV (symV "lock") (symV "counter") s.st.1 :=
  ⟨split_dl h.split, split_dc h.split⟩

omit [Executable.ValidLayout (layout spinImageV)] in
theorem StartStateVD.st {ds : Decls} {s : State} (h : StartStateVD ds s) : s.st = (s.st.1, labV "worker") := by
  refine Prod.ext rfl ?_; rw [h.pc, h.exe]

/-- **The verbatim worker's initial invariant with declarations** (thread
`tid` of `N`; `spinInvV_init` through `invGRXMD_init`). -/
theorem spinInvV_initD {ds : Decls} (hsz : ds.Sized) {N : Nat} (hlc : symV "lock" ≠ symV "counter")
    (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N) {states : List isa.State} {initMem : List (Loc × Val)}
    {s : isa.State} (hs : states[tid]? = some s) (hst : StartStateVD ds s)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨symV "lock", 4⟩ = 0) :
    (spinRuleV_envGD hsz (ghostSys N (symV "lock") (symV "counter")) tid (symV "lock") (symV "counter")
      (ghost0 N (symV "lock") (symV "counter") (Config.init states initMem).mem).rel).Inv True
      (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨symV "lock", 4⟩ (ghostSys N (symV "lock") (symV "counter")).K
        (ghostSys N (symV "lock") (symV "counter")).F tid)
      (ghost0 N (symV "lock") (symV "counter") (Config.init states initMem).mem) := by
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  have hend : s.endPc = labV "done" := by rw [hst.endPc, hst.exe]
  have hFr : Fr (ghostSys N (symV "lock") (symV "counter")) tid (σInitX (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨symV "lock", 4⟩ (ghostSys N (symV "lock") (symV "counter")).K
        (ghostSys N (symV "lock") (symV "counter")).F tid)
      (ghost0 N (symV "lock") (symV "counter") (Config.init states initMem).mem)) := by
    refine ⟨world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_, threadRes_lkLe hLk0 _⟩
    intro f hf
    simp [σInitX, Views.getFwd] at hf
  have hsafe := Safely.uncountV
    (spinWorkerV_envG (ghostSys N (symV "lock") (symV "counter")) tid _ _ rfl rfl rfl rfl hL hN0 htid hN32
      s.st.1 (_, 0) ⟨hst.frame, hFr⟩)
  rw [← hst.st] at hsafe
  exact invGRXMD_init (S := spinS (symV "lock") (symV "counter")) (e := layout spinImageV) (e' := layout spinImageV)
    (endPc := labV "done") (post := postSpinV (ghostSys N (symV "lock") (symV "counter"))) hs rfl
    ⟨hst.exe, hst.decls, hend, hst.split, hsafe⟩

/-- **The all-release specification holds at a start state with
declarations.** -/
theorem spinNoNTSpecV_holdsD {ds : Decls} {s : isa.State} (h : StartStateVD ds s) : spinNoNTSpecV.HoldsD ds s := by
  refine ⟨h.exe, by rw [h.endPc, h.exe]; rfl, h.decls, h.split, ?_⟩
  rw [h.st]
  exact Safely.uncountV (spinWorkerV_noNT _ _ rfl rfl s.st.1 ((), 0) h.frame)

/-! ## The theorem -/

/-- **`counter = N` for `N` x64 xchg-spinlock workers running `spinlock2.kl`'s
code verbatim, with the runner's declarations, under `Arch.tso`**:
`x64_spin_counter_envG_verbatim` for threads whose declarations are strict
sized (`ds.Sized`: the `.kl` runner's, from the typed header). -/
theorem x64_spin_counter_envG_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (N : Nat)
    (hdisj : Decls.overlaps (symV "lock") 4 (symV "counter") 4 = false)
    (hN32 : N < 2 ^ 32) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateVD ds s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symV "counter", 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨symV "lock", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨symV "counter", 4⟩ = BitVec.ofNat 128 N :=
  CasSmoke.spin_counter_core N hdisj hN hC0 hc hf fun hlc hN0 hfin =>
    final_of_relPureSafelyQX_tsoD fuel
      (B := fun _ r _ => Post N ⟨symV "lock", 4⟩ (ghostSys N (symV "lock") (symV "counter")).K r)
      (Φ := fun cfg => cfg.mem.finalVal ⟨symV "counter", 4⟩ = BitVec.ofNat 128 N)
      (erase_init_lockPred (C := ⟨symV "counter", 4⟩) _ (ghostSys_spinLocs hlc) hN hN0 hC0 hLk0)
      pend_init
      (fun _ => spinNoNTSpecV) (fun _ => ds) (fun _ => hsz)
      (fun _ s hs => spinNoNTSpecV_holdsD (hst s (List.mem_of_getElem? hs)))
      (fun tid htid n m => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact NPSafe.of_ruleRX _ n m _ _ _ _
          (spinInvV_initD hsz hlc hN32 (hN ▸ htid) hs (hst s (List.mem_of_getElem? hs)) hLk0))
      hc hf hfin

end Kraken.Promising.X64.EnvG.SpinAbs

/-! ## The runner's configuration -/

namespace Kraken.Promising.X64.EnvG.SpinAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.SpinAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-- The runner's declarations for the typed `spinlock2.kl`: `lock` and
`counter`, 4-byte words (strict). -/
def spinDeclsD : Decls := { locs := [⟨0x1000000, 4⟩, ⟨0x1000100, 4⟩], unsizedDefault := false }

theorem spinDeclsD_sized : spinDeclsD.Sized := ⟨rfl, by decide⟩

/-- A worker as the runner prepares it: `spinWorkerV0` with the runner's
declarations. -/
def spinWorkerD0 : X64.State := { spinWorkerV0 with decls := spinDeclsD }

/-- The runner's configuration is `Config.init (List.replicate n spinWorkerD0)
spinInitMemV` in everything the theorem reads: per thread the executable,
end, pc, registers, private memory, **declarations** and no promise; the
initial memory (`lock = 0`, `counter = 0`, 4-byte words) and no message. -/
def runnerMatchesD (src : String) (n : Nat) : Bool :=
  runnerMatchesDN src n spinWorkerD0 spinInitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD spinlock2Kl 2

/-- `spinlock3.kl`: the same worker, three threads. -/
def spinlock3Kl : String := include_str "../../../Examples/LockFree/X64/spinlock3.kl"

/-- info: true -/
#guard_msgs in
#eval codeMatches spinlock3Kl

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD spinlock3Kl 3

section
attribute [local instance] spinLayoutV

theorem spinWorkerD0_start : StartStateVD spinDeclsD spinWorkerD0 :=
  ⟨rfl, rfl, by show _ = labV "worker"; rw [labV_at 0]; decide,
    by show _ = labV "done"; rw [labV_at 13]; decide, Split.empty _⟩

end

/-- **`counter = N`** for `N < 2 ^ 32` workers of `spinlock2.kl`'s code, from
the runner's exact thread state and initial memory (declarations included). -/
theorem x64_spin_counter_envG_runner_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init (List.replicate N spinWorkerD0) spinInitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000100, 4⟩ = BitVec.ofNat 128 N := by
  have h := x64_spin_counter_envG_runner (layout := spinLayoutV) spinDeclsD_sized N
    (by rw [symV_lock, symV_counter]; decide) hN32
    (fun s hs => (List.eq_of_mem_replicate hs) ▸ spinWorkerD0_start) List.length_replicate
    (by rw [symV_counter]; simp only [Config.init_mem]; decide)
    (by rw [symV_lock]; simp only [Config.init_mem]; decide) hc hf
  rwa [symV_counter] at h

/-- **`counter = 2` for the two workers of `spinlock2.kl`, from the runner's
exact configuration** (declarations and initial memory included). -/
theorem x64_spin_counter_envG_runner_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [spinWorkerD0, spinWorkerD0] spinInitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000100, 4⟩ = 2 :=
  x64_spin_counter_envG_runner_concreteN 2 (by decide) hc hf

/-- **`counter = 3` for the three workers of `spinlock3.kl`**, from the
runner's exact configuration. -/
theorem x64_spin_counter_envG_runner_concrete3 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [spinWorkerD0, spinWorkerD0, spinWorkerD0] spinInitMemV) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨0x1000100, 4⟩ = 3 :=
  x64_spin_counter_envG_runner_concreteN 3 (by decide) hc hf

end Kraken.Promising.X64.EnvG.SpinAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.SpinAbs.x64_spin_counter_envG_runner
#print axioms Kraken.Promising.X64.EnvG.SpinAbs.Concrete.x64_spin_counter_envG_runner_concrete2
#print axioms Kraken.Promising.X64.EnvG.SpinAbs.Concrete.x64_spin_counter_envG_runner_concrete3
