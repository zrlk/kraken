/-
**The x64 `lock cmpxchg` spinlock worker verbatim, on `EnvG` by `vcgen`**
The worker of
`Kraken/Examples/LockFree/X64/spinlock_cmpxchg2.kl` as written, with the
absolute operands `(lock)` and `(counter)` (`cmpxWorkerV`), run in its image
`cmpxImageV`: the code followed by the `.kl` runner's data trailer (the
`spinlock2.kl` trailer `SpinAbs.spinDataV`: `lock`, `counter`).

The VCs are the x64 `cmpxchg` lock proof's and the x64 `xchg` lock proof's,
unchanged (`EnvG/X64CmpxVC.lean`,
`EnvG/X64SpinVC.lean`); the table is `SpinAbs.spinTableV`, the script
`Cmpx.cmpxWorkerG_envG`'s with the address equations closed by `rfl` (the
symbols, `hl`/`hc`, instead of `%rdi`/`%rsi`). The absolute `lock cmpxchgl`
cell uses `MachineWP.lock_cmpxchg32_abs_shared_spec` (`Kraken/EnvVCGenAbs.lean`),
the placement `cfgEnv_partial_at` (`Kraken/EnvCfgAbs.lean`).

- `cmpxWorkerV_envG`: the worker's run in the counted `EnvGX`;
- `cmpxWorkerV_noNT`: the worker's run in the all-release environment.
-/
import Kraken.Promising.SLR.EnvG.X64CmpxVCGen
import Kraken.Promising.SLR.EnvG.X64CmpxRelPure
import Kraken.Promising.SLR.EnvG.X64SpinAbsVCGen

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin
open Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.Cmpx Kraken.Promising.X64.EnvG.SpinAbs
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.CmpxAbs

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program and its image -/

/-- **The x64 `lock cmpxchg` spinlock worker of `spinlock_cmpxchg2.kl`,
verbatim** (its `code` block). -/
def cmpxWorkerV : Program := parse("
worker:
  xorl %eax,%eax
  movl $1,%ecx
  lock cmpxchgl %ecx,(lock)
  jne worker
  movl (counter),%edx
  addl $1,%edx
  movl %edx,(counter)
  movl $0,(lock)
  jmp done
done:
")

/-- The worker's image: the code, then the `.kl` runner's data trailer
(`lock`, `counter`, in the order of first mention). -/
def cmpxImageV : Program := cmpxWorkerV ++ spinDataV

/-- info: 11 -/
#guard_msgs in
#eval cmpxWorkerV.length

theorem cmpxImageV_wf : Program.WF cmpxImageV := by decide

theorem cmpxWorkerV_sub : Program.subBlocksOfE cmpxWorkerV cmpxImageV = true := by decide

/-! ## The symbols -/

variable [layout : _root_.Layout]

/-- A label's address in the image (`(sym)` points to `(labC x).toBitVec`). -/
abbrev labC (x : Label) : Int64 := (_root_.Executable.labels (layout cmpxImageV)).label x

/-- A symbol's address in the image. -/
abbrev symC (x : Label) : BitVec 64 := (labC x).toBitVec

variable [Executable.ValidLayout (layout cmpxImageV)]

local instance cmpxImageV.env : CodeEnv := ⟨layout cmpxImageV⟩

theorem cmpxWorkerV_placedIn : Program.PlacedIn cmpxWorkerV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := cmpxImageV) cmpxImageV_wf rfl (by decide))
    cmpxWorkerV_sub

omit [Executable.ValidLayout (layout cmpxImageV)] in
theorem cmpxWorkerV_last : ∀ l blk, Program.blockAt cmpxWorkerV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labC "done" :=
  Program.after_last_of (by decide)

/-! ## The worker -/

/-- **The verbatim x64 `lock cmpxchg` spinlock worker on `EnvG`** (counted,
partial): from `Fr` at the entry label, every run that reaches the exit label
is in `QEnd`. -/
theorem cmpxWorkerV_envG (P : Sys) (tid : Nat) (l c : BitVec 64) (hl : symC "lock" = l)
    (hc : symC "counter" = c) (hLk : P.Lk = ⟨l, 4⟩) (hC : P.C = ⟨c, 4⟩)
    (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32) :
    ∀ s g, FrameV l c s ∧ Fr P tid g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (E P tid l c)))
        (fun x => (x.1.2 = labC "done" ∧ QEnd P x.2.1) ∨ False) ((s, labC "worker"), g) := by
  obtain ⟨N, Lk, C, K, F⟩ := P
  simp only at hLk hC
  subst hLk hC
  have hLC : Sys.Lk ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ ≠ Sys.C ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ := hL.lk_c
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (E ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid l c))
    (Q := fun _ σ => QEnd ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ σ.1)
    (E := fun _ _ _ => False) (spinTableV ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid l c) ?_ rfl
    (by decide) cmpxWorkerV_placedIn cmpxWorkerV_last s g (by simpa [spinTableV] using hsg)
  cfg_cases_env [cmpxWorkerV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hdl, hdc⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envG, Reg64s.get64] at *
  case vc1 => simp [hdl]
  case vc2 =>
    rename_i af σ1 σ2 hf1 hf2 _
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_rmw]
    refine ⟨vc_cmpx_ok_at hN0 _ (Fr.fence (Fr.fence hT hf1.1) hf2.1) rfl rfl (by simp [cmpxOp]),
      by simp⟩
  case vc3 =>
    rename_i af σ1 σ2 old σ3 hx heq hz σ4 hf1 hf2 hf3 _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd heq hz
  case vc4 => simp <;> trivial
  case vc5 =>
    rename_i af σ1 σ2 old σ3 hx heq hz σ4 y σ5 hld σ6 hm hf1 hf2 hf3 hf4 _
    simp at heq
    rcases vc_cmpx_at hN0 _ (Fr.fence (Fr.fence hT hf1.1) hf2.1) rfl rfl (by simp [cmpxOp]) old _
      hx.1 with ⟨h0, -⟩ | ⟨-, hH1⟩
    · exact absurd heq h0
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
    · simp [hdc] at hm
    have hH2 := vc_ld_c_at hLC _ (H1.fence hH1 hf3.1) rfl rfl w _ hst2.1
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
    exact ⟨vc_st_c_ok_at hLC _ _ (H2.fence hH2 hf4.1) rfl rfl (by simp [BitVec.add_comm]),
      by simp⟩
  case vc6 =>
    rename_i af σ1 σ2 old σ3 hx heq hz σ4 y σ5 hld σ6 dm σ7 hst3 hf1 hf2 hf3 hf4 _
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, -, -⟩
    · simp [hdc] at hm
    · simp [hdl]
  case vc7 =>
    rename_i af σ1 σ2 old σ3 hx heq hz σ4 y σ5 hld σ6 dm σ7 hst3 hf1 hf2 hf3 hf4 _
    simp at heq
    rcases vc_cmpx_at hN0 _ (Fr.fence (Fr.fence hT hf1.1) hf2.1) rfl rfl (by simp [cmpxOp]) old _
      hx.1 with ⟨h0, -⟩ | ⟨-, hH1⟩
    · exact absurd heq h0
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
    · simp [hdc] at hm
    have hH2 := vc_ld_c_at hLC _ (H1.fence hH1 hf3.1) rfl rfl w _ hst2.1
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hdc] at hm
    have hH3 := vc_st_c_at hLC _ _ (H2.fence hH2 hf4.1) rfl rfl (by simp [BitVec.add_comm]) b _
      hst3.1
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
    exact ⟨vc_rel_ok_at hL hN0 htid hN32 _ _ hH3 rfl rfl (by simp), by simp⟩
  case vc8 =>
    rename_i af σ1 σ2 old σ3 hx heq hz σ4 y σ5 hld σ6 dm σ7 hst3 b' σ8 hrel σ9 hf1 hf2 hf3 hf4 hf5 _
    simp at heq
    rcases vc_cmpx_at hN0 _ (Fr.fence (Fr.fence hT hf1.1) hf2.1) rfl rfl (by simp [cmpxOp]) old _
      hx.1 with ⟨h0, -⟩ | ⟨-, hH1⟩
    · exact absurd heq h0
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
    · simp [hdc] at hm
    have hH2 := vc_ld_c_at hLC _ (H1.fence hH1 hf3.1) rfl rfl w _ hst2.1
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hdc] at hm
    have hH3 := vc_st_c_at hLC _ _ (H2.fence hH2 hf4.1) rfl rfl (by simp [BitVec.add_comm]) b _
      hst3.1
    have hQ := vc_rel_at hL hN0 htid hN32 _ _ hH3 rfl rfl (by simp) b' _ hrel.1
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hdl,
      by simpa using hdc⟩, .inr ⟨rfl, QEnd.fence hQ hf5.1⟩⟩, .inl (by decide)⟩
  case vc9 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 hf1 hf2 hf3 _
    simp at hne
    rcases vc_cmpx_at hN0 _ (Fr.fence (Fr.fence hT hf1.1) hf2.1) rfl rfl (by simp [cmpxOp]) old _
      hx.1 with ⟨-, hF⟩ | ⟨h0, -⟩
    · have hn := hx.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hdl,
        by simpa using hdc⟩, .inl ⟨rfl, Fr.fence hF hf3.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
    · exact absurd h0 hne
  case vc10 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 hm hf1 hf2 hf3 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd hz hne
  case vc11 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 y σ5 hld σ6 hm hf1 hf2 hf3 hf4 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd hz hne
  case vc12 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 y σ5 hld σ6 dm σ7 hst3 hf1 hf2 hf3 hf4 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd hz hne
  case vc13 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 y σ5 hld σ6 dm σ7 hst3 hf1 hf2 hf3 hf4 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd hz hne
  case vc14 =>
    rename_i af σ1 σ2 old σ3 hx hne hz σ4 y σ5 hld σ6 dm σ7 hst3 b' σ8 hrel σ9 hf1 hf2 hf3 hf4 hf5 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd hz hne
  case vc1 => exact hT

/-! ## Only release writes -/

open Kraken.Promising.X64.EnvG.SpinRelPure in
/-- **The verbatim x64 `lock cmpxchg` spinlock worker makes only release
writes** (counted, partial; `CmpxRelPure.cmpxWorkerG_noNT` verbatim). -/
theorem cmpxWorkerV_noNT (l c : BitVec 64) (hl : symC "lock" = l) (hc : symC "counter" = c) :
    ∀ s g, FrameV l c s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvR l c)))
        (fun x => (x.1.2 = labC "done" ∧ True) ∨ False) ((s, labC "worker"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvR l c)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (spinPureTableV l c) ?_ rfl (by decide) cmpxWorkerV_placedIn cmpxWorkerV_last s g
    (fun _ => hs)
  cfg_cases_env [cmpxWorkerV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals obtain ⟨hdl, hdc⟩ := hT
  all_goals simp only [Reg64s.get64, SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  all_goals first
    | (simp [hdl]; done)
    | (simp; done)
    | (simp; trivial)
    | (simp; exact fun h => absurd rfl h)
    | (simp; exact fun h => h rfl)
    | (exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩)
    | skip
  case vc3 | vc9 =>
    rename_i hx _
    refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simpa using hdl, by simpa using hdc⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    have hn := hx.2
    subst hg
    omega
  case vc6 | vc12 =>
    rename_i hst3 _
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, -⟩
    · simp [hdc] at hm
    · simp [hdl]

end Kraken.Promising.X64.EnvG.CmpxAbs
