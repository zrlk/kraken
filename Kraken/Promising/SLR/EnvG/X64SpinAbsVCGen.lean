/-
**The x64 xchg spinlock worker verbatim, on `EnvG` by `vcgen`**: the worker of `Kraken/Examples/LockFree/X64/spinlock2.kl` as written,
with the absolute operands `(lock)` and `(counter)` (`spinWorkerV`), run in
its image `spinImageV`: the code followed by the `.kl` runner's data trailer
(`spinDataV`: a padding `.byteArray`, `.label "lock"`, a padding
`.byteArray`, `.label "counter"`; `Kraken.Litmus.X64.prepareProgram`), so
that `(lock)`/`(counter)` resolve to the symbols' addresses (`symV`).

The VCs are the x64 `xchg` lock proof's, unchanged (`EnvG/X64SpinVC.lean`, at an address given
by an equation: `vc_*_at` of `EnvG/X64SpinVCGen.lean`); the table and the
script are `spinWorkerG_envG`'s with the frame `FrameV` (no register holds an
address: the symbols are facts about the code, `hl`/`hc`). The absolute
cells use `EnvVCGenAbs.lean`'s rules, the placement `EnvCfgAbs.lean`
(`cfgEnv_partial_at` at the entry label `worker`, ending at the exit label
`done`).

- `spinWorkerV_envG`: the worker's run in the counted `EnvGX`;
- `spinWorkerV_noNT`: the worker's run in the all-release environment.
-/
import Kraken.Promising.SLR.EnvG.X64SpinVCGen
import Kraken.Promising.SLR.EnvG.X64SpinRelPure
import Kraken.EnvVCGenAbs
import Kraken.EnvCfgAbs

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin
open Kraken.Promising.X64.EnvG.Spin
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.SpinAbs

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program and its image -/

/-- **The x64 spinlock worker of `spinlock2.kl`, verbatim** (its `code`
block). -/
def spinWorkerV : Program := parse("
worker:
  movl (lock),%eax
  testl %eax,%eax
  jne worker
  movl $1,%eax
  xchgl %eax,(lock)
  testl %eax,%eax
  jne worker
  movl (counter),%ecx
  addl $1,%ecx
  movl %ecx,(counter)
  movl $0,(lock)
  jmp done
done:
")

/-- The `.kl` runner's data trailer of `spinlock2.kl`: each symbol a label
behind a padding cell, in the order of first mention (`lock`, `counter`). -/
def spinDataV : Program :=
  [.byteArray (.mk #[]), .label "lock", .byteArray (.mk #[]), .label "counter"]

/-- The worker's image: the code, then the data trailer. -/
def spinImageV : Program := spinWorkerV ++ spinDataV

/-- info: 14 -/
#guard_msgs in
#eval spinWorkerV.length

theorem spinImageV_wf : Program.WF spinImageV := by decide

/-- The worker's blocks are placed in its image. -/
theorem spinWorkerV_sub : Program.subBlocksOfE spinWorkerV spinImageV = true := by decide

/-! ## The symbols -/

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spinImageV)]

local instance spinImageV.env : CodeEnv := ⟨layout spinImageV⟩

/-- A symbol's address in the image: where `(sym)` points. -/
abbrev symV (x : Label) : BitVec 64 := ((_root_.Executable.labels (layout spinImageV)).label x).toBitVec

/-- The entry (`worker`) or exit (`done`) label's address. -/
abbrev labV (x : Label) : Int64 := (_root_.Executable.labels (layout spinImageV)).label x

theorem spinWorkerV_placedIn : Program.PlacedIn spinWorkerV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := spinImageV) spinImageV_wf rfl (by decide))
    spinWorkerV_sub

omit [Executable.ValidLayout (layout spinImageV)] in
theorem spinWorkerV_last : ∀ l blk, Program.blockAt spinWorkerV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labV "done" :=
  Program.after_last_of (by decide)

/-! ## The worker -/

/-- The worker's frame: neither word in `dmem`. -/
abbrev FrameV (l c : BitVec 64) (s : MachineData) : Prop :=
  Mem.loadInt s.dmem l 4 = none ∧ Mem.loadInt s.dmem c 4 = none

/-- The worker's table: `Fr` at `worker`, `QEnd` at `done`. -/
abbrev spinTableV (P : Sys) (tid : Nat) (l c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (E P tid l c)).State → Prop :=
  fun lb s σ => FrameV l c s ∧ ((lb = "worker" ∧ Fr P tid σ.1) ∨ (lb = "done" ∧ QEnd P σ.1))

/-- **The verbatim x64 spinlock worker on `EnvG`** (counted, partial): from
`Fr` at the entry label, every run that reaches the exit label is in
`QEnd`. -/
theorem spinWorkerV_envG (P : Sys) (tid : Nat) (l c : BitVec 64) (hl : symV "lock" = l) (hc : symV "counter" = c)
    (hLk : P.Lk = ⟨l, 4⟩) (hC : P.C = ⟨c, 4⟩)
    (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32) :
    ∀ s g, FrameV l c s ∧ Fr P tid g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (E P tid l c)))
        (fun x => (x.1.2 = labV "done" ∧ QEnd P x.2.1) ∨ False) ((s, labV "worker"), g) := by
  obtain ⟨N, Lk, C, K, F⟩ := P
  simp only at hLk hC
  subst hLk hC
  have hLC : Sys.Lk ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ ≠ Sys.C ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ := hL.lk_c
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (E ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid l c))
    (Q := fun _ σ => QEnd ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ σ.1)
    (E := fun _ _ _ => False) (spinTableV ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid l c) ?_ rfl
    (by decide) spinWorkerV_placedIn spinWorkerV_last s g (by simpa [spinTableV] using hsg)
  cfg_cases_env [spinWorkerV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hdl, hdc⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envG, Reg64s.get64,
    ] at *
  case vc1 =>
    simp <;> trivial
  case vc2 =>
    rename_i x σ1 hld af σ2 hz σ3 hf1 hf2 _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdl] at hm
    · have hR := vc_ld_spin_at _ hT rfl rfl v _ hst.1
      have hn := hst.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hdl, by simpa using hdc⟩,
        .inl ⟨rfl, Fr.fence (Fr.fence hR hf1.1) hf2.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 =>
    simp [hdl]
  case vc4 =>
    rename_i x σ1 hld af σ2 hz σ3 σ4 hf1 hf2 hf3 _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdl] at hm
    · have hR := vc_ld_spin_at _ hT rfl rfl v _ hst.1
      simp only [SharedEnv.counted_ok, SharedEnv.within_ok_rmw]
      refine ⟨vc_xchg_ok_at hN0 _ (Fr.fence (Fr.fence (Fr.fence hR hf1.1) hf2.1) hf3.1) rfl rfl
        (by simp [xchgOp]), by simp⟩
  case vc5 =>
    rename_i x σ1 hld af σ2 hz1 σ3 σ4 old σ5 hx af2 σ6 hz2 σ7 hf1 hf2 hf3 hf4 hf5 _
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdl] at hm
    · have hR := vc_ld_spin_at _ hT rfl rfl v _ hst.1
      have hX := vc_xchg_at hN0 _ (Fr.fence (Fr.fence (Fr.fence hR hf1.1) hf2.1) hf3.1) rfl rfl
        (by simp [xchgOp]) old _ hx.1
      rcases hX with ⟨-, hF⟩ | ⟨h0, -⟩
      · have hn := hst.2
        have hn' := hx.2
        refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hdl, by simpa using hdc⟩,
          .inl ⟨rfl, Fr.fence (Fr.fence hF hf4.1) hf5.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
        subst hg
        simp [SharedAccess.tick] at hn hn'
        omega
      · exact absurd h0 hz2
  case vc6 =>
    simp <;> trivial
  case vc7 =>
    rename_i x σ1 hld af σ2 hz1 σ3 σ4 old σ5 hx af2 σ6 hz2 σ7 y σ8 hld2 σ9 hl hf1 hf2 hf3 hf4 hf5 hf6 _
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdl] at hm
    · have hR := vc_ld_spin_at _ hT rfl rfl v _ hst.1
      have hX := vc_xchg_at hN0 _ (Fr.fence (Fr.fence (Fr.fence hR hf1.1) hf2.1) hf3.1) rfl rfl
        (by simp [xchgOp]) old _ hx.1
      rcases hX with ⟨h0, -⟩ | ⟨-, hH1⟩
      · exact absurd hz2 h0
      · rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
        · simp [hdc] at hm
        · have hH2 := vc_ld_c_at hLC _ (H1.fence (H1.fence hH1 hf4.1) hf5.1) rfl rfl w _ hst2.1
          simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
          refine ⟨vc_st_c_ok_at hLC _ _ (H2.fence hH2 hf6.1) rfl rfl
            (by simp [BitVec.add_comm]), by simp⟩
  case vc8 =>
    rename_i x σ1 hld af σ2 hz1 σ3 σ4 old σ5 hx af2 σ6 hz2 σ7 y σ8 hld2 σ9 dm σ10 hst3 hf1 hf2 hf3 hf4 hf5 hf6 _
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, -, -⟩
    · simp [hdc] at hm
    · simp [hdl]
  case vc9 =>
    rename_i x σ1 hld af σ2 hz1 σ3 σ4 old σ5 hx af2 σ6 hz2 σ7 y σ8 hld2 σ9 dm σ10 hst3 hf1 hf2 hf3 hf4 hf5 hf6 _
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdl] at hm
    · have hR := vc_ld_spin_at _ hT rfl rfl v _ hst.1
      have hX := vc_xchg_at hN0 _ (Fr.fence (Fr.fence (Fr.fence hR hf1.1) hf2.1) hf3.1) rfl rfl
        (by simp [xchgOp]) old _ hx.1
      rcases hX with ⟨h0, -⟩ | ⟨-, hH1⟩
      · exact absurd hz2 h0
      · rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
        · simp [hdc] at hm
        · have hH2 := vc_ld_c_at hLC _ (H1.fence (H1.fence hH1 hf4.1) hf5.1) rfl rfl w _ hst2.1
          rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
          · simp [hdc] at hm
          · have hH3 := vc_st_c_at hLC _ _ (H2.fence hH2 hf6.1) rfl rfl
              (by simp [BitVec.add_comm]) b _ hst3.1
            simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
            refine ⟨vc_rel_ok_at hL hN0 htid hN32 _ _ hH3 rfl rfl (by simp), by simp⟩
  case vc10 =>
    rename_i x σ1 hld af σ2 hz1 σ3 σ4 old σ5 hx af2 σ6 hz2 σ7 y σ8 hld2 σ9 dm σ10 hst3 b' σ11 hrel σ12
      hf1 hf2 hf3 hf4 hf5 hf6 hf7 _
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdl] at hm
    · have hR := vc_ld_spin_at _ hT rfl rfl v _ hst.1
      have hX := vc_xchg_at hN0 _ (Fr.fence (Fr.fence (Fr.fence hR hf1.1) hf2.1) hf3.1) rfl rfl
        (by simp [xchgOp]) old _ hx.1
      rcases hX with ⟨h0, -⟩ | ⟨-, hH1⟩
      · exact absurd hz2 h0
      · rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
        · simp [hdc] at hm
        · have hH2 := vc_ld_c_at hLC _ (H1.fence (H1.fence hH1 hf4.1) hf5.1) rfl rfl w _ hst2.1
          rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
          · simp [hdc] at hm
          · have hH3 := vc_st_c_at hLC _ _ (H2.fence hH2 hf6.1) rfl rfl
              (by simp [BitVec.add_comm]) b _ hst3.1
            have hQ := vc_rel_at hL hN0 htid hN32 _ _ hH3 rfl rfl (by simp) b' _ hrel.1
            refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hdl, by simpa using hdc⟩,
              .inr ⟨rfl, QEnd.fence hQ hf7.1⟩⟩, .inl (by decide)⟩
  case vc1 =>
    exact hT

/-! ## Only release writes -/

open Kraken.Promising.X64.EnvG.SpinRelPure in
/-- The purity table: the frame at `worker`. -/
abbrev spinPureTableV (l c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (EnvR l c)).State → Prop :=
  fun lb s _ => lb = "worker" → FrameV l c s

open Kraken.Promising.X64.EnvG.SpinRelPure in
/-- **The verbatim x64 spinlock worker makes only release writes** (counted,
partial; `spinWorkerG_noNT` verbatim). -/
theorem spinWorkerV_noNT (l c : BitVec 64) (hl : symV "lock" = l) (hc : symV "counter" = c) :
    ∀ s g, FrameV l c s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvR l c)))
        (fun x => (x.1.2 = labV "done" ∧ True) ∨ False) ((s, labV "worker"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvR l c)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (spinPureTableV l c) ?_ rfl (by decide) spinWorkerV_placedIn spinWorkerV_last s g
    (fun _ => hs)
  cfg_cases_env [spinWorkerV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals obtain ⟨hdl, hdc⟩ := hT
  all_goals simp only [Reg64s.get64, SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  case vc1 => simp; trivial
  case vc2 =>
    rename_i x σ1 af hz hld _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdl] at hm
    · refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simpa using hdl, by simpa using hdc⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      have hn := hst.2
      subst hg
      omega
  case vc3 => simp [hdl]
  case vc4 => simp; exact fun h => absurd rfl h
  case vc5 =>
    rename_i x σ1 af hz1 old σ5 af2 hz2 hld hx _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdl] at hm
    · refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simpa using hdl, by simpa using hdc⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      have hn := hst.2
      have hn' := hx.2
      subst hg
      omega
  case vc6 => simp; trivial
  case vc7 => simp; exact fun h => h rfl
  case vc8 =>
    rename_i x σ1 af hz1 old σ5 af2 hz2 y σ8 dm σ10 hld hx hld2 hst3 _
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, -⟩
    · simp [hdc] at hm
    · simp [hdl]
  case vc9 => simp; exact fun h => h rfl
  case vc10 =>
    exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals trivial

end Kraken.Promising.X64.EnvG.SpinAbs
