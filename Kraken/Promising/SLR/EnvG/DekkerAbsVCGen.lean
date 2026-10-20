/-
**Dekker's worker verbatim, on `EnvG` by `vcgen`**:
the worker of `Kraken/Examples/LockFree/X64/dekker_mfence.kl` as written,
with the absolute operand `(counter)` (`dkWorkerV`), run in its image
`dkImageV`: the code followed by the `.kl` runner's data trailer
(`dkDataV`: `flag0`, `flag1`, `counter`, each a label behind a padding
`.byteArray`; `Kraken.Litmus.X64.prepareProgram`). The flags stay in `%rsi`
and `%rdi`, which the `.kl` sets (`0:rsi=flag0; 0:rdi=flag1; ...`).

The VCs are the Dekker proof's, unchanged (`EnvG/DekkerVCX.lean`, at an address
given by an equation: `vc_*_at` of `EnvG/DekkerVCGenX.lean`); the table and
the script are `worker_envG`'s with the frame `FrameDV` (no `%rbx`: the
counter is the symbol, `hc`). Placement: `cfgEnv_partial_at`
(`Kraken/EnvCfgAbs.lean`), from the entry label `worker` to the exit label
`done`.

- `dkWorkerV_envG`: the worker's run in the counted `EnvGX`;
- `dkWorkerV_noNT`: the worker's run in the all-release environment.
-/
import Kraken.Promising.SLR.EnvG.DekkerRelPureX
import Kraken.EnvVCGenAbs
import Kraken.EnvCfgAbs

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Dekker Kraken.Promising.X64.EnvG.Dekker
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.DekkerAbs

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program and its image -/

/-- **Dekker's worker of `dekker_mfence.kl`, verbatim** (its `code` block). -/
def dkWorkerV : Program := parse("
worker:
  xorl %edx,%edx
  movl $1,(%rsi)
  mfence
  movl (%rdi),%eax
  testl %eax,%eax
  jne done
  movl $1,%edx
  movl (counter),%ecx
  addl $1,%ecx
  movl %ecx,(counter)
  movl $0,(%rsi)
  jmp done
done:
")

/-- The `.kl` runner's data trailer of `dekker_mfence.kl`: each symbol a
label behind a padding cell, in the order of first mention (`flag0`,
`flag1`, `counter`). -/
def dkDataV : Program :=
  [.byteArray (.mk #[]), .label "flag0", .byteArray (.mk #[]), .label "flag1", .byteArray (.mk #[]),
    .label "counter"]

/-- The worker's image: the code, then the data trailer. -/
def dkImageV : Program := dkWorkerV ++ dkDataV

/-- info: 14 -/
#guard_msgs in
#eval dkWorkerV.length

theorem dkImageV_wf : Program.WF dkImageV := by decide

theorem dkWorkerV_sub : Program.subBlocksOfE dkWorkerV dkImageV = true := by decide

/-! ## The symbols -/

variable [layout : _root_.Layout]

/-- A label's address in the image (`(sym)` points to `(labD x).toBitVec`). -/
abbrev labD (x : Label) : Int64 := (_root_.Executable.labels (layout dkImageV)).label x

/-- A symbol's address in the image. -/
abbrev symD (x : Label) : BitVec 64 := (labD x).toBitVec

variable [Executable.ValidLayout (layout dkImageV)]

local instance dkImageV.env : CodeEnv := ⟨layout dkImageV⟩

theorem dkWorkerV_placedIn : Program.PlacedIn dkWorkerV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := dkImageV) dkImageV_wf rfl (by decide))
    dkWorkerV_sub

omit [Executable.ValidLayout (layout dkImageV)] in
theorem dkWorkerV_last : ∀ l blk, Program.blockAt dkWorkerV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labD "done" :=
  Program.after_last_of (by decide)

/-! ## The worker -/

/-- The frame: the flags in `%rsi`/`%rdi`, none of the words in `dmem`. -/
abbrev FrameDV (f o c : BitVec 64) (s : MachineData) : Prop :=
  s.regs.get64 .rsi = f ∧ s.regs.get64 .rdi = o ∧ Mem.loadInt s.dmem f 4 = none ∧
    Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none

/-- The worker's table: `D0` at `worker`; at `done`, `edx = 1 → D6`. -/
abbrev dkTableV (tid : Nat) (f o c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (E tid f o c)).State → Prop :=
  fun lb s σ => FrameDV f o c s ∧
    ((lb = "worker" ∧ D0 f o c σ.1) ∨ (lb = "done" ∧ ((s.regs.get64 .rdx).setWidth 32 = 1 → D6 tid f o c σ.1)))

/-- **Dekker's verbatim worker on `EnvG`** (counted, partial): from `D0` at
the entry label, every run that reaches the exit label has `edx = 1 → D6`. -/
theorem dkWorkerV_envG (tid : Nat) (f o c : BitVec 64) (hc : symD "counter" = c) (hL : Locs f o c) :
    ∀ s g, FrameDV f o c s ∧ D0 f o c g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (E tid f o c)))
        (fun x => (x.1.2 = labD "done" ∧ ((x.1.1.regs.get64 .rdx).setWidth 32 = 1 → D6 tid f o c x.2.1)) ∨ False)
        ((s, labD "worker"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (E tid f o c))
    (Q := fun s σ => (s.regs.get64 .rdx).setWidth 32 = 1 → D6 tid f o c σ.1)
    (E := fun _ _ _ => False) (dkTableV tid f o c) ?_ rfl (by decide) dkWorkerV_placedIn dkWorkerV_last s g
    (by simpa [dkTableV] using hsg)
  cfg_cases_env [dkWorkerV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hdf, hdo, hdc⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envG, Reg64s.get64] at *
  case vc1 => simp [hx0, hdf]
  case vc2 =>
    rename_i af1 σ1 hf1 _
    have h0 := (D0.fence hT hf1.1).res
    exact vc_store_ok_at (by rw [h0.qF]; decide) h0.world (by simp) (by simp [hx0])
  case vc3 => exact ⟨trivial, trivial⟩
  case vc4 => exact ⟨trivial, by simp [SharedEnv.AccessIn, hx1]⟩
  case vc5 =>
    rename_i af1 σ1 rb1 σ2 hraise σ3 hfe y σ4 hldO af2 σ5 hnz σ6 hf1 hf2 hf3 _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
      by simpa using hdo, by simpa using hdc⟩, .inr ⟨rfl, fun h => absurd h (by simp)⟩⟩, .inl (by decide)⟩
  case vc6 =>
    rename_i af1 σ1 rb1 σ2 hraise σ3 hfe y σ4 hldO af2 σ5 hnz σ6 σ7 hx hf1 hf2 hf3 hf4 _
    simp [CondCode.interp, StatusFlags.from_result] at hnz
    exact ⟨trivial, by simp [SharedEnv.AccessIn]⟩
  case vc7 =>
    rename_i af1 σ1 rb1 σ2 hraise σ3 hfe y σ4 hldO af2 σ5 hnz σ6 σ7 z σ8 hldC σ9 hx hf1 hf2 hf3 hf4 hf5 _
    simp [CondCode.interp, StatusFlags.from_result] at hnz
    have e1 := vc_raise_at (tid := tid) hL (D0.fence hT hf1.1) (by simp [hx0]) (by simp) _ _ hraise.1
    have e2 := vc_fence e1 hfe.1
    rcases hldO with ⟨w, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx1, hdo] at hm
    have e3 := D3.fence (D3.fence (D3.fence (vc_readO_at e2 (by simp [hx1]) _ _ hst.1) hf2.1) hf3.1) hf4.1
    rcases hldC with ⟨w, hm, -, -⟩ | ⟨-, x, hst', rfl⟩
    · simp [hdc] at hm
    have e4 := D4.fence (vc_readC_at e3 hnz rfl _ _ hst'.1) hf5.1
    obtain ⟨XF, h⟩ := e4.res
    exact vc_store_ok_at (by rw [h.qC]; decide +kernel) h.world (by simp) rfl
  case vc8 =>
    rename_i af1 σ1 rb1 σ2 hraise σ3 hfe y σ4 hldO af2 σ5 hnz σ6 σ7 z σ8 hldC σ9 dm σ10 hstC hf1 hf2 hf3 hf4 hf5 _
    rcases hstC with ⟨hsome, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hdc] at hsome
    simp [hx0, hdf]
  case vc9 =>
    rename_i af1 σ1 rb1 σ2 hraise σ3 hfe y σ4 hldO af2 σ5 hnz σ6 σ7 z σ8 hldC σ9 dm σ10 hstC hf1 hf2 hf3 hf4 hf5 _
    simp [CondCode.interp, StatusFlags.from_result] at hnz
    have e1 := vc_raise_at (tid := tid) hL (D0.fence hT hf1.1) (by simp [hx0]) (by simp) _ _ hraise.1
    have e2 := vc_fence e1 hfe.1
    rcases hldO with ⟨w, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx1, hdo] at hm
    have e3 := D3.fence (D3.fence (D3.fence (vc_readO_at e2 (by simp [hx1]) _ _ hst.1) hf2.1) hf3.1) hf4.1
    rcases hldC with ⟨w, hm, -, -⟩ | ⟨-, x, hst', rfl⟩
    · simp [hdc] at hm
    have e4 := D4.fence (vc_readC_at e3 hnz rfl _ _ hst'.1) hf5.1
    rcases hstC with ⟨hsome, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hdc] at hsome
    have e5 := vc_writeC_at hL e4 rfl (by rw [← inc_eq]; simp) _ _ hst3.1
    obtain ⟨XF, XC, h⟩ := e5.res
    exact vc_store_ok_at (by rw [h.qF]; decide) h.world (by simp) (by simp [hx0])
  case vc10 =>
    rename_i af1 σ1 rb1 σ2 hraise σ3 hfe y σ4 hldO af2 σ5 hnz σ6 σ7 z σ8 hldC σ9 dm σ10 hstC rb2 σ11 hlow σ12 hf1 hf2 hf3 hf4 hf5 hf6 _
    simp [CondCode.interp, StatusFlags.from_result] at hnz
    have e1 := vc_raise_at (tid := tid) hL (D0.fence hT hf1.1) (by simp [hx0]) (by simp) _ _ hraise.1
    have e2 := vc_fence e1 hfe.1
    rcases hldO with ⟨w, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx1, hdo] at hm
    have e3 := D3.fence (D3.fence (D3.fence (vc_readO_at e2 (by simp [hx1]) _ _ hst.1) hf2.1) hf3.1) hf4.1
    rcases hldC with ⟨w, hm, -, -⟩ | ⟨-, x, hst', rfl⟩
    · simp [hdc] at hm
    have e4 := D4.fence (vc_readC_at e3 hnz rfl _ _ hst'.1) hf5.1
    rcases hstC with ⟨hsome, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hdc] at hsome
    have e5 := vc_writeC_at hL e4 rfl (by rw [← inc_eq]; simp) _ _ hst3.1
    have e6 := D6.fence (vc_lower_at hL e5 (by simp [hx0]) (by simp) _ _ hlow.1) hf6.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdf,
      by simpa using hdo, by simpa using hdc⟩, .inr ⟨rfl, fun _ => e6⟩⟩, .inl (by decide)⟩
  case vc1 =>
    exact hT ‹_›

/-! ## Only release writes -/

/-- The all-release table: the frame at `worker`. -/
abbrev relTableV (f o c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (EnvR f o c)).State → Prop :=
  fun lb s _ => lb = "worker" → FrameDV f o c s

/-- **Dekker's verbatim worker writes only by releases** (counted,
partial). -/
theorem dkWorkerV_noNT (f o c : BitVec 64) (hc : symD "counter" = c) :
    ∀ s g, FrameDV f o c s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvR f o c)))
        (fun x => (x.1.2 = labD "done" ∧ True) ∨ False) ((s, labD "worker"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvR f o c)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (relTableV f o c) ?_ rfl (by decide) dkWorkerV_placedIn dkWorkerV_last s g
    (fun _ => hs)
  cfg_cases_env [dkWorkerV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  all_goals obtain ⟨hx0, hx1, hdf, hdo, hdc⟩ := hT
  all_goals simp only [Reg64s.get64] at hx0 hx1
  case vc4 | vc9 => exact Table.ofLabelsEnv_at ⟨by decide, fun h => absurd h (by decide), .inl (by decide)⟩
  all_goals simp_all
  all_goals first
    | trivial
    | exact fun h => h rfl

end Kraken.Promising.X64.EnvG.DekkerAbs
