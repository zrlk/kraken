/-
**Dekker's `worker` on `EnvGX` by
`vcgen`**. The worker of
`Kraken/Examples/LockFree/X64/dekker_mfence.kl`, with the counter addressed
through `%rbx` instead of the absolute `(counter)` (as the spinlock workers
address theirs through a register), as a `PartialTripleEnv` in the counted
`EnvGX` by `cfgEnv_partial` with a two-label table (`worker`: the frame and
`D0`; `done`: the frame and `edx = 1 → D6`), and the VCs of
`EnvG/DekkerVCX.lean`.
-/
import Kraken.Promising.SLR.EnvG.DekkerVCX
import Kraken.Promising.SLR.EnvG.X64VCGen
import Kraken.X64.Parser

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Dekker
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.Dekker

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- **Dekker's worker** (`dekker_mfence.kl`'s `code` block, `(counter)` as
`(%rbx)`): raise the own flag `(%rsi)`, `mfence`, read the other flag
`(%rdi)`; if it is down, record entry in `edx`, increment the counter
non-atomically and lower the own flag. -/
def worker : Program := parse("
worker:
  xorl %edx,%edx
  movl $1,(%rsi)
  mfence
  movl (%rdi),%eax
  testl %eax,%eax
  jne done
  movl $1,%edx
  movl (%rbx),%ecx
  addl $1,%ecx
  movl %ecx,(%rbx)
  movl $0,(%rsi)
  jmp done
done:
")

/-- info: 14 -/
#guard_msgs in
#eval worker.length

/-- The frame: the three addresses in their registers, none in `dmem`. -/
abbrev Frame (f o c : BitVec 64) (s : MachineData) : Prop :=
  s.regs.get64 .rsi = f ∧ s.regs.get64 .rdi = o ∧ s.regs.get64 .rbx = c ∧ Mem.loadInt s.dmem f 4 = none ∧
    Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none

/-- The worker's table: `D0` at `worker`; at `done`, `edx = 1 → D6`. -/
abbrev dkTable (tid : Nat) (f o c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (E tid f o c)).State → Prop :=
  fun lb s σ => Frame f o c s ∧
    ((lb = "worker" ∧ D0 f o c σ.1) ∨ (lb = "done" ∧ ((s.regs.get64 .rdx).setWidth 32 = 1 → D6 tid f o c σ.1)))

/-! ## The VCs at an address and value given by equations

As in `X64MpVCGen`: `vcgen`'s goals state addresses and values as register
expressions, so the VCs are restated at any `a = …`, `v = …`. -/

section At

variable {tid : Nat} {f o c : BitVec 64}

theorem vc_raise_at (hL : Locs f o c) {σ : EStateX} (h : D0 f o c σ) {a : BitVec 64} {v : Val}
    (ha : a = f) (hv : v = 1) :
    ∀ b (σ' : EStateX), (E tid f o c).step (.store .plain false a 4 v) σ b σ' → D1 tid f o c σ' := by
  subst ha hv; exact vc_raise hL h

theorem vc_readO_at {σ : EStateX} (h : D2 tid f o c σ) {a : BitVec 64} (ha : a = o) :
    ∀ v (σ' : EStateX), (E tid f o c).step (.load .plain false a 4) σ v σ' → D3 tid f o c v σ' := by
  subst ha; exact vc_readO h

theorem vc_readC_at {σ : EStateX} {v : Val} (h : D3 tid f o c v σ) (hz : v.setWidth 32 = 0) {a : BitVec 64}
    (ha : a = c) :
    ∀ x (σ' : EStateX), (E tid f o c).step (.load .plain false a 4) σ x σ' → D4 tid f o c x σ' := by
  subst ha; exact vc_readC h hz

theorem vc_writeC_at (hL : Locs f o c) {σ : EStateX} {x : Val} (h : D4 tid f o c x σ) {a : BitVec 64} {v : Val}
    (ha : a = c) (hv : v = inc x) :
    ∀ b (σ' : EStateX), (E tid f o c).step (.store .plain false a 4 v) σ b σ' → D5 tid f o c x σ' := by
  subst ha hv; exact vc_writeC hL h

theorem vc_lower_at (hL : Locs f o c) {σ : EStateX} {x : Val} (h : D5 tid f o c x σ) {a : BitVec 64} {v : Val}
    (ha : a = f) (hv : v = 0) :
    ∀ b (σ' : EStateX), (E tid f o c).step (.store .plain false a 4 v) σ b σ' → D6 tid f o c σ' := by
  subst ha hv; exact vc_lower hL h

theorem D0.res {σ : EStateX} (h : D0 f o c σ) : Res0 f c σ X0 X0 := h.1
theorem D4.res {σ : EStateX} {x : Val} (h : D4 tid f o c x σ) : ∃ XF, Res0 f c σ XF X0 := by
  obtain ⟨t, r, trc, v, -, -, -, -, -, h⟩ := h; exact ⟨_, h⟩
theorem D5.res {σ : EStateX} {x : Val} (h : D5 tid f o c x σ) : ∃ XF XC, Res0 f c σ XF XC := by
  obtain ⟨t, r, trc, v, tc, -, -, -, -, -, -, -, h⟩ := h; exact ⟨_, _, h⟩

theorem vc_store_ok_at {σ : EStateX} {a a' : BitVec 64} {v : Val} (hq : 0 < (σ.r.wr ⟨a', 4⟩).q)
    (hw : World σ.g) (hin : (a', 4) ∈ dkS f o c) (ha : a = a') : (E tid f o c).ok (.store .plain false a 4 v) σ := by
  subst ha; exact vc_store_ok hq hw hin

/-- The incremented counter value as `vcgen` states it. -/
theorem inc_eq (x : Val) :
    BitVec.setWidth 128 (BitVec.setWidth 32 (BitVec.setWidth 32 (Int64.toBitVec 1) +
      BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x)))) = inc x := by
  have h1 : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = BitVec.setWidth 32 x := by
    apply BitVec.eq_of_toNat_eq; simp
  have h2 : BitVec.setWidth 32 (Int64.toBitVec 1) = 1#32 := by decide
  simp only [inc, h1, h2, BitVec.setWidth_eq]; rw [BitVec.add_comm]; rfl

end At

variable [layout : _root_.Layout] [Executable.ValidLayout (layout worker)]

local instance worker.env : CodeEnv := ⟨layout worker⟩

/-- **Dekker's worker on `EnvG`** (counted, partial): from `D0`, every run
that reaches the end has `edx = 1 → D6`. -/
theorem worker_envG (tid : Nat) (f o c : BitVec 64) (hL : Locs f o c) :
    PartialTripleEnv (SharedEnv.counted (E tid f o c))
      (fun s σ => Frame f o c s ∧ D0 f o c σ.1) worker
      (fun s σ => (s.regs.get64 .rdx).setWidth 32 = 1 → D6 tid f o c σ.1) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (dkTable tid f o c) (hP := by funext s g; simp [dkTable])
  cfg_cases_env [worker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hx2, hdf, hdo, hdc⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
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
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf,
      by simpa using hdo, by simpa using hdc⟩, .inr ⟨rfl, fun h => absurd h (by simp)⟩⟩, .inl (by decide)⟩
  case vc6 =>
    rename_i af1 σ1 rb1 σ2 hraise σ3 hfe y σ4 hldO af2 σ5 hnz σ6 σ7 hx hf1 hf2 hf3 hf4 _
    simp [CondCode.interp, StatusFlags.from_result] at hnz
    exact ⟨trivial, by simp [SharedEnv.AccessIn, hx2]⟩
  case vc7 =>
    rename_i af1 σ1 rb1 σ2 hraise σ3 hfe y σ4 hldO af2 σ5 hnz σ6 σ7 z σ8 hldC σ9 hx hf1 hf2 hf3 hf4 hf5 _
    simp [CondCode.interp, StatusFlags.from_result] at hnz
    have e1 := vc_raise_at (tid := tid) hL (D0.fence hT hf1.1) (by simp [hx0]) (by simp) _ _ hraise.1
    have e2 := vc_fence e1 hfe.1
    rcases hldO with ⟨w, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx1, hdo] at hm
    have e3 := D3.fence (D3.fence (D3.fence (vc_readO_at e2 (by simp [hx1]) _ _ hst.1) hf2.1) hf3.1) hf4.1
    rcases hldC with ⟨w, hm, -, -⟩ | ⟨-, x, hst', rfl⟩
    · simp [hx2, hdc] at hm
    have e4 := D4.fence (vc_readC_at e3 hnz (by simp [hx2]) _ _ hst'.1) hf5.1
    obtain ⟨XF, h⟩ := e4.res
    exact vc_store_ok_at (by rw [h.qC]; decide +kernel) h.world (by simp) (by simp [hx2])
  case vc8 =>
    rename_i af1 σ1 rb1 σ2 hraise σ3 hfe y σ4 hldO af2 σ5 hnz σ6 σ7 z σ8 hldC σ9 dm σ10 hstC hf1 hf2 hf3 hf4 hf5 _
    rcases hstC with ⟨hsome, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hx2, hdc] at hsome
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
    · simp [hx2, hdc] at hm
    have e4 := D4.fence (vc_readC_at e3 hnz (by simp [hx2]) _ _ hst'.1) hf5.1
    rcases hstC with ⟨hsome, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hx2, hdc] at hsome
    have e5 := vc_writeC_at hL e4 (by simp [hx2]) (by rw [← inc_eq]; simp) _ _ hst3.1
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
    · simp [hx2, hdc] at hm
    have e4 := D4.fence (vc_readC_at e3 hnz (by simp [hx2]) _ _ hst'.1) hf5.1
    rcases hstC with ⟨hsome, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hx2, hdc] at hsome
    have e5 := vc_writeC_at hL e4 (by simp [hx2]) (by rw [← inc_eq]; simp) _ _ hst3.1
    have e6 := D6.fence (vc_lower_at hL e5 (by simp [hx0]) (by simp) _ _ hlow.1) hf6.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simp [hx2], by simpa using hdf,
      by simpa using hdo, by simpa using hdc⟩, .inr ⟨rfl, fun _ => e6⟩⟩, .inl (by decide)⟩
  case vc1 =>
    exact hT ‹_›

end Kraken.Promising.X64.EnvG.Dekker
