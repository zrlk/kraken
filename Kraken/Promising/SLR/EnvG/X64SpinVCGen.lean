/-
**The x64 xchg spinlock worker on `EnvG` by `vcgen`**: the worker of `Kraken/Examples/LockFree/X64/spinlock2.kl`, with the
lock and the counter addressed through `%rdi`/`%rsi` (as the old proof's
`X64SpinTrees.spinWorker`; the text is the same), as a `PartialTripleEnv` in
the counted `EnvGX` (`EnvG` restricted to `[(l, 4), (c, 4)]`, `Arch.tso`), by
`cfgEnv_partial` with a two-label table (`worker`: `Fr`; `done`: `QEnd`) and
the VCs of `EnvG/X64SpinVC.lean`.

The `testl`, `xchgl`, `addl $1` and `movl $0, (%rdi)` cells use the rules of
`EnvG/X64SpinSpecs.lean`; the silent cells `envMonoX_lift_spec`
(`EnvG/X64VCGen.lean`). The VCs are restated at an address, operation and
value given by equations (`*_at`), as in `X64MpVCGen`: a step hypothesis
cannot be rewritten by `simp`.
-/
import Kraken.Promising.SLR.EnvG.X64SpinVC
import Kraken.Promising.SLR.EnvG.X64SpinSpecs
import Kraken.Promising.SLR.EnvG.X64VCGen
import Kraken.X64.Parser

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.Spin

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program -/

/-- **The x64 spinlock worker** of `spinlock2.kl` (`code` block verbatim,
with `(lock)`/`(counter)` as `(%rdi)`/`(%rsi)`): test-and-test-and-set with a
plain-load spin, `xchgl` acquire, plain increment of the counter, plain-store
release `movl $0`. -/
def spinWorkerG : Program := parse("
worker:
  movl (%rdi),%eax
  testl %eax,%eax
  jne worker
  movl $1,%eax
  xchgl %eax,(%rdi)
  testl %eax,%eax
  jne worker
  movl (%rsi),%ecx
  addl $1,%ecx
  movl %ecx,(%rsi)
  movl $0,(%rdi)
  jmp done
done:
")

/-- info: 14 -/
#guard_msgs in
#eval spinWorkerG.length

/-- The environment of thread `tid` (x64, `Arch.tso`), on the lock and
counter words. -/
noncomputable abbrev E (P : Sys) (tid : Nat) (l c : BitVec 64) : SharedEnv :=
  EnvGX Arch.tso tid (xlockPlan P tid) [(l, 4), (c, 4)]

/-! ## The table predicates are monotone under fences -/

theorem Fr.fence {P : Sys} {tid : Nat} {σ σ' : EStateX} (h : Fr P tid σ) (hf : FenceLe σ σ') : Fr P tid σ' := by
  unfold Fr LkFwd LkLe LockVC.LkLe; rw [hf.g, hf.r, hf.getFwd, hf.getCoh]; exact h

theorem H1.fence {P : Sys} {tid : Nat} {σ σ' : EStateX} (h : H1 P tid σ) (hf : FenceLe σ σ') : H1 P tid σ' :=
  LockVC.H1.fence h hf

theorem H2.fence {P : Sys} {tid : Nat} {x5 : BitVec 32} {σ σ' : EStateX} (h : H2 P tid x5 σ)
    (hf : FenceLe σ σ') : H2 P tid x5 σ' :=
  LockVC.H2.fence h hf

theorem H3.fence {P : Sys} {tid : Nat} {x5 : BitVec 32} {σ σ' : EStateX} (h : H3 P tid x5 σ)
    (hf : FenceLe σ σ') : H3 P tid x5 σ' :=
  LockVC.H3.fence h hf

theorem QEnd.fence {P : Sys} {σ σ' : EStateX} (h : QEnd P σ) (hf : FenceLe σ σ') : QEnd P σ' :=
  LockVC.QEnd.fence h hf

/-! ## The VCs at an address, operation and value given by equations -/

section At

variable {P : Sys} {tid : Nat} {a : BitVec 64}

theorem vc_ld_spin_at (σ : EStateX) (h : Fr P tid σ) (ha : a = P.Lk.addr) (hn : 4 = P.Lk.bytes) :
    ∀ v (σ' : EStateX), (EG P tid).step (.load .plain false a 4) σ v σ' → Fr P tid σ' := by
  subst ha; rw [hn]; exact vc_ld_spin σ h

theorem vc_xchg_ok_at (hN0 : 0 < P.N) (σ : EStateX) (h : Fr P tid σ) {op : Val → Option Val}
    (ha : a = P.Lk.addr) (hn : 4 = P.Lk.bytes) (hop : op = xchgOp) : (EG P tid).ok (.rmw .acqRel a 4 op) σ := by
  subst ha hop; rw [hn]; exact (vc_xchg hN0 σ h).1

theorem vc_xchg_at (hN0 : 0 < P.N) (σ : EStateX) (h : Fr P tid σ) {op : Val → Option Val}
    (ha : a = P.Lk.addr) (hn : 4 = P.Lk.bytes) (hop : op = xchgOp) :
    ∀ old (σ' : EStateX), (EG P tid).step (.rmw .acqRel a 4 op) σ old σ' →
      (BitVec.setWidth 32 old ≠ 0 ∧ Fr P tid σ') ∨ (BitVec.setWidth 32 old = 0 ∧ H1 P tid σ') := by
  subst ha hop; rw [hn]; exact (vc_xchg hN0 σ h).2

theorem vc_ld_c_at (hLC : P.Lk ≠ P.C) (σ : EStateX) (h : H1 P tid σ) (ha : a = P.C.addr) (hn : 4 = P.C.bytes) :
    ∀ v (σ' : EStateX), (EG P tid).step (.load .plain false a 4) σ v σ' → H2 P tid (BitVec.setWidth 32 v) σ' := by
  subst ha; rw [hn]; exact vc_ld_c hLC σ h

theorem vc_st_c_ok_at (hLC : P.Lk ≠ P.C) (x5 : BitVec 32) (σ : EStateX) (h : H2 P tid x5 σ) {v : Val}
    (ha : a = P.C.addr) (hn : 4 = P.C.bytes) (hv : v = BitVec.setWidth 128 (x5 + 1)) :
    (EG P tid).ok (.store .plain false a 4 v) σ := by
  subst ha hv; rw [hn]; exact (vc_st_c hLC x5 σ h).1

theorem vc_st_c_at (hLC : P.Lk ≠ P.C) (x5 : BitVec 32) (σ : EStateX) (h : H2 P tid x5 σ) {v : Val}
    (ha : a = P.C.addr) (hn : 4 = P.C.bytes) (hv : v = BitVec.setWidth 128 (x5 + 1)) :
    ∀ b (σ' : EStateX), (EG P tid).step (.store .plain false a 4 v) σ b σ' → H3 P tid (x5 + 1) σ' := by
  subst ha hv; rw [hn]; exact (vc_st_c hLC x5 σ h).2

theorem vc_rel_ok_at (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32)
    (x5 : BitVec 32) (σ : EStateX) (h : H3 P tid x5 σ) {v : Val} (ha : a = P.Lk.addr) (hn : 4 = P.Lk.bytes)
    (hv : v = 0) : (EG P tid).ok (.store .plain false a 4 v) σ := by
  subst ha hv; rw [hn]; exact (vc_rel hL hN0 htid hN32 x5 σ h).1

theorem vc_rel_at (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32)
    (x5 : BitVec 32) (σ : EStateX) (h : H3 P tid x5 σ) {v : Val} (ha : a = P.Lk.addr) (hn : 4 = P.Lk.bytes)
    (hv : v = 0) : ∀ b (σ' : EStateX), (EG P tid).step (.store .plain false a 4 v) σ b σ' → QEnd P σ' := by
  subst ha hv; rw [hn]; exact (vc_rel hL hN0 htid hN32 x5 σ h).2

end At

/-! ## The worker -/

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spinWorkerG)]

local instance spinWorkerG.env : CodeEnv := ⟨layout spinWorkerG⟩

/-- The worker's frame: `rdi = l`, `rsi = c`, neither word in `dmem`. -/
abbrev FrameX (l c : BitVec 64) (s : MachineData) : Prop :=
  s.regs.get64 .rdi = l ∧ s.regs.get64 .rsi = c ∧ Mem.loadInt s.dmem l 4 = none ∧ Mem.loadInt s.dmem c 4 = none

/-- The worker's table: `Fr` at `worker`, `QEnd` at `done`. -/
abbrev spinTable (P : Sys) (tid : Nat) (l c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (E P tid l c)).State → Prop :=
  fun lb s σ => FrameX l c s ∧ ((lb = "worker" ∧ Fr P tid σ.1) ∨ (lb = "done" ∧ QEnd P σ.1))

/-- **The x64 spinlock worker on `EnvG`** (counted, partial): from `Fr`, every
run that reaches the end is in `QEnd`. -/
theorem spinWorkerG_envG (P : Sys) (tid : Nat) (l c : BitVec 64) (hLk : P.Lk = ⟨l, 4⟩) (hC : P.C = ⟨c, 4⟩)
    (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32) :
    PartialTripleEnv (SharedEnv.counted (E P tid l c))
      (fun s σ => FrameX l c s ∧ Fr P tid σ.1) spinWorkerG (fun _ σ => QEnd P σ.1) (fun _ _ _ => False) := by
  obtain ⟨N, Lk, C, K, F⟩ := P
  simp only at hLk hC
  subst hLk hC
  have hLC : Sys.Lk ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ ≠ Sys.C ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ := hL.lk_c
  apply MachineWP.cfgEnv_partial (spinTable ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid l c)
    (hP := by funext s g; simp [spinTable])
  cfg_cases_env [spinWorkerG]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hdl, hdc⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envG, Reg64s.get64] at *
  case vc1 =>
    simp [hx0] <;> trivial
  case vc2 =>
    rename_i x σ1 hld af σ2 hz σ3 hf1 hf2 _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdl] at hm
    · have hR := vc_ld_spin_at _ hT (by simp [hx0]) rfl v _ hst.1
      have hn := hst.2
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdl,
        by simpa using hdc⟩, .inl ⟨rfl, Fr.fence (Fr.fence hR hf1.1) hf2.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      simp [SharedAccess.tick] at hn
      omega
  case vc3 =>
    simp [hx0, hdl]
  case vc4 =>
    rename_i x σ1 hld af σ2 hz σ3 σ4 hf1 hf2 hf3 _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdl] at hm
    · have hR := vc_ld_spin_at _ hT (by simp [hx0]) rfl v _ hst.1
      simp only [SharedEnv.counted_ok, SharedEnv.within_ok_rmw]
      refine ⟨vc_xchg_ok_at hN0 _ (Fr.fence (Fr.fence (Fr.fence hR hf1.1) hf2.1) hf3.1) (by simp [hx0]) rfl
        (by simp [xchgOp]), by simp [hx0]⟩
  case vc5 =>
    rename_i x σ1 hld af σ2 hz1 σ3 σ4 old σ5 hx af2 σ6 hz2 σ7 hf1 hf2 hf3 hf4 hf5 _
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdl] at hm
    · have hR := vc_ld_spin_at _ hT (by simp [hx0]) rfl v _ hst.1
      have hX := vc_xchg_at hN0 _ (Fr.fence (Fr.fence (Fr.fence hR hf1.1) hf2.1) hf3.1) (by simp [hx0]) rfl
        (by simp [xchgOp]) old _ hx.1
      rcases hX with ⟨-, hF⟩ | ⟨h0, -⟩
      · have hn := hst.2
        have hn' := hx.2
        refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdl,
          by simpa using hdc⟩, .inl ⟨rfl, Fr.fence (Fr.fence hF hf4.1) hf5.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
        subst hg
        simp [SharedAccess.tick] at hn hn'
        omega
      · exact absurd h0 hz2
  case vc6 =>
    simp [hx1] <;> trivial
  case vc7 =>
    rename_i x σ1 hld af σ2 hz1 σ3 σ4 old σ5 hx af2 σ6 hz2 σ7 y σ8 hld2 σ9 hl hf1 hf2 hf3 hf4 hf5 hf6 _
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdl] at hm
    · have hR := vc_ld_spin_at _ hT (by simp [hx0]) rfl v _ hst.1
      have hX := vc_xchg_at hN0 _ (Fr.fence (Fr.fence (Fr.fence hR hf1.1) hf2.1) hf3.1) (by simp [hx0]) rfl
        (by simp [xchgOp]) old _ hx.1
      rcases hX with ⟨h0, -⟩ | ⟨-, hH1⟩
      · exact absurd hz2 h0
      · rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
        · simp [hx1, hdc] at hm
        · have hH2 := vc_ld_c_at hLC _ (H1.fence (H1.fence hH1 hf4.1) hf5.1) (by simp [hx1]) rfl w _ hst2.1
          simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
          refine ⟨vc_st_c_ok_at hLC _ _ (H2.fence hH2 hf6.1) (by simp [hx1]) rfl
            (by simp [BitVec.add_comm]), by simp [hx1]⟩
  case vc8 =>
    rename_i x σ1 hld af σ2 hz1 σ3 σ4 old σ5 hx af2 σ6 hz2 σ7 y σ8 hld2 σ9 dm σ10 hst3 hf1 hf2 hf3 hf4 hf5 hf6 _
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, -, -⟩
    · simp [hx1, hdc] at hm
    · simp [hx0, hdl]
  case vc9 =>
    rename_i x σ1 hld af σ2 hz1 σ3 σ4 old σ5 hx af2 σ6 hz2 σ7 y σ8 hld2 σ9 dm σ10 hst3 hf1 hf2 hf3 hf4 hf5 hf6 _
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdl] at hm
    · have hR := vc_ld_spin_at _ hT (by simp [hx0]) rfl v _ hst.1
      have hX := vc_xchg_at hN0 _ (Fr.fence (Fr.fence (Fr.fence hR hf1.1) hf2.1) hf3.1) (by simp [hx0]) rfl
        (by simp [xchgOp]) old _ hx.1
      rcases hX with ⟨h0, -⟩ | ⟨-, hH1⟩
      · exact absurd hz2 h0
      · rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
        · simp [hx1, hdc] at hm
        · have hH2 := vc_ld_c_at hLC _ (H1.fence (H1.fence hH1 hf4.1) hf5.1) (by simp [hx1]) rfl w _ hst2.1
          rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
          · simp [hx1, hdc] at hm
          · have hH3 := vc_st_c_at hLC _ _ (H2.fence hH2 hf6.1) (by simp [hx1]) rfl
              (by simp [BitVec.add_comm]) b _ hst3.1
            simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
            refine ⟨vc_rel_ok_at hL hN0 htid hN32 _ _ hH3 (by simp [hx0]) rfl (by simp), by simp [hx0]⟩
  case vc10 =>
    rename_i x σ1 hld af σ2 hz1 σ3 σ4 old σ5 hx af2 σ6 hz2 σ7 y σ8 hld2 σ9 dm σ10 hst3 b' σ11 hrel σ12
      hf1 hf2 hf3 hf4 hf5 hf6 hf7 _
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdl] at hm
    · have hR := vc_ld_spin_at _ hT (by simp [hx0]) rfl v _ hst.1
      have hX := vc_xchg_at hN0 _ (Fr.fence (Fr.fence (Fr.fence hR hf1.1) hf2.1) hf3.1) (by simp [hx0]) rfl
        (by simp [xchgOp]) old _ hx.1
      rcases hX with ⟨h0, -⟩ | ⟨-, hH1⟩
      · exact absurd hz2 h0
      · rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst2, rfl⟩
        · simp [hx1, hdc] at hm
        · have hH2 := vc_ld_c_at hLC _ (H1.fence (H1.fence hH1 hf4.1) hf5.1) (by simp [hx1]) rfl w _ hst2.1
          rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
          · simp [hx1, hdc] at hm
          · have hH3 := vc_st_c_at hLC _ _ (H2.fence hH2 hf6.1) (by simp [hx1]) rfl
              (by simp [BitVec.add_comm]) b _ hst3.1
            have hQ := vc_rel_at hL hN0 htid hN32 _ _ hH3 (by simp [hx0]) rfl (by simp) b' _ hrel.1
            refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdl,
              by simpa using hdc⟩, .inr ⟨rfl, QEnd.fence hQ hf7.1⟩⟩, .inl (by decide)⟩
  case vc1 =>
    exact hT

end Kraken.Promising.X64.EnvG.Spin
