/-
**Part 3: the `swpl`-released SWP spinlock
worker on `EnvGC` by `vcgen`**: the whole worker `swplWorker` as a
`PartialTripleEnv` in the counted `EnvGC`, by `cfgEnv_partial` with the CAS
lock's five-label table shape (`CasVCGen.casTable`) and the VCs of
`EnvG/SwplLockVC.lean`. The swaps use the generic `swp_shared_spec`; the
`EnvGC` simp set and `FenceMono` instance are `RmwGhostVCGen`'s.

The VCs are restated at an address and operation given by equations (`*_at`,
as in `X64SpinVCGen`): a step hypothesis cannot be rewritten by `simp`.
-/
import Kraken.Promising.SLR.EnvG.SwplLockVC
import Kraken.Promising.SLR.EnvG.A64VCGen
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon

namespace Kraken.Promising.SLR.EnvG.SwplLock

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The table predicates are monotone under fences -/

theorem Fr.fence {P : Sys} {tid : Nat} {σ σ' : State isa} (h : Fr P tid σ) (hf : FenceLe σ σ') : Fr P tid σ' := by
  unfold Fr LkFwdM LkLe LockVC.LkLe; rw [hf.g, hf.r, hf.getFwd, hf.getCoh, hf.snap]; exact h

theorem H1.fence {P : Sys} {tid : Nat} {σ σ' : State isa} (h : H1 P tid σ) (hf : FenceLe σ σ') : H1 P tid σ' :=
  LockVC.H1.fence h hf

theorem H2.fence {P : Sys} {tid : Nat} {x5 : BitVec 32} {σ σ' : State isa} (h : H2 P tid x5 σ)
    (hf : FenceLe σ σ') : H2 P tid x5 σ' :=
  LockVC.H2.fence h hf

theorem H3.fence {P : Sys} {tid : Nat} {x5 : BitVec 32} {σ σ' : State isa} (h : H3 P tid x5 σ)
    (hf : FenceLe σ σ') : H3 P tid x5 σ' :=
  LockVC.H3.fence h hf

theorem QEnd.fence {P : Sys} {σ σ' : State isa} (h : QEnd P σ) (hf : FenceLe σ σ') : QEnd P σ' :=
  LockVC.QEnd.fence h hf

/-! ## The swap VCs at an operation given by an equation -/

section At

variable {P : Sys} {tid : Nat} {a : BitVec 64}

theorem vc_swpa_ok_at (hN0 : 0 < P.N) (σ : State isa) (h : Fr P tid σ) (ha : a = P.Lk.addr) (hn : 4 = P.Lk.bytes)
    {op : Val → Option Val} (hop : ∀ x, op x = some 1#128) : (E P tid).ok (.rmw .acq a 4 op) σ := by
  subst ha; rw [hn]; exact (vc_swpa hN0 σ h op hop).1

theorem vc_swpa_at (hN0 : 0 < P.N) (σ : State isa) (h : Fr P tid σ) (ha : a = P.Lk.addr) (hn : 4 = P.Lk.bytes)
    {op : Val → Option Val} (hop : ∀ x, op x = some 1#128) :
    ∀ old (σ' : State isa), (E P tid).step (.rmw .acq a 4 op) σ old σ' →
      (BitVec.setWidth 32 old ≠ 0 ∧ Fr P tid σ') ∨ (BitVec.setWidth 32 old = 0 ∧ H1 P tid σ') := by
  subst ha; rw [hn]; exact (vc_swpa hN0 σ h op hop).2

theorem vc_swpl_ok_at (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N)
    (hN32 : P.N < 2 ^ 32) (x5 : BitVec 32) (σ : State isa) (h : H3 P tid x5 σ) (ha : a = P.Lk.addr)
    (hn : 4 = P.Lk.bytes) {op : Val → Option Val} (hop : ∀ x, op x = some 0) :
    (E P tid).ok (.rmw .rel a 4 op) σ := by
  subst ha; rw [hn]; exact (vc_swpl hL hN0 htid hN32 x5 σ h op hop).1

theorem vc_swpl_at (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N)
    (hN32 : P.N < 2 ^ 32) (x5 : BitVec 32) (σ : State isa) (h : H3 P tid x5 σ) (ha : a = P.Lk.addr)
    (hn : 4 = P.Lk.bytes) {op : Val → Option Val} (hop : ∀ x, op x = some 0) :
    ∀ old (σ' : State isa), (E P tid).step (.rmw .rel a 4 op) σ old σ' → QEnd P σ' := by
  subst ha; rw [hn]; exact (vc_swpl hL hN0 htid hN32 x5 σ h op hop).2

end At

/-! ## The worker -/

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swplWorker)]

local instance swplWorker.envG : CodeEnv := ⟨layout swplWorker⟩

/-- The worker's table (`CasVCGen.casTable`'s shape). -/
abbrev swplTable (P : Sys) (tid : Nat) (l c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (E P tid)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
    Mem.loadInt s.dmem c 4 = none ∧
    ((lb = "worker" ∧ Fr P tid σ.1) ∨ ((lb = "try" ∨ lb = "spin") ∧ s.regs.X3.toBitVec.setWidth 32 = 1 ∧ Fr P tid σ.1) ∨
      (lb = "cs" ∧ H1 P tid σ.1) ∨ (lb = "done" ∧ QEnd P σ.1))

/-- **The `swpl`-released SWP worker on `EnvGC`** (counted, partial): from
`Fr`, every run that reaches the end is in `QEnd`. -/
theorem swplWorker_envGC (P : Sys) (tid : Nat) (l c : BitVec 64) (hLk : P.Lk = ⟨l, 4⟩) (hC : P.C = ⟨c, 4⟩)
    (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32) :
    PartialTripleEnv (SharedEnv.counted (E P tid))
      (fun s σ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
        Mem.loadInt s.dmem c 4 = none ∧ Fr P tid σ.1)
      swplWorker (fun _ σ => QEnd P σ.1) (fun _ _ _ => False) := by
  obtain ⟨N, Lk, C, K, F⟩ := P
  simp only at hLk hC
  subst hLk hC
  have hLC : Sys.Lk ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ ≠ Sys.C ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ := hL.lk_c
  apply MachineWP.cfgEnv_partial (swplTable ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid l c)
    (hP := by funext s g; simp [swplTable])
  cfg_cases_env [swplWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdl, hdc, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGC, SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hdl, hdc]; done)
  · -- `mov w3, #1`, then `try`
    rename_i hf _
    simp [hx0, hx1, hdl, hdc]
    exact Fr.fence hT hf.1
  · -- the `swpa` is permitted
    exact vc_swpa_ok_at hN0 _ hT.2 (by simp [hx0]) rfl (fun x => by simp [rmwOpBits, hT.1])
  · -- the `swpa` read `0`: `cs`
    rename_i s σ0 old σ1 hz σ2 hst hf _
    have hc := vc_swpa_at hN0 _ hT.2 (by simp [hx0]) rfl (fun x => by simp [rmwOpBits, hT.1]) old σ1.1 hst.1
    rcases hc with ⟨h0, -⟩ | ⟨-, hH⟩
    · exact absurd (by simpa using hz) h0
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdl], by simp [hdc],
      .inr (.inr (.inl ⟨rfl, H1.fence hH hf.1⟩))⟩, .inl (by decide)⟩
  · -- the `swpa` read a non-zero word: `spin`
    rename_i s σ0 old σ1 hz σ2 hst hf _
    have hc := vc_swpa_at hN0 _ hT.2 (by simp [hx0]) rfl (fun x => by simp [rmwOpBits, hT.1]) old σ1.1 hst.1
    rcases hc with ⟨-, hF⟩ | ⟨h0, -⟩
    · simp [hx0, hx1, hdl, hdc, hT.1]
      exact Fr.fence hF hf.1
    · exact absurd (by simpa using h0) hz
  · -- `ldr w2, [x0]`, `cbnz` taken: `spin` again; the counter moved
    rename_i s σ0 rng val σ1 hnz σ2 hld hf _
    simp [hx0, hdl] at hld
    obtain ⟨v, hst, rfl⟩ := hld
    have hF := vc_ldr_spin σ0.1 hT.2 v σ1.1 (by simpa using hst.1)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdl], by simp [hdc],
      .inr (.inl ⟨.inr rfl, by simpa using hT.1, Fr.fence hF hf.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  · -- `ldr w2, [x0]`, `cbnz` not taken, `b try`; the counter moved
    rename_i s σ0 rng val σ1 hnz σ2 σ3 hld hf1 hf2 _
    simp [hx0, hdl] at hld
    obtain ⟨v, hst, rfl⟩ := hld
    have hF := vc_ldr_spin σ0.1 hT.2 v σ1.1 (by simpa using hst.1)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdl], by simp [hdc],
      .inr (.inl ⟨.inl rfl, by simpa using hT.1, Fr.fence (Fr.fence hF hf1.1) hf2.1⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; omega
  · -- `ldr w5, [x1]`, `add`, `str w5, [x1]` is permitted
    rename_i s σ0 r1 val σ1 r2 σ2 r3 _ hld hf _
    simp [hx1, hdc] at hld
    obtain ⟨v, hst, rfl⟩ := hld
    have hH2 := vc_ldr_c hLC σ0.1 hT v σ1.1 (by simpa using hst.1)
    have hs := (vc_str_c hLC _ σ2.1 (H2.fence hH2 hf.1)).1
    simpa [hx1] using hs
  · -- the private memory is untouched by the shared store
    rename_i s σ0 r1 val σ1 r2 σ2 r3 dm σ3 hld hf hst _
    simp [hx1, hdc] at hld
    obtain ⟨v, -, rfl⟩ := hld
    simp [hx1, hdc] at hst
    simp [hst.1, hx0, hdl]
  · -- `swpl wzr, w2, [x0]` is permitted
    rename_i s σ0 r1 val σ1 r2 σ2 r3 dm σ3 hld hf hst _
    simp [hx1, hdc] at hld
    obtain ⟨v, hl, rfl⟩ := hld
    have hH2 := vc_ldr_c hLC σ0.1 hT v σ1.1 (by simpa using hl.1)
    have hs := (vc_str_c hLC _ σ2.1 (H2.fence hH2 hf.1)).2
    simp [hx1, hdc] at hst
    have hH3 : H3 ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid (BitVec.setWidth 32 v + 1) σ3.1 := by
      rcases hst.2.1 with h | h <;> exact hs _ _ (by simpa using h)
    exact vc_swpl_ok_at hL hN0 htid hN32 _ σ3.1 hH3 (by simp [hx0]) rfl (fun x => by simp [rmwOpBits])
  · -- after the release: `done`
    rename_i s σ0 r1 val σ1 r2 σ2 r3 dm σ3 old σ4 σ5 hld hf1 hst hst' hf _
    simp [hx1, hdc] at hld
    obtain ⟨v, hl, rfl⟩ := hld
    have hH2 := vc_ldr_c hLC σ0.1 hT v σ1.1 (by simpa using hl.1)
    have hs := (vc_str_c hLC _ σ2.1 (H2.fence hH2 hf1.1)).2
    simp [hx1, hdc] at hst
    have hH3 : H3 ⟨N, ⟨l, 4⟩, ⟨c, 4⟩, K, F⟩ tid (BitVec.setWidth 32 v + 1) σ3.1 := by
      rcases hst.2.1 with h | h <;> exact hs _ _ (by simpa using h)
    have hQ := QEnd.fence (vc_swpl_at hL hN0 htid hN32 _ σ3.1 hH3 (by simp [hx0]) rfl
      (fun x => by simp [rmwOpBits]) old σ4.1 hst'.1) hf.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hst.1, hdl], by simp [hst.1, hdc],
      .inr (.inr (.inr ⟨rfl, hQ⟩))⟩, .inl (by decide)⟩
  · exact hT

end Kraken.Promising.SLR.EnvG.SwplLock
