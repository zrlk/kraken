/-
**Item 2, part 2: the `ldaddal` ticket lock
worker on `EnvGTDR` by `vcgen`** (`EnvG/TicketLockVCGen.lean` for
`tkWorkerAl`): the whole worker as a `PartialTripleEnv` in the counted
`EnvGTDR` (`EAl`), by `cfgEnv_partial` with the three-label table of
`tkWorker`. The `ldaddal` uses `vc_ldaddal` (`EnvG/TicketAlSmoke.lean`); the
loads and stores reuse `vc_ldar_at`, `vc_ldr_at`, `vc_str_*at`, `vc_stlr_*at`
of `EnvG/TicketLockVCGen.lean` (stated for `E`; `EAl` has the same `ok` and
`step` at loads and stores, definitionally).
-/
import Kraken.Promising.SLR.EnvG.TicketAlSmoke
import Kraken.Promising.SLR.EnvG.TicketLockVCGen

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.SLR.EnvG.TicketLock

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The `ldaddal` VC at an address given by an equation -/

section At

variable {P : Sys} (hL : Locs P) {tid : Nat} {a : BitVec 64}

theorem vc_ldaddal_ok_at (σ : State isa) (h : Start P tid σ) (ha : a = P.X.addr) (hn : 4 = P.X.bytes)
    {op : Val → Option Val} (hop : ∀ x, op x = some ((x.setWidth 32 + 1#32).setWidth 128)) :
    (EAl isa P hL tid).ok (.rmw .acqRel a 4 op) σ := by
  subst ha; rw [hn]; exact (vc_ldaddal hL σ h hop).1

theorem vc_ldaddal_at (σ : State isa) (h : Start P tid σ) (ha : a = P.X.addr) (hn : 4 = P.X.bytes)
    {op : Val → Option Val} (hop : ∀ x, op x = some ((x.setWidth 32 + 1#32).setWidth 128)) :
    ∀ old (σ' : State isa), (EAl isa P hL tid).step (.rmw .acqRel a 4 op) σ old σ' → Spin P tid old.toNat σ' := by
  subst ha; rw [hn]; exact (vc_ldaddal hL σ h hop).2

/-! The store VCs of `EnvG/TicketLockVCGen.lean`, restated at `EAl` (same
`ok` and `step` as `E` at stores, definitionally). -/

theorem vc_str_ok_atAl {t : Nat} {v u : Val} (σ : State isa) (h : Read P tid t v σ)
    (hu : v.toNat = t → u.toNat = t + 1) (ha : a = P.C.addr) (hn : 4 = P.C.bytes) :
    (EAl isa P hL tid).ok (.store .plain false a 4 u) σ :=
  vc_str_ok_at hL σ h hu ha hn

theorem vc_str_atAl {t : Nat} {v u : Val} (σ : State isa) (h : Read P tid t v σ)
    (hu : v.toNat = t → u.toNat = t + 1) (ha : a = P.C.addr) (hn : 4 = P.C.bytes) :
    ∀ b (σ' : State isa), (EAl isa P hL tid).step (.store .plain false a 4 u) σ b σ' → Stored P tid t σ' :=
  vc_str_at hL σ h hu ha hn

theorem vc_stlr_ok_atAl {t : Nat} {u4 : Val} (σ : State isa) (h : Stored P tid t σ) (hu4 : lo u4 = t + 1)
    (ha : a = P.O.addr) (hn : 4 = P.O.bytes) : (EAl isa P hL tid).ok (.store .rel false a 4 u4) σ :=
  vc_stlr_ok_at hL σ h hu4 ha hn

theorem vc_stlr_atAl {t : Nat} {u4 : Val} (σ : State isa) (h : Stored P tid t σ) (hu4 : lo u4 = t + 1)
    (ha : a = P.O.addr) (hn : 4 = P.O.bytes) :
    ∀ b (σ' : State isa), (EAl isa P hL tid).step (.store .rel false a 4 u4) σ b σ' → QEnd P tid σ' :=
  vc_stlr_at hL σ h hu4 ha hn

end At

/-! ## The worker -/

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorkerAl)]

local instance tkWorkerAl.envG : CodeEnv := ⟨layout tkWorkerAl⟩

/-- The worker's table. -/
abbrev tkTableAl (P : Sys) (hL : Locs P) (tid : Nat) (x o c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (EAl isa P hL tid)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = x ∧ s.regs.X1.toBitVec = o ∧ s.regs.X2.toBitVec = c ∧
    Mem.loadInt s.dmem x 4 = none ∧ Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none ∧
    ((lb = "worker" ∧ Start P tid σ.1) ∨ (lb = "spin" ∧ Spin P tid (s.regs.X3.toBitVec.setWidth 32).toNat σ.1) ∨
      (lb = "done" ∧ QEnd P tid σ.1))

/-- **The `ldaddal` ticket lock worker on `EnvGTDR`** (counted, partial): from `Start`,
every run that reaches the end is in `QEnd`. -/
theorem tkWorkerAl_envGTDR (N : Nat) (x o c : BitVec 64) (hL : Locs ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (EAl isa ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩ hL tid))
      (fun s σ => s.regs.X0.toBitVec = x ∧ s.regs.X1.toBitVec = o ∧ s.regs.X2.toBitVec = c ∧
        Mem.loadInt s.dmem x 4 = none ∧ Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none ∧
        Start ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩ tid σ.1)
      tkWorkerAl (fun _ σ => QEnd ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩ tid σ.1) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (tkTableAl ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩ hL tid x o c)
    (hP := by funext s g; simp [tkTableAl])
  tk_worker_vcgen [tkWorkerAl] [fenceMono_le_envGTDR] vc_ldaddal_ok_at vc_ldaddal_at vc_str_ok_atAl vc_str_atAl
    vc_stlr_ok_atAl vc_stlr_atAl

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.tkWorkerAl_envGTDR
