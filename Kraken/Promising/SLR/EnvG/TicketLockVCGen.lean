/-
**Part 4: the ticket lock worker on `EnvGTD`
by `vcgen`**: the whole worker `tkWorker` as a `PartialTripleEnv` in the
counted `EnvGTD`, by `cfgEnv_partial` with a three-label table (`worker`:
`Start`; `spin`: `Spin` at the ticket `w3`; `done`: `QEnd`) and the VCs of
`EnvG/TicketLockVC.lean`. The `ldadda` uses the generic `ldop_shared_spec`.

The VCs are restated at an address given by an equation (`*_at`, as in
`SwplLockVCGen`): a step hypothesis cannot be rewritten by `simp`.
-/
import Kraken.Promising.SLR.EnvG.TicketLockVC
import Kraken.Promising.SLR.EnvG.TicketLockSmoke
import Kraken.Promising.SLR.EnvG.A64VCGen
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.SLR.EnvG.TicketLock

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The VCs at an address given by an equation -/

section At

variable {P : Sys} (hL : Locs P) {tid : Nat} {a : BitVec 64}

theorem vc_ldadda_ok_at (σ : State isa) (h : Start P tid σ) (ha : a = P.X.addr) (hn : 4 = P.X.bytes)
    {op : Val → Option Val} (hop : ∀ x, op x = some ((x.setWidth 32 + 1#32).setWidth 128)) :
    (E isa P hL tid).ok (.rmw .acq a 4 op) σ := by
  subst ha; rw [hn]; exact (vc_ldadda hL σ h hop).1

theorem vc_ldadda_at (σ : State isa) (h : Start P tid σ) (ha : a = P.X.addr) (hn : 4 = P.X.bytes)
    {op : Val → Option Val} (hop : ∀ x, op x = some ((x.setWidth 32 + 1#32).setWidth 128)) :
    ∀ old (σ' : State isa), (E isa P hL tid).step (.rmw .acq a 4 op) σ old σ' → Spin P tid old.toNat σ' := by
  subst ha; rw [hn]; exact (vc_ldadda hL σ h hop).2

theorem vc_ldar_at {t : Nat} (σ : State isa) (h : Spin P tid t σ) (ha : a = P.O.addr) (hn : 4 = P.O.bytes) :
    ∀ v (σ' : State isa), (E isa P hL tid).step (.load .acq false a 4) σ v σ' →
      (lo v ≠ t → Spin P tid t σ') ∧ (lo v = t → Got P tid t σ') := by
  subst ha; rw [hn]; exact vc_ldar hL σ h

theorem vc_ldr_at {t : Nat} (σ : State isa) (h : Got P tid t σ) (ha : a = P.C.addr) (hn : 4 = P.C.bytes) :
    ∀ v (σ' : State isa), (E isa P hL tid).step (.load .plain false a 4) σ v σ' → Read P tid t v σ' := by
  subst ha; rw [hn]; exact vc_ldr hL σ h

theorem vc_str_ok_at {t : Nat} {v u : Val} (σ : State isa) (h : Read P tid t v σ)
    (hu : v.toNat = t → u.toNat = t + 1) (ha : a = P.C.addr) (hn : 4 = P.C.bytes) :
    (E isa P hL tid).ok (.store .plain false a 4 u) σ := by
  subst ha; rw [hn]; exact (vc_str hL σ h hu).1

theorem vc_str_at {t : Nat} {v u : Val} (σ : State isa) (h : Read P tid t v σ)
    (hu : v.toNat = t → u.toNat = t + 1) (ha : a = P.C.addr) (hn : 4 = P.C.bytes) :
    ∀ b (σ' : State isa), (E isa P hL tid).step (.store .plain false a 4 u) σ b σ' → Stored P tid t σ' := by
  subst ha; rw [hn]; exact (vc_str hL σ h hu).2

theorem vc_stlr_ok_at {t : Nat} {u4 : Val} (σ : State isa) (h : Stored P tid t σ) (hu4 : lo u4 = t + 1)
    (ha : a = P.O.addr) (hn : 4 = P.O.bytes) : (E isa P hL tid).ok (.store .rel false a 4 u4) σ := by
  subst ha; rw [hn]; exact (vc_stlr hL σ h hu4).1

theorem vc_stlr_at {t : Nat} {u4 : Val} (σ : State isa) (h : Stored P tid t σ) (hu4 : lo u4 = t + 1)
    (ha : a = P.O.addr) (hn : 4 = P.O.bytes) :
    ∀ b (σ' : State isa), (E isa P hL tid).step (.store .rel false a 4 u4) σ b σ' → QEnd P tid σ' := by
  subst ha; rw [hn]; exact (vc_stlr hL σ h hu4).2

theorem hu_inc {N t : Nat} (hN : N + 1 < 2 ^ 32) (ht : t < N + 1) (w : Val) :
    w.toNat = t → ((w.setWidth 32 + 1#32).setWidth 128 : Val).toNat = t + 1 := by
  intro hw
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [hw]
  rw [Nat.mod_eq_of_lt (a := t) (by omega), Nat.mod_eq_of_lt (a := 1) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem lo_inc {N : Nat} (hN : N + 1 < 2 ^ 32) (y : BitVec 32) (ht : y.toNat < N + 1) :
    lo ((y + 1#32).setWidth 128) = y.toNat + 1 := by
  unfold lo
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 1) (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

end At

/-! ## The worker -/

set_option hygiene false in
/-- **The ticket lock worker's `vcgen` script** (shared by
`tkWorker_envGTD` and `tkWorkerAl_envGTDR`), after `cfgEnv_partial` with the
three-label table: the worker `wk`, the environment's `FenceMono` lemma `fm`,
the ticket RMW's VCs `vok`/`vat` and the store VCs `sok`/`sat` (counter) and
`lok`/`lat` (`owner` release) at the environment. Unhygienic: it uses the
theorem's `N`, `x`, `o`, `c`, `hL` and `tid`. -/
scoped macro "tk_worker_vcgen " "[" wk:Lean.Parser.Tactic.simpLemma "]" "[" fm:Lean.Parser.Tactic.simpLemma "]"
    vok:ident vat:ident sok:ident sat:ident lok:ident lat:ident : tactic => `(tactic| (
  cfg_cases_env [$wk]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hx2, hdx, hdo, hdc, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, $fm, SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hx2, hdx, hdo, hdc]; done)
  · -- the ticket RMW is permitted
    rename_i hf _
    exact $vok hL _ (hT.fence hf.1) (by simp [hx0]) rfl (fun x => by simp [rmwOpBits, AtomicOp.apply])
  · -- after the ticket RMW: `spin` at the ticket
    rename_i s σ0 σ1 old σ2 hf hst _
    have hS := $vat hL _ (hT.fence hf.1) (by simp [hx0]) rfl
      (fun x => by simp [rmwOpBits, AtomicOp.apply]) old σ2.1 hst.1
    have hlt : old.toNat < 2 ^ 32 := by have := hS.2.1; have := hL.n32; omega
    simp [hx0, hx1, hx2, hdx, hdo, hdc]
    rw [Nat.mod_eq_of_lt hlt]; exact hS
  · -- the `ldar` is permitted
    simp [hx1]
    exact fun h => hL.xo h.symm
  · rename_i m σ0 v σ1 σ2 hc σ3 hst hf1 hf2 _
    have hne : lo v ≠ (BitVec.setWidth 32 m.regs.X3.toBitVec).toNat := by
      simp at hc
      intro h; apply hc
      rw [BitVec.eq_of_toNat_eq h, BitVec.sub_self]
    have h := (vc_ldar_at hL _ hT (by simp [hx1]) rfl v σ1.1 hst.1).1 hne
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hx2], hdx, hdo, hdc,
      .inr (.inl ⟨rfl, ?_⟩)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simpa using (h.fence hf1.1).fence hf2.1
    · subst hg
      have := hst.2; have := hf1.2; have := hf2.2
      simp only [SharedEnv.tick_load] at *; omega
  · -- the `ldr` is permitted
    simp [hx2]
    exact fun h => hL.xc h.symm
  · -- the `str` is permitted
    rename_i m σ0 v σ1 σ2 hc σ3 rng1 r2 σ4 rng2 σ5 rng3 hdm hst hf1 hf2 hld hf3 _
    have heq : lo v = (BitVec.setWidth 32 m.regs.X3.toBitVec).toNat := by
      simp at hc
      unfold lo; congr 1; bv_omega
    have hG := (((vc_ldar_at hL _ hT (by simp [hx1]) rfl v σ1.1 hst.1).2 heq).fence hf1.1).fence hf2.1
    simp [hx2, hdc] at hld
    obtain ⟨w, hl, rfl⟩ := hld
    have hR := (vc_ldr_at hL _ hG rfl rfl w σ4.1 hl.1).fence hf3.1
    have hs := $sok hL _ hR (hu_inc hL.n32 hG.2.1 w) rfl rfl
    simpa [hx2] using hs
  · -- the private memory is untouched by the shared store
    rename_i m σ0 v σ1 σ2 hc σ3 rng1 r2 σ4 rng2 σ5 rng3 dm σ6 rng4 σ7 hstl hf1 hf2 hld hf3 hst hf4 _
    simp [hx2, hdc] at hld
    obtain ⟨w, -, rfl⟩ := hld
    simp [hx2, hdc] at hst
    simp [hst.1, hx1, hdo]
  · -- the `stlr` is permitted
    rename_i m σ0 v σ1 σ2 hc σ3 rng1 r2 σ4 rng2 σ5 rng3 dm σ6 rng4 σ7 hstl hf1 hf2 hld hf3 hst hf4 _
    have heq : lo v = (BitVec.setWidth 32 m.regs.X3.toBitVec).toNat := by
      simp at hc
      unfold lo; congr 1; bv_omega
    have hG := (((vc_ldar_at hL _ hT (by simp [hx1]) rfl v σ1.1 hstl.1).2 heq).fence hf1.1).fence hf2.1
    simp [hx2, hdc] at hld
    obtain ⟨w, hl, rfl⟩ := hld
    have hR := (vc_ldr_at hL _ hG rfl rfl w σ4.1 hl.1).fence hf3.1
    simp [hx2, hdc] at hst
    have hS : Stored ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩ tid (BitVec.setWidth 32 m.regs.X3.toBitVec).toNat σ6.1 := by
      rcases hst.2.1 with h | h <;>
        exact $sat hL _ hR (hu_inc hL.n32 hG.2.1 w) rfl rfl _ _ (by simpa [hx2] using h)
    have hs := $lok hL _ (hS.fence hf4.1) (lo_inc hL.n32 _ hG.2.1) rfl rfl
    simpa [hx1] using hs
  · -- after the release: `done`
    rename_i m σ0 v σ1 σ2 hc σ3 rng1 r2 σ4 rng2 σ5 rng3 dm σ6 rng4 σ7 b σ8 σ9 hstl hf1 hf2 hld hf3 hst hf4 hst2 hf5 _
    have heq : lo v = (BitVec.setWidth 32 m.regs.X3.toBitVec).toNat := by
      simp at hc
      unfold lo; congr 1; bv_omega
    have hG := (((vc_ldar_at hL _ hT (by simp [hx1]) rfl v σ1.1 hstl.1).2 heq).fence hf1.1).fence hf2.1
    simp [hx2, hdc] at hld
    obtain ⟨w, hl, rfl⟩ := hld
    have hR := (vc_ldr_at hL _ hG rfl rfl w σ4.1 hl.1).fence hf3.1
    simp [hx2, hdc] at hst
    have hS : Stored ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩ tid (BitVec.setWidth 32 m.regs.X3.toBitVec).toNat σ6.1 := by
      rcases hst.2.1 with h | h <;>
        exact $sat hL _ hR (hu_inc hL.n32 hG.2.1 w) rfl rfl _ _ (by simpa [hx2] using h)
    simp [hx1] at hst2
    have hQ := ($lat hL _ (hS.fence hf4.1) (lo_inc hL.n32 _ hG.2.1) rfl rfl b σ8.1 hst2.1).fence hf5.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hx2], by simp [hst.1, hdx],
      by simp [hst.1, hdo], by simp [hst.1, hdc], .inr (.inr ⟨rfl, hQ⟩)⟩, .inl (by decide)⟩
  · exact hT))

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorker)]

local instance tkWorker.envG : CodeEnv := ⟨layout tkWorker⟩

/-- The worker's table. -/
abbrev tkTable (P : Sys) (hL : Locs P) (tid : Nat) (x o c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (E isa P hL tid)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = x ∧ s.regs.X1.toBitVec = o ∧ s.regs.X2.toBitVec = c ∧
    Mem.loadInt s.dmem x 4 = none ∧ Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none ∧
    ((lb = "worker" ∧ Start P tid σ.1) ∨ (lb = "spin" ∧ Spin P tid (s.regs.X3.toBitVec.setWidth 32).toNat σ.1) ∨
      (lb = "done" ∧ QEnd P tid σ.1))

/-- **The ticket lock worker on `EnvGTD`** (counted, partial): from `Start`,
every run that reaches the end is in `QEnd`. -/
theorem tkWorker_envGTD (N : Nat) (x o c : BitVec 64) (hL : Locs ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (E isa ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩ hL tid))
      (fun s σ => s.regs.X0.toBitVec = x ∧ s.regs.X1.toBitVec = o ∧ s.regs.X2.toBitVec = c ∧
        Mem.loadInt s.dmem x 4 = none ∧ Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none ∧
        Start ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩ tid σ.1)
      tkWorker (fun _ σ => QEnd ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩ tid σ.1) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (tkTable ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩ hL tid x o c)
    (hP := by funext s g; simp [tkTable])
  tk_worker_vcgen [tkWorker] [fenceMono_le_envGTD] vc_ldadda_ok_at vc_ldadda_at vc_str_ok_at vc_str_at
    vc_stlr_ok_at vc_stlr_at

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.tkWorker_envGTD
