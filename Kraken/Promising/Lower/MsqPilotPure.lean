/-
**The lowered texts are pure** (the
`RelPureSpec` side of `final_of_relPureSafelyF`).

The first lowering pilot's modular mirror (`Lower/PilotPure.lean`) in
`RP rel = counted (relPure Arch.armv8 rel)`: `enq_pure`/`deq_pure` (partial
function specifications with the callee-saved frame only: their writes are
release `casal`s, unconstrained by `relPure`), and `mainE_pure`/`mainD_pure`
(`PartialTripleEnv`s of the whole texts, postcondition `True`), for release
predicates pure at the data words `[n1]`, `[n2]` (`main_e`'s only plain
stores).
-/
import Kraken.Promising.Lower.MsqPilotMain
import Kraken.Promising.Lower.PilotPure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.MsqPilot

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The frame part of a purity table: no `dmem` word, the link, the
callee-saved registers. -/
abbrev PFrame (ra : Int64) (t0 s : MachineData) : Prop :=
  (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.lr = ra ∧ CalleeSaved t0 s

set_option hygiene false in
/-- The purity VCs of a function: `casal`s unconstrained, jumps into the
table (forward, down the rank, or after a step), `ret` into the frame. -/
local macro "pure_vcs" : tactic => `(tactic| (
  all_goals try (simp [hd8, SharedEnv.relPureQ]; done)
  all_goals try (simp [SharedEnv.relPureQ]; exact fun h => (h (by decide)).elim)
  all_goals try (exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩)
  all_goals try (exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4,
    by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩, by simp (config := { decide := true })⟩,
    by first | exact .inl (by decide) | exact .inr (.inl ⟨by decide, by decide⟩)⟩))
  all_goals try (exact ⟨⟨by simpa using hd8, by simpa using hd4, by simpa [MachineData.lr] using hlr,
    by simpa [CalleeSaved] using hfr⟩, by simp (config := { decide := true })⟩)
  all_goals (
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩,
      by simp (config := { decide := true })⟩, ?_⟩)
    first
    | exact .inr fun ⟨_, hg⟩ => by subst hg; simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *; omega
    | exact .inr (.inr fun ⟨_, hg⟩ => by
        subst hg; simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *; omega))))

section E

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progE)]

local instance progE.envP : CodeEnv := ⟨layout progE⟩

/-- **`enq` is pure** (no plain store). -/
theorem enq_pure (rel : Loc → Pred) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "enq")
      (fun ra s _ => s.lr = ra ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') := by
  rintro ra t0 g ⟨hlr, ⟨hd8, hd4⟩⟩
  refine cfgEnv_partial_fun (p := enqFrag)
    (fun lb s (_ : (RP rel).State) => PFrame ra t0 s ∧ (lb = "enq" ∨ lb = "enq_loop" ∨ lb = "enq_fix"))
    (E := fun a s (_ : (RP rel).State) => a = ra ∧ CalleeSaved t0 s) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE progE_placed (by decide)) t0 g
    ⟨⟨hd8, hd4, hlr, by simp [CalleeSaved]⟩, .inl rfl⟩
  cfg_cases_env [enqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hd8, hd4, hlr, hfr⟩, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  pure_vcs

omit [Executable.ValidLayout (layout progE)] in
theorem mainE_pre_pure (rel : Loc → Pred) (n1 n2 : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec s.regs.X30.toBitVec = endE ∧
        s.regs.X22.toBitVec = n1 ∧ s.regs.X23.toBitVec = n2 ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨ePre⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => Int64.ofBitVec s.regs.X19.toBitVec = endE ∧ s.regs.X23.toBitVec = n2 ∧ NoDmem s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold ePre
  vcgen
  all_goals obtain ⟨⟨h30, h22, h23, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp [NoDmem] at *
  case vc2 => rw [h22]; exact hd _
  case vc3 =>
    rename_i s σ0 rng dm σ1 hst _
    simp [hd4] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [h30, h23, hd8, hd4]

omit [Executable.ValidLayout (layout progE)] in
theorem mainE_mid_pure (rel : Loc → Pred) (n2 : BitVec 64) (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n2, 4⟩) v) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec s.regs.X19.toBitVec = endE ∧
        s.regs.X23.toBitVec = n2 ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨eMid⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => Int64.ofBitVec s.regs.X19.toBitVec = endE ∧ s.regs.X23.toBitVec = n2 ∧ NoDmem s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold eMid
  vcgen
  all_goals obtain ⟨⟨h19, h23, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp [NoDmem] at *
  case vc2 => rw [h23]; exact hd2 _
  case vc3 =>
    rename_i s σ0 rng dm σ1 hst _
    simp [hd4] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [h19, h23, hd8, hd4]

omit [Executable.ValidLayout (layout progE)] in
theorem mainE_tail_pure (rel : Loc → Pred) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => Int64.ofBitVec s.regs.X19.toBitVec = endE ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨eTail⟩ : EnvProgram (RP rel)) ⦃ (fun _ _ _ => False); fun a _ _ => a = endE ⦄ := by
  intro s₀ g₀
  unfold eTail
  vcgen
  all_goals obtain ⟨h19, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  simpa using h19

/-- **`main_e` is pure**: a `PartialTripleEnv` of the whole text in
`relPure`, through `enq_pure`. -/
theorem mainE_pure (rel : Loc → Pred) (n1 n2 : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n2, 4⟩) v) :
    PartialTripleEnv (RP rel) (fun s _ => Int64.ofBitVec s.regs.X30.toBitVec = endE ∧ s.regs.X22.toBitVec = n1 ∧
      s.regs.X23.toBitVec = n2 ∧ NoDmem s) progE (fun _ _ => True) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  have hb : Program.blockAt progE "main_e" = some ⟨"main_e", mainEBody, some "enq"⟩ := by decide
  have call : ∀ s σ (rest : Program) (Q : MachineData → (RP rel).State → Prop) E,
      Int64.ofBitVec s.regs.X19.toBitVec = endE ∧ s.regs.X23.toBitVec = n2 ∧ NoDmem s →
      (∀ s' σ', Int64.ofBitVec s'.regs.X19.toBitVec = endE ∧ s'.regs.X23.toBitVec = n2 ∧ NoDmem s' →
        PartialWpEnv (RP rel) rest Q E s' σ') → PartialWpEnv (RP rel) (blTo "enq" :: rest) Q E s σ := by
    rintro s σ rest Q E ⟨h19, h23, ⟨hd8, hd4⟩⟩ hk
    refine PartialWpEnv.call (enq_pure rel) fun ra => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
      ⟨by simpa [MachineData.setLr] using hd8, by simpa [MachineData.setLr] using hd4⟩⟩, ?_⟩
    rintro s' σ' ⟨f19, -, -, -, f23, -, -, -, -, -, fdm⟩
    exact hk s' σ' ⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19,
      by simpa [f23, MachineData.setLr, Reg64s.setXReg] using h23,
      ⟨by simpa [fdm, MachineData.setLr] using hd8, by simpa [fdm, MachineData.setLr] using hd4⟩⟩
  have hbody : PartialWpEnv (RP rel) mainEBody (fun _ _ => False) (fun a _ _ => a = endE) s σ := by
    have h1 := (mainE_pre_pure rel n1 n2 hd s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
    refine fun s1 σ1 hA1 => call s1 σ1 _ _ _ hA1 fun s2 σ2 hB1 => ?_
    have h2 := (mainE_mid_pure rel n2 hd2 s2 σ2).le_wp s2 σ2 ⟨hB1, rfl, rfl⟩
    rw [wpEnv_eq] at h2
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h2)
    refine fun s3 σ3 hA2 => call s3 σ3 _ _ _ hA2 fun s4 σ4 hB2 => ?_
    have h3 := (mainE_tail_pure rel s4 σ4).le_wp s4 σ4 ⟨hB2.1, rfl, rfl⟩
    rw [wpEnv_eq] at h3
    exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun _ _ _ h => h) h3)
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := progE) progE [] 0 (by simp)
  rw [← progE_placed.entry pc hpc]
  refine (hbody _ (progE_placed.block _ _ hb)).mono fun x hx => .inl ⟨?_, trivial⟩
  rw [hx.resolve_left fun h => h.2, progE_placed.entry _ hs0, Nat.zero_add] at *
  exact haf.symm

end E

section D

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progD)]

local instance progD.envP : CodeEnv := ⟨layout progD⟩

/-- **`deq` is pure** (no plain store). -/
theorem deq_pure (rel : Loc → Pred) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "deq")
      (fun ra s _ => s.lr = ra ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') := by
  rintro ra t0 g ⟨hlr, ⟨hd8, hd4⟩⟩
  refine cfgEnv_partial_fun_rank (p := deqFrag)
    (fun lb s (_ : (RP rel).State) => PFrame ra t0 s ∧ (lb = "deq" ∨ lb = "deq_ne")) deqRank
    (E := fun a s (_ : (RP rel).State) => a = ra ∧ CalleeSaved t0 s) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE progD_placed (by decide)) t0 g
    ⟨⟨hd8, hd4, hlr, by simp [CalleeSaved]⟩, .inl rfl⟩
  cfg_cases_env_rank [deqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hd8, hd4, hlr, hfr⟩, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  pure_vcs

omit [Executable.ValidLayout (layout progD)] in
/-- `main_d`'s straight-line pieces keep the saved link and `dmem` (no
shared access); the first also saves the link. -/
theorem mainD_piece_pure (rel : Loc → Pred) (p : Program) (hp : p = dPre ∨ p = dMid) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec (if p = dPre then s.regs.X30 else s.regs.X19).toBitVec
        = endD ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨p⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => Int64.ofBitVec s.regs.X19.toBitVec = endD ∧ NoDmem s); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  rcases hp with rfl | rfl <;> simp only [show dMid ≠ dPre by decide, ↓reduceIte]
  · unfold dPre; vcgen
    all_goals obtain ⟨⟨h30, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
    simp [NoDmem, h30, hd8, hd4]
  · unfold dMid; vcgen
    all_goals obtain ⟨⟨h19, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
    simp [NoDmem, h19, hd8, hd4]

omit [Executable.ValidLayout (layout progD)] in
theorem mainD_tail_pure (rel : Loc → Pred) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => Int64.ofBitVec s.regs.X19.toBitVec = endD ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨dTail⟩ : EnvProgram (RP rel)) ⦃ (fun _ _ _ => False); fun a _ _ => a = endD ⦄ := by
  intro s₀ g₀
  unfold dTail
  vcgen
  all_goals obtain ⟨h19, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  simpa using h19

/-- **`main_d` is pure**, through `deq_pure`. -/
theorem mainD_pure (rel : Loc → Pred) :
    PartialTripleEnv (RP rel) (fun s _ => Int64.ofBitVec s.regs.X30.toBitVec = endD ∧ NoDmem s) progD
      (fun _ _ => True) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  have hb : Program.blockAt progD "main_d" = some ⟨"main_d", mainDBody, some "deq"⟩ := by decide
  have call : ∀ s σ (rest : Program) (Q : MachineData → (RP rel).State → Prop) E,
      Int64.ofBitVec s.regs.X19.toBitVec = endD ∧ NoDmem s →
      (∀ s' σ', Int64.ofBitVec s'.regs.X19.toBitVec = endD ∧ NoDmem s' → PartialWpEnv (RP rel) rest Q E s' σ') →
      PartialWpEnv (RP rel) (blTo "deq" :: rest) Q E s σ := by
    rintro s σ rest Q E ⟨h19, ⟨hd8, hd4⟩⟩ hk
    refine PartialWpEnv.call (deq_pure rel) fun ra => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
      ⟨by simpa [MachineData.setLr] using hd8, by simpa [MachineData.setLr] using hd4⟩⟩, ?_⟩
    rintro s' σ' ⟨f19, -, -, -, -, -, -, -, -, -, fdm⟩
    exact hk s' σ' ⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19,
      ⟨by simpa [fdm, MachineData.setLr] using hd8, by simpa [fdm, MachineData.setLr] using hd4⟩⟩
  have hbody : PartialWpEnv (RP rel) mainDBody (fun _ _ => False) (fun a _ _ => a = endD) s σ := by
    have h1 := (mainD_piece_pure rel dPre (.inl rfl) s σ).le_wp s σ ⟨by simpa using hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
    refine fun s1 σ1 hA1 => call s1 σ1 _ _ _ hA1 fun s2 σ2 hB1 => ?_
    have h2 := (mainD_piece_pure rel dMid (.inr rfl) s2 σ2).le_wp s2 σ2
      ⟨by simpa [show dMid ≠ dPre by decide] using hB1, rfl, rfl⟩
    rw [wpEnv_eq] at h2
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h2)
    refine fun s3 σ3 hA2 => call s3 σ3 _ _ _ hA2 fun s4 σ4 hB2 => ?_
    have h3 := (mainD_tail_pure rel s4 σ4).le_wp s4 σ4 ⟨hB2.1, rfl, rfl⟩
    rw [wpEnv_eq] at h3
    exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun _ _ _ h => h) h3)
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := progD) progD [] 0 (by simp)
  rw [← progD_placed.entry pc hpc]
  refine (hbody _ (progD_placed.block _ _ hb)).mono fun x hx => .inl ⟨?_, trivial⟩
  rw [hx.resolve_left fun h => h.2, progD_placed.entry _ hs0, Nat.zero_add] at *
  exact haf.symm

end D

end Kraken.Promising.Lower.MsqPilot
