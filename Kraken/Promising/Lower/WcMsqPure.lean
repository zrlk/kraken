/-
**Shape A's dequeuer text is pure** (the
`RelPureSpec` side of the kit). `MsqPilot`'s
`Lower/MsqPilotPure.lean` for `progD`: `wdeq_pure` (the callee-saved frame
only; `deq`'s only write is its release `casal`) and `mainD_pure`.
-/
import Kraken.Promising.Lower.WcMsqMain
import Kraken.Promising.Lower.MsqPilotPure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.WcMsq

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP)
open Kraken.Promising.Lower.MsqPilot (PFrame dPre blTo)

set_option mvcgen.warning false
set_option experimental.vcgen true

set_option hygiene false in
/-- The purity VCs of `deq` (`MsqPilot`'s `pure_vcs`, without the rank case). -/
local macro "pure_vcs" : tactic => `(tactic| (
  all_goals try (simp [hd8, hd4, SharedEnv.relPureQ]; done)
  all_goals try (simp [SharedEnv.relPureQ]; exact fun h => (h (by decide)).elim)
  all_goals try (exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩)
  all_goals try (exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4,
    by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩, by simp (config := { decide := true })⟩,
    .inl (by decide)⟩))
  all_goals try (exact ⟨⟨by simpa using hd8, by simpa using hd4, by simpa [MachineData.lr] using hlr,
    by simpa [CalleeSaved] using hfr⟩, by simp (config := { decide := true })⟩)
  all_goals (
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩,
      by simp (config := { decide := true })⟩, ?_⟩)
    exact .inr fun ⟨_, hg⟩ => by
      subst hg; simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *
      grind)))

section D

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progD)]

local instance progD.envP : CodeEnv := ⟨layout progD⟩

/-- **WeakCore's `deq` is pure** (no plain store). -/
theorem wdeq_pure (rel : Loc → Pred) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "deq")
      (fun ra s _ => s.lr = ra ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') := by
  rintro ra t0 g ⟨hlr, ⟨hd8, hd4⟩⟩
  refine cfgEnv_partial_fun (p := wcDeqFrag)
    (fun lb s (_ : (RP rel).State) => PFrame ra t0 s ∧ (lb = "deq" ∨ lb = "deq_empty"))
    (E := fun a s (_ : (RP rel).State) => a = ra ∧ CalleeSaved t0 s) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE progD_placed (by decide)) t0 g
    ⟨⟨hd8, hd4, hlr, by simp [CalleeSaved]⟩, .inl rfl⟩
  cfg_cases_env [wcDeqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hd8, hd4, hlr, hfr⟩, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  pure_vcs

omit [Executable.ValidLayout (layout progD)] in
/-- `main_d`'s straight-line pieces keep the saved link and `dmem`; the first
also saves the link. -/
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

/-- **`main_d` is pure**, through `wdeq_pure`. -/
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
    refine PartialWpEnv.call (wdeq_pure rel) fun ra => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
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

end Kraken.Promising.Lower.WcMsq
