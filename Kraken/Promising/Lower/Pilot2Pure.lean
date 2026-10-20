/-
**Part 5: `pilot2` is pure** (the `RelPureSpec` side
of `final_of_relPureSafelyF`).

`Lower/PilotPure.lean` with the frame: in
`SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)` the tables carry the
heap-off fact `HeapOff (HP P)` (so the fixed shared accesses stay shared and
never overwrite a private byte) and, in `main`, `FrameOK` (the epilogue reads
the slot back). `pop`'s `ldr x4, [x2, #8]` and `main`'s payload load go through
a pointer with no value information here: either outcome of the combined
load (private or shared) is accepted. The `casal`s are releases.
-/
import Kraken.Promising.Lower.Pilot2Main
import Kraken.Promising.Lower.PilotPure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.Pilot2

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Pilot (RP CalleeSaved pushFrag popFrag mainMid)

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot2)]

local instance pilot2.envP : CodeEnv := ⟨layout pilot2⟩

/-- `push`'s purity table. -/
abbrev pushPTable2 (rel : Loc → Pred) (P : Params) (w : Nat) (ra : Int64) (t0 : MachineData) :
    Label → MachineData → (RP rel).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ HeapOff (HP P) s.dmem ∧ s.lr = ra ∧
    Saved2 t0 s ∧ lb = "push"

/-- **`push` is pure** (its link store at `[n + 8]`). -/
theorem push_pure2 (rel : Loc → Pred) (P : Params) (w : Nat) (hw : w < 2)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨P.n w + 8, 8⟩) v) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "push")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ HeapOff (HP P) s.dmem)
      (fun _ s _ s' _ => Saved2 s s') := by
  have hn' : ∀ v : Val, Pred.Pure (rel ⟨P.n w + 8#64, 8⟩) v := hn
  have hw' := pn_cases (P := P) hw
  rintro ra t0 g ⟨hlr, hx0, hx1, hH⟩
  refine cfgEnv_partial_fun (p := pushFrag) (pushPTable2 rel P w ra t0)
    (E := fun a s (_ : (RP rel).State) => a = ra ∧ Saved2 t0 s) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot2_placed (by decide)) t0 g
    ⟨hx0, hx1, hH, hlr, Saved2.refl t0, rfl⟩
  cfg_cases_env [pushFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd, hlr, hfr, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals have ht8 := hd.loadInt_none (hp_top P) (n := 8) (by decide)
  all_goals have hn8 := hd.loadInt_none (hp_link hw') (n := 8) (by decide)
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, ht8, SharedEnv.relPureQ, Arch.storeKind, hn',
    show Arch.armv8.plainStore = .plain from rfl]; done)
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, ht8]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hx1, SharedEnv.relPureQ]
    exact fun h => (h (by decide)).elim
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, hst2⟩ := hst
    have h12 : σ1.2 ≤ σ2.2 := by omega
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simpa using hd,
      by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, -⟩ := hst
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr⟩
  all_goals done

/-- `pop`'s purity table. -/
abbrev popPTable2 (rel : Loc → Pred) (P : Params) (ra : Int64) (t0 : MachineData) :
    Label → MachineData → (RP rel).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = P.t ∧ HeapOff (HP P) s.dmem ∧ s.lr = ra ∧ Saved2 t0 s ∧
    (lb = "pop" ∨ lb = "pop_done")

/-- **`pop` is pure** (no plain store; the link load through `x2` may be
private or shared). -/
theorem pop_pure2 (rel : Loc → Pred) (P : Params) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "pop")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.t ∧ HeapOff (HP P) s.dmem)
      (fun _ s _ s' _ => Saved2 s s') := by
  rintro ra t0 g ⟨hlr, hx0, hH⟩
  refine cfgEnv_partial_fun (p := popFrag) (popPTable2 rel P ra t0)
    (E := fun a s (_ : (RP rel).State) => a = ra ∧ Saved2 t0 s) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot2_placed (by decide)) t0 g
    ⟨hx0, hH, hlr, Saved2.refl t0, .inl rfl⟩
  cfg_cases_env [popFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd, hlr, hfr, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals have ht8 := hd.loadInt_none (hp_top P) (n := 8) (by decide)
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, ht8, SharedEnv.relPureQ]; done)
  case vc4 =>
    exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd,
      by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, .inr rfl⟩, .inl (by decide)⟩)
  case vc9 =>
    simp [hx0, SharedEnv.relPureQ]
    exact fun h => (h (by decide)).elim
  case vc10 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp at hld2
    have h12 : σ1.2 ≤ σ2.2 := by
      rcases hld2 with ⟨_, _, _, rfl⟩ | ⟨_, h, _⟩ <;> omega
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd,
      by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, .inl rfl⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc11 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    exact ⟨by simp [hx0], by simpa using hd, by simpa [MachineData.lr] using hlr,
      by simpa [Saved2, CalleeSaved] using hfr, .inr trivial⟩
  case vc1 =>
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr⟩
  all_goals done

/-! ## `main` -/

/-- The tail's purity table: the frame. -/
abbrev tailPTable2 (rel : Loc → Pred) (P : Params) (lo : BitVec 64) (n : Nat) :
    Label → MachineData → (RP rel).State → Prop :=
  fun lb s _ => FrameOK P lo n s ∧ (lb = "ret_pop" ∨ lb = "empty")

theorem main_tail_pure2 (rel : Loc → Pred) (P : Params) (lo : BitVec 64) (n : Nat) : ∀ s (σ : (RP rel).State),
    FrameOK P lo n s → Safely (cenv.instrStepEnv (RP rel)) (fun x => x.1.2 = mainEnd2)
      ((s, (_root_.Executable.labels cenv).label "ret_pop"), σ) := by
  rintro s σ hF
  refine cfgEnv_partial_fun (p := tailFrag2) (tailPTable2 rel P lo n) (E := fun a _ _ => a = mainEnd2) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot2_placed (by decide)) s σ ⟨hF, .inl rfl⟩
  cfg_cases_env [tailFrag2]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hF, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [SharedEnv.relPureQ]; done)
  case vc1 =>
    exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa [FrameOK, Slot] using hF, .inr rfl⟩, .inl (by decide)⟩)
  case vc4 =>
    simpa [FrameOK, Slot] using hF
  case vc1 =>
    simpa using hF.2.1
  case vc3 =>
    rename_i s σ0 rng v σ1 hld _
    obtain ⟨-, -, ⟨u, hu, hv⟩⟩ := hF
    simp [hu] at hld
    obtain ⟨rfl, rfl⟩ := hld
    exact .inr (by simpa using hv)
  all_goals done

/-- The start of `main` for purity: `MainPre2` without the payload and `Pu0`. -/
def MainPreR2 (P : Params) (w : Nat) (lo : BitVec 64) (n : Nat) (s : MachineData) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = mainEnd2 ∧ s.regs.X21.toBitVec = P.t ∧ s.regs.X27.toBitVec = P.n w ∧
    s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ StackOK P lo n s.dmem ∧ s.regs.SP.toBitVec % 16#64 = 0 ∧
    (s.regs.SP.toBitVec - 16#64 - lo).toNat + 8 ≤ n

set_option linter.unusedSectionVars false in
theorem main_prefix_pure2 (rel : Loc → Pred) (P : Params) (w : Nat) (hw : w < 2) (lo : BitVec 64) (n : Nat)
    (hd : ∀ v : Val, Pred.Pure (rel ⟨P.n w, 4⟩) v) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => MainPreR2 P w lo n s ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainPre2⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ s.regs.X21.toBitVec = P.t ∧
        FrameOK P lo n s); fun _ _ _ => False ⦄ := by
  have hw' := pn_cases (P := P) hw
  intro s₀ g₀
  unfold mainPre2
  vcgen
  all_goals obtain ⟨⟨h30, h21, h27, hlim, ⟨hH, hS⟩, hal, hr⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hal]; done)
  all_goals simp at *
  all_goals have hsl := slot_isSome (‹MainPreR2 _ _ _ _ _›.2.2.2.2.1.2) ‹MainPreR2 _ _ _ _ _›.2.2.2.2.2.2
  case vc2 =>
    exact absurd ‹Mem.loadInt _ _ 8 = none› (Option.ne_none_iff_isSome.mpr hsl)
  case vc3 =>
    rename_i hhi _ _
    simp only [← UInt64.toNat_toBitVec] at hhi
    bv_omega
  case vc5 =>
    rw [h27]; exact hd _
  case vc6 =>
    rename_i s σ0 rng dm σ1 rng2 dm2 σ2 hhi hst1 hst2 _
    obtain ⟨-, rfl, rfl⟩ := hst1.resolve_right fun ⟨hn, _⟩ => absurd hn (Option.ne_none_iff_isSome.mpr hsl)
    have hH' := hH.storeInt hsl
    have hx27 := hp_data (Eq.subst (motive := fun x => x = P.n 0 ∨ x = P.n 1) h27.symm hw')
    have hd4 := fun v => (hH' v).loadInt_none hx27 (n := 4) (by decide)
    simp [hd4] at hst2
    obtain ⟨rfl, -⟩ := hst2
    refine ⟨h21, h27, h21, ⟨hH' _, hS.storeInt _ _ _⟩, ?_, ?_⟩
    · simp [Reg64s.setXReg]
      exact aligned_sub16 _ hal
    · refine ⟨Int.ofBytes (Int.toBytes 8 s.regs.X30.toBitVec.toInt), ?_, ?_⟩
      · simp [Reg64s.setXReg]
        exact Mem.loadInt_storeInt _ _ _ _ (by decide)
      · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
        simpa using h30

set_option linter.unusedSectionVars false in
theorem main_mid_pure2 (rel : Loc → Pred) (P : Params) (lo : BitVec 64) (n : Nat) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (s.regs.X21.toBitVec = P.t ∧ FrameOK P lo n s) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainMid⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = P.t ∧ FrameOK P lo n s); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainMid
  vcgen
  all_goals obtain ⟨⟨h21, hF⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  exact ⟨by simpa using h21, by simpa [FrameOK, Slot] using hF⟩

/-- **`main` is pure**: a `PartialTripleEnv` of the whole text in `relPure`,
through `push_pure2` and `pop_pure2`. -/
theorem main_pure2 (rel : Loc → Pred) (P : Params) (w : Nat) (hw : w < 2) (lo : BitVec 64) (n : Nat)
    (hd : ∀ v : Val, Pred.Pure (rel ⟨P.n w, 4⟩) v) (hn : ∀ v : Val, Pred.Pure (rel ⟨P.n w + 8, 8⟩) v) :
    PartialTripleEnv (RP rel) (fun s _ => MainPreR2 P w lo n s) pilot2 (fun _ _ => True) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  have hb : Program.blockAt pilot2 "main" = some ⟨"main", mainBody2, some "ret_pop"⟩ := by decide
  have hbody : PartialWpEnv (RP rel) mainBody2 (fun s _ => FrameOK P lo n s) (fun _ _ _ => False) s σ := by
    have h1 := (main_prefix_pure2 rel P w hw lo n hd s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h1)
    rintro s1 σ1 ⟨h0, h1, h21, hF⟩
    refine PartialWpEnv.call (push_pure2 rel P w hw hn) fun ra => ⟨?_, ?_⟩
    · exact ⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr, Reg64s.setXReg] using h0,
        by simpa [MachineData.setLr, Reg64s.setXReg] using h1, (hF.setLr ra).1.1⟩
    rintro s2 σ2 hsv
    have hF2 := (hF.setLr ra).saved hsv
    have h21' : s2.regs.X21.toBitVec = P.t := by
      obtain ⟨⟨-, -, f21, -⟩, -⟩ := hsv
      simpa [f21, MachineData.setLr, Reg64s.setXReg] using h21
    have h2 := (main_mid_pure2 rel P lo n s2 σ2).le_wp s2 σ2 ⟨⟨h21', hF2⟩, rfl, rfl⟩
    rw [wpEnv_eq] at h2
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h2)
    rintro s3 σ3 ⟨h0', hF3⟩
    refine PartialWpEnv.call (pop_pure2 rel P) fun ra => ⟨?_, ?_⟩
    · exact ⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr, Reg64s.setXReg] using h0',
        (hF3.setLr ra).1.1⟩
    rintro s4 σ4 hsv'
    exact PartialWpEnv.nil ((hF3.setLr ra).saved hsv')
  rw [← pilot2_placed.entry pc hpc]
  refine Safely.bind (hbody _ (pilot2_placed.block _ _ hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, hF⟩ | hF)
  · dsimp only at ha hF
    rw [pilot2_placed.next _ _ _ hb rfl] at ha
    subst ha
    refine (main_tail_pure2 rel P lo n s' g' hF).mono fun x hx => .inl ⟨?_, trivial⟩
    obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := pilot2) pilot2 [] 0 (by simp)
    rw [hx, pilot2_placed.entry _ hs0, Nat.zero_add] at *
    exact haf.symm
  · exact hF.elim

end Kraken.Promising.Lower.Pilot2
