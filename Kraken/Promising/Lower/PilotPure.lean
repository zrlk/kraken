/-
**Part 5: `pilot` is pure** (the `RelPureSpec` side
of `final_of_relPureSafelyF`).

The same modular assembly as `Lower/PilotSpecs.lean` and `Lower/PilotMain.lean`
in `SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)`, for release
predicates pure at the node's payload word `[n]` (4 bytes) and link
`[n + 8]` (8 bytes): `push_pure`, `pop_pure` (partial function specifications,
the callee-saved frame only), the tail, the prefix, `main_pure_run` and
`main_pure` (a `PartialTripleEnv` of the whole text with postcondition `True`).
The `casal`s are releases (unconstrained by `relPure`).
-/
import Kraken.Promising.Lower.PilotMain

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Pilot

open Kraken.Promising.SLR.EnvG.Treiber2

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot)]

local instance pilot.envP : CodeEnv := ⟨layout pilot⟩

/-- The purity environment. -/
abbrev RP (rel : Loc → Pred) : SharedEnv := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)

/-- `push`'s purity table. -/
abbrev pushPTable (rel : Loc → Pred) (t n : BitVec 64) (ra : Int64) (t0 : MachineData) :
    Label → MachineData → (RP rel).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.lr = ra ∧ CalleeSaved t0 s ∧ lb = "push"

/-- **`push` is pure** (its link store at `[n + 8]`). -/
theorem push_pure (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "push")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s') := by
  have hn' : ∀ v : Val, Pred.Pure (rel ⟨n + 8#64, 8⟩) v := hn
  rintro ra t0 g ⟨hlr, hx0, hx1, ⟨hd8, hd4⟩⟩
  refine cfgEnv_partial_fun (p := pushFrag) (pushPTable rel t n ra t0)
    (E := fun a s (_ : (RP rel).State) => a = ra ∧ CalleeSaved t0 s) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot_placed (by decide)) t0 g
    ⟨hx0, hx1, hd8, hd4, hlr, by simp [CalleeSaved], rfl⟩
  cfg_cases_env [pushFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hd4, hlr, hfr, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hd8, SharedEnv.relPureQ, Arch.storeKind, hn',
    show Arch.armv8.plainStore = .plain from rfl]; done)
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hd8]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hx1, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, hst2⟩ := hst
    have h12 : σ1.2 ≤ σ2.2 := by omega
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩
  all_goals done


/-- `pop`'s purity table. -/
abbrev popPTable (rel : Loc → Pred) (t : BitVec 64) (ra : Int64) (t0 : MachineData) :
    Label → MachineData → (RP rel).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.lr = ra ∧ CalleeSaved t0 s ∧ (lb = "pop" ∨ lb = "pop_done")

/-- **`pop` is pure** (no plain store). -/
theorem pop_pure (rel : Loc → Pred) (t : BitVec 64) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "pop")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') := by
  rintro ra t0 g ⟨hlr, hx0, ⟨hd8, hd4⟩⟩
  refine cfgEnv_partial_fun (p := popFrag) (popPTable rel t ra t0)
    (E := fun a s (_ : (RP rel).State) => a = ra ∧ CalleeSaved t0 s) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot_placed (by decide)) t0 g
    ⟨hx0, hd8, hd4, hlr, by simp [CalleeSaved], .inl rfl⟩
  cfg_cases_env [popFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd8, hd4, hlr, hfr, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hd8, SharedEnv.relPureQ]; done)
  case vc4 =>
    exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hd8], by simp [hd4],
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, .inr rfl⟩, .inl (by decide)⟩)
  case vc9 =>
    simp [hx0, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc10 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp [hd8] at hld2
    have h12 : σ1.2 ≤ σ2.2 := by
      obtain ⟨_, ⟨_, h⟩, _⟩ := hld2
      omega
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hd8], by simp [hd4],
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, .inl rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc11 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp [hd8] at hld2
    obtain ⟨_, ⟨_, -⟩, rfl⟩ := hld2
    exact ⟨by simp [hx0], by simp [hd8], by simp [hd4], by simpa [MachineData.lr] using hlr,
      by simpa [CalleeSaved] using hfr, .inr trivial⟩
  case vc1 =>
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩
  all_goals done


/-! ## `main` -/

/-- The tail's purity table. -/
abbrev tailPTable (rel : Loc → Pred) : Label → MachineData → (RP rel).State → Prop :=
  fun lb s _ => Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ (lb = "ret_pop" ∨ lb = "empty")

theorem main_tail_pure (rel : Loc → Pred) : ∀ s (σ : (RP rel).State),
    Int64.ofBitVec s.regs.X19.toBitVec = mainEnd → NoDmem s →
    Safely (cenv.instrStepEnv (RP rel)) (fun x => x.1.2 = mainEnd)
      ((s, (_root_.Executable.labels cenv).label "ret_pop"), σ) := by
  rintro s σ h19 ⟨hd8, hd4⟩
  refine cfgEnv_partial_fun (p := tailFrag) (tailPTable rel) (E := fun a _ _ => a = mainEnd) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot_placed (by decide)) s σ ⟨h19, hd8, hd4, .inl rfl⟩
  cfg_cases_env [tailFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨h19, hd8, hd4, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [h19, hd8, hd4, SharedEnv.relPureQ]; done)
  exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using h19, by simpa using hd8, by simpa using hd4,
    .inr rfl⟩, .inl (by decide)⟩)

omit [Executable.ValidLayout (layout pilot)] in
theorem main_prefix_pure (rel : Loc → Pred) (t n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec s.regs.X30.toBitVec = mainEnd ∧
        s.regs.X21.toBitVec = t ∧ s.regs.X27.toBitVec = n ∧ s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧
        NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mainPre⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧
        s.regs.X21.toBitVec = t ∧ NoDmem s); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainPre
  vcgen
  all_goals obtain ⟨⟨h30, h21, h27, hlim, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp [NoDmem] at *
  case vc1 =>
    rename_i s σ0 hhi _
    simp only [← UInt64.toNat_toBitVec] at hhi
    bv_omega
  case vc3 =>
    rw [h27]; exact hd _
  case vc4 =>
    rename_i s σ0 rng dm σ1 hhi hst _
    simp [hd4] at hst
    obtain ⟨rfl, -⟩ := hst
    first | exact ⟨h21, h27, h30, h21, hd8, hd4⟩ | simp [h21, h27, h30, hd8, hd4]


omit [Executable.ValidLayout (layout pilot)] in
theorem main_mid_pure (rel : Loc → Pred) (t : BitVec 64) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧
        s.regs.X21.toBitVec = t ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mainMid⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = t ∧ Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ NoDmem s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainMid
  vcgen
  all_goals obtain ⟨⟨h19, h21, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp [NoDmem, h19, h21, hd8, hd4]

/-- The start of `main` for purity: `MainPre` without the payload and `Pu0`. -/
def MainPreR (t n : BitVec 64) (s : MachineData) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = mainEnd ∧ s.regs.X21.toBitVec = t ∧ s.regs.X27.toBitVec = n ∧
    s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ NoDmem s

/-- **`main` is pure**: a `PartialTripleEnv` of the whole text in
`relPure`, through `push_pure` and `pop_pure`. -/
theorem main_pure (rel : Loc → Pred) (t n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    PartialTripleEnv (RP rel) (fun s _ => MainPreR t n s) pilot (fun _ _ => True) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  have hb : Program.blockAt pilot "main" = some ⟨"main", mainBody, some "ret_pop"⟩ := by decide
  have hbody : PartialWpEnv (RP rel) mainBody
      (fun s _ => Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ NoDmem s) (fun _ _ _ => False) s σ := by
    have h1 := (main_prefix_pure rel t n hd s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h1)
    rintro s1 σ1 ⟨h0, h1, h19, h21, ⟨hd8, hd4⟩⟩
    refine PartialWpEnv.call (push_pure rel t n hn) fun ra => ⟨?_, ?_⟩
    · exact ⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr, Reg64s.setXReg] using h0,
        by simpa [MachineData.setLr, Reg64s.setXReg] using h1, ⟨by simpa [MachineData.setLr] using hd8,
        by simpa [MachineData.setLr] using hd4⟩⟩
    rintro s2 σ2 ⟨f19, -, f21, -, -, -, -, -, -, -, fdm⟩
    have h2 := (main_mid_pure rel t s2 σ2).le_wp s2 σ2 ⟨⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19,
      by simpa [f21, MachineData.setLr, Reg64s.setXReg] using h21,
      ⟨by simpa [fdm, MachineData.setLr] using hd8, by simpa [fdm, MachineData.setLr] using hd4⟩⟩, rfl, rfl⟩
    rw [wpEnv_eq] at h2
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h2)
    rintro s3 σ3 ⟨h0', h19', ⟨hd8', hd4'⟩⟩
    refine PartialWpEnv.call (pop_pure rel t) fun ra => ⟨?_, ?_⟩
    · exact ⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr, Reg64s.setXReg] using h0',
        ⟨by simpa [MachineData.setLr] using hd8', by simpa [MachineData.setLr] using hd4'⟩⟩
    rintro s4 σ4 ⟨g19, -, -, -, -, -, -, -, -, -, gdm⟩
    exact PartialWpEnv.nil ⟨by simpa [g19, MachineData.setLr, Reg64s.setXReg] using h19',
      ⟨by simpa [gdm, MachineData.setLr] using hd8', by simpa [gdm, MachineData.setLr] using hd4'⟩⟩
  rw [← pilot_placed.entry pc hpc]
  refine Safely.bind (hbody _ (pilot_placed.block _ _ hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, h19, hdm⟩ | hF)
  · dsimp only at ha h19 hdm
    rw [pilot_placed.next _ _ _ hb rfl] at ha
    subst ha
    refine (main_tail_pure rel s' g' h19 hdm).mono fun x hx => .inl ⟨?_, trivial⟩
    obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := pilot) pilot [] 0 (by simp)
    rw [hx, pilot_placed.entry _ hs0, Nat.zero_add] at *
    exact haf.symm
  · exact hF.elim

end Kraken.Promising.Lower.Pilot
