/-
**Part 4: `publishP` is pure** in `RP rel` for
release predicates pure at `[n]` (4 bytes) and `[n + 8]` (8 bytes). ISA:
AArch64; machine: the executable machine's per-thread
environment semantics (`relPure` environment), partial correctness.

- `pushp_pure`: `pushp`'s purity from `Pilot.pushFrag_pure` (used as is) by
  `FragSpecEnvL.tail`; `relPure` skips fences, so `dmb ishst` leaves no VC.
- `alloc`, `pop` by the existing fragment specifications at `publishP`.
- `main`: the allocation pilot's proof (`Lower/AllocPure.lean`) at `publishP`, the call to
  `pushp` through `pushp_pure_at`.
-/
import Kraken.Promising.Lower.PublishMain

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Publish

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP pushFrag popFrag tailFrag mainMid pushFrag_pure
  popFrag_pure)
open Kraken.Promising.Lower.Alloc (mainInit mainSave rpFenceMono)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## `pushp`, `pop` -/

/-- **`pushp` is pure**, from `push`'s purity by `FragSpecEnvL.tail`. -/
theorem pushp_pure (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FragSpecEnvL (RP rel) [pushpFrag, pushFrag] "pushp"
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s') := by
  refine FragSpecEnvL.tail (pushFrag_pure rel t n hn).toL (blk := ⟨"pushp", pushpBody, none⟩) (by decide) ?_
  intro _ ra t0 g
  unfold pushpBody
  dsimp only
  vcgen
  obtain ⟨hpre, hs, -⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  subst hs
  exact .inl ⟨rfl, hpre, fun _ _ h => h⟩

variable [layout : _root_.Layout] [Executable.ValidLayout (layout publishP)]

local instance publishP.envP : CodeEnv := ⟨layout publishP⟩

/-- `pushp`'s purity at `publishP`. -/
theorem pushp_pure_at (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "pushp")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s') :=
  (pushp_pure rel t n hn).of_placed publishP_placed (by decide)

/-- `pop`'s purity at `publishP`. -/
theorem pop_pure (rel : Loc → Pred) (t : BitVec 64) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "pop")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') :=
  (popFrag_pure rel t).of_placed publishP_placed (by decide)

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
    rfl (by decide) (Program.PlacedIn.of_placedE publishP_placed (by decide)) s σ ⟨h19, hd8, hd4, .inl rfl⟩
  cfg_cases_env [tailFrag]
  all_goals (intro s₀ g₀; vcgen)
  all_goals obtain ⟨⟨h19, hd8, hd4, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [h19, hd8, hd4, SharedEnv.relPureQ]; done)
  exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using h19, by simpa using hd8, by simpa using hd4,
    .inr rfl⟩, .inl (by decide)⟩)

omit [Executable.ValidLayout (layout publishP)] in
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

omit [Executable.ValidLayout (layout publishP)] in
theorem main_save_pure (rel : Loc → Pred) (t n : BitVec 64) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec s.regs.X30.toBitVec = mainEnd ∧
        s.regs.X21.toBitVec = t ∧ s.regs.X27.toBitVec = n ∧ s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧
        NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mainSave⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ s.regs.X21.toBitVec = t ∧
        s.regs.X27.toBitVec = n ∧ s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ NoDmem s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainSave
  vcgen
  all_goals obtain ⟨⟨h30, h21, h27, hlim, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp [NoDmem, h30, h21, h27, hd8, hd4]
  exact h27 ▸ hlim

omit [Executable.ValidLayout (layout publishP)] in
/-- The initial stores are pure (`[n]`, `[n + 8]`). -/
theorem main_init_pure (rel : Loc → Pred) (t n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (s.regs.X0.toBitVec = n ∧
        Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ s.regs.X21.toBitVec = t ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainInit⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧
        s.regs.X21.toBitVec = t ∧ NoDmem s); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainInit
  vcgen
  all_goals obtain ⟨⟨h0, h19, h21, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp [NoDmem] at *
  case vc2 => rw [h0]; exact hd _
  case vc4 => rw [h0]; exact hn _
  case vc5 =>
    rename_i hst1 hst2 _
    simp [hd4] at hst1
    obtain ⟨rfl, -⟩ := hst1
    simp [hd8] at hst2
    obtain ⟨rfl, -⟩ := hst2
    exact ⟨h21, h0, h19, h21, hd8, hd4⟩

/-- `MainPre` without the payload and `Pu0`. -/
def MainPreR (t n : BitVec 64) (s : MachineData) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = mainEnd ∧ s.regs.X21.toBitVec = t ∧ s.regs.X27.toBitVec = n ∧
    s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ NoDmem s

attribute [local simp] MachineData.lr MachineData.setLr Reg64s.setXReg in
/-- **`main` is pure** (whole text). -/
theorem main_pure (rel : Loc → Pred) (t n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    PartialTripleEnv (RP rel) (fun s _ => MainPreR t n s) publishP (fun _ _ => True) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  have hb : Program.blockAt publishP "main" = some ⟨"main", mainBody, some "ret_pop"⟩ := by decide
  have hbody : PartialWpEnv (RP rel) mainBody
      (fun s _ => Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ NoDmem s) (fun _ _ _ => False) s σ := by
    have h1 := (main_save_pure rel t n s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h1)
    rintro s1 σ1 ⟨h19, h21, h27, hlim, ⟨hd8, hd4⟩⟩
    refine PartialWpEnv.call (@alloc_spec _ _ (RP rel) (rpFenceMono rel) (fun _ => True) (fun _ _ _ _ => trivial) n)
      fun ra => ⟨⟨by simp, by simpa using h27, by simpa using hlim, trivial⟩, ?_⟩
    rintro s2 σ2 ⟨a0, -, ⟨f19, -, f21, -, -, -, -, -, -, fdm⟩, -⟩
    have h2 := (main_init_pure rel t n hd hn s2 σ2).le_wp s2 σ2 ⟨⟨a0, by simpa [f19] using h19,
      by simpa [f21] using h21, ⟨by simpa [fdm] using hd8, by simpa [fdm] using hd4⟩⟩, rfl, rfl⟩
    rw [wpEnv_eq] at h2
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h2)
    clear h19 h21 hd8 hd4
    rintro s1 σ1 ⟨h0, h1, h19, h21, ⟨hd8, hd4⟩⟩
    refine PartialWpEnv.call (pushp_pure_at rel t n hn) fun ra =>
      ⟨⟨by simp, by simpa using h0, by simpa using h1, ⟨by simpa using hd8, by simpa using hd4⟩⟩, ?_⟩
    rintro s2 σ2 ⟨f19, -, f21, -, -, -, -, -, -, -, fdm⟩
    have h2 := (main_mid_pure rel t s2 σ2).le_wp s2 σ2 ⟨⟨by simpa [f19] using h19, by simpa [f21] using h21,
      ⟨by simpa [fdm] using hd8, by simpa [fdm] using hd4⟩⟩, rfl, rfl⟩
    rw [wpEnv_eq] at h2
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h2)
    rintro s3 σ3 ⟨h0', h19', ⟨hd8', hd4'⟩⟩
    refine PartialWpEnv.call (pop_pure rel t) fun ra =>
      ⟨⟨by simp, by simpa using h0', ⟨by simpa using hd8', by simpa using hd4'⟩⟩, ?_⟩
    rintro s4 σ4 ⟨g19, -, -, -, -, -, -, -, -, -, gdm⟩
    exact PartialWpEnv.nil ⟨by simpa [g19] using h19', ⟨by simpa [gdm] using hd8', by simpa [gdm] using hd4'⟩⟩
  rw [← publishP_placed.entry pc hpc]
  refine Safely.bind (hbody _ (publishP_placed.block _ _ hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, h19, hdm⟩ | hF)
  · dsimp only at ha h19 hdm
    rw [publishP_placed.next _ _ _ hb rfl] at ha
    subst ha
    refine (main_tail_pure rel s' g' h19 hdm).mono fun x hx => .inl ⟨?_, trivial⟩
    obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := publishP) publishP [] 0 (by simp)
    rw [hx, publishP_placed.entry _ hs0, Nat.zero_add] at *
    exact haf.symm
  · exact hF.elim

end Kraken.Promising.Lower.Publish
