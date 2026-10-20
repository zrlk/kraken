/-
**The relPure twins of `wcMsqX`'s two threads** (the kit's
`LowerCoreX.pure`: counted `EnvRT sAll`), as for the x64 MS queue pilot
(`Lower/MsqXRPure.lean`, its table `twinT`), exiting at `done`: the
enqueuer's is one `cfgEnv_partial_fun` over `fragE`; the dequeuer's composes
`main_w`'s blocks with `wdeq_twin`, a function specification of `wdeq`
(its empty exit returns without a shared access, a zero-step back edge in a
table over all of `fragW`).
-/
import Kraken.Promising.Lower.WcMsqXMain
import Kraken.Promising.Lower.MsqXRPure
import Kraken.Promising.SLR.EnvG.FenceInvTrue

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.WcMsqX

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll mem_sAll8 EnvRT)
open Kraken.Promising.X64.EnvG.Treiber2X (ldN stN)
open Kraken.Promising.Lower.PilotX (Saved Saved.refl)
open Kraken.Promising.Lower.PilotXR (D8 ofBitVec_reg)
open Kraken.Promising.Lower.MsqXR (twinT fragE mainETxt enqFrag mainEBody retE1Body retE2Body)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

set_option hygiene false in
/-- Land on a twin's table label (a back edge's count up), or exit at a link `hT`. -/
local macro "twin_land" : tactic => `(tactic| (
  first
    | exact .inr (ofBitVec_reg hT)
    | exact .inr (ofBitVec_reg hT.2)
    | (refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, ?_⟩, ?_⟩)
       · have hT' := hT; simp only [Reg64s.get64] at hT'
         simp (config := { decide := true }) [twinT, hT, hT']
       · first | exact .inl (by decide) | exact .inr fun ⟨_, hg⟩ => by subst hg; cnt_all; omega)))

/-- **A block at its label** (`Safely.blockAt` without `FenceMonoX`): for an
environment whose fences are always permitted (`FenceInv` of `True`). Alias of
the generic `_root_.Safely.blockAtT` (`Lower/PilotXRMain.lean`). -/
theorem Safely.blockAtT [CodeEnv] {env : SharedEnv} (hI : env.FenceInv fun _ => True) {p : Program} {l : Label}
    {blk : Program.Block} (hpl : Program.PlacedIn p) (hb : Program.blockAt p l = some blk) {s : MachineData}
    {g : env.State} {X : Int64 → MachineData → Prop} {Q : MachineState × env.State → Prop}
    (h : ⦃ fun s' => s' = s ⦄ blk.body ⦃ fun _ _ => False; X ⦄)
    (hk : ∀ a s' g', X a s' → Safely (cenv.instrStepEnv env) Q ((s', a), g')) :
    Safely (cenv.instrStepEnv env) Q ((s, (_root_.Executable.labels cenv).label l), g) :=
  _root_.Safely.blockAtT hI hpl hb h hk

/-- Alias of the generic `SharedEnv.Skips.fenceInv_true` (`SLR/EnvG/FenceInvTrue.lean`). -/
theorem fenceInv_rt : (SharedEnv.counted (EnvRT sAll)).FenceInv fun _ => True :=
  SharedEnv.Skips.fenceInv_true _

/-- **`wdeq`'s twin**: from the link in `r11` and `dmem` empty, `wdeq`
returns to the link with the callee-saved frame (`Saved`). Its exit
`wdeq_empty` returns without a shared access, so the dequeuer's twin goes
through this function specification rather than one table over `fragW`. -/
theorem wdeq_twin : FragSpecEnv (SharedEnv.counted (EnvRT sAll)) wdeqFrag "wdeq"
    (fun ra t _ => t.regs.get64 .r11 = ra.toBitVec ∧ D8 t.dmem) (fun _ t _ s _ => Saved t s) := by
  refine FragSpecEnv.of_cfg (fun ra t _ lb s _ => s.regs.get64 .r11 = ra.toBitVec ∧ Saved t s ∧ D8 s.dmem ∧
      (lb = "wdeq" ∨ lb = "wdeq_empty")) rfl (by decide)
    (fun ra t g ⟨h1, h2⟩ => ⟨h1, Saved.refl t, h2, .inl rfl⟩) ?_
  intro _; rintro ra t g -
  cfg_cases_env [wdeqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨h11, ⟨sv1, sv2, sv3, sv4, sv5, sv6, fdm⟩, hd8, -⟩, rfl, rfl⟩ :=
    ‹(_ ∧ _ ∧ _ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals first
    | exact hd8 _
    | (refine ⟨⟨?_, mem_sAll8 _⟩, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]
       first | rfl | trivial | exact fun h => absurd rfl h | exact fun h => h rfl)
    | (refine .inr ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩⟩ <;>
       simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] <;> first | assumption | exact ofBitVec_reg h11)
    | (refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8, by decide⟩, ?_⟩) <;>
       (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) <;>
       first | assumption | exact .inl (by decide) | exact .inr fun ⟨_, hg⟩ => by subst hg; cnt_all; omega)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout wcMsqX)]

local instance wcMsqX.envP : CodeEnv := ⟨layout wcMsqX⟩

/-- **The enqueuer's twin**: from `main_e` with `dmem` empty and the link at
`done`, every run that stops is at `done`. -/
theorem wcMsqX_pureE :
    ∀ s g, D8 s.dmem ∧ s.regs.get64 .r11 = (labW "done").toBitVec →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll))) (fun x => x.1.2 = labW "done")
        ((s, labW "main_e"), g) := by
  rintro s g ⟨hd8, h11⟩
  refine cfgEnv_partial_fun (p := fragE) (env := SharedEnv.counted (EnvRT sAll)) (E := fun a _ _ => a = labW "done")
    (fun lb s _ => twinT "main_e" "ret_e1" "ret_e2" (labW "done").toBitVec (labW "ret_e1").toBitVec
      (labW "ret_e2").toBitVec lb s) ?_ rfl
    (by decide) (Program.PlacedIn.of_placedE wcMsqX_placed (by decide)) s g ⟨hd8, by simpa [twinT] using h11⟩
  cfg_cases_env [fragE, mainETxt, enqFrag, mainEBody, retE1Body, retE2Body]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : twinT _ _ _ _ _ _ _ _ ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨hd8, hT⟩, rfl, rfl⟩ := hx
  all_goals simp only [↓reduceIte, String.reduceEq, or_false, false_or, or_self] at hT
  all_goals first
    | exact hd8 _
    | (refine ⟨⟨?_, mem_sAll8 _⟩, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]
       first | rfl | trivial | exact fun h => absurd rfl h | exact fun h => h rfl)
    | (try dsimp only
       try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
       first
         | twin_land
         | (rcases hT.1 with h | h <;> rw [ofBitVec_reg h] <;> twin_land))
    | skip

/-- **The dequeuer's twin**, from `main_w`: `main_w`'s three blocks around
two calls of `wdeq_twin`. -/
theorem wcMsqX_pureW :
    ∀ s g, D8 s.dmem ∧ s.regs.get64 .r11 = (labW "done").toBitVec →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll))) (fun x => x.1.2 = labW "done")
        ((s, labW "main_w"), g) := by
  have hpl : Program.PlacedIn wcMsqX := wcMsqX_placed.toPlacedIn
  have hD := wdeq_twin.of_placed wcMsqX_placed (by decide)
  rintro s g ⟨hd8, h11⟩
  refine Safely.blockAtT fenceInv_rt hpl blockAt_mainW (X := fun a s₁ => a = labW "wdeq" ∧
      s₁.regs.get64 .r11 = (labW "ret_w1").toBitVec ∧ s₁.regs.get64 .rbp = (labW "done").toBitVec ∧
      s₁.dmem = s.dmem) ?_ ?_
  · simp only [mainWBody]; vcgen
    case vc1 s' hs => subst hs; simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h11, and_true]
  rintro a s₁ g₁ ⟨rfl, h1r11, h1bp, h1dm⟩
  refine hD.jcall (ra := labW "ret_w1") ⟨h1r11, h1dm ▸ hd8⟩ fun s₂ g₂ ⟨_, h2bp, _, _, _, _, h2dm⟩ => ?_
  refine Safely.blockAtT fenceInv_rt hpl blockAt_retW1 (X := fun a s₃ => a = labW "wdeq" ∧
      s₃.regs.get64 .r11 = (labW "ret_w2").toBitVec ∧ s₃.regs.get64 .rbp = s₂.regs.get64 .rbp ∧
      s₃.dmem = s₂.dmem) ?_ ?_
  · simp only [retW1Body]; vcgen
    case vc1 s' hs => subst hs; simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_true]
  rintro a s₃ g₃ ⟨rfl, h3r11, h3bp, h3dm⟩
  refine hD.jcall (ra := labW "ret_w2") ⟨h3r11, by rw [h3dm, h2dm, h1dm]; exact hd8⟩
    fun s₄ g₄ ⟨_, h4bp, _, _, _, _, _⟩ => ?_
  refine Safely.blockAtT fenceInv_rt hpl blockAt_retW2 (X := fun a _ => a = Int64.ofBitVec (s₄.regs.get64 .rbp)) ?_ ?_
  · simp only [retW2Body]; vcgen
    case vc1 s' hs => subst hs; rfl
  rintro a s₅ g₅ rfl
  exact Safely.fold (.inl (ofBitVec_reg (by rw [h4bp, h3bp, h2bp, h1bp])))

end Kraken.Promising.Lower.WcMsqX
