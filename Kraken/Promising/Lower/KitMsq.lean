/-
**Validation 3: `msqPilot_promising` through the
kit.** ISA: AArch64; machine: the executable Promising
machine (`Reachable Arch.armv8`).

`msqPilot_promising_viaKit` has exactly the statement of the MS queue pilot's
`msqPilot_promising` (`Lower/MsqPilotWhole.lean`) and is proved by
`Kit.lower_promising` from the MS queue pilot's pieces (`main{E,D}_partialTripleEnv`,
`main{E,D}_pure`, `StartE`/`StartD`, the static facts) and msqueue2's final
reading `msqueue2_final_of_hB`. The two threads run different texts at
different thread ids and plans. Also: `KitCfg`'s
`cfgEnv_partial_fun_edgeRank` has the MS queue pilot's `cfgEnv_partial_fun_rank`
statement.
-/
import Kraken.Promising.Lower.Kit
import Kraken.Promising.Lower.KitCfg
import Kraken.Promising.Lower.MsqPilotWhole

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.KitMsq

open Kraken.Promising.SLR.EnvG.MsQueue Kraken.Promising.Lower.Kit Kraken.Promising.Lower.MsqPilot

/-- `hB` of the enqueuer (`ruleE`'s inline proof). -/
theorem hB_E (l : _root_.Layout) (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postOf (layout := l) progE (fun _ σ => ∃ _ : Nat, ComE2 P σ) (t.st.st, σ) → t.prom = [] →
    EnvRel 0 (planE2 P) σ c t r g cl → cl → MB2 P c r g := by
  intro c t r g cl σ hpost hp hrel _
  obtain ⟨-, -, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hcom.2.2.1
  · rw [hp] at hts; cases hts

/-- `hB` of the dequeuer (`ruleD`'s inline proof). -/
theorem hB_D (l : _root_.Layout) (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postOf (layout := l) progD (fun s σ => ∃ _ : Nat, Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ)
      (t.st.st, σ) → t.prom = [] → EnvRel 1 (planD2 P) σ c t r g cl → cl → MB2 P c r g := by
  intro c t r g cl σ hpost hp hrel _
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1⟩
  · rw [hp] at hts; cases hts

/-- **The enqueuer as a lowered thread** (thread `0`, `progE` at `l`). -/
noncomputable def enqT (l : _root_.Layout) [Executable.ValidLayout (l progE)] (P : Params2) (hL : QLocs2 P)
    (ht : P.t = P.h + 8) (hd : ∀ v : Val, Pred.Pure ((ghost2 P).rel ⟨P.n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure ((ghost2 P).rel ⟨P.n2, 4⟩) v) :
    LowerThread Arch.armv8 0 (ghost2 P).rel (MB2 P) where
  l := l
  p := progE
  valid := inferInstance
  pl := planE2 P
  hpl := planE2_valid P
  live := progE_rmwLive (layout := l)
  shape := progE_phase1F (layout := l)
  stuck env := not_instrStepEnv_of_end_labels (layout := l) env 1
  Q _ σ := ComE2 P σ.1
  hB := hB_E l P
  PreR s _ := Int64.ofBitVec s.regs.X30.toBitVec = endE (layout := l) ∧ s.regs.X22.toBitVec = P.n1 ∧
    s.regs.X23.toBitVec = P.n2 ∧ Pilot.NoDmem s
  QR _ _ := True
  pure := mainE_pure (layout := l) _ P.n1 P.n2 hd hd2
  Pre := MainEPre (layout := l) P
  main := mainE_partialTripleEnv (layout := l) P hL ht

/-- **The dequeuer as a lowered thread** (thread `1`, `progD` at `l`). -/
noncomputable def deqT (l : _root_.Layout) [Executable.ValidLayout (l progD)] (P : Params2) (hL : QLocs2 P)
    (ht : P.t = P.h + 8) : LowerThread Arch.armv8 1 (ghost2 P).rel (MB2 P) where
  l := l
  p := progD
  valid := inferInstance
  pl := planD2 P
  hpl := planD2_valid P
  live := progD_rmwLive (layout := l)
  shape := progD_phase1F (layout := l)
  stuck env := not_instrStepEnv_of_end_labels (layout := l) env 1
  Q s σ := Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1
  hB := hB_D l P
  PreR s _ := Int64.ofBitVec s.regs.X30.toBitVec = endD (layout := l) ∧ Pilot.NoDmem s
  QR _ _ := True
  pure := mainD_pure (layout := l) _
  Pre := MainDPre (layout := l) P
  main := mainD_partialTripleEnv (layout := l) P hL ht

/-- **`msqPilot_promising` through the kit** (same statement as the MS queue pilot's
`msqPilot_promising`). -/
theorem msqPilot_promising_viaKit {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64) (ht : t = h + 8) (hht : h ≠ t)
    (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8)
    (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartE (layout := l0) h n1 n2 s0)
    (h1 : StartD (layout := l1) h s1) (hi : InitV2 (Config.init [s0, s1] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : MsQueue2Final cfg := by
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  have hr : ∀ l, ¬ Params2.IsW ⟨⟨h, t, d, n1⟩, n2⟩ l → ∀ v, Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel l) v :=
    fun l hl v => by rw [ghost2_rel_ne hl]; exact Pred.emp_pure v
  refine lower_promising Arch.armv8 fuel (fun _ hc' => Config.ntFree_armv8 hc') (erase_init2 hL _) rfl
    (fun tid hh => match tid, hh with
      | 0, _ => enqT l0 _ hL ht (hr _ (not_isW_dat _)) (hr _ (not_isW_dat2 _))
      | 1, _ => deqT l1 _ hL ht
      | _ + 2, hh => absurd hh (by simp))
    (fun tid hh => ?_) hc hf fun rF' g' E' hle hsize hB => msqueue2_final_of_hB hL hf E' hle hsize hB
  rcases tid with _ | _ | _
  · obtain ⟨he, hds, hend, hpc, h30, h21, h22, h23, hd8, hd4⟩ := h0
    exact ⟨⟨he, hds, hend, hpc, 0, h30, h22, h23, hd8, hd4⟩, 0, h30, h21, h22, h23, ⟨hd8, hd4⟩, start1_init _ _⟩
  · obtain ⟨he, hds, hend, hpc, h30, h21, hd8, hd4⟩ := h1
    exact ⟨⟨he, hds, hend, hpc, 0, h30, hd8, hd4⟩, 0, h30, h21, ⟨hd8, hd4⟩, comD2_init _ _ hi⟩
  · simp at hh; omega

/-- The statement is `msqPilot_promising`'s, verbatim. -/
example : @msqPilot_promising_viaKit = @MsqPilot.msqPilot_promising := rfl

/-- `KitCfg`'s rank instance has the MS queue pilot's statement, verbatim. -/
example : @MachineWP.cfgEnv_partial_fun_edgeRank = @MsqPilot.cfgEnv_partial_fun_rank := rfl

end Kraken.Promising.Lower.KitMsq

#print axioms Kraken.Promising.Lower.KitMsq.msqPilot_promising_viaKit
