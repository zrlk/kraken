/-
**Validation 1: `pilot_promising` through the kit.**
ISA: AArch64; machine: the executable Promising machine
(`Reachable Arch.armv8`).

`pilot_promising_viaKit` has exactly the statement of the first lowering pilot's
`pilot_promising` (`Lower/PilotWhole.lean`) and is proved by
`Kit.lower_promising` from the first lowering pilot's pieces (`main_partialTripleEnv`,
`main_pure`, `hB_P`, `StartP`, the static facts). The final reading of the
Treiber client (`treiber2DFinal_of_hB`) is stated once here and reused by
`KitPilot2`; it depends on the data structure only, not on the lowering.
-/
import Kraken.Promising.Lower.Kit
import Kraken.Promising.Lower.PilotWhole

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.KitPilot

open Kraken.Promising.SLR.EnvG.Treiber2 Kraken.Promising.Lower.Kit Kraken.Promising.Lower.Pilot

/-- **The Treiber client's final reading** (the `hfin` of `treiber2_envG`,
`pilot_promising` and `pilot2_promising`): two done threads whose shared
postconditions are `TB2D` hold distinct nodes with their payloads. -/
theorem treiber2DFinal_of_hB {t n0 n1 : BitVec 64} (hL : TLocs (tPD t n0 n1)) {c : Config isa}
    (hf : c.final = true) {k : Nat} (hk : k = 2) :
    ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → (ghost₀ (tPD t n0 n1)).Le g' →
      c.threads.size = k → (∀ tid, c.Done tid → TB2D (tPD t n0 n1) c (rF' tid) g') → Treiber2DFinal n0 n1 c := by
  subst hk
  intro rF' g' E' hle hsize hB
  have hi0 : (0 : Nat) < c.threads.size := by rw [hsize]; decide
  have hi1 : (1 : Nat) < c.threads.size := by rw [hsize]; decide
  have hW := (ghost₀_gw (tPD t n0 n1)).mono hle
  have hno := Config.final_not_outstanding hf
  obtain ⟨w0, hw0, th, hth, hd0⟩ := hB 0 (Config.final_done hf hi0)
  obtain ⟨w1, hw1, th', hth', hd1⟩ := hB 1 (Config.final_done hf hi1)
  by_cases hww : w0 = w1
  · subst hww
    exact (acq_pair_false E' hi0 hi1 (by decide) hd0.1 hd1.1).elim
  rcases w0 with _ | _ | w0
  · rcases w1 with _ | _ | w1
    · exact absurd rfl hww
    · refine ⟨th, th', hth, hth', ?_⟩
      rcases final_values_data E' hW hL hno hi0 hi1 hd0 hd1 with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · omega
  · rcases w1 with _ | _ | w1
    · refine ⟨th', th, hth', hth, ?_⟩
      rcases final_values_data E' hW hL hno hi1 hi0 hd1 hd0 with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · exact absurd rfl hww
    · omega
  · omega

/-! ## The program's side: one `LowerThread` per thread -/

/-- **`pilot` as a lowered thread** at layout `l`, thread `w` (node `P.n w`,
payload `d9`). -/
noncomputable def pilotT (l : _root_.Layout) [Executable.ValidLayout (l pilot)] (P : Params) (w : Nat)
    (hL : TLocs P) (hw : w < 2) (d9 : BitVec 32) (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d)
    (hd : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w + 8, 8⟩) v) :
    LowerThread Arch.armv8 w (ghost₀ P).rel (TB2D P) where
  l := l
  p := pilot
  valid := inferInstance
  pl := plan P w
  hpl := plan_valid P w
  live := pilot_rmwLive (layout := l)
  shape := pilot_phase1F (layout := l)
  stuck env := not_instrStepEnv_of_end_labels (layout := l) env 1
  Q s σ := DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1
  hB := hB_P (layout := l) P hw
  PreR s _ := MainPreR P.t (P.n w) s
  QR _ _ := True
  pure := main_pure (layout := l) _ P.t (P.n w) hd hn
  Pre := MainPre P w d9
  main := main_partialTripleEnv (layout := l) P w hL hw d9 hD

/-- **A `StartP` start is a kit start** of `pilotT`. -/
theorem pilotT_start (l : _root_.Layout) [Executable.ValidLayout (l pilot)] {P : Params} {w : Nat}
    (hL : TLocs P) (hw : w < 2) {d9 : BitVec 32} (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) {hd hn}
    {s : isa.State} (hS : StartP (layout := l) P.t (P.n w) d9 s) {c : Config isa} (hT0 : c.mem.initVal P.top = 0) :
    (pilotT l P w hL hw d9 hD hd hn).Start (σInit c (thrRes c.mem P w) (ghost₀ P)) s := by
  obtain ⟨he, hds, hend, hpc, h30, h21, h27, h28, h9, hd8, hd4⟩ := hS
  exact ⟨⟨he, hds, hend, hpc, 0, h30, h21, h27, h28, hd8, hd4⟩,
    0, h30, h21, h27, h28, h9, ⟨hd8, hd4⟩, pu0_init P hL hw _ hT0⟩

/-- `pilotT`'s rule excludes faults (`ruleP_noFault` through the kit). -/
theorem pilotT_noFault (l : _root_.Layout) [Executable.ValidLayout (l pilot)] (P : Params) (w : Nat)
    (hL : TLocs P) (hw : w < 2) (d9 : BitVec 32) (hD hd hn) :
    NoFaultRuleF (pilotT l P w hL hw d9 hD hd hn).rule :=
  LowerThread.rule_noFault _ (pilot_noFault (layout := l))

/-! ## The headline through the kit -/

/-- **`pilot_promising` through the kit** (same statement as the first lowering pilot's
`pilot_promising`). -/
theorem pilot_promising_viaKit {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 pilot)]
    [Executable.ValidLayout (l1 pilot)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  have hr : ∀ l, l ≠ (tPD t n0 n1).top → ∀ v, Pred.Pure ((ghost₀ (tPD t n0 n1)).rel l) v :=
    fun l hl v => by rw [ghost₀_rel_ne hl]; exact Pred.emp_pure v
  refine lower_promising Arch.armv8 fuel (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) rfl
    (fun tid h => match tid, h with
      | 0, _ => pilotT l0 _ 0 hL (by decide) 1 (fun _ h => h) (hr _ (top_dd _ 0).symm) (hr _ (hL.top_nd' (by decide)).symm)
      | 1, _ => pilotT l1 _ 1 hL (by decide) 2 (fun _ h => h) (hr _ (top_dd _ 1).symm) (hr _ (hL.top_nd' (by decide)).symm)
      | _ + 2, h => absurd h (by simp))
    (fun tid h => ?_) hc hf (treiber2DFinal_of_hB hL hf rfl)
  rcases tid with _ | _ | _
  · exact pilotT_start l0 (w := 0) hL (by decide) _ h0 hT0
  · exact pilotT_start l1 (w := 1) hL (by decide) _ h1 hT0
  · simp at h; omega

/-- The statement is `pilot_promising`'s, verbatim. -/
example : @pilot_promising_viaKit = @Pilot.pilot_promising := rfl

end Kraken.Promising.Lower.KitPilot

#print axioms Kraken.Promising.Lower.KitPilot.pilot_promising_viaKit
