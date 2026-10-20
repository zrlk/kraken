/-
**Validation 2: `pilot2_promising` through the
frame + value-bridge kit.** ISA: AArch64; machine: the
executable Promising machine (`Reachable Arch.armv8`).

`pilot2_promising_viaKit` has exactly the statement of the unconditional stack-frame pilot's
`pilot2_promising` (`Lower/Pilot2ValsWhole.lean`; same section variables) and
is proved by `Kit.lower_promising_vals` from the stack-frame pilot's pieces
(`main_partialTripleEnv2`, `main_pure2`, `main_val2`, `hB_P2`, `StartP2`,
`memInv_treiber2_init`, the static facts) and the Treiber final reading
`KitPilot.treiber2DFinal_of_hB`.
-/
import Kraken.Promising.Lower.KitPilot
import Kraken.Promising.Lower.Pilot2ValsWhole

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.KitPilot2

open Kraken.Promising.SLR.EnvG.Treiber2 Kraken.Promising.Lower.Kit Kraken.Promising.Lower.Pilot2

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot2)]

/-- **`pilot2` as a lowered thread with a frame**, thread `w` (node `P.n w`,
payload `d9`, stack `[lo, lo + nb)`). -/
noncomputable def pilot2T (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d9 : BitVec 32) (lo : BitVec 64)
    (nb : Nat) (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d)
    (hd : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w + 8, 8⟩) v) :
    LowerThreadV Arch.armv8 w (ghost₀ P).rel (TB2D P) (SLay P) (GV P) where
  l := layout
  p := pilot2
  valid := inferInstance
  pl := plan P w
  hpl := plan_valid P w
  live := pilot2_rmwLive
  shape := pilot2_phase1F
  stuck env := not_instrStepEnv_of_end_labels env 1
  Q s σ := DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1
  hB := hB_P2 P hw
  PreR s _ := MainPreR2 P w lo nb s
  QR _ _ := True
  pure := main_pure2 _ P w hw lo nb hd hn
  Pre := MainPre2 P w d9 lo nb
  main := main_partialTripleEnv2 P w hL hw d9 lo nb hD
  PreV s _ := MainPreR2 P w lo nb s
  QV _ _ := True
  vals := main_val2 P w hw lo nb

/-- **A `StartP2` start is a kit start** of `pilot2T`. -/
theorem pilot2T_start {P : Params} {w : Nat} (hL : TLocs P) (hw : w < 2) {d9 : BitVec 32} {lo : BitVec 64}
    {nb : Nat} (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) {hd hn} {s : isa.State}
    (hS : StartP2 P w d9 lo nb s) {c : Config isa} (hT0 : c.mem.initVal P.top = 0) :
    (pilot2T P w hL hw d9 lo nb hD hd hn).Start (σInit c (thrRes c.mem P w) (ghost₀ P)) s := by
  obtain ⟨he, hds, hend, hpc, h30, h21, h27, h28, h9, hst, hsp, hsl⟩ := hS
  exact ⟨⟨he, hds, hend, hpc, 0, h30, h21, h27, h28, hst, hsp, hsl⟩,
    ⟨0, h30, h21, h27, h28, h9, hst, hsp, hsl, pu0_init P hL hw _ hT0⟩, 0, h30, h21, h27, h28, hst, hsp, hsl⟩

/-- **`pilot2_promising` through the kit** (same statement as the unconditional stack-frame pilot's
`pilot2_promising`). -/
theorem pilot2_promising_viaKit {t n0 n1 : BitVec 64} {fuel : Nat}
    (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} {lo0 lo1 : BitVec 64} {nb0 nb1 : Nat}
    (h0 : StartP2 (tPD t n0 n1) 0 1 lo0 nb0 s0) (h1 : StartP2 (tPD t n0 n1) 1 2 lo1 nb1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [s0, s1] initMem).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem).mem.initVal ⟨n1 + 8, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  have hr : ∀ l, l ≠ (tPD t n0 n1).top → ∀ v, Pred.Pure ((ghost₀ (tPD t n0 n1)).rel l) v :=
    fun l hl v => by rw [ghost₀_rel_ne hl]; exact Pred.emp_pure v
  refine lower_promising_vals Arch.armv8 fuel (treiber2GA t n0 n1) (fun _ hc' => Config.ntFree_armv8 hc')
    (erase_init hL _) rfl (memInv_treiber2_init hT0 hN0 hN1)
    (fun tid h => match tid, h with
      | 0, _ => pilot2T _ 0 hL (by decide) 1 lo0 nb0 (fun _ h => h) (hr _ (top_dd _ 0).symm)
          (hr _ (hL.top_nd' (by decide)).symm)
      | 1, _ => pilot2T _ 1 hL (by decide) 2 lo1 nb1 (fun _ h => h) (hr _ (top_dd _ 1).symm)
          (hr _ (hL.top_nd' (by decide)).symm)
      | _ + 2, h => absurd h (by simp))
    (fun tid h => ?_) hc hf (KitPilot.treiber2DFinal_of_hB hL hf rfl)
  rcases tid with _ | _ | _
  · exact pilot2T_start (w := 0) hL (by decide) _ h0 hT0
  · exact pilot2T_start (w := 1) hL (by decide) _ h1 hT0
  · simp at h; omega

omit [Executable.ValidLayout (layout pilot2)] in
/-- The statement is `pilot2_promising`'s, verbatim. -/
example : @pilot2_promising_viaKit = @Pilot2.pilot2_promising := rfl

end Kraken.Promising.Lower.KitPilot2

#print axioms Kraken.Promising.Lower.KitPilot2.pilot2_promising_viaKit
