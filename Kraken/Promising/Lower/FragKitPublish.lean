/-
**The publish pilot and the allocation pilot through the fragment
route.** ISA: AArch64 (`isa`); `Arch.armv8`; the
executable machine (`Reachable`).

One `main` proof (`FragKit.main_fragL`, `Lower/FragKitMain.lean`) serves both
texts; per text the kit's `main` field is one application of
`Kit.partialTripleEnv_of_fragL` (`Lower/KitFrag.lean`), side conditions by
`decide`, `rfl` and `id` (the original `MainPre` is `MainPreF` at the end of
the text, definitionally):

- `publishMain_fragL` (frags `[mainFragG "pushp", allocFrag, popFrag,
  pushpFrag, pushFrag]`, `Publish.pushp_spec`) and `publish_main_viaFragKit`
  (the original `Publish.main_partialTripleEnv`'s statement);
- `allocMain_fragL` (frags `[mainFragG "push", allocFrag, popFrag, pushFrag]`,
  `Pilot.pushFrag_spec.toL`) and `alloc_main_viaFragKit`
  (`Alloc.main_partialTripleEnv`'s statement);
- `publishTF`, `allocTF`: the threads by `LowerThread.ofFrag` from the original
  threads' `LowerCore` fields (`publishC`, `allocC`, verbatim) and `main_fragL`;
  their start lemmas are the original proofs.
- `publish_promising_viaFragKit`, `alloc_promising_viaFragKit`: the original
  whole-program theorems re-derived; `example … := rfl` checks that the
  statements coincide with `Publish.publish_promising` and
  `Alloc.alloc_promising`. Neither proof mentions `Publish`/`Alloc`'s
  `main_partialTripleEnv`, `main_body`, `main_tail` or `publishT`/`allocT`.
-/
import Kraken.Promising.Lower.KitFrag
import Kraken.Promising.Lower.FragKitMain
import Kraken.Promising.Lower.PublishWhole
import Kraken.Promising.Lower.AllocWhole

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.Promising.Lower.Variant Kraken.Promising.Live.Bridge

namespace Kraken.Promising.Lower.FragKit

open Kraken.Promising.SLR.EnvG.Treiber2 Kraken.Promising.Lower.Kit
open Kraken.Promising.Lower.Pilot (pushFrag popFrag pushFrag_spec)
open Kraken.Promising.Lower.Alloc (allocFrag allocP)
open Kraken.Promising.Lower.Publish (publishP pushpFrag pushp_spec)

/-! ## `main`'s spec at the two texts (no proof beyond `decide`) -/

theorem publishMain_fragL (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d : BitVec 32)
    (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) :
    FragSpecEnvL (SharedEnv.counted (EW P w)) [mainFragG "pushp", allocFrag, popFrag, pushpFrag, pushFrag] "main"
      (MainPreF P w d) (MainPostF P w) :=
  main_fragL P w hL hw d hD (pushp_spec P w hL hw) (by decide) (by decide)

theorem allocMain_fragL (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d : BitVec 32)
    (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) :
    FragSpecEnvL (SharedEnv.counted (EW P w)) [mainFragG "push", allocFrag, popFrag, pushFrag] "main"
      (MainPreF P w d) (MainPostF P w) :=
  main_fragL P w hL hw d hD (pushFrag_spec P w hL hw).toL (by decide) (by decide)

/-! ## The texts' side conditions (closed, `decide`) -/

theorem publishP_wf' : Program.WF publishP := by decide
theorem publishP_ne : publishP.any (fun d => !d.isLabel) = true := by decide
theorem publishP_hs :
    [mainFragG "pushp", allocFrag, popFrag, pushpFrag, pushFrag].all (Program.subBlocksOfE · publishP) = true := by
  decide
theorem allocP_wf' : Program.WF allocP := by decide
theorem allocP_ne : allocP.any (fun d => !d.isLabel) = true := by decide
theorem allocP_hs : [mainFragG "push", allocFrag, popFrag, pushFrag].all (Program.subBlocksOfE · allocP) = true := by
  decide

/-! ## The kit's `main` field at every layout -/

/-- `Publish.main_partialTripleEnv`, from `publishMain_fragL`. -/
theorem publish_main_viaFragKit [layout : _root_.Layout] [Executable.ValidLayout (layout publishP)] (P : Params)
    (w : Nat) (hL : TLocs P) (hw : w < 2) (d : BitVec 32) (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) :
    @PartialTripleEnv ⟨layout publishP⟩ (SharedEnv.counted (EW P w)) (Publish.MainPre P w d) publishP
      (fun s σ => DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) (fun _ _ _ => False) :=
  partialTripleEnv_of_fragL (p := publishP) (publishMain_fragL P w hL hw d hD) publishP_wf' rfl publishP_ne publishP_hs
    (fun _ _ h => h) (fun _ _ _ _ _ h => h)

/-- `Alloc.main_partialTripleEnv`, from `allocMain_fragL`: the same `main`
proof at a second text. -/
theorem alloc_main_viaFragKit [layout : _root_.Layout] [Executable.ValidLayout (layout allocP)] (P : Params)
    (w : Nat) (hL : TLocs P) (hw : w < 2) (d : BitVec 32) (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) :
    @PartialTripleEnv ⟨layout allocP⟩ (SharedEnv.counted (EW P w)) (Alloc.MainPre P w d) allocP
      (fun s σ => DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) (fun _ _ _ => False) :=
  partialTripleEnv_of_fragL (p := allocP) (allocMain_fragL P w hL hw d hD) allocP_wf' rfl allocP_ne allocP_hs
    (fun _ _ h => h) (fun _ _ _ _ _ h => h)

example : @publish_main_viaFragKit = @Publish.main_partialTripleEnv := rfl
example : @alloc_main_viaFragKit = @Alloc.main_partialTripleEnv := rfl

/-! ## The threads, from a `LowerCore` and `main`'s fragment spec

The original `publishT`/`allocT` without their `main` field (so the threads
below do not mention `Publish.main_partialTripleEnv`/`Alloc.main_partialTripleEnv`
at all); `LowerThread.ofFrag` adds `main` from `main_fragL`. -/

/-- `publishT`'s `LowerCore` (fields verbatim). -/
noncomputable def publishC (l : _root_.Layout) [Executable.ValidLayout (l publishP)] (P : Params) (w : Nat)
    (hw : w < 2) (hd : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w + 8, 8⟩) v) :
    LowerCore Arch.armv8 w (ghost₀ P).rel (TB2D P) where
  l := l
  p := publishP
  valid := inferInstance
  pl := plan P w
  hpl := plan_valid P w
  live := Publish.publishP_rmwLive (layout := l)
  shape := Publish.publishP_phase1F (layout := l)
  stuck env := not_instrStepEnv_of_end_labels (layout := l) env 1
  Q s σ := DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1
  hB := Publish.hB_P (layout := l) P hw
  PreR s _ := Publish.MainPreR (layout := l) P.t (P.n w) s
  QR _ _ := True
  pure := Publish.main_pure (layout := l) _ P.t (P.n w) hd hn

/-- **`publishP` as a lowered thread, `main` by the fragment route.** -/
noncomputable def publishTF (l : _root_.Layout) [Executable.ValidLayout (l publishP)] (P : Params) (w : Nat)
    (hL : TLocs P) (hw : w < 2) (d : BitVec 32) (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v)
    (hd : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w + 8, 8⟩) v) :
    LowerThread Arch.armv8 w (ghost₀ P).rel (TB2D P) :=
  LowerThread.ofFrag (publishC l P w hw hd hn) (publishMain_fragL P w hL hw d hD) publishP_wf' rfl publishP_ne publishP_hs
    (Publish.MainPre (layout := l) P w d) (fun _ _ h => h) (fun _ _ _ _ _ h => h)

/-- `allocT`'s `LowerCore` (fields verbatim). -/
noncomputable def allocC (l : _root_.Layout) [Executable.ValidLayout (l allocP)] (P : Params) (w : Nat)
    (hw : w < 2) (hd : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w + 8, 8⟩) v) :
    LowerCore Arch.armv8 w (ghost₀ P).rel (TB2D P) where
  l := l
  p := allocP
  valid := inferInstance
  pl := plan P w
  hpl := plan_valid P w
  live := Alloc.allocP_rmwLive (layout := l)
  shape := Alloc.allocP_phase1F (layout := l)
  stuck env := not_instrStepEnv_of_end_labels (layout := l) env 1
  Q s σ := DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1
  hB := Alloc.hB_A (layout := l) P hw
  PreR s _ := Alloc.MainPreR (layout := l) P.t (P.n w) s
  QR _ _ := True
  pure := Alloc.main_pure (layout := l) _ P.t (P.n w) hd hn

/-- **`allocP` as a lowered thread, `main` by the same `main_fragL`.** -/
noncomputable def allocTF (l : _root_.Layout) [Executable.ValidLayout (l allocP)] (P : Params) (w : Nat)
    (hL : TLocs P) (hw : w < 2) (d : BitVec 32) (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v)
    (hd : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w + 8, 8⟩) v) :
    LowerThread Arch.armv8 w (ghost₀ P).rel (TB2D P) :=
  LowerThread.ofFrag (allocC l P w hw hd hn) (allocMain_fragL P w hL hw d hD) allocP_wf' rfl allocP_ne allocP_hs
    (Alloc.MainPre (layout := l) P w d) (fun _ _ h => h) (fun _ _ _ _ _ h => h)

/-- `Publish.publishT_start` for `publishTF` (same proof). -/
theorem publishTF_start (l : _root_.Layout) [Executable.ValidLayout (l publishP)] {P : Params} {w : Nat}
    (hL : TLocs P) (hw : w < 2) {d : BitVec 32} (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) {hd hn}
    {s : isa.State} (hS : Publish.StartP (layout := l) P.t (P.n w) d s) {c : Config isa}
    (hT0 : c.mem.initVal P.top = 0) :
    (publishTF l P w hL hw d hD hd hn).Start (σInit c (thrRes c.mem P w) (ghost₀ P)) s := by
  obtain ⟨he, hds, hend, hpc, h30, h21, h27, h28, h20, hd8, hd4⟩ := hS
  exact ⟨⟨he, hds, hend, hpc, 0, h30, h21, h27, h28, hd8, hd4⟩,
    0, h30, h21, h27, h28, h20, ⟨hd8, hd4⟩, pu0_init P hL hw _ hT0⟩

/-- `Alloc.allocT_start` for `allocTF` (same proof). -/
theorem allocTF_start (l : _root_.Layout) [Executable.ValidLayout (l allocP)] {P : Params} {w : Nat}
    (hL : TLocs P) (hw : w < 2) {d : BitVec 32} (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) {hd hn}
    {s : isa.State} (hS : Alloc.StartA (layout := l) P.t (P.n w) d s) {c : Config isa}
    (hT0 : c.mem.initVal P.top = 0) :
    (allocTF l P w hL hw d hD hd hn).Start (σInit c (thrRes c.mem P w) (ghost₀ P)) s := by
  obtain ⟨he, hds, hend, hpc, h30, h21, h27, h28, h20, hd8, hd4⟩ := hS
  exact ⟨⟨he, hds, hend, hpc, 0, h30, h21, h27, h28, hd8, hd4⟩,
    0, h30, h21, h27, h28, h20, ⟨hd8, hd4⟩, pu0_init P hL hw _ hT0⟩

/-! ## The whole programs -/

/-- `Publish.publish_promising`, the threads `publishTF` (`main` from the
fragment route). -/
theorem publish_promising_viaFragKit {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 publishP)]
    [Executable.ValidLayout (l1 publishP)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : Publish.StartP (layout := l0) t n0 1 s0) (h1 : Publish.StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  have hr : ∀ l, l ≠ (tPD t n0 n1).top → ∀ v, Pred.Pure ((ghost₀ (tPD t n0 n1)).rel l) v :=
    fun l hl v => by rw [ghost₀_rel_ne hl]; exact Pred.emp_pure v
  refine lower_promising Arch.armv8 fuel (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) rfl
    (fun tid h => match tid, h with
      | 0, _ => publishTF l0 _ 0 hL (by decide) 1 (fun _ h => h) (hr _ (top_dd _ 0).symm)
          (hr _ (hL.top_nd' (by decide)).symm)
      | 1, _ => publishTF l1 _ 1 hL (by decide) 2 (fun _ h => h) (hr _ (top_dd _ 1).symm)
          (hr _ (hL.top_nd' (by decide)).symm)
      | _ + 2, h => absurd h (by simp))
    (fun tid h => ?_) hc hf (KitPilot.treiber2DFinal_of_hB hL hf rfl)
  rcases tid with _ | _ | _
  · exact publishTF_start l0 (w := 0) hL (by decide) (fun _ h => h) (hd := hr _ (top_dd _ 0).symm)
      (hn := hr _ (hL.top_nd' (by decide)).symm) h0 hT0
  · exact publishTF_start l1 (w := 1) hL (by decide) (fun _ h => h) (hd := hr _ (top_dd _ 1).symm)
      (hn := hr _ (hL.top_nd' (by decide)).symm) h1 hT0
  · simp at h; omega

example : @publish_promising_viaFragKit = @Publish.publish_promising := rfl

/-- `Alloc.alloc_promising`, the threads `allocTF` (the same `main_fragL` as
`publish_promising_viaFragKit`). -/
theorem alloc_promising_viaFragKit {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 allocP)]
    [Executable.ValidLayout (l1 allocP)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : Alloc.StartA (layout := l0) t n0 1 s0) (h1 : Alloc.StartA (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  have hr : ∀ l, l ≠ (tPD t n0 n1).top → ∀ v, Pred.Pure ((ghost₀ (tPD t n0 n1)).rel l) v :=
    fun l hl v => by rw [ghost₀_rel_ne hl]; exact Pred.emp_pure v
  refine lower_promising Arch.armv8 fuel (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) rfl
    (fun tid h => match tid, h with
      | 0, _ => allocTF l0 _ 0 hL (by decide) 1 (fun _ h => h) (hr _ (top_dd _ 0).symm)
          (hr _ (hL.top_nd' (by decide)).symm)
      | 1, _ => allocTF l1 _ 1 hL (by decide) 2 (fun _ h => h) (hr _ (top_dd _ 1).symm)
          (hr _ (hL.top_nd' (by decide)).symm)
      | _ + 2, h => absurd h (by simp))
    (fun tid h => ?_) hc hf (KitPilot.treiber2DFinal_of_hB hL hf rfl)
  rcases tid with _ | _ | _
  · exact allocTF_start l0 (w := 0) hL (by decide) (fun _ h => h) (hd := hr _ (top_dd _ 0).symm)
      (hn := hr _ (hL.top_nd' (by decide)).symm) h0 hT0
  · exact allocTF_start l1 (w := 1) hL (by decide) (fun _ h => h) (hd := hr _ (top_dd _ 1).symm)
      (hn := hr _ (hL.top_nd' (by decide)).symm) h1 hT0
  · simp at h; omega

example : @alloc_promising_viaFragKit = @Alloc.alloc_promising := rfl

end Kraken.Promising.Lower.FragKit

#print axioms Kraken.Promising.Lower.FragKit.publish_promising_viaFragKit
#print axioms Kraken.Promising.Lower.FragKit.alloc_promising_viaFragKit
