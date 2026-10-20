/-
**The publish pilot and the allocation pilot with both `main` and
`pure` from the fragment route.** ISA: AArch64 (`isa`);
`Arch.armv8`; the executable machine (`Reachable`).

The fragment kit (`Lower/FragKitPublish.lean`) took the kit's `main` field from one
spec (`FragKit.main_fragL`) but copied the original `LowerCore`s verbatim, so
its threads still used the per-text purity proofs `Publish.main_pure` and
`Alloc.main_pure`. Here the `pure` field also comes from one spec,
`FragKit.main_pure_fragL` (`Lower/FragKitPure.lean`), through
`Kit.LowerStatic.ofFragPure`:

- `publishPure_fragL` (frags as `publishMain_fragL`, push entry by
  `Publish.pushp_pure`) and `allocPure_fragL` (frags as `allocMain_fragL`,
  `(Pilot.pushFrag_pure …).toL`): one line each, plus `decide`.
- `publishS`, `allocS`: the original threads' static fields (verbatim);
  `publishTF2`, `allocTF2`: `LowerThread.ofFrag` of `LowerStatic.ofFragPure`,
  with the original `PreR`/`QR` (the original `MainPreR` is `MainPreRF` at the
  end of the text, definitionally) and the original `Pre`; the start lemmas are
  the original proofs.
- `publish_promising_viaFragKit2`, `alloc_promising_viaFragKit2`: the original
  whole-program theorems re-derived; `example … := rfl` checks that the
  statements coincide with `Publish.publish_promising` and
  `Alloc.alloc_promising`. Neither proof mentions a per-text `main` or
  `pure` proof (`Publish`/`Alloc` `.main_partialTripleEnv`, `.main_pure`,
  their block lemmas, `publishT`/`allocT`, the fragment kit's `publishC`/`allocC`).
-/
import Kraken.Promising.Lower.FragKitPure
import Kraken.Promising.Lower.FragKitPublish

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.Promising.Lower.Variant Kraken.Promising.Live.Bridge

namespace Kraken.Promising.Lower.FragKit

open Kraken.Promising.SLR.EnvG.Treiber2 Kraken.Promising.Lower.Kit
open Kraken.Promising.Lower.Pilot (RP pushFrag popFrag pushFrag_pure)
open Kraken.Promising.Lower.Alloc (allocFrag allocP)
open Kraken.Promising.Lower.Publish (publishP pushpFrag pushp_pure)

/-! ## `main`'s purity at the two texts (no proof beyond `decide`) -/

theorem publishPure_fragL (rel : Loc → Pred) (t n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FragSpecEnvL (RP rel) [mainFragG "pushp", allocFrag, popFrag, pushpFrag, pushFrag] "main" (MainPreRF rel t n)
      (fun _ _ _ _ _ => True) :=
  main_pure_fragL rel t n hd hn (pushp_pure rel t n hn) (by decide) (by decide)

theorem allocPure_fragL (rel : Loc → Pred) (t n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FragSpecEnvL (RP rel) [mainFragG "push", allocFrag, popFrag, pushFrag] "main" (MainPreRF rel t n)
      (fun _ _ _ _ _ => True) :=
  main_pure_fragL rel t n hd hn (pushFrag_pure rel t n hn).toL (by decide) (by decide)

/-! ## The threads: static fields, `pure` and `main` from fragment specs -/

/-- `publishT`'s static fields (verbatim). -/
noncomputable def publishS (l : _root_.Layout) [Executable.ValidLayout (l publishP)] (P : Params) (w : Nat)
    (hw : w < 2) : LowerStatic Arch.armv8 w (TB2D P) where
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

/-- `allocT`'s static fields (verbatim). -/
noncomputable def allocS (l : _root_.Layout) [Executable.ValidLayout (l allocP)] (P : Params) (w : Nat)
    (hw : w < 2) : LowerStatic Arch.armv8 w (TB2D P) where
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

/-- **`publishP` as a lowered thread, `main` and `pure` by the fragment route.** -/
noncomputable def publishTF2 (l : _root_.Layout) [Executable.ValidLayout (l publishP)] (P : Params) (w : Nat)
    (hL : TLocs P) (hw : w < 2) (d : BitVec 32) (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v)
    (hd : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w + 8, 8⟩) v) :
    LowerThread Arch.armv8 w (ghost₀ P).rel (TB2D P) :=
  LowerThread.ofFrag
    ((publishS l P w hw).ofFragPure _ (publishPure_fragL _ P.t (P.n w) hd hn) publishP_wf' rfl publishP_ne
      publishP_hs (fun s _ => Publish.MainPreR (layout := l) P.t (P.n w) s) (fun _ _ => True) (fun _ _ h => h)
      (fun _ _ _ _ _ _ => trivial))
    (publishMain_fragL P w hL hw d hD) publishP_wf' rfl publishP_ne publishP_hs
    (Publish.MainPre (layout := l) P w d) (fun _ _ h => h) (fun _ _ _ _ _ h => h)

/-- **`allocP` as a lowered thread, `main` and `pure` by the same specs.** -/
noncomputable def allocTF2 (l : _root_.Layout) [Executable.ValidLayout (l allocP)] (P : Params) (w : Nat)
    (hL : TLocs P) (hw : w < 2) (d : BitVec 32) (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v)
    (hd : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w + 8, 8⟩) v) :
    LowerThread Arch.armv8 w (ghost₀ P).rel (TB2D P) :=
  LowerThread.ofFrag
    ((allocS l P w hw).ofFragPure _ (allocPure_fragL _ P.t (P.n w) hd hn) allocP_wf' rfl allocP_ne allocP_hs
      (fun s _ => Alloc.MainPreR (layout := l) P.t (P.n w) s) (fun _ _ => True) (fun _ _ h => h)
      (fun _ _ _ _ _ _ => trivial))
    (allocMain_fragL P w hL hw d hD) allocP_wf' rfl allocP_ne allocP_hs
    (Alloc.MainPre (layout := l) P w d) (fun _ _ h => h) (fun _ _ _ _ _ h => h)

/-- `Publish.publishT_start` for `publishTF2` (same proof). -/
theorem publishTF2_start (l : _root_.Layout) [Executable.ValidLayout (l publishP)] {P : Params} {w : Nat}
    (hL : TLocs P) (hw : w < 2) {d : BitVec 32} (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) {hd hn}
    {s : isa.State} (hS : Publish.StartP (layout := l) P.t (P.n w) d s) {c : Config isa}
    (hT0 : c.mem.initVal P.top = 0) :
    (publishTF2 l P w hL hw d hD hd hn).Start (σInit c (thrRes c.mem P w) (ghost₀ P)) s := by
  obtain ⟨he, hds, hend, hpc, h30, h21, h27, h28, h20, hd8, hd4⟩ := hS
  exact ⟨⟨he, hds, hend, hpc, 0, h30, h21, h27, h28, hd8, hd4⟩,
    0, h30, h21, h27, h28, h20, ⟨hd8, hd4⟩, pu0_init P hL hw _ hT0⟩

/-- `Alloc.allocT_start` for `allocTF2` (same proof). -/
theorem allocTF2_start (l : _root_.Layout) [Executable.ValidLayout (l allocP)] {P : Params} {w : Nat}
    (hL : TLocs P) (hw : w < 2) {d : BitVec 32} (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) {hd hn}
    {s : isa.State} (hS : Alloc.StartA (layout := l) P.t (P.n w) d s) {c : Config isa}
    (hT0 : c.mem.initVal P.top = 0) :
    (allocTF2 l P w hL hw d hD hd hn).Start (σInit c (thrRes c.mem P w) (ghost₀ P)) s := by
  obtain ⟨he, hds, hend, hpc, h30, h21, h27, h28, h20, hd8, hd4⟩ := hS
  exact ⟨⟨he, hds, hend, hpc, 0, h30, h21, h27, h28, hd8, hd4⟩,
    0, h30, h21, h27, h28, h20, ⟨hd8, hd4⟩, pu0_init P hL hw _ hT0⟩

/-! ## The whole programs -/

/-- `Publish.publish_promising`, the threads `publishTF2` (`main` and `pure`
from the fragment route). -/
theorem publish_promising_viaFragKit2 {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 publishP)]
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
      | 0, _ => publishTF2 l0 _ 0 hL (by decide) 1 (fun _ h => h) (hr _ (top_dd _ 0).symm)
          (hr _ (hL.top_nd' (by decide)).symm)
      | 1, _ => publishTF2 l1 _ 1 hL (by decide) 2 (fun _ h => h) (hr _ (top_dd _ 1).symm)
          (hr _ (hL.top_nd' (by decide)).symm)
      | _ + 2, h => absurd h (by simp))
    (fun tid h => ?_) hc hf (KitPilot.treiber2DFinal_of_hB hL hf rfl)
  rcases tid with _ | _ | _
  · exact publishTF2_start l0 (w := 0) hL (by decide) (fun _ h => h) (hd := hr _ (top_dd _ 0).symm)
      (hn := hr _ (hL.top_nd' (by decide)).symm) h0 hT0
  · exact publishTF2_start l1 (w := 1) hL (by decide) (fun _ h => h) (hd := hr _ (top_dd _ 1).symm)
      (hn := hr _ (hL.top_nd' (by decide)).symm) h1 hT0
  · simp at h; omega

example : @publish_promising_viaFragKit2 = @Publish.publish_promising := rfl

/-- `Alloc.alloc_promising`, the threads `allocTF2` (the same
`main_fragL` and `main_pure_fragL` as `publish_promising_viaFragKit2`). -/
theorem alloc_promising_viaFragKit2 {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 allocP)]
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
      | 0, _ => allocTF2 l0 _ 0 hL (by decide) 1 (fun _ h => h) (hr _ (top_dd _ 0).symm)
          (hr _ (hL.top_nd' (by decide)).symm)
      | 1, _ => allocTF2 l1 _ 1 hL (by decide) 2 (fun _ h => h) (hr _ (top_dd _ 1).symm)
          (hr _ (hL.top_nd' (by decide)).symm)
      | _ + 2, h => absurd h (by simp))
    (fun tid h => ?_) hc hf (KitPilot.treiber2DFinal_of_hB hL hf rfl)
  rcases tid with _ | _ | _
  · exact allocTF2_start l0 (w := 0) hL (by decide) (fun _ h => h) (hd := hr _ (top_dd _ 0).symm)
      (hn := hr _ (hL.top_nd' (by decide)).symm) h0 hT0
  · exact allocTF2_start l1 (w := 1) hL (by decide) (fun _ h => h) (hd := hr _ (top_dd _ 1).symm)
      (hn := hr _ (hL.top_nd' (by decide)).symm) h1 hT0
  · simp at h; omega

example : @alloc_promising_viaFragKit2 = @Alloc.alloc_promising := rfl

end Kraken.Promising.Lower.FragKit

#print axioms Kraken.Promising.Lower.FragKit.publish_promising_viaFragKit2
#print axioms Kraken.Promising.Lower.FragKit.alloc_promising_viaFragKit2
