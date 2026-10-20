/-
**`alloc_promising` on `isaLSE2`, through the kit.**
ISA: AArch64 with FEAT_LSE2 (`isaLSE2`); `Arch.armv8`.

The WeakCore lowering target is `isaLSE2`. The allocation pilot's `alloc_promising`
(`Lower/AllocWhole.lean`) is proved by `Kit.lower_promising` on the
executable machine of `isa`. Here the same threads (`allocT`), the same start
discharge (`allocT_start`) and the same final reading
(`KitPilot.treiber2DFinal_of_hB`) are fed to `Kit.lower_promising_lse2` and
its `_sem`/`_semInf` forms (`Lower/KitLSE2.lean`), with

- `hH` along `ReachableK` (`Config.ntFree_armv8K`),
- `hfree` from `allocP_lse2Free` (no 64-bit `LDP`/`STP` in `allocP`, by
  `decide`),
- the final reading for every final configuration.

No `#chaink_clone'`: this is the clone-free pattern of `Lower/KitMsqLSE2.lean`.
The hypotheses are `alloc_promising`'s, verbatim; the conclusion is read in
`Config isa` through `ofL` (a field-by-field copy; it changes no data).

`pilot_promising_lse2_viaKit` is the same for the first lowering pilot's kit instance
(`KitPilot.pilot_promising_viaKit`); its statement is the calls layer's
`Pilot.pilot_promising_lse2` (`Lower/PilotLSE2.lean`, by the clone route),
verbatim (checked below by `rfl`).
-/
import Kraken.Promising.Lower.AllocWhole
import Kraken.Promising.Lower.KitLSE2
import Kraken.Promising.Lower.PilotLSE2

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.Promising.Lower.Variant Kraken.Promising.Live.Bridge

namespace Kraken.Promising.Lower.Alloc

open Kraken.Promising.SLR.EnvG.Treiber2 Kraken.Promising.Lower.Kit

/-- **`allocP` has no LSE2 pair** (no 64-bit `LDP`/`STP`). -/
theorem allocP_lse2Free : ∀ d ∈ allocP, d.LSE2Free := by decide

/-- The lowered threads of `alloc_promising`, at layouts `l0`, `l1`. -/
noncomputable abbrev allocTs (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 allocP)]
    [Executable.ValidLayout (l1 allocP)] (t n0 n1 : BitVec 64) (hL : TLocs (tPD t n0 n1))
    {s0 s1 : isa.State} : ∀ tid, tid < [s0, s1].length → LowerThread Arch.armv8 tid (ghost₀ (tPD t n0 n1)).rel
      (TB2D (tPD t n0 n1)) :=
  have hr : ∀ l, l ≠ (tPD t n0 n1).top → ∀ v, Pred.Pure ((ghost₀ (tPD t n0 n1)).rel l) v :=
    fun l hl v => by rw [ghost₀_rel_ne hl]; exact Pred.emp_pure v
  fun tid h => match tid, h with
    | 0, _ => allocT l0 _ 0 hL (by decide) 1 (fun _ h => h) (hr _ (top_dd _ 0).symm)
      (hr _ (hL.top_nd' (by decide)).symm)
    | 1, _ => allocT l1 _ 1 hL (by decide) 2 (fun _ h => h) (hr _ (top_dd _ 1).symm)
      (hr _ (hL.top_nd' (by decide)).symm)
    | _ + 2, h => absurd h (by simp)

theorem allocTs_start (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 allocP)]
    [Executable.ValidLayout (l1 allocP)] {t n0 n1 : BitVec 64} (hL : TLocs (tPD t n0 n1))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartA (layout := l0) t n0 1 s0) (h1 : StartA (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid (h : tid < [s0, s1].length), (allocTs l0 l1 t n0 n1 hL tid h).Start
      (σInit (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem (tPD t n0 n1) tid)
        (ghost₀ (tPD t n0 n1))) [s0, s1][tid] := by
  intro tid h
  rcases tid with _ | _ | _
  · exact allocT_start l0 (w := 0) hL (by decide) _ h0 hT0
  · exact allocT_start l1 (w := 1) hL (by decide) _ h1 hT0
  · simp at h; omega

theorem allocTs_free (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 allocP)]
    [Executable.ValidLayout (l1 allocP)] {t n0 n1 : BitVec 64} (hL : TLocs (tPD t n0 n1))
    {s0 s1 : isa.State} :
    ∀ tid (h : tid < [s0, s1].length), ∀ d ∈ (allocTs l0 l1 t n0 n1 hL (s0 := s0) (s1 := s1) tid h).p,
      d.LSE2Free := by
  intro tid h
  rcases tid with _ | _ | _
  · exact allocP_lse2Free
  · exact allocP_lse2Free
  · simp at h; omega

/-- **The allocating Treiber client on `isaLSE2`** (AArch64 with FEAT_LSE2,
`Arch.armv8`, executable machine): for the hypotheses of `alloc_promising`,
every final configuration of `isaLSE2` reachable from the two start states
satisfies `Treiber2DFinal n0 n1` (read in `Config isa` through `ofL`). -/
theorem alloc_promising_lse2 {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 allocP)]
    [Executable.ValidLayout (l1 allocP)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartA (layout := l0) t n0 1 s0) (h1 : StartA (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isaLSE2} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) :=
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  lower_promising_lse2 Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init hL _) rfl
    (allocTs l0 l1 t n0 n1 hL) (allocTs_start l0 l1 hL h0 h1 hT0) (allocTs_free l0 l1 hL)
    (fun _ hf' => KitPilot.treiber2DFinal_of_hB hL hf' rfl) hc hf

/-- **`alloc_promising_lse2`, semantic machine** (`ReachableSem`). -/
theorem alloc_promising_lse2_sem {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 allocP)]
    [Executable.ValidLayout (l1 allocP)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartA (layout := l0) t n0 1 s0) (h1 : StartA (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isaLSE2}
    (hc : ReachableSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) :=
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  lower_promising_lse2_sem Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init hL _) rfl
    (allocTs l0 l1 t n0 n1 hL) (allocTs_start l0 l1 hL h0 h1 hT0) (allocTs_free l0 l1 hL)
    (fun _ hf' => KitPilot.treiber2DFinal_of_hB hL hf' rfl) hc hf

/-- **`alloc_promising_lse2`, fuel-free semantic machine**
(`ReachableSemInf`), the form the lowering consumes. -/
theorem alloc_promising_lse2_semInf (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 allocP)]
    [Executable.ValidLayout (l1 allocP)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartA (layout := l0) t n0 1 s0) (h1 : StartA (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf Arch.armv8 (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) :=
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  lower_promising_lse2_semInf Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init hL _) rfl
    (allocTs l0 l1 t n0 n1 hL) (allocTs_start l0 l1 hL h0 h1 hT0) (allocTs_free l0 l1 hL)
    (fun _ hf' => KitPilot.treiber2DFinal_of_hB hL hf' rfl) hc hf

/-- **Non-vacuity**: `alloc_promising_lse2` at the explorer's configuration
(`AllocProg`: `top` at `0x1000`, garbage arenas at `0x2000`/`0x3000`,
payloads `1`, `2`). No hypothesis beyond reachability and finality. -/
theorem alloc_promising_lse2_concrete {fuel : Nat} {c : Config isaLSE2}
    (hc : Reachable Arch.armv8 fuel (Config.init [thread 0x2000 1, thread 0x3000 2] initMem : Config isaLSE2) c)
    (hf : c.final = true) : Treiber2DFinal 0x2000 0x3000 (ofL c) :=
  alloc_promising_lse2 aLayout aLayout 0x1000 0x2000 0x3000 (by decide) (by decide) (by decide) (by decide)
    (by decide) (thread_start _ _ _ _ rfl (by decide) (by decide))
    (thread_start _ _ _ _ rfl (by decide) (by decide)) (by simp only [Config.init_mem]; decide) hc hf

end Kraken.Promising.Lower.Alloc

namespace Kraken.Promising.Lower.KitPilot

open Kraken.Promising.SLR.EnvG.Treiber2 Kraken.Promising.Lower.Kit Kraken.Promising.Lower.Pilot

/-- **`pilot_promising` on `isaLSE2` through the kit** (executable machine;
same statement as `Pilot.pilot_promising_lse2`). -/
theorem pilot_promising_lse2_viaKit {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 pilot)]
    [Executable.ValidLayout (l1 pilot)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isaLSE2} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  have hr : ∀ l, l ≠ (tPD t n0 n1).top → ∀ v, Pred.Pure ((ghost₀ (tPD t n0 n1)).rel l) v :=
    fun l hl v => by rw [ghost₀_rel_ne hl]; exact Pred.emp_pure v
  refine lower_promising_lse2 Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init hL _) rfl
    (fun tid h => match tid, h with
      | 0, _ => pilotT l0 _ 0 hL (by decide) 1 (fun _ h => h) (hr _ (top_dd _ 0).symm) (hr _ (hL.top_nd' (by decide)).symm)
      | 1, _ => pilotT l1 _ 1 hL (by decide) 2 (fun _ h => h) (hr _ (top_dd _ 1).symm) (hr _ (hL.top_nd' (by decide)).symm)
      | _ + 2, h => absurd h (by simp))
    (fun tid h => ?_) (fun tid h => ?_) (fun _ hf' => treiber2DFinal_of_hB hL hf' rfl) hc hf
  · rcases tid with _ | _ | _
    · exact pilotT_start l0 (w := 0) hL (by decide) _ h0 hT0
    · exact pilotT_start l1 (w := 1) hL (by decide) _ h1 hT0
    · simp at h; omega
  · rcases tid with _ | _ | _
    · exact pilot_lse2Free
    · exact pilot_lse2Free
    · simp at h; omega

/-- The statement is `Pilot.pilot_promising_lse2`'s, verbatim. -/
example : @pilot_promising_lse2_viaKit = @Pilot.pilot_promising_lse2 := rfl

end Kraken.Promising.Lower.KitPilot

#print axioms Kraken.Promising.Lower.Alloc.alloc_promising_lse2
#print axioms Kraken.Promising.Lower.Alloc.alloc_promising_lse2_sem
#print axioms Kraken.Promising.Lower.Alloc.alloc_promising_lse2_semInf
#print axioms Kraken.Promising.Lower.Alloc.alloc_promising_lse2_concrete
#print axioms Kraken.Promising.Lower.KitPilot.pilot_promising_lse2_viaKit
