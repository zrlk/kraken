/-
**The publish pilot on the semantic machines, and its concrete
instances.** ISA: AArch64 (`isa` for
`publish_promising_concrete`; `isaLSE2`, the WeakCore lowering target, for the
rest); `Arch.armv8`.

`Publish.publish_promising_lse2` (`Lower/PublishWhole.lean`) is on the
executable machine (`Reachable`). Here, as the allocation pilot's `Lower/AllocLSE2.lean`:

- `publish_promising_lse2_sem`: the semantic machine (`ReachableSem`);
- `publish_promising_lse2_semInf`: the fuel-free semantic machine
  (`Live.Inf.ReachableSemInf`), the form the lowering consumes;

both by `Kit.lower_promising_lse2_sem` / `_semInf` with the same threads
(`publishTs`), start discharge (`publishTs_start`), `hfree`
(`publishP_lse2Free`) and final reading (`KitPilot.treiber2DFinal_of_hB`).
Hypotheses and conclusion are `publish_promising_lse2`'s, verbatim, with only
the machine changed. `Kit.lower_promising` (on `isa`) has no `_sem`/`_semInf`
form, so there are no `isa` semantic-machine forms.

**Non-vacuity.** `PublishProg.lean` has no explorer configuration, so this file
mirrors `AllocProg`'s: `threadP base v` is `Alloc.thread base v` at `publishP`
(text at `0x100000` with each directive its `fakeSize`, `pLayout`; `x21 = &top
= 0x1000`, arena `[base, base + 0x100)`, payload `x20 = v`), and the initial
memory is `Alloc.initMem` itself (`top = 0`, garbage `7` in both arenas).
`publish_promising_concrete` (`isa`) and `publish_promising_lse2_concrete`
(`isaLSE2`), both on the executable machine, assume only reachability and
finality. No explorer run is recorded for `publishP`.
-/
import Kraken.Promising.Lower.PublishWhole
import Kraken.Promising.Lower.AllocWhole
import Kraken.AArch64.WP.LayoutOfSize

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.Promising.Lower.Variant Kraken.Promising.Live.Bridge

namespace Kraken.Promising.Lower.Publish

open Kraken.Promising.SLR.EnvG.Treiber2 Kraken.Promising.Lower.Kit

theorem publishTs_free (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 publishP)]
    [Executable.ValidLayout (l1 publishP)] {t n0 n1 : BitVec 64} (hL : TLocs (tPD t n0 n1))
    {s0 s1 : isa.State} :
    ∀ tid (h : tid < [s0, s1].length), ∀ d ∈ (publishTs l0 l1 t n0 n1 hL (s0 := s0) (s1 := s1) tid h).p,
      d.LSE2Free := by
  intro tid h
  rcases tid with _ | _ | _
  · exact publishP_lse2Free
  · exact publishP_lse2Free
  · simp at h; omega

/-- **`publish_promising_lse2`, semantic machine** (`ReachableSem` of
`isaLSE2`, `Arch.armv8`): same hypotheses and conclusion. -/
theorem publish_promising_lse2_sem {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 publishP)]
    [Executable.ValidLayout (l1 publishP)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isaLSE2}
    (hc : ReachableSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) :=
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  lower_promising_lse2_sem Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init hL _) rfl
    (publishTs l0 l1 t n0 n1 hL) (publishTs_start l0 l1 hL h0 h1 hT0) (publishTs_free l0 l1 hL)
    (fun _ hf' => KitPilot.treiber2DFinal_of_hB hL hf' rfl) hc hf

/-- **`publish_promising_lse2`, fuel-free semantic machine**
(`Live.Inf.ReachableSemInf` of `isaLSE2`, `Arch.armv8`), the form the lowering
consumes: same hypotheses and conclusion. -/
theorem publish_promising_lse2_semInf (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 publishP)]
    [Executable.ValidLayout (l1 publishP)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf Arch.armv8 (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) :=
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  lower_promising_lse2_semInf Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init hL _) rfl
    (publishTs l0 l1 t n0 n1 hL) (publishTs_start l0 l1 hL h0 h1 hT0) (publishTs_free l0 l1 hL)
    (fun _ hf' => KitPilot.treiber2DFinal_of_hB hL hf' rfl) hc hf

/-! ## The concrete instance (`AllocProg`'s configuration at `publishP`) -/

/-- Text at `0x100000`, each directive its `fakeSize` (`Alloc.aLayout` at
`publishP`). -/
@[reducible] def pLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize publishP

instance pValid : Executable.ValidLayout (pLayout publishP) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The end address: `38` instructions of `4` bytes (`Alloc.endA` plus
`dmb ishst` and `b push`). -/
def endP : Int64 := 0x100000 + 152

/-- Thread start (`Alloc.thread` at `publishP`): `x21 = &top`, arena
`[x27, x28)`, payload `x20 = v`. -/
def threadP (base v : UInt64) : AArch64.State where
  exe := pLayout publishP
  endPc := endP
  st := ({ regs := { X21 := 0x1000, X27 := base, X28 := base + 0x100, X20 := v, X30 := 0x100000 + 152 } },
    0x100000)

section
attribute [local instance] pLayout

theorem threadP_start (base v : UInt64) (n : BitVec 64) (d : BitVec 32) (hn : base.toBitVec = n)
    (hlim : base.toBitVec + 16 ≤ (base + 0x100).toBitVec) (hd : v.toBitVec.setWidth 32 = d) :
    StartP (layout := pLayout) 0x1000 n d (threadP base v) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, hn, hlim, hd, ?_, ?_⟩ <;> try (simp only [threadP]; decide)
  all_goals simp [threadP, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **Non-vacuity**: `publish_promising` (`isa`, executable machine) at
`AllocProg`'s configuration moved to `publishP`: `top` at `0x1000`, arenas at
`0x2000`/`0x3000` holding garbage (`7`, `Alloc.initMem`), payloads `1`, `2`.
No hypothesis beyond reachability and finality. -/
theorem publish_promising_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [threadP 0x2000 1, threadP 0x3000 2] Alloc.initMem) c)
    (hf : c.final = true) : Treiber2DFinal 0x2000 0x3000 c :=
  publish_promising pLayout pLayout 0x1000 0x2000 0x3000 (by decide) (by decide) (by decide) (by decide)
    (by decide) (threadP_start _ _ _ _ rfl (by decide) (by decide))
    (threadP_start _ _ _ _ rfl (by decide) (by decide)) (by simp only [Config.init_mem]; decide) hc hf

/-- **Non-vacuity on `isaLSE2`**: `publish_promising_lse2` (executable
machine) at the same configuration. -/
theorem publish_promising_lse2_concrete {fuel : Nat} {c : Config isaLSE2}
    (hc : Reachable Arch.armv8 fuel
      (Config.init [threadP 0x2000 1, threadP 0x3000 2] Alloc.initMem : Config isaLSE2) c)
    (hf : c.final = true) : Treiber2DFinal 0x2000 0x3000 (ofL c) :=
  publish_promising_lse2 pLayout pLayout 0x1000 0x2000 0x3000 (by decide) (by decide) (by decide)
    (by decide) (by decide) (threadP_start _ _ _ _ rfl (by decide) (by decide))
    (threadP_start _ _ _ _ rfl (by decide) (by decide)) (by simp only [Config.init_mem]; decide) hc hf

end Kraken.Promising.Lower.Publish

#print axioms Kraken.Promising.Lower.Publish.publish_promising_lse2_sem
#print axioms Kraken.Promising.Lower.Publish.publish_promising_lse2_semInf
#print axioms Kraken.Promising.Lower.Publish.publish_promising_concrete
#print axioms Kraken.Promising.Lower.Publish.publish_promising_lse2_concrete
