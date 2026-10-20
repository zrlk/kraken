/-
**The allocating MS queue pilot on the semantic machines.** ISA: AArch64 with
FEAT_LSE2 (`isaLSE2`, the WeakCore lowering
target); `Arch.armv8`.

`MsqAlloc.msqAlloc_promising_lse2` (`Lower/MsqAllocWhole.lean`) is on the
executable machine (`Reachable`). Here, as the allocation pilot's `Lower/AllocLSE2.lean`:

- `msqAlloc_promising_lse2_sem`: the semantic machine (`ReachableSem`);
- `msqAlloc_promising_lse2_semInf`: the fuel-free semantic machine
  (`Live.Inf.ReachableSemInf`), the form the lowering consumes;

both by `Kit.lower_promising_lse2_sem` / `_semInf` with the same threads
(`msqAllocTs`), start discharge (`msqAllocTs_start`), `hfree` (`msqA_lse2Free`,
`MsqPilot.progD_wcLowerable.lse2Free`) and final reading
(`msqueue2_final_of_hB`). Hypotheses and conclusion are
`msqAlloc_promising_lse2`'s, verbatim, with only the machine changed.
`Kit.lower_promising` (on `isa`) has no `_sem`/`_semInf` form, so there are no
`isa` semantic-machine forms.
-/
import Kraken.Promising.Lower.MsqAllocWhole

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.Promising.Lower.Variant Kraken.Promising.Live.Bridge

namespace Kraken.Promising.Lower.MsqAlloc

open Kraken.Promising.SLR.EnvG.MsQueue Kraken.Promising.Lower.Kit
open Kraken.Promising.Lower.MsqPilot (StartD progD)

theorem msqAllocTs_free (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 msqA)]
    [Executable.ValidLayout (l1 progD)] {h t d base : BitVec 64} (hL : QLocs2 (pA h t d base)) (ht : t = h + 8)
    {s0 s1 : isa.State} :
    ∀ tid (hh : tid < [s0, s1].length), ∀ x ∈ (msqAllocTs l0 l1 h t d base hL ht tid hh).p, x.LSE2Free := by
  intro tid hh
  rcases tid with _ | _ | _
  · exact msqA_lse2Free
  · exact MsqPilot.progD_wcLowerable.lse2Free
  · simp at hh; omega

/-- **`msqAlloc_promising_lse2`, semantic machine** (`ReachableSem` of
`isaLSE2`, `Arch.armv8`): same hypotheses and conclusion. -/
theorem msqAlloc_promising_lse2_sem {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 msqA)]
    [Executable.ValidLayout (l1 progD)] (h t d base : BitVec 64) (ht : t = h + 8) (hht : h ≠ t)
    (hhd : h ≠ d + 8) (htd : t ≠ d + 8) (hb1 : h ≠ base + 8) (hb2 : h ≠ base + 16 + 8) (tb1 : t ≠ base + 8)
    (tb2 : t ≠ base + 16 + 8) (db1 : d ≠ base) (db2 : d ≠ base + 16) (hb0 : base ≠ 0) (hb16 : base + 16 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartA (layout := l0) h base s0)
    (h1 : StartD (layout := l1) h s1)
    (hhead : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨h, 8⟩) = d)
    (htail : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩) = d)
    (hdl : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨d + 8, 8⟩) = 0)
    (hl1 : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨base + 8, 8⟩) = 0)
    (hl2 : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨base + 16 + 8, 8⟩) = 0)
    {cfg : Config isaLSE2}
    (hc : ReachableSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : MsQueue2Final (ofL cfg) :=
  have hL := qLocsA hht hhd htd hb1 hb2 tb1 tb2 db1 db2 hb0 hb16
  lower_promising_lse2_sem Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init2 hL _) rfl
    (msqAllocTs l0 l1 h t d base hL ht) (msqAllocTs_start l0 l1 hL ht h0 h1 ⟨⟨hhead, htail, hdl, hl1⟩, hl2⟩)
    (msqAllocTs_free l0 l1 hL ht)
    (fun _ hf' _ _ E' hle hsize hB => msqueue2_final_of_hB hL hf' E' hle hsize hB) hc hf

/-- **`msqAlloc_promising_lse2`, fuel-free semantic machine**
(`Live.Inf.ReachableSemInf` of `isaLSE2`, `Arch.armv8`), the form the lowering
consumes: same hypotheses and conclusion. -/
theorem msqAlloc_promising_lse2_semInf (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 msqA)]
    [Executable.ValidLayout (l1 progD)] (h t d base : BitVec 64) (ht : t = h + 8) (hht : h ≠ t)
    (hhd : h ≠ d + 8) (htd : t ≠ d + 8) (hb1 : h ≠ base + 8) (hb2 : h ≠ base + 16 + 8) (tb1 : t ≠ base + 8)
    (tb2 : t ≠ base + 16 + 8) (db1 : d ≠ base) (db2 : d ≠ base + 16) (hb0 : base ≠ 0) (hb16 : base + 16 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartA (layout := l0) h base s0)
    (h1 : StartD (layout := l1) h s1)
    (hhead : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨h, 8⟩) = d)
    (htail : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩) = d)
    (hdl : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨d + 8, 8⟩) = 0)
    (hl1 : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨base + 8, 8⟩) = 0)
    (hl2 : BitVec.setWidth 64 ((Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨base + 16 + 8, 8⟩) = 0)
    {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf Arch.armv8 (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : MsQueue2Final (ofL cfg) :=
  have hL := qLocsA hht hhd htd hb1 hb2 tb1 tb2 db1 db2 hb0 hb16
  lower_promising_lse2_semInf Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init2 hL _) rfl
    (msqAllocTs l0 l1 h t d base hL ht) (msqAllocTs_start l0 l1 hL ht h0 h1 ⟨⟨hhead, htail, hdl, hl1⟩, hl2⟩)
    (msqAllocTs_free l0 l1 hL ht)
    (fun _ hf' _ _ E' hle hsize hB => msqueue2_final_of_hB hL hf' E' hle hsize hB) hc hf

end Kraken.Promising.Lower.MsqAlloc

#print axioms Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2_sem
#print axioms Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2_semInf
