/-
**The x64 pilots on the semantic machines.**
ISA: x64 (`isa`); `Arch.tso`.

The three x64 whole-program pilots are on the executable machine
(`Reachable Arch.tso fuel`): `PilotXR.pilotXR_promising`
(`Lower/PilotXRWhole.lean`), `MsqXR.msqXR_promising` (`Lower/MsqXRWhole.lean`)
and `MsqAllocX.msqAllocX_promising` (`Lower/MsqAllocXWhole.lean`). Here each
gets

- `_sem`: the semantic machine (`ReachableSem Arch.tso fuel`), by
  `KitX.lower_promising_x64_sem` (`Lower/KitX64Sem.lean`) with the
  original threads (`xrT`, `msqT`, `msqAT`), start records and final readings
  (`PilotX.pilotX_final`; the x64 MS queue pilot's `MQX` reading, here factored
  once as `MsqXR.msqFinal` and shared by the x64 MS queue pilot and the x64 allocating MS queue pilot);
- `_semInf`: the fuel-free semantic machine (`Live.Inf.ReachableSemInf
  Arch.tso`), the form the WeakCore lowering consumes, from `_sem` through
  `Live.Inf.reachableSemInf_iff` (a fuel-free run is a semantic run at some
  fuel).

The x64 Treiber pilot with a `dmem` call stack, `PilotX.pilotX_promising`
(`Lower/PilotX64Whole.lean`), gets the same two forms by the value-restricted
purity bridge on the semantic machines
(`Vals.envGValsBridgeX_ofPure_sem`/`_semInf`, `Lower/KitX64ValsPureSem.lean`)
instead of the frameless kit.

Hypotheses and conclusions are the executable-machine theorems', verbatim, with only the
machine changed (the `fuel` binder dropped in `_semInf`). Scope and limits:
as for the executable-machine pilots and the kit.
-/
import Kraken.Promising.Lower.KitX64Sem
import Kraken.Promising.Lower.PilotXRWhole
import Kraken.Promising.Lower.MsqXRWhole
import Kraken.Promising.Lower.MsqAllocXWhole
import Kraken.Promising.Lower.PilotX64Whole
import Kraken.Promising.Lower.KitX64ValsPureSem

open Std.WP Kraken Kraken.Promising MachineWP Kraken.Promising.Live.Bridge
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

/-! ## the x64 register-link pilot -/

namespace Kraken.Promising.Lower.PilotXR

open Kraken.Promising.X64.EnvG.Treiber2X
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16)
open Kraken.Promising.Lower.KitX (lower_promising_x64_sem)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilotXR)]

/-- **`pilotXR_promising`, semantic machine** (`ReachableSem Arch.tso fuel`):
same hypotheses and conclusion. -/
theorem pilotXR_promising_sem {fuel : Nat} {P : Params} (hL : TLocs P) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartXR P 0 s0) (h1 : StartXR P 1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0)
    {cfg : Config isa} (hc : ReachableSem Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2FinalX (P.n 0) (P.n 1) cfg := by
  refine lower_promising_x64_sem (Φ := Treiber2FinalX (P.n 0) (P.n 1)) fuel sAll_le16 (erase_init hL _) rfl
    (fun tid h => xrT P hL tid (by simpa using h)) ?_ hc hf
    fun _ _ E' hle hsize hB => PilotX.pilotX_final hL hf E' hle hsize hB
  intro tid h
  rcases tid with _ | _ | i
  · exact xrT_start hL (by decide) h0 hT0
  · exact xrT_start hL (by decide) h1 hT0
  · simp only [List.length_cons, List.length_nil] at h; omega

/-- **`pilotXR_promising`, fuel-free semantic machine**
(`Live.Inf.ReachableSemInf Arch.tso`): same hypotheses and conclusion. -/
theorem pilotXR_promising_semInf {P : Params} (hL : TLocs P) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartXR P 0 s0) (h1 : StartXR P 1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0)
    {cfg : Config isa} (hc : Live.Inf.ReachableSemInf Arch.tso (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2FinalX (P.n 0) (P.n 1) cfg :=
  let ⟨_, hc⟩ := Live.Inf.reachableSemInf_iff.mp hc
  pilotXR_promising_sem hL h0 h1 hT0 hc hf

end Kraken.Promising.Lower.PilotXR

/-! ## the x64 MS queue pilot -/

namespace Kraken.Promising.Lower.MsqXR

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 split_sAll)
open Kraken.Promising.Lower.KitX (lower_promising_x64_sem)

/-- **The x64 MS queue pilot's final reading** (the reading step of `msqXR_promising`,
factored): from the done threads' `MQX P` (two threads, a ghost above
`ghost₀ P`), the dequeuer's `r12 = n1`, `r13 = n2`. -/
theorem msqFinal {P : Params} (hL : QLocs P) {cfg : Config isa} (hf : cfg.final = true)
    {rF' : Nat → Res} {g' : Ghost} (E' : Erase rF' g' (fun _ => False) cfg) (hle : (ghost₀ P).Le g')
    (hsize : cfg.threads.size = 2) (hB : ∀ tid, cfg.Done tid → MQX P cfg (rF' tid) g') :
    MsQueue2FinalX P.n1 P.n2 cfg := by
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw P).mono hle
  have fin : ∀ i, i < cfg.threads.size → MQX P cfg (rF' i) g' → 1 ≤ ((rF' i).wr P.tokH).q ∨
      MsQueue2FinalX P.n1 P.n2 cfg := by
    rintro i hi (⟨th, hth, hd, hiv, hacq⟩ | hq)
    · exact .inr ⟨th, hth, final_values E' hW hL hiv
        (fun x hx => TreiberCommon.total_acq_of_ge E' hi (hacq x hx)) hd⟩
    · exact .inl hq
  rcases fin 0 hi0 (hB 0 (Config.final_done hf hi0)) with hq0 | h
  · rcases fin 1 hi1 (hB 1 (Config.final_done hf hi1)) with hq1 | h
    · exact (tokH_pair_false E' hi0 hi1 (by decide) hq0 hq1).elim
    · exact h
  · exact h

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msqXR)]

/-- **`msqXR_promising`, semantic machine** (`ReachableSem Arch.tso fuel`):
same hypotheses and conclusion. -/
theorem msqXR_promising_sem {fuel : Nat} {P : Params} (hL : QLocs P) (hpt : P.trk = false)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartE P s0) (h1 : StartD P s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem P)
    {cfg : Config isa} (hc : ReachableSem Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : MsQueue2FinalX P.n1 P.n2 cfg := by
  refine lower_promising_x64_sem (Φ := MsQueue2FinalX P.n1 P.n2) fuel sAll_le16 (erase_init hL _) rfl
    (msqT P hL hpt) ?_ hc hf fun _ _ E' hle hsize hB => msqFinal hL hf E' hle hsize hB
  intro tid h
  rcases tid with _ | _ | i
  · exact ⟨⟨h0.exe, h0.decls, h0.endPc, h0.pc, split_sAll h0.dmem, 0, d8_of_dmem h0.dmem, h0.r11⟩,
      0, h0.r11, h0.rbx, h0.r12, h0.r13, d8_of_dmem h0.dmem, e0_init P _⟩
  · exact ⟨⟨h1.exe, h1.decls, h1.endPc, h1.pc, split_sAll h1.dmem, 0, d8_of_dmem h1.dmem, h1.r11⟩,
      0, h1.r11, h1.rbx, h1.r14, d8_of_dmem h1.dmem, comD_init P _ hi⟩
  · simp only [List.length_cons, List.length_nil] at h; omega

/-- **`msqXR_promising`, fuel-free semantic machine**
(`Live.Inf.ReachableSemInf Arch.tso`): same hypotheses and conclusion. -/
theorem msqXR_promising_semInf {P : Params} (hL : QLocs P) (hpt : P.trk = false)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartE P s0) (h1 : StartD P s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem P)
    {cfg : Config isa} (hc : Live.Inf.ReachableSemInf Arch.tso (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : MsQueue2FinalX P.n1 P.n2 cfg :=
  let ⟨_, hc⟩ := Live.Inf.reachableSemInf_iff.mp hc
  msqXR_promising_sem hL hpt h0 h1 hi hc hf

end Kraken.Promising.Lower.MsqXR

/-! ## the x64 allocating MS queue pilot -/

namespace Kraken.Promising.Lower.MsqAllocX

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 split_sAll)
open Kraken.Promising.Lower.KitX (lower_promising_x64_sem)
open Kraken.Promising.Lower.MsqXR (StartD msqXR msqFinal)

/-- **`msqAllocX_promising`, semantic machine** (`ReachableSem Arch.tso
fuel`): same hypotheses and conclusion. -/
theorem msqAllocX_promising_sem {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 msqAX)]
    [Executable.ValidLayout (l1 msqXR)] {h t s base : BitVec 64} (hA : ArenaLocs h t s base)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartA (layout := l0) (pAX h t s base) s0)
    (h1 : StartD (layout := l1) (pAX h t s base) s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem (pAX h t s base))
    {cfg : Config isa} (hc : ReachableSem Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : MsQueue2FinalX base (base + 16) cfg := by
  have hL := hA.qLocs
  refine lower_promising_x64_sem (Φ := MsQueue2FinalX base (base + 16)) fuel sAll_le16 (erase_init hL _) rfl
    (msqAT l0 l1 h t s base hA) ?_ hc hf fun _ _ E' hle hsize hB => msqFinal hL hf E' hle hsize hB
  intro tid htid
  rcases tid with _ | _ | i
  · obtain ⟨he, hds, hpc, hend, h11, hbx, h14, hr1, hr2, hdm⟩ := h0
    exact ⟨⟨he, hds, hend, hpc, split_sAll hdm, 0, h11, hr1,
      (show s0.st.1.regs.get64 .r14 + 16 + 16 ≤ _ by rw [h14]; exact hr2), d8_of_dmem hdm⟩,
      0, h11, hbx, h14, hr1, hr2, d8_of_dmem hdm, e0_init _ _⟩
  · obtain ⟨he, hds, hpc, hend, h11, hbx, h14, hdm⟩ := h1
    exact ⟨⟨he, hds, hend, hpc, split_sAll hdm, 0, d8_of_dmem hdm, h11⟩, 0, h11, hbx, h14, d8_of_dmem hdm,
      comD_init _ _ hi⟩
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **`msqAllocX_promising`, fuel-free semantic machine**
(`Live.Inf.ReachableSemInf Arch.tso`): same hypotheses and conclusion. -/
theorem msqAllocX_promising_semInf (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 msqAX)]
    [Executable.ValidLayout (l1 msqXR)] {h t s base : BitVec 64} (hA : ArenaLocs h t s base)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartA (layout := l0) (pAX h t s base) s0)
    (h1 : StartD (layout := l1) (pAX h t s base) s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem (pAX h t s base))
    {cfg : Config isa} (hc : Live.Inf.ReachableSemInf Arch.tso (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : MsQueue2FinalX base (base + 16) cfg :=
  let ⟨_, hc⟩ := Live.Inf.reachableSemInf_iff.mp hc
  msqAllocX_promising_sem l0 l1 hA h0 h1 hi hc hf

end Kraken.Promising.Lower.MsqAllocX

/-! ## the x64 Treiber pilot with a `dmem` call stack -/

namespace Kraken.Promising.Lower.PilotX

open Kraken.Promising.X64.EnvG.Treiber2X

/-- **`pilotX_promising`, semantic machine** (`ReachableSem Arch.tso fuel`):
same hypotheses and conclusion. -/
theorem pilotX_promising_sem {fuel : Nat} (l0 l1 : _root_.Layout)
    [Executable.ValidLayout (l0 pilotX)] [Executable.ValidLayout (l1 pilotX)] {P : Params} (hL : TLocs P)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartPX (layout := l0) P 0 s0) (h1 : StartPX (layout := l1) P 1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0)
    (hm0 : MemInv (GV P) (Config.init [s0, s1] initMem).mem)
    {cfg : Config isa} (hc : ReachableSem Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2FinalX (P.n 0) (P.n 1) cfg := by
  have hv : ∀ w, Executable.ValidLayout (layouts l0 l1 w pilotX) := fun w => by
    rcases w with _ | _ <;> assumption
  refine Vals.envGValsBridgeX_ofPure_sem (le16_SL P) (GV P) (erase_init hL _) (ghost₀_pend _)
    (fun w => pilotXPure (layout := layouts l0 l1 w) P) (fun w => @pilotX_phase1FX (layouts l0 l1 w) (hv w))
    ?_ hm0 (hthr_pX (layouts l0 l1) hL h0 h1 hT0) hc hf
    fun _ _ E' hle hsize hB => pilotX_final hL hf E' hle hsize hB
  rintro (_ | _ | w) s hs
  · cases hs; exact pilotXPure_holds (layout := l0) P (by decide) h0
  · cases hs; exact pilotXPure_holds (layout := l1) P (by decide) h1
  · cases hs

/-- **`pilotX_promising`, fuel-free semantic machine**
(`Live.Inf.ReachableSemInf Arch.tso`): same hypotheses and conclusion. -/
theorem pilotX_promising_semInf (l0 l1 : _root_.Layout)
    [Executable.ValidLayout (l0 pilotX)] [Executable.ValidLayout (l1 pilotX)] {P : Params} (hL : TLocs P)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartPX (layout := l0) P 0 s0) (h1 : StartPX (layout := l1) P 1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0)
    (hm0 : MemInv (GV P) (Config.init [s0, s1] initMem).mem)
    {cfg : Config isa} (hc : Live.Inf.ReachableSemInf Arch.tso (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2FinalX (P.n 0) (P.n 1) cfg :=
  let ⟨_, hc⟩ := Live.Inf.reachableSemInf_iff.mp hc
  pilotX_promising_sem l0 l1 hL h0 h1 hT0 hm0 hc hf

end Kraken.Promising.Lower.PilotX

#print axioms Kraken.Promising.Lower.PilotXR.pilotXR_promising_sem
#print axioms Kraken.Promising.Lower.PilotXR.pilotXR_promising_semInf
#print axioms Kraken.Promising.Lower.MsqXR.msqFinal
#print axioms Kraken.Promising.Lower.MsqXR.msqXR_promising_sem
#print axioms Kraken.Promising.Lower.MsqXR.msqXR_promising_semInf
#print axioms Kraken.Promising.Lower.MsqAllocX.msqAllocX_promising_sem
#print axioms Kraken.Promising.Lower.MsqAllocX.msqAllocX_promising_semInf
#print axioms Kraken.Promising.Lower.PilotX.pilotX_promising_sem
#print axioms Kraken.Promising.Lower.PilotX.pilotX_promising_semInf
