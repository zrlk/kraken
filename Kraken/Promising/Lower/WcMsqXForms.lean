/-
WeakCore's try-once Michael–Scott queue lowered to x64, whole program, on the
semantic machines. ISA: x64 (`isa`); `Arch.tso`.

`wcMsqX_promising_sem` (`ReachableSem Arch.tso fuel`, by
`KitX.lower_promising_x64_sem` with the threads `wcT`) and
`wcMsqX_promising_semInf` (`Live.Inf.ReachableSemInf Arch.tso`, the form the
WeakCore lowering consumes, through `Live.Inf.reachableSemInf_iff`) are
`WcMsqX.wcMsqX_promising`'s hypotheses and conclusion (`WcMsqXFinal`),
verbatim, with only the machine changed. The start and final-reading steps
of the executable-machine proof are factored here once (`wcT_start`,
`wcMsqXFinal_of_hB`). Scope and limits: as for `wcMsqX_promising`.
-/
import Kraken.Promising.Lower.KitX64Sem
import Kraken.Promising.Lower.WcMsqXWhole

open Std.WP Kraken Kraken.Promising MachineWP Kraken.Promising.Live.Bridge
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.WcMsqX

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 split_sAll)
open Kraken.Promising.Lower.KitX (lower_promising_x64_sem)

/-- **The final reading of `wcMsqX`** (the reading step of
`wcMsqX_promising`, factored): from the done threads' `MQW P` (two threads,
a ghost above `ghost₀W P`, no tracking), the dequeuer's results satisfy
`WValsX`. -/
theorem wcMsqXFinal_of_hB {P : Params} (hL : QLocs P) (hpt : P.trk = false) {cfg : Config isa}
    (hf : cfg.final = true) {rF' : Nat → Res} {g' : Ghost} (E' : Erase rF' g' (fun _ => False) cfg)
    (hle : (ghost₀W P).Le g') (hsize : cfg.threads.size = 2) (hB : ∀ tid, cfg.Done tid → MQW P cfg (rF' tid) g') :
    WcMsqXFinal P.n1 P.n2 cfg := by
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀W_gww P).mono hle
  have fin : ∀ i, i < cfg.threads.size → MQW P cfg (rF' i) g' → 1 ≤ ((rF' i).wr P.tokH).q ∨
      WcMsqXFinal P.n1 P.n2 cfg := by
    rintro i hi (⟨th, hth, hd, hiv, hacq⟩ | hq)
    · exact .inr ⟨th, hth, final_valuesW E' hW hL hiv
        (fun x hx => TreiberCommon.total_acq_of_ge E' hi (hacq x hx)) hpt hi hd⟩
    · exact .inl hq
  exact (fin 0 hi0 (hB 0 (Config.final_done hf hi0))).elim (fun hq0 => (fin 1 hi1
    (hB 1 (Config.final_done hf hi1))).elim (fun hq1 => (tokH_pair_false E' hi0 hi1 (by decide) hq0 hq1).elim) id) id

variable [layout : _root_.Layout] [Executable.ValidLayout (layout wcMsqX)]

/-- **The two threads at their starts** (the start step of
`wcMsqX_promising`, factored). -/
theorem wcT_start {P : Params} (hL : QLocs P) (hpt : P.trk = false) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartEW P s0) (h1 : StartW P s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem P) :
    ∀ tid (h : tid < [s0, s1].length), (wcT P hL hpt tid h).Start
      (σInitX (Config.init [s0, s1] initMem) (tResW (Config.init [s0, s1] initMem).mem P tid) (ghost₀W P))
      [s0, s1][tid] := by
  intro tid h
  rcases tid with _ | _ | i
  · exact ⟨⟨h0.exe, h0.decls, h0.endPc, h0.pc, split_sAll h0.dmem, 0, d8_of_dmem h0.dmem, h0.r11⟩,
      0, h0.r11, h0.rbx, h0.r12, h0.r13, d8_of_dmem h0.dmem, e0_initW P _⟩
  · refine ⟨⟨h1.exe, h1.decls, h1.endPc, h1.pc, split_sAll h1.dmem, 0, d8_of_dmem h1.dmem, h1.r11⟩,
      0, h1.r11, h1.rbx, d8_of_dmem h1.dmem, comDW_init P _, hi, ?_⟩
    unfold TokFrozen; show (1 : Rat) ≤ fracDW P P.tokQ; simp [fracDW]
  · simp only [List.length_cons, List.length_nil] at h; omega

/-- **`wcMsqX_promising`, semantic machine** (`ReachableSem Arch.tso fuel`):
same hypotheses and conclusion. -/
theorem wcMsqX_promising_sem {fuel : Nat} {P : Params} (hL : QLocs P) (hpt : P.trk = false) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartEW P s0) (h1 : StartW P s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem P)
    {cfg : Config isa} (hc : ReachableSem Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : WcMsqXFinal P.n1 P.n2 cfg :=
  lower_promising_x64_sem (Φ := WcMsqXFinal P.n1 P.n2) fuel sAll_le16 (erase_initW hL _) rfl
    (wcT P hL hpt) (wcT_start hL hpt h0 h1 hi) hc hf
    fun _ _ E' hle hsize hB => wcMsqXFinal_of_hB hL hpt hf E' hle hsize hB

/-- **`wcMsqX_promising`, fuel-free semantic machine**
(`Live.Inf.ReachableSemInf Arch.tso`): same hypotheses and conclusion. -/
theorem wcMsqX_promising_semInf {P : Params} (hL : QLocs P) (hpt : P.trk = false) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartEW P s0) (h1 : StartW P s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem P)
    {cfg : Config isa} (hc : Live.Inf.ReachableSemInf Arch.tso (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : WcMsqXFinal P.n1 P.n2 cfg :=
  let ⟨_, hc⟩ := Live.Inf.reachableSemInf_iff.mp hc
  wcMsqX_promising_sem hL hpt h0 h1 hi hc hf

end Kraken.Promising.Lower.WcMsqX

#print axioms Kraken.Promising.Lower.WcMsqX.wcMsqX_promising_sem
#print axioms Kraken.Promising.Lower.WcMsqX.wcMsqX_promising_semInf
