/-
A private FlatHashMap lookup feeding the shared Michael–Scott queue, on the
FEAT_LSE2 target `isaLSE2`. ISA: AArch64; `Arch.armv8`.

* `mixProg_promising_lse2` (executable machine) and `_lse2_semInf`
  (`Live.Inf.ReachableSemInf`, the form the WeakCore lowering consumes):
  `Flat.Mix.mixProg_promising`'s hypotheses, verbatim, give `MixFinal x` of
  `ofL cfg` for every final configuration `cfg` of `isaLSE2`, through
  `KitVals.lower_promising_valsW_lse2`/`_semInf` (`Lower/KitValsLSE2.lean`)
  with the threads `mixT`/`deqT`. The start and final-reading steps
  of the executable-machine proof are factored once (`mixTs_start`, `mixFinal_of_hB`).
* `mixProg_promising_tblD_lse2_semInf`: the concrete instance of
  `Lower/FlatMixWhole.lean` (`tblD`, key `6`, a miss) on `isaLSE2`, fuel-free
  semantic machine: the dequeuer's `1`, `2` and thread `0`'s `x20 = 1`.
-/
import Kraken.Promising.Lower.FlatMixWhole
import Kraken.Promising.Lower.KitValsLSE2
import Kraken.Promising.Lower.MsqPilotLSE2

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Flat.Mix

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.Lower.MsqPilot (progD StartD progD_lse2Free)
open Kraken.Promising.Lower.KitVals (LowerThreadW lower_promising_valsW_lse2 lower_promising_valsW_lse2_semInf)

/-! ## The two threads, their starts and the final reading -/

/-- The node data words carry no release predicate. -/
theorem mix_datPure (P : Params2) :
    ∀ m, m = P.n1 ∨ m = P.n2 → ∀ v : Val, Pred.Pure ((ghost2 P).rel ⟨m, 4⟩) v := by
  obtain ⟨⟨h, t, d, n1⟩, n2⟩ := P
  have hr' : ∀ l, ¬ Params2.IsW ⟨⟨h, t, d, n1⟩, n2⟩ l → ∀ v, Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel l) v :=
    fun l hl v => by rw [ghost2_rel_ne hl]; exact Pred.emp_pure v
  rintro m (rfl | rfl) v
  · exact hr' _ (not_isW_dat _) v
  · exact hr' _ (not_isW_dat2 _) v

/-- The threads of `mixProg_promising`. -/
noncomputable def mixTs (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 mixProg)]
    [Executable.ValidLayout (l1 progD)] (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (x : Tbl × Nat) :
    ∀ tid, tid < 2 → LowerThreadW Arch.armv8 tid (ghost2 P).rel (MixB P x) (QS P) (QG P)
  | 0, _ => mixT l0 P hL ht x (mix_datPure P)
  | 1, _ => deqT l1 P hL ht x
  | _ + 2, hh => absurd hh (by omega)

/-- **The two threads at their starts** (the start step of
`mixProg_promising`, factored). -/
theorem mixTs_start (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 mixProg)]
    [Executable.ValidLayout (l1 progD)] (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (x : Tbl × Nat)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : MixStartS l0 P x s0)
    (h1 : StartD (layout := l1) P.h s1) (hi : InitV2 (Config.init [s0, s1] initMem).mem P) :
    ∀ tid (hh : tid < [s0, s1].length), (mixTs l0 l1 P hL ht x tid hh).Start
      (σInit (Config.init [s0, s1] initMem) (tRes2 (Config.init [s0, s1] initMem).mem P tid) (ghost2 P))
      [s0, s1][tid] := by
  intro tid hh
  rcases tid with _ | _ | _
  · obtain ⟨he, hds, hend, hpc, hpre⟩ := h0
    obtain ⟨⟨hl, h25, h26, h27, -⟩, hlo, hq⟩ := id hpre
    exact ⟨he, hds, hend, hpc, ⟨0, hpre⟩, ⟨0, ⟨hl, h25, h26, h27, rfl, hlo, start1_init _ _⟩, hq⟩, ⟨0, hpre⟩⟩
  · obtain ⟨he, hds, hend, hpc, h30, h21, hd8, hd4⟩ := h1
    exact ⟨he, hds, hend, hpc, ⟨0, h30, hd8, hd4⟩, ⟨0, h30, h21, ⟨hd8, hd4⟩, comD2_init _ _ hi⟩,
      ⟨0, h30, h21, hd8, hd4⟩⟩
  · simp at hh; omega

/-- **The final reading of `mixProg`** (the reading step of
`mixProg_promising`, factored): from the done threads' `MixB P x` (two
threads, a ghost above `ghost2 P`), `MixFinal x`. -/
theorem mixFinal_of_hB {P : Params2} (hL : QLocs2 P) (x : Tbl × Nat) {c : Config isa} (hf : c.final = true)
    {rF' : Nat → Res} {g' : Ghost} (E' : Erase rF' g' (fun _ => False) c) (hle : (ghost2 P).Le g')
    (hsize : c.threads.size = 2) (hB : ∀ tid, c.Done tid → MixB P x c (rF' tid) g') : MixFinal x c := by
  obtain ⟨⟨h, t, d, n1⟩, n2⟩ := P
  have hi0 : (0 : Nat) < c.threads.size := by omega
  have hi1 : (1 : Nat) < c.threads.size := by omega
  refine ⟨msqueue2_final_of_hB hL hf E' hle hsize fun tid hd => (hB tid hd).mb2, ?_⟩
  rcases hB 0 (Config.final_done hf hi0) with ⟨-, -, -, -, a0⟩ | ⟨-, hs⟩; rotate_left; exact hs
  rcases hB 1 (Config.final_done hf hi1) with ⟨-, -, -, -, a1⟩ | ⟨-, hs⟩; rotate_left; exact hs
  exact (TreiberCommon.acq_pair_false E' hi0 hi1 (by decide) (a0 _ (Or.inl rfl)) (a1 _ (Or.inl rfl))).elim

set_option maxRecDepth 8000 in
/-- `mixProg` has no LSE2 pair (no 64-bit `LDP`/`STP`). -/
theorem mixProg_lse2Free : ∀ d ∈ mixProg, d.LSE2Free := by decide

/-- Neither thread's text has an LSE2 pair. -/
theorem mixTs_free (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 mixProg)]
    [Executable.ValidLayout (l1 progD)] (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (x : Tbl × Nat)
    {s0 s1 : isa.State} : ∀ tid (hh : tid < [s0, s1].length), ∀ d ∈ (mixTs l0 l1 P hL ht x tid hh).p, d.LSE2Free
  | 0, _ => mixProg_lse2Free | 1, _ => progD_lse2Free | _ + 2, hh => absurd hh (by simp)

/-! ## The headlines on `isaLSE2` -/

section LSE2

variable (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 mixProg)] [Executable.ValidLayout (l1 progD)]
  (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (x : Tbl × Nat) {s0 s1 : isa.State}
  {initMem : List (Loc × Val)} (h0 : MixStartS l0 P x s0) (h1 : StartD (layout := l1) P.h s1)
  (hi : InitV2 (Config.init [s0, s1] initMem).mem P) (hm : ∀ p ∈ initMem, QG P p.1 p.2)
include hL ht h0 h1 hi hm

/-- **`mixProg_promising` on `isaLSE2`** (executable machine): same
hypotheses; the conclusion read through `ofL`. -/
theorem mixProg_promising_lse2 {fuel : Nat} {cfg : Config isaLSE2}
    (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg) (hf : cfg.final = true) :
    MixFinal x (ofL cfg) :=
  lower_promising_valsW_lse2 Arch.armv8 (QG P) (fun _ hc' => Config.ntFree_armv8K hc') (erase_init2 hL _) rfl
    (MemInv.of_init rfl (fun _ _ => .inl (by simp)) hm) (mixTs l0 l1 P hL ht x)
    (mixTs_start l0 l1 P hL ht x h0 h1 hi) (mixTs_free l0 l1 P hL ht x)
    (fun _ hf' _ _ E' hle hsize hB => mixFinal_of_hB hL x hf' E' hle (by simpa using hsize) hB) hc hf

/-- **`mixProg_promising` on `isaLSE2`, fuel-free semantic machine**
(`ReachableSemInf`), the form the lowering consumes. -/
theorem mixProg_promising_lse2_semInf {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf Arch.armv8 (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : MixFinal x (ofL cfg) :=
  lower_promising_valsW_lse2_semInf Arch.armv8 (QG P) (fun _ hc' => Config.ntFree_armv8K hc')
    (erase_init2 hL _) rfl (MemInv.of_init rfl (fun _ _ => .inl (by simp)) hm) (mixTs l0 l1 P hL ht x)
    (mixTs_start l0 l1 P hL ht x h0 h1 hi) (mixTs_free l0 l1 P hL ht x)
    (fun _ hf' _ _ E' hle hsize hB => mixFinal_of_hB hL x hf' E' hle (by simpa using hsize) hB) hc hf

end LSE2

/-! ## The concrete instance on `isaLSE2` -/

/-- **`mixProg_promising_tblD` on `isaLSE2`, fuel-free semantic machine**
(`ReachableSemInf`), the conclusion read through `ofL`. -/
theorem mixProg_promising_tblD_lse2_semInf {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf Arch.armv8
      (Config.init [threadMD, MsqPilot.threadD] MsqPilot.initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) :
    MsQueue2Final (ofL cfg) ∧ ∃ th, (ofL cfg).threads[0]? = some th ∧ th.st.st.1.regs.X20.toNat = 1 := by
  obtain ⟨hF, th, h0, r, hr, hx⟩ := mixProg_promising_lse2_semInf layoutM MsqPilot.layoutD P1 qLocs2_P1
    (by decide) (tblD, 6) threadMD_start MsqPilot.threadD_start initV2_P1 initMem_QG hc hf
  rw [tblD_lookup6] at hr; cases hr
  exact ⟨hF, th, h0, hx⟩

end Kraken.Promising.Lower.Flat.Mix

#print axioms Kraken.Promising.Lower.Flat.Mix.mixProg_promising_lse2
#print axioms Kraken.Promising.Lower.Flat.Mix.mixProg_promising_lse2_semInf
#print axioms Kraken.Promising.Lower.Flat.Mix.mixProg_promising_tblD
#print axioms Kraken.Promising.Lower.Flat.Mix.mixProg_promising_tblD_lse2_semInf
