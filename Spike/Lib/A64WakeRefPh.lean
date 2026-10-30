/-
**wake.w's threads abort path and refused-`clone` blocks at `ph2b`**
(AArch64): the phase checks `stubTW_sfactsAC` (`abortPhThreadsOk`) and
`blkWs_spawnFail_wake` (`pcb`, `pcl`, `pfl`) ask, at the projected phase
`ph2b` (`Spike/Lib/A64WakeTake2.lean`; at `phW` the blocks, in `wakeR`,
are a phase off the abort `.1_spawnfail5` calls) and wake.w's off-site pcs,
decided once by `decide +kernel` on the certificate's keyed table (no pc literal).

- `abortRefTabW`: the facts, as the certificate's table; `abortRefFactsW`:
  they hold at the resolved phases.
- `abortPhTW`: `abortPhThreadsOk` at `ph2b`.
- `refPh_cb`, `refPh_cl`, `refPh_fl`: the three blocks' `blkPh`.
- `abortIn_wakeR`: wake.w's program has the abort code.
-/
import Spike.Lib.A64AbortPhT
import Spike.Lib.A64WakeTake2
import Spike.Lib.A64WakeSpawnFail

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.A64.Flow.Worker.Wake.Child (cb pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (cl)
open Spike.Lib.A64.Flow.Worker.Wake.SpawnFail (flB)

set_option linter.unusedSimpArgs false

/-- **wake.w's program has the abort code.** -/
theorem abortIn_wakeR : Scc.Cert.Rt.A64.Abort.abortIn wakeProg = true := by decide +kernel

/-- **The threads abort path's facts** (`abortPhThreadsOk`'s) and the
refused-`clone` blocks', as the certificate's table. -/
def abortRefTabW : List Scc.Cert.Rt.A64.PhFact :=
  [.blk "scc_rt_abort" 0 Abort.Disp.d0 none none, .blk ".L12_scc_rt_abort.0_entry" 0 Abort.Disp.t1 none none,
   .blk ".L12_scc_rt_abort.0_entry" 4 Abort.Disp.j1 none none,
   .blk ".L12_scc_rt_abort.2_next1" 0 Abort.Disp.t2 none none,
   .blk ".L12_scc_rt_abort.2_next1" 4 Abort.Disp.j2 none none,
   .blk ".L12_scc_rt_abort.4_next3" 0 Abort.Disp.t3 none none,
   .blk ".L12_scc_rt_abort.4_next3" 4 Abort.Disp.j3 none none,
   .blk ".L12_scc_rt_abort.6_next5" 0 Abort.Disp.t4 none none,
   .blk ".L12_scc_rt_abort.6_next5" 4 Abort.Disp.j4 none none,
   .blk ".L12_scc_rt_abort.8_next7" 0 Abort.Disp.t5 none none,
   .blk ".L12_scc_rt_abort.9_is8" 0 Abort.Disp.g5 none none, .blk "scc_rt_abort_threads" 0 Abort.b0 none none,
   .step ".L17_scc_rt_abort_threads.0_entry" 0, .step ".L17_scc_rt_abort_threads.0_entry" 1,
   .blk ".L17_scc_rt_abort_threads.0_entry" 2 Abort.b1Threads none none,
   .step ".L17_scc_rt_abort_threads.0_entry" 7,
   .blk ".L17_scc_rt_abort_threads.0_entry" 8 Abort.b2 none none,
   .ph "scc_rt_abort_threads_exit" 1 0, .ph "scc_rt_abort_threads_exit" 0 0,
   .blk (pfxM ++ ".sp6") 14 (cb pfxM) none none, .blk (pfxM ++ ".clone9") 0 (cl pfxM) none none,
   .blk (pfxM ++ ".1_spawnfail5") 0 flB none none]

/-- The table's facts hold at the resolved phases. -/
theorem abortRefFactsW :
    abortRefTabW.all (Scc.Cert.Rt.A64.factOk (codeT lo wakeProg) okC ph2bC) = true := by
  decide +kernel

section
variable {Λ : Scc.Sem.Layout} {lab : Label → Int64}

private theorem hr0 : ∀ r, (none : Option String) = some r → (0 : Int64) = lab r := fun _ h => by cases h

private theorem hn0 : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo wakeProg) none t = true → (fun _ => false) t = true :=
  fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h

/-- The table's facts at `ph2b` and the off-site pcs. -/
private theorem facts (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) :
    abortRefTabW.all (Scc.Cert.Rt.A64.factOk (codeOf lo wakeProg) (Scc.Cert.Rt.A64.okPcOf lo wakeProg Λ) ph2b) =
      true := by
  have h := abortRefFactsW
  rwa [codeT_eq, ← okPc_eq hΛ, ← ph2b_eq] at h

/-- **`abortPhThreadsOk` at `ph2b`** with the certificate's labels. -/
theorem abortPhTW (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → lab l = Int64.ofNat x) :
    Spike.Lib.A64.StubW.abortPhThreadsOk (Scc.Cert.Rt.A64.okPcOf lo wakeProg Λ) ph2b lab = true := by
  have h := facts hΛ
  simp only [abortRefTabW, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, -⟩ := h
  have so : ∀ {l : String} {k : Nat},
      Scc.Cert.Rt.A64.factOk (codeOf lo wakeProg) (Scc.Cert.Rt.A64.okPcOf lo wakeProg Λ) ph2b (.step l k) = true →
      Spike.Lib.A64.StubW.phOne (Scc.Cert.Rt.A64.okPcOf lo wakeProg Λ) ph2b (lab l + Int64.ofNat (4 * k)) = true :=
    fun h => by
      obtain ⟨h1, h2⟩ := Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab h
      simp only [Spike.Lib.A64.StubW.phOne, h1, h2, beq_self_eq_true, Bool.and_self]
  have bp := fun {l k b} (f : Scc.Cert.Rt.A64.factOk (codeOf lo wakeProg) (Scc.Cert.Rt.A64.okPcOf lo wakeProg Λ)
      ph2b (.blk l k b none none) = true) => Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr0 hn0 f
  have e17 := Spike.Lib.A64.Rt.PhOfTab.ph_of_factOk hlab f17
  have e18 := Spike.Lib.A64.Rt.PhOfTab.ph_of_factOk hlab f18
  rw [Spike.Lib.A64.Flow.ofNat4_zero] at e18
  unfold Spike.Lib.A64.StubW.abortPhThreadsOk
  simp only [Abort.threads]
  rw [bp f0, bp f1, bp f2, bp f3, bp f4, bp f5, bp f6, bp f7, bp f8, bp f9, bp f10, bp f11, so f12, so f13,
    bp f14, so f15, bp f16]
  simp only [Bool.true_and, beq_iff_eq]
  exact e17.trans e18.symm

/-- **`.sp6`'s `cbz` block's phase check at `ph2b`.** -/
theorem refPh_cb (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → lab l = Int64.ofNat x) :
    blkPh (Scc.Cert.Rt.A64.okPcOf lo wakeProg Λ) ph2b (fun _ => false) lab
      (lab (pfxM ++ ".sp6") + Int64.ofNat (4 * 14)) 0 (cb pfxM) = true := by
  have h := facts hΛ
  simp only [abortRefTabW, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr0 hn0 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **`.clone9`'s block's phase check at `ph2b`.** -/
theorem refPh_cl (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → lab l = Int64.ofNat x) :
    blkPh (Scc.Cert.Rt.A64.okPcOf lo wakeProg Λ) ph2b (fun _ => false) lab
      (lab (pfxM ++ ".clone9") + Int64.ofNat (4 * 0)) 0 (cl pfxM) = true := by
  have h := facts hΛ
  simp only [abortRefTabW, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr0 hn0 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **`.1_spawnfail5`'s block's phase check at `ph2b`.** -/
theorem refPh_fl (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → lab l = Int64.ofNat x) :
    blkPh (Scc.Cert.Rt.A64.okPcOf lo wakeProg Λ) ph2b (fun _ => false) lab
      (lab (pfxM ++ ".1_spawnfail5") + Int64.ofNat (4 * 0)) 0 flB = true := by
  have h := facts hΛ
  simp only [abortRefTabW, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr0 hn0 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end

end Spike.Lib.A64.WakePh

/-- info: 'Spike.Lib.A64.WakePh.abortPhTW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.abortPhTW

/-- info: 'Spike.Lib.A64.WakePh.refPh_cb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.refPh_cb

/-- info: 'Spike.Lib.A64.WakePh.refPh_cl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.refPh_cl

/-- info: 'Spike.Lib.A64.WakePh.refPh_fl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.refPh_fl
