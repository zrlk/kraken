/-
**hello.w's threads abort path and refused-`clone` blocks at `ph2bH`** (AArch64;
part 2; the hello twin of `Spike/Lib/A64WakeRefPh.lean`): the phase checks `stubTW_sfactsACG`
(`abortPhThreadsOk`) and the refusal blocks (`blkPh` of `cb`, `cl`, `flB`) ask, at the projected phase `ph2bH`
(`Spike/Lib/A64HelloOwn2.lean`) and hello.w's off-site pcs, decided once by `decide +kernel` on the
certificate's keyed table (no pc literal).

- `abortRefTabH`: the facts, as the certificate's table; `abortRefFactsH`: they hold at the resolved phases.
- `abortPhTH`: `abortPhThreadsOk` at `ph2bH`.
- `refPh_cbH`, `refPh_clH`, `refPh_flH`: the three blocks' `blkPh` (`cb` at `.sp6 + 4 · 26`, the `cbz` past the
  clone's `svc`; `.clone13`'s `cl`; `.1_spawnfail5`'s `flB`).
-/
import Spike.Lib.A64AbortPhT
import Spike.Lib.A64HelloTake2
import Spike.Lib.A64HelloSpawnFail

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.A64.Flow.Worker.Hello.Child (cb pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (cl)
open Spike.Lib.A64.Flow.Worker.Hello.SpawnFail (flB)

set_option linter.unusedSimpArgs false

/-- **The threads abort path's facts** (`abortPhThreadsOk`'s) and the refused-`clone` blocks', as the
certificate's table. -/
def abortRefTabH : List Scc.Cert.Rt.A64.PhFact :=
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
   .blk (pfxM ++ ".sp6") 26 (cb pfxM) none none, .blk (pfxM ++ ".clone13") 0 (cl pfxM) none none,
   .blk (pfxM ++ ".1_spawnfail5") 0 flB none none]

/-- The table's facts hold at the resolved phases. -/
theorem abortRefFactsH :
    abortRefTabH.all (Scc.Cert.Rt.A64.factOk (codeT lo SccCode.helloProg) okC ph2bHC) = true := by
  decide +kernel

section
variable {Λ : Scc.Sem.Layout} {lab : Label → Int64}

private theorem hr0 : ∀ r, (none : Option String) = some r → (0 : Int64) = lab r := fun _ h => by cases h

private theorem hn0 :
    ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo SccCode.helloProg) none t = true → (fun _ => false) t = true :=
  fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h

/-- The table's facts at `ph2bH` and the off-site pcs. -/
private theorem facts (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) :
    abortRefTabH.all
      (Scc.Cert.Rt.A64.factOk (codeOf lo SccCode.helloProg) (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg Λ) ph2bH) =
      true := by
  have h := abortRefFactsH
  rwa [codeT_eq, ← okPc_eq hΛ, ← ph2bH_eq] at h

/-- **`abortPhThreadsOk` at `ph2bH`** with the certificate's labels. -/
theorem abortPhTH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → lab l = Int64.ofNat x) :
    Spike.Lib.A64.StubW.abortPhThreadsOk (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg Λ) ph2bH lab = true := by
  have h := facts hΛ
  simp only [abortRefTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, -⟩ := h
  have so : ∀ {l : String} {k : Nat},
      Scc.Cert.Rt.A64.factOk (codeOf lo SccCode.helloProg) (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg Λ) ph2bH
        (.step l k) = true →
      Spike.Lib.A64.StubW.phOne (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg Λ) ph2bH (lab l + Int64.ofNat (4 * k))
        = true :=
    fun h => by
      obtain ⟨h1, h2⟩ := Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab h
      simp only [Spike.Lib.A64.StubW.phOne, h1, h2, beq_self_eq_true, Bool.and_self]
  have bp := fun {l k b} (f : Scc.Cert.Rt.A64.factOk (codeOf lo SccCode.helloProg)
      (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg Λ) ph2bH (.blk l k b none none) = true) =>
    Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr0 hn0 f
  have e17 := Spike.Lib.A64.Rt.PhOfTab.ph_of_factOk hlab f17
  have e18 := Spike.Lib.A64.Rt.PhOfTab.ph_of_factOk hlab f18
  rw [Spike.Lib.A64.Flow.ofNat4_zero] at e18
  unfold Spike.Lib.A64.StubW.abortPhThreadsOk
  simp only [Abort.threads]
  rw [bp f0, bp f1, bp f2, bp f3, bp f4, bp f5, bp f6, bp f7, bp f8, bp f9, bp f10, bp f11, so f12, so f13,
    bp f14, so f15, bp f16]
  simp only [Bool.true_and, beq_iff_eq]
  exact e17.trans e18.symm

/-- **The `cbz` block past the clone's `svc`'s phase check at `ph2bH`** (`fNS .cb`'s pc, `.sp6 + 4 · 26`). -/
theorem refPh_cbH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → lab l = Int64.ofNat x) :
    blkPh (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg Λ) ph2bH (fun _ => false) lab
      (lab (pfxM ++ ".sp6") + Int64.ofNat (4 * 26)) 0 (cb pfxM) = true := by
  have h := facts hΛ
  simp only [abortRefTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr0 hn0 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **`.clone13`'s block's phase check at `ph2bH`.** -/
theorem refPh_clH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → lab l = Int64.ofNat x) :
    blkPh (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg Λ) ph2bH (fun _ => false) lab
      (lab (pfxM ++ ".clone13") + Int64.ofNat (4 * 0)) 0 (cl pfxM) = true := by
  have h := facts hΛ
  simp only [abortRefTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr0 hn0 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **`.1_spawnfail5`'s block's phase check at `ph2bH`.** -/
theorem refPh_flH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → lab l = Int64.ofNat x) :
    blkPh (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg Λ) ph2bH (fun _ => false) lab
      (lab (pfxM ++ ".1_spawnfail5") + Int64.ofNat (4 * 0)) 0 flB = true := by
  have h := facts hΛ
  simp only [abortRefTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr0 hn0 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.abortPhTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.abortPhTH

/-- info: 'Spike.Lib.A64.HelloPh.refPh_cbH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.refPh_cbH

/-- info: 'Spike.Lib.A64.HelloPh.refPh_clH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.refPh_clH

/-- info: 'Spike.Lib.A64.HelloPh.refPh_flH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.refPh_flH
