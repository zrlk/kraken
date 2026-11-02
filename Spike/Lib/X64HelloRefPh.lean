/-
**hello.w's threads abort path and refused-`clone` nodes at `ph2bH`**
(x86-64; the twin of `Spike/Lib/A64HelloRefPh.lean`, at the template of
`Spike/Lib/X64WakeRefPh.lean`): the phase checks `stubTW_sfactsAC`
(`abortPhThreadsOk`) and the refusal path's nodes ask, at the projected
phase `ph2bH` (`Spike/Lib/X64HelloOwn2.lean`) and hello.w's off-site pcs,
decided once by `decide +kernel` on the certificate's keyed table (no pc
literal but the resolved exit label).

- `abortRefTabH`: the facts, as the certificate's table; `abortRefFactsH`:
  they hold at the resolved phases.
- `abortPhTH`: `abortPhThreadsOk` at `ph2bH`.
- `refPh_tsH`, `refPh_jeH`, `refPh_x26H`, `refPh_flH`: the refusal path's
  test (`phOne`) and three blocks' `blkPh`.

**Deviation from the A64 file.** As in `X64WakeRefPh`: offsets are bytes
and the labels `helloCells'` (`codeLabel`); the stub's `leaq` is one step
(`entry + 0`, 7 bytes), the `syscall` a step of 2 bytes at `entry + 34`;
the exit call's phase equation is decided on the resolved exit label (A64's
two `.ph` facts); the refusal path is the `testq` at `.x25 + 96` (3 bytes)
and the blocks `je` at `.x25 + 99`, `.x26`, `.spawnfail5` (A64's blocks
`cb`, `cl`, `flB`, so A64's `refPh_cbH`/`refPh_clH` are
`refPh_tsH`/`refPh_jeH`/`refPh_x26H`). The phase `ph2bH` is
`X64HelloOwn2`'s (A64: imported through `A64HelloTake2`).
-/
import Spike.Lib.X64AbortPhT
import Spike.Lib.X64HelloOwn2
import Spike.Lib.X64HelloSpawnFail

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq PhFact factOk deadN okPcOf)
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.X64.StubW (abortPhThreadsOk phOne)
open Spike.Lib.X64.Rt.PhOfTab (blkPh_of_factOk step_of_factOk)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (jeB x26B)
open Spike.Lib.X64.Flow.Worker.Hello.SpawnFail (flB)

set_option linter.unusedSimpArgs false

/-- **The threads abort path's facts** (`abortPhThreadsOk`'s but the exit
call's) and the refusal path's, as the certificate's table. -/
def abortRefTabH : List PhFact :=
  [.blk "scc_rt_abort" 0 Abort.Disp.d0 none none, .blk ".Lscc_rt_abort.entry" 0 Abort.Disp.t1 none none,
   .blk ".Lscc_rt_abort.entry" 16 Abort.Disp.j1 none none,
   .blk ".Lscc_rt_abort.next1" 0 Abort.Disp.t2 none none,
   .blk ".Lscc_rt_abort.next1" 16 Abort.Disp.j2 none none,
   .blk ".Lscc_rt_abort.next3" 0 Abort.Disp.t3 none none,
   .blk ".Lscc_rt_abort.next3" 16 Abort.Disp.j3 none none,
   .blk ".Lscc_rt_abort.next5" 0 Abort.Disp.t4 none none,
   .blk ".Lscc_rt_abort.next5" 16 Abort.Disp.j4 none none,
   .blk ".Lscc_rt_abort.next7" 0 Abort.Disp.t5 none none,
   .blk ".Lscc_rt_abort.is8" 0 Abort.Disp.g5 none none, .blk "scc_rt_abort_threads" 0 Abort.x0 none none,
   .step ".Lscc_rt_abort_threads.entry" 0 7, .blk ".Lscc_rt_abort_threads.entry" 7 Abort.x1Threads none none,
   .step ".Lscc_rt_abort_threads.entry" 34 2, .blk ".Lscc_rt_abort_threads.entry" 36 Abort.x2 none none,
   .step ".Lwc_main.x25" 96 3, .blk ".Lwc_main.x25" 99 jeB none none, .blk ".Lwc_main.x26" 0 x26B none none,
   .blk ".Lwc_main.spawnfail5" 0 flB none none]

/-- The table's facts hold at the resolved phases. -/
theorem abortRefFactsH : abortRefTabH.all (factOk (codeT lo helloCells) okC ph2bHC) = true := by
  decide +kernel

section

variable {Λ : Scc.Sem.Layout} {lab : Label → Int64}

private theorem hr0 : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = lab r + Int64.ofNat o' :=
  fun _ _ h => by cases h

private theorem hn0 : ∀ t, deadN (codeLabel lo helloCells) none t = true → (fun _ => false) t = true :=
  fun _ h => by simp [deadN] at h

/-- The table's facts at `ph2bH` and the off-site pcs. -/
private theorem facts (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) :
    abortRefTabH.all (factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) ph2bH) = true := by
  have h := abortRefFactsH
  rwa [codeT_eq, ← okPc_eq hΛ, ← ph2bH_eq] at h

/-- A step fact as `phOne`. -/
private theorem so (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) {l : String}
    {o z : Nat} (h : factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) ph2bH (.step l o z) = true) :
    phOne (okPcOf lo helloCells Λ) ph2bH (lab l + Int64.ofNat o) z = true := by
  obtain ⟨h1, h2⟩ := step_of_factOk hlab h
  simp only [phOne, h1, h2, beq_self_eq_true, Bool.and_self]

/-- **`abortPhThreadsOk` at `ph2bH`** with the certificate's labels. -/
theorem abortPhTH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) :
    abortPhThreadsOk (okPcOf lo helloCells Λ) ph2bH lab = true := by
  have h := facts hΛ
  simp only [abortRefTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, -⟩ := h
  have hex : lab "scc_rt_abort_threads_exit" = Int64.ofNat 4202964 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  unfold abortPhThreadsOk
  simp only [Abort.threads]
  rw [blkPh_of_factOk hlab hr0 hn0 f0, blkPh_of_factOk hlab hr0 hn0 f1, blkPh_of_factOk hlab hr0 hn0 f2,
    blkPh_of_factOk hlab hr0 hn0 f3, blkPh_of_factOk hlab hr0 hn0 f4, blkPh_of_factOk hlab hr0 hn0 f5,
    blkPh_of_factOk hlab hr0 hn0 f6, blkPh_of_factOk hlab hr0 hn0 f7, blkPh_of_factOk hlab hr0 hn0 f8,
    blkPh_of_factOk hlab hr0 hn0 f9, blkPh_of_factOk hlab hr0 hn0 f10, blkPh_of_factOk hlab hr0 hn0 f11,
    so hlab f12, blkPh_of_factOk hlab hr0 hn0 f13, so hlab f14, blkPh_of_factOk hlab hr0 hn0 f15, hex, ph2bH_eq]
  decide +kernel

/-- **The refusal path's `testq` at `.x25 + 96`** (3 bytes): its phase
check at `ph2bH`. -/
theorem refPh_tsH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) :
    phOne (okPcOf lo helloCells Λ) ph2bH (lab ".Lwc_main.x25" + Int64.ofNat 96) 3 = true := by
  have h := facts hΛ
  simp only [abortRefTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact so hlab h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The `je` block at `.x25 + 99`**: its phase check at `ph2bH`. -/
theorem refPh_jeH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) :
    blkPh (okPcOf lo helloCells Λ) ph2bH (fun _ => false) lab (lab ".Lwc_main.x25" + Int64.ofNat 99) 0 jeB =
      true := by
  have h := facts hΛ
  simp only [abortRefTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact blkPh_of_factOk hlab hr0 hn0 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **`.x26`'s block**: its phase check at `ph2bH`. -/
theorem refPh_x26H (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) :
    blkPh (okPcOf lo helloCells Λ) ph2bH (fun _ => false) lab (lab ".Lwc_main.x26" + Int64.ofNat 0) 0 x26B =
      true := by
  have h := facts hΛ
  simp only [abortRefTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact blkPh_of_factOk hlab hr0 hn0 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **`.spawnfail5`'s block**: its phase check at `ph2bH`. -/
theorem refPh_flH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) :
    blkPh (okPcOf lo helloCells Λ) ph2bH (fun _ => false) lab (lab ".Lwc_main.spawnfail5" + Int64.ofNat 0) 0 flB =
      true := by
  have h := facts hΛ
  simp only [abortRefTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact blkPh_of_factOk hlab hr0 hn0 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.abortPhTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.abortPhTH

/-- info: 'Spike.Lib.X64.HelloPh.refPh_tsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.refPh_tsH

/-- info: 'Spike.Lib.X64.HelloPh.refPh_jeH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.refPh_jeH

/-- info: 'Spike.Lib.X64.HelloPh.refPh_x26H' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.refPh_x26H

/-- info: 'Spike.Lib.X64.HelloPh.refPh_flH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.refPh_flH
