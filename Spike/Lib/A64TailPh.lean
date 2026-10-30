/-
**The write tail's phase check** (AArch64; A7's `tailOffC`): every pc a
program's write tail can reach from `scc_rt_print` is off the sites and in
its phase. `printPhOk` covers `scc_rt_print` (each block `blkPh` without
dead targets, the `write` call `phOne`, the `ret`'s pc off the sites, its
target not checked: the return address is the caller's);
`abortPhWriteOk` (`Spike/Lib/A64AbortPhW.lean`) the dispatcher at code 4
and the write stub (`print`'s abort call); `abortPhHeapOk`
(`Spike/Lib/A64AbortPhH.lean`) the dispatcher at code 2 and the heap stub
(the allocator's abort call); `allocPhOk` (`Spike/Lib/A64AllocPh.lean`)
`scc_rt_alloc` (each block, the single instructions, the `ret`'s pc); `allocAbOk`
(`Spike/Lib/A64AllocAbOk.lean`) `scc_rt_alloc`'s targets off the write abort's pcs
(labels only). All are checked on the program at A6's tables
(`phOf`, `okPcOf`) and the program's code labels (`labC`), fail-closed:

- `printPhOk`, `tailPhOk`: the checks at any `okPc`, `ph` and labels;
  `scc_rt_print`'s write block is led by the barrier `dmb ish` (every
  AArch64 program, `Runtime.printF`): `tailPhOk` checks the barrier's pc
  (`phOne` at `writeL`) and `printPhOk` at `fenceLab`, the labels with
  `writeL` one instruction on;
- `printLabs`, `tailLabs`: the labels they read; `printPhOk_congr`,
  `tailPhOk_congr`: two label maps agreeing on them give the same check;
- `tailOffC`: at A6's phase table and sites (`false` if either is
  missing), every label of `tailLabs` resolving, `tailPhOk` at `labC`;
  `tailOffC_parts` at A6's `phOf`/`okPcOf`; `tailPhOk_of_tailOffC` at any
  labels agreeing with the code labels where they resolve.

A site's cell is checked nowhere else, and a pc at a label's offset 0 can
be a site's when the site's label sits right before it: this check rules
it out for the tail's pcs.

Like `A64AbortPh`, this file stays free of the segment proofs so that
`PlaceOK` (A7) reads it.
-/
import Spike.Lib.A64AbortPhW
import Spike.Lib.A64AbortPhH
import Spike.Lib.A64AllocPh
import Spike.Lib.A64AllocAbOk
import Spike.Lib.A64Print

namespace Spike.Lib.A64.StubW

open Kraken Kraken.AArch64.Parser
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.LowerA64 (blkLabs blkPh_congr labC)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.AllocG (allocPhOk allocLabs allocPhOk_congr allocAbOk allocAbLabs allocAbOk_congr)

/-- **`scc_rt_print`'s phase check**: its blocks (`blkPh` without dead
targets; the epilogue `b16` without its `ret`), the `write` call
(`phOne`), and the `ret`'s pc off the sites (its target, the caller's
return address, is not a label). -/
def printPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab "scc_rt_print" + Int64.ofNat (4 * 0)) 0 Print.b0 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.0_entry" + Int64.ofNat (4 * 0)) 0 Print.b1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.1_loop" + Int64.ofNat (4 * 0)) 0 Print.b2 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.1_loop" + Int64.ofNat (4 * 4)) 0 Print.b3 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.2_write" + Int64.ofNat (4 * 0)) 0 Print.b4 &&
  phOne okPc ph (lab ".L9_scc_rt_print.2_write" + Int64.ofNat (4 * 4)) &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.2_write" + Int64.ofNat (4 * 5)) 0 Print.b5 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.2_write" + Int64.ofNat (4 * 12)) 0 Print.b6 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.2_write" + Int64.ofNat (4 * 13)) 0 Print.b7 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.3_chk2" + Int64.ofNat (4 * 0)) 0 Print.b8 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.3_chk2" + Int64.ofNat (4 * 6)) 0 Print.b9 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.3_chk2" + Int64.ofNat (4 * 7)) 0 Print.b10 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.4_chk3" + Int64.ofNat (4 * 0)) 0 Print.b11 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.4_chk3" + Int64.ofNat (4 * 4)) 0 Print.b12 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.5_adv" + Int64.ofNat (4 * 0)) 0 Print.b13 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.6_fail" + Int64.ofNat (4 * 0)) 0 Print.b14 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L9_scc_rt_print.7_done" + Int64.ofNat (4 * 0)) 0 (Print.b16.take 3) &&
  okPc (lab ".L9_scc_rt_print.7_done" + Int64.ofNat (4 * 3)).toBitVec.toNat

/-- The function's own labels `printPhOk` reads. -/
def printOwnLabs : List String :=
  ["scc_rt_print", ".L9_scc_rt_print.0_entry", ".L9_scc_rt_print.1_loop", ".L9_scc_rt_print.2_write",
    ".L9_scc_rt_print.3_chk2", ".L9_scc_rt_print.4_chk3", ".L9_scc_rt_print.5_adv", ".L9_scc_rt_print.6_fail",
    ".L9_scc_rt_print.7_done"]

/-- **The labels `printPhOk` reads**: the function's own and its blocks'
branch and call targets. -/
def printLabs : List String :=
  printOwnLabs ++ blkLabs Print.b0 ++ blkLabs Print.b1 ++ blkLabs Print.b2 ++ blkLabs Print.b3 ++
    blkLabs Print.b4 ++ blkLabs Print.b5 ++ blkLabs Print.b6 ++ blkLabs Print.b7 ++ blkLabs Print.b8 ++
    blkLabs Print.b9 ++ blkLabs Print.b10 ++ blkLabs Print.b11 ++ blkLabs Print.b12 ++ blkLabs Print.b13 ++
    blkLabs Print.b14 ++ blkLabs (Print.b16.take 3)

/-- **`printPhOk` reads the labels of `printLabs` only.** -/
theorem printPhOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ printLabs, lab l = lab' l) : printPhOk okPc ph lab = printPhOk okPc ph lab' := by
  have ho : ∀ l ∈ printOwnLabs, lab l = lab' l := fun l hl => h l (by simp only [printLabs]; simp [hl])
  have hb : ∀ blk, blkLabs blk ⊆ printLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl => h l (hs hl)
  unfold printPhOk
  rw [ho "scc_rt_print" (by simp [printOwnLabs]), ho ".L9_scc_rt_print.0_entry" (by simp [printOwnLabs]),
    ho ".L9_scc_rt_print.1_loop" (by simp [printOwnLabs]), ho ".L9_scc_rt_print.2_write" (by simp [printOwnLabs]),
    ho ".L9_scc_rt_print.3_chk2" (by simp [printOwnLabs]), ho ".L9_scc_rt_print.4_chk3" (by simp [printOwnLabs]),
    ho ".L9_scc_rt_print.5_adv" (by simp [printOwnLabs]), ho ".L9_scc_rt_print.6_fail" (by simp [printOwnLabs]),
    ho ".L9_scc_rt_print.7_done" (by simp [printOwnLabs]),
    blkPh_congr (hb Print.b0 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b1 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b2 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b3 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b4 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b5 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b6 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b7 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b8 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b9 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b10 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b11 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b12 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b13 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.b14 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb (Print.b16.take 3) fun l hl => by simp only [printLabs]; simp [hl])]

/-- The write block's label, led by the barrier (`Print.bF`). -/
abbrev writeL : Label := ".L9_scc_rt_print.2_write"

/-- **The labels one instruction on at the write block** (`writeL`): the
body's checks (`printPhOk`, `allocAbOk`) read at them the write's pcs past
the barrier. -/
def fenceLab (lab : Label → Int64) (l : Label) : Int64 :=
  if l = writeL then lab l + 4 else lab l

/-- `fenceLab` of two label maps agreeing at a label agree there. -/
theorem fenceLab_congr {lab lab' : Label → Int64} {l : Label} (h : lab l = lab' l) :
    fenceLab lab l = fenceLab lab' l := by
  unfold fenceLab; rw [h]

/-- **The runtime routines' phase check**: `scc_rt_print`'s (the barrier,
`phOne` at `writeL`, and `printPhOk` at `fenceLab`: the write block one on,
`b3`'s branch to `writeL` read there one on, in the barrier's phase), the
write abort path's, the heap abort path's and `scc_rt_alloc`'s, and
`scc_rt_alloc`'s targets off the write abort's pcs at `fenceLab` (its pcs
past the system call one on). -/
def tailPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  phOne okPc ph (lab writeL) && printPhOk okPc ph (fenceLab lab) && abortPhWriteOk okPc ph lab &&
    abortPhHeapOk okPc ph lab && allocPhOk okPc ph lab && allocAbOk (fenceLab lab)

/-- **The labels `tailPhOk` reads.** -/
def tailLabs : List String :=
  printLabs ++ abortWriteLabs ++ abortHeapLabs ++ allocLabs ++ allocAbLabs

/-- **`tailPhOk` reads the labels of `tailLabs` only.** -/
theorem tailPhOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ tailLabs, lab l = lab' l) : tailPhOk okPc ph lab = tailPhOk okPc ph lab' := by
  have hw : writeL ∈ tailLabs := by simp [tailLabs, printLabs, printOwnLabs]
  unfold tailPhOk
  rw [h writeL hw,
    printPhOk_congr fun l hl => fenceLab_congr (h l (by simp [tailLabs, hl])),
    abortPhWriteOk_congr fun l hl => h l (by simp [tailLabs, hl]),
    abortPhHeapOk_congr fun l hl => h l (by simp [tailLabs, hl]),
    allocPhOk_congr fun l hl => h l (by simp [tailLabs, hl]),
    allocAbOk_congr fun l hl => fenceLab_congr (h l (by simp [tailLabs, hl]))]

section Parts

variable {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} (h : tailPhOk okPc ph lab = true)
include h

/-- `tailPhOk`'s barrier part. -/
theorem fencePh_of_tailPhOk : phOne okPc ph (lab writeL) = true := by
  simp only [tailPhOk, Bool.and_eq_true] at h; exact h.1.1.1.1.1

/-- `tailPhOk`'s `scc_rt_print` part, at `fenceLab`. -/
theorem printPhOk_of_tailPhOk : printPhOk okPc ph (fenceLab lab) = true := by
  simp only [tailPhOk, Bool.and_eq_true] at h; exact h.1.1.1.1.2

/-- `tailPhOk`'s write abort part. -/
theorem abortPhWriteOk_of_tailPhOk : abortPhWriteOk okPc ph lab = true := by
  simp only [tailPhOk, Bool.and_eq_true] at h; exact h.1.1.1.2

/-- `tailPhOk`'s heap abort part. -/
theorem abortPhHeapOk_of_tailPhOk : abortPhHeapOk okPc ph lab = true := by
  simp only [tailPhOk, Bool.and_eq_true] at h; exact h.1.1.2

/-- `tailPhOk`'s `scc_rt_alloc` phase part. -/
theorem allocPhOk_of_tailPhOk : allocPhOk okPc ph lab = true := by
  simp only [tailPhOk, Bool.and_eq_true] at h; exact h.1.2

/-- `tailPhOk`'s `scc_rt_alloc` target part, at `fenceLab`. -/
theorem allocAbOk_of_tailPhOk : allocAbOk (fenceLab lab) = true := by
  simp only [tailPhOk, Bool.and_eq_true] at h; exact h.2

end Parts

/-- **A7's write tail part**: at A6's phase table and sites of the program
at `lo` (`false` if either is missing) and its code labels, every label the
check reads resolving, the write tail's phase check. -/
def tailOffC (lo : Nat) (Λ : Scc.Sem.Layout) (prog : Program) : Bool :=
  match Scc.Cert.Rt.A64.phTabOf lo prog, Scc.Cert.Rt.A64.sitesOf lo prog Λ with
  | some T, some ss =>
    tailLabs.all (fun l => (codeOf lo prog l).isSome) && tailPhOk (fun pc => !ss.contains pc) T.ph (labC lo prog)
  | _, _ => false

/-- **`tailOffC`'s parts** at A6's `phOf`/`okPcOf`. -/
theorem tailOffC_parts {lo : Nat} {Λ : Scc.Sem.Layout} {prog : Program} (h : tailOffC lo Λ prog = true) :
    (∀ l ∈ tailLabs, (codeOf lo prog l).isSome = true) ∧
      tailPhOk (Scc.Cert.Rt.A64.okPcOf lo prog Λ) (Scc.Cert.Rt.A64.phOf lo prog) (labC lo prog) = true := by
  unfold tailOffC at h
  split at h
  · next T ss hT hs =>
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    have hph : Scc.Cert.Rt.A64.phOf lo prog = T.ph := by unfold Scc.Cert.Rt.A64.phOf; rw [hT]
    have hok : Scc.Cert.Rt.A64.okPcOf lo prog Λ = fun pc => !ss.contains pc := by
      funext pc; unfold Scc.Cert.Rt.A64.okPcOf; rw [hs]
    rw [hph, hok]
    exact h
  · cases h

/-- **`tailPhOk` at any labels agreeing with the code labels** where they
resolve, from `tailOffC`. -/
theorem tailPhOk_of_tailOffC {lo : Nat} {Λ : Scc.Sem.Layout} {prog : Program} (h : tailOffC lo Λ prog = true)
    {lab : Label → Int64} (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a) :
    tailPhOk (Scc.Cert.Rt.A64.okPcOf lo prog Λ) (Scc.Cert.Rt.A64.phOf lo prog) lab = true := by
  obtain ⟨hres, hph⟩ := tailOffC_parts h
  rw [tailPhOk_congr (lab' := labC lo prog) fun l hl => ?_]
  · exact hph
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hres l hl)
    rw [hlab l a ha, labC, ha]
    rfl

end Spike.Lib.A64.StubW
