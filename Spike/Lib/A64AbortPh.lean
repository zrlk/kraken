/-
**The overflow abort path's phase check** (AArch64; A7's `abortPhC`):
`abortPhOk` (each block of the dispatcher's code 1 and of the overflow stub
`blkPh` without dead targets, each single instruction off the sites and its
next pc in its phase, the exit call's next pc in its phase), checked on the
program at A6's tables (`phOf`, `okPcOf`) and the program's code labels
(`labC`), fail-closed:

- `phOne`, `abortPhOk`: the check at any `okPc`, `ph` and labels (read by
  `Spike/Lib/A64StubW.lean`'s `stubW_sfacts`);
- `abortLabs`: the labels it reads (the path's labels and every branch
  target of its blocks); `abortPhOk_congr`: two label maps agreeing on them
  give the same check;
- `abortPhC`: at A6's phase table and sites (`false` if either is missing),
  every label of `abortLabs` resolving, `abortPhOk` at `labC`;
  `abortPhC_parts` at A6's `phOf`/`okPcOf`.

This file stays free of the segment proofs so that `PlaceOK` (A7) reads it.
-/
import Spike.Lib.LowerA64.PhCheck
import Spike.Lib.A64Abort

namespace Spike.Lib.A64.StubW

open Kraken Kraken.AArch64.Parser
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.LowerA64 (blkLabs blkPh_congr labC)
open Scc.Cert.Link.A64 (codeOf)

/-- **A single instruction at `p`** off the sites, its next pc in its phase. -/
def phOne (okPc : Nat → Bool) (ph : Nat → Nat) (p : Int64) : Bool :=
  okPc p.toBitVec.toNat && ph (p + Int64.ofNat 4).toBitVec.toNat == ph p.toBitVec.toNat

/-- **The overflow abort path's phase check**: the dispatcher's blocks at
code 1 and the stub's blocks (`blkPh` without dead targets), the stub's
single instructions (`phOne`), and the exit call's next pc in its phase
(the exit call is an abort site, so not off the sites). -/
def abortPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab "scc_rt_abort" + Int64.ofNat (4 * 0)) 0 Abort.Disp.d0 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.0_entry" + Int64.ofNat (4 * 0)) 0 Abort.Disp.t1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".L12_scc_rt_abort.1_is0" + Int64.ofNat (4 * 0)) 0 Abort.Disp.g1 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.overflow.fn + Int64.ofNat (4 * 0)) 0 Abort.b0 &&
  phOne okPc ph (lab Abort.overflow.entry + Int64.ofNat (4 * 0)) &&
  phOne okPc ph (lab Abort.overflow.entry + Int64.ofNat (4 * 1)) &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.overflow.entry + Int64.ofNat (4 * 2)) 0 Abort.b1Overflow &&
  phOne okPc ph (lab Abort.overflow.entry + Int64.ofNat (4 * 7)) &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.overflow.entry + Int64.ofNat (4 * 8)) 0 Abort.b2 &&
  ph (lab Abort.overflow.exit + Int64.ofNat 4).toBitVec.toNat == ph (lab Abort.overflow.exit).toBitVec.toNat

/-- The path's own labels `abortPhOk` reads. -/
def abortOwnLabs : List String :=
  ["scc_rt_abort", ".L12_scc_rt_abort.0_entry", ".L12_scc_rt_abort.1_is0", Abort.overflow.fn,
    Abort.overflow.entry, Abort.overflow.exit]

/-- **The labels `abortPhOk` reads**: the path's own and its blocks'
branch targets. -/
def abortLabs : List String :=
  abortOwnLabs ++ blkLabs Abort.Disp.d0 ++ blkLabs Abort.Disp.t1 ++ blkLabs Abort.Disp.g1 ++ blkLabs Abort.b0 ++
    blkLabs Abort.b1Overflow ++ blkLabs Abort.b2

/-- **`abortPhOk` reads the labels of `abortLabs` only.** -/
theorem abortPhOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ abortLabs, lab l = lab' l) : abortPhOk okPc ph lab = abortPhOk okPc ph lab' := by
  have ho : ∀ l ∈ abortOwnLabs, lab l = lab' l := fun l hl => h l (by simp only [abortLabs]; simp [hl])
  have hb : ∀ blk, blkLabs blk ⊆ abortLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl => h l (hs hl)
  unfold abortPhOk
  rw [ho "scc_rt_abort" (by simp [abortOwnLabs]), ho ".L12_scc_rt_abort.0_entry" (by simp [abortOwnLabs]),
    ho ".L12_scc_rt_abort.1_is0" (by simp [abortOwnLabs]), ho Abort.overflow.fn (by simp [abortOwnLabs]),
    ho Abort.overflow.entry (by simp [abortOwnLabs]), ho Abort.overflow.exit (by simp [abortOwnLabs]),
    blkPh_congr (hb _ fun l hl => by simp only [abortLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t1 fun l hl => by simp only [abortLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.g1 fun l hl => by simp only [abortLabs]; simp [hl]),
    blkPh_congr (hb Abort.b0 fun l hl => by simp only [abortLabs]; simp [hl]),
    blkPh_congr (hb Abort.b1Overflow fun l hl => by simp only [abortLabs]; simp [hl]),
    blkPh_congr (hb Abort.b2 fun l hl => by simp only [abortLabs]; simp [hl])]

/-- **A7's phase part**: at A6's phase table and sites of the program at
`lo` (`false` if either is missing) and its code labels, every label the
check reads resolving, the overflow abort path's phase check. -/
def abortPhC (lo : Nat) (Λ : Scc.Sem.Layout) (prog : Program) : Bool :=
  match Scc.Cert.Rt.A64.phTabOf lo prog, Scc.Cert.Rt.A64.sitesOf lo prog Λ with
  | some T, some ss =>
    abortLabs.all (fun l => (codeOf lo prog l).isSome) && abortPhOk (fun pc => !ss.contains pc) T.ph (labC lo prog)
  | _, _ => false

/-- **`abortPhC`'s parts** at A6's `phOf`/`okPcOf`. -/
theorem abortPhC_parts {lo : Nat} {Λ : Scc.Sem.Layout} {prog : Program} (h : abortPhC lo Λ prog = true) :
    (∀ l ∈ abortLabs, (codeOf lo prog l).isSome = true) ∧
      abortPhOk (Scc.Cert.Rt.A64.okPcOf lo prog Λ) (Scc.Cert.Rt.A64.phOf lo prog) (labC lo prog) = true := by
  unfold abortPhC at h
  split at h
  · next T ss hT hs =>
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    have hph : Scc.Cert.Rt.A64.phOf lo prog = T.ph := by unfold Scc.Cert.Rt.A64.phOf; rw [hT]
    have hok : Scc.Cert.Rt.A64.okPcOf lo prog Λ = fun pc => !ss.contains pc := by
      funext pc; unfold Scc.Cert.Rt.A64.okPcOf; rw [hs]
    rw [hph, hok]
    exact h
  · cases h

/-- **`abortPhOk` at any labels agreeing with the code labels** where they
resolve, from `abortPhC`. -/
theorem abortPhOk_of_abortPhC {lo : Nat} {Λ : Scc.Sem.Layout} {prog : Program} (h : abortPhC lo Λ prog = true)
    {lab : Label → Int64} (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a) :
    abortPhOk (Scc.Cert.Rt.A64.okPcOf lo prog Λ) (Scc.Cert.Rt.A64.phOf lo prog) lab = true := by
  obtain ⟨hres, hph⟩ := abortPhC_parts h
  rw [abortPhOk_congr (lab' := labC lo prog) fun l hl => ?_]
  · exact hph
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hres l hl)
    rw [hlab l a ha, labC, ha]
    rfl

end Spike.Lib.A64.StubW
