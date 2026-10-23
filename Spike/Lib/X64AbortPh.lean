/-
**The overflow abort path's phase check** (x86-64; A7's `abortPhC`): the
twin of `Spike/Lib/A64AbortPh.lean`. `abortPhOk` (each block of the
dispatcher's code 1 and of the overflow stub `blkPh` without dead targets,
each single instruction off the sites and its next pc in its phase, the
exit call's next pc in its phase), checked on the cells at A6's tables
(`phOf`, `okPcOf`) and the cells' code labels (`labC`), fail-closed:

- `phOne`, `abortPhOk`: the check at any `okPc`, `ph` and labels (read by
  `Spike/Lib/X64StubW.lean`'s `stubW_sfacts`);
- `abortLabs`: the labels it reads (the path's labels and every branch
  target of its blocks); `abortPhOk_congr`: two label maps agreeing on them
  give the same check;
- `abortPhC`: at A6's phase table and sites (`false` if either is missing),
  every label of `abortLabs` resolving, `abortPhOk` at `labC`;
  `abortPhC_parts` at A6's `phOf`/`okPcOf`.

**Unlike AArch64**: instructions have sizes (`phOne` takes the size).

This file stays free of the segment proofs so that `PlaceOK` (A7) reads it.
-/
import Spike.Lib.LowerX64.PhCheck
import Spike.Lib.X64Abort

namespace Spike.Lib.X64.StubW

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.LowerX64 (blkLabs blkPh_congr labC)
open Scc.Sem.X64 (codeLabel)

/-- **A single instruction of `z` bytes at `p`** off the sites, its next pc
in its phase. -/
def phOne (okPc : Nat → Bool) (ph : Nat → Nat) (p : Int64) (z : Nat) : Bool :=
  okPc p.toBitVec.toNat && ph (p + Int64.ofNat z).toBitVec.toNat == ph p.toBitVec.toNat

/-- **The overflow abort path's phase check**: the dispatcher's blocks at
code 1 and the stub's blocks (`blkPh` without dead targets), the stub's
single instructions (`phOne`: the `leaq` and the `write` call), and the
exit call's next pc in its phase (the exit call is an abort site, so not
off the sites). -/
def abortPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab "scc_rt_abort" + Int64.ofNat 0) 0 Abort.Disp.d0 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.entry" + Int64.ofNat 0) 0 Abort.Disp.t1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_abort.is0" + Int64.ofNat 0) 0 Abort.Disp.g1 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.overflow.fn + Int64.ofNat 0) 0 Abort.x0 &&
  phOne okPc ph (lab Abort.overflow.entry + Int64.ofNat 0) 7 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.overflow.entry + Int64.ofNat 7) 0 Abort.x1Overflow &&
  phOne okPc ph (lab Abort.overflow.entry + Int64.ofNat 34) 2 &&
  blkPh okPc ph (fun _ => false) lab (lab Abort.overflow.entry + Int64.ofNat 36) 0 Abort.x2 &&
  ph (lab Abort.overflow.exit + Int64.ofNat 2).toBitVec.toNat == ph (lab Abort.overflow.exit).toBitVec.toNat

/-- The path's own labels `abortPhOk` reads. -/
def abortOwnLabs : List String :=
  ["scc_rt_abort", ".Lscc_rt_abort.entry", ".Lscc_rt_abort.is0", Abort.overflow.fn, Abort.overflow.entry,
    Abort.overflow.exit]

/-- **The labels `abortPhOk` reads**: the path's own and its blocks'
branch targets. -/
def abortLabs : List String :=
  abortOwnLabs ++ blkLabs Abort.Disp.d0 ++ blkLabs Abort.Disp.t1 ++ blkLabs Abort.Disp.g1 ++ blkLabs Abort.x0 ++
    blkLabs Abort.x1Overflow ++ blkLabs Abort.x2

/-- **`abortPhOk` reads the labels of `abortLabs` only.** -/
theorem abortPhOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ abortLabs, lab l = lab' l) : abortPhOk okPc ph lab = abortPhOk okPc ph lab' := by
  have ho : ∀ l ∈ abortOwnLabs, lab l = lab' l := fun l hl => h l (by simp only [abortLabs]; simp [hl])
  have hb : ∀ blk, blkLabs blk ⊆ abortLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl => h l (hs hl)
  unfold abortPhOk
  rw [ho "scc_rt_abort" (by simp [abortOwnLabs]), ho ".Lscc_rt_abort.entry" (by simp [abortOwnLabs]),
    ho ".Lscc_rt_abort.is0" (by simp [abortOwnLabs]), ho Abort.overflow.fn (by simp [abortOwnLabs]),
    ho Abort.overflow.entry (by simp [abortOwnLabs]), ho Abort.overflow.exit (by simp [abortOwnLabs]),
    blkPh_congr (hb Abort.Disp.d0 fun l hl => by simp only [abortLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.t1 fun l hl => by simp only [abortLabs]; simp [hl]),
    blkPh_congr (hb Abort.Disp.g1 fun l hl => by simp only [abortLabs]; simp [hl]),
    blkPh_congr (hb Abort.x0 fun l hl => by simp only [abortLabs]; simp [hl]),
    blkPh_congr (hb Abort.x1Overflow fun l hl => by simp only [abortLabs]; simp [hl]),
    blkPh_congr (hb Abort.x2 fun l hl => by simp only [abortLabs]; simp [hl])]

/-- **A7's phase part**: at A6's phase table and sites of the cells at `lo`
(`false` if either is missing) and their code labels, every label the check
reads resolving, the overflow abort path's phase check. -/
def abortPhC (lo : Nat) (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) : Bool :=
  match Scc.Cert.Rt.X64.phTabOf lo cells, Scc.Cert.Rt.X64.sitesOf lo cells Λ with
  | some T, some ss =>
    abortLabs.all (fun l => (codeLabel lo cells l).isSome) &&
      abortPhOk (fun pc => !ss.contains pc) T.ph (labC lo cells)
  | _, _ => false

/-- **`abortPhC`'s parts** at A6's `phOf`/`okPcOf`. -/
theorem abortPhC_parts {lo : Nat} {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)}
    (h : abortPhC lo Λ cells = true) :
    (∀ l ∈ abortLabs, (codeLabel lo cells l).isSome = true) ∧
      abortPhOk (Scc.Cert.Rt.X64.okPcOf lo cells Λ) (Scc.Cert.Rt.X64.phOf lo cells) (labC lo cells) = true := by
  unfold abortPhC at h
  split at h
  · next T ss hT hs =>
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    have hph : Scc.Cert.Rt.X64.phOf lo cells = T.ph := by unfold Scc.Cert.Rt.X64.phOf; rw [hT]
    have hok : Scc.Cert.Rt.X64.okPcOf lo cells Λ = fun pc => !ss.contains pc := by
      funext pc; unfold Scc.Cert.Rt.X64.okPcOf; rw [hs]
    rw [hph, hok]
    exact h
  · cases h

/-- **`abortPhOk` at any labels agreeing with the code labels** where they
resolve, from `abortPhC`. -/
theorem abortPhOk_of_abortPhC {lo : Nat} {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)}
    (h : abortPhC lo Λ cells = true) {lab : Label → Int64}
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a) :
    abortPhOk (Scc.Cert.Rt.X64.okPcOf lo cells Λ) (Scc.Cert.Rt.X64.phOf lo cells) lab = true := by
  obtain ⟨hres, hph⟩ := abortPhC_parts h
  rw [abortPhOk_congr (lab' := labC lo cells) fun l hl => ?_]
  · exact hph
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hres l hl)
    rw [hlab l a ha, labC, ha]
    rfl

end Spike.Lib.X64.StubW
