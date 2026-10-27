/-
**The runtime routines' phase check** (x86-64; A7's `tailOffC`): every pc
of the runtime routines a program's code calls after the thread start (a
write tail from `scc_rt_print`, an allocation) is off the sites and in its
phase. `printPhOk` covers `scc_rt_print` (each block `blkPh` without dead
targets, the `write` call `phOne`, the `ret`'s pc off the sites and in the entry's
phase, its target not checked: the return address is the caller's, which
the call's own check puts in the entry's phase); `abortPhWriteOk`
(`Spike/Lib/X64AbortPhW.lean`) the dispatcher at code 4 and the write stub
(`print`'s abort call); `abortPhHeapOk` (`Spike/Lib/X64AbortPhH.lean`) the
dispatcher at code 2 and the heap stub (the allocator's abort call);
`AllocG.allocPhOk` (`Spike/Lib/X64AllocPh.lean`) `scc_rt_alloc` (the slow
path's `.spin`, in no block of the code check, in its phase as a branch
target), with its targets off the write abort path's pcs
(`AllocG.allocAbOk`, `Spike/Lib/X64AllocAbOk.lean`: `.spin` is placed by no
code check). All are checked on the cells at A6's tables
(`phOf`, `okPcOf`) and the cells' code labels (`labC`), fail-closed:

- `printPhOk`, `tailPhOk`: the checks at any `okPc`, `ph` and labels;
- `printLabs`, `tailLabs`: the labels they read; `printPhOk_congr`,
  `tailPhOk_congr`: two label maps agreeing on them give the same check;
- `tailOffC`: at A6's phase table and sites (`false` if either is
  missing), every label of `tailLabs` resolving, `tailPhOk` at `labC`;
  `tailOffC_parts` at A6's `phOf`/`okPcOf`; `tailPhOk_of_tailOffC` at any
  labels agreeing with the code labels where they resolve.

No other component gives these: a site's cell is checked nowhere else (a
pc at a label's offset 0 can be a site's when the site's label sits right
before it), and no component orders these routines' labels against the
phase ranges' bounds.

Like `X64AbortPh`, this file stays free of the segment proofs so that
`PlaceOK` (A7) reads it.
-/
import Spike.Lib.X64AbortPhW
import Spike.Lib.X64AbortPhH
import Spike.Lib.X64Print
import Spike.Lib.X64AllocAbOk

namespace Spike.Lib.X64.StubW

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.LowerX64 (blkLabs blkPh_congr labC)
open Scc.Sem.X64 (codeLabel)

/-- **`scc_rt_print`'s phase check**: its blocks (`blkPh` without dead
targets; the epilogue `x13` without its `ret`), the `write` call
(`phOne`), and the `ret`'s pc off the sites and in the function's entry
phase (its target, the caller's return address, is not a label: a call's
own check puts it in the callee's entry phase). -/
def printPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab "scc_rt_print" + Int64.ofNat 0) 0 Print.x0 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.entry" + Int64.ofNat 0) 0 Print.x1 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.loop" + Int64.ofNat 0) 0 Print.x2 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.loop" + Int64.ofNat 20) 0 Print.x3 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.write" + Int64.ofNat 0) 0 Print.x4 &&
  phOne okPc ph (lab ".Lscc_rt_print.write" + Int64.ofNat 20) 2 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.write" + Int64.ofNat 22) 0 Print.x5 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.write" + Int64.ofNat 42) 0 Print.x6 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.chk2" + Int64.ofNat 0) 0 Print.x7 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.chk2" + Int64.ofNat 16) 0 Print.x8 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.chk3" + Int64.ofNat 0) 0 Print.x9 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.chk3" + Int64.ofNat 16) 0 Print.x10 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.adv" + Int64.ofNat 0) 0 Print.x11 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.fail" + Int64.ofNat 0) 0 Print.x12 &&
  blkPh okPc ph (fun _ => false) lab (lab ".Lscc_rt_print.done" + Int64.ofNat 0) 0 (Print.x13.take 2) &&
  okPc (lab ".Lscc_rt_print.done" + Int64.ofNat 4).toBitVec.toNat &&
  ph (lab ".Lscc_rt_print.done" + Int64.ofNat 4).toBitVec.toNat == ph (lab "scc_rt_print").toBitVec.toNat

/-- The function's own labels `printPhOk` reads. -/
def printOwnLabs : List String :=
  ["scc_rt_print", ".Lscc_rt_print.entry", ".Lscc_rt_print.loop", ".Lscc_rt_print.write", ".Lscc_rt_print.chk2",
    ".Lscc_rt_print.chk3", ".Lscc_rt_print.adv", ".Lscc_rt_print.fail", ".Lscc_rt_print.done"]

/-- **The labels `printPhOk` reads**: the function's own and its blocks'
branch and call targets. -/
def printLabs : List String :=
  printOwnLabs ++ blkLabs Print.x0 ++ blkLabs Print.x1 ++ blkLabs Print.x2 ++ blkLabs Print.x3 ++
    blkLabs Print.x4 ++ blkLabs Print.x5 ++ blkLabs Print.x6 ++ blkLabs Print.x7 ++ blkLabs Print.x8 ++
    blkLabs Print.x9 ++ blkLabs Print.x10 ++ blkLabs Print.x11 ++ blkLabs Print.x12 ++
    blkLabs (Print.x13.take 2)

/-- **`printPhOk` reads the labels of `printLabs` only.** -/
theorem printPhOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ printLabs, lab l = lab' l) : printPhOk okPc ph lab = printPhOk okPc ph lab' := by
  have ho : ∀ l ∈ printOwnLabs, lab l = lab' l := fun l hl => h l (by simp only [printLabs]; simp [hl])
  have hb : ∀ blk, blkLabs blk ⊆ printLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl => h l (hs hl)
  unfold printPhOk
  rw [ho "scc_rt_print" (by simp [printOwnLabs]), ho ".Lscc_rt_print.entry" (by simp [printOwnLabs]),
    ho ".Lscc_rt_print.loop" (by simp [printOwnLabs]), ho ".Lscc_rt_print.write" (by simp [printOwnLabs]),
    ho ".Lscc_rt_print.chk2" (by simp [printOwnLabs]), ho ".Lscc_rt_print.chk3" (by simp [printOwnLabs]),
    ho ".Lscc_rt_print.adv" (by simp [printOwnLabs]), ho ".Lscc_rt_print.fail" (by simp [printOwnLabs]),
    ho ".Lscc_rt_print.done" (by simp [printOwnLabs]),
    blkPh_congr (hb Print.x0 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x1 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x2 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x3 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x4 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x5 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x6 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x7 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x8 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x9 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x10 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x11 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb Print.x12 fun l hl => by simp only [printLabs]; simp [hl]),
    blkPh_congr (hb (Print.x13.take 2) fun l hl => by simp only [printLabs]; simp [hl])]

/-- **The runtime routines' phase check**: `scc_rt_print`'s, the write
abort path's, the heap abort path's and `scc_rt_alloc`'s, and
`scc_rt_alloc`'s targets off the write abort path's pcs. -/
def tailPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  printPhOk okPc ph lab && abortPhWriteOk okPc ph lab && abortPhHeapOk okPc ph lab &&
    AllocG.allocPhOk okPc ph lab && AllocG.allocAbOk lab

/-- **The labels `tailPhOk` reads.** -/
def tailLabs : List String :=
  printLabs ++ abortWriteLabs ++ abortHeapLabs ++ AllocG.allocLabs ++ AllocG.allocAbLabs

/-- **`tailPhOk` reads the labels of `tailLabs` only.** -/
theorem tailPhOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ tailLabs, lab l = lab' l) : tailPhOk okPc ph lab = tailPhOk okPc ph lab' := by
  unfold tailPhOk
  rw [printPhOk_congr fun l hl => h l (by simp [tailLabs, hl]),
    abortPhWriteOk_congr fun l hl => h l (by simp [tailLabs, hl]),
    abortPhHeapOk_congr fun l hl => h l (by simp [tailLabs, hl]),
    AllocG.allocPhOk_congr fun l hl => h l (by simp [tailLabs, hl]),
    AllocG.allocAbOk_congr fun l hl => h l (by simp [tailLabs, hl])]

/-- **A7's write tail part**: at A6's phase table and sites of the cells at
`lo` (`false` if either is missing) and their code labels, every label the
check reads resolving, the write tail's phase check. -/
def tailOffC (lo : Nat) (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) : Bool :=
  match Scc.Cert.Rt.X64.phTabOf lo cells, Scc.Cert.Rt.X64.sitesOf lo cells Λ with
  | some T, some ss =>
    tailLabs.all (fun l => (codeLabel lo cells l).isSome) &&
      tailPhOk (fun pc => !ss.contains pc) T.ph (labC lo cells)
  | _, _ => false

/-- **`tailOffC`'s parts** at A6's `phOf`/`okPcOf`. -/
theorem tailOffC_parts {lo : Nat} {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)}
    (h : tailOffC lo Λ cells = true) :
    (∀ l ∈ tailLabs, (codeLabel lo cells l).isSome = true) ∧
      tailPhOk (Scc.Cert.Rt.X64.okPcOf lo cells Λ) (Scc.Cert.Rt.X64.phOf lo cells) (labC lo cells) = true := by
  unfold tailOffC at h
  split at h
  · next T ss hT hs =>
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    have hph : Scc.Cert.Rt.X64.phOf lo cells = T.ph := by unfold Scc.Cert.Rt.X64.phOf; rw [hT]
    have hok : Scc.Cert.Rt.X64.okPcOf lo cells Λ = fun pc => !ss.contains pc := by
      funext pc; unfold Scc.Cert.Rt.X64.okPcOf; rw [hs]
    rw [hph, hok]
    exact h
  · cases h

/-- **`tailPhOk` at any labels agreeing with the code labels** where they
resolve, from `tailOffC`. -/
theorem tailPhOk_of_tailOffC {lo : Nat} {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)}
    (h : tailOffC lo Λ cells = true) {lab : Label → Int64}
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a) :
    tailPhOk (Scc.Cert.Rt.X64.okPcOf lo cells Λ) (Scc.Cert.Rt.X64.phOf lo cells) lab = true := by
  obtain ⟨hres, hph⟩ := tailOffC_parts h
  rw [tailPhOk_congr (lab' := labC lo cells) fun l hl => ?_]
  · exact hph
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hres l hl)
    rw [hlab l a ha, labC, ha]
    rfl

end Spike.Lib.X64.StubW
