/-
**`scc_rt_alloc`'s phase check** (x86-64; read by A7's `tailOffC`), the twin
of `Spike/Lib/A64AllocPh.lean`: `allocPhOk` (each block of `Alloc.allocIn`
`blkPh` without dead targets, each single instruction off the sites and its
next pc in its phase, the `ret` off the sites and in the phase of the
function's entry), at any `okPc`, `ph` and labels:

- `allocPhOk`: the check. The `ret`'s target is its caller's return address,
  not checked here: a call site gives the return address in the phase of
  `scc_rt_alloc`'s entry (its `call`'s target), and the check gives the
  `ret`'s pc in that phase, so the two meet without a walk along the
  function's edges.
- `allocLabs`: the labels it reads (the function's labels and every branch
  target of its blocks); `allocPhOk_congr`: two label maps agreeing on them
  give the same check.

This file stays free of the segment proofs so that `PlaceOK` (A7) reads it.
-/
import Spike.Lib.X64AbortPh
import Scc.Cert.Rt.X64AllocIn

namespace Spike.Lib.X64.AllocG

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.LowerX64 (blkLabs blkPh_congr)
open Spike.Lib.X64.StubW (phOne)
open Spike.Lib.X64.Alloc

/-- A block of `scc_rt_alloc` at `l + off`, without dead targets. -/
abbrev aBlk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (l : Label) (off : Nat)
    (blk : List (Directive × Nat)) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab l + Int64.ofNat off) 0 blk

/-- **`scc_rt_alloc`'s phase check**: its blocks (`blkPh` without dead
targets), its single instructions (`phOne`), and its `ret` off the sites
and in the phase of the function's entry. -/
def allocPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Bool :=
  aBlk okPc ph lab fnL 0 bPro && aBlk okPc ph lab entryL 0 bChk && aBlk okPc ph lab entryL 16 bJ1 &&
  phOne okPc ph (lab cntL + Int64.ofNat 0) 7 && aBlk okPc ph lab cntL 7 bC1 &&
  phOne okPc ph (lab cntL + Int64.ofNat 19) 5 && aBlk okPc ph lab cntL 24 bC2 && aBlk okPc ph lab cntL 59 bJ2 &&
  aBlk okPc ph lab slowL 0 bSlow && aBlk okPc ph lab slowL 16 bJ3 && aBlk okPc ph lab fullL 0 bFull &&
  aBlk okPc ph lab okL 0 bO0 && phOne okPc ph (lab okL + Int64.ofNat 11) 3 && aBlk okPc ph lab okL 14 bO1 &&
  phOne okPc ph (lab okL + Int64.ofNat 29) 3 && aBlk okPc ph lab okL 32 bO2 &&
  phOne okPc ph (lab okL + Int64.ofNat 36) 7 && aBlk okPc ph lab okL 43 bO3 &&
  phOne okPc ph (lab okL + Int64.ofNat 58) 3 && aBlk okPc ph lab okL 61 bO4 &&
  phOne okPc ph (lab okL + Int64.ofNat 88) 4 && aBlk okPc ph lab okL 92 bO5 &&
  phOne okPc ph (lab okL + Int64.ofNat 107) 3 && aBlk okPc ph lab okL 110 bO6 &&
  phOne okPc ph (lab okL + Int64.ofNat 125) 3 && aBlk okPc ph lab okL 128 bO7 &&
  phOne okPc ph (lab okL + Int64.ofNat 140) 3 && aBlk okPc ph lab okL 143 bO8 &&
  phOne okPc ph (lab okL + Int64.ofNat 170) 3 && aBlk okPc ph lab okL 173 bO9 &&
  okPc (lab okL + Int64.ofNat 226).toBitVec.toNat &&
  ph (lab okL + Int64.ofNat 226).toBitVec.toNat == ph (lab fnL).toBitVec.toNat

/-- The function's own labels `allocPhOk` reads. -/
def allocOwnLabs : List String := [fnL, entryL, cntL, slowL, fullL, okL]

/-- **The labels `allocPhOk` reads**: the function's own and its blocks'
branch targets. -/
def allocLabs : List String :=
  allocOwnLabs ++ blkLabs bPro ++ blkLabs bChk ++ blkLabs bJ1 ++ blkLabs bC1 ++ blkLabs bC2 ++ blkLabs bJ2 ++
    blkLabs bSlow ++ blkLabs bJ3 ++ blkLabs bFull ++ blkLabs bO0 ++ blkLabs bO1 ++ blkLabs bO2 ++ blkLabs bO3 ++
    blkLabs bO4 ++ blkLabs bO5 ++ blkLabs bO6 ++ blkLabs bO7 ++ blkLabs bO8 ++ blkLabs bO9

/-- **`allocPhOk` reads the labels of `allocLabs` only.** -/
theorem allocPhOk_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64}
    (h : ∀ l ∈ allocLabs, lab l = lab' l) : allocPhOk okPc ph lab = allocPhOk okPc ph lab' := by
  have ho : ∀ l ∈ allocOwnLabs, lab l = lab' l := fun l hl => h l (by simp only [allocLabs]; simp [hl])
  have hb : ∀ blk, blkLabs blk ⊆ allocLabs → ∀ l ∈ blkLabs blk, lab l = lab' l :=
    fun _ hs l hl => h l (hs hl)
  unfold allocPhOk aBlk
  rw [ho fnL (by simp [allocOwnLabs]), ho entryL (by simp [allocOwnLabs]), ho cntL (by simp [allocOwnLabs]),
    ho slowL (by simp [allocOwnLabs]), ho fullL (by simp [allocOwnLabs]), ho okL (by simp [allocOwnLabs]),
    blkPh_congr (hb bPro fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bChk fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bJ1 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bC1 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bC2 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bJ2 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bSlow fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bJ3 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bFull fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bO0 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bO1 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bO2 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bO3 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bO4 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bO5 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bO6 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bO7 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bO8 fun l hl => by simp only [allocLabs]; simp [hl]),
    blkPh_congr (hb bO9 fun l hl => by simp only [allocLabs]; simp [hl])]

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.AllocG.allocPhOk_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms allocPhOk_congr

end Spike.Lib.X64.AllocG
