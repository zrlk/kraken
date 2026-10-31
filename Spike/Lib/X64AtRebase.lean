/-
**Re-basing a node's region** (x86-64): the same cells seen from a base `d`
bytes higher (`Region.fp`, ISA-neutral, `Spike/Lib/RegionFp.lean`). A pair
at a node `n` of `R` is at a node `n'` of `R.fp d` whose static offsets are
`n`'s shifted by `-d` and whose invariant holds of the shifted abstract
state (`enter d σ`: slot `k` of it is slot `d + k` of `σ`). A theorem over
the existing `At`: no new constructor, no `Seg` change.

Used where a function's region is handed over at the return address's cell
(offset `0` at the entry, `X64WakeMain.wR`) but its body's nodes are stated
in its frame based at the saved `%rbp` (`d = -8`, `WcClone.oW`).

- `FStable.fp`: a frame condition stable on `R` is stable on `R.fp d`;
- `At.rebase`: the node on the re-based region;
- `rebase_wcMain`: an instance at `d = -8` on a concrete region, from
  offsets `⟨-72, [(.rbp, -8)]⟩` to `⟨-64, [(.rbp, 0)]⟩` with the saved
  `%rbp` and return address carried from slots `-8`, `0` to `0`, `8` (the
  transport premise is met, not vacuous).
-/
import Spike.Lib.X64Call
import Spike.Lib.RegionFp

namespace Spike.Lib.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib

variable {R : Region} {d : Int}

/-- **A frame condition stable on `R` is stable on `R.fp d`** (the same
address range). -/
theorem FStable.fp {F : MachineData → Prop} (hR : R.OK) (h1 : R.lo ≤ d) (h2 : d < R.hi) (hF : FStable R F) :
    FStable (R.fp d) F :=
  fun m m' hm hD => hF m m' hm fun a ha hd => hD a ha (Region.fp_out hR h1 h2 hd)

/-- **A node on the re-based region**: a pair at `n` on `R` is at `n'` on
`R.fp d` when `n'` is at `n`'s pc, its static offsets are `n`'s shifted by
`-d` (`ho`), and its invariant holds of the shifted state (`hJ`). -/
theorem At.rebase {exe : _root_.Executable} {endPc : Int64} {F : MachineData → Prop} {n n' : ND}
    (hd8 : d % 8 = 0) (hpc : n'.pc = n.pc) (ho : ∀ r k, n'.o.get r = some k → n.o.get r = some (d + k))
    (hJ : ∀ σ c, n.J σ c → n'.J (enter d σ) c) {s : State} {c : Ctl} (h : At exe endPc R F n s c) :
    At exe endPc (R.fp d) F n' s c := by
  obtain ⟨he, hn, hdc, hp, σ, hA, hD, hJn⟩ := h
  refine ⟨he, hn, hdc, hpc ▸ hp, enter d σ, ⟨hA.regs, hA.zmms, hA.status, ?_, fun k hk => ?_⟩, hD, hJ σ c hJn⟩
  · intro r k hr
    rw [Region.fp_addr]
    exact hA.so r (d + k) (ho r k hr)
  · rw [Region.fp_addr]
    exact hA.slot (d + k) (Region.fp_off hd8 hk)

/-- **The offsets of `wc_main`'s body from the return address's base**:
`⟨-64, [(.rbp, 0)]⟩` on `R.fp (-8)` is `⟨-72, [(.rbp, -8)]⟩` on `R`. -/
theorem so_rebase_wcMain (r : Reg64) (k : Int) (h : SO.get ⟨-64, [(.rbp, 0)]⟩ r = some k) :
    SO.get ⟨-72, [(.rbp, -8)]⟩ r = some (-8 + k) := by
  unfold SO.get at h ⊢
  split at h
  · cases h; simp_all
  · rename_i hr
    simp only [hr, ↓reduceIte]
    simp only [lk] at h ⊢
    split at h
    · cases h; simp_all
    · cases h

/-- **`At.rebase` at `d = -8`, concretely**: on a region based at
`0x10000` spanning `[-80, 16)`, a pair whose `%rbp` cell (slot `-8`) holds
`b` and whose return address cell (slot `0`) holds `a`, at offsets
`⟨-72, [(.rbp, -8)]⟩`, is on the re-based region with those words at slots
`0` and `8`, at `⟨-64, [(.rbp, 0)]⟩`. -/
theorem rebase_wcMain {exe : _root_.Executable} {endPc : Int64} {F : MachineData → Prop} {pc : Int64}
    {a b : BitVec 64} {s : State} {c : Ctl}
    (h : At exe endPc ⟨0x10000#64, -80, 16⟩ F
      ⟨pc, ⟨-72, [(.rbp, -8)]⟩, fun σ _ => σ.slot (-8) = b ∧ σ.slot 0 = a⟩ s c) :
    At exe endPc ((⟨0x10000#64, -80, 16⟩ : Region).fp (-8)) F
      ⟨pc, ⟨-64, [(.rbp, 0)]⟩, fun σ _ => σ.slot 0 = b ∧ σ.slot 8 = a⟩ s c :=
  At.rebase (R := ⟨0x10000#64, -80, 16⟩) (d := -8)
    (n := ⟨pc, ⟨-72, [(.rbp, -8)]⟩, fun σ _ => σ.slot (-8) = b ∧ σ.slot 0 = a⟩)
    (n' := ⟨pc, ⟨-64, [(.rbp, 0)]⟩, fun σ _ => σ.slot 0 = b ∧ σ.slot 8 = a⟩) (by decide) rfl
    so_rebase_wcMain (fun σ _ ⟨hb, ha⟩ => ⟨by simpa [enter] using hb, by simpa [enter] using ha⟩) h

end Spike.Lib.X64

/-- info: 'Spike.Lib.X64.FStable.fp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.FStable.fp

/-- info: 'Spike.Lib.X64.At.rebase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.At.rebase

/-- info: 'Spike.Lib.X64.rebase_wcMain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.rebase_wcMain
