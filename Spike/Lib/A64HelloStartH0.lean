/-
**`hello_start_wc_place`'s memory-side box facts at the arena `arW`**
(hello.w, AArch64; the layout-generic half
of `A64WakeStartH0`): at any `PlaceW` output's runtime layout
`Ly := RuntimeLayout.ofPlaceW hpw i` and the arena `WakeOD.arW hpw i`, the
memory side `msOfA (Ly).Λ μ rd G own arW I L0 ls0 fs` maps a heap word, a
`.data` word and a box's fitting cell for writing and shares them. Wake's
lemmas fix `G := gW`, `own := ownG` and `fs := []`; `mp` reads neither, so
these hold at hello's choices (`ownGH`, hello's `G`) as they are stated
here, generic in both.

The rest of `wake_start_wc_h0` (the start control's box `C0Box`, `hq0`,
`hbox`) reads the start segment `wake_start_wc_place`, whose hello twin
waits on the `_start → wc_main` composite (`A64HelloMainGlueW`).

- `mp_heapH`, `mp_dataH`: a heap / `.data` word is mapped and shared;
- `mp_cellH`: a box's fitting cell is mapped and shared (any `AGB`).
-/
import Spike.Lib.A64WakeStartH0

namespace Spike.Lib.A64.HelloPh.StartH0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow.WakeWc (AGB)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "MS" => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ μ rd G own (Spike.Lib.WakeOD.arW hpw i) I L0 ls0 fs

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Spike.Lib.A64ConsumerS.OwnS} {I : Spike.Lib.A64ConsumerS.InvS} {L0 : Lbl} {ls0 : Lsize}
  {fs : List TermRun.Frame}

/-- **A heap word is mapped and shared** at the memory side. -/
theorem mp_heapH {a : BitVec 64} (h : ∀ k < 8, (Ly).Λ.heap.contains (a.toNat + k)) : (MS).mp ⟨a, 8⟩ true :=
  ⟨Spike.Lib.LowerA64.mapped_K0_of_heap h,
    fun _ k hk => .inr (.inl (h k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))⟩

/-- **A `.data` word is mapped and shared** at the memory side. -/
theorem mp_dataH {a : BitVec 64} (h : ∀ k < 8, (Ly).Λ.data.contains (a.toNat + k)) : (MS).mp ⟨a, 8⟩ true :=
  ⟨Spike.Lib.A64Consumer.mapped_K0_of_mem fun k hk => .inl (h k hk),
    fun _ k hk => .inl (h k (by simpa [Scc.Sem.Kernel.locBytes] using hk))⟩

/-- **A box's fitting cell is mapped and shared**: its word `heap + 16 o + 8`
lies in the heap (`heapSize_of_placeW`, `heap_below_of_placeW`). -/
theorem mp_cellH (q : AGB MS (Ly).lab) (o' : Nat) (_ : (MS).lo o') (ho : o' + (MS).units 1 q.1.τ ≤ (MS).cells) :
    (MS).mp ⟨BitVec.ofNat 64 ((MS).heap + 16 * o' + (MS).off 1 q.1.τ), 8⟩ true := by
  have hu : 1 ≤ (MS).units 1 q.1.τ := Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) q.2.toS.accs
  have hf : (MS).off 1 q.1.τ = 8 := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) q.2.toS.accs
  have hs : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.heap_below_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hc : (MS).cells = 4194304 := rfl
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hh : (MS).heap = (Ly).Λ.heap.lo := rfl
  rw [hf]
  refine mp_heapH hpw i fun k hk => ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Scc.Sem.Range.contains; omega

end Spike.Lib.A64.HelloPh.StartH0

/-- info: 'Spike.Lib.A64.HelloPh.StartH0.mp_heapH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0.mp_heapH

/-- info: 'Spike.Lib.A64.HelloPh.StartH0.mp_dataH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0.mp_dataH

/-- info: 'Spike.Lib.A64.HelloPh.StartH0.mp_cellH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0.mp_cellH
