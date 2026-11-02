/-
**`hello_start_wc_place`'s memory-side box facts at the arena `arW` on x86-64** (the twin of
`Spike/Lib/A64HelloStartH0.lean`; the layout-generic half of `Spike/Lib/X64WakeStartH0.lean`): at any
`PlaceWX` output's runtime layout `Ly := RuntimeLayout.ofPlaceWX hpw i` and the arena `X64.WakeOD.arW hpw i`, the
memory side `msOfA (Ly).Λ μ rd G own arW I L0 ls0 fs` maps a heap word and a `.data` word for writing and shares
them. Wake's lemmas (`mp_heapW`, `mp_dataW`) fix `G := gW` and `fs := []`; `mp` reads neither, so these hold at
hello's choices as they are stated here, generic in `G`, `own` and `fs`.

- `mp_heapH`, `mp_dataH`: a heap / `.data` word is mapped and shared.

## Differences from the AArch64 version

- Over x86-64's `PlaceWX`, `RuntimeLayout.ofPlaceWX`, `X64.WakeOD.arW` and `X64ConsumerA.msOfA`; the proofs are
  wake x86-64's `mp_heapW`, `mp_dataW` (`LowerX64.mapped_K0_of_heap`, `X64Consumer.mapped_K0_of_mem`).
- A64's `mp_cellH` is dead and not twinned.
-/
import Spike.Lib.X64WakeStartH0

namespace Spike.Lib.X64.HelloPh.StartH0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib (PlaceWX)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "MS" => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd G own (Spike.Lib.X64.WakeOD.arW hpw i) I L0 ls0 fs

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Spike.Lib.X64ConsumerS.OwnS} {I : Spike.Lib.X64ConsumerS.InvS} {L0 : Lbl} {ls0 : Lsize}
  {fs : List TermRun.Frame}

/-- **A heap word is mapped and shared** at the memory side. -/
theorem mp_heapH {a : BitVec 64} (h : ∀ k < 8, (Ly).Λ.heap.contains (a.toNat + k)) : (MS).mp ⟨a, 8⟩ true :=
  ⟨Spike.Lib.LowerX64.mapped_K0_of_heap h,
    fun _ k hk => .inr (.inl (h k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))⟩

/-- **A `.data` word is mapped and shared** at the memory side. -/
theorem mp_dataH {a : BitVec 64} (h : ∀ k < 8, (Ly).Λ.data.contains (a.toNat + k)) : (MS).mp ⟨a, 8⟩ true :=
  ⟨Spike.Lib.X64Consumer.mapped_K0_of_mem fun k hk => .inl (h k hk),
    fun _ k hk => .inl (h k (by simpa [Scc.Sem.Kernel.locBytes] using hk))⟩

end Spike.Lib.X64.HelloPh.StartH0

/-- info: 'Spike.Lib.X64.HelloPh.StartH0.mp_heapH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0.mp_heapH

/-- info: 'Spike.Lib.X64.HelloPh.StartH0.mp_dataH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0.mp_dataH
