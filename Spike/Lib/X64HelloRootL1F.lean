/-
**hello.w's level 1 at an empty-slot fragment** (x86-64; the twin of `Spike/Lib/A64HelloRootL1F.lean`): why it
exists. The root's level-1 invariant is a greatest fixed point over level 1's memory side `msOfA … I`. The
fragment the root's statements are asked at is `IH D = I3 … inv0 inv1 inv2`, which contains `inv1` (and `inv0`,
which is stated over `inv1`), so `I := IH D` would define `inv1` in terms of itself. Level 1 is instead taken at
`I₀ := I3 ar L0 ls0 ⊥ ⊥ inv2`, whose level-0 and level-1 slots are empty (level 1's only allocation, the box,
lands in the level-2 slot), and lifted to `IH D`: the fragment is read only through `msOfA`'s `xa`, the
allocation landings, where it occurs positively (`X64GfpS.segInvS_mono_xa`).

- `I0H`: the fragment `I3 ar L0 ls0 ⊥ ⊥ inv2` (at the root `I3 arW L0T (ls0T ls) ⊥ ⊥ inv2R`).
- `I0H_le`: `I0H` is inside `I3 … inv0 inv1 inv2` (at the root, `IH D`).
- `h1_bridge`: a segment under `msOfA … I` is one under `msOfA … I'` for `I ⊆ I'` (level 1 at `I0H` to `IH D`).
- `h1_bridgeP`: the same for the publishing segment invariant `SegWPub.SegInvSP` (x86-64's level 1).
- `rdLandH_xa`: level 1's entry `StartH0H1.RdLandH` (`h1`'s `Rd`) does not read the fragment: it moves between
  any two (the call's premises and the allocator's nodes read `msUH`'s geometry, not `xa`).

## Differences from the AArch64 version

- The layout is `RuntimeLayout.ofPlaceWX` (AArch64 `ofPlaceW`); `RdLandH` is x86-64's (`StartH0H1`, the call's
  region `mR (RS helloLsw v)` at offsets `⟨-48, []⟩`, its frame kept by `CKept … (-48) (-160) 8`).
- AArch64's closing `example` (the box store's landing at `I0H` is `RootHP.hland2_boxMRU`'s, at
  `LandR1U.HLand2U`) is not repeated: neither has an x86-64 version yet.
-/
import Spike.Lib.X64GfpS
import Spike.Lib.X64HelloStartH0H1
import Spike.Lib.X64SegWPub

namespace Spike.Lib.X64.HelloPh.RootL1F

open Kraken.Promising Kraken.Promising.X64
open Spike.Lib (FragS Arena PlaceWX)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SegInvS msOfA I3)
open Spike.Lib.X64ConsumerS (InvS)

/-- **Level 1's fragment at the root**: `I3` with its level-0 and level-1 slots empty. The root's fragment
`IH D` cannot be used for level 1: both the root's `inv0` and level 1's invariant `inv1` (over `msOfA … I`)
depend on it, so `I := IH D` would define `inv1` through itself. Only the level-2 slot is kept (level 1's box
lands there), and the root's `inv2` does not depend on `inv1`. -/
abbrev I0H (ar : Arena) (L0 : Lbl) (ls0 : Lsize)
    (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa) : InvS :=
  I3 ar L0 ls0 (fun _ _ _ => False) (fun _ _ _ _ _ _ => False) inv2

/-- **`I0H` is inside the full fragment** (at the root, `IH D`): its emptied slots are `False`. This is the
inclusion `h1_bridge` lifts level 1 by, from `I0H` to the fragment the root asks at. -/
theorem I0H_le {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isa}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa} :
    ∀ lbl lsize s c fs, I0H ar L0 ls0 inv2 lbl lsize s c fs → I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize s c fs
  | _, _, _, _, _, .inl ⟨_, _, h⟩ => h.elim
  | _, _, _, _, _, .inr (.inl ⟨_, _, _, _, _, _, _, h⟩) => h.elim
  | _, _, _, _, _, .inr (.inr h) => .inr (.inr h)

/-- **A segment under `msOfA … I` is one under `msOfA … I'`** for a larger fragment (`segInvS_mono_xa`,
`msOfA_xa_mono`: the fragment is read only by `xa`, positively, at the allocation landings). The root's level 1
is proved at `I0H` and lifted by this to `IH D` with `I0H_le`. -/
theorem h1_bridge {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop}
    {G own} {ar : Arena} {I I' : InvS}
    {p : CoreTerm.Prog} {W inv : FragS isa} {K : State → State → Prop} {lbl lbl' : Lbl} {lsize : Lsize}
    (hI : ∀ lbl lsize s c fs, I lbl lsize s c fs → I' lbl lsize s c fs)
    (h : SegInvS W K p lbl (msOfA Λ μ rd G own ar I lbl' lsize) inv) :
    SegInvS W K p lbl (msOfA Λ μ rd G own ar I' lbl' lsize) inv :=
  Spike.Lib.X64GfpS.segInvS_mono_xa h (fun fs => Spike.Lib.X64GfpS.msOfA_with_xa fs)
    fun fs _ _ _ _ _ hx => Spike.Lib.X64GfpS.msOfA_xa_mono hI fs hx

/-- **`h1_bridge` for the publishing segment invariant** (`SegWPub.SegInvSP.mono_xa`, `msOfA_xa_mono`): x86-64's
level 1 is a `SegInvSP`, lifted from `I0H` to `IH D` the same way. -/
theorem h1_bridgeP {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop}
    {G own} {ar : Arena} {I I' : InvS}
    {p : CoreTerm.Prog} {W inv : FragS isa} {K : State → State → Prop} {lbl lbl' : Lbl} {lsize : Lsize}
    (hI : ∀ lbl lsize s c fs, I lbl lsize s c fs → I' lbl lsize s c fs)
    (h : Spike.Lib.X64SegWPub.SegInvSP W K p lbl (msOfA Λ μ rd G own ar I lbl' lsize) inv) :
    Spike.Lib.X64SegWPub.SegInvSP W K p lbl (msOfA Λ μ rd G own ar I' lbl' lsize) inv :=
  Spike.Lib.X64SegWPub.SegInvSP.mono_xa h (fun fs => Spike.Lib.X64GfpS.msOfA_with_xa fs)
    fun fs _ _ _ _ _ hx => Spike.Lib.X64GfpS.msOfA_xa_mono hI fs hx

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

/-- **Level 1's entry does not read the fragment** (`RdLandH` at `I` is `RdLandH` at `I'`): its call's premises
and the allocator's nodes read `msUH`'s geometry, which `msOfA` takes off the arena whatever `I`. Level 1 is at
`I0H`, level 0's landing at `IH D`: this moves the entry across. -/
theorem rdLandH_xa {asm : Scc.Sem.X64.Asm} {E : Scc.Sem.Entry} {rd : TermRun.Word → Prop} {I I' : InvS}
    {ls : Lsize} {J1 : Spike.Lib.X64.AS → Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel}
    {b w : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : Spike.Lib.X64.HelloPh.StartH0H1.RdLandH (asm := asm) hpw i0 E rd I ls J1 l b w s c) :
    Spike.Lib.X64.HelloPh.StartH0H1.RdLandH (asm := asm) hpw i0 E rd I' ls J1 l b w s c := by
  obtain ⟨v, m0, σC, q, F', h1, h2, h3, hu, ht⟩ := h
  exact ⟨v, m0, σC, ⟨q.1, { q.2 with }⟩, F', h1, h2, h3, hu, ht⟩

end Spike.Lib.X64.HelloPh.RootL1F

/-- info: 'Spike.Lib.X64.HelloPh.RootL1F.I0H_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1F.I0H_le

/--
info: 'Spike.Lib.X64.HelloPh.RootL1F.h1_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1F.h1_bridge

/-- info: 'Spike.Lib.X64.HelloPh.RootL1F.rdLandH_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1F.rdLandH_xa

/--
info: 'Spike.Lib.X64.HelloPh.RootL1F.h1_bridgeP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL1F.h1_bridgeP
