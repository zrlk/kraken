/-
**hello.w's level 1 at an empty-slot fragment** (AArch64): why it exists. The root's level-1
invariant is `inv1 := inv1RU (inv1G W1R XR … (MS1 I))`, a greatest fixed point over level 1's memory side `MS1 I`
(`msOfA … I`). The fragment the root's statements are asked at is `IH D = I3 … inv0 inv1 inv2`, which contains
`inv1` (and `helloDR`'s `inv0 := inv0H … inv1 …`), so `I := IH D` would define `inv1` in terms of itself. Level 1
is instead taken at `I₀ := I3 ar L0 ls0 ⊥ ⊥ inv2`, whose level-0 and level-1 slots are empty (level 1's only
allocation, the box, lands in the level-2 slot, `RootHP.hland2_boxMRU`, generic in both), and lifted to `IH D`:
the fragment is read only through `msOfA`'s `xa`, the allocation landings, where it occurs positively
(`A64GfpS.segInvS_mono_xa`).

- `I0H`: the fragment `I3 ar L0 ls0 ⊥ ⊥ inv2` (at the root `I3 arW L0T (ls0T ls) ⊥ ⊥ inv2R`).
- `I0H_le`: `I0H` is inside `I3 … inv0 inv1 inv2` (at the root, `IH D`).
- `h1_bridge`: a segment under `msOfA … I` is one under `msOfA … I'` for `I ⊆ I'` (level 1 at `I0H` to `IH D`).
- `rdLandH_xa`: level 1's entry `RdLandH` (`h1`'s `Rd`) does not read the fragment: it moves between any two
  (`Call.OK` and the allocator's nodes read `msOfA`'s geometry, not `xa`).

The `example` at the end checks that the emptied slots lose nothing `MainWcL1A.h1_level1P`'s `hX` needs: the box
store's landing at `I0H` is `RootHP.hland2_boxMRU`'s.
-/
import Spike.Lib.A64GfpS
import Spike.Lib.A64HelloStartH0H1
import Spike.Lib.A64HelloRootHP

namespace Spike.Lib.A64.HelloPh.RootL1F

open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (FragS MemSide Arena PlaceW)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SegInvS msOfA I3)
open Spike.Lib.A64ConsumerS (InvS)

/-- **Level 1's fragment at the root**: `I3` with its level-0 and level-1 slots empty. The root's fragment
`IH D` cannot be used for level 1: both `helloDR`'s `inv0` (`inv0H … inv1 …`) and level 1's invariant `inv1`
(`inv1G` over `msOfA … I`) depend on it, so `I := IH D` would define `inv1` through itself. Only the level-2 slot is
kept (level 1's box lands there), and `inv2R` does not depend on `inv1`. -/
abbrev I0H (ar : Arena) (L0 : Lbl) (ls0 : Lsize)
    (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : InvS :=
  I3 ar L0 ls0 (fun _ _ _ => False) (fun _ _ _ _ _ _ => False) inv2

/-- **`I0H` is inside the full fragment** (at the root, `IH D`): its emptied slots are `False`. This is the
inclusion `h1_bridge` lifts level 1 by, from `I0H` (needed because `inv0H` and `inv1G` depend on `IH D`) to the
fragment the root asks at. -/
theorem I0H_le {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isaLSE2}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} :
    ∀ lbl lsize s c fs, I0H ar L0 ls0 inv2 lbl lsize s c fs → I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize s c fs
  | _, _, _, _, _, .inl ⟨_, _, h⟩ => h.elim
  | _, _, _, _, _, .inr (.inl ⟨_, _, _, _, _, _, _, h⟩) => h.elim
  | _, _, _, _, _, .inr (.inr h) => .inr (.inr h)

/-- **A segment under `msOfA … I` is one under `msOfA … I'`** for a larger fragment (`segInvS_mono_xa`,
`msOfA_xa_mono`: the fragment is read only by `xa`, positively, at the allocation landings). The root's level 1
is proved at `I0H` (`inv0H` and `inv1G` depend on `IH D`) and lifted by this to `IH D` with `I0H_le`. -/
theorem h1_bridge {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop}
    {G own} {ar : Arena} {I I' : InvS}
    {p : CoreTerm.Prog} {W inv : FragS isaLSE2} {K : State → State → Prop} {lbl lbl' : Lbl} {lsize : Lsize}
    (hI : ∀ lbl lsize s c fs, I lbl lsize s c fs → I' lbl lsize s c fs)
    (h : SegInvS W K p lbl (msOfA Λ μ rd G own ar I lbl' lsize) inv) :
    SegInvS W K p lbl (msOfA Λ μ rd G own ar I' lbl' lsize) inv :=
  Spike.Lib.A64GfpS.segInvS_mono_xa h (fun fs => Spike.Lib.A64GfpS.msOfA_with_xa fs)
    fun fs _ _ _ _ _ hx => Spike.Lib.A64GfpS.msOfA_xa_mono hI fs hx

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

/-- **Level 1's entry does not read the fragment** (`RdLandH` at `I` is `RdLandH` at `I'`): its call's premises
`Call.OK` and the allocator's nodes read `msUH`'s geometry, which `msOfA` takes off the arena whatever `I`. Level 1
is at `I0H` (`inv0H` and `inv1G` depend on `IH D`), level 0's landing at `IH D`: this moves the entry across. -/
theorem rdLandH_xa {asm : String} {E : Scc.Sem.Entry} {rd : TermRun.Word → Prop} {I I' : InvS} {ls : Lsize}
    {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel}
    {b w : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : Spike.Lib.A64.HelloPh.StartH0H1.RdLandH (asm := asm) hpw i0 E rd I ls J1 l b w s c) :
    Spike.Lib.A64.HelloPh.StartH0H1.RdLandH (asm := asm) hpw i0 E rd I' ls J1 l b w s c := by
  obtain ⟨v, m0, σC, q, F', h1, h2, h3, hu, ht⟩ := h
  exact ⟨v, m0, σC, ⟨q.1, { q.2 with }⟩, F', h1, h2, h3, hu, ht⟩

section Check

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0
set_option hygiene false in
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hpw IH
set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH
set_option hygiene false in
local notation "LB" => Spike.Lib.WakeLoadT.L0T (Ly).Λ

/-- `MainWcL1A.h1_level1P`'s `hX` at `I0H` is `RootHP.hland2_boxMRU`'s (generic in the emptied slots): the box's
landing is `I3`'s level-2 slot, which `I0H` keeps. -/
example {asm : String} (E : Scc.Sem.Entry) (rd : TermRun.Word → Prop) (ls : Lsize)
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    {L : Spike.Lib.A64.Rt.RuntimeLayout} {endPc : Int64} {F0 : MachineData → Prop}
    (h2 : Spike.Lib.HelloPreA.H2StmtH W2 K (AR) (LB) ms2 L endPc
      (fun l b n l' A n' s c => Spike.Lib.HelloHMid.BoxMH (Ly)
        (Spike.Lib.A64.HelloPh.Land.ref1H (asm := asm) hpw i0 E rd ls l b n []) F0
        (Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l) l' A
        (Spike.Lib.HelloHMid.slWsH l) n' s c ∧ Spike.Lib.A64.KeepUn.U (Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab) s)
      inv2)
    (hF0 : ∀ v m1 σ1 m, Spike.Lib.A64.Flow.HelloM.wcF (Spike.Lib.A64.Flow.swR v
        (-Spike.Lib.A64.HelloPh.StartH0G.helloLsw) 0) Spike.Lib.A64.HelloPh.StartH0G.helloD
        (Spike.Lib.A64.WakePh.MainGlue.FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) Spike.Lib.A64.HelloPh.StartH0G.helloLsw
          0#64 v) m1 σ1 m → F0 m) :
    ∀ l b n, (LB) l = none → Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells b n →
      Spike.Lib.A64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n
        (msOfA (Ly).Λ ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
          (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
          (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (AR)
          (I0H (AR) (LB) (Spike.Lib.WakeLoadT.ls0T ls) inv2) (Spike.Lib.A64ConsumerA.upd (LB) l b)
          (Spike.Lib.A64ConsumerA.updN (Spike.Lib.WakeLoadT.ls0T ls) l n) []).xa :=
  fun _ _ _ hl hb => Spike.Lib.A64.HelloPh.RootHP.hland2_boxMRU hpw i0 E rd ls h2 hl hb hF0

end Check

end Spike.Lib.A64.HelloPh.RootL1F

/-- info: 'Spike.Lib.A64.HelloPh.RootL1F.I0H_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootL1F.I0H_le

/--
info: 'Spike.Lib.A64.HelloPh.RootL1F.h1_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootL1F.h1_bridge

/-- info: 'Spike.Lib.A64.HelloPh.RootL1F.rdLandH_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootL1F.rdLandH_xa
