/-
**The start's value-invariant premises at `PlaceWX`** (x86-64; the twin of
`Spike/Lib/A64StartOfPlaceW.lean`): `X64StartOfPlaceOK`'s runtime stores at
`GOf` (`hGh_ofPlaceW` … `hGn_ofPlaceW`) and their `GOf2` forms
(`hGh_ofPlaceW2` … `hGn_ofPlaceW2`, the counters' given `hctr2`) at
`RuntimeLayout.ofPlaceWX`, where `placeOKAt` is false for wake. The proofs
are `X64StartOfPlaceOK`'s, with A8's TCB separation from `PlaceWX`
(`ctr_neW`).

Where x86-64 differs from AArch64: A64 imports `A64StartOfPlaceOK2` for
`loc_ne2` only (its `_ofPlaceOK2` lemmas are at `placeOKAt`, unused on the
wake path); that file has no x86-64 twin, and `loc_ne2` is restated here.
The namespace is `Spike.Lib.PlaceWX` (A64 `Spike.Lib.PlaceW`); the lemma
names are A64's.
-/
import Spike.Lib.X64PlaceWRt
import Spike.Lib.X64WakeGOf2

namespace Spike.Lib.PlaceWX

open Kraken Kraken.Promising
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (GOf m0Of gOf_ne pin_ne limV)
open Spike.Lib.X64WakeGOf2 (GOf2 gOf2_of lim2A lim2Off pin_ne2)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : PlaceWX pcfg Λ o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- Words off `lim2A` are locations off it (A64's `WakeGOf2.loc_ne2`, from
`A64StartOfPlaceOK2`, which has no x86-64 twin). -/
theorem loc_ne2 {L : RuntimeLayout} {a : BitVec 64} (h : a ≠ lim2A L) : (⟨a, 8⟩ : Loc) ≠ ⟨lim2A L, 8⟩ :=
  fun e => h (congrArg Loc.addr e)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX h i

set_option hygiene false in
local notation "M0" => m0Of (RuntimeLayout.ofPlaceWX h i).Λ o.prog o.secs

/-- **The counters are not the first limit word** (A8's `tcbSep`). -/
theorem ctr_neW {a : BitVec 64} (ha : a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA]) :
    a ≠ (Ly).pinA + 16#64 := by
  rintro rfl
  exact Scc.Cert.Rt.X64.tcbSep_of_wordsOk
    (Scc.Cert.Rt.X64.wordsOk_of_rtWordsOk (rtWordsOk_link_of_placeWX i h)) 2 (by decide) ha

/-- The first TCB's header store. -/
theorem hGh_ofPlaceW :
    GOf Ly M0 ⟨(Ly).pinA + 0#64, 8⟩ ((Spike.Lib.X64.Flow.Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128) :=
  gOf_ne (pin_ne (by simp)) _

/-- The first TCB's field stores: off the limit word, but the limit field's,
whose value is the limit. -/
theorem hGf_ofPlaceW :
    ∀ e ∈ Spike.Lib.X64.Flow.Ret0.ThreadInit.fields ((Ly).pinA + 0#64 + 8#64) ((Ly).stacksA + 0#64),
      GOf Ly M0 ⟨(Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128) := by
  intro e he
  have hq : ∀ k : Nat, (Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 k = (Ly).pinA + (8#64 + BitVec.ofNat 64 k) := by
    intro k; rw [BitVec.add_zero, BitVec.add_assoc]
  simp only [Spike.Lib.X64.Flow.Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hq]
  · exact gOf_ne (pin_ne (by simp)) _
  · unfold GOf Scc.Sem.FixG
    intro a' w hm _
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨-, rfl⟩ := hm
    left
    simp only [limV, BitVec.add_zero]
  all_goals exact gOf_ne (pin_ne (by simp)) _

/-- The store of `scc_rt_pinned_next`. -/
theorem hGt_ofPlaceW :
    GOf Ly M0 ⟨(Ly).pnA, 8⟩ ((0#64 + Spike.Lib.X64.Flow.Ret0.AllocTcb.tcbLen).setWidth 128) :=
  gOf_ne (ctr_neW h i (by simp)) _

/-- The lock's store of `1`. -/
theorem hG1_ofPlaceW : GOf Ly M0 ⟨(Ly).lockA, 8⟩ ((1#64).setWidth 128) :=
  gOf_ne (ctr_neW h i (by simp)) _

/-- The lock's store of `0`. -/
theorem hG0_ofPlaceW : GOf Ly M0 ⟨(Ly).lockA, 8⟩ ((0#64).setWidth 128) :=
  gOf_ne (ctr_neW h i (by simp)) _

/-- The store of `scc_rt_stack_next`. -/
theorem hGn_ofPlaceW :
    GOf Ly M0 ⟨(Ly).nextA, 8⟩ ((0#64 + Spike.Lib.X64.Flow.Ret0.StackTake.size0).setWidth 128) :=
  gOf_ne (ctr_neW h i (by simp)) _

/-- The first TCB's header store, at `GOf2`. -/
theorem hGh_ofPlaceW2 :
    GOf2 Ly M0 ⟨(Ly).pinA + 0#64, 8⟩ ((Spike.Lib.X64.Flow.Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128) :=
  gOf2_of (hGh_ofPlaceW h i) (loc_ne2 (pin_ne2 (by decide)))

/-- The first TCB's field stores, at `GOf2`. -/
theorem hGf_ofPlaceW2 :
    ∀ e ∈ Spike.Lib.X64.Flow.Ret0.ThreadInit.fields ((Ly).pinA + 0#64 + 8#64) ((Ly).stacksA + 0#64),
      GOf2 Ly M0 ⟨(Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128) := by
  intro e he
  refine gOf2_of (hGf_ofPlaceW h i e he) (loc_ne2 ?_)
  have hq : ∀ k : Nat, (Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 k = (Ly).pinA + (8#64 + BitVec.ofNat 64 k) := by
    intro k; rw [BitVec.add_zero, BitVec.add_assoc]
  simp only [Spike.Lib.X64.Flow.Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hq] <;> exact pin_ne2 (by simp [lim2Off])

variable (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ lim2A Ly)
include hctr2

/-- The store of `scc_rt_pinned_next`, at `GOf2`. -/
theorem hGt_ofPlaceW2 :
    GOf2 Ly M0 ⟨(Ly).pnA, 8⟩ ((0#64 + Spike.Lib.X64.Flow.Ret0.AllocTcb.tcbLen).setWidth 128) :=
  gOf2_of (hGt_ofPlaceW h i) (loc_ne2 (hctr2 _ (by simp)))

/-- The lock's store of `1`, at `GOf2`. -/
theorem hG1_ofPlaceW2 : GOf2 Ly M0 ⟨(Ly).lockA, 8⟩ ((1#64).setWidth 128) :=
  gOf2_of (hG1_ofPlaceW h i) (loc_ne2 (hctr2 _ (by simp)))

/-- The lock's store of `0`, at `GOf2`. -/
theorem hG0_ofPlaceW2 : GOf2 Ly M0 ⟨(Ly).lockA, 8⟩ ((0#64).setWidth 128) :=
  gOf2_of (hG0_ofPlaceW h i) (loc_ne2 (hctr2 _ (by simp)))

/-- The store of `scc_rt_stack_next`, at `GOf2`. -/
theorem hGn_ofPlaceW2 :
    GOf2 Ly M0 ⟨(Ly).nextA, 8⟩ ((0#64 + Spike.Lib.X64.Flow.Ret0.StackTake.size0).setWidth 128) :=
  gOf2_of (hGn_ofPlaceW h i) (loc_ne2 (hctr2 _ (by simp)))

end Spike.Lib.PlaceWX

/-- info: 'Spike.Lib.PlaceWX.loc_ne2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.loc_ne2

/-- info: 'Spike.Lib.PlaceWX.ctr_neW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.ctr_neW

/-- info: 'Spike.Lib.PlaceWX.hGh_ofPlaceW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hGh_ofPlaceW

/-- info: 'Spike.Lib.PlaceWX.hGf_ofPlaceW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hGf_ofPlaceW

/-- info: 'Spike.Lib.PlaceWX.hGt_ofPlaceW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hGt_ofPlaceW

/-- info: 'Spike.Lib.PlaceWX.hG1_ofPlaceW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hG1_ofPlaceW

/-- info: 'Spike.Lib.PlaceWX.hG0_ofPlaceW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hG0_ofPlaceW

/-- info: 'Spike.Lib.PlaceWX.hGn_ofPlaceW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hGn_ofPlaceW

/-- info: 'Spike.Lib.PlaceWX.hGh_ofPlaceW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hGh_ofPlaceW2

/-- info: 'Spike.Lib.PlaceWX.hGf_ofPlaceW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hGf_ofPlaceW2

/-- info: 'Spike.Lib.PlaceWX.hGt_ofPlaceW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hGt_ofPlaceW2

/-- info: 'Spike.Lib.PlaceWX.hG1_ofPlaceW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hG1_ofPlaceW2

/-- info: 'Spike.Lib.PlaceWX.hG0_ofPlaceW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hG0_ofPlaceW2

/-- info: 'Spike.Lib.PlaceWX.hGn_ofPlaceW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.hGn_ofPlaceW2
