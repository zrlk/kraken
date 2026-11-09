/-
**hello's value invariant with the second TCB's limit word pinned** (AArch64;
hello twin of `WakeGOf2` and `WakeOG`): `GOf2H L m0`, the consumer's `GOf` (`FixG` at the first TCB's limit word
`pinA + 16`) with hello's second TCB's limit word `lim2AH L = pinA + lim2OffH` also pinned, to its initial value
or the limit main's second `scc_rt_thread_init` stores there, `lim2V L` (the second stack's base plus the guard,
the same value as wake's).

hello's second `scc_rt_alloc_tcb` takes its header at `pinA + 136` (`tcb2QH_hdrA`), one word past wake's
`pinA + 128`, so the second TCB is `tH = pinA + 144` and its limit field (`ThreadInit.fields`' offset `8`)
`pinA + 152` (`lim2OffH`, the one place this offset is written). wake's `GOf2` pins `pinA + 144`, which in hello
is the TCB's field `0` (it holds the TCB's own address after `scc_rt_thread_init`), so hello's root cannot use
wake's guarantee `WakeOG.gW`; `gWH` is its twin.

- `lim2OffH`, `lim2AH`, `GOf2H`.
- `gOf2H_ne`: off both limit words, any value; `gOf2H_of`: `GOf` off the second limit word is `GOf2H`;
  `gOf_of_gOf2H`: `GOf2H` is `GOf` with one more word pinned; `pin_ne2H`, `lim2H_ne`, `loc_ne2H`.
- `gOf2H_lim2V`, `gOf2H_lim2`: the second limit word's values; `gOf2H_lim2_le`: at most the second stack's base
  plus 4096, given the word's initial value is `0` (`hinit2`).
- `gWH`: hello's guarantee at `ofPlaceW`, the flag at `cT`; `hGpl_ofPlaceW2H`, `hGpl_gWH`: `GOf2H` (`gWH`) of any
  value at a placed word of `.data` or the heap, given the pinned region reaches `pinA + 200` (`hpin2`, the
  root's existing layout fact; `pinA + 160` would do).
- `hGh_ofPlaceW2H`, `hGf_ofPlaceW2H`, `hGt_ofPlaceW2H`, `hG1_ofPlaceW2H`, `hG0_ofPlaceW2H`, `hGn_ofPlaceW2H`:
  main's first TCB and counter stores at `GOf2H` (`PlaceW.hG*_ofPlaceW2`'s twins; the counters off hello's second
  limit word, `hctr2`).
- `room_gWH`, `room_gWH_top`: the first TCB's limit word's room (wake's `StartGlue.room_gW`, `room_gW_top`).
-/
import Spike.Lib.WakeOG
import Spike.Lib.A64WakeStartGlue
import Spike.Lib.A64StartOfPlaceW

namespace Spike.Lib.HelloGOf2H

open Kraken Kraken.Promising
open Scc.Sem (FixG)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (GOf limW limV pin_ne m0Of)
open Spike.Lib.WakeGOf2 (lim2V)
open Spike.Lib.PlaceW

/-- **hello's second TCB's limit word's offset** in the pinned region: the header `pinA + 136`, the TCB
`tH = pinA + 144` one word on, its field `1` one more. -/
abbrev lim2OffH : BitVec 64 := 152#64

/-- **hello's second TCB's limit word** (`scc_rt_thread_init`'s field `1` of the TCB `tH = pinA + 144`). -/
abbrev lim2AH (L : RuntimeLayout) : BitVec 64 := L.pinA + lim2OffH

/-- **hello's runtime value invariant**: both TCBs' limit words hold their initial value or their limit; any value
elsewhere. -/
def GOf2H (L : RuntimeLayout) (m0 : Memory) : Loc → Val → Prop :=
  FixG [(limW L, limV L), ((lim2AH L).toNat, lim2V L)] m0

variable {L : RuntimeLayout} {m0 : Memory}

/-- The second limit word is not the first. -/
theorem lim2H_ne : lim2AH L ≠ L.pinA + 16#64 := pin_ne (by decide)

/-- Off both limit words, any value. -/
theorem gOf2H_ne {a : BitVec 64} (ha : a ≠ L.pinA + 16#64) (hb : a ≠ lim2AH L) (v : Val) :
    GOf2H L m0 ⟨a, 8⟩ v := by
  unfold GOf2H FixG
  intro a' w hm hl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  simp only [Loc.mk.injEq, and_true] at hl
  rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact (ha (by rw [hl]; simp only [limW, BitVec.ofNat_toNat, BitVec.setWidth_eq])).elim
  · exact (hb (by rw [hl]; simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq])).elim

/-- **`GOf` off the second limit word is `GOf2H`.** -/
theorem gOf2H_of {l : Loc} {v : Val} (h : GOf L m0 l v) (hl : l ≠ ⟨lim2AH L, 8⟩) : GOf2H L m0 l v := by
  unfold GOf2H FixG
  intro a w hm he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with hm | hm
  · exact h a w (by rw [hm]; exact List.mem_singleton_self _) he
  · simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, -⟩ := hm
    exact (hl (by rw [he]; simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq])).elim

/-- **`GOf2H` is `GOf`** with one more word pinned. -/
theorem gOf_of_gOf2H {l : Loc} {v : Val} (h : GOf2H L m0 l v) : GOf L m0 l v := by
  unfold GOf FixG
  intro a w hm he
  exact h a w (List.mem_cons.mpr (.inl (List.mem_singleton.mp hm))) he

/-- A word `pinA + c` is hello's second limit word only at `c = lim2OffH`. -/
theorem pin_ne2H {c : BitVec 64} (hc : c ≠ lim2OffH) : L.pinA + c ≠ lim2AH L :=
  fun h => hc ((BitVec.add_right_inj _).mp h)

/-- A word other than hello's second limit word is another location. -/
theorem loc_ne2H {a : BitVec 64} (h : a ≠ lim2AH L) : (⟨a, 8⟩ : Loc) ≠ ⟨lim2AH L, 8⟩ :=
  fun e => h (congrArg Loc.addr e)

/-- The second limit word may hold its limit. -/
theorem gOf2H_lim2V : GOf2H L m0 ⟨lim2AH L, 8⟩ (lim2V L) := by
  unfold GOf2H FixG
  intro a w hm he
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
  · have h := congrArg Loc.addr he
    simp only [limW, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    exact (lim2H_ne (L := L) h).elim
  · exact .inl rfl

/-- **The second limit word's values**: its limit or its initial value. -/
theorem gOf2H_lim2 {v : Val} (h : GOf2H L m0 ⟨lim2AH L, 8⟩ v) : v = lim2V L ∨ v = m0.initVal ⟨lim2AH L, 8⟩ :=
  h _ _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- **The second limit word's values are at most the second stack's base plus 4096**, given its initial value is
`0`. -/
theorem gOf2H_lim2_le (hinit2 : m0.initVal ⟨lim2AH L, 8⟩ = 0) {v : Val} (h : GOf2H L m0 ⟨lim2AH L, 8⟩ v) :
    (v.setWidth 64).toNat ≤ (L.stacksA + 16384#64).toNat + 4096 := by
  rcases gOf2H_lim2 h with rfl | rfl
  · have := L.pool_fit
    obtain ⟨h1, h2⟩ := L.stacks_sub
    simp only at h1 h2
    simp only [lim2V, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [hinit2]; simp

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : PlaceW pcfg Λ o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW h i

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => m0Of (RuntimeLayout.ofPlaceW h i).Λ o.prog o.secs

/-- **hello's guarantee** at the layout of `ofPlaceW`, the flag at `cT` (wake's `WakeOG.gW` at `GOf2H`). -/
def gWH (cT : Loc) : Loc → Val → Prop := Spike.Lib.WakeG.wakeG (GOf2H Ly M0) cT

include h

/-- **The value invariant at a placed word** of `.data` or the heap, given the second limit word lies in the
pinned region (`hpin2`). -/
theorem hGpl_ofPlaceW2H (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) :
    ∀ a v, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → GOf2H Ly M0 (Scc.Sem.wordLoc a) v := by
  intro a v ha
  refine gOf2H_of (hGpl_ofPlaceW h i a v ha) fun he => ?_
  have hwf := wf_link_of_placeW i h
  have hd : Λ.data.InSpace := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.data ∈ (Ly).Λ.regions)
  have hh : Λ.heap.InSpace := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, -⟩ := hwf.disjoint
  have hdp' : Λ.data.Disjoint Λ.pinned := hdp
  have hhp' : Λ.heap.Disjoint Λ.pinned := hhp
  have hp : (Ly).pinA.toNat = Λ.pinned.lo := pinA_toNat_ofPlaceW h i
  change (Ly).pinA.toNat + 200 ≤ Λ.pinned.lo + Λ.pinned.size at hpin2
  change Λ.heap.contains a ∨ Λ.data.contains a at ha
  have hx := congrArg (fun l : Loc => l.addr.toNat) he
  simp only [Scc.Sem.wordLoc, lim2AH, lim2OffH, BitVec.toNat_ofNat, BitVec.toNat_add] at hx
  simp only [Scc.Sem.Range.InSpace] at hd hh
  simp only [Scc.Sem.Range.contains] at ha
  simp only [Scc.Sem.Range.Disjoint] at hdp' hhp'
  have hsm := (Ly).words_small _ (Ly).pin_mem
  have ha64 : a < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt (by omega : (Ly).pinA.toNat + 152 < 2 ^ 64)] at hx
  omega

/-- **`OPrem.hGpl` at hello's guarantee.** -/
theorem hGpl_gWH (cT : Loc) (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) :
    ∀ a v, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → gWH h i cT (Scc.Sem.wordLoc a) v :=
  fun a v ha => .inr (hGpl_ofPlaceW2H h i hpin2 a v ha)

/-- **`hctr2` at hello's second limit word** (`StartPlaceLy.hctr2_of_data`'s twin) from the counters in `.data`
and the pinned region reaching `pinA + 200` (`hpin2`): `.data` and the pinned region are disjoint (`Layout.WF`),
`pinA` the pinned region's base. -/
theorem hctr2_of_dataH (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hctrD : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], (Ly).Λ.data.contains a.toNat) :
    ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ lim2AH (Ly) := by
  intro a ha he
  have hd : Λ.data.contains a.toNat := hctrD a ha
  have hpz : (Ly).pinA.toNat + 200 ≤ Λ.pinned.lo + Λ.pinned.size := hpin2
  have hp0 : (Ly).pinA.toNat = Λ.pinned.lo := pinA_toNat_ofPlaceW h i
  have hdp : Λ.data.Disjoint Λ.pinned := (wf_link_of_placeW i h).disjoint.2.2.2.2.2.2.2.1
  have hs := (Ly).words_small _ (Ly).pin_mem
  have hb : a.toNat = (Ly).pinA.toNat + 152 := by
    rw [he]
    show ((Ly).pinA + 152#64).toNat = _
    rw [BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint] at hd hdp
  omega

/-- The first TCB's header store, at `GOf2H` (`PlaceW.hGh_ofPlaceW2`'s twin). -/
theorem hGh_ofPlaceW2H :
    GOf2H Ly M0 ⟨(Ly).pinA + 0#64, 8⟩ ((Spike.Lib.A64.Flow.Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128) :=
  gOf2H_of (hGh_ofPlaceW h i) (loc_ne2H (pin_ne2H (by decide)))

/-- The first TCB's field stores, at `GOf2H` (`PlaceW.hGf_ofPlaceW2`'s twin). -/
theorem hGf_ofPlaceW2H :
    ∀ e ∈ Spike.Lib.A64.Flow.Ret0.ThreadInit.fields ((Ly).pinA + 0#64 + 8#64) ((Ly).stacksA + 0#64),
      GOf2H Ly M0 ⟨(Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128) := by
  intro e he
  refine gOf2H_of (hGf_ofPlaceW h i e he) (loc_ne2H ?_)
  have hq : ∀ k : Nat, (Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 k = (Ly).pinA + (8#64 + BitVec.ofNat 64 k) := by
    intro k; rw [BitVec.add_zero, BitVec.add_assoc]
  simp only [Spike.Lib.A64.Flow.Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hq] <;> exact pin_ne2H (by simp [lim2OffH])

variable (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ lim2AH Ly)
include hctr2

/-- The store of `scc_rt_pinned_next`, at `GOf2H`. -/
theorem hGt_ofPlaceW2H :
    GOf2H Ly M0 ⟨(Ly).pnA, 8⟩ ((0#64 + Spike.Lib.A64.Flow.Ret0.AllocTcb.tcbLen).setWidth 128) :=
  gOf2H_of (hGt_ofPlaceW h i) (loc_ne2H (hctr2 _ (by simp)))

/-- The lock's store of `1`, at `GOf2H`. -/
theorem hG1_ofPlaceW2H : GOf2H Ly M0 ⟨(Ly).lockA, 8⟩ ((1#64).setWidth 128) :=
  gOf2H_of (hG1_ofPlaceW h i) (loc_ne2H (hctr2 _ (by simp)))

/-- The lock's store of `0`, at `GOf2H`. -/
theorem hG0_ofPlaceW2H : GOf2H Ly M0 ⟨(Ly).lockA, 8⟩ ((0#64).setWidth 128) :=
  gOf2H_of (hG0_ofPlaceW h i) (loc_ne2H (hctr2 _ (by simp)))

/-- The store of `scc_rt_stack_next`, at `GOf2H`. -/
theorem hGn_ofPlaceW2H :
    GOf2H Ly M0 ⟨(Ly).nextA, 8⟩ ((0#64 + Spike.Lib.A64.Flow.Ret0.StackTake.size0).setWidth 128) :=
  gOf2H_of (hGn_ofPlaceW h i) (loc_ne2H (hctr2 _ (by simp)))

end Place

/-! ## The first limit word's room (wake's `StartGlue.room_gW`, `room_gW_top` at `GOf2H`) -/

/-- **The first TCB's limit word under hello's value invariant** is at most any `b` past the first stack's guard
(`hb`): it holds the limit `stacksA + 4096` or its initial `0` (`hinit`), the root's word `cT` being another
(`hcT`). -/
theorem room_gWH {cT : Loc} {b : Nat}
    (hcT : cT ≠ ⟨L.pinA + 16#64, 8⟩) (hinit : m0.initVal ⟨L.pinA + 16#64, 8⟩ = 0)
    (hb : L.stacksA.toNat + 4096 ≤ b) :
    ∀ v : Val, Spike.Lib.WakeG.wakeG (GOf2H L m0) cT
      ⟨Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64)), 8⟩ v → (v.setWidth 64).toNat ≤ b := by
  intro v hv
  rw [Spike.Lib.A64.Rt.limA_tcb0 L] at hv
  rcases (show Spike.Lib.WakeG.wakeG (GOf2H L m0) cT ⟨L.pinA + 16#64, 8⟩ v from hv) with h | h
  · exact absurd h.symm hcT
  rcases Spike.Lib.A64.PhRec.gOf_lim (gOf_of_gOf2H h) with rfl | rfl
  · have := L.pool_fit
    obtain ⟨h1, h2⟩ := L.stacks_sub
    simp only at h1 h2
    simp only [Spike.Lib.A64.PhRec.limV, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128),
      BitVec.setWidth_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [hinit]
    simp

/-- **The room at `scc_rt_main`'s entry** at the first stack's top less `Z` (`Z ≤ 12288`): `room_gWH` at
`b = (stacksA + 16384 - Z).toNat`. -/
theorem room_gWH_top {cT : Loc} {Z : Int64}
    (hcT : cT ≠ ⟨L.pinA + 16#64, 8⟩) (hinit : m0.initVal ⟨L.pinA + 16#64, 8⟩ = 0)
    (hZ : Z.toBitVec.toNat ≤ 12288) :
    ∀ v : Val, Spike.Lib.WakeG.wakeG (GOf2H L m0) cT
      ⟨Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (L.pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Spike.Lib.A64.Flow.Ret0.stacksA L.lab + 0#64 + 16384#64 - Z.toBitVec).toNat := by
  refine room_gWH hcT hinit ?_
  have := L.pool_fit
  obtain ⟨h1, h2⟩ := L.stacks_sub
  simp only at h1 h2
  rw [L.lab_stacks, BitVec.add_zero, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end Spike.Lib.HelloGOf2H

/-- info: 'Spike.Lib.HelloGOf2H.room_gWH_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloGOf2H.room_gWH_top

/-- info: 'Spike.Lib.HelloGOf2H.gOf2H_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloGOf2H.gOf2H_ne

/-- info: 'Spike.Lib.HelloGOf2H.gOf2H_lim2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloGOf2H.gOf2H_lim2_le

/-- info: 'Spike.Lib.HelloGOf2H.hGpl_gWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloGOf2H.hGpl_gWH
