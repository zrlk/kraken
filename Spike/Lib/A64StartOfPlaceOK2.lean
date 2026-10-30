/-
**The start segment's runtime premises at `GOf2`** (AArch64):
the value-invariant premises of `A64StartOfPlaceOK` restated at wake's
invariant `WakeGOf2.GOf2` (the second TCB's limit word `lim2A = pinA + lim2Off`, `pinA + 112`
pinned too), at the runtime's layout of an output passing `placeOK`. Each
is the `GOf` lemma, by `gOf2_of` off `lim2A` or `gOf_of_gOf2` at the
first limit word.

- `G0_ofPlaceOK2`: the invariant at load (`memInv_fixG_load`).
- `hGh_ofPlaceOK2`, `hGf_ofPlaceOK2`: the first TCB's stores, at
  `pinA + 0 … pinA + 48`, off `lim2A`.
- `hGt_ofPlaceOK2`, `hG1_ofPlaceOK2`, `hG0_ofPlaceOK2`, `hGn_ofPlaceOK2`:
  the counters' stores, given the counters are not `lim2A` (`hctr2`;
  A8 separates them from the first TCB's words only).
- `hroomM_ofPlaceOK2`, `hroomU_ofPlaceOK2`: the first limit word's values.
- `hGpl_ofPlaceOK2`: any value at a placed word of `.data` or the heap,
  given the second limit word lies in the pinned region (`hpin2`; the
  pinned region is disjoint from both, `Layout.WF`).

`hctr2` and `hpin2` are facts of the concrete layout, to be decided there.
-/
import Spike.Lib.WakeGOf2
import Spike.Lib.LowerA64.PinnedTcbA

namespace Spike.Lib.WakeGOf2

open Kraken Kraken.Promising
open Scc.Sem (FixG)
open Spike.Lib.A64Consumer (TPar TParE)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (GOf m0Of)
open Spike.Lib.A64.Flow.Ret0 (limA)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- Words off `lim2A` are locations off it. -/
theorem loc_ne2 {L : RuntimeLayout} {a : BitVec 64} (h : a ≠ lim2A L) : (⟨a, 8⟩ : Loc) ≠ ⟨lim2A L, 8⟩ :=
  fun e => h (congrArg Loc.addr e)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

set_option hygiene false in
/-- The layout of `ofPlaceOK`. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => m0Of (RuntimeLayout.ofPlaceOK h i).Λ o.prog o.secs

/-- **The invariant at load**, at an entry state `E` clear of the layout. -/
theorem G0_ofPlaceOK2E {E : Scc.Sem.Entry} (hE : E.clear (Ly).Λ = true) :
    ∀ t0, (TParE E).load (o.prog, o.secs) (Ly).Λ = some t0 → MemInv (GOf2 Ly M0) t0.1.mem := by
  intro t0 hl
  have he : (TParE E).load (o.prog, o.secs) (Ly).Λ = _ :=
    Scc.Cert.Link.A64.loadParsed_of_loadOk (H := Scc.Sem.A64.kernel 1) (loadOk_link_of_placeOKAt i h) hE
  rw [he] at hl
  cases hl
  exact Scc.Sem.memInv_fixG_load rfl rfl

/-- **The invariant at load.** -/
theorem G0_ofPlaceOK2 : ∀ t0, TPar.load (o.prog, o.secs) (Ly).Λ = some t0 → MemInv (GOf2 Ly M0) t0.1.mem :=
  G0_ofPlaceOK2E h i (clear_link_of_placeOKAt i h)

/-- The first TCB's header store. -/
theorem hGh_ofPlaceOK2 :
    GOf2 Ly M0 ⟨(Ly).pinA + 0#64, 8⟩ ((Spike.Lib.A64.Flow.Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128) :=
  gOf2_of (Spike.Lib.A64.PhRec.hGh_ofPlaceOK h i) (loc_ne2 (pin_ne2 (by decide)))

/-- The first TCB's field stores. -/
theorem hGf_ofPlaceOK2 :
    ∀ e ∈ Spike.Lib.A64.Flow.Ret0.ThreadInit.fields ((Ly).pinA + 0#64 + 8#64) ((Ly).stacksA + 0#64),
      GOf2 Ly M0 ⟨(Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128) := by
  intro e he
  refine gOf2_of (Spike.Lib.A64.PhRec.hGf_ofPlaceOK h i e he) (loc_ne2 ?_)
  have hq : ∀ k : Nat, (Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 k = (Ly).pinA + (8#64 + BitVec.ofNat 64 k) := by
    intro k; rw [BitVec.add_zero, BitVec.add_assoc]
  simp only [Spike.Lib.A64.Flow.Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hq] <;> exact pin_ne2 (by simp [lim2Off])

variable (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ lim2A Ly)
include hctr2

/-- The store of `scc_rt_pinned_next`. -/
theorem hGt_ofPlaceOK2 :
    GOf2 Ly M0 ⟨(Ly).pnA, 8⟩ ((0#64 + Spike.Lib.A64.Flow.Ret0.AllocTcb.tcbLen).setWidth 128) :=
  gOf2_of (Spike.Lib.A64.PhRec.hGt_ofPlaceOK h i) (loc_ne2 (hctr2 _ (by simp)))

/-- The lock's store of `1`. -/
theorem hG1_ofPlaceOK2 : GOf2 Ly M0 ⟨(Ly).lockA, 8⟩ ((1#64).setWidth 128) :=
  gOf2_of (Spike.Lib.A64.PhRec.hG1_ofPlaceOK h i) (loc_ne2 (hctr2 _ (by simp)))

/-- The lock's store of `0`. -/
theorem hG0_ofPlaceOK2 : GOf2 Ly M0 ⟨(Ly).lockA, 8⟩ ((0#64).setWidth 128) :=
  gOf2_of (Spike.Lib.A64.PhRec.hG0_ofPlaceOK h i) (loc_ne2 (hctr2 _ (by simp)))

/-- The store of `scc_rt_stack_next`. -/
theorem hGn_ofPlaceOK2 :
    GOf2 Ly M0 ⟨(Ly).nextA, 8⟩ ((0#64 + Spike.Lib.A64.Flow.Ret0.StackTake.size0).setWidth 128) :=
  gOf2_of (Spike.Lib.A64.PhRec.hGn_ofPlaceOK h i) (loc_ne2 (hctr2 _ (by simp)))

omit hctr2

/-- **`scc_rt_main`'s room** at `GOf2`. -/
theorem hroomM_ofPlaceOK2 :
    ∀ v : Val, GOf2 Ly M0 ⟨limA (UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤
        (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - Spike.Lib.A64.Rt.bareMC.Z.toBitVec).toNat :=
  fun v hv => Spike.Lib.A64.PhRec.hroomM_ofPlaceOK h i v (gOf_of_gOf2 hv)

/-- **A user frame's room** at `GOf2`. -/
theorem hroomU_ofPlaceOK2 :
    ∀ {frame : Int}, 0 ≤ frame → frame ≤ 4095 →
      ∀ v : Val, GOf2 Ly M0 ⟨limA (UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
        (v.setWidth 64).toNat ≤
          (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - Spike.Lib.A64.Rt.bareMC.Z.toBitVec -
            (Int64.ofInt frame).toBitVec).toNat :=
  fun h0 h1 v hv => Spike.Lib.A64.PhRec.hroomU_ofPlaceOK h i h0 h1 v (gOf_of_gOf2 hv)

/-- `scc_rt_pinned` is the pinned region's base. -/
theorem pinA_toNat_ofPlaceOK2 : (Ly).pinA.toNat = (Ly).Λ.pinned.lo := by
  have hb := below32_of_placeOKAt h Λ.pinned (by simp [Scc.Sem.Layout.regions])
  have hp : (Ly).pinA = BitVec.ofNat 64 Λ.pinned.lo := (Spike.Lib.LowerA64.rtA_pinned_of_placeOKAtA h)
  rw [hp, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- **The value invariant at a placed word** of `.data` or the heap, given
the second limit word lies in the pinned region (`hpin2`). -/
theorem hGpl_ofPlaceOK2 (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) :
    ∀ a v, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → GOf2 Ly M0 (Scc.Sem.wordLoc a) v := by
  intro a v ha
  refine gOf2_of (Spike.Lib.A64.PhRec.hGpl_ofPlaceOK h i a v ha) fun he => ?_
  have hwf := wf_link_of_placeOKAt i h
  have hd : Λ.data.InSpace := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.data ∈ (Ly).Λ.regions)
  have hh : Λ.heap.InSpace := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, -⟩ := hwf.disjoint
  have hdp' : Λ.data.Disjoint Λ.pinned := hdp
  have hhp' : Λ.heap.Disjoint Λ.pinned := hhp
  have hp : (Ly).pinA.toNat = Λ.pinned.lo := pinA_toNat_ofPlaceOK2 h i
  change (Ly).pinA.toNat + 168 ≤ Λ.pinned.lo + Λ.pinned.size at hpin2
  change Λ.heap.contains a ∨ Λ.data.contains a at ha
  have hx := congrArg (fun l : Loc => l.addr.toNat) he
  simp only [Scc.Sem.wordLoc, lim2A, lim2Off, BitVec.toNat_ofNat, BitVec.toNat_add] at hx
  simp only [Scc.Sem.Range.InSpace] at hd hh
  simp only [Scc.Sem.Range.contains] at ha
  simp only [Scc.Sem.Range.Disjoint] at hdp' hhp'
  have hsm := (Ly).words_small _ (Ly).pin_mem
  have ha64 : a < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt (by omega : (Ly).pinA.toNat + 112 < 2 ^ 64)] at hx
  omega

end Place

/-- info: 'Spike.Lib.WakeGOf2.hGpl_ofPlaceOK2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hGpl_ofPlaceOK2
/-- info: 'Spike.Lib.WakeGOf2.hGf_ofPlaceOK2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hGf_ofPlaceOK2

end Spike.Lib.WakeGOf2
