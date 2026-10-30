/-
**The runtime's layout and its placement facts at `PlaceW`** (AArch64):
the Spike lemmas wake's lift reads at `RuntimeLayout.ofPlaceOK h i`
(`h : placeOKAt …`), restated at `h : PlaceW …` (`Spike/Lib/PlaceW.lean`),
their proofs the originals' with the `*_of_placeW` extraction lemmas.

- `RuntimeLayout.ofPlaceW`, `ofPlaceW_below`: the layout (A2, A8) and A2's
  `noClash` (`RuntimeLayout.ofPlaceOK`, `ofPlaceOK_below`). Its data are
  `ofPlaceOK`'s: `ofPlaceW (PlaceW.ofAt h) i` and `ofPlaceOK h i` agree in
  every field but the proofs.
- `PlaceW.codeEnd_lt`, `PlaceW.abortAt_eq`, `PlaceW.lab_toNat`,
  `PlaceW.hlab_ofPlaceW`: the code's end, the abort sites and the labels
  (`PhRec.codeEnd_lt`, `LowerA64.abortAt_eq`, `LowerA64.lab_toNat`,
  `PhRecOf.hlab_ofPlaceOK`).
- `PlaceW.limInit_ofPlaceW`, `PlaceW.room_of_le`, `PlaceW.hGpl_ofPlaceW`: the
  limit word's initial value and values, the invariant at a placed word
  (`PhRec.limInit_ofPlaceOK`, `PhRec.room_of_le`, `PhRec.hGpl_ofPlaceOK`).
- `PlaceW.rtA_pinned_of_placeW`, `PlaceW.pinA_toNat_ofPlaceW`:
  `scc_rt_pinned` is the pinned region's base (`rtA_pinned_of_placeOKAtA`,
  `WakeGOf2.pinA_toNat_ofPlaceOK2`).
-/
import Spike.Lib.PlaceW
import Spike.Lib.WakeGOf2
import Spike.Lib.LowerA64.AbortOfPlaceOK
import Spike.Lib.LowerA64.PinnedTcbA

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64 Scc.Cert.Link.A64
open Spike.Lib.PlaceW

namespace RuntimeLayout

/-- **The runtime's layout of an output with wake's placement facts** at a
layout `Λ`: `ofPlaceOK`'s, from `PlaceW`. -/
def ofPlaceW {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : PlaceW pcfg Λ o)
    (i : CoreTerm.Expr → String → Nat → Option Nat) : RuntimeLayout :=
  let Λi : Scc.Sem.Layout := { Λ with imms := i }
  let A := Scc.Cert.Rt.A64.rtA Λi o.prog o.secs
  have hw := Scc.Cert.Rt.A64.wordsOk_of_rtWordsOk (rtWordsOk_link_of_placeW i h)
  have hl {x : String} (hx : x ∈ Scc.Cert.Rt.A64.rtNames) := lab_link_of_placeW i h hx Scc.Sem.Entry.linux
  { exe := (Scc.Sem.A64.threadAt Scc.Sem.Entry.linux Λi.code.lo o.prog (Scc.Sem.loadSyms Λi o.secs.rodata)).exe
    prog := o.prog
    Λ := Λi
    pfx := Scc.Cert.Rt.A64.belowLen Λi.code.lo (Scc.Sem.loadSyms Λi o.secs.rodata)
    lays := lays_of_loadOk (loadOk_link_of_placeW i h) _
    valid := validLayout_of_loadOk (loadOk_link_of_placeW i h) _
    pinA := A "scc_rt_pinned"
    pnA := A "scc_rt_pinned_next"
    stacksA := A "scc_rt_stacks"
    nextA := A "scc_rt_stack_next"
    lockA := A "scc_rt_stack_lock"
    freeNA := A "scc_rt_stack_free_n"
    lab_pin := hl (by decide)
    lab_pn := hl (by decide)
    lab_stacks := hl (by decide)
    lab_next := hl (by decide)
    lab_lock := hl (by decide)
    lab_freeN := hl (by decide)
    words_small := Scc.Cert.Rt.A64.words_small_of_wordsOk hw
    words_pool := Scc.Cert.Rt.A64.words_pool_of_wordsOk hw
    words_mapped a ha :=
      have hm := (Scc.Cert.Rt.A64.words_mapped_of_wordsOk hw a ha).2.2
      ⟨Spike.Lib.A64Consumer.mapped_K0_of_mem hm, Spike.Lib.A64Consumer.mapped_K0_of_mem hm, hm⟩
    pool_fit := Scc.Cert.Rt.A64.pool_fit_of_wordsOk hw
    stacks_al := Scc.Cert.Rt.A64.stacks_al_of_wordsOk hw
    stacks_sub := Scc.Cert.Rt.A64.stacks_sub_of_wordsOk hw }

/-- **No data symbol of `ofPlaceW` below the code is named like a code
label** (A2's `noClash`). -/
theorem ofPlaceW_below {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : PlaceW pcfg Λ o)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {l : String} {a : Nat}
    (ha : codeOf (ofPlaceW h i).Λ.code.lo o.prog l = some a) :
    ∀ p ∈ Scc.Sem.symsBelow (ofPlaceW h i).Λ.code.lo (Scc.Sem.loadSyms (ofPlaceW h i).Λ o.secs.rodata),
      p.1 ≠ l :=
  below_ne_of_loadOk (loadOk_link_of_placeW i h) ha

/-- `ofPlaceW` at `PlaceW.ofAt h` is `ofPlaceOK h` (proofs aside). -/
example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    ofPlaceW (PlaceW.ofAt h) i = ofPlaceOK h i := rfl

end RuntimeLayout

end Spike.Lib.A64.Rt

namespace Spike.Lib.PlaceW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (μ GOf m0Of gOf_ne gOf_lim limV)
open Spike.Lib.A64.Flow.Ret0 (limA)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : PlaceW pcfg Λ o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW h i

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => m0Of (RuntimeLayout.ofPlaceW h i).Λ o.prog o.secs

/-- **The code's end is in the address space.** -/
theorem codeEnd_lt : Scc.Sem.A64.codeEnd (Ly).Λ.code.lo o.prog < 2 ^ 64 :=
  Scc.Cert.Link.A64.codeEnd_lt_of_loadOk (loadOk_link_of_placeW i h)

/-- **An abort kind's site is its exit call's `codeOf` address.** -/
theorem abortAt_eq (k : Scc.Sem.AbortKind) :
    (μ Ly).abortAt k = codeOf Λ.code.lo o.prog (Scc.Cert.Link.abortName k) := by
  show codeOf Λ.code.lo o.prog (Λ.abortLbl k) = _
  rw [abortLbl_of_placeW h]

/-- **A resolved code label's address** in the loaded thread is its
`codeOf` address. -/
theorem lab_toNat {l : String} {a : Nat} (ha : codeOf Λ.code.lo o.prog l = some a) :
    ((Ly).lab l).toBitVec.toNat = a := by
  have hlab := Scc.Cert.Rt.A64.label_threadAt_of_codeOf_below (E := Scc.Sem.Entry.linux)
    (syms := Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW_below h i ha) ha
  have hlt : a < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Spike.Lib.A64.PhRec.le_codeEnd_of_codeOf ha) (codeEnd_lt h i)
  have hlab' : (Ly).lab l = Int64.ofNat a := hlab
  rw [hlab']
  simp [Nat.mod_eq_of_lt hlt]

/-- **The record's labels agree with `codeOf`** where it resolves. -/
theorem hlab_ofPlaceW : ∀ l a, codeOf (Ly).Λ.code.lo o.prog l = some a → (Ly).lab l = Int64.ofNat a :=
  fun _ _ ha =>
  Scc.Cert.Rt.A64.label_threadAt_of_codeOf_below (E := Scc.Sem.Entry.linux)
    (syms := Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW_below h i ha) ha

/-- The limit word's initial value is `0` (A8's `rtInitOk`). -/
theorem limInit_ofPlaceW : (M0).initVal ⟨(Ly).pinA + 16#64, 8⟩ = 0 :=
  Scc.Cert.Rt.A64.initVal_rt_of_rtInitOk (rtInit_of_placeW h) rfl
    ((Ly).fld_mem (i := 1) (by decide))

/-- **The limit word's values are at most `b`**, for any `b` at least the
limit. -/
theorem room_of_le {b : Nat} (hb : (Ly).stacksA.toNat + 4096 ≤ b) :
    ∀ v : Val, GOf Ly M0 ⟨limA (UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64)), 8⟩ v → (v.setWidth 64).toNat ≤ b := by
  intro v hv
  rw [Spike.Lib.A64.Rt.limA_tcb0 (RuntimeLayout.ofPlaceW h i)] at hv
  rcases gOf_lim (show GOf Ly M0 ⟨(Ly).pinA + 16#64, 8⟩ v from hv) with rfl | rfl
  · have := (Ly).pool_fit
    obtain ⟨h1, h2⟩ := (Ly).stacks_sub
    simp only at h1 h2
    simp only [limV, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [limInit_ofPlaceW h i]
    simp

/-- **The value invariant at a placed word** of `.data` or the heap: not
the limit word (A8's `rtOffOk`), so any value. -/
theorem hGpl_ofPlaceW :
    ∀ a v, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → GOf Ly M0 (Scc.Sem.wordLoc a) v := by
  intro a v ha
  have hc := Scc.Cert.Rt.A64.clear_of_rtOffOk (rtOff_of_placeW h) (j := 2) (by decide)
  have hw := (wf_link_of_placeW i h).inSpace
  have hd := hw _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.data ∈ (Ly).Λ.regions)
  have hh := hw _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  change Scc.Cert.Rt.A64.clearB (Ly).Λ.data ((Ly).pinA + 16#64) = true ∧
    Scc.Cert.Rt.A64.clearB (Ly).Λ.heap ((Ly).pinA + 16#64) = true at hc
  simp only [Scc.Cert.Rt.A64.clearB, Bool.or_eq_true, decide_eq_true_eq] at hc
  simp only [Scc.Sem.Range.InSpace] at hd hh
  simp only [Scc.Sem.Range.contains] at ha
  refine gOf_ne (fun he => ?_) v
  have hb := congrArg BitVec.toNat he
  rw [BitVec.toNat_ofNat] at hb
  have : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  omega

omit i in
/-- **The runtime's `scc_rt_pinned` is the pinned region's base**
(`rtWordsOk`, `regionsTied`, `lookup_loadSymsA`). -/
theorem rtA_pinned_of_placeW :
    Scc.Cert.Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned" = BitVec.ofNat 64 Λ.pinned.lo := by
  have hrt := rtWordsOk_of_placeW h
  simp only [Scc.Cert.Rt.A64.rtWordsOk, Bool.and_eq_true, List.all_eq_true] at hrt
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hrt.1.1 "scc_rt_pinned" (by decide))
  have hreg := regionsTied_of_placeW h
  simp only [regionsTied, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hreg
  have hsym : Λ.symbols.lookup "scc_rt_pinned" = some Λ.pinned.lo := hreg.2.2.1
  have hld := loadOk_of_placeW h
  simp only [Scc.Cert.Link.A64.loadOk, Bool.and_eq_true] at hld
  have hl := Spike.Lib.LowerA64.lookup_loadSymsA hld.1.1.1.1.1.1.2 hsym
  have ha' := ha
  simp only [Scc.Cert.Rt.A64.symLab, hl] at ha'
  split at ha'
  · cases ha'
    simp only [Scc.Cert.Rt.A64.rtA, ha, Option.getD_some]
  · cases ha'

/-- `scc_rt_pinned` is the pinned region's base. -/
theorem pinA_toNat_ofPlaceW : (Ly).pinA.toNat = (Ly).Λ.pinned.lo := by
  have hb := below32_of_placeW h Λ.pinned (by simp [Scc.Sem.Layout.regions])
  have hp0 := rtA_pinned_of_placeW h
  have hp : (Ly).pinA = BitVec.ofNat 64 Λ.pinned.lo := hp0
  rw [hp, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

end Place

end Spike.Lib.PlaceW
