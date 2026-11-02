/-
**A box call's premises at the arena `arW`, on x86-64** (the twin of `Spike/Lib/A64HelloArWCall.lean`; generic,
for hello's levels and wake's start):
at any `PlaceWX` output's runtime layout `Ly := RuntimeLayout.ofPlaceWX hpw i`, the arena `X64.WakeOD.arW hpw i` (its
counter zero-initialised, `CtrZ`), the memory side `msOfA (Ly).Λ μ rd G own arW I lbl lsize fs` at any marks, read
side, owned words, fragment, labels and frames, a value invariant `G` admitting every value at every heap and
`.data` word (`hG`; wake's `X64WakeOG.hGpl_ofPlaceW2`), and a start control boxing a
zero (`StartH0.C0Box`): the box call's premises `Call.OKB` hold, given the counter word off every label (`hrtC`).
The headers are off every label by the counter floor (`AllocLo.LoOf`), at any labels.

This is `X64WakeStartH0X`'s inline `hq0` with `G`, `own`, the labels and the frames generic (wake's own
`MainWcP.hq`/`hq0` premise at its levels).

- `rt_hdr_loOf`: a header above the counter floor is the runtime's at any labels.
- `okb_arW`: the box call at a `C0Box` control (`h = 256`, one element, two units).

## Differences from the AArch64 version

- Over x86-64's `PlaceWX`, `RuntimeLayout.ofPlaceWX`, `X64.WakeOD.arW`, `X64ConsumerA.msOfA`, `X64.Alloc.Call`,
  `X64.Rt.ArenaW` and `X64.WakePh.StartH0.C0Box`; the proofs are A64's.
-/
import Spike.Lib.X64HelloStartH0

namespace Spike.Lib.X64.ArWCall

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (lrange)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.WakePh.StartH0 (C0Box)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "MS" => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd G own (Spike.Lib.X64.WakeOD.arW hpw i) I lbl lsize fs

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Spike.Lib.X64ConsumerS.OwnS} {I : Spike.Lib.X64ConsumerS.InvS} {lbl : Lbl} {lsize : Lsize}
  {fs : List TermRun.Frame}

/-- **A header above the counter floor is the runtime's** at any labels: the floor (`LoOf`) keeps the free cells
from `o'` on off every label, and the header's word is the first free cell's (`o' < cells`). -/
theorem rt_hdr_loOf {o' : Nat} (hlo : (MS).lo o') (hc : o' < (MS).cells) : (MS).rt ((MS).heap + 16 * o') := by
  rintro ⟨l, b, hl, hcn⟩
  have hd := (hlo l b hl).1
  simp only [Spike.Lib.AllocRow.freeR, Scc.Sem.Range.Disjoint, lrange, Scc.Sem.Range.contains] at hd hcn
  change o' < (Spike.Lib.X64.WakeOD.arW hpw i).cells at hc
  change (Spike.Lib.X64.WakeOD.arW hpw i).heap + 16 * o' + 16 * ((Spike.Lib.X64.WakeOD.arW hpw i).cells - o') ≤ b ∨
    b + 8 * lsize l ≤ (Spike.Lib.X64.WakeOD.arW hpw i).heap + 16 * o' at hd
  change b ≤ (Spike.Lib.X64.WakeOD.arW hpw i).heap + 16 * o' ∧ _ at hcn
  have hh : (MS).heap = (Spike.Lib.X64.WakeOD.arW hpw i).heap := rfl
  omega

/-- **The box call at a `C0Box` control** (module doc): `⟨c0, "o", z, int, e, int, [w], 1, 256, 0, 0⟩` meets
`Call.OKB` at the memory side, its header `256`, one element of two units. -/
theorem okb_arW (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hG : ∀ a v, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → G (Scc.Sem.wordLoc a) v)
    (hrtC : (MS).rt (BitVec.ofNat 64 (MS).ctr).toNat) {c0 : Spike.Lib.Ctl} (hbx : C0Box c0) :
    ∃ q : Call, q.OKB (MS) (Ly).lab ∧ q.c0 = c0 ∧ q.h = 256#64 ∧ q.k = 1#64 ∧ q.u (MS) = 2#64 := by
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX (Spike.Lib.PlaceWX.link i hpw)
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 :=
    Spike.Lib.X64.Rt.ArenaW.heap_below_of_placeW (Spike.Lib.PlaceWX.link i hpw)
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceWX.link i hpw)
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceWX.link i hpw) hc
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hh : (MS).heap = (Ly).Λ.heap.lo := rfl
  have hcl : (MS).cells = 4194304 := rfl
  have hct : (MS).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have hacc1 : ∃ us, TermRun.accs (TermRun.close [] .int) = some us := ⟨_, rfl⟩
  have hu2 : (MS).units 1 .int = 2 := rfl
  have hf1 : (MS).off 1 .int = 8 := rfl
  have hctrB : ∀ k < 8, (Ly).Λ.data.contains ((BitVec.ofNat 64 (MS).ctr).toNat + k) := fun k hk => by
    rw [hct, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; unfold Scc.Sem.Range.contains; omega
  have hG' : ∀ a : BitVec 64, a.toNat < 2 ^ 32 → ((Ly).Λ.heap.contains a.toNat ∨ (Ly).Λ.data.contains a.toNat) →
      ∀ v, (MS).G ⟨a, 8⟩ v := fun a _ hm v => by
    show G _ v
    simpa [Scc.Sem.wordLoc] using hG a.toNat v hm
  obtain ⟨e, he⟩ := hbx.term
  obtain ⟨w, hw, -⟩ := hbx.ev
  refine ⟨⟨c0, "o", .var "z", .int, e, .int, [w], 1, 256#64, 0#64, 0#64⟩,
    ⟨⟨.inr ⟨trivial, .var "z", [w], ⟨_, he⟩, hw, rfl⟩, hbx.hold, by show (1 : Nat) < 2 ^ 64; decide,
      Spike.Lib.X64.Rt.ArenaW.arOf_ctrLab (Spike.Lib.PlaceWX.link i hpw) .linux,
      Spike.Lib.X64.Rt.ArenaW.arOf_heapLab (Spike.Lib.PlaceWX.link i hpw) .linux,
      by rw [hh]; omega, rfl, by rw [hu2]; decide, by rw [hf1]; simp [Spike.Lib.X64.Alloc.mOf], hacc1, hrtC,
      Spike.Lib.X64.HelloPh.StartH0.mp_dataH hpw i hctrB,
      fun _ _ _ => hG' _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
        (.inr (by rw [hct, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact ⟨hc1, by omega⟩)) _,
      fun o' hlo ho => ?_⟩, trivial, ⟨_, he⟩, hw, rfl⟩, rfl, rfl, rfl, rfl⟩
  have hd : Call.hdrAt (MS) ⟨c0, "o", .var "z", .int, e, .int, [w], 1, 256#64, 0#64, 0#64⟩ o' =
      (MS).heap + 16 * o' := by simp [Call.hdrAt, Spike.Lib.X64.Alloc.mOf]
  rw [hu2, hcl] at ho
  have hT : (BitVec.ofNat 64 (Call.hdrAt (MS) ⟨c0, "o", .var "z", .int, e, .int, [w], 1, 256#64, 0#64, 0#64⟩ o')).toNat
      = (Ly).Λ.heap.lo + 16 * o' := by rw [hd, hh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hd ▸ rt_hdr_loOf hpw i hlo (by rw [hcl]; omega), Spike.Lib.X64.HelloPh.StartH0.mp_heapH hpw i fun k hk => ?_,
    hG' _ (by omega) (.inl ?_) _⟩
  · rw [hT]; unfold Scc.Sem.Range.contains; omega
  · rw [hT]; unfold Scc.Sem.Range.contains; omega

end Spike.Lib.X64.ArWCall

/-- info: 'Spike.Lib.X64.ArWCall.rt_hdr_loOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ArWCall.rt_hdr_loOf

/-- info: 'Spike.Lib.X64.ArWCall.okb_arW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ArWCall.okb_arW
