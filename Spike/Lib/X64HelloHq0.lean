/-
**rodata's buffer call's premises at the arena `arW`, on x86-64** (the twin of `Spike/Lib/A64HelloHq0.lean`):
at any `PlaceWX` output's runtime layout `Ly := RuntimeLayout.ofPlaceWX hpw i`, the arena `X64.WakeOD.arW hpw i` (its
counter zero-initialised, `CtrZ`), the memory side `msOfA (Ly).Λ μ rd G own arW I lbl lsize fs` at any marks, read
side, owned words, fragment, labels and frames, and a value invariant `G` admitting every value at every heap and
`.data` word (`hG`): rodata's `newBuf` at `rdCN` (two one-word lanes, header `257`) meets `Call.OK`, given the
counter word off every label (`hrtC`). This is `X64.ArWCall.okb_arW`'s twin for the buffer call; at the root's
memory side `msUH` it is the root's rodata premise `hq`.

- `ok_arW`: the buffer call at `rdCN` (`h = 257`, two elements, three units).
- `hq0_H`: the premise `hq` at `msUH` (any entry, read side, fragment, labels' sizes and frames), at any
  `mRdJ0 (rdJH (Ly).lab R J)`, the counter word off `L0T`'s words (`X64.WakePh.StartH0.rt_L0T`).

## Differences from the AArch64 version

- Over x86-64's `PlaceWX`, `RuntimeLayout.ofPlaceWX`, `X64.WakeOD.arW`, `X64ConsumerA.msOfA`, `X64.Alloc.Call`,
  `X64.Rt.ArenaW`, `X64HelloRodataSrc.rdCN`/`eW0` and `X64HelloGOf2H.hGpl_gWH`; the proofs are A64's.
- x86-64's `mNC` records the frame pointer, so `rdJH` takes the region `R`; `hq0_H` holds at every `R`.
-/
import Spike.Lib.X64HelloArWCall
import Spike.Lib.X64HelloStartH0U
import Spike.Lib.X64HelloStartWcS

namespace Spike.Lib.X64.HelloPh.Hq0

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.Flow.Hello1 (mRdJ0)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.HelloPh.StartH0U (msUH)
open Spike.Lib.X64HelloRodataSrc (rdCN eW0)
open Spike.Lib.Hello1RodataSrc (τ8)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o)

section Generic

variable (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "MS" => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd G own (Spike.Lib.X64.WakeOD.arW hpw i) I lbl lsize fs

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Spike.Lib.X64ConsumerS.OwnS} {I : Spike.Lib.X64ConsumerS.InvS} {lbl : Lbl} {lsize : Lsize}
  {fs : List TermRun.Frame}

/-- **The buffer call at `rdCN`** (module doc): `⟨rdCN, "b", m, τ8, eW0, int 2, [2], 2, 257, 0, 0⟩` meets
`Call.OK` at the memory side, its header `257`, two elements of three units. -/
theorem ok_arW (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hG : ∀ a v, (Ly).Λ.heap.contains a ∨ (Ly).Λ.data.contains a → G (Scc.Sem.wordLoc a) v)
    (hrtC : (MS).rt (BitVec.ofNat 64 (MS).ctr).toNat) :
    ∃ q : Call, q.OK (MS) (Ly).lab ∧ q.c0 = rdCN ∧ q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (MS) = 3#64 := by
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
  have hu3 : (MS).units 2 τ8 = 3 := rfl
  have hf8 : (MS).off 2 τ8 = 8 := rfl
  have hctrB : ∀ k < 8, (Ly).Λ.data.contains ((BitVec.ofNat 64 (MS).ctr).toNat + k) := fun k hk => by
    rw [hct, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; unfold Scc.Sem.Range.contains; omega
  have hG' : ∀ a : BitVec 64, a.toNat < 2 ^ 32 → ((Ly).Λ.heap.contains a.toNat ∨ (Ly).Λ.data.contains a.toNat) →
      ∀ v, (MS).G ⟨a, 8⟩ v := fun a _ hm v => by
    show G _ v
    simpa [Scc.Sem.wordLoc] using hG a.toNat v hm
  refine ⟨⟨rdCN, "b", .var "m", τ8, eW0, .intS (.lit 2), [TermRun.cst (.num 2)], 2, 257#64, 0#64, 0#64⟩,
    ⟨rfl, rfl, rfl, rfl, by decide,
      Spike.Lib.X64.Rt.ArenaW.arOf_ctrLab (Spike.Lib.PlaceWX.link i hpw) .linux,
      Spike.Lib.X64.Rt.ArenaW.arOf_heapLab (Spike.Lib.PlaceWX.link i hpw) .linux,
      by rw [hh]; omega, rfl, by rw [hu3]; decide, by rw [hf8]; decide, ⟨_, rfl⟩, hrtC,
      Spike.Lib.X64.HelloPh.StartH0.mp_dataH hpw i hctrB,
      fun _ _ _ => hG' _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
        (.inr (by rw [hct, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact ⟨hc1, by omega⟩)) _,
      fun o' hlo ho => ?_⟩, rfl, rfl, rfl, by show BitVec.ofNat 64 ((MS).units 2 τ8) = 3#64; rw [hu3]⟩
  have hd : Call.hdrAt (MS) ⟨rdCN, "b", .var "m", τ8, eW0, .intS (.lit 2), [TermRun.cst (.num 2)], 2, 257#64, 0#64,
      0#64⟩ o' = (MS).heap + 16 * o' := by simp [Call.hdrAt, Spike.Lib.X64.Alloc.mOf]
  change o' + (MS).units 2 τ8 ≤ (MS).cells at ho
  rw [hu3, hcl] at ho
  have hT : (BitVec.ofNat 64 (Call.hdrAt (MS) ⟨rdCN, "b", .var "m", τ8, eW0, .intS (.lit 2),
      [TermRun.cst (.num 2)], 2, 257#64, 0#64, 0#64⟩ o')).toNat = (Ly).Λ.heap.lo + 16 * o' := by
    rw [hd, hh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hd ▸ Spike.Lib.X64.ArWCall.rt_hdr_loOf hpw i hlo (by rw [hcl]; omega),
    Spike.Lib.X64.HelloPh.StartH0.mp_heapH hpw i fun k hk => ?_, hG' _ (by omega) (.inl ?_) _⟩
  · rw [hT]; unfold Scc.Sem.Range.contains; omega
  · rw [hT]; unfold Scc.Sem.Range.contains; omega

end Generic

variable (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls fs

/-- **The premise `hq` at the root's memory side** (module doc): at every `mRdJ0 (rdJH (Ly).lab R J)` state the
control is `rdCN` (`rdJH`), whose buffer call meets `Call.OK` at `msUH` (`ok_arW` at hello's value invariant,
`X64HelloGOf2H.hGpl_gWH`; the counter word off `L0T`'s words, `X64.WakePh.StartH0.rt_L0T`). -/
theorem hq0_H (hstat : Λ0.static = fun _ => none) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    {E : Entry} {rd : TermRun.Word → Prop} {I : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize}
    {fs : List TermRun.Frame} {R : Spike.Lib.Region} {J : FAS → Spike.Lib.Ctl → Prop} :
    ∀ σC σ c, mRdJ0 (rdJH (Ly).lab R J) σC σ c → ∃ q : Call, q.OK (MSU) (Ly).lab ∧
      q.c0 = c ∧ q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (MSU) = 3#64 := by
  rintro σC σ c ⟨-, rfl, -⟩
  exact ok_arW hpw IH hc
    (Spike.Lib.X64HelloGOf2H.hGpl_gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH) hpin2)
    (Spike.Lib.X64.WakePh.StartH0.rt_L0T (Λ := (Ly).Λ) hstat ls _)

end Spike.Lib.X64.HelloPh.Hq0

/-- info: 'Spike.Lib.X64.HelloPh.Hq0.ok_arW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Hq0.ok_arW

/-- info: 'Spike.Lib.X64.HelloPh.Hq0.hq0_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Hq0.hq0_H
