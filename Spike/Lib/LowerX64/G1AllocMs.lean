/-
**The allocator's memory side at every one-word allocation** (x86-64): at
the record of an output passing `placeOKAt`, `CallMsOK` holds at a call of
any `elem2` type whose header is the layout's array header, provided the
object layout's count field ends below bit `22` (the allocator's fixed
trace-word field).

- `regOf_elem2`, `countsO_elem2`: an `elem2` type's counts are `(1, 0)`;
- `mOf_header_elem2`: its array header has no trace words;
- `hms_of_elem2`: `CallMsOK` at the record's memory side over `arOf` and no
  placed label, by `callMsOK_arOf`.
-/
import Spike.Lib.LowerX64.ArCallMs
import Spike.Lib.Rt.X64CtrZOfEmitted
import Spike.Lib.LowerX64.G1AllocPt

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64ConsumerA (msOfAX)
open Spike.Lib.X64.Alloc (Call mOf)
open Spike.Lib.X64.Rt (RuntimeLayout arOf)

/-- **A one-word element's register counts**: an `elem2` type has counts
`(1, 0)` (`Obj.regOf`). -/
theorem regOf_elem2 {τ : Ty} (h : Scc.Lower.elem2 τ = true) : Scc.Obj.regOf τ = some (1, 0) := by
  cases τ <;> simp [Scc.Lower.elem2] at h <;> rfl

/-- **A one-word element's layout counts**: at any object layout, the
counts of an `elem2` type (`countsO`) are `(1, 0)`. -/
theorem countsO_elem2 {o : Scc.ObjLayout} {τ : Ty} (h : Scc.Lower.elem2 τ = true) {en em : Nat}
    (hc : Spike.Lib.LowerShape.countsO o τ = some (en, em)) : en = 1 ∧ em = 0 := by
  simp only [Spike.Lib.LowerShape.countsO, regOf_elem2 h] at hc
  revert hc
  cases Scc.Obj.counts o τ with
  | none => simp
  | some c =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    split
    · rename_i hcr; subst hcr; intro hh; cases hh; exact ⟨rfl, rfl⟩
    · simp

/-- **An `elem2` array header has no trace words**: at an object layout
whose count field ends below bit `22` (`hobj`), the array header of counts
`(1, 0)` is below `2 ^ 22`, so its trace-word field `mOf` is `0`. -/
theorem mOf_header_elem2 {o : Scc.ObjLayout} (hobj : Scc.Obj.nShift o < 22) {τ : Ty}
    (hel : Scc.Lower.elem2 τ = true) {en em hh : Nat}
    (hco : Spike.Lib.LowerShape.countsO o τ = some (en, em))
    (hhd : Scc.Obj.header0 o .array en em = some hh) :
    (Spike.Lib.X64.Alloc.mOf (BitVec.ofNat 64 hh)).toNat = 0 := by
  obtain ⟨rfl, rfl⟩ := countsO_elem2 hel hco
  simp only [Scc.Obj.header0] at hhd
  split at hhd
  · rename_i hfit
    cases hhd
    have hc : Scc.Obj.HeaderKind.array.code < 2 ^ o.kindBits := hfit.1
    have hk : 2 ^ o.kindBits ≤ 2 ^ Scc.Obj.nShift o :=
      Nat.pow_le_pow_right (by decide) (by simp [Scc.Obj.nShift])
    have hn : 2 ^ Scc.Obj.nShift o ≤ 2 ^ 21 :=
      Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_of_lt_succ hobj)
    have hlt : Scc.Obj.HeaderKind.array.code + 1 * 2 ^ Scc.Obj.nShift o + 0 * 2 ^ Scc.Obj.mShift o < 2 ^ 22 := by
      omega
    have hz : BitVec.ofNat 64 (Scc.Obj.HeaderKind.array.code + 1 * 2 ^ Scc.Obj.nShift o + 0 * 2 ^ Scc.Obj.mShift o)
        >>> 22 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt (by omega)]
      simp only [Nat.zero_mod]
      exact Nat.div_eq_of_lt hlt
    simp only [Spike.Lib.X64.Alloc.mOf, hz, BitVec.zero_and, BitVec.toNat_zero]
  · cases hhd

section Rec

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {cfg : Scc.Config} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
  (i : Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The runtime's layout of the output at the immediates `i`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i

set_option hygiene false in
/-- The record's initial memory. -/
local notation "M0" =>
  Spike.Lib.X64.PhRec.m0Of (Ly).Λ
    (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))
    (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs

/-- **`CallMsOK` at a one-word allocation** (`AllocPtV.hms`): at a call of
`kv` elements of an `elem2` type `τ` with the layout's array header, the
record's memory side over `arOf` at no placed label, by `callMsOK_arOf`
(the counter zeroed by `ctrZ_ofPlaceOK`, `GOf` free at the counter and the
heap, the header by `mOf_header_elem2` under `hobj`). -/
theorem hms_of_elem2 {o : Scc.ObjLayout} (hobj : Scc.Obj.nShift o < 22) {τ : Ty}
    (hel : Scc.Lower.elem2 τ = true) {rd : TermRun.Word → Prop} {I : Spike.Lib.X64ConsumerS.InvS}
    {ab : Option (Kraken.Promising.X64.State → Prop)} {ls : Spike.Lib.X64Consumer.Lsize}
    {fs : List TermRun.Frame} {en em hh : Nat} {kv : UInt64}
    (hco : Spike.Lib.LowerShape.countsO o τ = some (en, em))
    (hhd : Scc.Obj.header0 o .array en em = some hh) :
    ∀ q : Call, q.n = kv.toNat → q.τ = τ → q.h = BitVec.ofNat 64 hh →
      CallMsOK
        (msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd (Spike.Lib.X64.PhRec.GOf (Ly) M0)
          (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (arOf (Ly).Λ) I ab (fun _ => none) ls fs)
        (_root_.Executable.labels (Ly).exe).label q := by
  intro q _ hτ hqh
  obtain ⟨-, us, hus, -⟩ := elem2_words_accs hel
  exact callMsOK_arOf (cfg := pcfg) (Λ := (Ly).Λ) (o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)
    (μ := Spike.Lib.X64.PhRec.μ (Ly)) (p := p) (rd := rd) (own := fun s _ => Spike.Lib.X64.PhRec.own (Ly) s)
    (I := I) (ls := ls) (fs := fs) h (Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h)
    Scc.Sem.Entry.linux ab (gOf_ctr_arOf h i _) (gOf_heap_arOf h i _)
    (hacc := by rw [hτ]; exact ⟨us, hus⟩) (hm := by rw [hqh]; exact mOf_header_elem2 hobj hel hco hhd)

end Rec

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.regOf_elem2' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.regOf_elem2

/-- info: 'Spike.Lib.LowerX64.countsO_elem2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.countsO_elem2

/-- info: 'Spike.Lib.LowerX64.mOf_header_elem2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mOf_header_elem2

/-- info: 'Spike.Lib.LowerX64.hms_of_elem2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hms_of_elem2
