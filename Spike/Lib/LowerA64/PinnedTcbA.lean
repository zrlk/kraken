/-
**The first TCB is `Λ.pinned.lo + 8`** (AArch64; the twin of `Spike/Lib/LowerX64/PinnedTcb.lean`): at an output passing
`placeOKAt`, the runtime's `scc_rt_pinned` word (`rtA`, the label the
loaded thread gives it) is the pinned region's base `Λ.pinned.lo`, the
region the layout ties to the symbol (`regionsTied`); the symbol keeps
its address through the loader's symbol table (`loadSyms`, by
`symsAgree`). So the start's `me` word (`meW2`) is the number
`Λ.pinned.lo + 8`, the immediate `imms2Me` keys for `me`.

- `lookup_loadSymsA`: a symbol of the layout at its address in the loader's
  table;
- `rtA_pinned_of_placeOKAtA`: `rtA … "scc_rt_pinned" = Λ.pinned.lo`;
- `meW2_val_of_placeOKAtA`, `valRep_meW2_of_placeOKAtA`: `me`'s word is the
  number `Λ.pinned.lo + 8` and represents it.
-/
import Spike.Lib.LowerA64.Closed2OfA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- A filter by keys keeps the lookup of a key it keeps. -/
private theorem lookup_filter_key {β : Type} (P : String → Bool) (x : String) (hx : P x = true) :
    ∀ l : List (String × β), (l.filter (fun q => P q.1)).lookup x = l.lookup x
  | [] => rfl
  | (k, b) :: l => by
    by_cases hk : x = k
    · subst hk; simp [List.filter, hx, List.lookup]
    · have hne : (x == k) = false := by simpa using hk
      cases hP : P k <;> simp [List.filter, hP, List.lookup, hne, lookup_filter_key P x hx l]

/-- A filter by keys drops every entry of a key it drops. -/
private theorem lookup_filter_key_none {β : Type} (P : String → Bool) (x : String) (hx : P x = false) :
    ∀ l : List (String × β), (l.filter (fun q => P q.1)).lookup x = none
  | [] => rfl
  | (k, b) :: l => by
    by_cases hk : x = k
    · subst hk; simp [List.filter, hx, lookup_filter_key_none P x hx l]
    · have hne : (x == k) = false := by simpa using hk
      cases hP : P k <;> simp [List.filter, hP, List.lookup, hne, lookup_filter_key_none P x hx l]

private theorem lookup_append_none {β : Type} (x : String) :
    ∀ (l₁ l₂ : List (String × β)), l₁.lookup x = none → (l₁ ++ l₂).lookup x = l₂.lookup x
  | [], _, _ => rfl
  | (k, b) :: l₁, l₂, h => by
    by_cases hk : x = k
    · subst hk; simp [List.lookup] at h
    · have hne : (x == k) = false := by simpa using hk
      simp only [List.lookup, hne, List.cons_append] at h ⊢
      exact lookup_append_none x l₁ l₂ h

private theorem lookup_append_some {β : Type} (x : String) {b : β} :
    ∀ (l₁ l₂ : List (String × β)), l₁.lookup x = some b → (l₁ ++ l₂).lookup x = some b
  | [], _, h => by simp [List.lookup] at h
  | (k, b') :: l₁, l₂, h => by
    by_cases hk : x = k
    · subst hk; simpa [List.lookup] using h
    · have hne : (x == k) = false := by simpa using hk
      simp only [List.lookup, hne, List.cons_append] at h ⊢
      exact lookup_append_some x l₁ l₂ h

private theorem mem_of_lookup {β : Type} (x : String) {b : β} :
    ∀ l : List (String × β), l.lookup x = some b → (x, b) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k, b') :: l, h => by
    by_cases hk : x = k
    · subst hk; simp [List.lookup] at h; simp [h]
    · have hne : (x == k) = false := by simpa using hk
      simp only [List.lookup, hne] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup x l h)

/-- **A symbol of the layout at its address in the loader's table**: the
layout's symbols agree with the `.rodata` image (`symsAgree`), so a
symbol keeps its address whether or not it labels `.rodata`. -/
theorem lookup_loadSymsA {Λ : Scc.Sem.Layout} {items : List Kraken.DataImage.Item} {x : String} {v : Nat}
    (hag : Scc.Sem.symsAgree Λ items = true) (hx : Λ.symbols.lookup x = some v) :
    (Scc.Sem.loadSyms Λ items).lookup x = some v := by
  unfold Scc.Sem.loadSyms
  cases hd : Kraken.DataImage.dataLabel Λ.rodata.lo items x with
  | none =>
    apply lookup_append_some
    rw [lookup_filter_key (fun l => (Kraken.DataImage.dataLabel Λ.rodata.lo items l).isNone) x (by simp [hd])]
    exact hx
  | some b =>
    rw [lookup_append_none _ _ _ (lookup_filter_key_none
      (fun l => (Kraken.DataImage.dataLabel Λ.rodata.lo items l).isNone) x (by simp [hd]) _)]
    have hm := mem_of_lookup x _ hx
    simp only [Scc.Sem.symsAgree, List.all_eq_true] at hag
    have h1 := hag _ hm
    simp only [hd, beq_iff_eq] at h1
    subst h1
    exact hd

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out}

/-- **The runtime's `scc_rt_pinned` is the pinned region's base** at an
output passing `placeOKAt`: the symbol is decided (`rtWordsOk`) at its
address in the loader's table, the layout's `Λ.pinned.lo`
(`regionsTied`, `lookup_loadSymsA`). -/
theorem rtA_pinned_of_placeOKAtA (h : placeOKAt pcfg Λ o = true) :
    Scc.Cert.Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned" = BitVec.ofNat 64 Λ.pinned.lo := by
  have hrt := rtWordsOk_of_placeOKAt h
  simp only [Scc.Cert.Rt.A64.rtWordsOk, Bool.and_eq_true, List.all_eq_true] at hrt
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hrt.1.1 "scc_rt_pinned" (by decide))
  have hreg := regionsTied_of_placeOKAt h
  simp only [regionsTied, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hreg
  have hsym : Λ.symbols.lookup "scc_rt_pinned" = some Λ.pinned.lo := hreg.2.2.1
  have hld := loadOk_of_placeOKAt h
  simp only [Scc.Cert.Link.A64.loadOk, Bool.and_eq_true] at hld
  have hl := lookup_loadSymsA hld.1.1.1.1.1.1.2 hsym
  have ha' := ha
  simp only [Scc.Cert.Rt.A64.symLab, hl] at ha'
  split at ha'
  · cases ha'
    simp only [Scc.Cert.Rt.A64.rtA, ha, Option.getD_some]
  · cases ha'

/-- **`me`'s word at the start is the number `Λ.pinned.lo + 8`**, the first
TCB, at an output passing `placeOKAt` (`rtA_pinned_of_placeOKAtA`, the
pinned region below `2 ^ 32`). -/
theorem meW2_val_of_placeOKAtA (h : placeOKAt pcfg Λ o = true) :
    (meW2 Λ o).val = .num (Λ.pinned.lo + 8) := by
  have hb := below32_of_placeOKAt h Λ.pinned (by simp [Scc.Sem.Layout.regions])
  have hp : Λ.pinned.lo + 8 < 2 ^ 64 := by omega
  simp only [meW2, Spike.Lib.LowerNode.meNum, rtA_pinned_of_placeOKAtA h]
  show WeakMem.Val.num _ = _
  congr 1
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : Λ.pinned.lo < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

/-- **`me`'s word represents the first TCB** `Λ.pinned.lo + 8`
(`hv` of the setup call's placement, `placedS_setupCall`). -/
theorem valRep_meW2_of_placeOKAtA (h : placeOKAt pcfg Λ o = true) (lbl : WeakMem.AllocLabel → Option Nat) :
    Scc.Sem.ValRep lbl (meW2 Λ o).val (Λ.pinned.lo + 8) := by
  have hb := below32_of_placeOKAt h Λ.pinned (by simp [Scc.Sem.Layout.regions])
  rw [meW2_val_of_placeOKAtA h]
  exact ⟨by omega, rfl⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.valRep_meW2_of_placeOKAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms valRep_meW2_of_placeOKAtA

end Spike.Lib.LowerA64
