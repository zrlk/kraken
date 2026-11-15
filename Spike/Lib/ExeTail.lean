/-
**Laid-out cells and their first label cells** (ISA-neutral; shared by the
proofs, on both ISAs, that a text and the text with its last label moved
behind a tail load to executables with the same label table off the moved
and new labels). Each ISA's `Executable.labels` is the first label cell's
address among `withAddresses`; `findLbl lbl` is that search over a cell type
`D` with label cells `lbl l`.

- `withAddresses_append`: cells laid out one list after another;
- `findLbl`, `findLbl_none_of`, `findLbl_none_of_no`, `findLbl_append_of_no`,
  `findLbl_label_cons`: the first label cell;
- `findLbl_placeSyms`: the data symbols' label cells after the code sit at
  the symbols' addresses whatever the code's end.
-/
import Kraken.Layout
import Scc.Cert.PlaceSyms

namespace Spike.Lib.ExeTail

variable {D : Type}

/-- The cells of an executable laid out from `a`, one list after another. -/
theorem withAddresses_append : ∀ (A X : List (D × Nat)) (a : Int64),
    Kraken.Executable.withAddresses (a, A ++ X) =
      Kraken.Executable.withAddresses (a, A) ++
        Kraken.Executable.withAddresses (a + Int64.ofNat (A.map (·.2)).sum, X)
  | [], X, a => by
    have h0 : Kraken.Executable.withAddresses (a, ([] : List (D × Nat))) = [] := by
      rw [Kraken.Executable.withAddresses]
    simp [h0]
  | (d, z) :: A, X, a => by
    rw [List.cons_append]
    conv => lhs; rw [Kraken.Executable.withAddresses]
    conv => rhs; arg 1; rw [Kraken.Executable.withAddresses]
    rw [withAddresses_append A X, List.cons_append]
    congr 3
    simp only [List.map_cons, List.sum_cons]
    congr 1
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat']
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [Nat.add_mod]

variable [DecidableEq D] (lbl : String → D)

/-- The address of the first label cell named `l` among laid-out cells. -/
def findLbl (l : String) (W : List (Int64 × D × Nat)) : Option Int64 :=
  W.findSome? fun (p, d, _) => if d = lbl l then some p else none

variable {lbl}

/-- No first label cell `l`: no cell is the label `l`. -/
theorem findLbl_none_of {l : String} : ∀ {ds : List (D × Nat)} {a : Int64},
    findLbl lbl l (Kraken.Executable.withAddresses (a, ds)) = none → ∀ dz ∈ ds, dz.1 ≠ lbl l
  | [], _, _ => by simp
  | (d, z) :: ds, a, h => by
    rw [Kraken.Executable.withAddresses] at h
    simp only [findLbl, List.findSome?_cons] at h
    split at h
    · cases h
    · rename_i hn
      intro dz hdz
      rcases List.mem_cons.1 hdz with rfl | hdz
      · intro he; simp only at he; simp [he] at hn
      · exact findLbl_none_of h dz hdz

/-- No cell the label `l`: no label `l` among the laid-out cells. -/
theorem findLbl_none_of_no {l : String} : ∀ {ds : List (D × Nat)} {a : Int64},
    (∀ dz ∈ ds, dz.1 ≠ lbl l) → findLbl lbl l (Kraken.Executable.withAddresses (a, ds)) = none
  | [], _, _ => by rw [Kraken.Executable.withAddresses]; rfl
  | (d, z) :: ds, a, h => by
    rw [Kraken.Executable.withAddresses]
    simp only [findLbl, List.findSome?_cons]
    have hd : d ≠ lbl l := h _ List.mem_cons_self
    simp only [hd, ↓reduceIte]
    exact findLbl_none_of_no (fun dz hdz => h dz (List.mem_cons_of_mem _ hdz))

/-- **Past cells without the label `l`**, its first cell is the rest's. -/
theorem findLbl_append_of_no {l : String} {A X : List (D × Nat)} {a : Int64}
    (hA : ∀ dz ∈ A, dz.1 ≠ lbl l) :
    findLbl lbl l (Kraken.Executable.withAddresses (a, A ++ X)) =
      findLbl lbl l (Kraken.Executable.withAddresses (a + Int64.ofNat (A.map (·.2)).sum, X)) := by
  have h := findLbl_none_of_no (a := a) hA
  simp only [findLbl] at h ⊢
  rw [withAddresses_append, List.findSome?_append, h, Option.none_or]

/-- A label cell first: its address. -/
theorem findLbl_label_cons (l : String) (X : List (D × Nat)) (a : Int64) :
    findLbl lbl l (Kraken.Executable.withAddresses (a, (lbl l, 0) :: X)) = some a := by
  rw [Kraken.Executable.withAddresses]
  simp [findLbl]

open Scc.Sem in
/-- **The data symbols' label cells after the code** are at the symbols'
addresses, whatever the end of the code below them: the first label `l`
among `placeSyms … cur syms` laid out from `cur` is at the address of the
symbol named `l` (names unique, every symbol at or above `cur`; padding no
label cell, label cells naming their labels). -/
theorem findLbl_placeSyms {pad : D} (hpad : ∀ x, pad ≠ lbl x) (hlbl : ∀ x y, lbl x = lbl y → x = y)
    {cur : Nat} {syms : List (String × Nat)} (hc : ∀ p ∈ syms, cur ≤ p.2)
    (hone : ∀ p ∈ syms, ∀ q ∈ syms, p.1 = q.1 → p.2 = q.2) (l : String) :
    findLbl lbl l (Kraken.Executable.withAddresses (Int64.ofNat cur, placeSyms pad lbl cur syms)) =
      (syms.find? (·.1 == l)).map fun p => Int64.ofNat p.2 := by
  cases hf : syms.find? (·.1 == l) with
  | some p =>
    have hm := List.mem_of_find?_eq_some hf
    have hl : p.1 = l := by simpa using List.find?_some hf
    obtain ⟨x, a⟩ := p
    simp only at hl
    subst hl
    obtain ⟨pre, post, he, hpre, hsum⟩ := Scc.Cert.PlaceSyms.placeSyms_label pad lbl hpad hlbl hm (hc _ hm)
      (fun q hq hq1 => hone q hq _ hm hq1)
    rw [he, findLbl_append_of_no hpre, findLbl_label_cons]
    simp only [Option.map_some]
    congr 1
    rw [← hsum, Nat.add_comm, Int64.ofNat_add]
  | none =>
    simp only [Option.map_none]
    apply findLbl_none_of_no
    intro dz hdz
    rcases (Scc.Cert.PlaceSyms.placeSyms_spec pad lbl cur syms).1 dz hdz with ⟨h1, -⟩ | ⟨q, hq, rfl⟩
    · rw [h1]; exact hpad l
    · intro h
      have := List.find?_eq_none.1 hf q hq
      simp [hlbl _ _ h] at this

end Spike.Lib.ExeTail

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.ExeTail.findLbl_placeSyms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.ExeTail.findLbl_placeSyms
