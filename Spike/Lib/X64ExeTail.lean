/-
**The loaded executable of a text and of the text with its last label moved
behind a tail** (x86-64; the granule pass's post-pass cells are the
pre-pass cells without `scc_text_end:`, then a filler, `.Lgw0:`, a word and
`scc_text_end:`): their label tables agree off the moved and new labels,
and an instruction cell of the first is one of the second.

- `withAddresses_append`, `findLbl`, `findLbl_none_of`, `findLbl_none_of_no`,
  `findLbl_append_of_no`, `findLbl_label_cons`: laid-out cells and their
  first label cells;
- `codeAt_prefix`, `labels_prefix`: two executables sharing a prefix;
- `findLbl_placeSyms`: the data symbols' label cells after the code sit at
  the symbols' addresses whatever the code's end;
- `labels_threadAt_tail`, `cellAt_relab_tail`: the two loaded executables;
- `instr_ne_end`, `instr_mem_of_cellAt`: an instruction cell is short of any
  end at or past its code's, and a cell of the program.
-/
import Kraken.CodeAt
import Spike.Lib.ExeTail
import Scc.Cert.PlaceSyms
import Scc.Cert.LinkX64
import Spike.Lib.X64RestTail

namespace Spike.Lib.X64ExeTail

open Kraken.Executable

/-- The cells of an executable laid out from `a`, one list after another. -/
theorem withAddresses_append : ∀ (A X : List (Directive × Nat)) (a : Int64),
    Kraken.Executable.withAddresses (a, A ++ X) =
      Kraken.Executable.withAddresses (a, A) ++
        Kraken.Executable.withAddresses (a + Int64.ofNat (A.map (·.2)).sum, X) :=
  Spike.Lib.ExeTail.withAddresses_append

/-- **An instruction of a common prefix is found alike** in two executables
from the same start whose cells share the prefix `A`, the first's other
cells holding no instruction. -/
theorem codeAt_prefix {a : Int64} {A X Y : List (Directive × Nat)} [ValidLayout (a, A ++ X)]
    [ValidLayout (a, A ++ Y)] (hX : ∀ c ∈ X, ∀ i, c.1 ≠ .instr i) {pc : Int64} {i : Instr} {z : Nat}
    {rest : List (Directive × Nat)} (h : codeAt (a, A ++ X) pc = (.instr i, z) :: rest) :
    ∃ rest', codeAt (a, A ++ Y) pc = (.instr i, z) :: rest' := by
  obtain ⟨m, -, hpc, hdm, -⟩ := codeAt_pos (a, A ++ X) h
  have hmA : m < A.length := by
    rcases Nat.lt_or_ge m A.length with hc | hc
    · exact hc
    · have hdm' : (A ++ X)[m]? = some (.instr i, z) := hdm
      rw [List.getElem?_append_right hc] at hdm'
      exact absurd rfl (hX _ (List.mem_of_getElem? hdm') i)
  have haddr : addrOf (a, A ++ Y) m = addrOf (a, A ++ X) m := by
    simp only [addrOf, sizeBefore, List.take_append_of_le_length (Nat.le_of_lt hmA)]
  have hdY : (A ++ Y)[m]? = some (.instr i, z) := by
    have hdm' : (A ++ X)[m]? = some (.instr i, z) := hdm
    rw [List.getElem?_append_left hmA] at hdm' ⊢; exact hdm'
  have hlt : m < (A ++ Y).length := by simp only [List.length_append]; omega
  refine ⟨(A ++ Y).drop (m + 1), ?_⟩
  rw [← hpc, ← haddr, codeAt_addrOf_drop (a, A ++ Y) (Nat.le_of_lt hlt)]
  show ((A ++ Y).drop m).dropWhile _ = _
  rw [List.drop_eq_getElem_cons hlt]
  have hget : (A ++ Y)[m] = (.instr i, z) := by
    rw [List.getElem?_eq_getElem hlt] at hdY; exact Option.some.inj hdY
  rw [hget]
  simp [Directive.isLabel]

/-- The address of the first label cell named `l` among laid-out cells. -/
def findLbl (l : Label) (W : List (Int64 × Directive × Nat)) : Option Int64 :=
  W.findSome? fun (p, d, _) => if d = .label l then some p else none

/-- No first label cell `l`: no cell is the label `l`. -/
theorem findLbl_none_of {l : Label} : ∀ {ds : List (Directive × Nat)} {a : Int64},
    findLbl l (Kraken.Executable.withAddresses (a, ds)) = none → ∀ dz ∈ ds, dz.1 ≠ .label l :=
  Spike.Lib.ExeTail.findLbl_none_of

/-- **Two executables sharing a prefix of cells have the same label table**
off `B`, when their other cells place the labels off `B` that the prefix does
not have alike. -/
theorem labels_prefix {a : Int64} {A X Y : List (Directive × Nat)} {B : List Label}
    (hXY : ∀ l, l ∉ B → (∀ dz ∈ A, dz.1 ≠ .label l) →
      findLbl l (Kraken.Executable.withAddresses (a + Int64.ofNat (A.map (·.2)).sum, X)) =
        findLbl l (Kraken.Executable.withAddresses (a + Int64.ofNat (A.map (·.2)).sum, Y)))
    (l : Label) (hl : l ∉ B) :
    (_root_.Executable.labels (a, A ++ X)).label l = (_root_.Executable.labels (a, A ++ Y)).label l := by
  show ((Kraken.Executable.withAddresses (a, A ++ X)).findSome? _).getD (-1) =
    ((Kraken.Executable.withAddresses (a, A ++ Y)).findSome? _).getD (-1)
  rw [withAddresses_append, withAddresses_append, List.findSome?_append, List.findSome?_append]
  cases hA : findLbl l (Kraken.Executable.withAddresses (a, A)) with
  | some p =>
    have hA' : (Kraken.Executable.withAddresses (a, A)).findSome?
        (fun (p, d, _) => if d = .label l then some p else none) = some p := hA
    rw [hA']; rfl
  | none =>
    have hA' : (Kraken.Executable.withAddresses (a, A)).findSome?
        (fun (p, d, _) => if d = .label l then some p else none) = none := hA
    rw [hA']
    have h := hXY l hl (findLbl_none_of hA)
    simp only [findLbl] at h
    simp only [Option.none_or, h]

/-- No cell the label `l`: no label `l` among the laid-out cells. -/
theorem findLbl_none_of_no {l : Label} : ∀ {ds : List (Directive × Nat)} {a : Int64},
    (∀ dz ∈ ds, dz.1 ≠ .label l) → findLbl l (Kraken.Executable.withAddresses (a, ds)) = none :=
  Spike.Lib.ExeTail.findLbl_none_of_no

/-- **Past cells without the label `l`**, its first cell is the rest's. -/
theorem findLbl_append_of_no {l : Label} {A X : List (Directive × Nat)} {a : Int64}
    (hA : ∀ dz ∈ A, dz.1 ≠ .label l) :
    findLbl l (Kraken.Executable.withAddresses (a, A ++ X)) =
      findLbl l (Kraken.Executable.withAddresses (a + Int64.ofNat (A.map (·.2)).sum, X)) :=
  Spike.Lib.ExeTail.findLbl_append_of_no hA

/-- A label cell first: its address. -/
theorem findLbl_label_cons (l : Label) (X : List (Directive × Nat)) (a : Int64) :
    findLbl l (Kraken.Executable.withAddresses (a, (.label l, 0) :: X)) = some a :=
  Spike.Lib.ExeTail.findLbl_label_cons l X a

open Scc.Sem in
/-- **The data symbols' label cells after the code** are at the symbols'
addresses, whatever the end of the code below them: the first label `l`
among `placeSyms … cur syms` laid out from `cur` is at the address of the
symbol named `l` (names unique, every symbol at or above `cur`). -/
theorem findLbl_placeSyms {cur : Nat} {syms : List (String × Nat)} (hc : ∀ p ∈ syms, cur ≤ p.2)
    (hone : ∀ p ∈ syms, ∀ q ∈ syms, p.1 = q.1 → p.2 = q.2) (l : Label) :
    findLbl l (Kraken.Executable.withAddresses
        (Int64.ofNat cur, placeSyms (Directive.byteArray (.mk #[])) Directive.label cur syms)) =
      (syms.find? (·.1 == l)).map fun p => Int64.ofNat p.2 :=
  Spike.Lib.ExeTail.findLbl_placeSyms (lbl := Directive.label) (pad := .byteArray (.mk #[]))
    (fun _ h => nomatch h) (fun _ _ h => Directive.label.inj h) hc hone l

open Scc.Sem Scc.Sem.X64 in
/-- **The label tables of a text and of the text with its last label moved
behind a tail agree off `B`**: the loaded executables of `P ++ [te:]` and
`P ++ T` at the same base and data symbols, `te` and every label of `T` in
`B`, the data symbols at or above the base all at or above the longer
code's end and named once. -/
theorem labels_threadAt_tail {E : Entry} {base : Nat} {P T : List (Directive × Nat)} {te : Label}
    {syms : List (String × Nat)} {B : List Label} (hte : te ∈ B)
    (hT : ∀ dz ∈ T, ∀ l, dz.1 = .label l → l ∈ B)
    (hc : ∀ p ∈ symsFrom base syms, codeEnd base (P ++ T) ≤ p.2)
    (hone : ∀ p ∈ symsFrom base syms, ∀ q ∈ symsFrom base syms, p.1 = q.1 → p.2 = q.2)
    (l : Label) (hl : l ∉ B) :
    (_root_.Executable.labels (threadAt E base (P ++ [(.label te, 0)]) syms).exe).label l =
      (_root_.Executable.labels (threadAt E base (P ++ T) syms).exe).label l := by
  let pB := placeBelow (Directive.byteArray (.mk #[])) Directive.label base syms
  have hB : (pB.map (·.2)).sum + exeStart base syms = base :=
    (Scc.Cert.PlaceSyms.placeBelow_spec (Directive.byteArray (.mk #[])) Directive.label base syms).2
  have hE : (threadAt E base (P ++ [(.label te, 0)]) syms).exe =
      (Int64.ofNat (exeStart base syms), (pB ++ P) ++ ([(.label te, 0)] ++
        placeSyms (Directive.byteArray (.mk #[])) Directive.label (codeEnd base (P ++ [(.label te, 0)]))
          (symsFrom base syms))) := by
    refine Prod.ext rfl ?_
    rw [Scc.Cert.Link.X64.threadAt_exe_cells]; simp only [pB, List.append_assoc]
  have hF : (threadAt E base (P ++ T) syms).exe =
      (Int64.ofNat (exeStart base syms), (pB ++ P) ++ (T ++
        placeSyms (Directive.byteArray (.mk #[])) Directive.label (codeEnd base (P ++ T)) (symsFrom base syms))) := by
    refine Prod.ext rfl ?_
    rw [Scc.Cert.Link.X64.threadAt_exe_cells]; simp only [pB, List.append_assoc]
  rw [hE, hF]
  refine labels_prefix (fun l' hl' _ => ?_) l hl
  have hte' : ∀ dz ∈ [((Directive.label te : Directive), 0)], dz.1 ≠ .label l' := by
    intro dz hdz h; simp only [List.mem_singleton] at hdz; subst hdz
    cases h; exact hl' hte
  have hT' : ∀ dz ∈ T, dz.1 ≠ .label l' := fun dz hdz h => hl' (hT dz hdz l' h)
  rw [findLbl_append_of_no hte', findLbl_append_of_no hT']
  have hsE : Int64.ofNat (exeStart base syms) + Int64.ofNat ((pB ++ P).map (·.2)).sum +
      Int64.ofNat ([((Directive.label te : Directive), 0)].map (·.2)).sum =
      Int64.ofNat (codeEnd base (P ++ [(.label te, 0)])) := by
    rw [← Int64.ofNat_add, ← Int64.ofNat_add]; congr 1
    simp only [codeEnd, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  have hsF : Int64.ofNat (exeStart base syms) + Int64.ofNat ((pB ++ P).map (·.2)).sum +
      Int64.ofNat (T.map (·.2)).sum = Int64.ofNat (codeEnd base (P ++ T)) := by
    rw [← Int64.ofNat_add, ← Int64.ofNat_add]; congr 1
    simp only [codeEnd, List.map_append, List.sum_append]
    omega
  have hle : codeEnd base (P ++ [(.label te, 0)]) ≤ codeEnd base (P ++ T) := by
    simp only [codeEnd, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  rw [hsE, hsF, findLbl_placeSyms (fun p hp => Nat.le_trans hle (hc p hp)) hone,
    findLbl_placeSyms hc hone]

open Scc.Sem Scc.Sem.X64 Kraken.Promising.X64 in
open Kraken.Promising.Lower.X64 (CellAt) in
open Spike.Lib.X64RestTail (relab) in
/-- **An instruction cell of the text is one of the text with its last label
moved behind a tail**: a state of the first loaded executable at an
instruction cell is, relabelled to the second (valid, its pc short of the
second's end), at the same cell. -/
theorem cellAt_relab_tail {E : Entry} {base : Nat} {P T : List (Directive × Nat)} {te : Label}
    {syms : List (String × Nat)} {endF : Int64} {s : State} {i : Instr} {z : Nat}
    [Kraken.Executable.ValidLayout (threadAt E base (P ++ T) syms).exe]
    (hs : s.exe = (threadAt E base (P ++ [(.label te, 0)]) syms).exe) (hcell : CellAt s (.instr i) z)
    (hne : (s.st.2 == endF) = false) :
    CellAt (relab (threadAt E base (P ++ T) syms).exe endF s) (.instr i) z := by
  obtain ⟨hv, -, rest, hcode⟩ := hcell
  let pB := placeBelow (Directive.byteArray (.mk #[])) Directive.label base syms
  have hE : (threadAt E base (P ++ [(.label te, 0)]) syms).exe =
      (Int64.ofNat (exeStart base syms), (pB ++ P) ++ ([(.label te, 0)] ++
        placeSyms (Directive.byteArray (.mk #[])) Directive.label (codeEnd base (P ++ [(.label te, 0)]))
          (symsFrom base syms))) := by
    refine Prod.ext rfl ?_
    rw [Scc.Cert.Link.X64.threadAt_exe_cells]; simp only [pB, List.append_assoc]
  have hF : (threadAt E base (P ++ T) syms).exe =
      (Int64.ofNat (exeStart base syms), (pB ++ P) ++ (T ++
        placeSyms (Directive.byteArray (.mk #[])) Directive.label (codeEnd base (P ++ T)) (symsFrom base syms))) := by
    refine Prod.ext rfl ?_
    rw [Scc.Cert.Link.X64.threadAt_exe_cells]; simp only [pB, List.append_assoc]
  rw [hs, hE] at hv hcode
  have hvF := ‹Kraken.Executable.ValidLayout (threadAt E base (P ++ T) syms).exe›
  rw [hF] at hvF
  have hX : ∀ c ∈ [((Directive.label te : Directive), 0)] ++
      placeSyms (Directive.byteArray (.mk #[])) Directive.label (codeEnd base (P ++ [(.label te, 0)]))
        (symsFrom base syms), ∀ i, c.1 ≠ .instr i := by
    intro c hc i
    rcases List.mem_append.1 hc with hc | hc
    · simp only [List.mem_singleton] at hc; subst hc; exact fun h => nomatch h
    · rcases (Scc.Cert.PlaceSyms.placeSyms_spec (Directive.byteArray (.mk #[])) Directive.label _ _).1 c hc
        with ⟨h1, -⟩ | ⟨q, -, rfl⟩
      · rw [h1]; exact fun h => nomatch h
      · exact fun h => nomatch h
  obtain ⟨rest', hcode'⟩ := @codeAt_prefix _ _ _ _ hv hvF hX _ _ _ _ hcode
  refine ⟨?_, hne, rest', ?_⟩
  · show Kraken.Executable.ValidLayout (threadAt E base (P ++ T) syms).exe
    infer_instance
  · show Kraken.Executable.codeAt (threadAt E base (P ++ T) syms).exe s.st.2 = _
    rw [hF]; exact hcode'

open Scc.Sem Scc.Sem.X64 Kraken.Promising.X64 in
open Kraken.Promising.Lower.X64 (CellAt) in
/-- **An instruction cell of a loaded text is below the end of its code**:
the address of an instruction cell of `threadAt E base P syms` is short of
`codeEnd base P`, so short of any later end that fits in 64 bits. -/
theorem instr_ne_end {E : Entry} {base : Nat} {P : List (Directive × Nat)} {syms : List (String × Nat)}
    {s : State} {i : Instr} {z : Nat} (hs : s.exe = (threadAt E base P syms).exe)
    (hcell : CellAt s (.instr i) z) {n : Nat} (hn : codeEnd base P ≤ n) (hfit : n < 2 ^ 64) :
    (s.st.2 == Int64.ofNat n) = false := by
  obtain ⟨hv, -, rest, hcode⟩ := hcell
  have hE : (threadAt E base P syms).exe =
      (Int64.ofNat (exeStart base syms), (placeBelow (Directive.byteArray (.mk #[])) Directive.label base syms ++ P)
        ++ placeSyms (Directive.byteArray (.mk #[])) Directive.label (codeEnd base P) (symsFrom base syms)) := by
    refine Prod.ext rfl ?_
    rw [Scc.Cert.Link.X64.threadAt_exe_cells, List.append_assoc]
  rw [hs, hE] at hv hcode
  generalize hA : placeBelow (Directive.byteArray (.mk #[])) Directive.label base syms ++ P = A at hv hcode
  generalize hX : placeSyms (Directive.byteArray (.mk #[])) Directive.label (codeEnd base P)
    (symsFrom base syms) = X at hv hcode
  obtain ⟨m, -, hpc, hdm, -⟩ := @codeAt_pos _ hv _ _ _ _ hcode
  have hmA : m < A.length := by
    rcases Nat.lt_or_ge m A.length with hc | hc
    · exact hc
    · have hdm' : (A ++ X)[m]? = some (.instr i, z) := hdm
      rw [List.getElem?_append_right hc, ← hX] at hdm'
      rcases (Scc.Cert.PlaceSyms.placeSyms_spec (Directive.byteArray (.mk #[])) Directive.label _ _).1 _
          (List.mem_of_getElem? hdm') with ⟨h1, -⟩ | ⟨q, -, h1⟩
      · cases h1
      · cases h1
  have hz : 0 < z := hv.instr_size m _ z hdm (fun l h => nomatch h)
  have hdA : A[m]? = some (.instr i, z) := by
    have hdm' : (A ++ X)[m]? = some (.instr i, z) := hdm
    rwa [List.getElem?_append_left hmA] at hdm'
  have hlt : ((A.take m).map (·.2)).sum + z ≤ (A.map (·.2)).sum := by
    have hsplit := List.take_append_drop m A
    rw [List.drop_eq_getElem_cons hmA] at hsplit
    have hget : A[m] = (.instr i, z) := Option.some.inj ((List.getElem?_eq_getElem hmA).symm.trans hdA)
    have := congrArg (fun l : List (Directive × Nat) => (l.map (·.2)).sum) hsplit
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, hget] at this
    omega
  have hsum : (A.map (·.2)).sum + exeStart base syms = codeEnd base P := by
    have hB := (Scc.Cert.PlaceSyms.placeBelow_spec (Directive.byteArray (.mk #[])) Directive.label base syms).2
    rw [← hA]
    simp only [codeEnd, List.map_append, List.sum_append]
    omega
  have hpc' : s.st.2 = Int64.ofNat (exeStart base syms + ((A.take m).map (·.2)).sum) := by
    rw [← hpc]
    show Int64.ofNat (exeStart base syms) + Int64.ofNat (((A ++ X).take m).map (·.2)).sum = _
    rw [List.take_append_of_le_length (Nat.le_of_lt hmA), Int64.ofNat_add]
  rw [hpc']
  apply beq_false_of_ne
  intro he
  have := congrArg (fun x : Int64 => x.toBitVec.toNat) he
  simp only [Int64.toBitVec_ofNat', BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hfit] at this
  omega

open Scc.Sem Scc.Sem.X64 Kraken.Promising.X64 in
open Kraken.Promising.Lower.X64 (CellAt) in
/-- **An instruction cell of a loaded text is an instruction of its program**
before a tail holding none: at a state of `threadAt E base (P ++ X) syms`
at an instruction cell, the instruction is one of `P`'s. -/
theorem instr_mem_of_cellAt {E : Entry} {base : Nat} {P X : List (Directive × Nat)}
    {syms : List (String × Nat)} {s : State} {i : Instr} {z : Nat} (hX : ∀ dz ∈ X, ∀ i, dz.1 ≠ .instr i)
    (hs : s.exe = (threadAt E base (P ++ X) syms).exe) (hcell : CellAt s (.instr i) z) :
    (Directive.instr i, z) ∈ P := by
  obtain ⟨hv, -, rest, hcode⟩ := hcell
  have hE : (threadAt E base (P ++ X) syms).exe =
      (Int64.ofNat (exeStart base syms), placeBelow (Directive.byteArray (.mk #[])) Directive.label base syms ++
        (P ++ X ++ placeSyms (Directive.byteArray (.mk #[])) Directive.label (codeEnd base (P ++ X))
          (symsFrom base syms))) :=
    Prod.ext rfl (Scc.Cert.Link.X64.threadAt_exe_cells _ _ _ _)
  rw [hs, hE] at hv hcode
  obtain ⟨m, -, -, hdm, -⟩ := @codeAt_pos _ hv _ _ _ _ hcode
  have hmem := List.mem_of_getElem? hdm
  simp only [List.mem_append] at hmem
  rcases hmem with hB | (hP | hX') | hS
  · rcases (Scc.Cert.PlaceSyms.placeBelow_spec (Directive.byteArray (.mk #[])) Directive.label base syms).1 _ hB
      with ⟨h1, -⟩ | ⟨q, -, h1⟩
    · cases h1
    · cases h1
  · exact hP
  · exact absurd rfl (hX _ hX' i)
  · rcases (Scc.Cert.PlaceSyms.placeSyms_spec (Directive.byteArray (.mk #[])) Directive.label _ _).1 _ hS
      with ⟨h1, -⟩ | ⟨q, -, h1⟩
    · cases h1
    · cases h1

end Spike.Lib.X64ExeTail

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64ExeTail.labels_threadAt_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ExeTail.labels_threadAt_tail

/-- info: 'Spike.Lib.X64ExeTail.cellAt_relab_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ExeTail.cellAt_relab_tail

/-- info: 'Spike.Lib.X64ExeTail.instr_ne_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ExeTail.instr_ne_end

/-- info: 'Spike.Lib.X64ExeTail.instr_mem_of_cellAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ExeTail.instr_mem_of_cellAt
