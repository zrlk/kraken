/-
**The loaded executable of a text and of the text with its last label moved
behind a tail** (AArch64; the granule pass's post-pass program is the
pre-pass program without its last label `scc_text_end:`, then a filler,
`.Lgw0:`, a word and `scc_text_end:`): their label tables agree off the
moved and new labels, and an instruction cell of the first is one of the
second.

- `codeAt_prefix`, `labels_prefix`: two executables sharing a prefix;
- `labels_threadAt_tail`, `cellAt_relab_tail`: the two loaded executables;
- `instr_ne_end`, `instr_mem_of_cellAt`: an instruction cell is short of any end at or past
  its code's, and an instruction of the program.
-/
import Spike.Lib.ExeTail
import Spike.Lib.A64RestTail
import Scc.Cert.Rt.LayoutA64

namespace Spike.Lib.A64ExeTail

open Kraken.Executable
open Spike.Lib.ExeTail

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

/-- **Two executables sharing a prefix of cells have the same label table**
off `B`, when their other cells place the labels off `B` that the prefix does
not have alike. -/
theorem labels_prefix {a : Int64} {A X Y : List (Directive × Nat)} {B : List Label}
    (hXY : ∀ l, l ∉ B → (∀ dz ∈ A, dz.1 ≠ .label l) →
      findLbl Directive.label l (withAddresses (a + Int64.ofNat (A.map (·.2)).sum, X)) =
        findLbl Directive.label l (withAddresses (a + Int64.ofNat (A.map (·.2)).sum, Y)))
    (l : Label) (hl : l ∉ B) :
    (_root_.Executable.labels (a, A ++ X)).label l = (_root_.Executable.labels (a, A ++ Y)).label l := by
  show (findLbl Directive.label l (withAddresses (a, A ++ X))).getD (-1) =
    (findLbl Directive.label l (withAddresses (a, A ++ Y))).getD (-1)
  simp only [findLbl, withAddresses_append, List.findSome?_append]
  cases hA : findLbl Directive.label l (withAddresses (a, A)) with
  | some p =>
    have hA' : (withAddresses (a, A)).findSome?
        (fun (p, d, _) => if d = .label l then some p else none) = some p := hA
    rw [hA']; rfl
  | none =>
    have hA' : (withAddresses (a, A)).findSome?
        (fun (p, d, _) => if d = .label l then some p else none) = none := hA
    rw [hA']
    have h := hXY l hl (findLbl_none_of hA)
    simp only [findLbl] at h
    simp only [Option.none_or, h]

open Scc.Sem Scc.Sem.A64

/-- The pad and label cells of the loader place no instruction and name
their labels. -/
private theorem pad_ne (x : String) : (Directive.byteArray (.mk #[]) : Directive) ≠ .label x := nofun

private theorem label_inj (x y : String) (h : (Directive.label x : Directive) = .label y) : x = y := by
  cases h; rfl

/-- The loaded executable as a shared prefix (the cells below the code and
the program `P`) and the rest (the program's tail `T` and the data symbols'
cells after the code). -/
private theorem threadAt_exe_split (E : Entry) (base : Nat) (P T : Program) (syms : List (String × Nat)) :
    (threadAt E base (P ++ T) syms).exe =
      (Int64.ofNat (exeStart base syms),
        (placeBelow (.byteArray (.mk #[])) .label base syms ++ P.map (fun d => (d, d.fakeSize))) ++
          (T.map (fun d => (d, d.fakeSize)) ++
            placeSyms (.byteArray (.mk #[])) .label (codeEnd base (P ++ T)) (symsFrom base syms))) := by
  refine Prod.ext rfl ?_
  rw [Scc.Cert.Rt.A64.threadAt_exe_cells]; simp only [List.map_append, List.append_assoc]

/-- The rest of the loaded executable starts at the end of its code. -/
private theorem split_end (base : Nat) (P T : Program) (syms : List (String × Nat)) :
    Int64.ofNat (exeStart base syms) +
        Int64.ofNat ((placeBelow (Directive.byteArray (.mk #[])) Directive.label base syms ++
          P.map (fun d => (d, d.fakeSize))).map (·.2)).sum +
        Int64.ofNat ((T.map (fun d : Directive => (d, d.fakeSize))).map (·.2)).sum =
      Int64.ofNat (codeEnd base (P ++ T)) := by
  have hB := (Scc.Cert.PlaceSyms.placeBelow_spec (Directive.byteArray (.mk #[])) Directive.label base syms).2
  rw [← Int64.ofNat_add, ← Int64.ofNat_add]; congr 1
  simp only [codeEnd, List.map_append, List.sum_append, List.map_map]
  have hf : ((·.2) ∘ fun d : Directive => (d, d.fakeSize)) = Directive.fakeSize := rfl
  rw [hf]
  omega

/-- **The label tables of a text and of the text with its last label moved
behind a tail agree off `B`**: the loaded executables of `P ++ [te:]` and
`P ++ T` at the same base and data symbols, `te` and every label of `T` in
`B`, the data symbols at or above the base all at or above the longer
code's end and named once. -/
theorem labels_threadAt_tail {E : Entry} {base : Nat} {P T : Program} {te : Label}
    {syms : List (String × Nat)} {B : List Label} (hte : te ∈ B)
    (hT : ∀ d ∈ T, ∀ l, d = .label l → l ∈ B)
    (hc : ∀ p ∈ symsFrom base syms, codeEnd base (P ++ T) ≤ p.2)
    (hone : ∀ p ∈ symsFrom base syms, ∀ q ∈ symsFrom base syms, p.1 = q.1 → p.2 = q.2)
    (l : Label) (hl : l ∉ B) :
    (_root_.Executable.labels (threadAt E base (P ++ [.label te]) syms).exe).label l =
      (_root_.Executable.labels (threadAt E base (P ++ T) syms).exe).label l := by
  rw [threadAt_exe_split, threadAt_exe_split]
  refine labels_prefix (fun l' hl' _ => ?_) l hl
  have hte' : ∀ dz ∈ [Directive.label te].map (fun d => (d, d.fakeSize)), dz.1 ≠ .label l' := by
    intro dz hdz h; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hdz; subst hdz
    cases h; exact hl' hte
  have hT' : ∀ dz ∈ T.map (fun d => (d, d.fakeSize)), dz.1 ≠ .label l' := by
    intro dz hdz h
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hdz
    exact hl' (hT d hd l' h)
  rw [findLbl_append_of_no hte', findLbl_append_of_no hT', split_end, split_end]
  have hle : codeEnd base (P ++ [.label te]) ≤ codeEnd base (P ++ T) := by
    simp only [codeEnd, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Directive.fakeSize]
    omega
  rw [findLbl_placeSyms pad_ne label_inj (fun p hp => Nat.le_trans hle (hc p hp)) hone,
    findLbl_placeSyms pad_ne label_inj hc hone]

open Kraken.Promising.AArch64 in
open Kraken.Promising.Lower.A64 (CellAt) in
open Spike.Lib.A64RestTail (relab) in
/-- **An instruction cell of the text is one of the text with its last label
moved behind a tail**: a state of the first loaded executable at an
instruction cell is, relabelled to the second (valid, its pc short of the
second's end), at the same cell. -/
theorem cellAt_relab_tail {E : Entry} {base : Nat} {P T : Program} {te : Label}
    {syms : List (String × Nat)} {endF : Int64} {s : State} {i : Instr} {z : Nat}
    [ValidLayout (threadAt E base (P ++ T) syms).exe]
    (hs : s.exe = (threadAt E base (P ++ [.label te]) syms).exe) (hcell : CellAt s (.instr i) z)
    (hne : (s.st.2 == endF) = false) :
    CellAt (relab (threadAt E base (P ++ T) syms).exe endF s) (.instr i) z := by
  obtain ⟨hv, -, rest, hcode⟩ := hcell
  rw [hs, threadAt_exe_split] at hv hcode
  have hvF := ‹ValidLayout (threadAt E base (P ++ T) syms).exe›
  rw [threadAt_exe_split] at hvF
  have hX : ∀ c ∈ [Directive.label te].map (fun d => (d, d.fakeSize)) ++
      placeSyms (.byteArray (.mk #[])) .label (codeEnd base (P ++ [.label te])) (symsFrom base syms),
      ∀ i, c.1 ≠ .instr i := by
    intro c hc i
    rcases List.mem_append.1 hc with hc | hc
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc; subst hc; exact nofun
    · rcases (Scc.Cert.PlaceSyms.placeSyms_spec (Directive.byteArray (.mk #[])) Directive.label _ _).1 c hc
        with ⟨h1, -⟩ | ⟨q, -, rfl⟩
      · rw [h1]; exact nofun
      · exact nofun
  obtain ⟨rest', hcode'⟩ := @codeAt_prefix _ _ _ _ hv hvF hX _ _ _ _ hcode
  refine ⟨‹_›, hne, rest', ?_⟩
  show codeAt (threadAt E base (P ++ T) syms).exe s.st.2 = _
  rw [threadAt_exe_split]; exact hcode'

open Kraken.Promising.AArch64 in
open Kraken.Promising.Lower.A64 (CellAt) in
/-- **An instruction cell of a loaded text is below the end of its code**:
the address of an instruction cell of `threadAt E base P syms` is short of
`codeEnd base P`, so short of any later end that fits in 64 bits. -/
theorem instr_ne_end {E : Entry} {base : Nat} {P : Program} {syms : List (String × Nat)} {s : State}
    {i : Instr} {z : Nat} (hs : s.exe = (threadAt E base P syms).exe) (hcell : CellAt s (.instr i) z)
    {n : Nat} (hn : codeEnd base P ≤ n) (hfit : n < 2 ^ 64) : (s.st.2 == Int64.ofNat n) = false := by
  obtain ⟨hv, -, rest, hcode⟩ := hcell
  have hsplit := threadAt_exe_split E base P [] syms
  simp only [List.append_nil, List.map_nil, List.nil_append] at hsplit
  rw [hs, hsplit] at hv hcode
  generalize hA : placeBelow (Directive.byteArray (.mk #[])) Directive.label base syms ++
    P.map (fun d => (d, d.fakeSize)) = A at hv hcode
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
  have hz : z = 4 := hv.instr_size m i z hdm
  have hdA : A[m]? = some (.instr i, z) := by
    have hdm' : (A ++ X)[m]? = some (.instr i, z) := hdm
    rwa [List.getElem?_append_left hmA] at hdm'
  -- the cell's offset plus its four bytes is at most the code's size
  have hlt : ((A.take m).map (·.2)).sum + 4 ≤ (A.map (·.2)).sum := by
    conv => rhs; rw [← List.take_append_drop m A]
    rw [List.drop_eq_getElem_cons hmA, List.getElem?_eq_getElem hmA] at *
    have hget : A[m] = (.instr i, z) := Option.some.inj hdA
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, hget, hz]
    omega
  have hsum : (A.map (·.2)).sum + exeStart base syms = codeEnd base P := by
    have hB := (Scc.Cert.PlaceSyms.placeBelow_spec (Directive.byteArray (.mk #[])) Directive.label base syms).2
    rw [← hA]
    simp only [codeEnd, List.map_append, List.sum_append, List.map_map]
    have hf : ((·.2) ∘ fun d : Directive => (d, d.fakeSize)) = Directive.fakeSize := rfl
    rw [hf]; omega
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

open Kraken.Promising.AArch64 in
open Kraken.Promising.Lower.A64 (CellAt) in
/-- **An instruction cell of a loaded text is an instruction of its program**
before a tail holding none: at a state of `threadAt E base (P ++ X) syms`
at an instruction cell, the instruction is one of `P`'s. -/
theorem instr_mem_of_cellAt {E : Entry} {base : Nat} {P X : Program} {syms : List (String × Nat)}
    {s : State} {i : Instr} {z : Nat} (hX : ∀ d ∈ X, ∀ i, d ≠ .instr i)
    (hs : s.exe = (threadAt E base (P ++ X) syms).exe) (hcell : CellAt s (.instr i) z) :
    Directive.instr i ∈ P := by
  obtain ⟨hv, -, rest, hcode⟩ := hcell
  rw [hs, threadAt_exe_split] at hv hcode
  obtain ⟨m, -, -, hdm, -⟩ := @codeAt_pos _ hv _ _ _ _ hcode
  have hmem := List.mem_of_getElem? hdm
  simp only [List.mem_append, List.mem_map] at hmem
  rcases hmem with (hB | ⟨d, hd, he⟩) | (⟨d', hd', he'⟩ | hS)
  · rcases (Scc.Cert.PlaceSyms.placeBelow_spec (Directive.byteArray (.mk #[])) Directive.label base syms).1 _ hB
      with ⟨h1, -⟩ | ⟨q, -, h1⟩
    · cases h1
    · cases h1
  · simp only [Prod.mk.injEq] at he; rw [← he.1]; exact hd
  · simp only [Prod.mk.injEq] at he'; exact absurd he'.1 (hX d' hd' i)
  · rcases (Scc.Cert.PlaceSyms.placeSyms_spec (Directive.byteArray (.mk #[])) Directive.label _ _).1 _ hS
      with ⟨h1, -⟩ | ⟨q, -, h1⟩
    · cases h1
    · cases h1

end Spike.Lib.A64ExeTail

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64ExeTail.labels_threadAt_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ExeTail.labels_threadAt_tail

/-- info: 'Spike.Lib.A64ExeTail.cellAt_relab_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ExeTail.cellAt_relab_tail

/-- info: 'Spike.Lib.A64ExeTail.instr_ne_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ExeTail.instr_ne_end

/-- info: 'Spike.Lib.A64ExeTail.instr_mem_of_cellAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ExeTail.instr_mem_of_cellAt
