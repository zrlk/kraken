import Scc.Cert.LinkImage
import Scc.Cert.Rt.LaysX64
import Scc.Sem.LoadX64
import Scc.Cert.PlaceSyms

/-!
# The static link of an emitted x64 text

The x64 twin of `Scc/Cert/LinkA64.lean`: what `scc --code` needs to state the
layout of an x64 listing and check it in the kernel, besides
`Scc.Cert.Link`:

- the elaborator `scc_x64_cells%`, which runs the canonical loader's parser
  and layout (`Scc.Sem.X64.cellsOf`: Kraken's x64 parser on the `.text`
  sections, laid out at the text's size table) on a text at elaboration
  time and returns the code cells as a literal; with `scc_data_secs%`
  (`Scc/Cert/LinkImage.lean`) for the data sections. The kernel cannot
  evaluate the parsers, so the two parse equations are the trust boundary
  (`parsesTo`), checked by `#guard` in a generated file;
- `linkOf cells secs`: the static link at `Link.canonical`, its `.quad`
  labels the code labels of the cells;
- `abortsIn cells Λ`: each abort label of `Λ` is a code label;
- `imageIn cells secs Λ`: the image holds each data symbol's item
  (`Scc.Cert.Link.imageOk`);
- `loadOk Λ cells secs offs`: the canonical loader's checks of `Λ` against
  the parsed text (`Scc.Sem.X64.target`'s `load` but the entry state's
  `Entry.clear`), the size table's (`SizeCheck`) by a linear walk
  (`sizeOkC`, `sizeCheck_of_sizeOkC`: `SizeCheck` itself is quadratic in
  the kernel) with the label offsets in the code's order (`sizeOkL`,
  `sizeOkC_of_sizeOkL`: no string lookups), and the data symbols placeable (`symsOk`), so that the
  loaded thread's cells are a valid layout (`validLayout_of_loadOk`); with
  the entry state's check, the canonical load of the parsed text is the
  loaded configuration (`loadParsed_of_loadOk`), and with the parse
  equations the canonical target's load of the text is (`load_of_loadOk`);
- `lays_threadAt`, `endPc_threadAt`: the loaded thread lays out the code
  cells first and halts at their end (`Scc.Cert.Rt.X64.Lays`, `endOf`), the
  hypotheses of `codeAt_of_blocksIn`, `code_field` and every Code check
  built on them.
-/

namespace Scc.Cert.Link.X64

open Scc.Sem Scc.Sem.X64 Kraken.Promising Kraken.Promising.X64

open Lean Elab Term Meta in
/-- `scc_x64_cells% a`, `a` a constant of type `Scc.Sem.X64.Asm`: the code
cells the canonical loader lays out from its value (`cellsOf`), at
elaboration time, as a literal. -/
elab "scc_x64_cells% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let a ← unsafe evalConst Asm n
  match textProgram a.text with
  | .error msg => throwError "Kraken's x64 parser rejects the text: {msg}"
  | .ok _ =>
    match cellsOf a with
    | some cs => return toExpr cs
    | none => throwError "the size table does not fit the text's instructions"

/-- **The loader's parse of `a`** is the code cells `cells` and the data
sections `secs` (`cellsOf`, `dataSections`): the trust boundary of a
generated file, checked there by evaluation (`#guard`). -/
def parsesTo (a : Asm) (cells : List (Directive × Nat)) (secs : DataSecs) : Bool :=
  decide (cellsOf a = some cells) && decide (dataSections a.text = some secs)

/-- The parse equations from `parsesTo`. -/
theorem parsed_of_parsesTo {a : Asm} {cells : List (Directive × Nat)} {secs : DataSecs}
    (h : parsesTo a cells secs = true) : cellsOf a = some cells ∧ dataSections a.text = some secs := by
  simpa only [parsesTo, Bool.and_eq_true, decide_eq_true_eq] using h

/-- **The static link of laid-out code cells** at `Link.canonical`. -/
def linkOf (cells : List (Directive × Nat)) (secs : DataSecs) : Scc.Sem.Layout :=
  link canonical secs (codeLabel canonical.codeLo cells)

/-- Each abort label of `Λ` is a code label of `cells`. -/
def abortsIn (cells : List (Directive × Nat)) (Λ : Scc.Sem.Layout) : Bool :=
  kinds.all fun k => (codeLabel Λ.code.lo cells (Λ.abortLbl k)).isSome

/-- The image of `Λ` holds each data symbol's item (`imageOk`), `.quad`
labels resolved in `cells`. -/
def imageIn (cells : List (Directive × Nat)) (secs : DataSecs) (Λ : Scc.Sem.Layout) : Bool :=
  imageOk Λ secs (codeLabel Λ.code.lo cells)

/-! ## The size table, linearly -/

/-- One pass over code cells from offset `acc`: every cell's `cellSizeOk`
at its end address from `base`; the result is the labels with their
offsets, in order, and the end offset. -/
def cellsWalk (base : Int64) : List (Directive × Nat) → Nat → Option (List (String × Nat) × Nat)
  | [], acc => some ([], acc)
  | (.label l, z) :: cs, acc =>
    if z == 0 then (cellsWalk base cs acc).map fun r => ((l, acc) :: r.1, r.2) else none
  | c :: cs, acc =>
    if cellSizeOk (base + .ofNat (acc + c.2)) c then cellsWalk base cs (acc + c.2) else none

/-- **The linear size check** of laid-out cells: `cellsWalk` from offset 0
succeeds, ends below `2 ^ 64`, and every listed label's first offset is its
listed one. -/
def sizeOkC (base : Int64) (cells : List (Directive × Nat)) (offs : List (String × Nat)) : Bool :=
  match cellsWalk base cells 0 with
  | some (ls, n) => decide (n < 2 ^ 64) && offs.all fun (L, off) => ls.lookup L == some off
  | none => false

private def psum (cs : List (Directive × Nat)) (k : Nat) : Nat := ((cs.take k).map (·.2)).sum

private theorem cellsWalk_spec (base : Int64) : ∀ (cells : List (Directive × Nat)) (acc : Nat)
    (ls : List (String × Nat)) (n : Nat), cellsWalk base cells acc = some (ls, n) →
    n = acc + (cells.map (·.2)).sum ∧
      (∀ i c, cells[i]? = some c → cellSizeOk (base + .ofNat (acc + psum cells (i + 1))) c = true) ∧
      ∀ L, ls.lookup L = (labelIdx L cells).map fun k => acc + psum cells k
  | [], acc, ls, n, h => by
    simp only [cellsWalk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, by simp, by simp [labelIdx]⟩
  | (.label l, z) :: cs, acc, ls, n, h => by
    simp only [cellsWalk] at h
    split at h
    · rename_i hz
      simp only [beq_iff_eq] at hz
      subst hz
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨ls', n'⟩, h', he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hn, hok, hl⟩ := cellsWalk_spec base cs acc ls' n' h'
      refine ⟨by simp [hn], ?_, ?_⟩
      · intro i c hi
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi; simp [cellSizeOk]
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          have := hok i c hi
          simpa [psum, List.take_succ_cons] using this
      · intro L
        by_cases hL : l = L
        · subst hL; simp [List.lookup, labelIdx, psum]
        · have hL' : (L == l) = false := by simpa [beq_iff_eq] using Ne.symm hL
          have hd : ¬ (Directive.label l = Directive.label L) := by simpa using hL
          simp only [List.lookup, hL', labelIdx, hd, ↓reduceIte, hl, Option.map_map]
          congr 1; funext k; simp [psum, List.take_succ_cons]
    · simp at h
  | (.instr ins, z) :: cs, acc, ls, n, h => by
    simp only [cellsWalk] at h
    split at h
    · rename_i hz
      obtain ⟨hn, hok, hl⟩ := cellsWalk_spec base cs (acc + z) ls n h
      refine ⟨by simp [hn]; omega, ?_, ?_⟩
      · intro i c hi
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi; simpa [psum] using hz
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          have := hok i c hi
          simpa [psum, List.take_succ_cons, Nat.add_assoc] using this
      · intro L
        simp only [hl, labelIdx, reduceCtorEq, ↓reduceIte, Option.map_map]
        congr 1; funext k; simp [psum, List.take_succ_cons, Nat.add_assoc]
    · simp at h
  | (.byteArray b, z) :: cs, acc, ls, n, h => by
    simp only [cellsWalk] at h
    split at h
    · rename_i hz
      obtain ⟨hn, hok, hl⟩ := cellsWalk_spec base cs (acc + z) ls n h
      refine ⟨by simp [hn]; omega, ?_, ?_⟩
      · intro i c hi
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi; simpa [psum] using hz
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          have := hok i c hi
          simpa [psum, List.take_succ_cons, Nat.add_assoc] using this
      · intro L
        simp only [hl, labelIdx, reduceCtorEq, ↓reduceIte, Option.map_map]
        congr 1; funext k; simp [psum, List.take_succ_cons, Nat.add_assoc]
    · simp at h

/-- `sizeOkC` is sound for `SizeCheck`. -/
theorem sizeCheck_of_sizeOkC {base : Int64} {cells : List (Directive × Nat)} {offs : List (String × Nat)}
    (h : sizeOkC base cells offs = true) : SizeCheck base cells offs = true := by
  unfold sizeOkC at h
  split at h
  · rename_i ls n hw
    obtain ⟨hn, hok, hl⟩ := cellsWalk_spec base cells 0 ls n hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨hlt, hoffs⟩ := h
    simp only [SizeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · intro i _
      split
      · rename_i c hci
        simpa [Kraken.Executable.addrOf, Kraken.Executable.sizeBefore, psum] using hok i c hci
      · rfl
    · intro ⟨L, off⟩ hm
      have := hoffs (L, off) hm
      simp only [hl, beq_iff_eq, Option.map_eq_some_iff] at this
      obtain ⟨k, hk, rfl⟩ := this
      simp [hk, Kraken.Executable.sizeBefore, psum]
  · simp at h

/-! ## The label offsets, linearly

`sizeOkC`'s label part looks every listed label up in the walk's labels:
quadratic string comparisons, which dominate the kernel's memory on a
listing with a few hundred labels. `sizeOkL` checks the same with the listed
offsets in the walk's order: they are a subsequence of the walk's labels
(`subseqB`, linear), and the walk's labels are distinct, compared by a
numeric key (`labelKey`, `keysNodupB`: cheap literal comparisons; a key
collision only fails the check). -/

/-- A numeric key of a label: its UTF-8 bytes in base 256 after a leading 1.
Only used to show labels distinct (`keysNodupB`): distinct keys are distinct
labels whatever the key. -/
def labelKey (L : String) : Nat := L.toByteArray.data.toList.foldl (fun n b => n * 256 + b.toNat) 1

/-- No two numbers of the list are equal. -/
def keysNodupB : List Nat → Bool
  | [] => true
  | a :: l => l.all (· != a) && keysNodupB l

/-- `offs` is a subsequence of `ls` (both in order). -/
def subseqB : List (String × Nat) → List (String × Nat) → Bool
  | _, [] => true
  | [], _ :: _ => false
  | a :: r, b :: bs => if a == b then subseqB r bs else subseqB r (b :: bs)

/-- The walk's part of `sizeOkL`: `cellsWalk` from offset 0 succeeds, ends
below `2 ^ 64`, and the listed offsets are a subsequence of its labels with
their offsets. -/
def sizeOkW (base : Int64) (cells : List (Directive × Nat)) (offs : List (String × Nat)) : Bool :=
  match cellsWalk base cells 0 with
  | some (ls, n) => decide (n < 2 ^ 64) && subseqB ls offs
  | none => false

/-- The labels' part of `sizeOkL`: the labels of `cellsWalk` are distinct
(by their keys). -/
def labelsNodupL (base : Int64) (cells : List (Directive × Nat)) : Bool :=
  match cellsWalk base cells 0 with
  | some (ls, _) => keysNodupB (ls.map fun p => labelKey p.1)
  | none => false

/-- **The linear size check with ordered label offsets**: `cellsWalk` from
offset 0 succeeds, ends below `2 ^ 64`, the listed offsets are a subsequence
of its labels with their offsets (`sizeOkW`), and those labels are distinct
(`labelsNodupL`). Implies `sizeOkC` (`sizeOkC_of_sizeOkL`). -/
def sizeOkL (base : Int64) (cells : List (Directive × Nat)) (offs : List (String × Nat)) : Bool :=
  sizeOkW base cells offs && labelsNodupL base cells

private theorem keysNodupB_pairwise : ∀ {l : List Nat}, keysNodupB l = true → l.Pairwise (· ≠ ·)
  | [], _ => .nil
  | a :: l, h => by
    simp only [keysNodupB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
    exact .cons (fun b hb e => h.1 b hb e.symm) (keysNodupB_pairwise h.2)

private theorem subseqB_sublist : ∀ {ls offs : List (String × Nat)}, subseqB ls offs = true → offs.Sublist ls
  | _, [], _ => List.nil_sublist _
  | [], _ :: _, h => by simp [subseqB] at h
  | a :: r, b :: bs, h => by
    simp only [subseqB] at h
    split at h
    · rename_i e
      have e : a = b := by simpa using e
      subst e
      exact (subseqB_sublist h).cons_cons a
    · exact (subseqB_sublist h).cons a

private theorem lookup_of_mem : ∀ {ls : List (String × Nat)} {L : String} {o : Nat},
    ls.Pairwise (fun p q => p.1 ≠ q.1) → (L, o) ∈ ls → ls.lookup L = some o
  | [], _, _, _, hm => by simp at hm
  | (L', o') :: ls, L, o, hp, hm => by
    rw [List.pairwise_cons] at hp
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · simp [List.lookup]
    · have hne : L ≠ L' := fun e => hp.1 (L, o) hm (by simp [e])
      have : (L == L') = false := by simpa using hne
      simp only [List.lookup, this]
      exact lookup_of_mem hp.2 hm

/-- `sizeOkL` implies `sizeOkC`. -/
theorem sizeOkC_of_sizeOkL {base : Int64} {cells : List (Directive × Nat)} {offs : List (String × Nat)}
    (h : sizeOkL base cells offs = true) : sizeOkC base cells offs = true := by
  unfold sizeOkL sizeOkW labelsNodupL at h
  unfold sizeOkC
  split at h
  · rename_i ls n _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlt, hsub⟩, hnd⟩ := h
    have hp : ls.Pairwise (fun p q => p.1 ≠ q.1) :=
      (List.pairwise_map.mp (keysNodupB_pairwise hnd)).imp fun h e => h (by rw [e])
    simp only [hlt, decide_true, Bool.true_and, List.all_eq_true]
    intro ⟨L, off⟩ hm
    simp [lookup_of_mem hp ((subseqB_sublist hsub).subset hm)]
  · simp at h

/-! ## The canonical loader's thread -/

/-- A cell `placeSyms` may append: an empty label, or non-empty padding. -/
def padOk : Directive × Nat → Bool
  | (.label _, z) => z == 0
  | (.byteArray _, z) => 0 < z
  | _ => false

/-- **Valid cells after a valid layout**: code cells with a valid layout,
then empty labels and non-empty padding, all fitting the address space. -/
theorem validLayout_append {base : Int64} {cells new : List (Directive × Nat)}
    (hv : Kraken.Executable.ValidLayout (base, cells)) (hnew : ∀ c ∈ new, padOk c = true)
    (hw : ((cells ++ new).map (·.2)).sum < 2 ^ 64) :
    Kraken.Executable.ValidLayout (base, cells ++ new) := by
  have hnew' : ∀ {j : Nat} {c : Directive × Nat}, new[j]? = some c → padOk c = true :=
    fun h => hnew _ (List.mem_of_getElem? h)
  refine ⟨fun i l z h => ?_, fun i d z h hd => ?_, hw, fun i aw w n pad z h hn => ?_⟩
  · rcases Nat.lt_or_ge i cells.length with hi | hi
    · rw [List.getElem?_append_left hi] at h
      exact hv.label_size i l z h
    · rw [List.getElem?_append_right hi] at h
      simpa [padOk] using hnew' h
  · rcases Nat.lt_or_ge i cells.length with hi | hi
    · rw [List.getElem?_append_left hi] at h
      exact hv.instr_size i d z h hd
    · rw [List.getElem?_append_right hi] at h
      have := hnew' h
      cases d with
      | label l => exact absurd rfl (hd l)
      | byteArray => simpa [padOk] using this
      | instr => simp [padOk] at this
  · rcases Nat.lt_or_ge i cells.length with hi | hi
    · rw [List.getElem?_append_left hi] at h
      have := hv.align_addr i aw w n pad z h hn
      have he : Kraken.Executable.addrOf (base, cells ++ new) (i + 1) =
          Kraken.Executable.addrOf (base, cells) (i + 1) := by
        simp only [Kraken.Executable.addrOf, Kraken.Executable.sizeBefore,
          List.take_append_of_le_length (show i + 1 ≤ cells.length by omega)]
      rw [he]; exact this
    · rw [List.getElem?_append_right hi] at h
      have := hnew' h
      simp [padOk] at this

/-- The step of `placeSyms`' fold. -/
private def placeStep (acc : List (Directive × Nat) × Nat) (xa : String × Nat) : List (Directive × Nat) × Nat :=
  (acc.1 ++ [((Directive.byteArray (.mk #[]) : Directive), xa.2 - acc.2), (.label xa.1, 0)], max xa.2 acc.2)

/-- `placeSyms`' fold over symbols in strictly increasing address order, all
above the current address `c` and below `B`: it appends padding and labels
(`padOk`) whose sizes take `c` to its new current address, below `B`. -/
private theorem placeStep_fold : ∀ (L : List (String × Nat)) (cells : List (Directive × Nat)) (c B : Nat),
    (∀ p ∈ L, c < p.2 ∧ p.2 < B) → L.Pairwise (fun a b => a.2 < b.2) → c < B →
    ∃ new, (L.foldl placeStep (cells, c)).1 = cells ++ new ∧ (∀ x ∈ new, padOk x = true) ∧
      (new.map (·.2)).sum + c = (L.foldl placeStep (cells, c)).2 ∧ (L.foldl placeStep (cells, c)).2 < B
  | [], cells, c, _, _, _, hc => ⟨[], by simp, by simp, by simp, hc⟩
  | (x, a) :: L, cells, c, B, hL, hp, _ => by
    have ha := hL (x, a) (List.mem_cons_self ..)
    have hp' := List.pairwise_cons.mp hp
    obtain ⟨new, h1, h2, h3, h4⟩ := placeStep_fold L
      (cells ++ [((Directive.byteArray (.mk #[]) : Directive), a - c), (.label x, 0)]) a B
      (fun p hp => ⟨hp'.1 p hp, (hL p (List.mem_cons_of_mem _ hp)).2⟩) hp'.2 ha.2
    have hmax : max a c = a := Nat.max_eq_left (Nat.le_of_lt ha.1)
    refine ⟨[((Directive.byteArray (.mk #[]) : Directive), a - c), (.label x, 0)] ++ new, ?_, ?_, ?_, ?_⟩
    · simp only [List.foldl_cons, placeStep, hmax]; rw [h1, List.append_assoc]
    · intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with (rfl | rfl) | hy
      · simp [padOk]; omega
      · simp [padOk]
      · exact h2 y hy
    · simp only [List.foldl_cons, placeStep, hmax] at h3 ⊢
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
      omega
    · simpa only [List.foldl_cons, placeStep, hmax] using h4

/-- **The data symbols the canonical loader can place**: each above the end
of the code and below `base + 2⁶⁴`, at distinct addresses (no padding cell
is empty and the cells fit, `validLayout_threadAt`). -/
def symsOk (base : Nat) (cells : List (Directive × Nat)) (syms : List (String × Nat)) : Bool :=
  syms.all (fun p => decide (codeEnd base cells < p.2) && decide (p.2 < base + 2 ^ 64)) &&
  decide (syms.map (·.2)).Nodup

/-- The data symbols `symsOk` passes are above the end of the code. -/
theorem codeEnd_lt_of_symsOk {base : Nat} {cells : List (Directive × Nat)} {syms : List (String × Nat)}
    (h : symsOk base cells syms = true) : ∀ p ∈ syms, codeEnd base cells < p.2 := fun p hp => by
  simp only [symsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact (h.1 p hp).1

/-- The data symbols `symsOk` passes are at distinct addresses. -/
theorem nodup_of_symsOk {base : Nat} {cells : List (Directive × Nat)} {syms : List (String × Nat)}
    (h : symsOk base cells syms = true) : (syms.map (·.2)).Nodup := by
  simp only [symsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- The data symbols `symsOk` passes are none below the code (the premise
of `lays_threadAt`, `endPc_threadAt` and
`Rt.X64.label_threadAt_of_codeLabel`). -/
theorem above_of_symsOk {base : Nat} {cells : List (Directive × Nat)} {syms : List (String × Nat)}
    (h : symsOk base cells syms = true) : ∀ p ∈ syms, base ≤ p.2 := fun p hp => by
  have := codeEnd_lt_of_symsOk h p hp
  simp only [codeEnd] at this
  omega

/-- **The canonical loader's thread with no data symbol below the code**:
the executable starts at the code, the code cells first, then the label and
padding cells of the data symbols (`Scc.Sem.X64.threadAt`; no cells before
the code, `PlaceSyms.placeBelow_of_above`). -/
theorem threadAt_exe_of_above {E : Entry} {base : Nat} {cells : List (Directive × Nat)}
    {syms : List (String × Nat)} (h : ∀ p ∈ syms, base ≤ p.2) :
    (threadAt E base cells syms).exe = (Int64.ofNat base,
      cells ++ placeSyms (.byteArray (.mk #[])) .label (codeEnd base cells) syms) := by
  simp only [threadAt, PlaceSyms.exeStart_of_above h, PlaceSyms.placeBelow_of_above _ _ h,
    PlaceSyms.symsFrom_of_above h, List.nil_append]

/-- **The canonical loader's thread is the old-layout one** when every data
symbol lies above the end of the code at distinct addresses (`symsOk`): the
executable at the code, the code cells, then the old `placeSyms`
(`PlaceSyms.placeSymsOld`: a padding cell before each label cell). -/
theorem threadAt_exe_eq_old {E : Entry} {base : Nat} {cells : List (Directive × Nat)}
    {syms : List (String × Nat)} (h : ∀ p ∈ syms, codeEnd base cells < p.2) (hnd : (syms.map (·.2)).Nodup) :
    (threadAt E base cells syms).exe = (Int64.ofNat base,
      cells ++ PlaceSyms.placeSymsOld (.byteArray (.mk #[])) .label (codeEnd base cells) syms) := by
  rw [threadAt_exe_of_above (fun p hp => by have := h p hp; simp only [codeEnd] at this; omega),
    PlaceSyms.placeSyms_eq_old _ _ h hnd]

/-- **The canonical loader's thread has a valid layout** when its size
table checks at its base (`SizeCheck`) and its data symbols pass `symsOk`. -/
theorem validLayout_threadAt {E : Entry} {base : Nat} {cells : List (Directive × Nat)}
    {syms : List (String × Nat)} {offs : List (String × Nat)}
    (hsz : SizeCheck (Int64.ofNat base) cells offs = true) (hsyms : symsOk base cells syms = true) :
    Kraken.Executable.ValidLayout (threadAt E base cells syms).exe := by
  simp only [symsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsyms
  obtain ⟨hab, hnd⟩ := hsyms
  let le : String × Nat → String × Nat → Bool := fun a b => decide (a.2 ≤ b.2)
  have hperm := List.mergeSort_perm syms le
  have hsorted : (syms.mergeSort le).Pairwise (fun a b => le a b) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) syms
  have hnd' : ((syms.mergeSort le).map (·.2)).Nodup := hnd.perm (hperm.map _).symm
  have hlt : (syms.mergeSort le).Pairwise (fun a b => a.2 < b.2) := by
    have := List.Pairwise.and hsorted (List.pairwise_map.mp hnd')
    refine this.imp fun {a b} h => ?_
    simp only [le, decide_eq_true_eq] at h
    omega
  have hin : ∀ p ∈ syms.mergeSort le, codeEnd base cells < p.2 ∧ p.2 < base + 2 ^ 64 := fun p hp => by
    have := hab p (hperm.mem_iff.mp hp)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  have hv := validLayout_of_sizeCheck hsz
  have hcw := hv.no_wrap
  simp only at hcw
  obtain ⟨new, h1, h2, h3, h4⟩ := placeStep_fold (syms.mergeSort le) [] (codeEnd base cells) (base + 2 ^ 64)
    hin hlt (by simp only [codeEnd]; omega)
  have hcells : (threadAt E base cells syms).exe = (Int64.ofNat base, cells ++ new) := by
    rw [threadAt_exe_eq_old (fun p hp => (hin p (hperm.mem_iff.mpr hp)).1) hnd]
    show (Int64.ofNat base, cells ++ PlaceSyms.placeSymsOld _ _ _ _) = _
    rw [PlaceSyms.placeSymsOld]
    exact congrArg (fun t => (Int64.ofNat base, cells ++ t)) h1
  rw [hcells]
  refine validLayout_append hv h2 ?_
  rw [List.map_append, List.sum_append]
  simp only [codeEnd] at h3 h4
  omega

/-- **The canonical loader's thread lays out its code cells first**
(`Scc.Sem.X64.threadAt`), then padding and label cells for the data
symbols. -/
theorem lays_threadAt (E : Entry) (base : Nat) (cells : List (Directive × Nat)) (syms : List (String × Nat))
    (h : ∀ p ∈ syms, base ≤ p.2) : Scc.Cert.Rt.X64.Lays (threadAt E base cells syms).exe cells :=
  ⟨_, by rw [threadAt_exe_of_above h]⟩

/-- **The canonical loader's thread halts at the end of its code cells.** -/
theorem endPc_threadAt (E : Entry) (base : Nat) (cells : List (Directive × Nat)) (syms : List (String × Nat))
    (h : ∀ p ∈ syms, base ≤ p.2) :
    (threadAt E base cells syms).endPc = Scc.Cert.Rt.X64.endOf (threadAt E base cells syms).exe cells := by
  rw [threadAt_exe_of_above h]
  simp only [threadAt, Scc.Cert.Rt.X64.endOf, codeEnd]
  rw [Int64.ofNat_add]

/-- A dormant slot has the loaded thread's executable and end address. -/
theorem dormantAt_exe (E : Entry) (base : Nat) (cells : List (Directive × Nat)) (syms : List (String × Nat)) :
    (dormantAt E base cells syms).exe = (threadAt E base cells syms).exe ∧
      (dormantAt E base cells syms).endPc = (threadAt E base cells syms).endPc := ⟨rfl, rfl⟩

/-! ## The loader's checks -/

/-- The code labels the canonical loader resolves the `.rodata` quads
with: the cells', else `Λ`'s symbols. -/
def quadCode (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) (l : String) : Option Nat :=
  (codeLabel Λ.code.lo cells l).orElse fun _ => Λ.symbols.lookup l

/-! ## The `.quad` labels, linearly

`quadsResolve` looks every `.quad` label up in the `.rodata` items and the
code cells; `quadsOkL` instead checks the labels, in their order, a
subsequence of the code walk's labels (`cellsWalk`, the one `sizeOkL`
takes), which holds for `scc`'s stack maps (in code order). -/

/-- `sub` is a subsequence of `big`. -/
def strSubseqB : List String → List String → Bool
  | _, [] => true
  | [], _ :: _ => false
  | a :: r, b :: bs => if a == b then strSubseqB r bs else strSubseqB r (b :: bs)

/-- **The `.quad` labels of `items` are code labels**, in code order: a
subsequence of the labels of `cellsWalk base cells 0`. Implies
`quadsResolve` (`quadsResolve_of_quadsOkL`). -/
def quadsOkL (base : Int64) (cells : List (Directive × Nat)) (items : List Kraken.DataImage.Item) : Bool :=
  match cellsWalk base cells 0 with
  | some (ls, _) => strSubseqB (ls.map (·.1)) (Kraken.DataImage.quadLabels items)
  | none => false

private theorem strSubseqB_sublist : ∀ {big sub : List String}, strSubseqB big sub = true → sub.Sublist big
  | _, [], _ => List.nil_sublist _
  | [], _ :: _, h => by simp [strSubseqB] at h
  | a :: r, b :: bs, h => by
    simp only [strSubseqB] at h
    split at h
    · rename_i e
      have e : a = b := by simpa using e
      subst e
      exact (strSubseqB_sublist h).cons_cons a
    · exact (strSubseqB_sublist h).cons a

private theorem lookup_isSome_of_mem : ∀ {ls : List (String × Nat)} {L : String},
    L ∈ ls.map (·.1) → (ls.lookup L).isSome
  | [], _, h => by simp at h
  | (L', o') :: ls, L, h => by
    by_cases e : L = L'
    · subst e; simp [List.lookup]
    · have : (L == L') = false := by simpa using e
      simp only [List.lookup, this]
      simp only [List.map_cons, List.mem_cons, e, false_or] at h
      exact lookup_isSome_of_mem h

private theorem codeLabel_isSome : ∀ {cells : List (Directive × Nat)} {L : String} (b : Nat),
    (labelIdx L cells).isSome → (codeLabel b cells L).isSome
  | [], _, _, h => by simp [labelIdx] at h
  | c :: cs, L, b, h => by
    unfold codeLabel labelAddr
    by_cases e : labelName c.1 = some L
    · simp [e]
    · simp only [e, ↓reduceIte]
      have hc : c.1 ≠ .label L := fun h' => e (by simp [h', labelName])
      simp only [labelIdx, hc, ↓reduceIte, Option.isSome_map] at h
      exact codeLabel_isSome _ h

/-- `quadsOkL` implies `quadsResolve` with the code labels of `quadCode`. -/
theorem quadsResolve_of_quadsOkL {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)}
    {items : List Kraken.DataImage.Item} (h : quadsOkL (Int64.ofNat Λ.code.lo) cells items = true) :
    quadsResolve Λ items (quadCode Λ cells) = true := by
  unfold quadsOkL at h
  split at h
  · rename_i ls n hw
    obtain ⟨-, -, hl⟩ := cellsWalk_spec _ cells 0 ls n hw
    simp only [quadsResolve, List.all_eq_true, Bool.or_eq_true]
    intro l hm
    right
    have h1 := lookup_isSome_of_mem ((strSubseqB_sublist h).subset hm)
    rw [hl, Option.isSome_map] at h1
    have h2 := codeLabel_isSome Λ.code.lo h1
    simp only [quadCode]
    cases hc : codeLabel Λ.code.lo cells l with
    | none => simp [hc] at h2
    | some _ => simp
  · simp at h

/-- **The canonical loader's checks** of `Λ` against the parsed text, but
the entry state's (`Scc.Sem.X64.target`): the size table (`sizeOkL`, at the
code's base, with the label offsets `offs` in the code's order), the
`.rodata` image fits, `Λ.symbols` agrees with it, every `.quad` label
resolves (`quadsOkL`: a code label, in code order), every data symbol
is above the code; and the data symbols placeable (`symsOk`), so that the
loaded thread's cells are a valid layout. -/
def loadOk (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) (secs : DataSecs)
    (offs : List (String × Nat)) : Bool :=
  let ro := secs.rodata
  let syms := loadSyms Λ ro
  sizeOkL (Int64.ofNat Λ.code.lo) cells offs && rodataFits Λ ro && symsAgree Λ ro &&
    quadsOkL (Int64.ofNat Λ.code.lo) cells ro && symsAbove Λ.code.lo (codeEnd Λ.code.lo cells) syms &&
    symsOk Λ.code.lo cells syms

/-- `loadOk` from its parts, each decided in its own declaration by a
generated file (the kernel's cache is per declaration, so its memory is the
largest part's). -/
theorem loadOk_of {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)} {secs : DataSecs}
    {offs : List (String × Nat)}
    (hw : sizeOkW (Int64.ofNat Λ.code.lo) cells offs = true)
    (hl : labelsNodupL (Int64.ofNat Λ.code.lo) cells = true)
    (hq : quadsOkL (Int64.ofNat Λ.code.lo) cells secs.rodata = true)
    (hr : (rodataFits Λ secs.rodata && symsAgree Λ secs.rodata &&
      symsAbove Λ.code.lo (codeEnd Λ.code.lo cells) (loadSyms Λ secs.rodata) &&
      symsOk Λ.code.lo cells (loadSyms Λ secs.rodata)) = true) :
    loadOk Λ cells secs offs = true := by
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hr
  simp only [loadOk, sizeOkL, hw, hl, hq, h1, h2, h3, h4, Bool.and_self]

/-- **The loaded thread's layout is valid** when the checks pass. -/
theorem validLayout_of_loadOk {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)} {secs : DataSecs}
    {offs : List (String × Nat)} (h : loadOk Λ cells secs offs = true) (E : Entry) :
    Kraken.Executable.ValidLayout (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)).exe := by
  simp only [loadOk, Bool.and_eq_true] at h
  exact validLayout_threadAt (sizeCheck_of_sizeOkC (sizeOkC_of_sizeOkL h.1.1.1.1.1)) h.2

/-- **No data symbol below the code** when the checks pass (`symsOk`): the
premise of `lays_threadAt`, `endPc_threadAt` and
`Rt.X64.label_threadAt_of_codeLabel`. -/
theorem above_of_loadOk {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)} {secs : DataSecs}
    {offs : List (String × Nat)} (h : loadOk Λ cells secs offs = true) :
    ∀ p ∈ loadSyms Λ secs.rodata, Λ.code.lo ≤ p.2 := by
  simp only [loadOk, Bool.and_eq_true] at h
  exact above_of_symsOk h.2

/-- **The canonical load of the parsed text** when the loader's checks pass
(`loadOk`) and the entry state's (`Entry.clear`): the code cells' thread
with the data symbols `loadSyms` and the image and `.rodata` words as
initial memory. -/
theorem loadParsed_of_loadOk {H : Hooks isa} {E : Entry} {Λ : Scc.Sem.Layout}
    {cells : List (Directive × Nat)} {secs : DataSecs} {offs : List (String × Nat)}
    (h : loadOk Λ cells secs offs = true) (hE : E.clear Λ = true) :
    loadParsed H E Λ cells secs offs = some (loadProg H E Λ cells (loadSyms Λ secs.rodata)
      (imageMem Λ ++ wordsMem (rodataWords Λ secs.rodata (quadCode Λ cells)))) := by
  simp only [loadOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, -⟩ := h
  have h0' := sizeCheck_of_sizeOkC (sizeOkC_of_sizeOkL h0)
  have h3' : quadsResolve Λ secs.rodata
      (fun l => (codeLabel Λ.code.lo cells l).orElse fun _ => Λ.symbols.lookup l) = true :=
    quadsResolve_of_quadsOkL h3
  unfold loadParsed
  simp only [h0', h1, h2, h3', h4, hE, Bool.and_self, ↓reduceIte]
  rfl

/-- **The canonical target's load of the text `a`**, from the loader's
parse of it (`parsesTo`) and the checks (`loadOk` at its label offsets,
`Entry.clear`). -/
theorem load_of_loadOk {H : Hooks isa} {E : Entry} {Λ : Scc.Sem.Layout} {a : Asm}
    {cells : List (Directive × Nat)} {secs : DataSecs}
    (hp : parsesTo a cells secs = true) (h : loadOk Λ cells secs a.labelOffs = true)
    (hE : E.clear Λ = true) :
    (target H E).load a Λ = some (loadProg H E Λ cells (loadSyms Λ secs.rodata)
      (imageMem Λ ++ wordsMem (rodataWords Λ secs.rodata (quadCode Λ cells)))) := by
  obtain ⟨h1, h2⟩ := parsed_of_parsesTo hp
  rw [load_of_parsed H E Λ h1 h2, loadParsed_of_loadOk h hE]

end Scc.Cert.Link.X64
