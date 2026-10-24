import Scc.Frontend
import Scc.Lower.Program
import Scc.Emit.X64
import Scc.Emit.X64Lowerable
import Kraken.Promising.X64Sized

/-!
# Certificate support for x64

What an x64 certificate (`Scc.Cert.Gen`) uses: `compile`, the pipeline `scc`
runs (frontend, lowering, x64 emitter), for the reproducibility check; and
`reparse`, Kraken's x64 parser on the emitted text, with the elaborator
`scc_x64_reparse%` that runs it at elaboration time and returns the parsed
`Program` as a literal, so that `decide +kernel` can check
`Scc.Emit.X64.ProgramWCLowerable` of it.

**No raw lines.** Every instruction the emitter writes is a Kraken x64
instruction, so `reparse` drops only the assembler directive lines
(`stripDirectives`); every instruction line is part of the parsed program.
-/

namespace Scc.Cert.X64

open Scc

/-- Kraken's x64 parser on emitted text: directive lines dropped first. -/
def reparse (text : String) : Except String _root_.Program :=
  Kraken.X64.Parser.parse (Kraken.X64.Parser.stripDirectives text)

/-- **The size table checks** for a parsed program laid out from `base`:
it has one entry per non-label directive (`sizedCells`) and passes Kraken's
`SizeCheck` (positive sizes, empty labels, aligned `nopalign`s, no wrap,
and every listed label at its listed offset). The statement's loader
(`Scc.Sem.X64.target`) refuses a text whose table fails this at
`Λ.code.lo`. -/
def sizesOk (base : Nat) (prog : _root_.Program) (sizes : List Nat) (offs : List (String × Nat)) : Bool :=
  match Kraken.Promising.X64.sizedCells prog sizes with
  | some cells => Kraken.Promising.X64.SizeCheck (Int64.ofNat base) cells offs
  | none => false

section Fast
open Kraken.Promising.X64

/-- One pass over a program and its size table from offset `acc`, as
`sizedCells` pairs them: every non-label cell's `cellSizeOk` at its end
address from `base`; the result is the labels with their offsets, in text
order, and the end offset. -/
def sizeWalk (base : Int64) : _root_.Program → List Nat → Nat → Option (List (String × Nat) × Nat)
  | [], [], acc => some ([], acc)
  | [], _ :: _, _ => none
  | .label l :: ds, t, acc => (sizeWalk base ds t acc).map fun r => ((l, acc) :: r.1, r.2)
  | _ :: _, [], _ => none
  | d :: ds, z :: t, acc =>
    if cellSizeOk (base + .ofNat (acc + z)) (d, z) then sizeWalk base ds t (acc + z) else none

/-- **The linear size check**: `sizeWalk` from offset 0 succeeds, ends
below `2 ^ 64`, and every listed label's first offset is its listed one.
It implies `sizesOk` (`sizesOk_of_fast`) and is what certificates check by
`decide +kernel`: `SizeCheck` itself is quadratic in the kernel. -/
def sizesOkFast (base : Nat) (prog : _root_.Program) (sizes : List Nat) (offs : List (String × Nat)) : Bool :=
  match sizeWalk (Int64.ofNat base) prog sizes 0 with
  | some (ls, n) => decide (n < 2 ^ 64) && offs.all fun (L, off) => ls.lookup L == some off
  | none => false

private def psum (cs : List (Directive × Nat)) (k : Nat) : Nat := ((cs.take k).map (·.2)).sum

private theorem sizeWalk_spec (base : Int64) : ∀ (prog : _root_.Program) (t : List Nat) (acc : Nat)
    (ls : List (String × Nat)) (n : Nat), sizeWalk base prog t acc = some (ls, n) →
    ∃ cells, sizedCells prog t = some cells ∧ n = acc + (cells.map (·.2)).sum ∧
      (∀ i c, cells[i]? = some c → cellSizeOk (base + .ofNat (acc + psum cells (i + 1))) c = true) ∧
      ∀ L, ls.lookup L = (labelIdx L cells).map fun k => acc + psum cells k
  | [], [], acc, ls, n, h => by
    simp only [sizeWalk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp [sizedCells], by simp, by simp, by simp [labelIdx]⟩
  | [], _ :: _, _, _, _, h => by simp [sizeWalk] at h
  | .label l :: ds, t, acc, ls, n, h => by
    simp only [sizeWalk, Option.map_eq_some_iff] at h
    obtain ⟨⟨ls', n'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨cs, hc, hn, hok, hl⟩ := sizeWalk_spec base ds t acc ls' n' h'
    refine ⟨(.label l, 0) :: cs, by simp [sizedCells, hc], by simp [hn], ?_, ?_⟩
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
  | .instr i :: ds, [], _, _, _, h => by simp [sizeWalk] at h
  | .byteArray b :: ds, [], _, _, _, h => by simp [sizeWalk] at h
  | .instr ins :: ds, z :: t, acc, ls, n, h => by
    simp only [sizeWalk] at h
    split at h
    · rename_i hz
      obtain ⟨cs, hc, hn, hok, hl⟩ := sizeWalk_spec base ds t (acc + z) ls n h
      refine ⟨(.instr ins, z) :: cs, by simp [sizedCells, hc], by simp [hn]; omega, ?_, ?_⟩
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
  | .byteArray b :: ds, z :: t, acc, ls, n, h => by
    simp only [sizeWalk] at h
    split at h
    · rename_i hz
      obtain ⟨cs, hc, hn, hok, hl⟩ := sizeWalk_spec base ds t (acc + z) ls n h
      refine ⟨(.byteArray b, z) :: cs, by simp [sizedCells, hc], by simp [hn]; omega, ?_, ?_⟩
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

/-- `sizesOkFast` is sound for `sizesOk`. -/
theorem sizesOk_of_fast {base : Nat} {prog : _root_.Program} {sizes : List Nat}
    {offs : List (String × Nat)} (h : sizesOkFast base prog sizes offs = true) :
    sizesOk base prog sizes offs = true := by
  unfold sizesOkFast at h
  split at h
  · rename_i ls n hw
    obtain ⟨cs, hc, hn, hok, hl⟩ := sizeWalk_spec _ prog sizes 0 ls n hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨hlt, hoffs⟩ := h
    simp only [sizesOk, hc, SizeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range]
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

/-- A listed label `(L, off)` is at offset `off` in the walk's labels `ls`
(`sizesOkFast`'s label part). -/
def offOk (ls : List (String × Nat)) (lo : String × Nat) : Bool := ls.lookup lo.1 == some lo.2

/-- `offOk` on `offs` from position `a` on, from its piece of `c` labels
there and the rest: a certificate checks each piece in its own kernel run
(`sizesOkFast_of_chunks`). -/
theorem offsAll_drop {ls offs : List (String × Nat)} {a : Nat} (c : Nat)
    (h1 : ((offs.drop a).take c).all (offOk ls) = true) (h2 : (offs.drop (a + c)).all (offOk ls) = true) :
    (offs.drop a).all (offOk ls) = true := by
  rw [← List.take_append_drop c (offs.drop a), List.all_append, h1, List.drop_drop, h2]
  rfl

/-- **`sizesOkFast` in pieces**: the walk gives the labels `ls` and the end
offset `n` (a kernel check on literals), `n` is below `2 ^ 64`, and every
listed label is at its offset in `ls` (`offOk`, in `offsAll_drop`'s pieces). -/
theorem sizesOkFast_of_chunks {base : Nat} {prog : _root_.Program} {sizes : List Nat}
    {offs ls : List (String × Nat)} {n : Nat} (hw : sizeWalk (Int64.ofNat base) prog sizes 0 = some (ls, n))
    (hn : n < 2 ^ 64) (ho : (offs.drop 0).all (offOk ls) = true) :
    sizesOkFast base prog sizes offs = true := by
  unfold sizesOkFast
  rw [hw]
  simp only [List.drop_zero, List.all_eq_true, offOk] at ho
  simp only [hn, decide_true, Bool.true_and, List.all_eq_true]
  intro ⟨L, off⟩ hm
  exact ho _ hm

end Fast

/-- The pipeline of `scc --arch x64` on a source text. -/
def compile (cfg : Config) (src : String) : Except String String := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let ir ← Lower.lowerProgram cfg c
  Emit.X64.emit ir

/-- The reproducibility check: `src` compiles to exactly `asm`. -/
def reproduces (cfg : Config) (src asm : String) : Bool :=
  match compile cfg src with
  | .ok t => t == asm
  | .error _ => false

open Lean Elab Term Meta in
/-- `scc_x64_reparse% c`, `c` a string constant: run `reparse` on its value at
elaboration time and return the parsed `Program` as a literal. -/
elab "scc_x64_reparse% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let text ← unsafe evalConst String n
  match reparse text with
  | .ok p => return toExpr p
  | .error msg => throwError "Kraken's x64 parser rejects the text: {msg}"

end Scc.Cert.X64
