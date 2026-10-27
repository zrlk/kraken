/-
**Per-construct segments of `Accepted1`** (x86-64), symbolic in the frame,
the IR registers' slots, the pc, the cell sizes and the source; the twin of
`Spike/Lib/LowerA64/Node1.lean`, in the style of
`Spike/Lib/LowerX64/Node.lean`.

- `sub_seg`: the saturating `-`'s block (operand loads, `subq`, `movl`,
  `cmovb`) lands at the pending-store node (`pendN`: the source has
  subtracted, `x`'s cell valued by `%rax`); the store is `store_seg`'s.
- `br_seg`: the `if`'s compare block (operand loads, `cmpq`, `je T`) lands at
  the label `T` with the source at the `then` branch, or falls through with
  the source at the `else` branch.
- `jmp_seg`: `jmp F` lands at the label `F`, nothing else changed.

Where x86-64 differs from AArch64: the blocks are sized by `zs` (`hz`), the
pc after one is `pc + Int64.ofNat zs.sum`, an IR register's cell is its slot
offset (`rsOf`), no region alignment hypothesis, `16 ≤ R.hi` (the frame
record above `%rbp`).
-/
import Spike.Lib.LowerX64.Node
import Spike.Lib.LowerX64.Construct1
import Spike.Lib.LowerNode1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (Item)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Spike.Lib.LowerNode

set_option linter.unusedSimpArgs false

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {c0 : Ctl} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isa} {K : State → State → Prop}

/-- **The saturating `-`'s edge** (`sub_seg`'s block, at the labels `lab`). -/
theorem sub_edge {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ subSatItems)).length) (lab : String → Int64)
    {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d) :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN p lbl fr fp ra c0 pc (.let_ x (.sub a b) e) s)
      ((dirs (la ++ lb ++ subSatItems)).zip zs)
      (fun _ : Unit => pendN p lbl fr fp ra c0 (pc + Int64.ofNat zs.sum)
        e ((x, .int, [.one (.reg d)]) :: s) off) (fun e : Empty => e.elim) := by
  have hne : (dirs (la ++ lb ++ subSatItems)).zip zs ≠ [] := by
    obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb
    rw [dirs_append, dirs_append, hda, hdb, dirs_subSat] at hz ⊢
    match zs, hz with
    | [_, _, _, _, _], _ => simp
  have hok : okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs (la ++ lb ++ subSatItems)).zip zs) = true := by
    obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb
    have hz' := hz
    rw [dirs_append, dirs_append, hda, hdb, dirs_subSat] at hz'
    match zs, hz' with
    | [z0, z1, z2, z3, z4], _ =>
    have hsplit : (dirs (la ++ lb ++ subSatItems)).zip [z0, z1, z2, z3, z4] =
        (dirs la).zip [z0] ++ ((dirs lb).zip [z1] ++ (dirs subSatItems).zip [z2, z3, z4]) := by
      rw [dirs_append, dirs_append, hda, hdb, dirs_subSat]; rfl
    rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hda]),
      okBlk_getOp hf h1 (by decide) (by decide) hb (by simp [hdb])]
    exact okBlk_subSat (by simp [oB, SO.kill, rm]) (by simp [oB, SO.kill, rm])
  refine ⟨hne, hok, fun σ c ⟨hJ, hfj, hc0⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, oB fr, σ⟩) c'
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, h9, hsl⟩ :=
    sub_block hf h1 ha hb lab pc σ hz
  refine ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_, ?_, hc0⟩⟩
  · show pc + _ = _
    rw [hpc]
  · show SO.le (oB fr) _ = true
    rw [hso]; exact so_le_oB fr
  · show NJ p lbl (rsOf fr) e _ (upd _ off _) c
    rw [hsl]
    refine hJ.sub_ok hsa hsb hva hvb hd ?_ h9
    intro q hq pl hpl o ho r k' hor hr' hk
    subst hk
    exact hfr q hq pl hpl o ho r hor (rsOf_inj hf hr' hd)
  · show FrJ fp ra _
    rw [hsl]; exact hfj

/-- **The saturating `-`'s block is one segment**: from the node at
`let x = a - b` (operands placed at `pa`, `pb`, loaded into `%rax`, `%rcx`)
to the pending store after the block. `x`'s IR register `d` has a cell no
other placed operand has. -/
theorem sub_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ subSatItems)).length)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s pc ((dirs (la ++ lb ++ subSatItems)).zip zs))
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d)
    (hW : BlkW W K exe endPc R F (bodyN p lbl fr fp ra c0 pc (.let_ x (.sub a b) e) s)
      ((dirs (la ++ lb ++ subSatItems)).zip zs)) :
    SegW W K p lbl ms (At exe endPc R F (bodyN p lbl fr fp ra c0 pc (.let_ x (.sub a b) e) s))
      (At exe endPc R F (pendN p lbl fr fp ra c0 (pc + Int64.ofNat zs.sum)
          e ((x, .int, [.one (.reg d)]) :: s) off)) :=
  SegW.of_next1 ((sub_edge hf h1 ha hb hd hz _ hsa hsb hfr).seg hF hR hlo hhi hcode hW)

/-- **An `if`'s compare-and-branch's edge** (`br_seg`'s block, at the labels
`lab`): the internal nodes indexed by the comparison's outcome. -/
theorem br_edge {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    (T : String) {pc : Int64} {zs : List Nat} (hz : zs.length = (brDirs la lb T).length) (lab : String → Int64)
    {fp ra : BitVec 64} {a b : At} {yes no : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb])) :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN p lbl fr fp ra c0 pc (.ifeq a b yes no) s) ((brDirs la lb T).zip zs)
      (fun bb : Bool =>
        if bb then bodyN p lbl fr fp ra c0 (lab T) yes s
        else bodyN p lbl fr fp ra c0 (pc + Int64.ofNat zs.sum) no s)
      (fun e : Empty => e.elim) := by
  have hne : (brDirs la lb T).zip zs ≠ [] := by
    obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb
    rw [brDirs, dirs_append, dirs_append, hda, hdb, dirs_cmpJe] at hz ⊢
    match zs, hz with
    | [_, _, _, _], _ => simp
  have hok : okBlk (-(fr.size : Int)) 16 (oB fr) ((brDirs la lb T).zip zs) = true := by
    obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb
    have hz' := hz
    rw [brDirs, dirs_append, dirs_append, hda, hdb, dirs_cmpJe] at hz'
    match zs, hz' with
    | [z0, z1, z2, z3], _ =>
    have hsplit : (brDirs la lb T).zip [z0, z1, z2, z3] =
        (dirs la).zip [z0] ++ ((dirs lb).zip [z1] ++ (dirs (cmpJe T)).zip [z2, z3]) := by
      rw [brDirs, dirs_append, dirs_append, hda, hdb, dirs_cmpJe]; rfl
    rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hda]),
      okBlk_getOp hf h1 (by decide) (by decide) hb (by simp [hdb])]
    exact okBlk_cmpJe T
  refine ⟨hne, hok, fun σ c ⟨hJ, hfj, hc0⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, oB fr, σ⟩) c'
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, hsl⟩ :=
    br_block hf h1 ha hb T lab pc σ hz
  have hJ' := hJ.ifeq hsa hsb hva hvb
  refine ⟨c, .refl c, .inl ⟨decide (va = vb), ?_⟩⟩
  by_cases h : va = vb
  · have : va.toNat = vb.toNat := by rw [h]
    simp only [h, decide_true, ite_true] at hpc ⊢
    refine ⟨hpc.symm, ?_, ?_⟩
    · rw [hso]; exact so_le_oB fr
    · show NJ _ _ _ _ _ _ c ∧ _ ∧ _
      rw [hsl]
      exact ⟨by simpa [this] using hJ', hfj, hc0⟩
  · have : va.toNat ≠ vb.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [h, decide_false, Bool.false_eq_true, ite_false] at hpc ⊢
    refine ⟨hpc.symm, ?_, ?_⟩
    · rw [hso]; exact so_le_oB fr
    · show NJ _ _ _ _ _ _ c ∧ _ ∧ _
      rw [hsl]
      exact ⟨by simpa [this] using hJ', hfj, hc0⟩

/-- **An `if`'s compare-and-branch is one segment**: from the node at
`if a = b then yes else no` (operands placed at `pa`, `pb`) to the label `T`
with the source at `yes`, or, when the operands differ, to the fall-through
with the source at `no`; the symbolic environment unchanged. -/
theorem br_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    (T : String) {pc : Int64} {zs : List Nat} (hz : zs.length = (brDirs la lb T).length)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc ((brDirs la lb T).zip zs))
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) {fp ra : BitVec 64} {a b : At} {yes no : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hW : BlkW W K exe endPc R F (bodyN p lbl fr fp ra c0 pc (.ifeq a b yes no) s) ((brDirs la lb T).zip zs)) :
    SegW W K p lbl ms (At exe endPc R F (bodyN p lbl fr fp ra c0 pc (.ifeq a b yes no) s))
      (fun st c => At exe endPc R F (bodyN p lbl fr fp ra c0 ((_root_.Executable.labels exe).label T) yes s) st c ∨
        At exe endPc R F (bodyN p lbl fr fp ra c0 (pc + Int64.ofNat zs.sum) no s) st c) := by
  refine ((br_edge hf h1 ha hb T hz _ hsa hsb).seg hF hR hlo hhi hcode hW).mono_post fun st c h => ?_
  rcases h with ⟨bb, h⟩ | ⟨e, _⟩
  · cases bb
    · exact .inr h
    · exact .inl h
  · exact e.elim

/-- **`jmp F`'s edge** (`jmp_seg`'s block, at the labels `lab`). -/
theorem jmp_edge {fr : Scc.Emit.X64.Frame} (Fl : String) {pc : Int64} {z : Nat} (lab : String → Int64)
    {fp ra : BitVec 64} {t : Expr} {s : SEnv} :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN p lbl fr fp ra c0 pc t s) ((jmpDirs Fl).zip [z])
      (fun _ : Unit => bodyN p lbl fr fp ra c0 (lab Fl) t s) (fun e : Empty => e.elim) := by
  refine ⟨by simp [jmpDirs], okBlk_jmp Fl, fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩⟩
  · show _ = (arun _ ((jmpDirs Fl).zip [z]) ⟨pc, oB fr, σ⟩).pc
    rw [arun_jmp]; rfl
  · show SO.le (oB fr) (arun _ ((jmpDirs Fl).zip [z]) ⟨pc, oB fr, σ⟩).so = true
    rw [arun_jmp]; exact so_le_oB fr
  · show (bodyN p lbl fr fp ra c0 _ t s).J (arun _ ((jmpDirs Fl).zip [z]) ⟨pc, oB fr, σ⟩).σ c
    rw [arun_jmp]; exact hJ

/-- **`jmp F` is one segment**: a node at `pc` moves to the label `F`, the
source and the frame unchanged. -/
theorem jmp_seg {fr : Scc.Emit.X64.Frame} (Fl : String) {pc : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc ((jmpDirs Fl).zip [z]))
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) {fp ra : BitVec 64} {t : Expr} {s : SEnv}
    (hW : BlkW W K exe endPc R F (bodyN p lbl fr fp ra c0 pc t s) ((jmpDirs Fl).zip [z])) :
    SegW W K p lbl ms (At exe endPc R F (bodyN p lbl fr fp ra c0 pc t s))
      (At exe endPc R F (bodyN p lbl fr fp ra c0 ((_root_.Executable.labels exe).label Fl) t s)) :=
  SegW.of_next1 ((jmp_edge Fl _).seg hF hR hlo hhi hcode hW)

end Spike.Lib.LowerX64
