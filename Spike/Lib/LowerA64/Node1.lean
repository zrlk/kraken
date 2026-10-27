/-
**Per-construct segments of call-free `Accepted1` bodies** (AArch64), next
to `Spike/Lib/LowerA64/Node.lean`'s checked `+`, store and `ret`.

- `sub_seg`: the saturating `-`'s block (operand loads, `subs`, `csel`) lands
  at the pending-store node (`pendN`: the source has subtracted, `x`'s slot
  valued by `x9`); `store_seg` then stores it.
- `br_seg`: an `if`'s compare-and-branch (operand loads, `cmp`, `b.eq T`)
  lands at the `then` label with the source at the `yes` branch, or falls
  through with the source at the `no` branch.
- `jmp_seg`: `b F` moves a node to `F`.
-/
import Spike.Lib.LowerA64.Node
import Spike.Lib.LowerA64.Construct1
import Spike.Lib.LowerNode1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Spike.Lib.LowerNode

set_option linter.unusedSimpArgs false

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {c0 : Ctl} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isaLSE2} {K : State → State → Prop}

private theorem one_of_next {P : Frag isaLSE2} {n : ND}
    (h : SegW W K p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim))) :
    SegW W K p lbl ms P (At exe endPc R F n) :=
  h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim

/-- **The saturating `-`'s edge** (`sub_seg`'s block, at the labels `lab`). -/
theorem sub_edge {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : cx.getOp .X9 pa = .ok la) (hb : cx.getOp .X10 pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : cx.slotOff d = .ok off) {pc : Int64} (lab : Label → Int64)
    {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d) :
    BlkEdge p lab (-(cx.frame : Int)) 0 (bodyN p lbl cx fp ra c0 pc (.let_ x (.sub a b) e) s)
      (directives (la ++ lb ++ subSat .X9 .X9 .X10))
      (fun _ : Unit => pendN p lbl cx fp ra c0
          (pc + Int64.ofNat (4 * (directives (la ++ lb ++ subSat .X9 .X9 .X10)).length))
          e ((x, .int, [.one (.reg d)]) :: s) (off - cx.frame)) (fun e : Empty => e.elim) := by
  have hne : directives (la ++ lb ++ subSat .X9 .X9 .X10) ≠ [] := by
    simp [directives_append, directives_subSat]
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx) (directives (la ++ lb ++ subSat .X9 .X9 .X10)) = true := by
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_subSat
  refine ⟨hne, hok, fun σ c ⟨hJ, hfj, hc0⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c'
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, h9, hsl⟩ :=
    sub_block hf h1 h16 ha hb lab pc σ
  refine ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_, ?_, hc0⟩⟩
  · show pc + _ = _
    rw [hpc]
  · show SO.le (oF cx) _ = true
    rw [hso]; exact so_le_refl _ rfl
  · show NJ p lbl (rsOf cx) e _ (upd _ (off - cx.frame) _) c
    rw [hsl]
    refine hJ.sub_ok hsa hsb hva hvb (by simp [rsOf, hd]) ?_ ?_
    · intro q hq pl hpl o ho r k' hor hr' hk
      subst hk
      exact hfr q hq pl hpl o ho r hor (rsOf_inj hr' (by simp [rsOf, hd]))
    · exact h9
  · show FrJ fp ra _
    rw [hsl]; exact hfj

/-- **The saturating `-`'s block is one segment**: from the node at
`let x = a - b` (operands placed at `pa`, `pb`, loaded into `x9`, `x10`) to
the pending store after the block. `x`'s IR register `d` has a cell no other
placed operand has. -/
theorem sub_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : cx.getOp .X9 pa = .ok la) (hb : cx.getOp .X10 pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : cx.slotOff d = .ok off) {pc : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s pc (directives (la ++ lb ++ subSat .X9 .X9 .X10)))
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d)
    (hW : BlkW W K exe endPc R F (bodyN p lbl cx fp ra c0 pc (.let_ x (.sub a b) e) s)
      (directives (la ++ lb ++ subSat .X9 .X9 .X10))) :
    SegW W K p lbl ms (At exe endPc R F (bodyN p lbl cx fp ra c0 pc (.let_ x (.sub a b) e) s))
      (At exe endPc R F (pendN p lbl cx fp ra c0
          (pc + Int64.ofNat (4 * (directives (la ++ lb ++ subSat .X9 .X9 .X10)).length))
          e ((x, .int, [.one (.reg d)]) :: s) (off - cx.frame))) :=
  one_of_next ((sub_edge hf h1 h16 ha hb hd _ hsa hsb hfr).seg hF hR hal hlo hhi hcode hW)

/-- **An `if`'s compare-and-branch's edge** (`br_seg`'s block, at the labels
`lab`): the internal nodes indexed by the comparison's outcome. -/
theorem br_edge {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : cx.getOp .X9 pa = .ok la) (hb : cx.getOp .X10 pb = .ok lb)
    (T : Label) {pc : Int64} (lab : Label → Int64) {fp ra : BitVec 64} {a b : At} {yes no : Expr} {s : SEnv}
    {ta tb : Ty} (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb])) :
    BlkEdge p lab (-(cx.frame : Int)) 0 (bodyN p lbl cx fp ra c0 pc (.ifeq a b yes no) s) (brDirs la lb T)
      (fun bb : Bool =>
        if bb then bodyN p lbl cx fp ra c0 (lab T) yes s
        else bodyN p lbl cx fp ra c0 (pc + Int64.ofNat (4 * (brDirs la lb T).length)) no s)
      (fun e : Empty => e.elim) := by
  have hne : brDirs la lb T ≠ [] := by simp [brDirs, directives_append, directives_cmpJcc]
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx) (brDirs la lb T) = true := by
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [brDirs, directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_cmpJcc T
  refine ⟨hne, hok, fun σ c ⟨hJ, hfj, hc0⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c'
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, hsl⟩ :=
    br_block hf h1 h16 ha hb T lab pc σ
  have hJ' := hJ.ifeq hsa hsb hva hvb
  refine ⟨c, .refl c, .inl ⟨decide (va = vb), ?_⟩⟩
  by_cases h : va = vb
  · have : va.toNat = vb.toNat := by rw [h]
    simp only [h, decide_true, ite_true] at hpc ⊢
    refine ⟨hpc.symm, ?_, ?_⟩
    · rw [hso]; exact so_le_refl _ rfl
    · show NJ _ _ _ _ _ _ c ∧ _ ∧ _
      rw [hsl]
      exact ⟨by simpa [this] using hJ', hfj, hc0⟩
  · have : va.toNat ≠ vb.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [h, decide_false, Bool.false_eq_true, ite_false] at hpc ⊢
    refine ⟨hpc.symm, ?_, ?_⟩
    · rw [hso]; exact so_le_refl _ rfl
    · show NJ _ _ _ _ _ _ c ∧ _ ∧ _
      rw [hsl]
      exact ⟨by simpa [this] using hJ', hfj, hc0⟩

/-- **An `if`'s compare-and-branch is one segment**: from the node at
`if a = b then yes else no` (operands placed at `pa`, `pb`) to the label `T`
with the source at `yes`, or, when the operands differ, to the fall-through
with the source at `no`; the symbolic environment unchanged. -/
theorem br_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : cx.getOp .X9 pa = .ok la) (hb : cx.getOp .X10 pb = .ok lb)
    (T : Label) {pc : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc (brDirs la lb T))
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {a b : At} {yes no : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hW : BlkW W K exe endPc R F (bodyN p lbl cx fp ra c0 pc (.ifeq a b yes no) s) (brDirs la lb T)) :
    SegW W K p lbl ms (At exe endPc R F (bodyN p lbl cx fp ra c0 pc (.ifeq a b yes no) s))
      (fun st c => At exe endPc R F (bodyN p lbl cx fp ra c0 ((_root_.Executable.labels exe).label T) yes s) st c ∨
        At exe endPc R F (bodyN p lbl cx fp ra c0 (pc + Int64.ofNat (4 * (brDirs la lb T).length)) no s) st c) := by
  refine ((br_edge hf h1 h16 ha hb T _ hsa hsb).seg hF hR hal hlo hhi hcode hW).mono_post fun st c h => ?_
  rcases h with ⟨bb, h⟩ | ⟨e, _⟩
  · cases bb
    · exact .inr h
    · exact .inl h
  · exact e.elim

/-- **`b F`'s edge** (`jmp_seg`'s block, at the labels `lab`). -/
theorem jmp_edge {cx : FnCtx} (Fl : Label) {pc : Int64} (lab : Label → Int64) {fp ra : BitVec 64} {t : Expr}
    {s : SEnv} :
    BlkEdge p lab (-(cx.frame : Int)) 0 (bodyN p lbl cx fp ra c0 pc t s) (jmpDirs Fl)
      (fun _ : Unit => bodyN p lbl cx fp ra c0 (lab Fl) t s) (fun e : Empty => e.elim) := by
  refine ⟨by simp [jmpDirs, directives, jmp, ins], okBlk_jmp Fl, fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩⟩
  · show _ = (arun _ (jmpDirs Fl) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩).pc
    rw [arun_jmp]; rfl
  · show SO.le (oF cx) (arun _ (jmpDirs Fl) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩).so = true
    rw [arun_jmp]; exact so_le_refl _ rfl
  · show (bodyN p lbl cx fp ra c0 _ t s).J (arun _ (jmpDirs Fl) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩).σ c
    rw [arun_jmp]; exact hJ

/-- **`b F` is one segment**: a node at `pc` moves to the label `F`, the
source and the frame unchanged. -/
theorem jmp_seg {cx : FnCtx} (Fl : Label) {pc : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc (jmpDirs Fl))
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {t : Expr} {s : SEnv}
    (hW : BlkW W K exe endPc R F (bodyN p lbl cx fp ra c0 pc t s) (jmpDirs Fl)) :
    SegW W K p lbl ms (At exe endPc R F (bodyN p lbl cx fp ra c0 pc t s))
      (At exe endPc R F (bodyN p lbl cx fp ra c0 ((_root_.Executable.labels exe).label Fl) t s)) :=
  one_of_next ((jmp_edge Fl _).seg hF hR hal hlo hhi hcode hW)

end Spike.Lib.LowerA64
