/-
**Blocks at a label prefix** (AArch64 block data): the compiler numbers a
function's local labels per program (`.L<n>_fn.0_entry`), so a function's
proof that names its blocks takes the prefix `.L<n>_fn` as a parameter. A
block that ends in a branch to a local label is then its template (decided
once by `block_spec`, at a placeholder prefix) with the branch's label
replaced: its `okBlk` is the template's (`okBlk_snoc`, the side conditions
do not read labels) and its abstract run is the template's under the
relabelling `rl` (`arun_snoc` with `dstep_bc` / `dstep_b`: the directives
before the branch do not read labels, `foldl_dstep_noTerm`).
-/
import Spike.Lib.A64Flow

namespace Spike.Lib.A64.Flow

open Kraken Kraken.Promising.AArch64

/-- A conditional branch to a label. -/
def bcD (c : CondCode) (L : Label) : Directive := .instr ⟨.W64, .B_cond c (.label L)⟩

/-- A branch to a label. -/
def bD (L : Label) : Directive := .instr ⟨.W64, .B (.label L)⟩

/-- No covered directive of `pre` is a branch. -/
def NoTerm (pre : List Directive) : Bool :=
  pre.all fun d => match classify d with | some a => !a.isTerm | none => true

/-- The labels `lab` with `L0` read as `L1`. -/
def rl (lab : Label → Int64) (L0 L1 : Label) : Label → Int64 := fun L => if L = L0 then lab L1 else lab L

theorem rl_self (lab : Label → Int64) (L0 L1 : Label) : rl lab L0 L1 L0 = lab L1 := by simp [rl]

/-- A run without branches does not read the labels. -/
theorem foldl_dstep_noTerm (lab lab' : Label → Int64) : ∀ (pre : List Directive) (am : AM), NoTerm pre = true →
    pre.foldl (dstep lab) am = pre.foldl (dstep lab') am
  | [], _, _ => rfl
  | d :: ds, am, h => by
    simp only [NoTerm, List.all_cons, Bool.and_eq_true] at h
    have hd : dstep lab am d = dstep lab' am d := by
      unfold dstep
      cases ha : classify d with
      | none => rfl
      | some a =>
        rw [ha] at h; simp only [Bool.not_eq_true'] at h
        simp only [AI.tgt_of_not_term h.1]
    simp only [List.foldl, hd]; exact foldl_dstep_noTerm lab lab' ds _ h.2

theorem arun_snoc {lab lab' : Label → Int64} {pre : List Directive} (hpre : NoTerm pre = true) {t t' : Directive}
    (ht : ∀ am, dstep lab am t = dstep lab' am t') (am : AM) :
    arun lab (pre ++ [t]) am = arun lab' (pre ++ [t']) am := by
  simp only [arun, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_dstep_noTerm lab lab' pre am hpre]; exact ht _

theorem okBlk_snoc {lo hi : Int} {t t' : Directive} (h0 : ∀ o, okBlk lo hi o [t] = okBlk lo hi o [t']) :
    ∀ (pre : List Directive) (o : SO), okBlk lo hi o (pre ++ [t]) = okBlk lo hi o (pre ++ [t'])
  | [], o => h0 o
  | d :: ds, o => by
    simp only [List.cons_append, okBlk]
    cases classify d with
    | none => rfl
    | some a =>
      have he : (ds ++ [t]).isEmpty = (ds ++ [t']).isEmpty := by cases ds <;> rfl
      simp only [he, okBlk_snoc h0 ds]

theorem dstep_bc (lab : Label → Int64) (c : CondCode) (L0 L1 : Label) (am : AM) :
    dstep lab am (bcD c L1) = dstep (rl lab L0 L1) am (bcD c L0) := by
  simp only [dstep, bcD, classify, AI.tgt, AI.so, AI.step, rl_self]

theorem dstep_b (lab : Label → Int64) (L0 L1 : Label) (am : AM) :
    dstep lab am (bD L1) = dstep (rl lab L0 L1) am (bD L0) := by
  simp only [dstep, bD, classify, AI.tgt, AI.so, AI.step, rl_self]

end Spike.Lib.A64.Flow
