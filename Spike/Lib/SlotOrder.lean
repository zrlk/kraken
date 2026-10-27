/-
**The order of a function's register slots** (ISA-neutral).

Both emitters give a function's IR registers slots in order of first
occurrence: x64 `Emit.X64.frameOf` takes
`(f.params ++ f.blocks.flatMap (insts.flatMap instRegs ++ termRegs)).eraseDups`,
A64 `Emit.A64.funcRegs` the same with its own per-instruction lists. When
each instruction's list is its definitions followed by its uses, and every
use is a parameter or defined before, the first occurrences are the
parameters and the definitions, in order.

- `Chunk`, `UsesDefined acc cs`: a list of (definitions, uses) chunks whose
  uses are each in `acc`, an earlier chunk's definitions or the chunk's own;
- `eraseDups_chunks`: then the uses do not change the first occurrences;
- `funcChunks D U T f`: a function's chunks, one per instruction (`D i`,
  `U i`) and one per terminator (none, `T t`);
- `slots_eq`: for a per-instruction list `R` with `R i = D i ++ U i`,
  `(f.params ++ f.blocks.flatMap (insts.flatMap R ++ T term)).eraseDups` is
  `(f.params ++ defsOf D f).eraseDups`, and `f.params ++ defsOf D f` itself
  when that has no duplicates.
-/
import Scc.IR.Core

namespace Spike.Lib.SlotOrder

open Scc.IR

/-- A function's chunk: the registers an instruction defines, then those it
uses. -/
abbrev Chunk := List Reg × List Reg

/-- **Every use is defined before**: in `acc`, an earlier chunk's
definitions, or the chunk's own definitions. -/
def UsesDefined : List Reg → List Chunk → Prop
  | _, [] => True
  | acc, c :: cs => (∀ r ∈ c.2, r ∈ acc ∨ r ∈ c.1) ∧ UsesDefined (acc ++ c.1) cs

theorem removeAll_nil_of_sub {l m : List Reg} (h : ∀ r ∈ m, r ∈ l) : m.removeAll l = [] := by
  simp only [List.removeAll, List.filter_eq_nil_iff]
  intro r hr
  simp [h r hr]

/-- Registers already present do not change the first occurrences. -/
theorem eraseDups_sub (a u rest : List Reg) (h : ∀ r ∈ u, r ∈ a) :
    (a ++ u ++ rest).eraseDups = (a ++ rest).eraseDups := by
  rw [List.append_assoc, List.eraseDups_append, List.eraseDups_append]
  congr 2
  simp only [List.removeAll, List.filter_append]
  have := removeAll_nil_of_sub h
  simp only [List.removeAll] at this
  rw [this, List.nil_append]

/-- **The uses do not change the first occurrences** of a chunk list whose
uses are defined before (`UsesDefined`). -/
theorem eraseDups_chunks : ∀ (cs : List Chunk) (acc : List Reg), UsesDefined acc cs →
    (acc ++ cs.flatMap (fun c => c.1 ++ c.2)).eraseDups = (acc ++ cs.flatMap (·.1)).eraseDups
  | [], _, _ => by simp
  | c :: cs, acc, ⟨hc, hcs⟩ => by
    have h1 : acc ++ (c :: cs).flatMap (fun c => c.1 ++ c.2) = (acc ++ c.1) ++ c.2 ++
        cs.flatMap (fun c => c.1 ++ c.2) := by simp [List.append_assoc]
    have h2 : acc ++ (c :: cs).flatMap (·.1) = (acc ++ c.1) ++ cs.flatMap (·.1) := by
      simp [List.append_assoc]
    rw [h1, h2, eraseDups_sub _ _ _ (fun r hr => by
      rcases hc r hr with h | h <;> simp [h])]
    exact eraseDups_chunks cs _ hcs

/-- **A function's chunks**: for each block, one chunk per instruction (its
definitions `D i`, its uses `U i`), then one for the terminator (no
definitions, its uses `T t`). -/
def funcChunks (D U : Inst → List Reg) (T : Term → List Reg) (f : Func) : List Chunk :=
  f.blocks.flatMap fun b => b.insts.map (fun i => (D i, U i)) ++ [([], T b.term)]

/-- **The registers a function defines**, in order. -/
def defsOf (D : Inst → List Reg) (f : Func) : List Reg :=
  f.blocks.flatMap fun b => b.insts.flatMap D

theorem fm_map {α β : Type} (g : β → List Reg) (h : α → β) (k : α → List Reg) (hk : ∀ a, g (h a) = k a) :
    ∀ l : List α, (l.map h).flatMap g = l.flatMap k
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.flatMap_cons, hk, fm_map g h k hk l]

theorem funcChunks_all (D U : Inst → List Reg) (T : Term → List Reg) (R : Inst → List Reg)
    (hR : ∀ i, R i = D i ++ U i) (f : Func) :
    (funcChunks D U T f).flatMap (fun c => c.1 ++ c.2) = f.blocks.flatMap fun b => b.insts.flatMap R ++ T b.term := by
  unfold funcChunks
  generalize f.blocks = bs
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.flatMap_append, ih]
    rw [fm_map _ _ _ (fun i => (hR i).symm)]
    simp

theorem funcChunks_defs (D U : Inst → List Reg) (T : Term → List Reg) (f : Func) :
    (funcChunks D U T f).flatMap (·.1) = defsOf D f := by
  unfold funcChunks defsOf
  generalize f.blocks = bs
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.flatMap_append, ih]
    rw [fm_map _ _ _ (fun _ => rfl)]
    simp

/-- **The slot order**: for a per-instruction register list `R` that lists
an instruction's definitions `D i` before its uses `U i`, if every use is a
parameter or defined before (`UsesDefined f.params (funcChunks D U T f)`),
the first occurrences of the function's registers are those of its
parameters and definitions. -/
theorem slots_eq (D U : Inst → List Reg) (T : Term → List Reg) (R : Inst → List Reg)
    (hR : ∀ i, R i = D i ++ U i) (f : Func) (hu : UsesDefined f.params (funcChunks D U T f)) :
    (f.params ++ f.blocks.flatMap fun b => b.insts.flatMap R ++ T b.term).eraseDups =
      (f.params ++ defsOf D f).eraseDups := by
  rw [← funcChunks_all D U T R hR, ← funcChunks_defs D U T f]
  exact eraseDups_chunks _ _ hu

theorem eraseDups_of_nodup' : ∀ {l : List Reg}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.eraseDups_cons, List.filter_eq_self.mpr, eraseDups_of_nodup' h.2]
    intro b hb
    have : b ≠ a := fun e => h.1 (e ▸ hb)
    simp [this]

/-- **The slot order, without duplicates**: the parameters, then the
definitions in order, when those have no duplicates. -/
theorem slots_eq_nodup (D U : Inst → List Reg) (T : Term → List Reg) (R : Inst → List Reg)
    (hR : ∀ i, R i = D i ++ U i) (f : Func) (hu : UsesDefined f.params (funcChunks D U T f))
    (hn : (f.params ++ defsOf D f).Nodup) :
    (f.params ++ f.blocks.flatMap fun b => b.insts.flatMap R ++ T b.term).eraseDups = f.params ++ defsOf D f := by
  rw [slots_eq D U T R hR f hu, eraseDups_of_nodup' hn]

end Spike.Lib.SlotOrder
