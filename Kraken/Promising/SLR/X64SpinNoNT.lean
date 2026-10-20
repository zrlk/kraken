/-
The x64 spinlock worker (`spinWorker`, `SLR/X64SpinTrees.lean`) makes no
non-temporal store: `spinWorker_noNTInv`, the
`ISA.NoNTInv Arch.tso` invariant of `NTFreeTso.lean` for the worker, and
`spinWorker_ntFree`, Theorem 1′'s scope `Config.NTFree Arch.tso` for every
configuration reachable from threads started anywhere in the worker.

The invariant `SpinPc` says only where the thread is: running the laid-out
worker, without declarations, at the address of one of its positions
`0..14`. Registers and private memory are arbitrary, so the cell facts here
do not use the `hx`/`hdm` hypotheses of `X64SpinTrees`' `exec_*` theorems:
each cell is unfolded with the private-memory case split left in, and both
branches are checked (a private access makes no event at all; a shared one
is a plain load, a plain store, which `Arch.tso` makes `.rel`, or the
`acqRel` `xchg`).

## Contents

- `SpinPc`: the invariant; `spinPc_addrOf`.
- `cell_ok_1` … `cell_ok_12`: at each instruction, the tree makes no
  non-temporal store and every leaf is again at a position of the worker.
- `exec_end`: at the end of the text (position 14, behind the label `done`)
  the thread has halted (`isa.exec = none`).
- `spinWorker_noNTInv`, `spinWorker_ntFree`.
-/
import Kraken.Promising.SLR.X64SpinTrees
import Kraken.Promising.SeqLinkX64Prog
import Kraken.Promising.NTFreeTso
import Kraken.Promising.CertifyX64

namespace Kraken.Promising.SLR.X64SpinTrees

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.X64.Parser

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-- The address of a position `0..14` of the laid-out worker. -/
def PcOk (pc : Int64) : Prop := ∃ i, i ≤ 14 ∧ pc = (layout spinWorker).addrOf i

/-- The thread runs the laid-out worker, without declarations, at the
address of a position `0..14` (registers and private memory arbitrary). -/
def SpinPc (st : State) : Prop :=
  st.exe = layout spinWorker ∧ st.decls = {} ∧ PcOk st.st.2

omit hv in
@[simp] theorem pcOk_addrOf {i : Nat} (hi : i ≤ 14) : PcOk ((layout spinWorker).addrOf i) :=
  ⟨i, hi, rfl⟩

/-- Read the cell at position `i` with the private-memory case splits left
in, and check that it makes no non-temporal store and stays in the worker. -/
local macro "cellok" h:ident i:num : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := spinWorker) (i := $i)
    (d := spinWorker[$i]) (by decide) (by decide)
  have hnext := (addrOf_step (i := $i) (by decide)).symm
  rw [← ($h).pc] at hnext
  have he := ($h).exe
  have hds := ($h).decls
  rw [← ($h).pc] at hc
  generalize hd : spinWorker[$i] = d at hc
  simp only [spinWorker, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  intro tree ht
  rw [exec_eq_of_codeAt he hds ($h).ne hc] at ht
  cases ht
  simp only [Directive.interp, Instr.interp, Operation.interp, label_worker, label_done]
  simp [toEv, EvTree.map, EvTree.access_empty, Operand.interp, RegOrMem.interp, MachineData.set,
    MachineData.load, MachineData.store, MachineData.rmwK, RegOrMem.rmw, AddrExpr.interp,
    MachineData.setReg, RelRegOrMem.interp, ConstExpr.interp, BitVec.toAddressSize, label_worker,
    label_done, hnext]
  all_goals (repeat' split) <;>
    simp [toEv, EvTree.map, EvTree.NoNT, EvTree.All, EvTree.access_empty, Arch.storeKind, Arch.tso,
      Arch.rmwKind, SpinPc, he, hds, hnext, label_worker, label_done]
  all_goals first | decide | (constructor <;> decide)
  ))

/-- A cell of the worker: no non-temporal store, every leaf in the worker. -/
abbrev CellOk (st : State) : Prop :=
  ∀ tree, isa.exec st = some tree → tree.NoNT Arch.tso ∧ tree.All SpinPc

theorem cell_ok_1 (st : State) (h : At st 1) : CellOk st := by cellok h 1
theorem cell_ok_2 (st : State) (h : At st 2) : CellOk st := by cellok h 2
theorem cell_ok_3 (st : State) (h : At st 3) : CellOk st := by cellok h 3
theorem cell_ok_4 (st : State) (h : At st 4) : CellOk st := by cellok h 4
theorem cell_ok_5 (st : State) (h : At st 5) : CellOk st := by cellok h 5
theorem cell_ok_6 (st : State) (h : At st 6) : CellOk st := by cellok h 6
theorem cell_ok_7 (st : State) (h : At st 7) : CellOk st := by cellok h 7
theorem cell_ok_8 (st : State) (h : At st 8) : CellOk st := by cellok h 8
theorem cell_ok_9 (st : State) (h : At st 9) : CellOk st := by cellok h 9
theorem cell_ok_10 (st : State) (h : At st 10) : CellOk st := by cellok h 10
theorem cell_ok_11 (st : State) (h : At st 11) : CellOk st := by cellok h 11
theorem cell_ok_12 (st : State) (h : At st 12) : CellOk st := by cellok h 12

omit layout hv in
private theorem dropWhile_nil_of_all {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true) → l.dropWhile p = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.dropWhile_cons_of_pos (h a List.mem_cons_self)]
    exact dropWhile_nil_of_all p l (fun x hx => h x (List.mem_cons_of_mem a hx))

/-- At the end of the text (behind the label `done`) the thread has halted. -/
theorem exec_end (st : State) (he : st.exe = layout spinWorker)
    (hpc : st.st.2 = (layout spinWorker).addrOf 14) : isa.exec st = none := by
  have hls := directivesFromAddress_end_labels (p := spinWorker) 1
    (dlast := spinWorker[12]) (by decide) (by decide) (by decide)
  have hdir : st.directive = none := by
    unfold State.directive
    rw [he, hpc]
    rw [show (14 : Nat) = spinWorker.length from rfl]
    rw [dropWhile_nil_of_all _ _ ?_]
    · rfl
    · intro c hc
      obtain ⟨hl, -⟩ := hls c hc
      obtain ⟨d, z⟩ := c
      cases d <;> simp_all [Directive.isLabel]
  simp [isa, exec, hdir]

/-- **The worker makes no non-temporal store**: `SpinPc` is an
`ISA.NoNTInv Arch.tso` invariant. -/
theorem spinWorker_noNTInv : isa.NoNTInv Arch.tso SpinPc := by
  suffices h : ∀ s, SpinPc s → CellOk s from
    ⟨fun s hs tree ht => (h s hs tree ht).1, fun s hs tree ht => (h s hs tree ht).2⟩
  rintro s ⟨he, hd, i, hi, hpc⟩ tree ht
  cases hne : (s.st.2 == s.endPc)
  · have hAt : ∀ j, s.st.2 = (layout spinWorker).addrOf j → At s j := fun j h => ⟨he, hd, h, hne⟩
    have h0 : (layout spinWorker).addrOf 0 = (layout spinWorker).addrOf 1 :=
      (addrOf_label (i := 0) (l := "worker") rfl).symm
    have h13 : (layout spinWorker).addrOf 13 = (layout spinWorker).addrOf 14 :=
      (addrOf_label (i := 13) (l := "done") rfl).symm
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_ok_1 s (hAt 1 (hpc.trans h0)) tree ht
    · exact cell_ok_1 s (hAt 1 hpc) tree ht
    · exact cell_ok_2 s (hAt 2 hpc) tree ht
    · exact cell_ok_3 s (hAt 3 hpc) tree ht
    · exact cell_ok_4 s (hAt 4 hpc) tree ht
    · exact cell_ok_5 s (hAt 5 hpc) tree ht
    · exact cell_ok_6 s (hAt 6 hpc) tree ht
    · exact cell_ok_7 s (hAt 7 hpc) tree ht
    · exact cell_ok_8 s (hAt 8 hpc) tree ht
    · exact cell_ok_9 s (hAt 9 hpc) tree ht
    · exact cell_ok_10 s (hAt 10 hpc) tree ht
    · exact cell_ok_11 s (hAt 11 hpc) tree ht
    · exact cell_ok_12 s (hAt 12 hpc) tree ht
    · rw [exec_end s he (hpc.trans h13)] at ht; cases ht
    · rw [exec_end s he hpc] at ht; cases ht
  · simp [isa, exec, hne] at ht

/-- **Theorem 1′'s scope for the x64 spinlock**: under `Arch.tso`, every
configuration reachable from threads that all start in the worker (`SpinPc`,
e.g. at `worker`) satisfies `Config.NTFree`. -/
theorem spinWorker_ntFree {fuel : Nat} {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, SpinPc s) {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init states initMem) c) : c.NTFree Arch.tso :=
  Config.ntFree_of_noNTInv spinWorker_noNTInv hs hc

end Kraken.Promising.SLR.X64SpinTrees
