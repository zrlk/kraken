/-
**The x86-64 system-call convention under another executable and end**
(for `Spike/Lib/RestTail.lean`'s `MsMap.kAt` and `PubOut`'s system-call
test along `Spike.Lib.X64RestTail.relab`): at a cell both executables hold,
the convention reads the same cell, so its tests, its arguments and its
resumptions commute with `relab`.

- `nextPc_of_cellAt`: the next pc at a cell is past the cell;
- `atSys_relab_cell`, `nextPc_relab_cell`: the system-call test and the next
  pc at a shared cell;
- `ret_relab_cell`, `certSuccs_relab_cell`: the resumptions along `relab`;
- `kAt_relab_cell`: `MsMap.kAt`'s clauses at the convention.
-/
import Spike.Lib.X64RestTail
import Kraken.Promising.SeqLinkX64Step
import Scc.Sem.TargetX64

namespace Spike.Lib.X64AbiRelab

open Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower.X64 (CellAt)
open Scc.Sem Scc.Sem.X64
open Spike.Lib.X64RestTail (relab directive_of_cellAt)

/-- **The next pc at a cell** is past the cell (the labels before it have
no size). -/
theorem nextPc_of_cellAt {s : State} {d : Directive} {sz : Nat} (h : CellAt s d sz) :
    nextPc s = s.st.2 + Int64.ofNat sz := by
  obtain ⟨hv, -, rest, hcode⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt (hv := hv) hcode
  have h0 : ∀ l : List (Directive × Nat), (∀ c ∈ l, c.1.isLabel = true ∧ c.2 = 0) →
      (l.map (·.2)).sum = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [(hl c List.mem_cons_self).2, ih fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')]
  unfold nextPc
  rw [hat, List.map_append, List.sum_append, h0 ls hls]
  simp

/-- **The next pc at a cell both executables hold** is the same. -/
theorem nextPc_relab_cell {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive}
    {sz : Nat} (hE : CellAt s d sz) (hF : CellAt (relab exe endPc s) d sz) :
    nextPc (relab exe endPc s) = nextPc s := by
  rw [nextPc_of_cellAt hE, nextPc_of_cellAt hF]
  rfl

/-- **The system-call test at a cell both executables hold** is the same. -/
theorem atSys_relab_cell {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive}
    {sz : Nat} (hE : CellAt s d sz) (hF : CellAt (relab exe endPc s) d sz) :
    abi.atSys (relab exe endPc s) = abi.atSys s := by
  show atSyscall _ = atSyscall _
  unfold atSyscall
  rw [directive_of_cellAt hE, directive_of_cellAt hF]

/-- **A return from a system call along `relab`**, at a cell both
executables hold. -/
theorem ret_relab_cell {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive}
    {sz : Nat} (hE : CellAt s d sz) (hF : CellAt (relab exe endPc s) d sz) (x : BitVec 64) :
    abi.ret (relab exe endPc s) x = relab exe endPc (abi.ret s x) := by
  show { relab exe endPc s with st := ({ s.st.1 with regs := retRegs64 (relab exe endPc s) x },
    nextPc (relab exe endPc s)) } = relab exe endPc { s with st := _ }
  have hr : retRegs64 (relab exe endPc s) x = retRegs64 s x := by
    unfold retRegs64
    rw [nextPc_relab_cell hE hF]
    rfl
  rw [hr, nextPc_relab_cell hE hF]
  rfl

/-- **The kernel model's resumptions along `relab`**, at a cell both
executables hold. -/
theorem certSuccs_relab_cell {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive}
    {sz : Nat} (hE : CellAt s d sz) (hF : CellAt (relab exe endPc s) d sz) (call : Kernel.Call) :
    Kernel.certSuccs abi (relab exe endPc s) call = (Kernel.certSuccs abi s call).map (relab exe endPc) := by
  cases call with
  | archSetFs a =>
    show [abi.ret (abi.setTp (relab exe endPc s) a) 0] = [relab exe endPc (abi.ret (abi.setTp s a) 0)]
    have hs : abi.setTp (relab exe endPc s) a = relab exe endPc (abi.setTp s a) := rfl
    have hE' : CellAt (abi.setTp s a) d sz := ⟨hE.valid, hE.ne, hE.code⟩
    have hF' : CellAt (relab exe endPc (abi.setTp s a)) d sz := ⟨hF.valid, hF.ne, hF.code⟩
    rw [hs, ret_relab_cell hE' hF']
    rfl
  | _ =>
    have key : ∀ l : List (BitVec 64),
        l.map (abi.ret (relab exe endPc s)) = (l.map (abi.ret s)).map (relab exe endPc) := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
        show abi.ret (relab exe endPc s) x :: _ = relab exe endPc (abi.ret s x) :: _
        rw [ret_relab_cell hE hF x, ih]
        rfl
    exact key _

/-- **`MsMap.kAt`'s clauses at the x86-64 convention** along `relab`, at a
cell both executables hold. -/
theorem kAt_relab_cell {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive}
    {sz : Nat} (hE : CellAt s d sz) (hF : CellAt (relab exe endPc s) d sz) (K : Kernel.Abi isa)
    (hK : some abi = some K) :
    K.atSys (relab exe endPc s) = K.atSys s ∧ K.nr (relab exe endPc s) = K.nr s ∧
      K.arg (relab exe endPc s) = K.arg s ∧ (∀ x, K.ret (relab exe endPc s) x = relab exe endPc (K.ret s x)) ∧
      (∀ call, Kernel.certSuccs K (relab exe endPc s) call = (Kernel.certSuccs K s call).map (relab exe endPc)) := by
  cases hK
  exact ⟨atSys_relab_cell hE hF, rfl, rfl, ret_relab_cell hE hF, certSuccs_relab_cell hE hF⟩

end Spike.Lib.X64AbiRelab

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64AbiRelab.kAt_relab_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64AbiRelab.kAt_relab_cell
