/-
**x64 dead nodes and the abort exits**: nodes no run reaches (the `ud2`
after a call that does not return or after `exit_group`), and the
`exit_group` system calls that end the abort stubs.

- **Dead nodes** (`dead_nd`): a node whose invariant no pair satisfies is a
  segment to any exit, whatever its instruction (`Seg`'s invariant is the
  node's fragment, which is empty). Kraken's `ud2` faults
  (`exec_ud2`, `Kraken/Promising/Lower/EventsX64Sys.lean`), and `Out` has no
  fault row, so a `ud2` is only covered where no run reaches it: that no
  edge lands there is the obligation of the predecessor's node (its `Lands`
  lands elsewhere), not of the dead node.
- **The abort exits** (`exit_nd`): at `scc_rt_abort_*_exit` the stub calls
  `exit_group` (`%rax = 231`, the code in `%rdi`). Under the kernel model
  `Scc.Sem.X64.abi` the call has no result (`Kernel.results (.exitGroup _) =
  []`), so the node is a segment to any exit, from `Out.sys` with no
  successor, given that the call is one the judgement matches (`SysOk`: at
  an abort site, or `main` returning). `syscallCall_exitGroup`: the decoded call from the registers.
-/
import Spike.Lib.X64Nodes

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64

/-! ## The decoded `exit_group` -/

/-- **`%rax = 231` decodes to `exit_group(%rdi)`.** -/
theorem syscallCall_exitGroup {r : Reg64s} (h : r.rax.toNat = 231) :
    syscallCall r = some (.exitGroup r.rdi.toNat) := by
  simp [syscallCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, h]

/-- `exit_group` resumes in no state. -/
theorem certSuccs_exitGroup {I : ISA} (K : Scc.Sem.Kernel.Abi I) (s : I.State) (v : Nat) :
    Scc.Sem.Kernel.certSuccs K s (.exitGroup v) = [] := rfl

/-- `ud2`. -/
def ud2Dir : Directive := op64 .ud2

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-! ## Dead nodes -/

/-- **A dead node**: a node whose invariant holds of no abstract state and
control is a segment to any exit. -/
theorem dead_nd {n : ND} {Q : Frag isa} (hJ : ∀ σ c, ¬ n.J σ c) : Seg p lbl ms (At exe endPc R F n) Q :=
  ⟨At exe endPc R F n, fun _ _ h => h, fun _ _ ⟨_, _, _, _, σ, _, _, h⟩ => absurd h (hJ σ _)⟩

/-- **A dead node inside any `W`**, with any outside moves: it has no
state. -/
theorem dead_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {Q : Frag isa}
    (hJ : ∀ σ c, ¬ n.J σ c) : SegW W K p lbl ms (At exe endPc R F n) Q :=
  SegW.step (fun _ _ ⟨_, _, _, _, σ, _, _, h⟩ => absurd h (hJ σ _)) fun _ _ ⟨_, _, _, _, σ, _, _, h⟩ => absurd h (hJ σ _)

/-! ## The abort exits -/

/-- **A node at `exit_group`**: `syscall` with `%rax = 231` in every state
of the invariant, under the kernel model, the call one the judgement matches
(`hok`: at an abort site, or `main` returning `%rdi`), is a segment to any
exit (the call does not return). Its states lie in `W` and no outside move
`K` moves them (`hW`). -/
theorem exit_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {Q : Frag isa} {z : Nat}
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hW : NodeW W K exe endPc R F n)
    (hx : ∀ σ c, n.J σ c → σ.regs.rax.toNat = 231)
    (hok : ∀ s c σ, At exe endPc R F n s c → n.J σ c → s.st.1.regs = σ.regs →
      SysOk p ms s c (.exitGroup σ.regs.rdi.toNat)) :
    SegW W K p lbl ms (At exe endPc R F n) Q := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := id hAt
  have hc : CellAt s (op64 .syscall) z := (hcode s he hn).cell0 rfl rfl hpc
  have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.x64 (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
      some (.exitGroup σ.regs.rdi.toNat) := by
    rw [← syscallCall_exitGroup (hx σ c hJ), syscallCall, ← hA.regs]; rfl
  refine .sys _ _ hK (Scc.Sem.X64.atSyscall_of_cellAt hc) hd (hok s c σ hAt hJ hA.regs) fun s' hs' => ?_
  rw [certSuccs_exitGroup] at hs'
  cases hs'

/-- **A node at `exit_group`** (`exit_ndW` inside the trivial predicate,
with no outside moves). -/
theorem exit_nd {n : ND} {Q : Frag isa} {z : Nat} (hK : ms.K = some Scc.Sem.X64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hx : ∀ σ c, n.J σ c → σ.regs.rax.toNat = 231)
    (hok : ∀ s c σ, At exe endPc R F n s c → n.J σ c → SysOk p ms s c (.exitGroup σ.regs.rdi.toNat)) :
    Seg p lbl ms (At exe endPc R F n) Q :=
  (exit_ndW hK hcode NodeW.triv hx fun s c σ hAt hJ _ => hok s c σ hAt hJ).toSeg

end Fn

/-! ## The parser's forms -/

section Parse

open Kraken.X64.Parser

/-- `ud2Dir` is what Kraken's parser makes of `ud2`. -/
example : parse("ud2") = [ud2Dir] := by
  decide

end Parse

end Spike.Lib.X64
