/-
**AArch64 dead nodes and the abort exits**: nodes no run reaches, and the
`exit_group` system calls that end the abort stubs.

- **Dead nodes** (`dead_nd`): a node whose invariant no pair satisfies is a
  segment to any exit, whatever its instruction (`Seg`'s invariant is the
  node's fragment, which is empty). scc puts code no run reaches after a
  call that does not return and after `exit_group` (on x64 a `ud2`, on
  AArch64 the halt loop `b .`); that no edge lands there is the obligation
  of the predecessor's node (its `Lands` lands elsewhere), not of the dead
  node.
- **The abort exits** (`exit_nd`): at `scc_rt_abort_*_exit` the stub calls
  `exit_group` (`x8 = 94`, the code in `x0`). Under the kernel model
  `Scc.Sem.A64.abi` the call has no result (`Kernel.results (.exitGroup _) =
  []`), so the node is a segment to any exit, from `Out.sys` with no
  successor, given that the call is one the judgement matches (`SysOk`: at
  an abort site, or `main` returning). `svcCall_exitGroup`: the decoded
  call from the registers.
-/
import Spike.Lib.A64Nodes

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

/-! ## The decoded `exit_group` -/

/-- **`x8 = 94` decodes to `exit_group(x0)`.** -/
theorem svcCall_exitGroup {r : Reg64s} (h : r.X8.toNat = 94) :
    svcCall r = some (.exitGroup r.X0.toNat) := by
  simp [svcCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, h, Scc.Sem.A64.xRegs]

/-- `exit_group` resumes in no state. -/
theorem certSuccs_exitGroup {I : ISA} (K : Scc.Sem.Kernel.Abi I) (s : I.State) (v : Nat) :
    Scc.Sem.Kernel.certSuccs K s (.exitGroup v) = [] := rfl

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-! ## Dead nodes -/

/-- **A dead node**: a node whose invariant holds of no abstract state and
control is a segment to any exit. -/
theorem dead_nd {n : ND} {Q : Frag isaLSE2} (hJ : ∀ σ c, ¬ n.J σ c) : Seg p lbl ms (At exe endPc R F n) Q :=
  ⟨At exe endPc R F n, fun _ _ h => h, fun _ _ ⟨_, _, _, _, σ, _, _, h⟩ => absurd h (hJ σ _)⟩

/-- **A dead node inside any `W`**, with any outside moves: it has no
state. -/
theorem dead_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {Q : Frag isaLSE2}
    (hJ : ∀ σ c, ¬ n.J σ c) : SegW W K p lbl ms (At exe endPc R F n) Q :=
  SegW.step (fun _ _ ⟨_, _, _, _, σ, _, _, h⟩ => absurd h (hJ σ _))
    fun _ _ ⟨_, _, _, _, σ, _, _, h⟩ => absurd h (hJ σ _)

/-! ## The abort exits -/

/-- **A node at `exit_group`**: `svc #0` with `x8 = 94` in every state of
the invariant, under the kernel model, the call one the judgement matches
(`hok`: at an abort site, or `main` returning `x0`), is a segment to any exit
(the call does not return). Its states lie in `W` and no outside move `K`
moves them (`hW`). `hok` is given the abstract state's registers as the machine's. -/
theorem exit_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {Q : Frag isaLSE2}
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hW : NodeW W K exe endPc R F n)
    (hx : ∀ σ c, n.J σ c → σ.regs.X8.toNat = 94)
    (hok : ∀ s c σ, At exe endPc R F n s c → n.J σ c → s.st.1.regs = σ.regs →
      SysOk p ms s c (.exitGroup σ.regs.X0.toNat)) :
    SegW W K p lbl ms (At exe endPc R F n) Q := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := id hAt
  have hc : CellAt s svcDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.a64 (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.exitGroup σ.regs.X0.toNat) := by
    rw [← svcCall_exitGroup (hx σ c hJ), svcCall, ← hA.regs]; rfl
  refine .sys _ _ hK (Scc.Sem.A64.atSvc_of_cellAt hc) hd (hok s c σ hAt hJ hA.regs) fun s' hs' => ?_
  rw [certSuccs_exitGroup] at hs'
  cases hs'

/-- **A node at `exit_group`** (`exit_ndW` inside the trivial predicate,
with no outside moves). -/
theorem exit_nd {n : ND} {Q : Frag isaLSE2} (hK : ms.K = some Scc.Sem.A64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hx : ∀ σ c, n.J σ c → σ.regs.X8.toNat = 94)
    (hok : ∀ s c σ, At exe endPc R F n s c → n.J σ c → SysOk p ms s c (.exitGroup σ.regs.X0.toNat)) :
    Seg p lbl ms (At exe endPc R F n) Q :=
  (exit_ndW hK hcode NodeW.triv hx fun s c σ hAt hJ _ => hok s c σ hAt hJ).toSeg

end Fn

/-! ## The parser's forms -/

section Parse

open Kraken.AArch64.Parser

/-- `svcDir` is what Kraken's parser makes of the abort exit's `svc #0`. -/
example : parseAArch64("svc #0") = [svcDir] := by
  decide

end Parse

end Spike.Lib.A64.Flow
