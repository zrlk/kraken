/-
**Concrete instance of `Lower.MsqXR.msqXR_promising`.**
ISA: x64; machine: the executable Promising machine
(`Reachable Arch.tso`).

The instance is at the explorer's configuration of `Lower/MsqXRProg.lean`
(the one its `#guard_msgs` runs explore): the layout `mxLayout` (text at
`0x100000`, labels 0 bytes, every instruction 1), the start states `threadE`
(pc `main_e`, `rbx = &tail = 0x1008`, `r12`/`r13` the nodes `0x2100`/`0x2200`)
and `threadD` (pc `main_d`, `rbx = &head = 0x1000`, `r14 = &tail`), both with
`r11` the end of the text and `dmem` empty, and the initial memory
`initMemMX` (`head = tail = s = 0x2000`, the links zero).

- `pMX`: the parameters (`trk = false`) and `pMX_locs` (`QLocs`, by `decide`).
- `labMX_main_e`, `labMX_main_d`, `labMX_done`: the label addresses (through
  `Program.label_addrOf_drop` and `MsqXR.labX_done`).
- `threadE_start`, `threadD_start`, `initMemMX_initV`: the start facts.
- `msqXR_noFault`: no cell of `msqXR` faults (`DirsNoFault`, as the x64 register-link pilot's
  `pilotXR_noFault`; the x64 MS queue pilot dropped it to fit its cap).
- `msqXR_concrete`: every final configuration reachable under `Arch.tso`
  from that configuration has the dequeuer's `r12 = 0x2100` and
  `r13 = 0x2200` (FIFO). Its only hypotheses are the reachability `hc` and
  finality `hf`.
-/
import Kraken.Promising.Lower.MsqXRWhole
import Kraken.Promising.SLR.EnvG.ConcreteCommon

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.MsqXR.Concrete

open Kraken.Promising.Lower.MsqXR
open Kraken.Promising.X64.EnvG.MsQueueX

/-- The explorer's parameters: `head` at `0x1000`, `tail` at `0x1008`, the
sentinel at `0x2000`, the nodes at `0x2100`/`0x2200`; untracked swings. -/
def pMX : Params := ⟨0x1000, 0x1008, 0x2000, 0x2100, 0x2200, false⟩

/-- `head`, `tail` and the three links are distinct; the nodes non-null. -/
theorem pMX_locs : QLocs pMX :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

section
attribute [local instance] mxLayout

set_option maxRecDepth 20000

/-- `main_e` is the start of the text. -/
theorem labMX_main_e : labX "main_e" = (0x100000 : Int64) := by
  rw [show labX "main_e" = (mxLayout msqXR).addrOf 0 from
    Program.label_addrOf_drop msqXR_wf.nodup (by decide) (by decide)]
  decide

/-- `main_d` is `26` instructions in (cell `31`). -/
theorem labMX_main_d : labX "main_d" = (0x100000 + 26 : Int64) := by
  rw [show labX "main_d" = (mxLayout msqXR).addrOf 31 from
    Program.label_addrOf_drop msqXR_wf.nodup (by decide) (by decide)]
  decide

/-- `done` is `endMX`, the end of the text. -/
theorem labMX_done : labX "done" = endMX := by
  rw [labX_done]; decide

/-- **The enqueuer's explorer start state satisfies `StartE`.** -/
theorem threadE_start : StartE pMX threadE := by
  refine ⟨rfl, rfl, labMX_main_e.symm, labMX_done.symm, ?_, rfl, rfl, rfl, ?_⟩
  · rw [labMX_done]; rfl
  · intro k; simp [threadE]

/-- **The dequeuer's explorer start state satisfies `StartD`.** -/
theorem threadD_start : StartD pMX threadD := by
  refine ⟨rfl, rfl, labMX_main_d.symm, labMX_done.symm, ?_, rfl, rfl, ?_⟩
  · rw [labMX_done]; rfl
  · intro k; simp [threadD]

/-- **The explorer's initial memory initialises the queue** (`InitV`). -/
theorem initMemMX_initV : InitV (Config.init (I := isa) [threadE, threadD] initMemMX).mem pMX := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [pMX, Params.head, Params.tail, Params.ls, Params.l1, Params.l2, Config.init_mem] <;> decide

end

section Static

variable [layout : _root_.Layout]

set_option hygiene false in
set_option linter.unusedSimpArgs false in
/-- No cell of `msqXR` faults (`dirs_no_fault`'s script, with `msqXR`'s
parts unfolded first). -/
theorem msqXR_noFault : DirsNoFault (layout msqXR) := by
  refine Kraken.Promising.X64.dirsNoFault_layout (p := msqXR) ?_
  intro d hd e z s pc
  simp only [msqXR, fragE, fragD, mainETxt, enqFrag, mainDTxt, deqFrag, mainEBody, retE1Body, retE2Body,
    mainDBody, retD1Body, retD2Body, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals try simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault, _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, Kraken.Promising.EvTree.access_empty, _root_.RelRegOrMem.interp]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault, Kraken.Promising.EvTree.access_empty]))
  all_goals try (refine Kraken.Promising.prop_ite (P := fun x =>
                Kraken.Promising.EvTree.NoFault (Kraken.Promising.X64.toEv {} x)) ?_ ?_ <;>
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault])

end Static

/-- **The two-node Michael–Scott queue lowered to x64 functions (stackless
register-link convention), at the explorer's configuration**: every final
configuration reachable under `Arch.tso` from `threadE`, `threadD` and
`initMemMX` has the dequeuer's `r12 = n1 = 0x2100` and `r13 = n2 = 0x2200`
(FIFO). -/
theorem msqXR_concrete {fuel : Nat} {cfg : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [threadE, threadD] initMemMX) cfg)
    (hf : cfg.final = true) :
    ∃ th1, cfg.threads[1]? = some th1 ∧ th1.st.st.1.regs.get64 .r12 = 0x2100 ∧
      th1.st.st.1.regs.get64 .r13 = 0x2200 :=
  msqXR_promising (layout := mxLayout) (P := pMX) pMX_locs rfl threadE_start threadD_start initMemMX_initV
    hc hf

end Kraken.Promising.Lower.MsqXR.Concrete

#print axioms Kraken.Promising.Lower.MsqXR.Concrete.msqXR_concrete
#print axioms Kraken.Promising.Lower.MsqXR.Concrete.msqXR_noFault
