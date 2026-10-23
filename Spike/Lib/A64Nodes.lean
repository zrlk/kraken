/-
**AArch64 instructions outside the block lemma, as nodes of a function**:
label addresses and the system instructions without an event.

The block lemma (`Spike/Lib/A64Flow.lean`) covers register operations,
stack accesses and branches; its abstract step reads no label. scc's
runtime also takes label addresses (`adrp Xd, L; add Xd, Xd, :lo12:L`), and
`_start` and the thread start set the thread pointer (`msr tpidr_el0, Xn`)
and pad with `nop`. Each is a single instruction of its own (`SI`) with no
event: Kraken's rows (`Kraken/Promising/Lower/EventsA64Sys.lean`:
`exec_adrp_label`, `exec_add_lo12`, `exec_nop`, `exec_msr`) give the
registers after it (`SI.regs`, with the program's label addresses), and a
function's node at such an instruction lands at the next node (`si_nd`, the
`seg_nd` of `Spike/Lib/A64Cfg.lean` for one instruction). The destination
of a label address is forgotten in the static offsets (it is not a stack
address); the thread pointer is not a general register, so `msr` keeps them.

A **system call** `svc #0` is a node too (`svc_nd`), through `Out.sys` and
the kernel model `Scc.Sem.A64.abi` (`ms.K`): the call is decoded from the
abstract registers (`svcCall`), and every result the kernel may return
(`Kernel.results`) lands at the next node with `x0` set to it and its
static offset forgotten (`Scc/Sem/SysA64.lean`: `mem_certSuccs_svc`). A
call that does not return (`exit`, `exit_group`) has no result, so its node
needs no successor.
-/
import Spike.Lib.A64Cfg
import Kraken.Promising.Lower.EventsA64Sys
import Kraken.AArch64.Parser
import Scc.Sem.SysA64

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

/-! ## The instructions -/

/-- **A single instruction without an event** outside the block lemma
(general registers, no `sp` or zero register). -/
inductive SI where
  /-- `adrp Xd, L`. -/
  | adrp (d : XReg) (L : Label)
  /-- `add Xd, Xs, :lo12:L`. -/
  | addLo12 (d s : XReg) (L : Label)
  /-- `nop`. -/
  | nop
  /-- `msr tpidr_el0, Xs`. -/
  | msr (s : XReg)

/-- The directive. -/
def SI.toDir : SI → Directive
  | .adrp d L => .instr ⟨.W64, .ADRP (.low (.reg d) .W64) (.label L)⟩
  | .addLo12 d s L => .instr ⟨.W64, .ADD_e (.low (.reg d) .W64) (.low (.reg s) .W64) (.imm ⟨.lo12 (.label L), .S0⟩)⟩
  | .nop => .instr ⟨.W64, .NOP⟩
  | .msr s => .instr ⟨.W64, .MSR .TPIDR_EL0 (.low (.reg s) .W64)⟩

/-- **The registers after it**, with the label addresses `lab`. -/
def SI.regs (lab : Label → Int64) : SI → Reg64s → Reg64s
  | .adrp d L, r => r.setRegOrZr (.low (.reg d) .W64) ((lab L).toBitVec &&& ~~~0xFFF#64)
  | .addLo12 d s L, r =>
    r.setRegOrSp (.low (.reg d) .W64) (r.getRegOrSp (.low (.reg s) .W64) + ((lab L).toBitVec &&& 0xFFF#64))
  | .nop, r => r
  | .msr s, r => { r with TPIDR_EL0 := UInt64.ofBitVec (r.getRegOrZr (.low (.reg s) .W64)) }

/-- The general register it writes. -/
def SI.dst : SI → Option XReg
  | .adrp d _ | .addLo12 d _ _ => some d
  | .nop | .msr _ => none

/-- The static offsets after it: the destination forgotten. -/
def SI.so (si : SI) (o : SO) : SO :=
  match si.dst with
  | some d => o.kill d
  | none => o

theorem SI.regs_get (lab : Label → Int64) (si : SI) (r : Reg64s) {x : XRegOrSp}
    (hx : ∀ d, si.dst = some d → x ≠ .reg d) : (si.regs lab r).getRegOrSp64 x = r.getRegOrSp64 x := by
  cases si with
  | adrp d L =>
    exact Reg64s.getRegOrSp64_setRegOrZr_ne _ _ _ (by
      simp only [zrB, Option.some.injEq]; rintro _ rfl; exact hx d rfl)
  | addLo12 d s L => exact Reg64s.getRegOrSp64_setRegOrSp_ne _ _ _ (hx d rfl)
  | nop => rfl
  | msr s =>
    rcases x with y | _
    · cases y <;> rfl
    · rfl

/-! ## Kraken's step -/

/-- **Kraken's step at an `SI`**: no event, the registers `SI.regs` with the
program's label addresses. -/
theorem exec_si {st : State} {si : SI} (hc : CellAt st si.toDir 4) :
    isaLSE2.exec st = some (.done (after st 4 { st.st.1 with regs := si.regs (labelAddr st) st.st.1.regs })) := by
  cases si with
  | adrp d L => exact exec_adrp_label hc
  | addLo12 d s L => exact exec_add_lo12 hc
  | nop => exact exec_nop hc
  | msr s => exact exec_msr hc

/-! ## The abstract state -/

/-- **The abstract state after it.** -/
def SI.step (lab : Label → Int64) (si : SI) (σ : AS) : AS := { σ with regs := si.regs lab σ.regs }

theorem SI.abs (lab : Label → Int64) (si : SI) {R : Region} {o : SO} {m : MachineData} {σ : AS}
    (hA : Abs R o m σ) : Abs R (si.so o) { m with regs := si.regs lab m.regs } (si.step lab σ) := by
  refine ⟨by simp only [SI.step, hA.regs], hA.status, ?_, hA.slot⟩
  simp only [SI.so, SI.step]
  split
  · rename_i d hd
    exact hA.so.kill d fun r hr => si.regs_get lab _ (by rw [hd]; rintro _ ⟨⟩; exact hr)
  · rename_i hd
    intro r k h
    rw [si.regs_get lab _ (by rw [hd]; simp)]
    exact hA.so r k h

/-! ## A node at it -/

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node's states inside `W`**, none moved by `K`: the obligation `hW`
of a node lemma (`si_ndW`, `svc_ndW`, a given node's segment). A function
lemma over `SegW` names one per node. -/
def NodeW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (n : ND) : Prop :=
  ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s'

/-- **A block node's states inside `W`**, none moved by `K`: the obligation
`hW` of `seg_ndW` for the block `blk` at node `n` (the states before each
instruction, related to the abstract run so far, the memory outside the
region as at the node). -/
def BlkW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (n : ND) (blk : List Directive) : Prop :=
  ∀ (s : State) σ c, s.exe = exe → s.endPc = endPc → s.decls = {} → s.st.2 = n.pc → Abs R n.o s.st.1 σ →
    F s.st.1 → n.J σ c → ∀ k < blk.length, ∀ m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ → DFrame R s.st.1 m →
      W { s with st := (m, n.pc + Int64.ofNat (4 * k)) } c ∧
        ∀ s', ¬ K { s with st := (m, n.pc + Int64.ofNat (4 * k)) } s'

/-- Every node is inside the trivial predicate, with no outside moves. -/
theorem NodeW.triv {n : ND} : NodeW (fun _ _ => True) (fun _ _ => False) exe endPc R F n :=
  fun _ _ _ => ⟨trivial, fun _ h => h⟩

/-- Every block node is inside the trivial predicate, with no outside moves. -/
theorem BlkW.triv {n : ND} {blk : List Directive} : BlkW (fun _ _ => True) (fun _ _ => False) exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨trivial, fun _ h => h⟩

/-- **A node at a single instruction without an event**: from every state
of the invariant, the state after it lands at a node, after a local run of
the source. Its states lie in `W` and no outside move `K` moves them
(`hW`). -/
theorem si_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {si : SI} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [si.toDir])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ σ c, n.J σ c → ∃ c', LocalRun p c c' ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, si.so n.o, si.step (_root_.Executable.labels exe).label σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s si.toDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  have hl : labelAddr s = (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels s.exe).label L = _; rw [he]
  have hex := exec_si hc
  rw [hl] at hex
  obtain ⟨c', hr, hL⟩ := hedge σ c hJ
  refine .silent _ c' hex hr ?_
  have hA' := si.abs (_root_.Executable.labels exe).label hA
  have hD' : F { s.st.1 with regs := si.regs (_root_.Executable.labels exe).label s.st.1.regs } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s 4 { s.st.1 with regs := si.regs (_root_.Executable.labels exe).label s.st.1.regs } =
      { s with st := ({ s.st.1 with regs := si.regs (_root_.Executable.labels exe).label s.st.1.regs },
        n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨x, hx⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨x, hx.at he hn hdc hA' hD'⟩

/-- **A node at a single instruction without an event** (`si_ndW` inside
the trivial predicate, with no outside moves). -/
theorem si_nd {n : ND} {si : SI} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [si.toDir])
    (hedge : ∀ σ c, n.J σ c → ∃ c', LocalRun p c c' ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, si.so n.o, si.step (_root_.Executable.labels exe).label σ⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (si_ndW (W := fun _ _ => True) (K := fun _ _ => False) hF hcode (fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hedge).toSeg

/-- **The system call the kernel model decodes** from the registers `r`
(`x8`, `x0`–`x5`; `Scc.Sem.A64.abi`). -/
def svcCall (r : Reg64s) : Option Scc.Sem.Kernel.Call :=
  Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.a64 r.X8.toNat fun i => ((Scc.Sem.A64.xRegs r).getD i.val 0).toNat

/-- The abstract state after a system call returns `v`: `x0 := v`. -/
def svcStep (v : BitVec 64) (σ : AS) : AS := { σ with regs := { σ.regs with X0 := UInt64.ofNat v.toNat } }

/-- `svc #0`. -/
def svcDir : Directive := .instr ⟨.W64, .SVC 0⟩

/-- **A node at a system call** `svc #0`, under the kernel model
`Scc.Sem.A64.abi`: from every state of the invariant the call decodes, and
for every result the kernel may return, the state after it (`x0` the
result, its offset forgotten) lands at a node after a local run of the
source; the call is one the judgement matches (`hok`, `SysOk`). Only the
thread's control (see `Out.sys`). Its states lie in `W` and no outside
move `K` moves them (`hW`). -/
theorem svc_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} (hK : ms.K = some Scc.Sem.A64.abi)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ σ c, n.J σ c → ∃ call, svcCall σ.regs = some call ∧ ∀ v ∈ Scc.Sem.Kernel.results call,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill .X0, svcStep v σ⟩ c')
    (hok : ∀ s c σ call, At exe endPc R F n s c → n.J σ c → svcCall σ.regs = some call → SysOk p ms s c call) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := id hAt
  have hc : CellAt s svcDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨call, hcall, hres⟩ := hedge σ c hJ
  have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.a64 (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some call := by
    rw [← hcall, svcCall, ← hA.regs]; rfl
  refine .sys _ call hK (Scc.Sem.A64.atSvc_of_cellAt hc) hd (hok s c σ call hAt hJ hcall) fun s' hs' => ?_
  obtain ⟨v, hv, rfl⟩ := (Scc.Sem.A64.mem_certSuccs_svc hc hd).1 hs'
  obtain ⟨c', hr, hL⟩ := hres v hv
  refine ⟨c', hr, ?_⟩
  have hA' : Abs R (n.o.kill .X0) { s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat v.toNat } }
      (svcStep v σ) := by
    refine ⟨by simp only [svcStep, hA.regs], hA.status, ?_, hA.slot⟩
    refine hA.so.kill .X0 fun r hr => ?_
    rcases r with y | _
    · cases y <;> first | rfl | exact absurd rfl hr
    · rfl
  have hD' : F { s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat v.toNat } } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : svcRet s 4 v = { s with st := ({ s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat v.toNat } },
      n.pc + Int64.ofNat 4) } := by
    simp only [svcRet, after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨x, hx⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨x, hx.at he hn hdc hA' hD'⟩

/-- **A node at a system call** (`svc_ndW` inside the trivial predicate,
with no outside moves). -/
theorem svc_nd {n : ND} (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hedge : ∀ σ c, n.J σ c → ∃ call, svcCall σ.regs = some call ∧ ∀ v ∈ Scc.Sem.Kernel.results call,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill .X0, svcStep v σ⟩ c')
    (hok : ∀ s c σ call, At exe endPc R F n s c → n.J σ c → svcCall σ.regs = some call → SysOk p ms s c call) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (svc_ndW (W := fun _ _ => True) (K := fun _ _ => False) hK hF hcode (fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hedge hok).toSeg

end Fn

/-! ## The parser's forms -/

section Parse

open Kraken.AArch64.Parser

/-- `SI.toDir` is what Kraken's parser makes of scc's text. -/
example : parseAArch64("adrp x9, scc_rt_heap
add x9, x9, :lo12:scc_rt_heap
nop
msr tpidr_el0, x0") = [SI.toDir (.adrp .X9 "scc_rt_heap"), SI.toDir (.addLo12 .X9 .X9 "scc_rt_heap"),
    SI.toDir .nop, SI.toDir (.msr .X0)] := by
  decide

/-- `svcDir` is what Kraken's parser makes of `svc #0`. -/
example : parseAArch64("svc #0") = [svcDir] := by
  decide

end Parse

end Spike.Lib.A64.Flow
