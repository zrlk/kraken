/-
**x64 label addresses as nodes of a function**: `leaq L(%rip), %r`.

The block lemma (`Spike/Lib/X64Block.lean`) reads no label in its abstract
step. scc's runtime takes the address of its globals with `leaq
L(%rip), %r` (Kraken's row `exec_lea_rip_label`,
`Kraken/Promising/Lower/EventsX64Sys.lean`: no event, `r` is the label's
address). Each is a single instruction of its own (`SI`), and a function's
node at it lands at the next node (`si_nd`, the `seg_nd` of
`Spike/Lib/X64Cfg.lean` for one instruction). The destination is forgotten
in the static offsets (it is not a stack address).

A **system call** `syscall` is a node too (`syscall_nd`), through `Out.sys`
and the kernel model `Scc.Sem.X64.abi` (`ms.K`): the call is decoded from
the abstract registers (`syscallCall`), and every result the kernel may
return (`Kernel.results`) lands at the next node with `%rax` the result,
`%rcx` the next pc, `%r11` the flags (`syscallStep`), their static offsets
forgotten (`Scc/Sem/SysX64.lean`: `mem_certSuccs_syscall`). A call that
does not return (`exit`, `exit_group`) has no result. `arch_prctl` (which
also sets the thread pointer) is not covered here: it is `archSetFs_nd`
(`Spike/Lib/X64RtNodes.lean`).

A **thread-pointer load** `movq %fs:k, %r` (the stack limit, the thread's
control block) is a node too (`fsld_nd`), through `Out.rtLoad`: it reads
an address the runtime owns (`ms.rt`), outside the thread's private memory,
and every value read lands at the next node with `%r` forgotten (Kraken's
row `exec_movfs_load_agrees`).
-/
import Spike.Lib.X64Cfg
import Kraken.Promising.Lower.EventsX64Sys
import Kraken.X64.Parser
import Scc.Sem.SysX64

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64

/-! ## The instructions -/

/-- **A single instruction without an event** outside the block lemma. -/
inductive SI where
  /-- `leaq L(%rip), %d`. -/
  | leaRip (d : Reg64) (L : Label)

/-- The directive. -/
def SI.toDir : SI → Directive
  | .leaRip d L =>
    op64 (.lea (.low d .W64) { base := some .rip, idx := none, disp := .sub (.label L) .after_current_instruction })

/-- **The registers after it**, with the label addresses `lab`. -/
def SI.regs (lab : Label → Int64) : SI → Reg64s → Reg64s
  | .leaRip d L, r => r.set64 d (lab L).toBitVec

/-- The register it writes. -/
def SI.dst : SI → Reg64
  | .leaRip d _ => d

/-- The side condition: it does not write `%rsp`. -/
def SI.ok (si : SI) : Bool := si.dst != .rsp

/-- The static offsets after it: the destination forgotten. -/
def SI.so (si : SI) (o : SO) : SO := o.kill si.dst

theorem SI.regs_get64 (lab : Label → Int64) (si : SI) (r : Reg64s) {x : Reg64} (hx : si.dst ≠ x) :
    (si.regs lab r).get64 x = r.get64 x := by
  cases si with
  | leaRip d L => exact Reg64s.get64_set64_ne _ (Ne.symm hx) _

/-! ## Kraken's step -/

/-- **Kraken's step at an `SI`**: no event, the registers `SI.regs` with the
program's label addresses. -/
theorem exec_si {st : State} {si : SI} {z : Nat} (hc : CellAt st si.toDir z) :
    isa.exec st = some (.done (after st z { st.st.1 with regs := si.regs (labelAddr st) st.st.1.regs })) := by
  cases si with
  | leaRip d L => exact exec_lea_rip_label hc

/-! ## The abstract state -/

/-- **The abstract state after it.** -/
def SI.step (lab : Label → Int64) (si : SI) (σ : AS) : AS := { σ with regs := si.regs lab σ.regs }

theorem SI.abs (lab : Label → Int64) {si : SI} (hok : si.ok = true) {R : Region} {o : SO} {m : MachineData}
    {σ : AS} (hA : Abs R o m σ) : Abs R (si.so o) { m with regs := si.regs lab m.regs } (si.step lab σ) := by
  refine ⟨by simp only [SI.step, hA.regs], hA.zmms, hA.status, ?_, hA.slot⟩
  have hdr : si.dst ≠ .rsp := by
    intro h; rw [SI.ok, h] at hok; exact absurd hok (by decide)
  refine SORel.write (o := o) (d := si.dst) (by simp [SO.write, hdr, SI.so]) hA.so fun r hr =>
    si.regs_get64 lab _ (Ne.symm hr)

/-! ## A node at it -/

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at a single instruction without an event**: from every state
of the invariant, the state after it lands at a node, after a local run of
the source. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem si_ndW {W : Frag isa} {K : State → State → Prop}
    {n : ND} {si : SI} {z : Nat} (hok : si.ok = true) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(si.toDir, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ σ c, n.J σ c → ∃ c', LocalRun p c c' ∧
      Lands N E ⟨n.pc + Int64.ofNat z, si.so n.o, si.step (_root_.Executable.labels exe).label σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s si.toDir z := (hcode s he hn).cell0 rfl rfl hpc
  have hl : labelAddr s = (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels s.exe).label L = _; rw [he]
  have hex := exec_si hc
  rw [hl] at hex
  obtain ⟨c', hr, hL⟩ := hedge σ c hJ
  refine .silent _ c' hex hr ?_
  have hA' := SI.abs (_root_.Executable.labels exe).label hok hA
  have hD' : F { s.st.1 with regs := si.regs (_root_.Executable.labels exe).label s.st.1.regs } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s z { s.st.1 with regs := si.regs (_root_.Executable.labels exe).label s.st.1.regs } =
      { s with st := ({ s.st.1 with regs := si.regs (_root_.Executable.labels exe).label s.st.1.regs },
        n.pc + Int64.ofNat z) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨x, hx⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨x, hx.at he hn hdc hA' hD'⟩

/-- **`si_ndW` inside the trivial predicate**, with no outside moves. -/
theorem si_nd {n : ND} {si : SI} {z : Nat} (hok : si.ok = true) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(si.toDir, z)])
    (hedge : ∀ σ c, n.J σ c → ∃ c', LocalRun p c c' ∧
      Lands N E ⟨n.pc + Int64.ofNat z, si.so n.o, si.step (_root_.Executable.labels exe).label σ⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (si_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hok hF hcode hedge).toSeg

/-- **The system call the kernel model decodes** from the registers `r`
(`%rax`, then `%rdi`, `%rsi`, `%rdx`, `%r10`, `%r8`, `%r9`; `Scc.Sem.X64.abi`). -/
def syscallCall (r : Reg64s) : Option Scc.Sem.Kernel.Call :=
  Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.x64 r.rax.toNat fun i =>
    ([r.rdi, r.rsi, r.rdx, r.r10, r.r8, r.r9].getD i.val 0).toNat

/-- The registers after a `syscall` returns `v`: `%rax := v`, `%rcx :=`
the next pc `nx` (the address after the instruction), `%r11 :=` the flags
`fl`. -/
def syscallRegs (nx : Int64) (fl : BitVec 64) (v : BitVec 64) (r : Reg64s) : Reg64s :=
  { r with
    rax := UInt64.ofNat v.toNat
    rcx := UInt64.ofNat nx.toBitVec.toNat
    r11 := UInt64.ofNat fl.toNat }

/-- The abstract state after a `syscall` returns `v`, `nx` the next pc. -/
def syscallStep (nx : Int64) (v : BitVec 64) (σ : AS) : AS :=
  { σ with regs := syscallRegs nx (Scc.Sem.X64.rflags σ.status) v σ.regs }

/-- The static offsets after a `syscall`: `%rax`, `%rcx`, `%r11` forgotten. -/
def syscallSO (o : SO) : SO := ((o.kill .rax).kill .rcx).kill .r11

theorem syscallSO_rel {R : Region} {o : SO} {regs : Reg64s} (hr : SORel R o regs) (pc : Int64)
    (fl v : BitVec 64) : SORel R (syscallSO o) (syscallRegs pc fl v regs) := by
  intro r k h
  simp only [syscallSO, SO.get_kill _ (by decide : Reg64.r11 ≠ .rsp), SO.get_kill _ (by decide : Reg64.rcx ≠ .rsp),
    SO.get_kill _ (by decide : Reg64.rax ≠ .rsp)] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rw [← hr r k h]
  cases r <;> first | rfl | (exfalso; simp_all)

/-- **A node at a system call** `syscall`, under the kernel model
`Scc.Sem.X64.abi`: from every state of the invariant the call decodes (not
to `arch_prctl`), and for every result the kernel may return, the state
after it lands at a node after a local run of the source; the call is one
the judgement matches (`hok`, `SysOk`). Only the thread's control (see
`Out.sys`). Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem syscall_ndW {W : Frag isa} {K : State → State → Prop}
    {n : ND} {z : Nat} (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ σ c, n.J σ c → ∃ call, syscallCall σ.regs = some call ∧ (∀ a, call ≠ .archSetFs a) ∧
      ∀ v ∈ Scc.Sem.Kernel.results call,
        ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, syscallSO n.o,
          syscallStep (n.pc + Int64.ofNat z) v σ⟩ c')
    (hok : ∀ s c σ call, At exe endPc R F n s c → n.J σ c → syscallCall σ.regs = some call →
      SysOk p ms s c call) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := id hAt
  have hc : CellAt s (op64 .syscall) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨call, hcall, hna, hres⟩ := hedge σ c hJ
  have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.x64 (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
      some call := by
    rw [← hcall, syscallCall, ← hA.regs]; rfl
  refine .sys _ call hK (Scc.Sem.X64.atSyscall_of_cellAt hc) hd (hok s c σ call hAt hJ hcall) fun s' hs' => ?_
  obtain ⟨v, hv, rfl⟩ := (Scc.Sem.X64.mem_certSuccs_syscall hc hna).1 hs'
  obtain ⟨c', hr, hL⟩ := hres v hv
  refine ⟨c', hr, ?_⟩
  have hA' : Abs R (syscallSO n.o)
      { s.st.1 with regs := syscallRegs (n.pc + Int64.ofNat z) (Scc.Sem.X64.rflags σ.status) v s.st.1.regs }
      (syscallStep (n.pc + Int64.ofNat z) v σ) := by
    refine ⟨by simp only [syscallStep, hA.regs], hA.zmms, hA.status, ?_, hA.slot⟩
    exact syscallSO_rel hA.so _ _ _
  have hD' : F { s.st.1 with regs := syscallRegs (n.pc + Int64.ofNat z) (Scc.Sem.X64.rflags σ.status) v s.st.1.regs } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : syscallRet s z (Scc.Sem.X64.kret (Scc.Sem.X64.rflags s.st.1.status) (syscallInfo s z) v) =
      { s with st := ({ s.st.1 with
          regs := syscallRegs (n.pc + Int64.ofNat z) (Scc.Sem.X64.rflags σ.status) v s.st.1.regs },
        n.pc + Int64.ofNat z) } := by
    simp only [syscallRet, after, Scc.Sem.X64.kret, syscallRegs, hpc, hA.status]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨x, hx⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨x, hx.at he hn hdc hA' hD'⟩

/-- **`syscall_ndW` inside the trivial predicate**, with no outside moves. -/
theorem syscall_nd {n : ND} {z : Nat} (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hedge : ∀ σ c, n.J σ c → ∃ call, syscallCall σ.regs = some call ∧ (∀ a, call ≠ .archSetFs a) ∧
      ∀ v ∈ Scc.Sem.Kernel.results call,
        ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, syscallSO n.o,
          syscallStep (n.pc + Int64.ofNat z) v σ⟩ c')
    (hok : ∀ s c σ call, At exe endPc R F n s c → n.J σ c → syscallCall σ.regs = some call →
      SysOk p ms s c call) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (syscall_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hK hF hcode hedge hok).toSeg

/-- `movq %fs:k, %d`. -/
def fsDir (d : Reg64) (k : Int64) : Directive :=
  op64 (.movfs (.reg (.low d .W64)) (.mem { base := none, idx := none, disp := .int64 k }))

/-- The abstract state after a thread-pointer load of `v` into `d`. -/
def fsStep (d : Reg64) (v : BitVec 64) (σ : AS) : AS := { σ with regs := σ.regs.set64 d v }

/-- **A node at a thread-pointer load** `movq %fs:k, %d` (`d` not `%rsp`):
from every state of the invariant the address (the thread pointer plus
`k`) is owned by the runtime (`ms.rt`) and mapped for reading (`ms.mp`),
is not in the thread's private memory (it resolves to itself: a node's
states have no declarations, `At`), and
for every value read the state
after it (`d` the value, its offset forgotten) lands at a node after a local
run of the source. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem fsld_ndW {W : Frag isa} {K : State → State → Prop}
    {n : ND} {d : Reg64} {k : Int64} {z : Nat} (hd : d ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fsDir d k, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + k.toBitVec).toNat ∧ ms.mp ⟨σ.regs.fsBase.toBitVec + k.toBitVec, 8⟩ false ∧
      Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + k.toBitVec) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ ∀ v, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill d, fsStep d v σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (fsDir d k) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨hrt, hmp, hdm, c', hr, hL⟩ := hedge _ σ c hA hD hJ
  have ha : fsAddr s z { base := none, idx := none, disp := .int64 k } = σ.regs.fsBase.toBitVec + k.toBitVec := by
    simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
  have hex := exec_movfs_load_agrees hc ha hdm (agrees_of_decls hdc _ _)
  refine .rtLoad _ _ _ c' hex hrt hmp hr fun v _ _ => ?_
  have hset : s.st.1.regs.set (Reg.low d .W64) (v.setWidth 64) = s.st.1.regs.set64 d (v.setWidth 64) := by
    cases d <;> rfl
  have hA' : Abs R (n.o.kill d) { s.st.1 with regs := s.st.1.regs.set64 d (v.setWidth 64) }
      (fsStep d (v.setWidth 64) σ) := by
    refine ⟨by simp only [fsStep, hA.regs], hA.zmms, hA.status, ?_, hA.slot⟩
    exact SORel.write (o := n.o) (d := d) (by simp [SO.write, hd]) hA.so fun r hr =>
      Reg64s.get64_set64_ne _ hr _
  have hD' : F { s.st.1 with regs := s.st.1.regs.set64 d (v.setWidth 64) } := hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s z { s.st.1 with regs := s.st.1.regs.set (Reg.low d .W64) (v.setWidth 64) } =
      { s with st := ({ s.st.1 with regs := s.st.1.regs.set64 d (v.setWidth 64) }, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc, hset]
  rw [hs1]
  rcases hL (v.setWidth 64) with ⟨j, hj⟩ | ⟨x, hx⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨x, hx.at he hn hdc hA' hD'⟩

/-- **`fsld_ndW` inside the trivial predicate**, with no outside moves. -/
theorem fsld_nd {n : ND} {d : Reg64} {k : Int64} {z : Nat} (hd : d ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fsDir d k, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + k.toBitVec).toNat ∧ ms.mp ⟨σ.regs.fsBase.toBitVec + k.toBitVec, 8⟩ false ∧
      Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + k.toBitVec) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ ∀ v, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill d, fsStep d v σ⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (fsld_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hd hF hcode hedge).toSeg

end Fn

/-! ## The parser's forms -/

section Parse

open Kraken.X64.Parser

/-- `SI.toDir` is what Kraken's parser makes of scc's text. -/
example : parse("leaq scc_rt_heap(%rip), %rax") = [SI.toDir (.leaRip .rax "scc_rt_heap")] := by
  decide

/-- `fsDir` is what Kraken's parser makes of scc's thread-pointer loads. -/
example : parse("movq %fs:8, %r11
movq %fs:0, %rax") = [fsDir .r11 8, fsDir .rax 0] := by
  decide

/-- `syscall` is what `syscall_nd` reads. -/
example : parse("syscall") = [op64 .syscall] := by
  decide

end Parse

end Spike.Lib.X64
