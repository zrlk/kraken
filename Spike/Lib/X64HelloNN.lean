/-
**hello.w's worker states off the transfer sites on x86-64, its system calls `print`'s `write` allowed**
(`WCompatH.noSite`, `WCompatH.sysOkH`): `Spike/Lib/X64WakeNN.lean`'s `NN` with
the system-call condition a parameter `Sy`.

wake's worker makes no `write`, so `NN` asks every system call `exit` or neither a `write` nor an
`exit_group` (`SysSafe`, `WCompat.sysOk`). hello's worker calls `print`, whose one system call is a `write`
to fd 1; the worker side's field is `WCompatH.sysOkH` (`SysSafeH`: `exit`, a `write` to fd 1, at
`scc_rt_abort_write`'s two calls (`AbW`, `print`'s refused write's abort) a `write` to fd 2 or
`exit_group(101)`, or neither). Inside `print` the condition is the `write` alone (`SysW1`), which also rules
out `exit` (`NoTop`, the callee's rows at depth, `Spike/Lib/HelloSegTCS.lean`).

- `SysP Sy s`, `NNP Sy exe endPc s`, `NNZP Sy exe endPc Z`: a system call at `s` decodes into `Sy`; `NN` and
  `NNZ` over `SysP Sy`.
- `AbW`, `AbC`, `safeH`, `SysSafeH`, `NNH`, `NNZH`: at `Sy := safeH (AbC exe s)` (`WCompatH.sysOkH`'s
  condition; `scc_rt_abort_write`'s two calls each at its own site, `AbC`, inside `AbW`: `AbC.toAbW`);
  `sysSafe_H`, `NN.toH`, `NNP.toH`: wake's are hello's.
- `SysW1`, `NNZP.toH`, `noTop_of`: `print`'s condition, a `write` to fd 1; its states are `NNZH`, and at no
  `exit` (with the control at no `unpark`, `NoTop`).
- `nn_of_cellP`, `nodeW_nnzPSvc`: a node's states are `NNP Sy` (no `nop`, no `syscall`; a `syscall` whose
  call is in `Sy`).
- `step_ndNNP`, `blkW_nnzPA`, `nodeW_nnzPA`, `nodeW_nnzPSvcA`, `seg_ndNNPA`: the leaves over
  `SegTC (NNZP Sy exe endPc Z)` with `Z` at the node's states (`NodeZA`/`NodeW`): a block, any node given
  row by row (`print`'s `write`).

## Differences from the AArch64 version

`Spike/Lib/A64HelloNN.lean`.

- The cells are sized (`List (Directive × Nat)`, `X64WakeNN.NodeZ` indexed by the node's block), the system
  call is `syscall` (`syscallCall`), and `scc_rt_abort_write`'s `write` site is `X64Abort.pcSys`.
- `print` has no fence on x86-64, so there is no twin of `dmb_ndNNPA`.
- Only the live constants are twinned: `NNZ.toH`, `NNZP.mono`, `SegTC.toH`, `blkW_nnzP`, `nodeW_nnzP`,
  `seg_ndNNP` and `dmb_ndNNP` are not.
-/
import Spike.Lib.X64WakeNN
import Spike.Lib.X64Abort
import Spike.Lib.HelloSegTCS

namespace Spike.Lib.X64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.HelloSegTCS (NoTop)

/-! ## The system-call condition as a parameter -/

/-- **A system call in `Sy`**: at a system call of the kernel model
`Scc.Sem.X64.abi`, the call decoded satisfies `Sy`. -/
def SysP (Sy : Scc.Sem.Kernel.Call → Prop) (s : State) : Prop :=
  Scc.Sem.X64.abi.atSys s = true → ∀ call, Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s)
    (Scc.Sem.X64.abi.arg s) = some call → Sy call

/-- **A state off the transfer sites, its system call in `Sy`** (`NN` over
`SysP Sy`). -/
def NNP (Sy : Scc.Sem.Kernel.Call → Prop) (exe : _root_.Executable) (endPc : Int64) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧ Scc.Sem.X64.atNop s = false ∧ SysP Sy s

/-- **Off the transfer sites, its system call in `Sy`, with `Z`.** -/
def NNZP (Sy : Scc.Sem.Kernel.Call → Prop) (exe : _root_.Executable) (endPc : Int64) (Z : Frag isa) :
    Frag isa :=
  fun s c => NNP Sy exe endPc s ∧ Z s c

/-- **At one of `scc_rt_abort_write`'s two system calls** (by label in
`exe`): its `write` of the message to fd 2 (`Abort.pcSys` of `Abort.write`)
or its `exit_group(101)` (`scc_rt_abort_write_exit`, the `writeErr` abort
site). `print`'s refused `write` reaches them through `scc_rt_abort(4)`. -/
def AbW (exe : _root_.Executable) (s : State) : Prop :=
  s.st.2 = Spike.Lib.X64.Abort.pcSys (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write ∨
    s.st.2 = (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write.exit

/-- **`scc_rt_abort_write`'s two system calls, each pinned to its site**:
the `write` to fd 2 at `Abort.pcSys … Abort.write`,
`exit_group(abortStatus)` at `Abort.write.exit`. (A site-blind
`AbW ∧ (write 2 ∨ exit_group)` would allow `exit_group` at the `write`'s
site, so `AbExit` at `helloDR` would not follow.) -/
def AbC (exe : _root_.Executable) (s : State) (call : Scc.Sem.Kernel.Call) : Prop :=
  (s.st.2 = Spike.Lib.X64.Abort.pcSys (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write ∧
      ∃ buf n, call = .write 2 buf n) ∨
    (s.st.2 = (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write.exit ∧
      call = .exitGroup Scc.Sem.Kernel.abortStatus)

/-- `AbC` is at `AbW`, its call a `write` to fd 2 or `exit_group(abortStatus)`. -/
theorem AbC.toAbW {exe : _root_.Executable} {s : State} {call : Scc.Sem.Kernel.Call} (h : AbC exe s call) :
    AbW exe s ∧ ((∃ buf n, call = .write 2 buf n) ∨ call = .exitGroup Scc.Sem.Kernel.abortStatus) :=
  h.elim (fun ⟨hp, hw⟩ => ⟨.inl hp, .inl hw⟩) fun ⟨hp, hx⟩ => ⟨.inr hp, .inr hx⟩

/-- **The worker's system calls** (`WCompatH.sysOkH`): `exit`, a `write` to
fd 1 (`print`'s), at the write abort stub a call of `ab` (`AbC`: a `write`
to fd 2 at its site, `exit_group(abortStatus)` at its), or neither a `write`
nor an `exit_group`. -/
def safeH (ab : Scc.Sem.Kernel.Call → Prop) (call : Scc.Sem.Kernel.Call) : Prop :=
  call = .exit ∨ (∃ buf n, call = .write 1 buf n) ∨ ab call ∨
    ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)

/-- **A safe system call for hello** (`WCompatH.sysOkH`'s fact). -/
def SysSafeH (exe : _root_.Executable) (s : State) : Prop := SysP (safeH (AbC exe s)) s

/-- **A hello worker state off the transfer sites.** -/
def NNH (exe : _root_.Executable) (endPc : Int64) (s : State) : Prop := NNP (safeH (AbC exe s)) exe endPc s

/-- **Off the transfer sites for hello, with `Z`.** -/
def NNZH (exe : _root_.Executable) (endPc : Int64) (Z : Frag isa) : Frag isa :=
  fun s c => NNH exe endPc s ∧ Z s c

/-- **`print`'s system call**: a `write` to fd 1. -/
def SysW1 (call : Scc.Sem.Kernel.Call) : Prop := ∃ buf n, call = .write 1 buf n

variable {exe : _root_.Executable} {endPc : Int64} {Z : Frag isa} {Sy Sy' : Scc.Sem.Kernel.Call → Prop}

/-- A weaker condition. -/
theorem NNP.mono {s : State} (h : NNP Sy exe endPc s) (hS : ∀ call, Sy call → Sy' call) : NNP Sy' exe endPc s :=
  ⟨h.1, h.2.1, h.2.2.1, fun ha call hd => hS call (h.2.2.2 ha call hd)⟩

/-- **wake's safe call is hello's.** -/
theorem sysSafe_H {s : State} (h : SysSafe s) : SysSafeH exe s :=
  fun ha call hd => (h ha call hd).elim .inl fun h => .inr (.inr (.inr h))

/-- wake's `NN` is hello's. -/
theorem NN.toH {s : State} (h : NN exe endPc s) : NNH exe endPc s :=
  ⟨h.1, h.2.1, h.2.2.1, sysSafe_H h.2.2.2⟩

/-- `NNH` is `NNP` at the state's condition. -/
theorem NNP.toH {s : State} (h : NNP Sy exe endPc s) (hS : ∀ call, Sy call → safeH (AbC exe s) call) :
    NNH exe endPc s :=
  h.mono hS

/-- `print`'s `write` is a hello worker's call. -/
theorem NNZP.toH {s : State} {c : Ctl} (h : NNZP SysW1 exe endPc Z s c) : NNZH exe endPc Z s c :=
  ⟨h.1.toH fun _ h => .inr (.inl h), h.2⟩

/-- **No thread-only row at `print`'s states**: its system call a `write`
(no `exit`), its control at no `unpark` binding (`hu`). -/
theorem noTop_of {ms : MemSide isa} {s : State} {c : Ctl} (hK : ms.K = some Scc.Sem.X64.abi)
    (h : NNP SysW1 exe endPc s) (hu : ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e) : NoTop ms s c := by
  refine ⟨hu, fun K hk ha hd => ?_⟩
  rw [hK] at hk
  cases hk
  obtain ⟨buf, n, h⟩ := h.2.2.2 ha _ hd
  cases h

/-! ## A node's states -/

/-- A cell other than a `nop` or a `syscall` is off the transfer sites, at
no system call (any `Sy`). -/
theorem nn_of_cellP {s : State} {d : Directive} {z : Nat} (hc : CellAt s d z) (he : s.exe = exe)
    (hn : s.endPc = endPc) (hd : notNop d = true) : NNP Sy exe endPc s := by
  refine ⟨he, hn, Scc.Sem.X64.atNop_false_of_cellAt hc (notNop_ne hd), fun ha => ?_⟩
  have : Scc.Sem.X64.atSyscall s = false := Scc.Sem.X64.atSyscall_false_of_cellAt hc (notNop_neSys hd)
  exact absurd ha (by simp only [Scc.Sem.X64.abi] at ha ⊢; rw [this]; decide)

section Nodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **A system call's node's states are `NNZP Sy`**: the call its invariant
decodes is in `Sy` (`hsafe`), `Z` at its pc. -/
theorem nodeW_nnzPSvc {n : ND} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hsafe : ∀ σ c, n.J σ c → ∀ call, syscallCall σ.regs = some call → Sy call)
    (hz : NodeZ Z exe n [(op64 .syscall, z)]) :
    NodeW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, _, hpc, σ, hA, _, hJ⟩ => by
    have hc : CellAt s (op64 .syscall) z := (hcode s he hn).cell0 rfl rfl hpc
    refine ⟨⟨⟨he, hn, Scc.Sem.X64.atNop_false_of_cellAt hc (by intro w w' n h; cases h), fun _ call hd => ?_⟩,
      hz s σ c 0 (by simp) he (by rw [hpc, cellOff_zero]) hJ⟩, fun _ h => h⟩
    exact hsafe σ c hJ call (by rw [syscallCall, ← hA.regs]; exact hd)

/-! ## The leaves -/

/-- **Any node given row by row** inside `NNZP Sy` (its states there,
`hW`): a system call's node whose row is not `Out.sys` (`print`'s
`write`, the output row `Out.emit`). -/
theorem step_ndNNP {n : ND} {Q : Frag isa} (hW : NodeW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n)
    (h : ∀ s c, At exe endPc R F n s c → OutT p lbl ms Q s c) :
    SegTC (NNZP Sy exe endPc Z) p lbl ms (At exe endPc R F n) Q :=
  SegTC.step (fun s c hs => (hW s c hs).1) h

/-! ## The leaves with `Z` at the node's states

`NodeZA`/`NodeW` (`Spike/Lib/X64WakeNN.lean`): `Z` may read the registers
and the frame's cells (the instruction's event tree, `RelZ`). -/

/-- **A block node's states are `NNZP Sy`, with `Z` at the block's states**
(`NodeZA`): its block has no `nop` or `syscall`. -/
theorem blkW_nnzPA {n : ND} {blk : List (Directive × Nat)}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hb : blk.all (fun c => notNop c.1) = true)
    (hz : NodeZA Z exe endPc R F n blk) : BlkW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn hd hpc hA hD hJ k hk m hA' hD'
  refine ⟨⟨?_, (hz s σ c he hn hd hpc hA hD hJ k hk m hA' hD').1⟩, fun _ h => h⟩
  have hd := List.all_eq_true.mp hb _ (List.getElem_mem hk)
  exact nn_of_cellP ((hcode s he hn).cell (List.getElem?_eq_getElem hk) rfl rfl rfl) he hn hd

/-- **A node's states are `NNZP Sy`, with `Z` at the node's states**
(`NodeW`): its first directive is not a `nop` or a `syscall`. -/
theorem nodeW_nnzPA {n : ND} {d : Directive} {z : Nat} {ds : List (Directive × Nat)}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc ((d, z) :: ds)) (hd : notNop d = true)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    NodeW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c hs =>
    ⟨⟨nn_of_cellP ((hcode s hs.1 hs.2.1).cell0 rfl rfl hs.2.2.2.1) hs.1 hs.2.1 hd, (hz s c hs).1⟩,
      fun _ h => h⟩

/-- **`nodeW_nnzPSvc` with `Z` at the node's states** (`NodeW`). -/
theorem nodeW_nnzPSvcA {n : ND} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hsafe : ∀ σ c, n.J σ c → ∀ call, syscallCall σ.regs = some call → Sy call)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    NodeW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c hs => ⟨⟨((nodeW_nnzPSvc (Z := fun _ _ => True) hcode hsafe NodeZ.top) s c hs).1.1,
    (hz s c hs).1⟩, fun _ h => h⟩

/-- **A block node inside `NNZP Sy`, with `Z` at the block's states**
(`seg_ndW`, `NodeZA`). -/
theorem seg_ndNNPA {n : ND} {lo hi : Int} {blk : List (Directive × Nat)} (hne : blk ≠ [])
    (hok : okBlk lo hi n.o blk = true) (hb : blk.all (fun c => notNop c.1) = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hedge : ∀ σ c, n.J σ c →
      ∃ c', LocalRun p c c' ∧ Lands N E (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩) c')
    (hz : NodeZA Z exe endPc R F n blk) :
    SegTC (NNZP Sy exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (seg_ndW hne hok hF hR hlo hhi hcode (blkW_nnzPA hcode hb hz) hedge)

end Nodes

end Spike.Lib.X64.Flow.Worker

/-- info: 'Spike.Lib.X64.Flow.Worker.seg_ndNNPA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.seg_ndNNPA

/-- info: 'Spike.Lib.X64.Flow.Worker.nodeW_nnzPSvcA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.nodeW_nnzPSvcA
