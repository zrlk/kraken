/-
**hello.w's worker states off the transfer sites, its system calls
`print`'s `write` allowed** (`WCompatH.noSite`,
`WCompatH.sysOkH`, AArch64): `Spike/Lib/A64WakeNN.lean`'s `NN` with the
system-call condition a parameter `Sy`.

wake's worker makes no `write`, so `NN` asks every system call `exit` or
neither a `write` nor an `exit_group` (`SysSafe`, `WCompat.sysOk`). hello's
worker calls `print`, whose one system call is a `write` to fd 1; the
worker side's field is `WCompatH.sysOkH` (`SysSafeH`: `exit`, a `write` to
fd 1, at `scc_rt_abort_write`'s two calls (`AbW`, `print`'s refused write's
abort) a `write` to fd 2 or `exit_group(101)`, or neither). Inside `print` the condition is the `write` alone
(`SysW1`), which also rules out `exit` (`NoTop`, the callee's rows at depth,
`Spike/Lib/HelloSegTCS.lean`).

- `SysP Sy s`, `NNP Sy exe endPc s`, `NNZP Sy exe endPc Z`: a system call at
  `s` decodes into `Sy`; `NN` and `NNZ` over `SysP Sy`.
- `AbW`, `AbC`, `safeH`, `SysSafeH`, `NNH`, `NNZH`: at
  `Sy := safeH (AbC exe s)` (`WCompatH.sysOkH`'s condition;
  `scc_rt_abort_write`'s two calls each at its own site, `AbC`, inside
  `AbW`: `AbC.toAbW`); `sysSafe_H`, `NN.toH`, `NNZ.toH`, `NNP.toH`, `SegTC.toH`: wake's
  are hello's (every leaf of `A64WakeNN` reused as is).
- `SysW1`, `NNZP.toH`, `noTop_of`: `print`'s condition, a `write` to fd 1;
  its states are `NNZH`, and at no `exit` (with the control at no `unpark`,
  `NoTop`).
- `nn_of_cellP`, `blkW_nnzP`, `nodeW_nnzP`, `nodeW_nnzPSvc`: a node's states
  are `NNZP Sy` (no `nop`, no `svc`; an `svc` whose call is in `Sy`).
- `seg_ndNNP`, `dmb_ndNNP`, `step_ndNNP`: the leaves over
  `SegTC (NNZP Sy exe endPc Z)`: a block, a fence (`print`'s `dmb ish`), any
  node given row by row (`print`'s `write`, `PrintF.FA.hsvc_of_emitT`'s
  row).
-/
import Spike.Lib.A64WakeNN
import Spike.Lib.HelloSegTCS

namespace Spike.Lib.A64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.HelloSegTCS (NoTop)

/-! ## The system-call condition as a parameter -/

/-- **A system call in `Sy`**: at a system call of the kernel model
`Scc.Sem.A64.abi`, the call decoded satisfies `Sy`. -/
def SysP (Sy : Scc.Sem.Kernel.Call → Prop) (s : State) : Prop :=
  Scc.Sem.A64.abi.atSys s = true → ∀ call, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s)
    (Scc.Sem.A64.abi.arg s) = some call → Sy call

/-- **A state off the transfer sites, its system call in `Sy`** (`NN` over
`SysP Sy`). -/
def NNP (Sy : Scc.Sem.Kernel.Call → Prop) (exe : _root_.Executable) (endPc : Int64) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧ Scc.Sem.A64.atNop s = false ∧ SysP Sy s

/-- **Off the transfer sites, its system call in `Sy`, with `Z`.** -/
def NNZP (Sy : Scc.Sem.Kernel.Call → Prop) (exe : _root_.Executable) (endPc : Int64) (Z : Frag isaLSE2) :
    Frag isaLSE2 :=
  fun s c => NNP Sy exe endPc s ∧ Z s c

/-- **At one of `scc_rt_abort_write`'s two system calls** (by label in
`exe`): its `write` of the message to fd 2 (`Abort.pcSvc` of `Abort.write`)
or its `exit_group(101)` (`scc_rt_abort_write_exit`, the `writeErr` abort
site). `print`'s refused `write` reaches them through `scc_rt_abort(4)`. -/
def AbW (exe : _root_.Executable) (s : State) : Prop :=
  s.st.2 = Spike.Lib.A64.Abort.pcSvc (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write ∨
    s.st.2 = (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write.exit

/-- **`scc_rt_abort_write`'s two system calls, each pinned to its site**
(the abort exit's system calls): the `write` to fd 2 at `Abort.pcSvc … Abort.write`,
`exit_group(abortStatus)` at `Abort.write.exit`. (A site-blind
`AbW ∧ (write 2 ∨ exit_group)` would allow `exit_group` at the `write`'s
site, so `AbExit` at `helloDR` would not follow.) -/
def AbC (exe : _root_.Executable) (s : State) (call : Scc.Sem.Kernel.Call) : Prop :=
  (s.st.2 = Spike.Lib.A64.Abort.pcSvc (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write ∧
      ∃ buf n, call = .write 2 buf n) ∨
    (s.st.2 = (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write.exit ∧
      call = .exitGroup Scc.Sem.Kernel.abortStatus)

/-- `AbC` is at `AbW`, its call a `write` to fd 2 or `exit_group(abortStatus)`. -/
theorem AbC.toAbW {exe : _root_.Executable} {s : State} {call : Scc.Sem.Kernel.Call} (h : AbC exe s call) :
    AbW exe s ∧ ((∃ buf n, call = .write 2 buf n) ∨ call = .exitGroup Scc.Sem.Kernel.abortStatus) :=
  h.elim (fun ⟨hp, hw⟩ => ⟨.inl hp, .inl hw⟩) fun ⟨hp, hx⟩ => ⟨.inr hp, .inr hx⟩

/-- **The worker's system calls** (`WCompatH.sysOkH`, with
`print`'s abort): `exit`, a `write` to fd 1 (`print`'s), at the write abort
stub a call of `ab` (`AbC`: a `write` to fd 2 at its site,
`exit_group(abortStatus)` at its), or neither a `write` nor an
`exit_group`. -/
def safeH (ab : Scc.Sem.Kernel.Call → Prop) (call : Scc.Sem.Kernel.Call) : Prop :=
  call = .exit ∨ (∃ buf n, call = .write 1 buf n) ∨ ab call ∨
    ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)

/-- **A safe system call for hello** (`WCompatH.sysOkH`'s fact). -/
def SysSafeH (exe : _root_.Executable) (s : State) : Prop := SysP (safeH (AbC exe s)) s

/-- **A hello worker state off the transfer sites.** -/
def NNH (exe : _root_.Executable) (endPc : Int64) (s : State) : Prop := NNP (safeH (AbC exe s)) exe endPc s

/-- **Off the transfer sites for hello, with `Z`.** -/
def NNZH (exe : _root_.Executable) (endPc : Int64) (Z : Frag isaLSE2) : Frag isaLSE2 :=
  fun s c => NNH exe endPc s ∧ Z s c

/-- **`print`'s system call**: a `write` to fd 1. -/
def SysW1 (call : Scc.Sem.Kernel.Call) : Prop := ∃ buf n, call = .write 1 buf n

variable {exe : _root_.Executable} {endPc : Int64} {Z : Frag isaLSE2} {Sy Sy' : Scc.Sem.Kernel.Call → Prop}

/-- A weaker condition. -/
theorem NNP.mono {s : State} (h : NNP Sy exe endPc s) (hS : ∀ call, Sy call → Sy' call) : NNP Sy' exe endPc s :=
  ⟨h.1, h.2.1, h.2.2.1, fun ha call hd => hS call (h.2.2.2 ha call hd)⟩

/-- A weaker condition, with `Z`. -/
theorem NNZP.mono {s : State} {c : Ctl} (h : NNZP Sy exe endPc Z s c) (hS : ∀ call, Sy call → Sy' call) :
    NNZP Sy' exe endPc Z s c :=
  ⟨h.1.mono hS, h.2⟩

/-- **wake's safe call is hello's.** -/
theorem sysSafe_H {s : State} (h : SysSafe s) : SysSafeH exe s :=
  fun ha call hd => (h ha call hd).elim .inl fun h => .inr (.inr (.inr h))

/-- wake's `NN` is hello's. -/
theorem NN.toH {s : State} (h : NN exe endPc s) : NNH exe endPc s :=
  ⟨h.1, h.2.1, h.2.2.1, sysSafe_H h.2.2.2⟩

/-- wake's `NNZ` is hello's. -/
theorem NNZ.toH {s : State} {c : Ctl} (h : NNZ exe endPc Z s c) : NNZH exe endPc Z s c :=
  ⟨h.1.toH, h.2⟩

/-- `NNH` is `NNP` at the state's condition. -/
theorem NNP.toH {s : State} (h : NNP Sy exe endPc s) (hS : ∀ call, Sy call → safeH (AbC exe s) call) :
    NNH exe endPc s :=
  h.mono hS

/-- `print`'s `write` is a hello worker's call. -/
theorem NNZP.toH {s : State} {c : Ctl} (h : NNZP SysW1 exe endPc Z s c) : NNZH exe endPc Z s c :=
  ⟨h.1.toH fun _ h => .inr (.inl h), h.2⟩

/-- **A segment of wake's leaves is one inside hello's fragment.** -/
theorem SegTC.toH {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {P Q : Frag isaLSE2}
    (h : SegTC (NNZ exe endPc Z) p lbl ms P Q) : SegTC (NNZH exe endPc Z) p lbl ms P Q :=
  h.mono_S fun _ _ h => h.toH

/-- **No thread-only row at `print`'s states**: its system call a `write`
(no `exit`), its control at no `unpark` binding (`hu`). -/
theorem noTop_of {ms : MemSide isaLSE2} {s : State} {c : Ctl} (hK : ms.K = some Scc.Sem.A64.abi)
    (h : NNP SysW1 exe endPc s) (hu : ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e) : NoTop ms s c := by
  refine ⟨hu, fun K hk ha hd => ?_⟩
  rw [hK] at hk
  cases hk
  obtain ⟨buf, n, h⟩ := h.2.2.2 ha _ hd
  cases h

/-! ## A node's states -/

/-- A cell other than a `nop` or an `svc` is off the transfer sites, at no
system call (any `Sy`). -/
theorem nn_of_cellP {s : State} {d : Directive} (hc : CellAt s d 4) (he : s.exe = exe) (hn : s.endPc = endPc)
    (hd : notNop d = true) : NNP Sy exe endPc s := by
  refine ⟨he, hn, Scc.Sem.A64.atNop_false_of_cellAt hc (notNop_ne hd), fun ha => ?_⟩
  have : Scc.Sem.A64.atSvc s = false := Scc.Sem.A64.atSvc_false_of_cellAt hc (notNop_neSvc hd)
  exact absurd ha (by simp only [Scc.Sem.A64.abi] at ha ⊢; rw [this]; decide)

section Nodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **A block node's states are `NNZP Sy`**: its block has no `nop` or
`svc`, `Z` at its pcs. -/
theorem blkW_nnzP {n : ND} {blk : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hb : blk.all notNop = true)
    (hz : NodeZ Z exe n blk.length) : BlkW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ hJ k hk m _ _
  refine ⟨⟨?_, hz _ σ c k hk he rfl hJ⟩, fun _ h => h⟩
  have hd := List.all_eq_true.mp hb _ (List.getElem_mem hk)
  exact nn_of_cellP ((hcode s he hn).cell (List.getElem?_eq_getElem hk) rfl rfl rfl) he hn hd

/-- **A node's states are `NNZP Sy`**: its first directive is not a `nop`
or an `svc`, `Z` at its pc. -/
theorem nodeW_nnzP {n : ND} {d : Directive} {ds : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (d :: ds)) (hd : notNop d = true)
    (hz : NodeZ Z exe n 1) : NodeW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, _, hpc, σ, _, _, hJ⟩ =>
    ⟨⟨nn_of_cellP ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)) he hn hd,
      hz s σ c 0 (by decide) he (by rw [hpc, Spike.Lib.A64.Flow.ofNat4_zero]) hJ⟩, fun _ h => h⟩

/-- **A system call's node's states are `NNZP Sy`**: the call its invariant
decodes is in `Sy` (`hsafe`), `Z` at its pc. -/
theorem nodeW_nnzPSvc {n : ND}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hsafe : ∀ σ c, n.J σ c → ∀ call, svcCall σ.regs = some call → Sy call) (hz : NodeZ Z exe n 1) :
    NodeW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, _, hpc, σ, hA, _, hJ⟩ => by
    have hc : CellAt s svcDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
    refine ⟨⟨⟨he, hn, Scc.Sem.A64.atNop_false_of_cellAt hc (by rintro w ⟨⟩), fun _ call hd => ?_⟩,
      hz s σ c 0 (by decide) he (by rw [hpc, Spike.Lib.A64.Flow.ofNat4_zero]) hJ⟩, fun _ h => h⟩
    exact hsafe σ c hJ call (by rw [svcCall, ← hA.regs]; exact hd)

/-! ## The leaves -/

/-- **A block node inside `NNZP Sy`** (`seg_ndW`). -/
theorem seg_ndNNP {n : ND} {lo hi : Int} {blk : List Directive} (hne : blk ≠ [])
    (hok : okBlk lo hi n.o blk = true) (hb : blk.all notNop = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hedge : ∀ σ c, n.J σ c →
      ∃ c', LocalRun p c c' ∧ Lands N E (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩) c')
    (hz : NodeZ Z exe n blk.length) :
    SegTC (NNZP Sy exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (seg_ndW hne hok hF hR hal hlo hhi hcode (blkW_nnzP hcode hb hz) hedge)

/-- **Any node given row by row** inside `NNZP Sy` (its states there,
`hW`): a system call's node whose row is not `Out.sys` (`print`'s
`write`, the output row `Out.emit`). -/
theorem step_ndNNP {n : ND} {Q : Frag isaLSE2} (hW : NodeW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n)
    (h : ∀ s c, At exe endPc R F n s c → OutT p lbl ms Q s c) :
    SegTC (NNZP Sy exe endPc Z) p lbl ms (At exe endPc R F n) Q :=
  SegTC.step (fun s c hs => (hW s c hs).1) h

/-- **A fence's node inside `NNZP Sy`** (`dmb_nd`; `print`'s `dmb ish`):
the source stutters (`OutT.fnc`). -/
theorem dmb_ndNNP {n : ND} {k : FenceKind}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [.instr ⟨.W64, .DMB k⟩])
    (hedge : ∀ σ c, n.J σ c → Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c) (hz : NodeZ Z exe n 1) :
    SegTC (NNZP Sy exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine step_ndNNP (nodeW_nnzP hcode rfl hz) fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (.instr ⟨.W64, .DMB k⟩) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  refine .fnc k _ c (exec_dmb hc) (.refl c) ?_
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hedge σ c hJ with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-! ## The leaves with `Z` at the node's states

`NodeZA`/`NodeW` (`Spike/Lib/A64WakeNN.lean`) in place of `NodeZ`: `Z` may
read the registers and the frame's cells (the instruction's event tree,
`RelZ`). -/

/-- **`blkW_nnzP` with `Z` at the block's states** (`NodeZA`). -/
theorem blkW_nnzPA {n : ND} {blk : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hb : blk.all notNop = true)
    (hz : NodeZA Z exe endPc R F n blk) : BlkW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn hd hpc hA hD hJ k hk m hA' hD'
  refine ⟨⟨?_, (hz s σ c he hn hd hpc hA hD hJ k hk m hA' hD').1⟩, fun _ h => h⟩
  have hd := List.all_eq_true.mp hb _ (List.getElem_mem hk)
  exact nn_of_cellP ((hcode s he hn).cell (List.getElem?_eq_getElem hk) rfl rfl rfl) he hn hd

/-- **`nodeW_nnzP` with `Z` at the node's states** (`NodeW`). -/
theorem nodeW_nnzPA {n : ND} {d : Directive} {ds : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (d :: ds)) (hd : notNop d = true)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) : NodeW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c hs =>
    ⟨⟨nn_of_cellP ((hcode s hs.1 hs.2.1).cell (j := 0) rfl rfl rfl (by rw [hs.2.2.2.1]; simp)) hs.1 hs.2.1 hd,
      (hz s c hs).1⟩, fun _ h => h⟩

/-- **`nodeW_nnzPSvc` with `Z` at the node's states** (`NodeW`). -/
theorem nodeW_nnzPSvcA {n : ND}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hsafe : ∀ σ c, n.J σ c → ∀ call, svcCall σ.regs = some call → Sy call)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    NodeW (NNZP Sy exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c hs => ⟨⟨((nodeW_nnzPSvc (Z := fun _ _ => True) hcode hsafe (fun _ _ _ _ _ _ _ _ => trivial)) s c hs).1.1,
    (hz s c hs).1⟩, fun _ h => h⟩

/-- **`seg_ndNNP` with `Z` at the block's states** (`NodeZA`). -/
theorem seg_ndNNPA {n : ND} {lo hi : Int} {blk : List Directive} (hne : blk ≠ [])
    (hok : okBlk lo hi n.o blk = true) (hb : blk.all notNop = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hedge : ∀ σ c, n.J σ c →
      ∃ c', LocalRun p c c' ∧ Lands N E (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩) c')
    (hz : NodeZA Z exe endPc R F n blk) :
    SegTC (NNZP Sy exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (seg_ndW hne hok hF hR hal hlo hhi hcode (blkW_nnzPA hcode hb hz) hedge)

/-- **`dmb_ndNNP` with `Z` at the node's states** (`NodeW`). -/
theorem dmb_ndNNPA {n : ND} {k : FenceKind}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [.instr ⟨.W64, .DMB k⟩])
    (hedge : ∀ σ c, n.J σ c → Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZP Sy exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine step_ndNNP (nodeW_nnzPA hcode rfl hz) fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (.instr ⟨.W64, .DMB k⟩) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  refine .fnc k _ c (exec_dmb hc) (.refl c) ?_
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hedge σ c hJ with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

end Nodes

end Spike.Lib.A64.Flow.Worker
