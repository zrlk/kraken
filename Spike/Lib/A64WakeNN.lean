/-
**The worker's states are off the transfer sites** (`WCompat.noSite`, AArch64): the leaves of the worker's segments over
`SegTS (NN exe endPc)`, every state of the hidden invariant at a cell other
than a `nop`.

The kernel's transfer sites (`scc_rt_take_site`, `scc_rt_release_site`) are
`nop`s; a state at a cell that is not a `nop` has `Scc.Sem.A64.atNop s =
false`. Each node of the worker's functions proves it of its own states from
its code (`CodeAt.cell`, `Scc.Sem.A64.atNop_false_of_cellAt`) and a decided
check that its block has no `nop` (`notNop`), so the fact rides along the
segment through `SegTS`'s combinators (`Spike/Lib/SegThrS.lean`).

- `NN exe endPc s`: the executable, its end, no `nop` at the pc, and a
  system call there safe (`SysSafe`: `exit`, or neither `write` nor
  `exit_group`; `WCompat.sysOk`).
- `notNop`, `nn_of_cell`: the check on a directive (neither `nop` nor
  `svc`); a cell passing it.
- `nodeW_nn`, `blkW_nn`, `at_nn`: a node's (a block node's) states are `NN`;
  `nodeW_nnSvc`, `at_nnSvc`: a system call's node, its call safe.
- `NodeZ Z exe n len`, `NNZ exe endPc Z`, `blkW_nnz`, `nodeW_nnz`, `at_nnz`:
  a fact `Z` of the state and the control at a node's pcs (the worker's store
  point on both sides, `WCompat.pass`; `NodeZ.top` the trivial one), carried
  with `NN`.
- `seg_ndNN`, `svc_ndNN`, `ownStlr_ndNN`, `rtld_ndNN`,
  `prologue_seg_ofNN`: the `W` leaves (`seg_ndW`, `svc_ndW`, `ownStlr_ndW`,
  `rtld_ndW`, `prologue_seg_ofW`) at `W := NNZ exe endPc Z`, as `SegTC`,
  each with its node's `NodeZ` (`hz`).
- `relStore_ndS`, `unpkSwp_ndS`, `texit_ndS`, `call_ndTS`, `fn_segTS`: the
  thread-row leaves of `Spike/Lib/A64WorkerRows.lean` over `SegTC S` (the
  same proofs; each node's states inside the fragment `S`, `hS`), with
  `relStore_ndNN`, `unpkSwp_ndNN`, `texit_ndNN` at `S := NNZ exe endPc Z`.
-/
import Spike.Lib.A64WorkerRows
import Spike.Lib.SegThrS

namespace Spike.Lib.A64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Spike.Lib.A64.Flow.Ret0 (StOk land_ldStep ownStlr_ndW)
open Spike.Lib.A64.Flow.Park (swpDir)

/-! ## Off the `nop`s -/

/-- **A safe system call**: at a system call of the kernel model
`Scc.Sem.A64.abi`, the call decoded is `exit`, or neither a `write` nor an
`exit_group` (`WCompat.sysOk`'s fact). -/
def SysSafe (s : State) : Prop :=
  Scc.Sem.A64.abi.atSys s = true → ∀ call, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s)
    (Scc.Sem.A64.abi.arg s) = some call →
    call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)

/-- **A state off the transfer sites**: at the executable `exe` (ending at
`endPc`), the cell at its pc not a `nop`, and a system call there safe
(`SysSafe`). -/
def NN (exe : _root_.Executable) (endPc : Int64) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧ Scc.Sem.A64.atNop s = false ∧ SysSafe s

/-- **A directive other than a `nop` or an `svc`.** -/
def notNop : Directive → Bool
  | .instr ⟨_, .NOP⟩ => false
  | .instr ⟨_, .SVC _⟩ => false
  | _ => true

theorem notNop_ne {d : Directive} (h : notNop d = true) : ∀ w, d ≠ .instr ⟨w, .NOP⟩ := by
  rintro w rfl
  simp [notNop] at h

theorem notNop_neSvc {d : Directive} (h : notNop d = true) : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩ := by
  rintro imm rfl
  simp [notNop] at h

/-- A cell other than a `nop` or an `svc` is off the transfer sites (and at
no system call). -/
theorem nn_of_cell {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive}
    (hc : CellAt s d 4) (he : s.exe = exe) (hn : s.endPc = endPc) (hd : notNop d = true) : NN exe endPc s := by
  refine ⟨he, hn, Scc.Sem.A64.atNop_false_of_cellAt hc (notNop_ne hd), fun ha => ?_⟩
  have : Scc.Sem.A64.atSvc s = false := Scc.Sem.A64.atSvc_false_of_cellAt hc (notNop_neSvc hd)
  exact absurd ha (by simp only [Scc.Sem.A64.abi] at ha ⊢; rw [this]; decide)

section Nodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node's states are off the transfer sites**: its code's first
directive is not a `nop`. -/
theorem nodeW_nn {n : ND} {d : Directive} {ds : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (d :: ds)) (hd : notNop d = true) :
    NodeW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n :=
  fun s _ ⟨he, hn, _, hpc, _⟩ =>
    ⟨nn_of_cell ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)) he hn hd, fun _ h => h⟩

/-- `nodeW_nn` as the state predicate of the node's fragment. -/
theorem at_nn {n : ND} {d : Directive} {ds : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (d :: ds)) (hd : notNop d = true) :
    ∀ s c, At exe endPc R F n s c → NN exe endPc s :=
  fun s c h => (nodeW_nn (R := R) (F := F) hcode hd s c h).1

/-- **A system call's node is off the transfer sites, its call safe**: the
call its invariant decodes is safe (`hsafe`). -/
theorem nodeW_nnSvc {n : ND}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hsafe : ∀ σ c, n.J σ c → ∀ call, svcCall σ.regs = some call →
      call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)) :
    NodeW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, _, hpc, σ, hA, _, hJ⟩ => by
    have hc : CellAt s svcDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
    refine ⟨⟨he, hn, Scc.Sem.A64.atNop_false_of_cellAt hc (by rintro w ⟨⟩), fun _ call hd => ?_⟩, fun _ h => h⟩
    exact hsafe σ c hJ call (by rw [svcCall, ← hA.regs]; exact hd)

/-- `nodeW_nnSvc` as the state predicate of the node's fragment. -/
theorem at_nnSvc {n : ND}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hsafe : ∀ σ c, n.J σ c → ∀ call, svcCall σ.regs = some call →
      call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)) :
    ∀ s c, At exe endPc R F n s c → NN exe endPc s :=
  fun s c h => (nodeW_nnSvc (R := R) (F := F) hcode hsafe s c h).1

/-- **A block node's states are off the transfer sites**: its block has no
`nop`. -/
theorem blkW_nn {n : ND} {blk : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hb : blk.all notNop = true) :
    BlkW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n blk := by
  intro s _ _ he hn _ _ _ _ _ k hk m _ _
  refine ⟨?_, fun _ h => h⟩
  have hd := List.all_eq_true.mp hb _ (List.getElem_mem hk)
  exact nn_of_cell ((hcode s he hn).cell (List.getElem?_eq_getElem hk) rfl rfl rfl) he hn hd

/-! ## A fact of the state and the control at each node -/

/-- **A fact `Z` of the state and the control at the node `n`'s first
`len` instructions**: at each of their pcs (`n.pc + 4k`, `k < len`), with
the control of the node's invariant. A segment's leaves carry it with `NN`
(`NNZ`); the worker's store point on both sides (`WCompat.pass`) is one. -/
def NodeZ (Z : Frag isaLSE2) (exe : _root_.Executable) (n : ND) (len : Nat) : Prop :=
  ∀ (s : State) (σ : AS) (c : Ctl) (k : Nat), k < len → s.exe = exe → s.st.2 = n.pc + Int64.ofNat (4 * k) →
    n.J σ c → Z s c

/-- Every node has the trivial fact. -/
theorem NodeZ.top {exe : _root_.Executable} {n : ND} {len : Nat} : NodeZ (fun _ _ => True) exe n len :=
  fun _ _ _ _ _ _ _ _ => trivial

/-- **Off the transfer sites, with `Z`.** -/
def NNZ (exe : _root_.Executable) (endPc : Int64) (Z : Frag isaLSE2) : Frag isaLSE2 :=
  fun s c => NN exe endPc s ∧ Z s c

variable {Z : Frag isaLSE2}

/-- A block node's states are `NNZ`: `NN` (`blkW_nn`) and `Z` at its pcs. -/
theorem blkW_nnz {n : ND} {blk : List Directive}
    (h : BlkW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n blk) (hz : NodeZ Z exe n blk.length) :
    BlkW (NNZ exe endPc Z) (fun _ _ => False) exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hD hJ k hk m hA' hF' =>
    ⟨⟨(h s σ c he hn hd hpc hA hD hJ k hk m hA' hF').1, hz _ σ c k hk he rfl hJ⟩, fun _ h => h⟩

/-- A node's states are `NNZ`: `NN` and `Z` at its pc. -/
theorem nodeW_nnz {n : ND} (h : NodeW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n)
    (hz : NodeZ Z exe n 1) : NodeW (NNZ exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c hs => by
    have h1 := (h s c hs).1
    obtain ⟨he, -, -, hpc, σ, -, -, hJ⟩ := hs
    exact ⟨⟨h1, hz s σ c 0 (by decide) he (by rw [hpc, Spike.Lib.A64.Flow.ofNat4_zero]) hJ⟩,
      fun _ h => h⟩

/-- `nodeW_nnz` as the fragment of the node's states. -/
theorem at_nnz {n : ND} (h : NodeW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n)
    (hz : NodeZ Z exe n 1) : ∀ s c, At exe endPc R F n s c → NNZ exe endPc Z s c :=
  fun s c hs => (nodeW_nnz h hz s c hs).1

/-! ## A fact at each node's states, with the abstract run -/

/-- **A fact `Z` at the states of the node `n` before each instruction of
its block `blk`**, each related to the abstract run so far and the memory
outside the region as at the node (`BlkW` with no outside moves). Unlike
`NodeZ`, which sees only the pc and the control, it knows the registers
and the frame's cells (`Abs`): the facts of the environment's places
(`Placed`) and of the addresses an instruction touches need them. A
single-instruction node takes `blk := [d]` (`NodeZA.toW`), a call node
`blk := []` (nothing to show). -/
abbrev NodeZA (Z : Frag isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (n : ND) (blk : List Directive) : Prop :=
  BlkW Z (fun _ _ => False) exe endPc R F n blk

/-- A fact of the pc and the control at a node's pcs is one at its states. -/
theorem NodeZ.toA {n : ND} {blk : List Directive} (h : NodeZ Z exe n blk.length) : NodeZA Z exe endPc R F n blk :=
  fun s σ c he _ _ _ _ _ hJ k hk _ _ _ => ⟨h _ σ c k hk he rfl hJ, fun _ h => h⟩

/-- `NodeZ.toA` at a length given as the block's. -/
theorem NodeZ.toAOf {n : ND} {len : Nat} {blk : List Directive} (h : NodeZ Z exe n len) (hl : len = blk.length) :
    NodeZA Z exe endPc R F n blk := by
  subst hl; exact h.toA

/-- A single-instruction node's fact is the node's obligation (`NodeW`). -/
theorem NodeZA.toW {n : ND} {d : Directive} (h : NodeZA Z exe endPc R F n [d]) :
    NodeW Z (fun _ _ => False) exe endPc R F n := fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => by
  have h0 := (h s σ c he hn hdc hpc hA hD hJ 0 (by simp) s.st.1 hA (DFrame.refl _ _)).1
  rw [Spike.Lib.A64.Flow.ofNat4_zero, ← hpc] at h0
  exact ⟨h0, fun _ h => h⟩

/-- Two facts at a node's states combine. -/
theorem NodeZA.and {Z' : Frag isaLSE2} {n : ND} {blk : List Directive} (h : NodeZA Z exe endPc R F n blk)
    (h' : NodeZA Z' exe endPc R F n blk) : NodeZA (fun s c => Z s c ∧ Z' s c) exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hD hJ k hk m hA' hD' =>
    ⟨⟨(h s σ c he hn hd hpc hA hD hJ k hk m hA' hD').1, (h' s σ c he hn hd hpc hA hD hJ k hk m hA' hD').1⟩,
      fun _ h => h⟩

/-- A weaker fact. -/
theorem NodeZA.mono {Z' : Frag isaLSE2} {n : ND} {blk : List Directive} (h : NodeZA Z exe endPc R F n blk)
    (hZ : ∀ s c, Z s c → Z' s c) : NodeZA Z' exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hD hJ k hk m hA' hD' =>
    ⟨hZ _ c (h s σ c he hn hd hpc hA hD hJ k hk m hA' hD').1, fun _ h => h⟩

/-- A block node's states are `NNZ`: `NN` (`blkW_nn`) and `Z` at its states. -/
theorem blkW_nnzA {n : ND} {blk : List Directive}
    (h : BlkW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n blk)
    (hz : NodeZA Z exe endPc R F n blk) : BlkW (NNZ exe endPc Z) (fun _ _ => False) exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hD hJ k hk m hA' hF' =>
    ⟨⟨(h s σ c he hn hd hpc hA hD hJ k hk m hA' hF').1, (hz s σ c he hn hd hpc hA hD hJ k hk m hA' hF').1⟩,
      fun _ h => h⟩

/-- A node's states are `NNZ`: `NN` and `Z` at its states. -/
theorem nodeW_nnzA {n : ND} (h : NodeW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) : NodeW (NNZ exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c hs => ⟨⟨(h s c hs).1, (hz s c hs).1⟩, fun _ h => h⟩

/-- `nodeW_nnzA` as the fragment of the node's states. -/
theorem at_nnzA {n : ND} (h : NodeW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) : ∀ s c, At exe endPc R F n s c → NNZ exe endPc Z s c :=
  fun s c hs => (nodeW_nnzA h hz s c hs).1

/-! ## The `W` leaves at `NNZ` -/

/-- **A block node off the transfer sites** (`seg_ndW` at `NNZ`), `Z` at
its pcs (`hz`). -/
theorem seg_ndNN {n : ND} {lo hi : Int} {blk : List Directive} (hne : blk ≠ [])
    (hok : okBlk lo hi n.o blk = true) (hb : blk.all notNop = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hedge : ∀ σ c, n.J σ c →
      ∃ c', LocalRun p c c' ∧ Lands N E (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩) c')
    (hz : NodeZ Z exe n blk.length) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (seg_ndW hne hok hF hR hal hlo hhi hcode (blkW_nnz (blkW_nn hcode hb) hz) hedge)

/-- **A system call's node off the transfer sites** (`svc_ndW` at `NN`),
its call safe (`hsafe`). -/
theorem svc_ndNN {n : ND} (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hedge : ∀ σ c, n.J σ c → ∃ call, svcCall σ.regs = some call ∧ ∀ v ∈ Scc.Sem.Kernel.results call,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill .X0, svcStep v σ⟩ c')
    (hok : ∀ s c σ call, At exe endPc R F n s c → n.J σ c → svcCall σ.regs = some call → SysOk p ms s c call)
    (hsafe : ∀ σ c, n.J σ c → ∀ call, svcCall σ.regs = some call →
      call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v))
    (hz : NodeZ Z exe n 1) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (svc_ndW hK hF hcode (nodeW_nnz (nodeW_nnSvc hcode hsafe) hz) hedge hok)

/-- **An own word's release off the transfer sites** (`ownStlr_ndW` at
`NN`). -/
theorem ownStlr_ndNN {n : ND} {t b : XReg} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ StOk ms F exe endPc A (σ.regs.getRegOrZr (.low (.reg t) .W64)) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c) (hz : NodeZ Z exe n 1) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (ownStlr_ndW hcode (nodeW_nnz (nodeW_nn hcode rfl) hz) hedge)

/-- **A runtime word's load off the transfer sites** (`rtld_ndW` at `NN`). -/
theorem rtld_ndNN {n : ND} {t b : XReg} {i : Int64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldrDir t b i])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (rAddr σ.regs b i).toNat ∧ ms.mp ⟨rAddr σ.regs b i, 8⟩ false ∧
      Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ ∀ v : Val, ms.G ⟨rAddr σ.regs b i, 8⟩ v →
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t (v.setWidth 64) σ⟩ c') (hz : NodeZ Z exe n 1) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (rtld_ndW hF hcode (nodeW_nnz (nodeW_nn hcode rfl) hz) hedge)

/-! ## The `W` leaves at `NNZ`, `Z` at the node's states -/

/-- **`seg_ndNN` with `Z` at the block's states** (`NodeZA`). -/
theorem seg_ndNNA {n : ND} {lo hi : Int} {blk : List Directive} (hne : blk ≠ [])
    (hok : okBlk lo hi n.o blk = true) (hb : blk.all notNop = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hedge : ∀ σ c, n.J σ c →
      ∃ c', LocalRun p c c' ∧ Lands N E (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩) c')
    (hz : NodeZA Z exe endPc R F n blk) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (seg_ndW hne hok hF hR hal hlo hhi hcode (blkW_nnzA (blkW_nn hcode hb) hz) hedge)

/-- **`svc_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem svc_ndNNA {n : ND} (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hedge : ∀ σ c, n.J σ c → ∃ call, svcCall σ.regs = some call ∧ ∀ v ∈ Scc.Sem.Kernel.results call,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill .X0, svcStep v σ⟩ c')
    (hok : ∀ s c σ call, At exe endPc R F n s c → n.J σ c → svcCall σ.regs = some call → SysOk p ms s c call)
    (hsafe : ∀ σ c, n.J σ c → ∀ call, svcCall σ.regs = some call →
      call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v))
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (svc_ndW hK hF hcode (nodeW_nnzA (nodeW_nnSvc hcode hsafe) hz) hedge hok)

/-- **`ownStlr_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem ownStlr_ndNNA {n : ND} {t b : XReg} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ StOk ms F exe endPc A (σ.regs.getRegOrZr (.low (.reg t) .W64)) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c) (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (ownStlr_ndW hcode (nodeW_nnzA (nodeW_nn hcode rfl) hz) hedge)

/-- **`rtld_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem rtld_ndNNA {n : ND} {t b : XReg} {i : Int64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldrDir t b i])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (rAddr σ.regs b i).toNat ∧ ms.mp ⟨rAddr σ.regs b i, 8⟩ false ∧
      Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ ∀ v : Val, ms.G ⟨rAddr σ.regs b i, 8⟩ v →
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t (v.setWidth 64) σ⟩ c')
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (rtld_ndW hF hcode (nodeW_nnzA (nodeW_nn hcode rfl) hz) hedge)

/-! ## The thread-row leaves inside `S` -/

variable {S : Frag isaLSE2}

/-- **A whole function inside `S`**: `fn_segT` over `SegTC`. -/
theorem fn_segTS (h : ∀ i, SegTC S p lbl ms (At exe endPc R F (N i)) (Next exe endPc R F N E)) (i0 : ι) :
    SegTC S p lbl ms (At exe endPc R F (N i0)) (fun s c => ∃ x, At exe endPc R F (E x) s c) :=
  (SegTC.cfg (fun i => At exe endPc R F (N i)) h).mono_pre fun _ _ h => ⟨i0, h⟩

/-- **`relStore_nd` inside `S`**: the node's states in `S` (`hS`). -/
theorem relStore_ndS {n : ND} {t b : XReg} {A : BitVec 64} (hS : ∀ s c, At exe endPc R F n s c → S s c)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩])
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧
      ∃ x a bb e ty tb w wb, c.term = .let_ x (.store true a bb none) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ (∃ sa, w.val = .loc sa 0) ∧
        TermRun.evalAt c.env bb = some (tb, [wb]) ∧
        ValRep lbl wb.val (σ.regs.getRegOrZr (.low (.reg t) .W64)).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ ⟨e, (x, .unit, []) :: c.env, none⟩) :
    SegTC S p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegTC.step hS fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => .outL (.out ?_)
  have hc : Lower.A64.CellAt s (.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩) 4 :=
    (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, x, a, bb, e, ty, tb, w, wb, ht, hev, hv, htag, hevb, hvb, hL⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := Lower.A64.exec_stlr_agrees hc (by rw [hb']; exact hdm _ hD)
    (by rw [hb']; exact agrees_of_decls hdc _ _)
  rw [hb'] at hex
  refine .store .rel A _ _ x a bb e ty tb w wb hex ht hev hv hevb
    (by rw [Spike.Lib.A64.toNat_setWidth128, hA.regs]; exact hvb) ?_ htag
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- **`unpkSwp_nd` inside `S`**: the node's states in `S` (`hS`). -/
theorem unpkSwp_ndS {n : ND} {k : RmwKind} {rs rt b : XReg} {A B : BitVec 64} (hF : FStable R F)
    (hS : ∀ s c, At exe endPc R F n s c → S s c)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [swpDir k rs rt b])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ σ.regs.getRegOrZr (.low (.reg rs) .W64) = 1#64 ∧
      StOk ms F exe endPc A 1#64 ∧ A = B + 16#64 ∧
      ∃ x a e ty jw, c.term = .let_ x (.ext .unpark a) e ∧ c.hold = none ∧
        TermRun.evalAt c.env a = some (ty, [jw]) ∧ ValRep lbl jw.val B.toNat ∧
        ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩
          ⟨e, (x, ExtName.unpark.sig.2, []) :: c.env, none⟩) :
    SegTC S p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegTC.step hS fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : Lower.A64.CellAt s (swpDir k rs rt b) 4 :=
    (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, h1, hS, hAB, x, a, e, ty, jw, ht, hh, hev, hv, hL⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := Lower.A64.exec_swp hc (by rw [hb']; exact hS.unmapped _ hD)
  rw [hb', Lower.A64.access_agrees (agrees_of_decls hdc _ _)] at hex
  have hz : (RegOrZr.low (.reg rt) .W64).isZr = false := rfl
  rw [hz] at hex
  refine .unpk k A B _ _ x a e ty jw hex hS.rt hS.mp (fun _ => by rw [hA.regs, h1, one_setWidth]) ht hh hev hv
    hAB fun old _ _ => ⟨?_, land_ldStep hF he hn hdc hpc hA hD (hL _)⟩
  have := hS.G
  rwa [one_setWidth] at this

/-- **`texit_nd` inside `S`**: the node's states in `S` (`hS`). -/
theorem texit_ndS {n : ND} {Q : Frag isaLSE2} (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : ∀ s c, At exe endPc R F n s c → S s c)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hx : ∀ σ c, n.J σ c → σ.regs.X8.toNat = 93 ∧ ∃ a, c.term = .ret a) :
    SegTC S p lbl ms (At exe endPc R F n) Q := by
  refine SegTC.step hS fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : Lower.A64.CellAt s svcDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨h8, a, ht⟩ := hx σ c hJ
  have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.a64 (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some .exit := by
    rw [← svcCall_exit h8, svcCall, ← hA.regs]; rfl
  exact .texit _ a hK (Scc.Sem.A64.atSvc_of_cellAt hc) hd ht

/-- **A call node inside `S`** (`call_ndT` over `SegTS`): the callee's
specification inside `S` is a given node of the caller. The call node's
states are the callee's entry states, so the call needs no `hS`. The proof
is `call_ndT`'s. -/
theorem call_ndTS {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegTC S p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter nC.o.sp σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegTC S p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  -- the callee's region and its ghost-indexed frame condition
  let kc := nC.o.sp
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkc (by omega)
  have hb' := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have hal' : R'.base.toNat % 16 = 0 := by
    have : ((R'.base.toNat : Int)) % 16 = 0 := by rw [hb']; omega
    omega
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkc (by omega) hF
  -- the ghost: the machine data and abstract state at the call, the caller's control, the callee's
  -- parameters; the facts about it ride in the frame condition (constant, so stable)
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ DFrame R' G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kc G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, hm.2.1.trans hd, hm.2.2⟩
  refine SegTC.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c)
    (SegTC.exists_pre fun G => ?_) ?_
  · -- the callee's segment, its exits landing at the caller's nodes
    refine (hcallee R' (F' G) hR' hal' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun _ h => h.1) G.2.2.2).mono_post ?_
    rintro s c ⟨x, he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩
    obtain ⟨mC, σC, cC, g⟩ := G
    simp only at hDF hAC hJC hJE hJx hAx hpc
    have hAR : Abs R ⟨kc + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kc σC σx) := by
      refine ⟨hAx.regs, hAx.status, ?_, fun k hk => ?_⟩
      · intro r k' hr
        rcases r with y | _
        · cases hr
        · simp only [SO.get, Option.some.injEq] at hr
          subst hr
          have := hAx.so .SP _ rfl
          simp only [leave] at this ⊢
          rw [this, Region.callee_addr]
      · by_cases hin : R'.Off (k - kc)
        · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
          refine ⟨j, ?_, ?_⟩
          · rw [Region.callee_addr, show kc + (k - kc) = k by omega] at hj; exact hj
          · simp only [leave]; rw [ite_eq_left hin]; exact hv
        · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
          refine ⟨j, ?_, ?_⟩
          · rw [hDF _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc (by omega) hl8 hh8 hk hin)]
            exact hj
          · simp only [leave]; rw [ite_eq_right hin]; exact hv
    have hL := hret g x σC cC σx c (leave R' kc σC σx) hJC hJE hJx rfl rfl
      (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
    have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
    rw [hs]
    rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
    · exact .inl ⟨j, hj.at he hn hdc hAR hD⟩
    · exact .inr ⟨y, hy.at he hn hdc hAR hD⟩
  · -- the caller's state at the call, seen from the callee
    rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), he, hn, hdc, by rw [hpc, hgpc], enter kc σC, ?_,
      ⟨hD, DFrame.refl _ _, hA, hJ, hgJ⟩, hgJ⟩
    rw [hNe]
    refine ⟨hA.regs, hA.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      rcases r with y | _
      · cases hr
      · simp only [SO.get, Option.some.injEq] at hr
        subst hr
        have := hA.so .SP _ rfl
        simp only [enter] at this ⊢
        rw [this, Region.callee_addr, Int.add_zero]
    · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo (by omega) (by omega) hk)
      exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

/-- **The callee's region and frame condition at a call** from the node
`nC` (region `R`, frame condition `F`), the callee's frame between `lo'`
and `hi'`: the region is well formed and covers the frame, `F'` is stable,
and it sees the caller (`sees`): every memory of `F'` is one of `F`, and
outside `R'` agrees with a memory at the call, related to an abstract state
and control of `nC` (`Abs`, `nC.J`). -/
structure CallerF (R : Region) (F : MachineData → Prop) (nC : ND) (lo' hi' : Int) (R' : Region)
    (F' : MachineData → Prop) : Prop where
  ok : R'.OK
  al : R'.base.toNat % 16 = 0
  lo : R'.lo ≤ lo'
  hi : hi' ≤ R'.hi
  stab : FStable R' F'
  sees : ∀ m, F' m → F m ∧ ∃ m0 σ0 c0, DFrame R' m0 m ∧ Abs R nC.o m0 σ0 ∧ nC.J σ0 c0

/-- **`call_ndTS` with the caller seen by the callee**: the callee's
segment is needed only at frame conditions that know the caller's frame
(`CallerF`), so facts of the callee's states may read the caller's cells.
The proof is `call_ndTS`'s. -/
theorem call_ndTSA {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), CallerF R F nC lo' hi' R' F' → ∀ g,
        SegTC S p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter nC.o.sp σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegTC S p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  -- the callee's region and its ghost-indexed frame condition
  let kc := nC.o.sp
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkc (by omega)
  have hb' := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have hal' : R'.base.toNat % 16 = 0 := by
    have : ((R'.base.toNat : Int)) % 16 = 0 := by rw [hb']; omega
    omega
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkc (by omega) hF
  -- the ghost: the machine data and abstract state at the call, the caller's control, the callee's
  -- parameters; the facts about it ride in the frame condition (constant, so stable)
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ DFrame R' G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kc G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, hm.2.1.trans hd, hm.2.2⟩
  refine SegTC.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c)
    (SegTC.exists_pre fun G => ?_) ?_
  · -- the callee's segment, its exits landing at the caller's nodes
    refine (hcallee R' (F' G) ⟨hR', hal', Int.le_refl _, Int.le_refl _, hF' G,
      fun _ h => ⟨h.1, G.1, G.2.1, G.2.2.1, h.2.1, h.2.2.1, h.2.2.2.1⟩⟩ G.2.2.2).mono_post ?_
    rintro s c ⟨x, he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩
    obtain ⟨mC, σC, cC, g⟩ := G
    simp only at hDF hAC hJC hJE hJx hAx hpc
    have hAR : Abs R ⟨kc + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kc σC σx) := by
      refine ⟨hAx.regs, hAx.status, ?_, fun k hk => ?_⟩
      · intro r k' hr
        rcases r with y | _
        · cases hr
        · simp only [SO.get, Option.some.injEq] at hr
          subst hr
          have := hAx.so .SP _ rfl
          simp only [leave] at this ⊢
          rw [this, Region.callee_addr]
      · by_cases hin : R'.Off (k - kc)
        · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
          refine ⟨j, ?_, ?_⟩
          · rw [Region.callee_addr, show kc + (k - kc) = k by omega] at hj; exact hj
          · simp only [leave]; rw [ite_eq_left hin]; exact hv
        · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
          refine ⟨j, ?_, ?_⟩
          · rw [hDF _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc (by omega) hl8 hh8 hk hin)]
            exact hj
          · simp only [leave]; rw [ite_eq_right hin]; exact hv
    have hL := hret g x σC cC σx c (leave R' kc σC σx) hJC hJE hJx rfl rfl
      (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
    have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
    rw [hs]
    rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
    · exact .inl ⟨j, hj.at he hn hdc hAR hD⟩
    · exact .inr ⟨y, hy.at he hn hdc hAR hD⟩
  · -- the caller's state at the call, seen from the callee
    rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), he, hn, hdc, by rw [hpc, hgpc], enter kc σC, ?_,
      ⟨hD, DFrame.refl _ _, hA, hJ, hgJ⟩, hgJ⟩
    rw [hNe]
    refine ⟨hA.regs, hA.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      rcases r with y | _
      · cases hr
      · simp only [SO.get, Option.some.injEq] at hr
        subst hr
        have := hA.so .SP _ rfl
        simp only [enter] at this ⊢
        rw [this, Region.callee_addr, Int.add_zero]
    · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo (by omega) (by omega) hk)
      exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

/-! ## The thread-row leaves at `NN` -/

/-- **`relStore_nd` off the transfer sites.** -/
theorem relStore_ndNN {n : ND} {t b : XReg} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩])
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧
      ∃ x a bb e ty tb w wb, c.term = .let_ x (.store true a bb none) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ (∃ sa, w.val = .loc sa 0) ∧
        TermRun.evalAt c.env bb = some (tb, [wb]) ∧
        ValRep lbl wb.val (σ.regs.getRegOrZr (.low (.reg t) .W64)).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ ⟨e, (x, .unit, []) :: c.env, none⟩) (hz : NodeZ Z exe n 1) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  relStore_ndS (at_nnz (nodeW_nn hcode rfl) hz) hcode hdm hedge

/-- **`unpkSwp_nd` off the transfer sites.** -/
theorem unpkSwp_ndNN {n : ND} {k : RmwKind} {rs rt b : XReg} {A B : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [swpDir k rs rt b])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ σ.regs.getRegOrZr (.low (.reg rs) .W64) = 1#64 ∧
      StOk ms F exe endPc A 1#64 ∧ A = B + 16#64 ∧
      ∃ x a e ty jw, c.term = .let_ x (.ext .unpark a) e ∧ c.hold = none ∧
        TermRun.evalAt c.env a = some (ty, [jw]) ∧ ValRep lbl jw.val B.toNat ∧
        ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩
          ⟨e, (x, ExtName.unpark.sig.2, []) :: c.env, none⟩) (hz : NodeZ Z exe n 1) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  unpkSwp_ndS hF (at_nnz (nodeW_nn hcode rfl) hz) hcode hedge

/-- **`texit_nd` off the transfer sites.** -/
theorem texit_ndNN {n : ND} {Q : Frag isaLSE2} (hK : ms.K = some Scc.Sem.A64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hx : ∀ σ c, n.J σ c → σ.regs.X8.toNat = 93 ∧ ∃ a, c.term = .ret a) (hz : NodeZ Z exe n 1) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) Q :=
  texit_ndS hK (at_nnz (nodeW_nnSvc hcode fun σ c hJ call hcall => by
    rw [svcCall_exit (hx σ c hJ).1] at hcall
    exact .inl (Option.some.inj hcall).symm) hz) hcode hx

/-- **`relStore_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem relStore_ndNNA {n : ND} {t b : XReg} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩])
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧
      ∃ x a bb e ty tb w wb, c.term = .let_ x (.store true a bb none) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ (∃ sa, w.val = .loc sa 0) ∧
        TermRun.evalAt c.env bb = some (tb, [wb]) ∧
        ValRep lbl wb.val (σ.regs.getRegOrZr (.low (.reg t) .W64)).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ ⟨e, (x, .unit, []) :: c.env, none⟩)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  relStore_ndS (at_nnzA (nodeW_nn hcode rfl) hz) hcode hdm hedge

/-- **`unpkSwp_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem unpkSwp_ndNNA {n : ND} {k : RmwKind} {rs rt b : XReg} {A B : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [swpDir k rs rt b])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ σ.regs.getRegOrZr (.low (.reg rs) .W64) = 1#64 ∧
      StOk ms F exe endPc A 1#64 ∧ A = B + 16#64 ∧
      ∃ x a e ty jw, c.term = .let_ x (.ext .unpark a) e ∧ c.hold = none ∧
        TermRun.evalAt c.env a = some (ty, [jw]) ∧ ValRep lbl jw.val B.toNat ∧
        ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩
          ⟨e, (x, ExtName.unpark.sig.2, []) :: c.env, none⟩)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  unpkSwp_ndS hF (at_nnzA (nodeW_nn hcode rfl) hz) hcode hedge

/-- **`texit_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem texit_ndNNA {n : ND} {Q : Frag isaLSE2} (hK : ms.K = some Scc.Sem.A64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hx : ∀ σ c, n.J σ c → σ.regs.X8.toNat = 93 ∧ ∃ a, c.term = .ret a)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) Q :=
  texit_ndS hK (at_nnzA (nodeW_nnSvc hcode fun σ c hJ call hcall => by
    rw [svcCall_exit (hx σ c hJ).1] at hcall
    exact .inl (Option.some.inj hcall).symm) hz) hcode hx

end Nodes

/-! ## The prologue at `NN` -/

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- A frame's set-up has no `nop`. -/
theorem frameSet_notNop (Z : Int64) (ps : List (XReg × Int64)) : (frameSet Z ps).all notNop = true := by
  simp [frameSet, frSetup, spStr, notNop, List.all_map]

/-- **The prologue off the transfer sites**: `prologue_seg_ofW` at `NNZ`,
`ProW` from the prologue's code (none of its blocks a `nop`) and `Zf` at its
`9 + ps.length` pcs with the entry's control (`hz`; every node of the
prologue keeps the entry's control). -/
theorem prologue_seg_ofNN {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {fn sc entry : Label}
    {Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} (hin : prologueIn prog fn sc entry Z lim L ps = true)
    {J : AS → Ctl → Prop} {nb : ND} (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt) (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, Spike.Lib.offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true)
    (hpc : nb.pc = (_root_.Executable.labels exe).label entry)
    (ho : SO.le nb.o (oFr Z) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs lim).toNat ∧ ms.mp ⟨tcbA σ.regs lim, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs lim) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs lim, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs Z (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs Z σ.regs }).regs →
          σ'.slot = stSlots (-Z.toInt) σ'.regs ps (frSlot σ) → nb.J σ' c)
    {Zf : Frag isaLSE2} (hz : ∀ (s : State) σ c (k : Nat), k < 9 + ps.length → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat (4 * k) → J σ c → Zf s c) :
    SegTC (NNZ exe endPc Zf) p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) := by
  refine SegW.toTC (prologue_seg_ofW hp hend hin h16 hZ hF hR hal hlo hhi hps hpc ho ?_ hedge)
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, -⟩ := hin
  have e0 := label_labelGap hp g0
  rw [ofNat4_zero] at e0
  have hfl : (frameSet Z ps).length = 4 + ps.length := by simp [frameSet, frSetup]; omega
  refine ⟨blkW_nnz (blkW_nn (code_of hp hend b0 ?_) (by simp [chkHead, notNop])) ?_,
    nodeW_nnz (nodeW_nn (code_of hp hend b1 ?_) rfl) ?_,
    blkW_nnz (blkW_nn (code_of hp hend b2 ?_) (by simp [chkBr, notNop])) ?_,
    blkW_nnz (blkW_nn (code_of hp hend b3 ?_) (frameSet_notNop Z ps)) ?_⟩
  · rw [e0, ofNat4_zero]
  · intro s σ c k hk he hpc hJ
    exact hz s σ c k (by simp [chkHead] at hk; omega) he hpc hJ
  · rw [e0]; simp only [proN1, ofNat4_succ, ofNat4_zero]
  · rintro s σ1 c k hk he hpc ⟨σ, hJ, -⟩
    refine hz s σ c (2 + k) (by omega) he ?_ hJ
    rw [hpc, ofNat4_add]; simp only [proN1, ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [proN2, ofNat4_succ, ofNat4_zero]
  · rintro s σ2 c k hk he hpc ⟨σ, v, hJ, -⟩
    refine hz s σ c (3 + k) (by simp [chkBr] at hk; omega) he ?_ hJ
    rw [hpc, ofNat4_add]; simp only [proN2, ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [proN3, ofNat4_succ, ofNat4_zero]
  · rintro s σ3 c k hk he hpc ⟨σ, v, hJ, -⟩
    refine hz s σ c (5 + k) (by rw [hfl] at hk; omega) he ?_ hJ
    rw [hpc, ofNat4_add]; simp only [proN3, ofNat4_succ, ofNat4_zero]

omit [Kraken.Executable.ValidLayout exe] in
/-- **A fact of the pc and the control at the prologue's pcs is one at its
states** (`ProW`): `Zf` at the `9 + ps.length` pcs from `pc0` with the
entry's control (every node of the prologue keeps it). -/
theorem ProW.ofPcs {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} {J : AS → Ctl → Prop}
    {Zf : Frag isaLSE2} (hz : ∀ (s : State) σ c (k : Nat), k < 9 + ps.length → s.exe = exe →
      s.st.2 = pc0 + Int64.ofNat (4 * k) → J σ c → Zf s c) :
    ProW Zf (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps J := by
  have hfl : (frameSet Z ps).length = 4 + ps.length := by simp [frameSet, frSetup]; omega
  refine ⟨NodeZ.toA ?_, NodeZA.toW (d := ldrDir .X10 .X10 lim) (NodeZ.toA ?_), NodeZ.toA ?_, NodeZ.toA ?_⟩
  · intro s σ c k hk he hpc hJ
    exact hz s σ c k (by simp [chkHead] at hk; omega) he hpc hJ
  · rintro s σ1 c k hk he hpc ⟨σ, hJ, -⟩
    refine hz s σ c (2 + k) (by simp at hk; omega) he ?_ hJ
    rw [hpc, ofNat4_add]; simp only [proN1, ofNat4_succ, ofNat4_zero]
  · rintro s σ2 c k hk he hpc ⟨σ, v, hJ, -⟩
    refine hz s σ c (3 + k) (by simp [chkBr] at hk; omega) he ?_ hJ
    rw [hpc, ofNat4_add]; simp only [proN2, ofNat4_succ, ofNat4_zero]
  · rintro s σ3 c k hk he hpc ⟨σ, v, hJ, -⟩
    refine hz s σ c (5 + k) (by rw [hfl] at hk; omega) he ?_ hJ
    rw [hpc, ofNat4_add]; simp only [proN3, ofNat4_succ, ofNat4_zero]

/-- **`prologue_seg_ofNN` with `Zf` at the prologue's states** (`ProW`). -/
theorem prologue_seg_ofNNA {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {fn sc entry : Label}
    {Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} (hin : prologueIn prog fn sc entry Z lim L ps = true)
    {J : AS → Ctl → Prop} {nb : ND} (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt) (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, Spike.Lib.offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true)
    (hpc : nb.pc = (_root_.Executable.labels exe).label entry)
    (ho : SO.le nb.o (oFr Z) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs lim).toNat ∧ ms.mp ⟨tcbA σ.regs lim, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs lim) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs lim, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs Z (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs Z σ.regs }).regs →
          σ'.slot = stSlots (-Z.toInt) σ'.regs ps (frSlot σ) → nb.J σ' c)
    {Zf : Frag isaLSE2}
    (hz : ProW Zf (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label fn) Z lim L ps J) :
    SegTC (NNZ exe endPc Zf) p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) := by
  refine SegW.toTC (prologue_seg_ofW hp hend hin h16 hZ hF hR hal hlo hhi hps hpc ho ?_ hedge)
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, -⟩ := hin
  have e0 := label_labelGap hp g0
  rw [ofNat4_zero] at e0
  refine ⟨blkW_nnzA (blkW_nn (code_of hp hend b0 ?_) (by simp [chkHead, notNop])) hz.w0,
    nodeW_nnzA (nodeW_nn (code_of hp hend b1 ?_) rfl) hz.w1,
    blkW_nnzA (blkW_nn (code_of hp hend b2 ?_) (by simp [chkBr, notNop])) hz.w2,
    blkW_nnzA (blkW_nn (code_of hp hend b3 ?_) (frameSet_notNop Z ps)) hz.w3⟩
  · rw [e0, ofNat4_zero]
  · rw [e0]; simp only [proN1, ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [proN2, ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [proN3, ofNat4_succ, ofNat4_zero]

end Pro

end Spike.Lib.A64.Flow.Worker
