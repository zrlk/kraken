/-
**The worker's states are off the transfer sites on x86-64** (the x64 twin
of `Spike/Lib/A64WakeNN.lean`, `WCompat.noSite`): the leaves of the
worker's segments over `SegTC (NNZ exe endPc Z)`, every state of the
hidden invariant at a cell other than a `nop`.

The kernel's transfer sites are `nop`s; a state at a cell that is not a
`nop` has `Scc.Sem.X64.atNop s = false`. Each node of the worker's
functions proves it of its own states from its code (`CodeAt.cell`,
`Scc.Sem.X64.atNop_false_of_cellAt`) and a decided check that its block has
no `nop` (`notNop`), so the fact rides along the segment through `SegTC`'s
combinators (`Spike/Lib/SegThrS.lean`).

- `NN exe endPc s`: the executable, its end, no `nop` at the pc, and a
  system call there safe (`SysSafe`: `exit`, or neither `write` nor
  `exit_group`; `WCompat.sysOk`).
- `notNop`, `nn_of_cell`: the check on a directive (neither `nop` nor
  `syscall`); a cell passing it.
- `nodeW_nn`, `blkW_nn`, `at_nn`: a node's (a block node's) states are `NN`;
  `nodeW_nnSys`, `at_nnSys`: a system call's node, its call safe.
- `NodeZ Z exe n blk`, `NNZ exe endPc Z`, `blkW_nnz`, `nodeW_nnz`, `at_nnz`:
  a fact `Z` of the state and the control at the pcs of a node's block,
  carried with `NN`; `NodeZA` (`BlkW`), the fact at the node's states, with
  its combinators.
- `seg_ndNN`, `syscall_ndNN`, `rtst_ndNN`, `ownFsld_ndNN` and their `…NNA`
  forms: the `W` leaves (`seg_ndW`, `syscall_ndW`, `rtst_ndW`,
  `ownFsld_ndW`) at `W := NNZ exe endPc Z`, as `SegTC`.
- `fn_segTS`, `relStore_ndS`, `unpkXchg_ndS`, `texit_ndS`, `call_ndTS`,
  `call_ndTSA`: the thread-row leaves of `Spike/Lib/X64WorkerRows.lean` over
  `SegTC S` (the same proofs; each node's states inside the fragment `S`,
  `hS`), with `relStore_ndNN`, `unpkXchg_ndNN`, `texit_ndNN` (and `…NNA`) at
  `S := NNZ exe endPc Z`.
- `prologue_seg_ofNN`, `prologue_seg_ofNNA`: the stack-checked prologue at
  `NNZ`.

**Unlike AArch64** (forced by the x64 shape):

- the cells are sized: `NodeZ` is indexed by the node's block (its pcs are
  `n.pc + cellOff blk k`), not a count of 4-byte instructions; a
  single-instruction node's block is `[(d, z)]`.
- the system call is `syscall` (`syscallCall`, `syscall_ndW`), and
  `notNop` also rules it out of the blocks (as A64 `svc`).
- the own word's load through the thread pointer (`ownFsld_ndW`, `movq
  %fs:k, %d`) and the runtime store (`rtst_ndW`) are the x64 leaves of
  A64's `rtld_ndNN`/`ownStlr_ndNN`.
- the prologue's `hz` is over byte offsets `k ≤ pz` from the function's
  label (`pz` its length in bytes).
- `call_ndTS` is `call_ndT`'s (`e0`, `hi'`, the vector registers), no
  alignment premise.
-/
import Spike.Lib.X64WorkerRows
import Spike.Lib.X64CodeSegs
import Spike.Lib.SegThrS

namespace Spike.Lib.X64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Sem (ValRep)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk)

set_option linter.unusedSimpArgs false

/-! ## Off the `nop`s -/

/-- **A safe system call**: at a system call of the kernel model
`Scc.Sem.X64.abi`, the call decoded is `exit`, or neither a `write` nor an
`exit_group` (`WCompat.sysOk`'s fact). -/
def SysSafe (s : State) : Prop :=
  Scc.Sem.X64.abi.atSys s = true → ∀ call, Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s)
    (Scc.Sem.X64.abi.arg s) = some call →
    call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)

/-- **A state off the transfer sites**: at the executable `exe` (ending at
`endPc`), the cell at its pc not a `nop`, and a system call there safe
(`SysSafe`). -/
def NN (exe : _root_.Executable) (endPc : Int64) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧ Scc.Sem.X64.atNop s = false ∧ SysSafe s

/-- **A directive other than a `nop` or a `syscall`.** -/
def notNop : Directive → Bool
  | .instr (.regular _ _ (.nop _)) => false
  | .instr (.regular _ _ .syscall) => false
  | _ => true

theorem notNop_ne {d : Directive} (h : notNop d = true) : ∀ w w' n, d ≠ .instr (.regular w w' (.nop n)) := by
  rintro w w' n rfl
  simp [notNop] at h

theorem notNop_neSys {d : Directive} (h : notNop d = true) : ∀ w w', d ≠ .instr (.regular w w' .syscall) := by
  rintro w w' rfl
  simp [notNop] at h

/-- A cell other than a `nop` or a `syscall` is off the transfer sites (and
at no system call). -/
theorem nn_of_cell {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive} {z : Nat}
    (hc : CellAt s d z) (he : s.exe = exe) (hn : s.endPc = endPc) (hd : notNop d = true) : NN exe endPc s := by
  refine ⟨he, hn, Scc.Sem.X64.atNop_false_of_cellAt hc (notNop_ne hd), fun ha => ?_⟩
  have : Scc.Sem.X64.atSyscall s = false := Scc.Sem.X64.atSyscall_false_of_cellAt hc (notNop_neSys hd)
  exact absurd ha (by simp only [Scc.Sem.X64.abi] at ha ⊢; rw [this]; decide)

section Nodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node's states are off the transfer sites**: its code's first
directive is not a `nop`. -/
theorem nodeW_nn {n : ND} {d : Directive} {z : Nat} {ds : List (Directive × Nat)}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc ((d, z) :: ds)) (hd : notNop d = true) :
    NodeW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n :=
  fun s _ ⟨he, hn, _, hpc, _⟩ => ⟨nn_of_cell ((hcode s he hn).cell0 rfl rfl hpc) he hn hd, fun _ h => h⟩

/-- `nodeW_nn` as the state predicate of the node's fragment. -/
theorem at_nn {n : ND} {d : Directive} {z : Nat} {ds : List (Directive × Nat)}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc ((d, z) :: ds)) (hd : notNop d = true) :
    ∀ s c, At exe endPc R F n s c → NN exe endPc s :=
  fun s c h => (nodeW_nn (R := R) (F := F) hcode hd s c h).1

/-- **A system call's node is off the transfer sites, its call safe**: the
call its invariant decodes is safe (`hsafe`). -/
theorem nodeW_nnSys {n : ND} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hsafe : ∀ σ c, n.J σ c → ∀ call, syscallCall σ.regs = some call →
      call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)) :
    NodeW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, _, hpc, σ, hA, _, hJ⟩ => by
    have hc : CellAt s (op64 .syscall) z := (hcode s he hn).cell0 rfl rfl hpc
    refine ⟨⟨he, hn, Scc.Sem.X64.atNop_false_of_cellAt hc (by intro w w' n h; cases h), fun _ call hd => ?_⟩,
      fun _ h => h⟩
    exact hsafe σ c hJ call (by rw [syscallCall, ← hA.regs]; exact hd)

/-- `nodeW_nnSys` as the state predicate of the node's fragment. -/
theorem at_nnSys {n : ND} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hsafe : ∀ σ c, n.J σ c → ∀ call, syscallCall σ.regs = some call →
      call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)) :
    ∀ s c, At exe endPc R F n s c → NN exe endPc s :=
  fun s c h => (nodeW_nnSys (R := R) (F := F) hcode hsafe s c h).1

/-- **A block node's states are off the transfer sites**: its block has no
`nop`. -/
theorem blkW_nn {n : ND} {blk : List (Directive × Nat)}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hb : blk.all (fun c => notNop c.1) = true) :
    BlkW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n blk := by
  intro s _ _ he hn _ _ _ _ _ k hk m _ _
  refine ⟨?_, fun _ h => h⟩
  have hd := List.all_eq_true.mp hb _ (List.getElem_mem hk)
  exact nn_of_cell ((hcode s he hn).cell (List.getElem?_eq_getElem hk) rfl rfl rfl) he hn hd

/-! ## A fact of the state and the control at each node -/

/-- **A fact `Z` of the state and the control at the pcs of the node `n`'s
block `blk`**: at each of its cells' pcs (`n.pc + cellOff blk k`, `k <
blk.length`), with the control of the node's invariant. A segment's leaves
carry it with `NN` (`NNZ`). -/
def NodeZ (Z : Frag isa) (exe : _root_.Executable) (n : ND) (blk : List (Directive × Nat)) : Prop :=
  ∀ (s : State) (σ : AS) (c : Ctl) (k : Nat), k < blk.length → s.exe = exe →
    s.st.2 = n.pc + Int64.ofNat (cellOff blk k) → n.J σ c → Z s c

/-- Every node has the trivial fact. -/
theorem NodeZ.top {exe : _root_.Executable} {n : ND} {blk : List (Directive × Nat)} :
    NodeZ (fun _ _ => True) exe n blk :=
  fun _ _ _ _ _ _ _ _ => trivial

/-- **Off the transfer sites, with `Z`.** -/
def NNZ (exe : _root_.Executable) (endPc : Int64) (Z : Frag isa) : Frag isa :=
  fun s c => NN exe endPc s ∧ Z s c

variable {Z : Frag isa}

/-- A block node's states are `NNZ`: `NN` (`blkW_nn`) and `Z` at its pcs. -/
theorem blkW_nnz {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n blk) (hz : NodeZ Z exe n blk) :
    BlkW (NNZ exe endPc Z) (fun _ _ => False) exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hD hJ k hk m hA' hF' =>
    ⟨⟨(h s σ c he hn hd hpc hA hD hJ k hk m hA' hF').1, hz _ σ c k hk he rfl hJ⟩, fun _ h => h⟩

/-- The first cell's pc is the node's. -/
theorem cellOff_zero (blk : List (Directive × Nat)) (pc : Int64) : pc + Int64.ofNat (cellOff blk 0) = pc := by
  simp only [cellOff, List.take_zero, List.map_nil, List.sum_nil]; exact ofNat_zero' pc

/-- A node's states are `NNZ`: `NN` and `Z` at its pc. -/
theorem nodeW_nnz {n : ND} {d : Directive × Nat}
    (h : NodeW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n)
    (hz : NodeZ Z exe n [d]) : NodeW (NNZ exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c hs => by
    have h1 := (h s c hs).1
    obtain ⟨he, -, -, hpc, σ, -, -, hJ⟩ := hs
    exact ⟨⟨h1, hz s σ c 0 (by simp) he (by rw [hpc, cellOff_zero]) hJ⟩, fun _ h => h⟩

/-- `nodeW_nnz` as the fragment of the node's states. -/
theorem at_nnz {n : ND} {d : Directive × Nat}
    (h : NodeW (fun s _ => NN exe endPc s) (fun _ _ => False) exe endPc R F n)
    (hz : NodeZ Z exe n [d]) : ∀ s c, At exe endPc R F n s c → NNZ exe endPc Z s c :=
  fun s c hs => (nodeW_nnz h hz s c hs).1

/-! ## A fact at each node's states, with the abstract run -/

/-- **A fact `Z` at the states of the node `n` before each cell of its
block `blk`**, each related to the abstract run so far and the memory
outside the region as at the node (`BlkW` with no outside moves). Unlike
`NodeZ`, which sees only the pc and the control, it knows the registers
and the frame's cells (`Abs`). A single-instruction node takes `blk :=
[(d, z)]` (`NodeZA.toW`), a call node `blk := []`. -/
abbrev NodeZA (Z : Frag isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (n : ND) (blk : List (Directive × Nat)) : Prop :=
  BlkW Z (fun _ _ => False) exe endPc R F n blk

/-- A fact of the pc and the control at a node's pcs is one at its states. -/
theorem NodeZ.toA {n : ND} {blk : List (Directive × Nat)} (h : NodeZ Z exe n blk) : NodeZA Z exe endPc R F n blk :=
  fun _ σ c he _ _ _ _ _ hJ k hk _ _ _ => ⟨h _ σ c k hk he rfl hJ, fun _ h => h⟩

/-- A single-instruction node's fact is the node's obligation (`NodeW`). -/
theorem NodeZA.toW {n : ND} {d : Directive × Nat} (h : NodeZA Z exe endPc R F n [d]) :
    NodeW Z (fun _ _ => False) exe endPc R F n := fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => by
  have h0 := (h s σ c he hn hdc hpc hA hD hJ 0 (by simp) s.st.1 hA (DFrame.refl _ _)).1
  rw [cellOff_zero, ← hpc] at h0
  exact ⟨h0, fun _ h => h⟩

/-- Two facts at a node's states combine. -/
theorem NodeZA.and {Z' : Frag isa} {n : ND} {blk : List (Directive × Nat)} (h : NodeZA Z exe endPc R F n blk)
    (h' : NodeZA Z' exe endPc R F n blk) : NodeZA (fun s c => Z s c ∧ Z' s c) exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hD hJ k hk m hA' hD' =>
    ⟨⟨(h s σ c he hn hd hpc hA hD hJ k hk m hA' hD').1, (h' s σ c he hn hd hpc hA hD hJ k hk m hA' hD').1⟩,
      fun _ h => h⟩

/-- A weaker fact. -/
theorem NodeZA.mono {Z' : Frag isa} {n : ND} {blk : List (Directive × Nat)} (h : NodeZA Z exe endPc R F n blk)
    (hZ : ∀ s c, Z s c → Z' s c) : NodeZA Z' exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hD hJ k hk m hA' hD' =>
    ⟨hZ _ c (h s σ c he hn hd hpc hA hD hJ k hk m hA' hD').1, fun _ h => h⟩

/-- A block node's states are `NNZ`: `NN` (`blkW_nn`) and `Z` at its states. -/
theorem blkW_nnzA {n : ND} {blk : List (Directive × Nat)}
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
theorem seg_ndNN {n : ND} {lo hi : Int} {blk : List (Directive × Nat)} (hne : blk ≠ [])
    (hok : okBlk lo hi n.o blk = true) (hb : blk.all (fun c => notNop c.1) = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hedge : ∀ σ c, n.J σ c →
      ∃ c', LocalRun p c c' ∧ Lands N E (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩) c')
    (hz : NodeZ Z exe n blk) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (seg_ndW hne hok hF hR hlo hhi hcode (blkW_nnz (blkW_nn hcode hb) hz) hedge)

/-- **A system call's node off the transfer sites** (`syscall_ndW` at
`NN`), its call safe (`hsafe`). -/
theorem syscall_ndNN {n : ND} {z : Nat} (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hedge : ∀ σ c, n.J σ c → ∃ call, syscallCall σ.regs = some call ∧ (∀ a, call ≠ .archSetFs a) ∧
      ∀ v ∈ Scc.Sem.Kernel.results call,
        ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, syscallSO n.o,
          syscallStep (n.pc + Int64.ofNat z) v σ⟩ c')
    (hok : ∀ s c σ call, At exe endPc R F n s c → n.J σ c → syscallCall σ.regs = some call →
      SysOk p ms s c call)
    (hsafe : ∀ σ c, n.J σ c → ∀ call, syscallCall σ.regs = some call →
      call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v))
    (hz : NodeZ Z exe n [(op64 .syscall, z)]) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (syscall_ndW hK hF hcode (nodeW_nnz (nodeW_nnSys hcode hsafe) hz) hedge hok)

/-- **A runtime store off the transfer sites** (`rtst_ndW` at `NN`). -/
theorem rtst_ndNN {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (bAddr σ.regs b k).toNat ∧ ms.mp ⟨bAddr σ.regs b k, 8⟩ true ∧
      ms.G ⟨bAddr σ.regs b k, 8⟩ ((σ.regs.get64 r).setWidth 128) ∧
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o, σ⟩ c')
    (hz : NodeZ Z exe n [(stDir b k r, z)]) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (rtst_ndW hcode (nodeW_nnz (nodeW_nn hcode rfl) hz) hedge)

/-- **An own word's load through the thread pointer off the transfer
sites** (`ownFsld_ndW` at `NN`). -/
theorem ownFsld_ndNN {n : ND} {d : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hd : d ≠ .rsp)
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fsDir d k, z)])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      σ.regs.fsBase.toBitVec + k.toBitVec = A ∧ ms.rt A.toNat ∧ ms.mp ⟨A, 8⟩ false ∧
      Mem.loadInt m.dmem A 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill d, fsStep d v σ⟩ c')
    (hz : NodeZ Z exe n [(fsDir d k, z)]) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (ownFsld_ndW hd hF hcode hown (nodeW_nnz (nodeW_nn hcode rfl) hz) hedge)

/-! ## The `W` leaves at `NNZ`, `Z` at the node's states -/

/-- **`seg_ndNN` with `Z` at the block's states** (`NodeZA`). -/
theorem seg_ndNNA {n : ND} {lo hi : Int} {blk : List (Directive × Nat)} (hne : blk ≠ [])
    (hok : okBlk lo hi n.o blk = true) (hb : blk.all (fun c => notNop c.1) = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hedge : ∀ σ c, n.J σ c →
      ∃ c', LocalRun p c c' ∧ Lands N E (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩) c')
    (hz : NodeZA Z exe endPc R F n blk) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (seg_ndW hne hok hF hR hlo hhi hcode (blkW_nnzA (blkW_nn hcode hb) hz) hedge)

/-- **`syscall_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem syscall_ndNNA {n : ND} {z : Nat} (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hedge : ∀ σ c, n.J σ c → ∃ call, syscallCall σ.regs = some call ∧ (∀ a, call ≠ .archSetFs a) ∧
      ∀ v ∈ Scc.Sem.Kernel.results call,
        ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, syscallSO n.o,
          syscallStep (n.pc + Int64.ofNat z) v σ⟩ c')
    (hok : ∀ s c σ call, At exe endPc R F n s c → n.J σ c → syscallCall σ.regs = some call →
      SysOk p ms s c call)
    (hsafe : ∀ σ c, n.J σ c → ∀ call, syscallCall σ.regs = some call →
      call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v))
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (syscall_ndW hK hF hcode (nodeW_nnzA (nodeW_nnSys hcode hsafe) hz) hedge hok)

/-- **`rtst_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem rtst_ndNNA {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (bAddr σ.regs b k).toNat ∧ ms.mp ⟨bAddr σ.regs b k, 8⟩ true ∧
      ms.G ⟨bAddr σ.regs b k, 8⟩ ((σ.regs.get64 r).setWidth 128) ∧
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o, σ⟩ c')
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (rtst_ndW hcode (nodeW_nnzA (nodeW_nn hcode rfl) hz) hedge)

/-- **`ownFsld_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem ownFsld_ndNNA {n : ND} {d : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hd : d ≠ .rsp)
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fsDir d k, z)])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      σ.regs.fsBase.toBitVec + k.toBitVec = A ∧ ms.rt A.toNat ∧ ms.mp ⟨A, 8⟩ false ∧
      Mem.loadInt m.dmem A 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill d, fsStep d v σ⟩ c')
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (ownFsld_ndW hd hF hcode hown (nodeW_nnzA (nodeW_nn hcode rfl) hz) hedge)

/-! ## The thread-row leaves inside `S` -/

variable {S : Frag isa}

/-- **A whole function inside `S`**: `fn_segT` over `SegTC`. -/
theorem fn_segTS (h : ∀ i, SegTC S p lbl ms (At exe endPc R F (N i)) (Next exe endPc R F N E)) (i0 : ι) :
    SegTC S p lbl ms (At exe endPc R F (N i0)) (fun s c => ∃ x, At exe endPc R F (E x) s c) :=
  (SegTC.cfg (fun i => At exe endPc R F (N i)) h).mono_pre fun _ _ h => ⟨i0, h⟩

/-- **`relStore_nd` inside `S`**: the node's states in `S` (`hS`). -/
theorem relStore_ndS {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A : BitVec 64}
    (hS : ∀ s c, At exe endPc R F n s c → S s c)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧
      ∃ x a bb e ty tb w wb, c.term = .let_ x (.store true a bb none) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ (∃ sa, w.val = .loc sa 0) ∧
        TermRun.evalAt c.env bb = some (tb, [wb]) ∧ ValRep lbl wb.val (σ.regs.get64 r).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat z, n.o, σ⟩ ⟨e, (x, .unit, []) :: c.env, none⟩) :
    SegTC S p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegTC.step hS fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => .outL (.out ?_)
  have hc : CellAt s (stDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, x, a, bb, e, ty, tb, w, wb, ht, hev, hv, htag, hevb, hvb, hL⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = A := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_store_agrees hc ha' (hdm _ hD) (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64, hA.regs] at hex
  refine .store .plain A _ _ x a bb e ty tb w wb hex ht hev hv hevb
    (by rw [toNat_setWidth128]; exact hvb) ?_ htag
  have hs1 : after s z s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- **`unpkXchg_nd` inside `S`**: the node's states in `S` (`hS`). -/
theorem unpkXchg_ndS {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A B : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F) (hS : ∀ s c, At exe endPc R F n s c → S s c)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xchgDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ σ.regs.get64 r = 1#64 ∧ StOk ms F A 1#64 ∧ A = B + 16#64 ∧
      ∃ x a e ty jw, c.term = .let_ x (.ext .unpark a) e ∧ c.hold = none ∧
        TermRun.evalAt c.env a = some (ty, [jw]) ∧ ValRep lbl jw.val B.toNat ∧
        ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩
          ⟨e, (x, ExtName.unpark.sig.2, []) :: c.env, none⟩) :
    SegTC S p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegTC.step hS fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (xchgDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, h1, hS, hAB, x, a, e, ty, jw, ht, hh, hev, hv, hL⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = A := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_xchgG_agrees (w := .W64) hc ha' (hS.unmapped _ hD) (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64] at hex
  refine .unpk .acqRel A B _ _ x a e ty jw hex hS.rt hS.mp (fun _ => by rw [hA.regs, h1, one_setWidth])
    ht hh hev hv hAB fun old _ _ => ⟨?_, ?_⟩
  · have := hS.G
    rwa [one_setWidth] at this
  · exact land_own (flm := s.st.1.status) (fla := σ.status) hA.status hr hF he hn hdc hpc hA hD (hL _)

/-- **`texit_nd` inside `S`**: the node's states in `S` (`hS`). -/
theorem texit_ndS {n : ND} {Q : Frag isa} {z : Nat} (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : ∀ s c, At exe endPc R F n s c → S s c)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hx : ∀ σ c, n.J σ c → σ.regs.rax.toNat = 60 ∧ ∃ a, c.term = .ret a) :
    SegTC S p lbl ms (At exe endPc R F n) Q := by
  refine SegTC.step hS fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (op64 .syscall) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨hax, a, ht⟩ := hx σ c hJ
  have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.x64 (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
      some .exit := by
    rw [← syscallCall_exit hax, syscallCall, ← hA.regs]; rfl
  exact .texit _ a hK (Scc.Sem.X64.atSyscall_of_cellAt hc) hd ht

/-- **A call node inside `S`** (`call_ndT` over `SegTC`): the callee's
specification inside `S` is a given node of the caller. The call node's
states are the callee's entry states, so the call needs no `hS`. The proof
is `call_ndT`'s. -/
theorem call_ndTS {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' → hi' ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) → ∀ g,
        SegTC S p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter (nC.o.sp - e0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegTC S p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  -- the callee's region and its ghost-indexed frame condition
  let kb := nC.o.sp - e0
  let R' := R.callee kb lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkb hhi
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkb hhi hF
  -- the ghost: the machine data and abstract state at the call, the caller's control, the callee's
  -- parameters; the facts about it ride in the frame condition (constant, so stable)
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ DFrame R' G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kb G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, hm.2.1.trans hd, hm.2.2⟩
  refine SegTC.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c)
    (SegTC.exists_pre fun G => ?_) ?_
  · -- the callee's segment, its exits landing at the caller's nodes
    refine (hcallee R' (F' G) hR' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun _ h => h.1) G.2.2.2).mono_post ?_
    rintro s c ⟨x, he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩
    obtain ⟨mC, σC, cC, g⟩ := G
    simp only at hDF hAC hJC hJE hJx hAx hpc
    have hAR : Abs R ⟨kb + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kb σC σx) := by
      refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
      · intro r k' hr
        obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
        have := hAx.so .rsp (Ex g x).o.sp (by simp [SO.get])
        simp only [leave] at this ⊢
        rw [this, Region.callee_addr]
      · by_cases hin : R'.Off (k - kb)
        · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
          refine ⟨j, ?_, ?_⟩
          · rw [Region.callee_addr, show kb + (k - kb) = k by omega] at hj; exact hj
          · simp only [leave]; rw [ite_eq_left hin]; exact hv
        · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
          refine ⟨j, ?_, ?_⟩
          · rw [hDF _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkb hk8 hl8 hh8 hk hin)]
            exact hj
          · simp only [leave]; rw [ite_eq_right hin]; exact hv
    have hL := hret g x σC cC σx c (leave R' kb σC σx) hJC hJE hJx rfl rfl rfl
      (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
    have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
    rw [hs]
    rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
    · exact .inl ⟨j, hj.at he hn hdc hAR hD⟩
    · exact .inr ⟨y, hy.at he hn hdc hAR hD⟩
  · -- the caller's state at the call, seen from the callee
    rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), he, hn, hdc, by rw [hpc, hgpc], enter kb σC, ?_,
      ⟨hD, DFrame.refl _ _, hA, hJ, hgJ⟩, hgJ⟩
    rw [hNe]
    refine ⟨hA.regs, hA.zmms, hA.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
      have := hA.so .rsp nC.o.sp (by simp [SO.get])
      simp only [enter] at this ⊢
      rw [this, Region.callee_addr]; congr 1; omega
    · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo hhi hk8 hk)
      exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

/-- **The callee's region and frame condition at a call** from the node
`nC` (region `R`, frame condition `F`), the callee's frame between `lo'`
and `hi'` from `nC.o.sp - e0`: the region is well formed and covers the
frame, `F'` is stable, and it sees the caller (`sees`): every memory of
`F'` is one of `F`, and outside `R'` agrees with a memory at the call,
related to an abstract state and control of `nC` (`Abs`, `nC.J`). -/
structure CallerF (R : Region) (F : MachineData → Prop) (nC : ND) (e0 lo' hi' : Int) (R' : Region)
    (F' : MachineData → Prop) : Prop where
  ok : R'.OK
  lo : R'.lo ≤ lo'
  hi : hi' ≤ R'.hi
  stab : FStable R' F'
  sees : ∀ m, F' m → F m ∧ ∃ m0 σ0 c0, DFrame R' m0 m ∧ Abs R nC.o m0 σ0 ∧ nC.J σ0 c0

/-- **`call_ndTS` with the caller seen by the callee**: the callee's
segment is needed only at frame conditions that know the caller's frame
(`CallerF`), so facts of the callee's states may read the caller's cells.
The proof is `call_ndTS`'s. -/
theorem call_ndTSA {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), CallerF R F nC e0 lo' hi' R' F' → ∀ g,
        SegTC S p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter (nC.o.sp - e0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegTC S p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  -- the callee's region and its ghost-indexed frame condition
  let kb := nC.o.sp - e0
  let R' := R.callee kb lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkb hhi
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkb hhi hF
  -- the ghost: the machine data and abstract state at the call, the caller's control, the callee's
  -- parameters; the facts about it ride in the frame condition (constant, so stable)
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ DFrame R' G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kb G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, hm.2.1.trans hd, hm.2.2⟩
  refine SegTC.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c)
    (SegTC.exists_pre fun G => ?_) ?_
  · -- the callee's segment, its exits landing at the caller's nodes
    refine (hcallee R' (F' G) ⟨hR', Int.le_refl _, Int.le_refl _, hF' G,
      fun _ h => ⟨h.1, G.1, G.2.1, G.2.2.1, h.2.1, h.2.2.1, h.2.2.2.1⟩⟩ G.2.2.2).mono_post ?_
    rintro s c ⟨x, he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩
    obtain ⟨mC, σC, cC, g⟩ := G
    simp only at hDF hAC hJC hJE hJx hAx hpc
    have hAR : Abs R ⟨kb + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kb σC σx) := by
      refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
      · intro r k' hr
        obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
        have := hAx.so .rsp (Ex g x).o.sp (by simp [SO.get])
        simp only [leave] at this ⊢
        rw [this, Region.callee_addr]
      · by_cases hin : R'.Off (k - kb)
        · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
          refine ⟨j, ?_, ?_⟩
          · rw [Region.callee_addr, show kb + (k - kb) = k by omega] at hj; exact hj
          · simp only [leave]; rw [ite_eq_left hin]; exact hv
        · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
          refine ⟨j, ?_, ?_⟩
          · rw [hDF _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkb hk8 hl8 hh8 hk hin)]
            exact hj
          · simp only [leave]; rw [ite_eq_right hin]; exact hv
    have hL := hret g x σC cC σx c (leave R' kb σC σx) hJC hJE hJx rfl rfl rfl
      (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
    have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
    rw [hs]
    rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
    · exact .inl ⟨j, hj.at he hn hdc hAR hD⟩
    · exact .inr ⟨y, hy.at he hn hdc hAR hD⟩
  · -- the caller's state at the call, seen from the callee
    rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), he, hn, hdc, by rw [hpc, hgpc], enter kb σC, ?_,
      ⟨hD, DFrame.refl _ _, hA, hJ, hgJ⟩, hgJ⟩
    rw [hNe]
    refine ⟨hA.regs, hA.zmms, hA.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
      have := hA.so .rsp nC.o.sp (by simp [SO.get])
      simp only [enter] at this ⊢
      rw [this, Region.callee_addr]; congr 1; omega
    · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo hhi hk8 hk)
      exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

/-! ## The thread-row leaves at `NN` -/

/-- **`relStore_nd` off the transfer sites.** -/
theorem relStore_ndNN {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧
      ∃ x a bb e ty tb w wb, c.term = .let_ x (.store true a bb none) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ (∃ sa, w.val = .loc sa 0) ∧
        TermRun.evalAt c.env bb = some (tb, [wb]) ∧ ValRep lbl wb.val (σ.regs.get64 r).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat z, n.o, σ⟩ ⟨e, (x, .unit, []) :: c.env, none⟩)
    (hz : NodeZ Z exe n [(stDir b k r, z)]) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  relStore_ndS (at_nnz (nodeW_nn hcode rfl) hz) hcode hdm hedge

/-- **`unpkXchg_nd` off the transfer sites.** -/
theorem unpkXchg_ndNN {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A B : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xchgDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ σ.regs.get64 r = 1#64 ∧ StOk ms F A 1#64 ∧ A = B + 16#64 ∧
      ∃ x a e ty jw, c.term = .let_ x (.ext .unpark a) e ∧ c.hold = none ∧
        TermRun.evalAt c.env a = some (ty, [jw]) ∧ ValRep lbl jw.val B.toNat ∧
        ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩
          ⟨e, (x, ExtName.unpark.sig.2, []) :: c.env, none⟩)
    (hz : NodeZ Z exe n [(xchgDir b k r, z)]) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  unpkXchg_ndS hr hF (at_nnz (nodeW_nn hcode rfl) hz) hcode hedge

/-- **`texit_nd` off the transfer sites.** -/
theorem texit_ndNN {n : ND} {Q : Frag isa} {z : Nat} (hK : ms.K = some Scc.Sem.X64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hx : ∀ σ c, n.J σ c → σ.regs.rax.toNat = 60 ∧ ∃ a, c.term = .ret a)
    (hz : NodeZ Z exe n [(op64 .syscall, z)]) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) Q :=
  texit_ndS hK (at_nnz (nodeW_nnSys hcode fun σ c hJ call hcall => by
    rw [syscallCall_exit (hx σ c hJ).1] at hcall
    exact .inl (Option.some.inj hcall).symm) hz) hcode hx

/-- **`relStore_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem relStore_ndNNA {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A : BitVec 64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧
      ∃ x a bb e ty tb w wb, c.term = .let_ x (.store true a bb none) e ∧
        TermRun.evalAt c.env a = some (ty, [w]) ∧ ValRep lbl w.val A.toNat ∧ (∃ sa, w.val = .loc sa 0) ∧
        TermRun.evalAt c.env bb = some (tb, [wb]) ∧ ValRep lbl wb.val (σ.regs.get64 r).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat z, n.o, σ⟩ ⟨e, (x, .unit, []) :: c.env, none⟩)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  relStore_ndS (at_nnzA (nodeW_nn hcode rfl) hz) hcode hdm hedge

/-- **`unpkXchg_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem unpkXchg_ndNNA {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A B : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xchgDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ σ.regs.get64 r = 1#64 ∧ StOk ms F A 1#64 ∧ A = B + 16#64 ∧
      ∃ x a e ty jw, c.term = .let_ x (.ext .unpark a) e ∧ c.hold = none ∧
        TermRun.evalAt c.env a = some (ty, [jw]) ∧ ValRep lbl jw.val B.toNat ∧
        ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩
          ⟨e, (x, ExtName.unpark.sig.2, []) :: c.env, none⟩)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  unpkXchg_ndS hr hF (at_nnzA (nodeW_nn hcode rfl) hz) hcode hedge

/-- **`texit_ndNN` with `Z` at the node's states** (`NodeW`). -/
theorem texit_ndNNA {n : ND} {Q : Frag isa} {z : Nat} (hK : ms.K = some Scc.Sem.X64.abi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hx : ∀ σ c, n.J σ c → σ.regs.rax.toNat = 60 ∧ ∃ a, c.term = .ret a)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) Q :=
  texit_ndS hK (at_nnzA (nodeW_nnSys hcode fun σ c hJ call hcall => by
    rw [syscallCall_exit (hx σ c hJ).1] at hcall
    exact .inl (Option.some.inj hcall).symm) hz) hcode hx

end Nodes

/-! ## The prologue at `NN` -/

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- A cell's offset is at most its block's length in bytes. -/
theorem cellOff_le (blk : List (Directive × Nat)) (k : Nat) : cellOff blk k ≤ (blk.map (·.2)).sum := by
  unfold cellOff
  induction blk generalizing k with
  | nil => simp
  | cons c cs ih =>
    cases k with
    | zero => simp
    | succ k => simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; have := ih k; omega

/-- The prologue's blocks have no `nop`. -/
theorem xHead_notNop : xHead.all (fun c => notNop c.1) = true := by decide
theorem xLea_notNop (Z : Int64) (z : Nat) : (xLea Z z).all (fun c => notNop c.1) = true := by
  simp [xLea, notNop]
theorem xCmp_notNop (L : String) (z1 z2 : Nat) : (xCmp L z1 z2).all (fun c => notNop c.1) = true := by
  simp [xCmp, notNop]
theorem xFr_notNop (Z : Int64) (z : Nat) (ps : List (Reg64 × Int64 × Nat)) :
    (xFr Z z ps).all (fun c => notNop c.1) = true := by
  simp [xFr, xSt, notNop, List.all_map]

/-- `a + 1 + 3 + m` as one offset. -/
theorem pc_off (a : Int64) (m j : Nat) : a + 1 + 3 + Int64.ofNat m + Int64.ofNat j = a + Int64.ofNat (4 + m + j) := by
  have h : a + 1 + 3 = a + Int64.ofNat 4 := by rw [Int64.add_assoc]; rfl
  rw [ofNat_add', ofNat_add', h]

theorem xHead_sum : (xHead.map (·.2)).sum = 4 := rfl
theorem xLea_sum (Z : Int64) (z : Nat) : ((xLea Z z).map (·.2)).sum = z := by simp [xLea]
theorem xCmp_sum (L : String) (z1 z2 : Nat) : ((xCmp L z1 z2).map (·.2)).sum = z1 + z2 := by simp [xCmp]

omit [Executable.ValidLayout exe] in
/-- **A fact of the pc and the control at the prologue's bytes is one at
its states** (`XProW`): `Zf` at the bytes `k ≤ pz` from `pc0` (`pz` the
prologue's length) with the entry's control (every node of the prologue
keeps it). -/
theorem XProW.ofPcs {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    {J : AS → Ctl → Prop} {Zf : Frag isa}
    (hz : ∀ (s : State) σ c (k : Nat), k ≤ 4 + zl + zf + z1 + z2 + zs + szSum ps → s.exe = exe →
      s.st.2 = pc0 + Int64.ofNat k → J σ c → Zf s c) :
    XProW Zf (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J := by
  have hsx : ((xFr Z zs ps).map (·.2)).sum = zs + szSum ps := by
    simp [xFr, xSt, szSum, Function.comp_def]
  refine ⟨NodeZ.toA ?_, NodeZ.toA ?_, NodeZA.toW (d := (fsDir .r11 lim, zf)) (NodeZ.toA ?_), NodeZ.toA ?_,
    NodeZ.toA ?_⟩
  · intro s σ c k _ he hpc hJ
    have := cellOff_le xHead k
    exact hz s σ c (cellOff xHead k) (by rw [xHead_sum] at this; omega) he hpc hJ
  · rintro s σ1 c k _ he hpc ⟨σ, hJ, -⟩
    have := cellOff_le (xLea Z zl) k
    refine hz s σ c (4 + 0 + cellOff (xLea Z zl) k) (by rw [xLea_sum] at this; omega) he ?_ hJ
    rw [hpc, ← pc_off, ofNat_zero']; rfl
  · rintro s σ2 c k hk he hpc ⟨σ, hJ, -⟩
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    refine hz s σ c (4 + zl + 0) (by omega) he ?_ hJ
    rw [hpc, ← pc_off, cellOff_zero, ofNat_zero']; rfl
  · rintro s σ3 c k _ he hpc ⟨σ, v, hJ, -⟩
    have := cellOff_le (xCmp L z1 z2) k
    refine hz s σ c (4 + (zl + zf) + cellOff (xCmp L z1 z2) k) (by rw [xCmp_sum] at this; omega) he ?_ hJ
    rw [hpc, ← pc_off, ofNat_add']; rfl
  · rintro s σ4 c k _ he hpc ⟨σ, v, hJ, -⟩
    have := cellOff_le (xFr Z zs ps) k
    refine hz s σ c (4 + (zl + zf + z1 + z2) + cellOff (xFr Z zs ps) k) (by rw [hsx] at this; omega) he ?_ hJ
    rw [hpc, ← pc_off, ofNat_add', ofNat_add', ofNat_add']; rfl

/-- **The prologue off the transfer sites, `Zf` at its states**
(`prologue_seg_ofW` at `NNZ`, `XProW` from the prologue's code, none of its
blocks a `nop`, and `hz`). -/
theorem prologue_seg_ofNNA {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    {fn sc entry : Label} {Z lim : Int64} {L : Label} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    (hin : prologueIn cells fn sc entry Z lim L zl zf z1 z2 zs ps = true)
    {J : AS → Ctl → Prop} {nb : ND} (hZ : 0 ≤ Z.toInt) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hpc : nb.pc = (_root_.Executable.labels exe).label entry)
    (ho : SO.le nb.o (oF Z) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + lim.toBitVec).toNat ∧ ms.mp ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + lim.toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs Z (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs ps (xS1 σ).slot → nb.J σ' c)
    {Zf : Frag isa}
    (hz : XProW Zf (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label fn) Z lim L
      zl zf z1 z2 zs ps J) :
    SegTC (NNZ exe endPc Zf) p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) := by
  refine SegW.toTC (prologue_seg_ofW hp hend hin hZ hF hR hlo hhi hps hpc ho ?_ hedge)
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, b4, -⟩ := hin
  have e0 := label_labelGapB hp g0
  have h4 : (_root_.Executable.labels exe).label fn + 1 + 3 = (_root_.Executable.labels exe).label sc := by
    rw [e0, Int64.add_assoc]; rfl
  refine ⟨blkW_nnzA (blkW_nn (code_field hp hend b0 (ofNat_zero' _)) xHead_notNop) hz.w0,
    blkW_nnzA (blkW_nn (code_field hp hend b1 ?_) (xLea_notNop Z zl)) hz.w1,
    nodeW_nnzA (nodeW_nn (code_field hp hend b2 ?_) rfl) hz.w2,
    blkW_nnzA (blkW_nn (code_field hp hend b3 ?_) (xCmp_notNop L z1 z2)) hz.w3,
    blkW_nnzA (blkW_nn (code_field hp hend b4 ?_) (xFr_notNop Z zs ps)) hz.w4⟩
  · show _ = _ + 1 + 3; rw [h4, ofNat_zero']
  · show _ = _ + 1 + 3 + _; rw [h4]
  · show _ = _ + 1 + 3 + _ + _; rw [h4, ofNat_add']
  · show _ = _ + 1 + 3 + _ + _ + _ + _; rw [h4, ofNat_add', ofNat_add', ofNat_add']

/-- **The prologue off the transfer sites** (`prologue_seg_ofNNA`), `Zf` at
its bytes with the entry's control (`hz`, `XProW.ofPcs`). -/
theorem prologue_seg_ofNN {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    {fn sc entry : Label} {Z lim : Int64} {L : Label} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    (hin : prologueIn cells fn sc entry Z lim L zl zf z1 z2 zs ps = true)
    {J : AS → Ctl → Prop} {nb : ND} (hZ : 0 ≤ Z.toInt) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hpc : nb.pc = (_root_.Executable.labels exe).label entry)
    (ho : SO.le nb.o (oF Z) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + lim.toBitVec).toNat ∧ ms.mp ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + lim.toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs Z (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs ps (xS1 σ).slot → nb.J σ' c)
    {Zf : Frag isa}
    (hz : ∀ (s : State) σ c (k : Nat), k ≤ 4 + zl + zf + z1 + z2 + zs + szSum ps → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat k → J σ c → Zf s c) :
    SegTC (NNZ exe endPc Zf) p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofNNA hp hend hin hZ hF hR hlo hhi hps hpc ho hedge (XProW.ofPcs hz)

end Pro

/-- info: 'Spike.Lib.X64.Flow.Worker.prologue_seg_ofNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prologue_seg_ofNN

/-- info: 'Spike.Lib.X64.Flow.Worker.call_ndTSA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms call_ndTSA

/-- info: 'Spike.Lib.X64.Flow.Worker.unpkXchg_ndNNA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unpkXchg_ndNNA


end Spike.Lib.X64.Flow.Worker
