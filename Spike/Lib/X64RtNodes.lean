/-
**x64 runtime stores as nodes of a function, and `%rbp` after a call**: the
x64 twin of `rtst_nd` in `Spike/Lib/A64AllocNodes.lean`.

- **A runtime store** `movq %r, k(%b)` (`rtst_nd`) to an address the runtime
  owns (`ms.rt`), outside the thread's private memory (the declarations
  agree there: a node's states have none, `At`): one `Out.rtStore` (Kraken's row
  `exec_store_agrees`, `Kraken/Promising/Lower/EventsX64.lean`); the state
  after it lands at a node with the registers, cells and offsets kept.
- **`%rbp`'s offset back after a call** (`At.rbp`): `call_nd` lands at
  offsets that know `%rsp` alone. A node whose invariant fixes `%rbp`
  relative to `%rsp` may also claim `%rbp`'s offset.
- **`arch_prctl(ARCH_SET_FS, a)`** (`archSetFs_nd`), the system call
  `syscall_nd` excludes: one `Out.sys` whose one successor
  (`certSuccs_archSetFs`) has the `%fs` base `a`, then the return of 0
  (`%rax`, `%rcx`, `%r11` as at every `syscall`). The call is always one the
  judgement matches (`SysOk.archSetFs`).
- **The runtime's accesses to its own words** (`ownXadd_nd`, `ownXchg_nd`
  through `Out.rtRmw`, `ownLd_nd` through `Out.rtLoad`): the old value, or
  the value read, is the one the thread owns at the access's pc (`OwnAt`),
  so the state after the access is determined; `%r` gets that value.
-/
import Spike.Lib.X64Nodes
import Kraken.Promising.Lower.EventsX64W

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64

/-! ## A runtime store -/

/-- `movq %r, k(%b)`. -/
def stDir (b : Reg64) (k : Int64) (r : Reg64) : Directive := (AI.st b k r).toDir

/-- The address `k(%b)` in the registers `regs`. -/
def bAddr (regs : Reg64s) (b : Reg64) (k : Int64) : BitVec 64 := regs.get64 b + BitVec.ofInt 64 k.toInt

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at a runtime store** `movq %r, k(%b)`: from every state of the
invariant the address is owned by the runtime and mapped for writing, the
runtime memory may hold
`%r` there, and the address is outside the thread's private memory; after a local run of the source the state after
the store (registers, cells and offsets kept) lands at a node. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem rtst_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (bAddr σ.regs b k).toNat ∧ ms.mp ⟨bAddr σ.regs b k, 8⟩ true ∧
      ms.G ⟨bAddr σ.regs b k, 8⟩ ((σ.regs.get64 r).setWidth 128) ∧
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o, σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (stDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨hrt, hmp, hG, hdm, c', hr, hL⟩ := hedge _ σ c hA hD hJ
  have ha : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_store_agrees hc ha (by exact hdm) (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64, hA.regs] at hex
  refine .rtStore _ _ _ _ c' hex hrt hmp hG hr ?_
  have hs1 : after s z s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- **`rtst_ndW` inside the trivial predicate**, with no outside moves. -/
theorem rtst_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (bAddr σ.regs b k).toNat ∧ ms.mp ⟨bAddr σ.regs b k, 8⟩ true ∧
      ms.G ⟨bAddr σ.regs b k, 8⟩ ((σ.regs.get64 r).setWidth 128) ∧
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o, σ⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (rtst_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hcode hedge).toSeg

/-! ## `arch_prctl(ARCH_SET_FS)` -/

/-- **The abstract state with the `%fs` base `a`** (`Scc.Sem.X64.abi.setTp`). -/
def setFsStep (a : Nat) (σ : AS) : AS := { σ with regs := { σ.regs with fsBase := UInt64.ofNat a } }

/-- The registers after `arch_prctl(ARCH_SET_FS, a)` returns, `nx` the next pc. -/
abbrev fsRegs (nx : Int64) (σ : AS) (a : Nat) (r : Reg64s) : Reg64s :=
  syscallRegs nx (Scc.Sem.X64.rflags σ.status) 0 { r with fsBase := UInt64.ofNat a }

/-- The `%fs` base is not a general register. -/
theorem get64_setFs (r : Reg64s) (a : UInt64) (x : Reg64) : ({ r with fsBase := a } : Reg64s).get64 x = r.get64 x := by
  cases x <;> rfl

/-- **`arch_prctl(ARCH_SET_FS, %rsi)`**: the call the kernel model decodes
from `%rax = 158` and `%rdi = ARCH_SET_FS`. -/
theorem syscallCall_archSetFs {r : Reg64s} (ha : r.rax.toNat = 158) (h0 : r.rdi.toNat = 4098) :
    syscallCall r = some (.archSetFs r.rsi.toNat) := by
  simp [syscallCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, ha, h0, Scc.Sem.Kernel.archSetFs]

/-- `arch_prctl` is a system call the judgement matches. -/
theorem SysOk.archSetFs {s : State} {c : Ctl} {a : Nat} : SysOk p ms s c (.archSetFs a) :=
  ⟨nofun, nofun, nofun, nofun⟩

/-- **A node at `arch_prctl(ARCH_SET_FS, a)`**, under the kernel model
`Scc.Sem.X64.abi`: from every state of the invariant the call decodes to
`arch_prctl` with some `a`, and the state after it (the `%fs` base `a`, then
`syscallStep` of the result 0) lands at a node after a local run of the
source. Only the thread's control (see `Out.sys`). Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem archSetFs_ndW {W : Frag isa} {K : State → State → Prop}
    {n : ND} {z : Nat} (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ σ c, n.J σ c → ∃ a, syscallCall σ.regs = some (.archSetFs a) ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, syscallSO n.o,
        syscallStep (n.pc + Int64.ofNat z) 0 (setFsStep a σ)⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := id hAt
  have hc : CellAt s (op64 .syscall) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨a, hcall, c', hr, hL⟩ := hedge σ c hJ
  have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.x64 (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
      some (.archSetFs a) := by
    rw [← hcall, syscallCall, ← hA.regs]; rfl
  refine .sys _ _ hK (Scc.Sem.X64.atSyscall_of_cellAt hc) hd SysOk.archSetFs fun s' hs' => ?_
  rw [Scc.Sem.X64.certSuccs_archSetFs hc a] at hs'
  obtain rfl := List.mem_singleton.1 hs'
  refine ⟨c', hr, ?_⟩
  have hA' : Abs R (syscallSO n.o)
      { s.st.1 with regs := fsRegs (n.pc + Int64.ofNat z) σ a s.st.1.regs }
      (syscallStep (n.pc + Int64.ofNat z) 0 (setFsStep a σ)) := by
    refine ⟨by simp only [syscallStep, setFsStep, hA.regs], hA.zmms, hA.status, ?_, hA.slot⟩
    refine syscallSO_rel (fun r k h => ?_) _ _ _
    rw [get64_setFs]; exact hA.so r k h
  have hD' : F { s.st.1 with regs := fsRegs (n.pc + Int64.ofNat z) σ a s.st.1.regs } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : syscallRet (Scc.Sem.X64.abi.setTp s a) z
      (Scc.Sem.X64.kret (Scc.Sem.X64.rflags s.st.1.status) (syscallInfo s z) 0) =
      { s with st := ({ s.st.1 with regs := fsRegs (n.pc + Int64.ofNat z) σ a s.st.1.regs },
        n.pc + Int64.ofNat z) } := by
    simp only [Scc.Sem.X64.abi, syscallRet, after, Scc.Sem.X64.kret, syscallRegs, hpc, hA.status]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨y, hy.at he hn hdc hA' hD'⟩

/-- **`archSetFs_ndW` inside the trivial predicate**, with no outside moves. -/
theorem archSetFs_nd {n : ND} {z : Nat} (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hedge : ∀ σ c, n.J σ c → ∃ a, syscallCall σ.regs = some (.archSetFs a) ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, syscallSO n.o,
        syscallStep (n.pc + Int64.ofNat z) 0 (setFsStep a σ)⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (archSetFs_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hK hF hcode hedge).toSeg

/-! ## Own-word accesses -/

/-- **The thread owns the word `a` with value `v` at `pc`** (`MemSide.own`):
at every state of the executable at that pc, the value before the access
there. A named hypothesis of the segments until the own map is wired. -/
def OwnAt (ms : MemSide isa) (exe : _root_.Executable) (endPc pc : Int64) (a v : BitVec 64) : Prop :=
  ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = pc → (⟨a, 8⟩, v.setWidth 128) ∈ ms.own s

/-- `lock xaddq %r, k(%b)`. -/
def xaddDir (b : Reg64) (k : Int64) (r : Reg64) : Directive := op64 (.xadd true (.mem (mB b k)) (.low r .W64))

/-- `xchgq %r, k(%b)`. -/
def xchgDir (b : Reg64) (k : Int64) (r : Reg64) : Directive := op64 (.xchg (.low r .W64) (.mem (mB b k)))

/-- `movq k(%b), %r`. -/
def ldDir (b : Reg64) (k : Int64) (r : Reg64) : Directive := (AI.ld r b k).toDir

/-- The abstract state after an access that writes `v` to `%d`. -/
def ownStep (d : Reg64) (v : BitVec 64) (σ : AS) : AS := { σ with regs := σ.regs.set64 d v }

theorem setWidth_128_64 (v : BitVec 64) : (v.setWidth 128).setWidth 64 = v := by simp

/-- The state after an access writing `v` to `%d` and the flags `flm`
(`fla` abstractly), landing in `Next`. -/
theorem land_own {s : State} {c : Ctl} {n : ND} {d : Reg64} {v : BitVec 64} {z : Nat} {σ : AS}
    {flm fla : StatusFlags} (hfl : flm = fla) (hd : d ≠ .rsp) (hF : FStable R F)
    (he : s.exe = exe) (hn : s.endPc = endPc) (hdc : s.decls = {}) (hpc : s.st.2 = n.pc) (hA : Abs R n.o s.st.1 σ)
    (hD : F s.st.1) (hL : Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill d, { ownStep d v σ with status := fla }⟩ c) :
    Next exe endPc R F N E (after s z { s.st.1 with regs := s.st.1.regs.set (Reg.low d .W64) v, status := flm }) c := by
  subst hfl
  have hset : s.st.1.regs.set (Reg.low d .W64) v = s.st.1.regs.set64 d v := by cases d <;> rfl
  rw [hset]
  have hA' : Abs R (n.o.kill d) { s.st.1 with regs := s.st.1.regs.set64 d v, status := flm }
      { ownStep d v σ with status := flm } := by
    refine ⟨by simp only [ownStep, hA.regs], hA.zmms, rfl, ?_, hA.slot⟩
    exact SORel.write (o := n.o) (d := d) (by simp [SO.write, hd]) hA.so fun r hr =>
      Reg64s.get64_set64_ne _ hr _
  have hD' : F { s.st.1 with regs := s.st.1.regs.set64 d v, status := flm } := hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s z { s.st.1 with regs := s.st.1.regs.set64 d v, status := flm } =
      { s with st := ({ s.st.1 with regs := s.st.1.regs.set64 d v, status := flm }, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨y, hy.at he hn hdc hA' hD'⟩

/-- **A node at an own word's `lock xaddq %r, k(%b)`**: the address `A` is
the runtime's, mapped for a write, outside the thread's private memory, the
thread owns it with value `v` (`hown`),
and runtime memory may hold `v + %r` there; `%r` gets `v`, the flags any
value. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem ownXadd_ndW {W : Frag isa} {K : State → State → Prop}
    {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xaddDir b k r, z)])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ ms.rt A.toNat ∧ ms.mp ⟨A, 8⟩ true ∧
      ms.G ⟨A, 8⟩ ((v + σ.regs.get64 r).setWidth 128) ∧ Mem.loadInt m.dmem A 8 = none ∧
      ∃ c', LocalRun p c c' ∧
        ∀ fl, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, { ownStep r v σ with status := fl }⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (xaddDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, hrt, hmp, hG, hdm, c', hrun, hL⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = A := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_xaddG_agrees (w := .W64) hc ha' hdm (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64] at hex
  refine .rtRmw .acqRel _ _ _ c' hex hrt hmp hrun fun old _ ho => ?_
  obtain rfl := ho _ (hown s he hn hpc)
  refine ⟨fun new hnew => ?_, ?_⟩
  · simp only [Option.some.injEq] at hnew
    subst hnew
    rw [setWidth_128_64, hA.regs]; exact hG
  · rw [setWidth_128_64]
    exact land_own rfl hr hF he hn hdc hpc hA hD (hL _)

/-- **`ownXadd_ndW` inside the trivial predicate**, with no outside moves. -/
theorem ownXadd_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xaddDir b k r, z)])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ ms.rt A.toNat ∧ ms.mp ⟨A, 8⟩ true ∧
      ms.G ⟨A, 8⟩ ((v + σ.regs.get64 r).setWidth 128) ∧ Mem.loadInt m.dmem A 8 = none ∧
      ∃ c', LocalRun p c c' ∧
        ∀ fl, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, { ownStep r v σ with status := fl }⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (ownXadd_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hr hF hcode hown hedge).toSeg

/-- **A node at an own word's `xchgq %r, k(%b)`**: as `ownXadd_nd`, the new
value `%r`'s, the flags kept. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem ownXchg_ndW {W : Frag isa} {K : State → State → Prop}
    {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xchgDir b k r, z)])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ ms.rt A.toNat ∧ ms.mp ⟨A, 8⟩ true ∧
      ms.G ⟨A, 8⟩ ((σ.regs.get64 r).setWidth 128) ∧ Mem.loadInt m.dmem A 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (xchgDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, hrt, hmp, hG, hdm, c', hrun, hL⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = A := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_xchgG_agrees (w := .W64) hc ha' hdm (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64] at hex
  refine .rtRmw .acqRel _ _ _ c' hex hrt hmp hrun fun old _ ho => ?_
  obtain rfl := ho _ (hown s he hn hpc)
  refine ⟨fun new hnew => ?_, ?_⟩
  · simp only [Option.some.injEq] at hnew
    subst hnew
    rw [hA.regs]; exact hG
  · rw [setWidth_128_64]
    exact land_own (flm := s.st.1.status) (fla := σ.status) hA.status hr hF he hn hdc hpc hA hD hL

/-- **`ownXchg_ndW` inside the trivial predicate**, with no outside moves. -/
theorem ownXchg_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xchgDir b k r, z)])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ ms.rt A.toNat ∧ ms.mp ⟨A, 8⟩ true ∧
      ms.G ⟨A, 8⟩ ((σ.regs.get64 r).setWidth 128) ∧ Mem.loadInt m.dmem A 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (ownXchg_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hr hF hcode hown hedge).toSeg

/-- **A node at an own word's load** `movq k(%b), %r`: the address `A` is
the runtime's, mapped for a read, outside the thread's private memory, and
the thread owns it with value `v`
(`hown`); `%r` gets `v`. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem ownLd_ndW {W : Frag isa} {K : State → State → Prop}
    {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(ldDir b k r, z)])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ ms.rt A.toNat ∧ ms.mp ⟨A, 8⟩ false ∧ Mem.loadInt m.dmem A 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (ldDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, hrt, hmp, hdm, c', hrun, hL⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = A := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_load_agrees hc ha' hdm (agrees_of_decls hdc _ _)
  refine .rtLoad _ _ _ c' hex hrt hmp hrun fun w _ ho => ?_
  obtain rfl := ho _ (hown s he hn hpc)
  rw [setWidth_128_64]
  exact land_own (flm := s.st.1.status) (fla := σ.status) hA.status hr hF he hn hdc hpc hA hD hL

/-- **`ownLd_ndW` inside the trivial predicate**, with no outside moves. -/
theorem ownLd_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(ldDir b k r, z)])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ ms.rt A.toNat ∧ ms.mp ⟨A, 8⟩ false ∧ Mem.loadInt m.dmem A 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (ownLd_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hr hF hcode hown hedge).toSeg

end Fn

/-! ## `%rbp`'s offset after a call -/

/-- **`%rbp`'s offset from the invariant**: at a node whose invariant puts
`%rbp` at `k - sp` bytes above `%rsp` (`sp` the node's offset of `%rsp`),
`%rbp` is at offset `k`. -/
theorem At.rbp {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {pc : Int64}
    {sp k : Int} {rs : List (Reg64 × Int)} {J : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F ⟨pc, ⟨sp, rs⟩, J⟩ s c)
    (hJ : ∀ σ c, J σ c → σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (k - sp)) :
    At exe endPc R F ⟨pc, ⟨sp, (.rbp, k) :: rs⟩, J⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ'⟩ := h
  refine ⟨he, hn, hdc, hpc, σ, ⟨hA.regs, hA.zmms, hA.status, fun r k' hk => ?_, hA.slot⟩, hD, hJ'⟩
  have hsp := hA.so .rsp sp (SO.get_rsp _)
  unfold SO.get at hk
  split at hk
  · rename_i hr; subst hr; cases hk; exact hsp
  · rename_i hr
    simp only [lk] at hk
    split at hk
    · rename_i hb; subst hb; cases hk
      rw [hJ σ c hJ', hsp, ← Region.addr_add]; congr 1; omega
    · exact hA.so r k' (by simp only [SO.get, hr, ↓reduceIte]; exact hk)

/-! ## The parser's forms -/

section Parse

open Kraken.X64.Parser

/-- `stDir` is what Kraken's parser makes of scc's runtime stores. -/
example : parse("movq %rax, (%rcx)
movq %rax, 8(%rcx)
movq %rax, 40(%rcx)") = [stDir .rcx 0 .rax, stDir .rcx 8 .rax, stDir .rcx 40 .rax] := by
  decide

/-- `xaddDir`, `xchgDir` and `ldDir` are what Kraken's parser makes of
scc's own-word accesses. -/
example : parse("lock xaddq %rax, (%rcx)
xchgq %rax, (%rcx)
movq (%rcx), %rax") = [xaddDir .rcx 0 .rax, xchgDir .rcx 0 .rax, ldDir .rcx 0 .rax] := by
  decide

end Parse

end Spike.Lib.X64
