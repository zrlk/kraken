/-
**The runtime's own-word accesses, owned at the node's states** (x86-64):
`ownXadd_ndW`, `ownXchg_ndW`, `ownLd_ndW` (`Spike/Lib/X64RtNodes.lean`) with
their `OwnAt` (every state at the access's pc) weakened to the access node's
states, and the callees' memory-side facts in that form. The x86-64 twin of
`Spike/Lib/Rt/A64OwnA.lean`. A runtime callee can run at one pc with
different owned values (`scc_rt_alloc_tcb` twice in wake.w), so `OwnAt` at
one pc cannot hold at an owned-words map telling the calls apart by `sp`
(`ownG`). The node's states carry the call's frame, so at them it can.

- `ownXadd_ndWA`, `ownXchg_ndWA`, `ownLd_ndWA`: the node lemmas, `hown` at
  `At … n` only (AArch64's `ownLdop_ndWA`, `ownSwp_ndWA`, `ownLdr_ndWA`);
- `TcbOkA`: `TcbOk` with `own` at `tcbN q .rmw`'s states in the callee's
  region `R` under its frame condition `F`;
- `TakeOkA`: `TakeOk` with `ownLock`, `ownFreeN`, `ownNext` at
  `takeNG q b .swp`'s, `.ldn`'s, `.nxt`'s states;
- `.of_tcbOk`, `.of_takeOk`: the `OwnAt` forms give them; `.mono`: under a
  stronger frame condition.
-/
import Spike.Lib.X64Ret0

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0

set_option linter.unusedSimpArgs false

section OwnA

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at an own word's `lock xaddq %r, k(%b)`, owned at the node's
states** (`ownXadd_ndW` with `hown` at `At … n` only). -/
theorem ownXadd_ndWA {W : Frag isa} {K : State → State → Prop}
    {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xaddDir b k r, z)])
    (hown : ∀ s c, At exe endPc R F n s c → (⟨A, 8⟩, v.setWidth 128) ∈ ms.own s)
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
  obtain rfl := ho _ (hown s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩)
  refine ⟨fun new hnew => ?_, ?_⟩
  · simp only [Option.some.injEq] at hnew
    subst hnew
    rw [setWidth_128_64, hA.regs]; exact hG
  · rw [setWidth_128_64]
    exact land_own rfl hr hF he hn hdc hpc hA hD (hL _)

/-- **A node at an own word's `xchgq %r, k(%b)`, owned at the node's
states** (`ownXchg_ndW` with `hown` at `At … n` only). -/
theorem ownXchg_ndWA {W : Frag isa} {K : State → State → Prop}
    {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xchgDir b k r, z)])
    (hown : ∀ s c, At exe endPc R F n s c → (⟨A, 8⟩, v.setWidth 128) ∈ ms.own s)
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
  obtain rfl := ho _ (hown s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩)
  refine ⟨fun new hnew => ?_, ?_⟩
  · simp only [Option.some.injEq] at hnew
    subst hnew
    rw [hA.regs]; exact hG
  · rw [setWidth_128_64]
    exact land_own (flm := s.st.1.status) (fla := σ.status) hA.status hr hF he hn hdc hpc hA hD hL

/-- **A node at an own word's load `movq k(%b), %r`, owned at the node's
states** (`ownLd_ndW` with `hown` at `At … n` only). -/
theorem ownLd_ndWA {W : Frag isa} {K : State → State → Prop}
    {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(ldDir b k r, z)])
    (hown : ∀ s c, At exe endPc R F n s c → (⟨A, 8⟩, v.setWidth 128) ∈ ms.own s)
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
  obtain rfl := ho _ (hown s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩)
  rw [setWidth_128_64]
  exact land_own (flm := s.st.1.status) (fla := σ.status) hA.status hr hF he hn hdc hpc hA hD hL

end OwnA

/-! ## The callees' memory-side facts, owned at the node's states -/

/-- **The counter's add at `q`, owned at the `lock xadd` node's states**
(`TcbOk` with `own` at `tcbN q .rmw`'s states in the callee's region `R`
under its frame condition `F`). -/
structure TcbOkA (ms : MemSide isa) (F0 : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (q : TcbG) : Prop where
  next : StOk ms F0 (pnA (_root_.Executable.labels exe).label) (q.n0 + AllocTcb.tcbLen)
  own : ∀ s c, At exe endPc R F (tcbN (_root_.Executable.labels exe).label q .rmw) s c →
    (⟨pnA (_root_.Executable.labels exe).label, 8⟩, q.n0.setWidth 128) ∈ ms.own s

/-- `TcbOk` (owned at every state at the pc) gives `TcbOkA`. -/
theorem TcbOkA.of_tcbOk {ms : MemSide isa} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TcbG} (h : TcbOk ms F0 exe endPc q.n0) : TcbOkA ms F0 exe endPc R F q :=
  ⟨h.next, fun s _ hA => h.own s hA.1 hA.2.1 hA.2.2.2.1⟩

/-- `TcbOkA` under a stronger frame condition. -/
theorem TcbOkA.mono {ms : MemSide isa} {F0 F F' : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TcbG} (h : TcbOkA ms F0 exe endPc R F q) (hFF : ∀ m, F' m → F m) :
    TcbOkA ms F0 exe endPc R F' q :=
  ⟨h.next, fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.own s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩⟩

/-- **The take's four own-word accesses at `q`, owned at the nodes' states**
(`TakeOk` with `ownLock`, `ownFreeN`, `ownNext` at `takeNG q b .swp`'s,
`.ldn`'s, `.nxt`'s states in the callee's region `R` under its frame
condition `F`). -/
structure TakeOkA (ms : MemSide isa) (F0 : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (q : TakeG) : Prop where
  lock1 : StOk ms F0 (lockA (_root_.Executable.labels exe).label) 1#64
  freeN : LdOk ms F0 (freeNA (_root_.Executable.labels exe).label)
  lock0 : StOk ms F0 (lockA (_root_.Executable.labels exe).label) 0#64
  next : StOk ms F0 (nextA (_root_.Executable.labels exe).label) (q.k0 + StackTake.size0)
  ownLock : ∀ b s c, At exe endPc R F (takeNG (_root_.Executable.labels exe).label q b .swp) s c →
    (⟨lockA (_root_.Executable.labels exe).label, 8⟩, (0#64).setWidth 128) ∈ ms.own s
  ownFreeN : ∀ b s c, At exe endPc R F (takeNG (_root_.Executable.labels exe).label q b .ldn) s c →
    (⟨freeNA (_root_.Executable.labels exe).label, 8⟩, (0#64).setWidth 128) ∈ ms.own s
  ownNext : ∀ b s c, At exe endPc R F (takeNG (_root_.Executable.labels exe).label q b .nxt) s c →
    (⟨nextA (_root_.Executable.labels exe).label, 8⟩, q.k0.setWidth 128) ∈ ms.own s

/-- `TakeOk` (owned at every state at the pcs) gives `TakeOkA`. -/
theorem TakeOkA.of_takeOk {ms : MemSide isa} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TakeG} (h : TakeOk ms F0 exe endPc q.k0) : TakeOkA ms F0 exe endPc R F q :=
  ⟨h.lock1, h.freeN, h.lock0, h.next, fun _ s _ hA => h.ownLock s hA.1 hA.2.1 hA.2.2.2.1,
    fun _ s _ hA => h.ownFreeN s hA.1 hA.2.1 hA.2.2.2.1, fun _ s _ hA => h.ownNext s hA.1 hA.2.1 hA.2.2.2.1⟩

/-- `TakeOkA` under a stronger frame condition. -/
theorem TakeOkA.mono {ms : MemSide isa} {F0 F F' : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TakeG} (h : TakeOkA ms F0 exe endPc R F q) (hFF : ∀ m, F' m → F m) :
    TakeOkA ms F0 exe endPc R F' q :=
  ⟨h.lock1, h.freeN, h.lock0, h.next,
    fun b s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.ownLock b s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩,
    fun b s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.ownFreeN b s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩,
    fun b s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.ownNext b s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩⟩

end Spike.Lib.X64.Rt

/-- info: 'Spike.Lib.X64.Rt.ownXadd_ndWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ownXadd_ndWA

/-- info: 'Spike.Lib.X64.Rt.ownXchg_ndWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ownXchg_ndWA

/-- info: 'Spike.Lib.X64.Rt.ownLd_ndWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ownLd_ndWA

/-- info: 'Spike.Lib.X64.Rt.TcbOkA.of_tcbOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TcbOkA.of_tcbOk

/-- info: 'Spike.Lib.X64.Rt.TcbOkA.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TcbOkA.mono

/-- info: 'Spike.Lib.X64.Rt.TakeOkA.of_takeOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TakeOkA.of_takeOk

/-- info: 'Spike.Lib.X64.Rt.TakeOkA.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TakeOkA.mono
