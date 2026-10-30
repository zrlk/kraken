/-
**The runtime's own-word accesses, owned at the node's states** (AArch64):
`ownLdop_ndW`, `ownSwp_ndW`, `ownLdr_ndW` (`Spike/Lib/A64Ret0.lean`) with
their `OwnAt` (every state at the access's pc) weakened to the access node's
states, and the callees' memory-side facts in that form. A runtime callee
can run at one pc with different owned values (`scc_rt_alloc_tcb` twice in
wake.w), so `OwnAt` at one pc cannot hold at an owned-words map telling the
calls apart by `sp` (`ownG`). The node's states carry the call's frame, so
at them it can.

- `ownLdop_ndWA`, `ownSwp_ndWA`, `ownLdr_ndWA`: the node lemmas, `hown` at
  `At … n` only;
- `TcbOkA`: `TcbOk` with `own` at `tcbN q .rmw`'s states in the callee's
  region `R` under its frame condition `F`;
- `TakeOkA`: `TakeOk` with `ownLock`, `ownFreeN`, `ownNext` at
  `takeNG q b .swp`'s, `.ldn`'s, `.nxt`'s states;
- `.of_tcbOk`, `.of_takeOk`: the `OwnAt` forms give them; `.mono`: under a
  stronger frame condition.
-/
import Spike.Lib.A64Ret0

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0

set_option linter.unusedSimpArgs false

section OwnA

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

theorem ownLdop_ndWA {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {op : AtomicOp} {k : RmwKind}
    {rs rt b : XReg} {A v : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldopDir op k rs rt b])
    (hown : ∀ s c, At exe endPc R F n s c → (⟨A, 8⟩, v.setWidth 128) ∈ ms.own s)
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ m σ c, Spike.Lib.A64.Flow.Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧
      StOk ms F exe endPc A (op.apply v (σ.regs.getRegOrZr (.low (.reg rs) .W64))) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩ c) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hc : CellAt s (ldopDir op k rs rt b) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, hS, hL⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := exec_ldop hc (by rw [hb']; exact hS.unmapped _ hD)
  rw [hb', access_agrees (agrees_of_decls hdc _ _)] at hex
  refine .rtRmw k _ _ _ c hex hS.rt hS.mp (.refl c) fun old _ ho => ?_
  obtain rfl := ho _ (hown s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩)
  refine ⟨fun new hnew => ?_, ?_⟩
  · simp only [Option.some.injEq] at hnew
    subst hnew
    rw [setWidth_128_64, hA.regs]; exact hS.G
  · rw [setWidth_128_64]; exact land_ldStep hF he hn hdc hpc hA hD hL

/-- **A node at an own word's `swp<k> Xs, Xt, [Xn]`, owned at the node's
states** (`ownSwp_ndW` with `hown` at `At … n` only). -/
theorem ownSwp_ndWA {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {k : RmwKind} {rs rt b : XReg}
    {A v : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s n.pc [.instr ⟨.W64, .SWP k .W64 (.low (.reg rs) .W64) (.low (.reg rt) .W64) (.low (.reg b) .W64)⟩])
    (hown : ∀ s c, At exe endPc R F n s c → (⟨A, 8⟩, v.setWidth 128) ∈ ms.own s)
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ m σ c, Spike.Lib.A64.Flow.Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ StOk ms F exe endPc A (σ.regs.getRegOrZr (.low (.reg rs) .W64)) ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩ c) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hc : CellAt s (.instr ⟨.W64, .SWP k .W64 (.low (.reg rs) .W64) (.low (.reg rt) .W64) (.low (.reg b) .W64)⟩) 4 :=
    (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, hS, hL⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := exec_swp hc (by rw [hb']; exact hS.unmapped _ hD)
  rw [hb', access_agrees (agrees_of_decls hdc _ _)] at hex
  refine .rtRmw k _ _ _ c hex hS.rt hS.mp (.refl c) fun old _ ho => ?_
  obtain rfl := ho _ (hown s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩)
  refine ⟨fun new hnew => ?_, ?_⟩
  · simp only [Option.some.injEq] at hnew
    subst hnew
    rw [hA.regs]; exact hS.G
  · rw [setWidth_128_64]; exact land_ldStep hF he hn hdc hpc hA hD hL

/-- **A node at an own word's load `ldr Xt, [Xn, #i]`, owned at the node's
states** (`ownLdr_ndW` with `hown` at `At … n` only). -/
theorem ownLdr_ndWA {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {t b : XReg} {i : Int64}
    {A v : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldrDir t b i])
    (hown : ∀ s c, At exe endPc R F n s c → (⟨A, 8⟩, v.setWidth 128) ∈ ms.own s)
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ m σ c, Spike.Lib.A64.Flow.Abs R n.o m σ → F m → n.J σ c →
      rAddr σ.regs b i = A ∧ LdOk ms F exe endPc A ∧
      Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t v σ⟩ c) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hc : CellAt s (ldrDir t b i) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨ha, hS, hL⟩ := hedge _ σ c hA hD hJ
  have ha' : rAddr s.st.1.regs b i = A := by rw [hA.regs]; exact ha
  have hex := exec_ldr_agrees hc ha' (hS.unmapped _ hD) (agrees_of_decls hdc _ _)
  refine .rtLoad _ _ _ c hex hS.rt hS.mp (.refl c) fun w _ ho => ?_
  obtain rfl := ho _ (hown s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩)
  rw [setWidth_128_64]; exact land_ldStep hF he hn hdc hpc hA hD hL

end OwnA

/-! ## The callees' memory-side facts, owned at the node's states -/

/-- **The counter's add at `q`, owned at the `ldadd` node's states**
(`TcbOk` with `own` at `tcbN q .rmw`'s states in the callee's region `R`
under its frame condition `F`). -/
structure TcbOkA (ms : MemSide isaLSE2) (F0 : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (q : TcbG) : Prop where
  next : StOk ms F0 exe endPc (pnA (_root_.Executable.labels exe).label) (q.n0 + AllocTcb.tcbLen)
  own : ∀ s c, At exe endPc R F (tcbN (_root_.Executable.labels exe).label q .rmw) s c →
    (⟨pnA (_root_.Executable.labels exe).label, 8⟩, q.n0.setWidth 128) ∈ ms.own s

/-- `TcbOk` (owned at every state at the pc) gives `TcbOkA`. -/
theorem TcbOkA.of_tcbOk {ms : MemSide isaLSE2} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TcbG} (h : TcbOk ms F0 exe endPc q.n0) : TcbOkA ms F0 exe endPc R F q :=
  ⟨h.next, fun s _ hA => h.own s hA.1 hA.2.1 hA.2.2.2.1⟩

/-- `TcbOkA` under a stronger frame condition. -/
theorem TcbOkA.mono {ms : MemSide isaLSE2} {F0 F F' : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TcbG} (h : TcbOkA ms F0 exe endPc R F q) (hFF : ∀ m, F' m → F m) :
    TcbOkA ms F0 exe endPc R F' q :=
  ⟨h.next, fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.own s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩⟩

/-- **The take's four own-word accesses at `q`, owned at the nodes' states**
(`TakeOk` with `ownLock`, `ownFreeN`, `ownNext` at `takeNG q b .swp`'s,
`.ldn`'s, `.nxt`'s states in the callee's region `R` under its frame
condition `F`). -/
structure TakeOkA (ms : MemSide isaLSE2) (F0 : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (q : TakeG) : Prop where
  lock1 : StOk ms F0 exe endPc (lockA (_root_.Executable.labels exe).label) 1#64
  freeN : LdOk ms F0 exe endPc (freeNA (_root_.Executable.labels exe).label)
  lock0 : StOk ms F0 exe endPc (lockA (_root_.Executable.labels exe).label) 0#64
  next : StOk ms F0 exe endPc (nextA (_root_.Executable.labels exe).label) (q.k0 + StackTake.size0)
  ownLock : ∀ b s c, At exe endPc R F (takeNG (_root_.Executable.labels exe).label q b .swp) s c →
    (⟨lockA (_root_.Executable.labels exe).label, 8⟩, (0#64).setWidth 128) ∈ ms.own s
  ownFreeN : ∀ b s c, At exe endPc R F (takeNG (_root_.Executable.labels exe).label q b .ldn) s c →
    (⟨freeNA (_root_.Executable.labels exe).label, 8⟩, (0#64).setWidth 128) ∈ ms.own s
  ownNext : ∀ b s c, At exe endPc R F (takeNG (_root_.Executable.labels exe).label q b .nxt) s c →
    (⟨nextA (_root_.Executable.labels exe).label, 8⟩, q.k0.setWidth 128) ∈ ms.own s

/-- `TakeOk` (owned at every state at the pcs) gives `TakeOkA`. -/
theorem TakeOkA.of_takeOk {ms : MemSide isaLSE2} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TakeG} (h : TakeOk ms F0 exe endPc q.k0) : TakeOkA ms F0 exe endPc R F q :=
  ⟨h.lock1, h.freeN, h.lock0, h.next, fun _ s _ hA => h.ownLock s hA.1 hA.2.1 hA.2.2.2.1,
    fun _ s _ hA => h.ownFreeN s hA.1 hA.2.1 hA.2.2.2.1, fun _ s _ hA => h.ownNext s hA.1 hA.2.1 hA.2.2.2.1⟩

/-- `TakeOkA` under a stronger frame condition. -/
theorem TakeOkA.mono {ms : MemSide isaLSE2} {F0 F F' : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TakeG} (h : TakeOkA ms F0 exe endPc R F q) (hFF : ∀ m, F' m → F m) :
    TakeOkA ms F0 exe endPc R F' q :=
  ⟨h.lock1, h.freeN, h.lock0, h.next,
    fun b s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.ownLock b s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩,
    fun b s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.ownFreeN b s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩,
    fun b s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.ownNext b s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩⟩

end Spike.Lib.A64.Rt
