/-
**An own word's load through the thread pointer** (x86-64): the node at
`movq %fs:k, %d` (`fsld_ndW`, `Spike/Lib/X64Nodes.lean`) when the thread
owns the word with value `v` (`OwnAt`, `Spike/Lib/X64RtNodes.lean`): `%d`
gets `v`, as at an own word's load `movq k(%b), %r` (`ownLd_ndW`). The
TCB's self pointer at `%fs:0` (`scc_rt_park`'s first load) is such a word:
runtime words start at `0` (`Scc/Cert/Rt/RtInitX64.lean`), so no sound
value invariant `G` pins it, but the thread that wrote it owns it.

- `ownFsld_ndW`, `ownFsld_nd`: the node.
-/
import Spike.Lib.X64RtNodes

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at an own word's load through the thread pointer**
`movq %fs:k, %d` (`d` not `%rsp`): from every state of the invariant the
address (the thread pointer plus `k`) is `A`, the runtime's, mapped for
reading and not in the thread's private memory, and the thread owns it with
value `v` (`hown`); after a local run of the source the state with `%d`
the value `v` (its offset forgotten) lands at a node. Its states lie in
`W`, and no outside move `K` moves them (`hW`). -/
theorem ownFsld_ndW {W : Frag isa} {K : State → State → Prop}
    {n : ND} {d : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hd : d ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fsDir d k, z)])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      σ.regs.fsBase.toBitVec + k.toBitVec = A ∧ ms.rt A.toNat ∧ ms.mp ⟨A, 8⟩ false ∧
      Mem.loadInt m.dmem A 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill d, fsStep d v σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (fsDir d k) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨hA0, hrt, hmp, hdm, c', hr, hL⟩ := hedge _ σ c hA hD hJ
  have ha : fsAddr s z { base := none, idx := none, disp := .int64 k } = A := by
    rw [← hA0]
    simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
  have hex := exec_movfs_load_agrees hc ha hdm (agrees_of_decls hdc _ _)
  refine .rtLoad _ _ _ c' hex hrt hmp hr fun w _ ho => ?_
  obtain rfl := ho _ (hown s he hn hpc)
  rw [setWidth_128_64]
  have hset : s.st.1.regs.set (Reg.low d .W64) v = s.st.1.regs.set64 d v := by
    cases d <;> rfl
  have hA' : Abs R (n.o.kill d) { s.st.1 with regs := s.st.1.regs.set64 d v } (fsStep d v σ) := by
    refine ⟨by simp only [fsStep, hA.regs], hA.zmms, hA.status, ?_, hA.slot⟩
    exact SORel.write (o := n.o) (d := d) (by simp [SO.write, hd]) hA.so fun r hr =>
      Reg64s.get64_set64_ne _ hr _
  have hD' : F { s.st.1 with regs := s.st.1.regs.set64 d v } := hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s z { s.st.1 with regs := s.st.1.regs.set (Reg.low d .W64) v } =
      { s with st := ({ s.st.1 with regs := s.st.1.regs.set64 d v }, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc, hset]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨x, hx⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨x, hx.at he hn hdc hA' hD'⟩

/-- **`ownFsld_ndW` inside the trivial predicate**, with no outside moves. -/
theorem ownFsld_nd {n : ND} {d : Reg64} {k : Int64} {z : Nat} {A v : BitVec 64} (hd : d ≠ .rsp)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fsDir d k, z)])
    (hown : OwnAt ms exe endPc n.pc A v)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      σ.regs.fsBase.toBitVec + k.toBitVec = A ∧ ms.rt A.toNat ∧ ms.mp ⟨A, 8⟩ false ∧
      Mem.loadInt m.dmem A 8 = none ∧
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill d, fsStep d v σ⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (ownFsld_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hd hF hcode hown hedge).toSeg

end Fn

end Spike.Lib.X64

/-- info: 'Spike.Lib.X64.ownFsld_ndW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ownFsld_ndW

/-- info: 'Spike.Lib.X64.ownFsld_nd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ownFsld_nd
