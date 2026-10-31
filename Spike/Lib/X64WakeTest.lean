/-
**`testq %a, %b` as a node that keeps its flags** (x64 wake.w port): the
clone's result test `testq %rax, %rax; je .child` reads the `ZF` the `test`
sets, so the `FI` row of `Spike/Lib/X64Flags.lean` (flags any `fl`) is too
weak there. Kraken's tree at a `test` is a choice of the `AF` bit only
(`exec_test_rr`, `Kraken/Promising/Lower/EventsX64Flags.lean`): every leaf
has the flags `logicFlags (a &&& b) af`, whose `ZF` is `a &&& b == 0`
(`logicFlags_zf`). So the abstract state after it is the registers
unchanged and those flags (`testStep`), for every `af` (`test_ndW`, the
`flag_ndW` of a `test`).

- `testDir a b`: the directive (`testq %b, %a`); `testStep a b σ af`.
- `exec_test`: Kraken's step as a silent tree over `af`.
- `test_ndW`, `test_nd`: the node.
- `testStep_zf`: the `ZF` after it.
-/
import Spike.Lib.X64Flags

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64

/-- `test %b, %a` (64-bit registers). -/
abbrev testDir (a b : Reg64) : Directive := op64 (.test (.reg (.low a .W64)) (.reg (.low b .W64)))

/-- The machine data after `test`: the flags of `a &&& b`, `AF` bit `af`. -/
abbrev testM (a b : Reg64) (m : MachineData) (af : Bool) : MachineData :=
  { m with status := logicFlags (m.regs.get64 a &&& m.regs.get64 b) af }

/-- **The abstract state after `test`**: registers unchanged, the flags of
`a &&& b` with `AF` bit `af`. -/
def testStep (a b : Reg64) (σ : AS) (af : Bool) : AS :=
  { σ with status := logicFlags (σ.regs.get64 a &&& σ.regs.get64 b) af }

/-- The `ZF` after `test`: the conjunction is zero. -/
@[simp] theorem testStep_zf (a b : Reg64) (σ : AS) (af : Bool) :
    (testStep a b σ af).status.zf = (σ.regs.get64 a &&& σ.regs.get64 b == 0#64) :=
  logicFlags_zf _ _

@[simp] theorem testStep_regs (a b : Reg64) (σ : AS) (af : Bool) : (testStep a b σ af).regs = σ.regs := rfl

@[simp] theorem testStep_slot (a b : Reg64) (σ : AS) (af : Bool) : (testStep a b σ af).slot = σ.slot := rfl

/-- **Kraken's step at `test`**: a silent tree whose every leaf is the flags
of `a &&& b` for some `AF` bit. -/
theorem exec_test {st : State} {a b : Reg64} {z : Nat} (hc : CellAt st (testDir a b) z) :
    ∃ t, isa.exec st = some t ∧ SilentTree (fun s' => ∃ af, s' = after st z (testM a b st.st.1 af)) t :=
  ⟨_, exec_test_rr hc, (silentTree_choose2 _).mono fun _ ⟨i, h⟩ => ⟨(i.val == 1), by
    rw [h]; simp only [testPost, Reg64s.get_low64]⟩⟩

theorem testStep_abs {a b : Reg64} {R : Region} {o : SO} {m : MachineData} {σ : AS} (hA : Abs R o m σ)
    (af : Bool) : Abs R o (testM a b m af) (testStep a b σ af) :=
  ⟨hA.regs, hA.zmms, by simp only [testStep, hA.regs], hA.so, hA.slot⟩

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at `test`**: from every state of the invariant, for every `AF`
bit, the state after it (flags of `a &&& b`) lands at a node, after a local
run of the source. Its states lie in `W`, and no outside move `K` moves
them (`hW`). -/
theorem test_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {a b : Reg64} {z : Nat}
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(testDir a b, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ σ c, n.J σ c → ∀ af,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o, testStep a b σ af⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (testDir a b) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨t, hex, hs⟩ := exec_test hc
  refine .choice _ t hex hs fun s' ⟨af, hs'⟩ => ?_
  obtain ⟨c', hr, hL⟩ := hedge σ c hJ af
  have hA' := testStep_abs (a := a) (b := b) hA af
  have hD' : F (testM a b s.st.1 af) := hF _ _ hD fun _ _ _ => rfl
  refine ⟨c', hr, ?_⟩
  subst hs'
  have hs1 : after s z (testM a b s.st.1 af) = { s with st := (testM a b s.st.1 af, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨x, hx⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨x, hx.at he hn hdc hA' hD'⟩

/-- **A node at `test`** (no `W`). -/
theorem test_nd {n : ND} {a b : Reg64} {z : Nat} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(testDir a b, z)])
    (hedge : ∀ σ c, n.J σ c → ∀ af,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o, testStep a b σ af⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (test_ndW (W := fun _ _ => True) (K := fun _ _ => False) hF hcode NodeW.triv hedge).toSeg

end Fn

section Parse

open Kraken.X64.Parser

/-- `testDir` is what Kraken's parser makes of scc's text. -/
example : parse("testq %rax, %rax") = [testDir .rax .rax] := by decide

end Parse

/-- info: 'Spike.Lib.X64.exec_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exec_test

/-- info: 'Spike.Lib.X64.test_ndW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms test_ndW

/-- info: 'Spike.Lib.X64.test_nd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms test_nd

/-- info: 'Spike.Lib.X64.testStep_zf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms testStep_zf

end Spike.Lib.X64
