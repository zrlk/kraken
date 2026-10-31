/-
**The threads abort phase kept at a node's states** (x86-64): `AcSt μ Cl
Ac s`, the state's share of `AbortPathSC`'s `instrC`, `sysC`, `takeC`
(`Spike/Lib/X64ConsumerACorrect.lean`) for a phase `Ac` entered only at a
state `Cl` marks, the twin of `AbSt` (`Spike/Lib/X64SFactsA.lean`,
`Spike/Lib/X64AbSt.lean`). The x86-64 twin of `Spike/Lib/A64AcSt.lean`.

- `AcSt`: off `Ac`, no instruction and no take enters it, and no system call
  off `Cl`.
- `AcSt.false`: with no phase; `AcSt.of_ac`: at a state in the phase.
- `AcSt.ofLeaves`: at a state off the take site and not at a system call,
  every leaf of the instruction's tree out of `Ac` when the state is.
- `blkW_acStN`: a covered block's states, every instruction's next state out
  of `Ac` when the state at the instruction is (`htgt`).

Where x86-64 differs from AArch64 (as in `Spike/Lib/X64AbSt.lean`):
instructions have their cells' sizes (`cellOff blk k`, `blk[k].2`), a target
reads the offsets (`a.tgt lab so`), and `exec_ai` needs no alignment.
-/
import Spike.Lib.X64AbSt

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64

/-- **The threads abort phase's fields of the state alone**: off the phase
`Ac`, no instruction and no take enters it, and no system call at a state
`Cl` does not mark (`AbortPathSC.instrC`, `sysC`, `takeC`). -/
structure AcSt (μ : Marks) (Cl Ac : State → Prop) (s : State) : Prop where
  acInstr : ¬ Ac s → abi.atSys s = false → ∀ tree,
    isa.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ac s')
  acSys : ¬ Ac s → abi.atSys s = true → ¬ Cl s → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, ¬ Ac s'
  acTake : ¬ Ac s → ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, ¬ Ac (abi.skip (abi.setDmem s m))

/-- `AcSt` with no threads abort phase. -/
theorem AcSt.false {μ : Marks} {Cl : State → Prop} {s : State} : AcSt μ Cl (fun _ => False) s :=
  ⟨fun _ _ tree _ => (allInv_true tree).mono fun _ _ h => h, fun _ _ _ _ _ _ _ h => h,
    fun _ _ _ _ _ h => h⟩

/-- `AcSt` at a state in the phase. -/
theorem AcSt.of_ac {μ : Marks} {Cl Ac : State → Prop} {s : State} (h : Ac s) : AcSt μ Cl Ac s :=
  ⟨fun hn => (hn h).elim, fun hn => (hn h).elim, fun hn => (hn h).elim⟩

/-- **The threads abort phase kept** at a state off the take site and not
at a system call whose instruction's every leaf is out of `Ac` when the
state is. -/
theorem AcSt.ofLeaves {μ : Marks} {Cl Ac : State → Prop} {s : State}
    (htk : ∀ a, μ.site .take = some a → pcOf s ≠ a) (hsys : abi.atSys s = Bool.false)
    (hl : ¬ Ac s → ∀ tree, isa.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ac s')) :
    AcSt μ Cl Ac s :=
  ⟨fun hn _ t ht => hl hn t ht, fun _ h => (by rw [hsys] at h; cases h), fun _ a ha hpc => (htk a ha hpc).elim⟩

/-- **A covered block's states keep the threads abort phase**: its pcs off
the take site (`hpc`), every instruction's next state, at the abstract run's
next pc and registers, out of `Ac` when the state at the instruction is
(`htgt`). -/
theorem blkW_acStN {μ : Marks} {Cl Ac : State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hpc : ∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk k) → PcOff μ s)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k].1 = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = n.pc + Int64.ofNat (cellOff blk k) →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so s0.st.1
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ → ¬ Ac s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ac s') :
    BlkW (fun s _ => AcSt μ Cl Ac s) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ hJ k hk m hA' _
  refine ⟨?_, fun _ h => h⟩
  have hP := hpc k hk { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } he hn rfl
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hd : blk[k]? = some (a.toDir, blk[k].2) := by rw [List.getElem?_eq_getElem hk, ← hdir]
  have hc : Kraken.Promising.Lower.X64.CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) }
      a.toDir blk[k].2 :=
    (hcode s he hn).cell hd rfl rfl rfl
  have hl : Kraken.Promising.Lower.X64.labelAddr { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } =
      (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels s.exe).label L = _; rw [he]
  obtain ⟨m', hex, hA'', -⟩ := exec_ai haok hR hlo hhi hc hreg hA'
  rw [hl] at hex
  refine AcSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc (AI.not_syscall hreg)) fun hnac t ht => ?_
  rw [hex] at ht
  cases ht
  exact htgt σ c hJ k hk a hca { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } he hn rfl hA' hnac _ he
    hn rfl hA''

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64ConsumerA.AcSt.ofLeaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AcSt.ofLeaves

/-- info: 'Spike.Lib.X64ConsumerA.blkW_acStN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_acStN

end Spike.Lib.X64ConsumerA
