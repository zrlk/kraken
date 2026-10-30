/-
**The threads abort phase kept at a node's states** (AArch64): `AcSt μ Cl
Ac s`, the state's share of `AbortPathSC`'s `instrC`, `sysC`, `takeC`
(`Spike/Lib/A64ConsumerACorrect.lean`) for a phase `Ac` entered only at a
state `Cl` marks, the twin of `AbSt` (`Spike/Lib/A64SFactsA.lean`,
`Spike/Lib/A64AbSt.lean`).

- `AcSt`: off `Ac`, no instruction and no take enters it, and no system call
  off `Cl`.
- `AcSt.false`: with no phase; `AcSt.of_ac`: at a state in the phase.
- `AcSt.ofLeaves`: at a state off the take site and not at a system call,
  every leaf of the instruction's tree out of `Ac` when the state is.
- `blkW_acStN`: a covered block's states, every instruction's next state out
  of `Ac` when the state at the instruction is (`htgt`).

The phase itself and the checks deciding `htgt` for the spawn's refusal are
`Spike/Lib/A64ThreadsAb.lean` and `Spike/Lib/A64ThreadsAcSt.lean`.
-/
import Spike.Lib.A64SFactsA

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)

/-- **The threads abort phase's fields of the state alone**: off the phase
`Ac`, no instruction and no take enters it, and no system call at a state
`Cl` does not mark (`AbortPathSC.instrC`, `sysC`, `takeC`). -/
structure AcSt (μ : Marks) (Cl Ac : State → Prop) (s : State) : Prop where
  acInstr : ¬ Ac s → abi.atSys s = false → ∀ tree,
    isaLSE2.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ac s')
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
    (hl : ¬ Ac s → ∀ tree, isaLSE2.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ac s')) :
    AcSt μ Cl Ac s :=
  ⟨fun hn _ t ht => hl hn t ht, fun _ h => (by rw [hsys] at h; cases h), fun _ a ha hpc => (htk a ha hpc).elim⟩

/-- **A covered block's states keep the threads abort phase**: its pcs off
the take site (`hpc`), every instruction's next state, at the abstract run's
next pc and registers, out of `Ac` when the state at the instruction is
(`htgt`). -/
theorem blkW_acStN {μ : Marks} {Cl Ac : State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hpc : ∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * k) →
      PcOff μ s)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k] = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = n.pc + Int64.ofNat (4 * k) →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so s0.st.1
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ → ¬ Ac s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ac s') :
    BlkW (fun s _ => AcSt μ Cl Ac s) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ hJ k hk m hA' _
  refine ⟨?_, fun _ h => h⟩
  have hP := hpc k hk { s with st := (m, n.pc + Int64.ofNat (4 * k)) } he hn rfl
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : Kraken.Promising.Lower.A64.CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s he hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  have hl : labA { s with st := (m, n.pc + Int64.ofNat (4 * k)) } = (_root_.Executable.labels exe).label := by
    show (_root_.Executable.labels s.exe).label = _; rw [he]
  obtain ⟨m', hex, hA'', -⟩ := exec_ai haok hR hal hlo hhi hc hreg hA'
  rw [hl] at hex
  refine AcSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc (AI.not_svc hreg)) fun hnac t ht => ?_
  rw [hex] at ht
  cases ht
  exact htgt σ c hJ k hk a hca { s with st := (m, n.pc + Int64.ofNat (4 * k)) } he hn rfl hA' hnac _ he hn rfl
    hA''

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64ConsumerA.AcSt.ofLeaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AcSt.ofLeaves

/-- info: 'Spike.Lib.A64ConsumerA.blkW_acStN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_acStN

end Spike.Lib.A64ConsumerA
