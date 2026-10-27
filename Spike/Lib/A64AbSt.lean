/-
**The abort phase kept at a node's states** (AArch64): `AbSt μ Ab s`
(`Spike/Lib/A64SFactsA.lean`) at states whose every next state is out of
`Ab`, for the write abort's phase `WriteAb.Ab lab`
(`Spike/Lib/A64WriteAb.lean`) at code off its pcs.

- `AbSt.ofLeaves`: at a state off the take site and not at a system call,
  every leaf of the instruction's tree out of `Ab`.
- `blkW_abSt`: a covered block's states (`blkW_sfacts`' shape), every
  instruction's next state out of `Ab` (`htgt`).
- `blkAb`, `blkAb_sound`: `htgt` at `WriteAb.Ab lab` from a check that
  every target of every instruction (a `ret`'s the return address `ra`) is
  off `abPcs lab`.
-/
import Spike.Lib.A64SegInst
import Spike.Lib.A64SFactsA
import Spike.Lib.A64WriteAb

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)

/-- **The abort phase kept** at a state off the take site and not at a
system call whose instruction's every leaf is out of `Ab`. -/
theorem AbSt.ofLeaves {μ : Marks} {Ab : State → Prop} {s : State}
    (htk : ∀ a, μ.site .take = some a → pcOf s ≠ a) (hsys : abi.atSys s = Bool.false)
    (hl : ∀ tree, isaLSE2.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ab s')) :
    AbSt μ Ab s :=
  ⟨fun _ _ t ht => hl t ht, fun _ h => (by rw [hsys] at h; cases h), fun _ a ha hpc => (htk a ha hpc).elim⟩

/-- **A covered block's states keep the abort phase**: its pcs off the take
site (`hpc`), every instruction's next state, at the abstract run's next pc
and registers, out of `Ab` (`htgt`). -/
theorem blkW_abSt {μ : Marks} {Ab : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hpc : ∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * k) →
      PcOff μ s)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k] = some a → ∀ s' : State,
      s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ab s') :
    BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk := by
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
  refine AbSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc (AI.not_svc hreg)) fun t ht => ?_
  rw [hex] at ht
  cases ht
  exact htgt σ c hJ k hk a hca _ he hn rfl hA''

/-- **A block's targets off the write abort's pcs**: every target of every
instruction (a `ret`'s the return address `ra`) is off `abPcs lab`. -/
def blkAb (lab : Label → Int64) (pc ra : Int64) (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match classify d with
      | some a => (aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a).all fun t =>
          !(Spike.Lib.A64.WriteAb.abPcs lab).contains t
      | none => false
    | none => false

/-- **`blkW_abSt`'s `htgt` at the write abort's phase from the check**,
every `ret` of the block returning to `ra` (`hret`). -/
theorem blkAb_sound {exe : _root_.Executable} {endPc : Int64} {R : Region} {n : ND} {blk : List Directive}
    {ra : Int64} (h : blkAb (_root_.Executable.labels exe).label n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed
        = ra) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k] = some a → ∀ s' : State,
      s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label s' := by
  intro σ c hJ k hk a ha s' _ _ hpc' _
  refine Spike.Lib.A64.WriteAb.not_ab_of_pc ?_
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [List.getElem?_eq_getElem hk, ha] at this
  have ht := List.all_eq_true.mp this _ (aiTgt_mem a fun r hr => hret σ c hJ k hk r (hr ▸ ha))
  rw [hpc']
  simpa only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] using ht

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64ConsumerA.AbSt.ofLeaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AbSt.ofLeaves

/-- info: 'Spike.Lib.A64ConsumerA.blkW_abSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt

/-- info: 'Spike.Lib.A64ConsumerA.blkAb_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkAb_sound

end Spike.Lib.A64ConsumerA
