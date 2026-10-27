/-
**The abort phase kept at a node's states** (x86-64): `AbSt μ Ab s`
(`Spike/Lib/X64SFactsA.lean`) at states whose every next state is out of
`Ab`, for the write abort's phase `WriteAb.Ab lab`
(`Spike/Lib/X64WriteAb.lean`) at code off its pcs. The x86-64 twin of
`Spike/Lib/A64AbSt.lean`.

- `AbSt.ofLeaves`: at a state off the take site and not at a system call,
  every leaf of the instruction's tree out of `Ab`.
- `blkW_abSt`: a covered block's states (`blkW_sfacts`' shape), every
  instruction's next state out of `Ab` (`htgt`).
- `blkAb`, `blkAb_sound`: `htgt` at `WriteAb.Ab lab` from a check that
  every target of every instruction (a `ret`'s the return address `ra`) is
  off `abPcs lab`.

Where x86-64 differs from AArch64: instructions have their cells' sizes
(`cellOff blk k`, `blk[k].2`), a target reads the offsets (`a.tgt lab so`),
a `ret`'s target is the slot at `%rsp`, and `exec_ai` needs no alignment.
-/
import Spike.Lib.X64SegInst
import Spike.Lib.X64SFactsA
import Spike.Lib.X64WriteAb

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64

/-- **The abort phase kept** at a state off the take site and not at a
system call whose instruction's every leaf is out of `Ab`. -/
theorem AbSt.ofLeaves {μ : Marks} {Ab : State → Prop} {s : State}
    (htk : ∀ a, μ.site .take = some a → pcOf s ≠ a) (hsys : abi.atSys s = Bool.false)
    (hl : ∀ tree, isa.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ab s')) :
    AbSt μ Ab s :=
  ⟨fun _ _ t ht => hl t ht, fun _ h => (by rw [hsys] at h; cases h), fun _ a ha hpc => (htk a ha hpc).elim⟩

/-- **A covered block's states keep the abort phase**: its pcs off the take
site (`hpc`), every instruction's next state, at the abstract run's next pc
and registers, out of `Ab` (`htgt`). -/
theorem blkW_abSt {μ : Marks} {Ab : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hpc : ∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk k) → PcOff μ s)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k].1 = some a → ∀ s' : State,
      s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ab s') :
    BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk := by
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
  refine AbSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc (AI.not_syscall hreg)) fun t ht => ?_
  rw [hex] at ht
  cases ht
  exact htgt σ c hJ k hk a hca _ he hn rfl hA''

/-- **A block's targets off the write abort's pcs**: every target of every
instruction (a `ret`'s the return address `ra`) is off `abPcs lab`. -/
def blkAb (lab : Label → Int64) (pc ra : Int64) (blk : List (Directive × Nat)) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some dz => match classify dz.1 with
      | some a => (aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2) ra a).all fun t =>
          !(Spike.Lib.X64.WriteAb.abPcs lab).contains t
      | none => false
    | none => false

/-- **`blkW_abSt`'s `htgt` at the write abort's phase from the check**,
every `ret` of the block returning to `ra` (`hret`). -/
theorem blkAb_sound {exe : _root_.Executable} {endPc : Int64} {R : Region} {n : ND}
    {blk : List (Directive × Nat)} {ra : Int64} (h : blkAb (_root_.Executable.labels exe).label n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp) = ra) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k].1 = some a → ∀ s' : State,
      s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label s' := by
  intro σ c hJ k hk a ha s' _ _ hpc' _
  refine Spike.Lib.X64.WriteAb.not_ab_of_pc ?_
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [List.getElem?_eq_getElem hk, ha] at this
  have ht := List.all_eq_true.mp this _ (aiTgt_mem a fun hr => hret σ c hJ k hk (hr ▸ ha))
  rw [hpc']
  simpa only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] using ht

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64ConsumerA.AbSt.ofLeaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AbSt.ofLeaves

/-- info: 'Spike.Lib.X64ConsumerA.blkW_abSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt

/-- info: 'Spike.Lib.X64ConsumerA.blkAb_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkAb_sound

end Spike.Lib.X64ConsumerA
