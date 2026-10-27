/-
**A user block ending in a `ret` keeps the write abort's phase** (x86-64;
the twin of `Spike/Lib/LowerA64/UserAbR.lean`): `blkW_abSt_pos` and
`blkW_abSt_subCdL` (`Spike/Lib/LowerX64/UserAb.lean`,
`Spike/Lib/LowerX64/UserAbC.lean`) with `ret`s allowed, each reached with the
return address `ra` at the stack's top (`hret`) and `ra` a position off the
write abort: the `hab` of a function's return block (`main`'s, through the
held return tail, at the return into `scc_rt_main`).

- `blkW_abSt_posR`: `blkW_abSt_pos` with `ret`s;
- `blkW_abSt_subCdLR`: `blkW_abSt_subCdL` with `ret`s, the pc right after
  the part asked only when its last cell is no `ret`.
-/
import Spike.Lib.LowerX64.UserAbC

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks)
open Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerA (AbSt blkW_abSt)
open Spike.Lib.X64
open Spike.Lib.X64.Rt (InstOk)
open Scc.Cert.Rt.X64 (blockAt)
open Spike.Lib.X64.WriteAb (Ab not_ab_of_pc)

/-- **A covered block with `ret`s keeps the write abort's phase**
(`blkW_abSt_pos` with the `ret`s reached at the return address `ra`,
`hret`): each target a position off the write abort or, for a
`call scc_rt_abort`, reached at `%rdi ≠ 4` (`htgt`). -/
theorem blkW_abSt_posR {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    {dead : Nat → Bool} {ra : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp) =
        ra)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a →
      ∀ t ∈ aiTgts lab (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) ra a,
        PosOff cells lab t ∨
          (a = .call "scc_rt_abort" ∧ (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64)) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  obtain ⟨hlays, -, rfl, -, hoff⟩ := hI
  refine blkW_abSt hcode hok hR hlo hhi (fun k hk s _ _ hs => (hoff s ?_).1) ?_
  · have := List.all_eq_true.mp hph k (List.mem_range.mpr hk)
    simp only [Bool.and_eq_true] at this
    show okPc s.st.2.toBitVec.toNat = true
    rw [hs]
    exact this.1.1
  · intro σ c hJ k hk a ha s' _ _ hpc' hA
    have hmem := aiTgt_mem (lab := (_root_.Executable.labels exe).label)
      (o := (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so)
      (fall := n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) (ra := ra)
      (σ := (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) a
      (fun hr => hret σ c hJ k hk (hr ▸ ha))
    rcases htgt σ c hJ k hk a ha _ hmem with hp | ⟨rfl, hx⟩
    · exact not_ab_of_pc (hpc' ▸ notAbPc_of_posOff hlays hpr hab hp)
    · refine not_ab_abortEntry hlays hpr hab hpc' ?_
      rw [hA.regs, step_call_rdi]
      exact hx

/-- **A part of the code off the write abort's labels with `ret`s keeps the
write abort's phase** (`blkW_abSt_subCdL` with `ret`s, `blkW_abSt_posR`):
the `ret`s reached at `ra` (`hret`); every target other than a cell's
fall-through, and every `ret`'s, a position off the write abort or, for a
`call scc_rt_abort`, reached at `%rdi ≠ 4` (`htgt`); the pc right after the
part a position off the write abort unless its last cell is a `ret`
(`hend`). -/
theorem blkW_abSt_subCdLR {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {ra : Int64}
    (hcd : SubCd (CdCL cells okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp) =
        ra)
    (hend : (∃ hne : blk ≠ [], classify (blk.getLast hne).1 = some .ret) ∨
      PosOff cells lab (n.pc + Int64.ofNat (cellOff blk blk.length)))
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a →
      ∀ t ∈ aiTgts lab (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) ra a,
        (t ≠ n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2 ∨ a = .ret) →
        PosOff cells lab t ∨
          (a = .call "scc_rt_abort" ∧ (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64)) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  have hcd' := hcd
  obtain ⟨pc0, pre, post, ⟨-, L, j, off, -, hpc0, hb, hrun⟩, hpc⟩ := hcd'
  have hc : cellOff (pre ++ blk ++ post) pre.length = (pre.map (·.2)).sum := by
    simp [cellOff]
  have hph := Scc.Cert.Ph1X64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  rw [hc, ← hpc] at hph
  have hpc' : lab L + Int64.ofNat (off + (pre.map (·.2)).sum) = n.pc := by
    rw [hpc, ← hpc0, Int64.ofNat_add, Int64.add_assoc]
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := by
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) (blockAt_sub hb)
    rwa [hI.labOk, hpc'] at this
  refine blkW_abSt_posR hI hpr hab hcode hok hR hlo hhi hph hret ?_
  intro σ c hJ k hk a ha t ht
  by_cases hr : a = .ret
  · exact htgt σ c hJ k hk a ha t ht (.inr hr)
  by_cases hf : t = n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2
  · refine .inl ?_
    have hf' : t = n.pc + Int64.ofNat (cellOff blk (k + 1)) := by
      rw [hf, cellOff_succ hk, Int64.ofNat_add, Int64.add_assoc]
    rw [hf']
    rcases Nat.lt_or_ge (k + 1) blk.length with h1 | h1
    · exact posOff_of_subCdL hcd h1
    · have hk1 : k + 1 = blk.length := by omega
      rw [hk1]
      rcases hend with ⟨hne, hl⟩ | hend
      · refine (hr ?_).elim
        have hlast : blk.getLast hne = blk[k] := by
          rw [List.getLast_eq_getElem]; congr 1; omega
        rw [hlast, ha] at hl
        exact Option.some.inj hl
      · exact hend
  · exact htgt σ c hJ k hk a ha t ht (.inl hf)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.blkW_abSt_posR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_posR

/-- info: 'Spike.Lib.LowerX64.blkW_abSt_subCdLR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_subCdLR

end Spike.Lib.LowerX64
