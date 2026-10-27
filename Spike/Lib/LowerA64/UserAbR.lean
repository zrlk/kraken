/-
**A user block ending in a `ret` keeps the write abort's phase** (AArch64):
`blkW_abSt_pos` and `blkW_abSt_subCdL` (`Spike/Lib/LowerA64/UserAb.lean`,
`Spike/Lib/LowerA64/UserAbC.lean`) with `ret`s allowed, each reached with the
return address `ra` in its register (`hret`) and `ra` a position off the
write abort: the `hab` of a function's return block (`main`'s, through the
held return tail, at the return into `scc_rt_main`).

- `blkW_abSt_posR`: `blkW_abSt_pos` with `ret`s;
- `blkW_abSt_subCdLR`: `blkW_abSt_subCdL` with `ret`s, the pc right after
  the part asked only when its last instruction is no `ret`.
-/
import Spike.Lib.LowerA64.UserAbC

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Spike.Lib.A64Consumer
open Spike.Lib.A64ConsumerA (AbSt blkW_abSt)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.WriteAb (Ab not_ab_of_pc)

/-- **A covered block with `ret`s keeps the write abort's phase**
(`blkW_abSt_pos` with the `ret`s reached at the return address `ra`,
`hret`): each target a position off the write abort or, for a
`bl scc_rt_abort`, reached at `x0 ≠ 4` (`htgt`). -/
theorem blkW_abSt_posR {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool}
    {ra : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k] = some a →
      ∀ t ∈ aiTgts lab (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a,
        PosOff prog lab t ∨ (a = .bl "scc_rt_abort" ∧ (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.X0 ≠ 4)) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  obtain ⟨hlays, -, rfl, -, hoff⟩ := hI
  refine blkW_abSt hcode hok hR hal hlo hhi (fun k hk s _ _ hs => (hoff s ?_).1) ?_
  · have := List.all_eq_true.mp hph k (List.mem_range.mpr hk)
    simp only [Bool.and_eq_true] at this
    show okPc s.st.2.toBitVec.toNat = true
    rw [hs]
    exact this.1.1
  · intro σ c hJ k hk a ha s' _ _ hpc' hA
    have hmem := aiTgt_mem (lab := (_root_.Executable.labels exe).label)
      (fall := n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) (ra := ra)
      (σ := (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) a
      (fun r hr => hret σ c hJ k hk r (hr ▸ ha))
    rcases htgt σ c hJ k hk a ha _ hmem with hp | ⟨rfl, hx⟩
    · exact not_ab_of_pc (hpc' ▸ notAbPc_of_posOff hlays hpr hab hp)
    · refine not_ab_abortEntry hlays hpr hab hpc' ?_
      rw [hA.regs, step_bl_X0]
      exact hx

/-- **A part of the code off the write abort's labels with `ret`s keeps the
write abort's phase** (`blkW_abSt_subCdL` with `ret`s, `blkW_abSt_posR`):
the `ret`s reached at `ra` (`hret`); every target other than an
instruction's fall-through, and every `ret`'s, a position off the write
abort or, for a `bl scc_rt_abort`, reached at `x0 ≠ 4` (`htgt`); the pc
right after the part a position off the write abort unless its last
instruction is a `ret` (`hend`). -/
theorem blkW_abSt_subCdLR {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int} {ra : Int64}
    (hcd : SubCd (CdCL prog okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hend : (∃ hne : blk ≠ [], ∃ r, classify (blk.getLast hne) = some (.ret r)) ∨
      PosOff prog lab (n.pc + Int64.ofNat (4 * blk.length)))
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k] = some a →
      ∀ t ∈ aiTgts lab (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a,
        (t ≠ n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4 ∨ ∃ r, a = .ret r) →
        PosOff prog lab t ∨ (a = .bl "scc_rt_abort" ∧ (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.X0 ≠ 4)) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  have hcd' := hcd
  obtain ⟨pc0, pre, suf, ⟨-, L, j, -, hpc0, hb, hrun⟩, hpc⟩ := hcd'
  have hph := Scc.Cert.Ph1A64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  rw [hpc] at hph
  have he : lab L + Int64.ofNat (4 * (j + pre.length)) = n.pc := by
    rw [← hpc, ← hpc0, ofNat4_add]
  have hcode := code_of hI.lays hI.endOk (blockAt_sub hb) (q := n.pc) (by rw [hI.labOk]; exact he)
  refine blkW_abSt_posR hI hpr hab hcode hok hR hal hlo hhi hph hret ?_
  intro σ c hJ k hk a ha t ht
  by_cases hr : ∃ r, a = .ret r
  · exact htgt σ c hJ k hk a ha t ht (.inr hr)
  by_cases hf : t = n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4
  · refine .inl ?_
    have hf' : t = n.pc + Int64.ofNat (4 * (k + 1)) := by rw [hf, ofNat4_succ]; rfl
    rw [hf']
    rcases Nat.lt_or_ge (k + 1) blk.length with h1 | h1
    · exact posOff_of_subCdL hcd h1
    · have hk1 : k + 1 = blk.length := by omega
      rw [hk1]
      rcases hend with ⟨hne, r, hl⟩ | hend
      · refine (hr ⟨r, ?_⟩).elim
        have hlast : blk.getLast hne = blk[k] := by
          rw [List.getLast_eq_getElem]; congr 1; omega
        rw [hlast, ha] at hl
        exact Option.some.inj hl
      · exact hend
  · exact htgt σ c hJ k hk a ha t ht (.inl hf)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.blkW_abSt_posR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_posR

/-- info: 'Spike.Lib.LowerA64.blkW_abSt_subCdLR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_subCdLR

end Spike.Lib.LowerA64
