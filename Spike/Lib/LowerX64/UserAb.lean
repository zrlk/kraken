/-
**A user block's states keep the write abort's phase** (x86-64): `hab` of
the `W2` block consumers (`Spike/Lib/LowerX64/W2Body.lean`), i.e.
`BlkW (fun s _ => AbSt μ (WriteAb.Ab lab) s) …`, for a covered block whose
every target is a position off the write abort (`PosOff`), or the
dispatcher's entry reached by a `call scc_rt_abort` with `%rdi ≠ 4` (the
dispatcher's prologue is in `Ab` only at `%rdi = 4`). The x86-64 twin of
`Spike/Lib/LowerA64/UserAb.lean`: positions are byte offsets in a label's
run (`InRunB`, `pc_ne_of_inRunB`, `abPos_inRunB`).

- `PosOff`: `t` is `lab L + off` for a cell `(L, off)` of a run, `L` none
  of `AllocG.abLabs`.
- `notAbPc_of_posOff`: such a pc is off `abPcs`.
- `not_ab_abortEntry`: the dispatcher's entry at `%rdi ≠ 4` is off `Ab`.
- `posOff_of_blockAt`: the cells of a block at a label none of the write
  abort's.
- `blkW_abSt_pos`: the consumers' `hab` from `InstOk`, the block's code and
  phase check, no `ret`, and every target `PosOff` (or the abort's entry at
  `%rdi ≠ 4`).
-/
import Spike.Lib.LowerX64.AllocRa
import Spike.Lib.X64AbSt
import Spike.Lib.X64AllocAbOk
import Spike.Lib.Rt.X64RtW

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerA (AbSt blkW_abSt)
open Spike.Lib.X64
open Spike.Lib.X64.Rt (InstOk)
open Scc.Cert.Rt.X64 (blockAt InRunB inRunB_of_blockAt pc_ne_of_inRunB Lays)
open Spike.Lib.X64.WriteAb (Ab abPcs not_ab_of_pc)
open Spike.Lib.X64.AllocG (abLabs abNoDispE)

/-! ## Positions off the write abort -/

/-- **`t` is a position off the write abort**: the address of a cell `off`
bytes into the run after a label `L` none of the write abort's labels. -/
def PosOff (cells : List (Directive × Nat)) (lab : Label → Int64) (t : Int64) : Prop :=
  ∃ L off, InRunB cells L off ∧ L ∉ abLabs ∧ lab L + Int64.ofNat off = t

/-- The write abort's positions are at its labels. -/
theorem abPos_abLabs : abPos.all (fun p => abLabs.contains p.1) = true := by decide

/-- **A position off the write abort is none of its pcs**, in a layout of
cells with the runtime's code. -/
theorem notAbPc_of_posOff {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {t : Int64} (h : PosOff cells (_root_.Executable.labels exe).label t) :
    t ∉ abPcs (_root_.Executable.labels exe).label := by
  obtain ⟨L, off, hr, hL, rfl⟩ := h
  rw [abPcs_eq, List.mem_map]
  rintro ⟨p, hp', he⟩
  refine pc_ne_of_inRunB hp (abPos_inRunB hpr hab p hp') hr ?_ he
  intro hpe
  have hc := List.all_eq_true.mp abPos_abLabs p hp'
  rw [congrArg Prod.fst hpe, List.contains_iff_mem] at hc
  exact hL hc

/-- The write abort's positions but the dispatcher's prologue. -/
def abPosN : List (Label × Nat) :=
  [(".Lscc_rt_print.write", 22),
   (".Lscc_rt_print.write", 26), (".Lscc_rt_print.write", 30), (".Lscc_rt_print.write", 37),
   (".Lscc_rt_print.write", 40), (".Lscc_rt_print.write", 42),
   (".Lscc_rt_print.chk2", 0), (".Lscc_rt_print.chk2", 4), (".Lscc_rt_print.chk2", 11),
   (".Lscc_rt_print.chk2", 14), (".Lscc_rt_print.chk2", 16),
   (".Lscc_rt_print.chk3", 0), (".Lscc_rt_print.chk3", 4), (".Lscc_rt_print.chk3", 11),
   (".Lscc_rt_print.chk3", 14),
   (".Lscc_rt_print.fail", 0), (".Lscc_rt_print.fail", 7),
   (".Lscc_rt_abort.entry", 0), (".Lscc_rt_abort.entry", 4), (".Lscc_rt_abort.entry", 11),
   (".Lscc_rt_abort.entry", 14), (".Lscc_rt_abort.entry", 16),
   (".Lscc_rt_abort.next1", 0), (".Lscc_rt_abort.next1", 4), (".Lscc_rt_abort.next1", 11),
   (".Lscc_rt_abort.next1", 14), (".Lscc_rt_abort.next1", 16),
   (".Lscc_rt_abort.next3", 0), (".Lscc_rt_abort.next3", 4), (".Lscc_rt_abort.next3", 11),
   (".Lscc_rt_abort.next3", 14), (".Lscc_rt_abort.next3", 16),
   (".Lscc_rt_abort.next5", 0), (".Lscc_rt_abort.next5", 4), (".Lscc_rt_abort.next5", 11),
   (".Lscc_rt_abort.next5", 14),
   (".Lscc_rt_abort.is6", 0), (".Lscc_rt_abort.is6", 3), (".Lscc_rt_abort.is6", 4),
   (Spike.Lib.X64.Abort.write.fn, 0), (Spike.Lib.X64.Abort.write.fn, 1), (Spike.Lib.X64.Abort.write.fn, 4),
   (Spike.Lib.X64.Abort.write.entry, 0), (Spike.Lib.X64.Abort.write.entry, 7),
   (Spike.Lib.X64.Abort.write.entry, 11), (Spike.Lib.X64.Abort.write.entry, 18),
   (Spike.Lib.X64.Abort.write.entry, 22), (Spike.Lib.X64.Abort.write.entry, 29),
   (Spike.Lib.X64.Abort.write.entry, 34), (Spike.Lib.X64.Abort.write.entry, 36),
   (Spike.Lib.X64.Abort.write.entry, 40), (Spike.Lib.X64.Abort.write.entry, 47),
   (Spike.Lib.X64.Abort.write.exit, 0)]

/-- `abPosN`'s positions are `abPos`'s, none at the dispatcher's label. -/
theorem abPosN_sub : abPosN.all (fun p => abPos.contains p && p.1 != "scc_rt_abort") = true := by decide

/-- **`abNoDispE` is `abPosN`'s positions' addresses.** -/
theorem abNoDispE_eq (lab : Label → Int64) :
    abNoDispE lab = abPosN.map fun p => lab p.1 + Int64.ofNat p.2 := by
  simp only [abNoDispE, abPosN, Spike.Lib.X64.WriteAb.pcRet, Spike.Lib.X64.WriteAb.tailPcs,
    Spike.Lib.X64.WriteAb.failPcs, Spike.Lib.X64.WriteAb.dispTPcs,
    Spike.Lib.X64.WriteAb.g4Pcs, Spike.Lib.X64.WriteAb.stubPcs, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
  rfl

/-- A state off `abNoDispE` and not at `%rdi = 4` is off `Ab`. -/
theorem not_ab_of_noDispE {lab : Label → Int64} {s : State} (h : s.st.2 ∉ abNoDispE lab)
    (hx : s.st.1.regs.get64 .rdi ≠ 4#64) : ¬ Ab lab s := by
  unfold Ab abNoDispE at *
  simp only [List.mem_cons, List.mem_append, not_or] at h
  obtain ⟨⟨⟨⟨⟨h0, ht⟩, hf⟩, hd⟩, hg⟩, hs⟩ := h
  rintro (⟨h1, -⟩ | ⟨h1, -⟩ | h1 | ⟨-, h2⟩ | ⟨h1, -⟩ | h1 | h1)
  · exact h0 h1
  · exact ht h1
  · exact hf h1
  · exact hx h2
  · exact hd h1
  · exact hg h1
  · exact hs h1

/-- **The dispatcher's entry at `%rdi ≠ 4` is off the write abort**, in a
layout of cells with the runtime's code. -/
theorem not_ab_abortEntry {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {s : State} (hpc : s.st.2 = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hx : s.st.1.regs.get64 .rdi ≠ 4#64) :
    ¬ Ab (_root_.Executable.labels exe).label s := by
  refine not_ab_of_noDispE ?_ hx
  have h0 : InRunB cells "scc_rt_abort" 0 := abPos_inRunB hpr hab ("scc_rt_abort", 0) (by decide)
  rw [hpc, abNoDispE_eq, List.mem_map]
  rintro ⟨p, hp', he⟩
  have hs := List.all_eq_true.mp abPosN_sub p hp'
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hs
  refine pc_ne_of_inRunB hp (abPos_inRunB hpr hab p hs.1) h0 ?_
    (he.trans (by rw [show Int64.ofNat 0 = 0 by decide, Int64.add_zero]))
  intro hpe
  have hn := hs.2
  rw [congrArg Prod.fst hpe] at hn
  exact absurd hn (by decide)

/-! ## Positions from the code -/

/-- **A block's cells are positions off the write abort** when its label is
none of the write abort's. -/
theorem posOff_of_blockAt {cells : List (Directive × Nat)} {lab : Label → Int64} {L : Label} {k off : Nat}
    {b : List (Directive × Nat)} (h : blockAt cells L k off b = true) (hL : L ∉ abLabs) {i : Nat}
    (hi : i < b.length) :
    PosOff cells lab (lab L + Int64.ofNat (off + ((b.take i).map (·.2)).sum)) :=
  ⟨L, _, inRunB_of_blockAt h hi, hL, rfl⟩

/-! ## The consumers' `hab` -/

/-- `call` keeps `%rdi`. -/
theorem step_call_rdi (o : SO) (fall : Int64) (L : Label) (σ : AS) :
    ((AI.call L).step o fall σ).regs.get64 .rdi = σ.regs.get64 .rdi :=
  by simp [AI.step]

/-- **A covered block's states keep the write abort's phase** (`blkW_abSt`'s
shape, the consumers' `hab`): at a block of code (`hcode`) covered at its
node's offsets (`hok`) passing its phase check (`hph`, so its pcs are off
the sites), with no `ret` (`hnr`), each of whose targets is a position off
the write abort or, for a `call scc_rt_abort`, reached at `%rdi ≠ 4`
(`htgt`), in a layout of cells with the runtime's code (`hI`, `hpr`,
`hab`). -/
theorem blkW_abSt_pos {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    {dead : Nat → Bool} {ra : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true) (hnr : noRetBlk blk = true)
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
      (fun hr => (noRet_false hnr k hk (hr ▸ ha)).elim)
    rcases htgt σ c hJ k hk a ha _ hmem with hp | ⟨rfl, hx⟩
    · exact not_ab_of_pc (hpc' ▸ notAbPc_of_posOff hlays hpr hab hp)
    · refine not_ab_abortEntry hlays hpr hab hpc' ?_
      rw [hA.regs, step_call_rdi]
      exact hx

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.not_ab_abortEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_ab_abortEntry

/-- info: 'Spike.Lib.LowerX64.blkW_abSt_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_pos

end Spike.Lib.LowerX64
