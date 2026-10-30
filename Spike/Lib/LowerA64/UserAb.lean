/-
**A user block's states keep the write abort's phase** (AArch64): `hab` of
the `W2` block consumers (`Spike/Lib/LowerA64/W2Body.lean`), i.e.
`BlkW (fun s _ => AbSt μ (WriteAb.Ab lab) s) …`, for a covered block whose
every target is a position off the write abort (`PosOff`), or the
dispatcher's entry reached by a `bl scc_rt_abort` with `x0 ≠ 4` (the
dispatcher's prologue is in `Ab` only at `x0 = 4`). No pc table: a position
`(L, j)` in a run of a label `L` outside the write abort's labels (`abLabs`)
is none of `WriteAb.abPcs` (`pc_ne_of_inRun`, `abPos_inRun`).

- `PosOff`: `t` is `lab L + 4 j` for an instruction `(L, j)` of a run, `L`
  none of `AllocG.abLabs`.
- `notAbPc_of_posOff`: such a pc is off `abPcs`.
- `not_ab_abortEntry`: the dispatcher's entry at `x0 ≠ 4` is off `Ab`.
- `posOff_of_blockAt`, `posOff_of_labelGap`, `local_not_abLabs`: the
  positions of a block, a label right before another, and a context's local
  labels outside the runtime's functions 9, 12, 16.
- `blkW_abSt_pos`: the consumers' `hab` from `InstOk`, the block's code and
  phase check, no `ret`, and every target `PosOff` (or the abort's entry at
  `x0 ≠ 4`).
-/
import Spike.Lib.LowerA64.AllocRa
import Spike.Lib.A64AbSt
import Spike.Lib.A64AllocAbOk
import Spike.Lib.Rt.A64RtW

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Scc.Sem.A64 (pcOf)
open Scc.Emit.A64 (FnCtx)
open Spike.Lib.A64Consumer
open Spike.Lib.A64ConsumerA (AbSt blkW_abSt)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (blockAt labelGap InRun inRun_of_blockAt pc_ne_of_inRun Lays label_labelGap)
open Spike.Lib.A64.WriteAb (Ab abPcs not_ab_of_pc)
open Spike.Lib.A64.AllocG (abLabs abNoDispE)

/-! ## Positions off the write abort -/

/-- **`t` is a position off the write abort**: the address of the `j`-th
instruction of the run after a label `L` none of the write abort's labels. -/
def PosOff (prog : List Directive) (lab : Label → Int64) (t : Int64) : Prop :=
  ∃ L j, InRun prog L j ∧ L ∉ abLabs ∧ lab L + Int64.ofNat (4 * j) = t

/-- The write abort's positions are at its labels. -/
theorem abPos_abLabs : abPos.all (fun p => abLabs.contains p.1) = true := by decide

/-- **A position off the write abort is none of its pcs**, in a layout of a
program with the runtime's code. -/
theorem notAbPc_of_posOff {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {t : Int64}
    (h : PosOff prog (_root_.Executable.labels exe).label t) :
    t ∉ abPcs (_root_.Executable.labels exe).label := by
  obtain ⟨L, j, hr, hL, rfl⟩ := h
  rw [abPcs_eq, List.mem_map]
  rintro ⟨p, hp', he⟩
  refine pc_ne_of_inRun hp (abPos_inRun hpr hab p hp') hr ?_ he
  intro hpe
  have hc := List.all_eq_true.mp abPos_abLabs p hp'
  rw [congrArg Prod.fst hpe, List.contains_iff_mem] at hc
  exact hL hc

/-- The write abort's positions but the dispatcher's prologue. -/
def abPosN : List (Label × Nat) :=
  ((List.range 9).map fun j => (".L9_scc_rt_print.2_write", j + 6)) ++
  ((List.range 8).map fun j => (".L9_scc_rt_print.3_chk2", j)) ++
  ((List.range 4).map fun j => (".L9_scc_rt_print.4_chk3", j)) ++
  ((List.range 2).map fun j => (".L9_scc_rt_print.6_fail", j)) ++
  ((List.range 5).map fun j => (".L12_scc_rt_abort.0_entry", j)) ++
  ((List.range 5).map fun j => (".L12_scc_rt_abort.2_next1", j)) ++
  ((List.range 5).map fun j => (".L12_scc_rt_abort.4_next3", j)) ++
  ((List.range 4).map fun j => (".L12_scc_rt_abort.6_next5", j)) ++
  ((List.range 4).map fun j => (".L12_scc_rt_abort.7_is6", j)) ++
  ((List.range 4).map fun j => (Spike.Lib.A64.Abort.write.fn, j)) ++
  ((List.range 11).map fun j => (Spike.Lib.A64.Abort.write.entry, j)) ++
  [(Spike.Lib.A64.Abort.write.exit, 0)]

/-- `abPosN`'s positions are `abPos`'s, none at the dispatcher's label. -/
theorem abPosN_sub : abPosN.all (fun p => abPos.contains p && p.1 != "scc_rt_abort") = true := by decide

/-- **`abNoDispE` is `abPosN`'s positions' addresses.** -/
theorem abNoDispE_eq (lab : Label → Int64) :
    abNoDispE lab = abPosN.map fun p => lab p.1 + Int64.ofNat (4 * p.2) := by
  simp [abNoDispE, abPosN, Spike.Lib.A64.WriteAb.pcRet, Spike.Lib.A64.WriteAb.tailPcs,
    Spike.Lib.A64.WriteAb.failPcs, Spike.Lib.A64.WriteAb.dispTPcs, Spike.Lib.A64.WriteAb.g4Pcs,
    Spike.Lib.A64.WriteAb.stubPcs, Spike.Lib.A64.PrintD.pcSvc, List.range_succ, Int64.add_assoc]

/-- A state off `abNoDispE` and not at `x0 = 4` is off `Ab`. -/
theorem not_ab_of_noDispE {lab : Label → Int64} {s : State} (h : s.st.2 ∉ abNoDispE lab)
    (hx : s.st.1.regs.X0 ≠ 4) : ¬ Ab lab s := by
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

/-- **The dispatcher's entry at `x0 ≠ 4` is off the write abort**, in a
layout of a program with the runtime's code. -/
theorem not_ab_abortEntry {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {s : State}
    (hpc : s.st.2 = (_root_.Executable.labels exe).label "scc_rt_abort") (hx : s.st.1.regs.X0 ≠ 4) :
    ¬ Ab (_root_.Executable.labels exe).label s := by
  refine not_ab_of_noDispE ?_ hx
  have h0 : InRun prog "scc_rt_abort" 0 := abPos_inRun hpr hab ("scc_rt_abort", 0) (by decide)
  rw [hpc, abNoDispE_eq, List.mem_map]
  rintro ⟨p, hp', he⟩
  have hs := List.all_eq_true.mp abPosN_sub p hp'
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hs
  refine pc_ne_of_inRun hp (abPos_inRun hpr hab p hs.1) h0 ?_ (he.trans (add0 _).symm)
  intro hpe
  have hn := hs.2
  rw [congrArg Prod.fst hpe] at hn
  exact absurd hn (by decide)
where
  add0 (a : Int64) : a + Int64.ofNat (4 * 0) = a := ofNat4_zero a

/-! ## Positions from the code -/

/-- **A block's instructions are positions off the write abort** when its
label is none of the write abort's. -/
theorem posOff_of_blockAt {prog : List Directive} {lab : Label → Int64} {L : Label} {j : Nat}
    {b : List Directive} (h : blockAt prog L j b = true) (hL : L ∉ abLabs) {i : Nat} (hi : i < b.length) :
    PosOff prog lab (lab L + Int64.ofNat (4 * (j + i))) :=
  ⟨L, j + i, inRun_of_blockAt h hi, hL, rfl⟩

/-- **A label right before another's position** (`labelGap … 0`) is that
position. -/
theorem posOff_of_labelGap {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) {a b : Label} (hg : labelGap prog a b 0 = true)
    (h : PosOff prog (_root_.Executable.labels exe).label ((_root_.Executable.labels exe).label b)) :
    PosOff prog (_root_.Executable.labels exe).label ((_root_.Executable.labels exe).label a) := by
  have := label_labelGap hp hg
  rw [ofNat4_zero] at this
  rwa [this] at h

/-- The write abort's labels carry the runtime's function indices: none, 9,
12 or 16. -/
theorem abLabs_labNum : abLabs.all (fun l => [[], ['9'], ['1', '2'], ['1', '6']].contains (labNumL l)) = true := by
  decide

/-- **A context's local label is none of the write abort's**, for a function
index other than the runtime's 9, 12, 16. -/
theorem local_not_abLabs {cx : FnCtx} (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (sfx : String) :
    cx.local sfx ∉ abLabs := by
  intro hm
  have hn := List.all_eq_true.mp abLabs_labNum _ hm
  rw [labNumL_local] at hn
  have hd : ∀ n, Nat.toDigits 10 cx.fi = Nat.toDigits 10 n → cx.fi = n := fun n e => by
    rw [← Nat.ofDigitChars_ten_toDigits (n := cx.fi), e, Nat.ofDigitChars_ten_toDigits]
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hn
  rcases hn with hn | hn | hn | hn
  · exact Nat.toDigits_ne_nil hn
  · exact hfi.1 (hd 9 hn)
  · exact hfi.2.1 (hd 12 hn)
  · exact hfi.2.2 (hd 16 hn)

/-! ## The consumers' `hab` -/

/-- `bl` keeps `x0`. -/
theorem step_bl_X0 (o : SO) (fall : Int64) (L : Label) (σ : AS) :
    ((AI.bl L).step o fall σ).regs.X0 = σ.regs.X0 := rfl

/-- **A covered block's states keep the write abort's phase** (`blkW_abSt`'s
shape, the consumers' `hab`): at a block of code (`hcode`) covered at its
node's offsets (`hok`) passing its phase check (`hph`, so its pcs are off
the sites), with no `ret` (`hnr`), each of whose targets is a position off
the write abort or, for a `bl scc_rt_abort`, reached at `x0 ≠ 4` (`htgt`),
in a layout of a program with the runtime's code (`hI`, `hpr`, `hab`). -/
theorem blkW_abSt_pos {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool}
    {ra : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true) (hnr : noRetBlk blk = true)
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
      (fun r hr => (noRet_false hnr k hk r (hr ▸ ha)).elim)
    rcases htgt σ c hJ k hk a ha _ hmem with hp | ⟨rfl, hx⟩
    · exact not_ab_of_pc (hpc' ▸ notAbPc_of_posOff hlays hpr hab hp)
    · refine not_ab_abortEntry hlays hpr hab hpc' ?_
      rw [hA.regs, step_bl_X0]
      exact hx

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.not_ab_abortEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_ab_abortEntry

/-- info: 'Spike.Lib.LowerA64.blkW_abSt_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_pos

end Spike.Lib.LowerA64
