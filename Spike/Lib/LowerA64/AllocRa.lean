/-
**A call's return-address facts for its callee** (AArch64): from a call's
`bl g` at `pc` at `BlC2` (`Spike/Lib/LowerA64/BlocksC2Seg.lean`), the
callee's entry `lab g` is in the phase of the return address `pc + 4`
(`hra` of `scc_rt_alloc`'s `allocAb`), and the return address is none of
the write abort's pcs (`hraAb`): it is the return label's first
instruction, a position in a run of a user function's local label, while
every pc of `WriteAb.abPcs` is a position in a run of a runtime label
(`scc_rt_print`'s, `scc_rt_abort`'s or `scc_rt_abort_write`'s); distinct
positions sit at distinct pcs (`pc_ne_of_inRun`). No pc table: the labels
are told apart by their names (`labNumL`).

- `blC2_hra`: `ph (lab g) = ph (pc + 4)`.
- `blC2_ret`: `pc + 4` is the return label's address.
- `abPos`, `abPcs_eq`: the write abort's pcs as label-relative positions.
- `abPos_inRun`: each in its label's run, from `printIn` and `abortIn`.
- `blC2_notAb`: `pc + 4 ∉ abPcs lab` for a caller's function index other
  than the runtime's 9, 12, 16.
-/
import Spike.Lib.LowerA64.BlocksC2Seg
import Spike.Lib.LowerA64.UserInj
import Spike.Lib.A64WriteAb
import Scc.Cert.Rt.A64Abort

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Emit.A64
open Scc.Cert.Rt.A64 (blockAt labelGap InRun inRun_of_blockAt pc_ne_of_inRun Lays label_labelGap)
open Spike.Lib.A64.WriteAb (abPcs)

/-! ## The callee's phase -/

/-- **The callee's entry is in the phase of the return address**: the
`bl`'s target in the `bl`'s phase (`blkPh`), the `bl`'s pc in `ra`'s, and
`ra`'s the return label's (`BlC`). -/
theorem blC2_hra {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {cx : FnCtx} {ra pc : Int64} {g : Label} {k : Nat} (h : BlC2 prog okPc ph lab cx ra pc g k) :
    ph (lab g).toBitVec.toNat = ph (pc + 4).toBitVec.toNat := by
  obtain ⟨⟨L, j, -, -, -, hb, h4⟩, hpc, -⟩ := h
  rw [h4, ← hpc]
  have hc : Spike.Lib.A64.Flow.classify (Directive.instr ⟨.W64, .BL (.label g)⟩) = some (.bl g) := rfl
  simp only [Spike.Lib.A64Consumer.blkPh, List.length_singleton, List.range_one, List.all_cons, List.all_nil,
    Bool.and_true, List.getElem?_cons_zero] at hb
  rw [hc] at hb
  simp [Spike.Lib.A64Consumer.aiTgts] at hb
  exact hb.2

/-- **The return address is the return label's**: `pc + 4`, the label
`j + 1` instructions after the `bl`'s label `L` (`labelGap`). -/
theorem blC2_ret {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) {okPc : Nat → Bool} {ph : Nat → Nat} {cx : FnCtx} {ra pc : Int64} {g : Label}
    {k : Nat} (h : BlC2 prog okPc ph (_root_.Executable.labels exe).label cx ra pc g k) :
    pc + 4 = (_root_.Executable.labels exe).label (cx.local s!"sp{k}") + Int64.ofNat (4 * 0) := by
  obtain ⟨⟨L, j, hL, -, hg, -⟩, -⟩ := h
  rw [label_labelGap hp hg, ← hL, Spike.Lib.A64.Flow.ofNat4_succ, Spike.Lib.A64.Flow.ofNat4_zero]

/-! ## The write abort's pcs by position -/

/-- The write abort's pcs (`abPcs`) as positions `(label, instruction)`. -/
def abPos : List (Label × Nat) :=
  ((List.range 9).map fun j => (".L9_scc_rt_print.2_write", j + 5)) ++
  ((List.range 8).map fun j => (".L9_scc_rt_print.3_chk2", j)) ++
  ((List.range 4).map fun j => (".L9_scc_rt_print.4_chk3", j)) ++
  ((List.range 2).map fun j => (".L9_scc_rt_print.6_fail", j)) ++
  ((List.range 5).map fun j => ("scc_rt_abort", j)) ++
  ((List.range 5).map fun j => (".L12_scc_rt_abort.0_entry", j)) ++
  ((List.range 5).map fun j => (".L12_scc_rt_abort.2_next1", j)) ++
  ((List.range 5).map fun j => (".L12_scc_rt_abort.4_next3", j)) ++
  ((List.range 4).map fun j => (".L12_scc_rt_abort.6_next5", j)) ++
  ((List.range 4).map fun j => (".L12_scc_rt_abort.7_is6", j)) ++
  ((List.range 4).map fun j => (Spike.Lib.A64.Abort.write.fn, j)) ++
  ((List.range 11).map fun j => (Spike.Lib.A64.Abort.write.entry, j)) ++
  [(Spike.Lib.A64.Abort.write.exit, 0)]

/-- **The write abort's pcs are `abPos`'s positions' addresses.** -/
theorem abPcs_eq (lab : Label → Int64) :
    abPcs lab = abPos.map fun p => lab p.1 + Int64.ofNat (4 * p.2) := by
  simp [abPcs, abPos, Spike.Lib.A64.WriteAb.pcRet, Spike.Lib.A64.WriteAb.tailPcs,
    Spike.Lib.A64.WriteAb.failPcs, Spike.Lib.A64.WriteAb.dispEPcs, Spike.Lib.A64.WriteAb.dispTPcs,
    Spike.Lib.A64.WriteAb.g4Pcs, Spike.Lib.A64.WriteAb.stubPcs, Spike.Lib.A64.Print.pcSvc, List.range_succ,
    Int64.add_assoc]

/-- The runtime's blocks covering `abPos`, at their labels and offsets. -/
def abBlks : List (Label × Nat × List Directive) :=
  [(".L9_scc_rt_print.2_write", 5, Spike.Lib.A64.Print.b5), (".L9_scc_rt_print.2_write", 12, Spike.Lib.A64.Print.b6),
   (".L9_scc_rt_print.2_write", 13, Spike.Lib.A64.Print.b7),
   (".L9_scc_rt_print.3_chk2", 0, Spike.Lib.A64.Print.b8), (".L9_scc_rt_print.3_chk2", 6, Spike.Lib.A64.Print.b9),
   (".L9_scc_rt_print.3_chk2", 7, Spike.Lib.A64.Print.b10),
   (".L9_scc_rt_print.4_chk3", 0, Spike.Lib.A64.Print.b11), (".L9_scc_rt_print.6_fail", 0, Spike.Lib.A64.Print.b14),
   ("scc_rt_abort", 0, Spike.Lib.A64.Abort.Disp.d0),
   (".L12_scc_rt_abort.0_entry", 0, Spike.Lib.A64.Abort.Disp.t1), (".L12_scc_rt_abort.0_entry", 4, Spike.Lib.A64.Abort.Disp.j1),
   (".L12_scc_rt_abort.2_next1", 0, Spike.Lib.A64.Abort.Disp.t2), (".L12_scc_rt_abort.2_next1", 4, Spike.Lib.A64.Abort.Disp.j2),
   (".L12_scc_rt_abort.4_next3", 0, Spike.Lib.A64.Abort.Disp.t3), (".L12_scc_rt_abort.4_next3", 4, Spike.Lib.A64.Abort.Disp.j3),
   (".L12_scc_rt_abort.6_next5", 0, Spike.Lib.A64.Abort.Disp.t4), (".L12_scc_rt_abort.7_is6", 0, Spike.Lib.A64.Abort.Disp.g4),
   (Spike.Lib.A64.Abort.write.fn, 0, Spike.Lib.A64.Abort.b0),
   (Spike.Lib.A64.Abort.write.entry, 0, [(Spike.Lib.A64.Flow.SI.adrp .X9 Spike.Lib.A64.Abort.write.msg).toDir]),
   (Spike.Lib.A64.Abort.write.entry, 1, [(Spike.Lib.A64.Flow.SI.addLo12 .X9 .X9 Spike.Lib.A64.Abort.write.msg).toDir]),
   (Spike.Lib.A64.Abort.write.entry, 2, Spike.Lib.A64.Abort.b1Write), (Spike.Lib.A64.Abort.write.entry, 7, [Spike.Lib.A64.Flow.svcDir]),
   (Spike.Lib.A64.Abort.write.entry, 8, Spike.Lib.A64.Abort.b2), (Spike.Lib.A64.Abort.write.exit, 0, [Spike.Lib.A64.Flow.svcDir])]

/-- Every position of `abPos` is inside a block of `abBlks`. -/
theorem abPos_covered : abPos.all (fun p => abBlks.any fun b =>
    b.1 == p.1 && decide (b.2.1 ≤ p.2) && decide (p.2 < b.2.1 + b.2.2.length)) = true := by
  decide

/-- **`abBlks` are in a program with the runtime's code.** -/
theorem abBlks_in {prog : List Directive} (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) :
    ∀ b ∈ abBlks, blockAt prog b.1 b.2.1 b.2.2 = true := by
  simp only [Scc.Cert.Rt.A64.Print.printIn, Scc.Cert.Rt.A64.Abort.abortIn, Scc.Cert.Rt.A64.Abort.stubIn,
    Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true] at hpr hab
  simp [abBlks, hpr, hab]

/-- **Each of the write abort's positions is in its label's run.** -/
theorem abPos_inRun {prog : List Directive} (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) : ∀ p ∈ abPos, InRun prog p.1 p.2 := by
  intro p hp
  obtain ⟨b, hb, hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp abPos_covered p hp)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨e, h1⟩, h2⟩ := hc
  have := inRun_of_blockAt (abBlks_in hpr hab b hb) (i := p.2 - b.2.1) (by omega)
  rwa [e, show b.2.1 + (p.2 - b.2.1) = p.2 by omega] at this

/-- The write abort's labels carry the runtime's function indices: none, 9,
12 or 16. -/
theorem abPos_labNum : abPos.all (fun p => [[], ['9'], ['1', '2'], ['1', '6']].contains (labNumL p.1)) = true := by
  decide

/-! ## The return address is off the write abort -/

/-- **A call's return address is none of the write abort's pcs**, for a
caller other than the runtime's `scc_rt_print`, `scc_rt_abort` and
`scc_rt_abort_write` (function indices 9, 12, 16), in a layout of a program
with the runtime's code. -/
theorem blC2_notAb {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {okPc : Nat → Bool} {ph : Nat → Nat} {cx : FnCtx}
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) {ra pc : Int64} {g : Label} {k : Nat}
    (h : BlC2 prog okPc ph (_root_.Executable.labels exe).label cx ra pc g k) :
    pc + 4 ∉ abPcs (_root_.Executable.labels exe).label := by
  rw [blC2_ret hp h, abPcs_eq, List.mem_map]
  rintro ⟨p, hp', he⟩
  refine pc_ne_of_inRun hp (abPos_inRun hpr hab p hp') h.2.2 ?_ he
  intro hpe
  have hl : p.1 = cx.local s!"sp{k}" := congrArg Prod.fst hpe
  have hn := List.all_eq_true.mp abPos_labNum p hp'
  rw [hl, labNumL_local] at hn
  have hd : ∀ n, Nat.toDigits 10 cx.fi = Nat.toDigits 10 n → cx.fi = n := fun n e => by
    rw [← Nat.ofDigitChars_ten_toDigits (n := cx.fi), e, Nat.ofDigitChars_ten_toDigits]
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hn
  rcases hn with hn | hn | hn | hn
  · exact Nat.toDigits_ne_nil hn
  · exact hfi.1 (hd 9 hn)
  · exact hfi.2.1 (hd 12 hn)
  · exact hfi.2.2 (hd 16 hn)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.blC2_notAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blC2_notAb

end Spike.Lib.LowerA64
