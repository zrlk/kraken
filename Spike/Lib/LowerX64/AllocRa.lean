/-
**A call's return-address facts for its callee** (x86-64): the twin of
`Spike/Lib/LowerA64/AllocRa.lean`. From a call's `call g` at `pc` (of size
`zc`) at `BlC2`, the callee's entry `lab g` is in the phase of the return
address `pc + zc` (`hra` of `scc_rt_alloc`'s `allocAb`), and the return
address is none of the write abort's pcs (`hraAb`): it is the return label's
first cell, a position in a run of a user function's return label
`.L<fn>.x<k>`, while every pc of `WriteAb.abPcs` is a position in a run of
a runtime label (`scc_rt_print`'s, `scc_rt_abort`'s or
`scc_rt_abort_write`'s); distinct positions sit at distinct pcs
(`pc_ne_of_inRunB`). No pc table: the labels are told apart by their names
(`retSfx`: a return label ends in `.x` and digits, no runtime label does).

- `BlC2`: `BlC` with the `call`'s pc in the phase of `ra` and a cell at the
  return label (`InRunB … 0`).
- `blC2_hra`: `ph (lab g) = ph (pc + zc)`.
- `blC2_ret`: `pc + zc` is the return label's address.
- `abPos`, `abPcs_eq`: the write abort's pcs as label-relative positions.
- `abPos_inRunB`: each in its label's run, from `printIn` and `abortIn`.
- `blC2_notAb`: `pc + zc ∉ abPcs lab`.
-/
import Spike.Lib.LowerX64.BlocksC1Code
import Spike.Lib.X64RunPc
import Spike.Lib.X64WriteAb
import Scc.Cert.Rt.X64Abort

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Emit.X64 (i64 rel)
open Scc.Cert.Rt.X64 (blockAt blockAtB labelGap InRunB inRunB_of_blockAt pc_ne_of_inRunB Lays
  label_labelGap_lays blockAt_of_blockAtB)
open Spike.Lib.X64 (cellOff)
open Spike.Lib.X64.WriteAb (abPcs)

/-! ## The call predicate -/

/-- **A call's `call g` at `pc` for a callee's return-address facts**:
`BlC`, the `call`'s pc in the phase of `ra` (so the callee's label,
`blkPh`'s target, is too), and a cell at the return label (`InRunB`, so the
return address is a position in a run, told apart from the runtime's by
`pc_ne_of_inRunB`). -/
def BlC2 (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64)
    (fr : Scc.Emit.X64.Frame) (ra : Int64) (pc : Int64) (zc : Nat) (g : Label) (k : Nat) : Prop :=
  BlC cells okPc ph lab fr ra pc zc g k ∧ ph pc.toBitVec.toNat = ph ra.toBitVec.toNat ∧
    InRunB cells s!".L{fr.fn}.x{k}" 0

theorem BlC2.toBlC {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {fr : Scc.Emit.X64.Frame} {ra pc : Int64} {zc : Nat} {g : Label} {k : Nat}
    (h : BlC2 cells okPc ph lab fr ra pc zc g k) : BlC cells okPc ph lab fr ra pc zc g k := h.1

/-! ## The callee's phase -/

/-- **The callee's entry is in the phase of the return address**: the
`call`'s target in the `call`'s phase (`blkPh`), the `call`'s pc in `ra`'s,
and `ra`'s the return label's (`BlC`). -/
theorem blC2_hra {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {fr : Scc.Emit.X64.Frame} {ra pc : Int64} {zc : Nat} {g : Label} {k : Nat}
    (h : BlC2 cells okPc ph lab fr ra pc zc g k) :
    ph (lab g).toBitVec.toNat = ph (pc + Int64.ofNat zc).toBitVec.toNat := by
  obtain ⟨⟨L, j, off, -, -, -, hb, h4⟩, hpc, -⟩ := h
  rw [h4, ← hpc]
  have hc : Spike.Lib.X64.classify (i64 (.call (rel g))) = some (Spike.Lib.X64.AI.call g) := rfl
  simp only [Spike.Lib.X64Consumer.blkPh, List.length_singleton, List.range_one, List.all_cons, List.all_nil,
    Bool.and_true, List.getElem?_cons_zero] at hb
  rw [hc] at hb
  simp [Spike.Lib.X64Consumer.aiTgts] at hb
  exact hb.2

/-- **The return address is the return label's**: `pc + zc`, the label
after the `call`'s label `L` by the `call`'s offset and size (`labelGap`). -/
theorem blC2_ret {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
    {kp : Nat} (hp : Lays exe cells kp) {okPc : Nat → Bool} {ph : Nat → Nat} {fr : Scc.Emit.X64.Frame}
    {ra pc : Int64} {zc : Nat} {g : Label} {k : Nat}
    (h : BlC2 cells okPc ph (_root_.Executable.labels exe).label fr ra pc zc g k) :
    pc + Int64.ofNat zc = (_root_.Executable.labels exe).label s!".L{fr.fn}.x{k}" + Int64.ofNat 0 := by
  obtain ⟨⟨L, j, off, hL, -, hg, -⟩, -⟩ := h
  rw [label_labelGap_lays hp hg, ← hL, show Int64.ofNat 0 = 0 by decide, Int64.add_zero, Int64.add_assoc,
    Int64.ofNat_add]

/-! ## The write abort's pcs by position -/

/-- The write abort's pcs (`abPcs`) as positions `(label, byte offset)`. -/
def abPos : List (Label × Nat) :=
  [(".Lscc_rt_print.write", 22),
   (".Lscc_rt_print.write", 26), (".Lscc_rt_print.write", 30), (".Lscc_rt_print.write", 37),
   (".Lscc_rt_print.write", 40), (".Lscc_rt_print.write", 42),
   (".Lscc_rt_print.chk2", 0), (".Lscc_rt_print.chk2", 4), (".Lscc_rt_print.chk2", 11),
   (".Lscc_rt_print.chk2", 14), (".Lscc_rt_print.chk2", 16),
   (".Lscc_rt_print.chk3", 0), (".Lscc_rt_print.chk3", 4), (".Lscc_rt_print.chk3", 11),
   (".Lscc_rt_print.chk3", 14),
   (".Lscc_rt_print.fail", 0), (".Lscc_rt_print.fail", 7),
   ("scc_rt_abort", 0), ("scc_rt_abort", 1), ("scc_rt_abort", 4), ("scc_rt_abort", 8),
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

/-- **The write abort's pcs are `abPos`'s positions' addresses.** -/
theorem abPcs_eq (lab : Label → Int64) :
    abPcs lab = abPos.map fun p => lab p.1 + Int64.ofNat p.2 := by
  simp only [abPcs, abPos, Spike.Lib.X64.WriteAb.pcRet, Spike.Lib.X64.WriteAb.tailPcs,
    Spike.Lib.X64.WriteAb.failPcs, Spike.Lib.X64.WriteAb.dispEPcs, Spike.Lib.X64.WriteAb.dispTPcs,
    Spike.Lib.X64.WriteAb.g4Pcs, Spike.Lib.X64.WriteAb.stubPcs, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
  rfl

/-- The runtime's blocks covering `abPos`, at their labels and byte offsets. -/
def abBlks : List (Label × Nat × List (Directive × Nat)) :=
  [(".Lscc_rt_print.write", 22, Spike.Lib.X64.Print.x5), (".Lscc_rt_print.write", 42, Spike.Lib.X64.Print.x6),
   (".Lscc_rt_print.chk2", 0, Spike.Lib.X64.Print.x7), (".Lscc_rt_print.chk2", 16, Spike.Lib.X64.Print.x8),
   (".Lscc_rt_print.chk3", 0, Spike.Lib.X64.Print.x9), (".Lscc_rt_print.fail", 0, Spike.Lib.X64.Print.x12),
   ("scc_rt_abort", 0, Spike.Lib.X64.Abort.Disp.d0),
   (".Lscc_rt_abort.entry", 0, Spike.Lib.X64.Abort.Disp.t1),
   (".Lscc_rt_abort.entry", 16, Spike.Lib.X64.Abort.Disp.j1),
   (".Lscc_rt_abort.next1", 0, Spike.Lib.X64.Abort.Disp.t2),
   (".Lscc_rt_abort.next1", 16, Spike.Lib.X64.Abort.Disp.j2),
   (".Lscc_rt_abort.next3", 0, Spike.Lib.X64.Abort.Disp.t3),
   (".Lscc_rt_abort.next3", 16, Spike.Lib.X64.Abort.Disp.j3),
   (".Lscc_rt_abort.next5", 0, Spike.Lib.X64.Abort.Disp.t4),
   (".Lscc_rt_abort.is6", 0, Spike.Lib.X64.Abort.Disp.g4),
   (Spike.Lib.X64.Abort.write.fn, 0, Spike.Lib.X64.Abort.x0),
   (Spike.Lib.X64.Abort.write.entry, 0,
     [((Spike.Lib.X64.Abort.siMsg Spike.Lib.X64.Abort.write).toDir, 7)]),
   (Spike.Lib.X64.Abort.write.entry, 7, Spike.Lib.X64.Abort.x1Write),
   (Spike.Lib.X64.Abort.write.entry, 34, [(op64 .syscall, 2)]),
   (Spike.Lib.X64.Abort.write.entry, 36, Spike.Lib.X64.Abort.x2),
   (Spike.Lib.X64.Abort.write.exit, 0, [(op64 .syscall, 2)])]

/-- Every position of `abPos` starts a cell of a block of `abBlks`. -/
theorem abPos_covered : abPos.all (fun p => abBlks.any fun b =>
    b.1 == p.1 && (List.range b.2.2.length).any fun i => b.2.1 + cellOff b.2.2 i == p.2) = true := by
  decide

/-- **`abBlks` are in cells with the runtime's code.** -/
theorem abBlks_in {cells : List (Directive × Nat)} (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) :
    ∀ b ∈ abBlks, blockAtB cells b.1 b.2.1 b.2.2 = true := by
  simp only [Scc.Cert.Rt.X64.Print.printIn, Scc.Cert.Rt.X64.Abort.abortIn, Scc.Cert.Rt.X64.Abort.stubIn,
    Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true] at hpr hab
  simp [abBlks, hpr, hab]

/-- **Each of the write abort's positions is in its label's run.** -/
theorem abPos_inRunB {cells : List (Directive × Nat)} (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) : ∀ p ∈ abPos, InRunB cells p.1 p.2 := by
  intro p hp
  obtain ⟨b, hb, hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp abPos_covered p hp)
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨e, hc⟩ := hc
  obtain ⟨i, hi, he⟩ := List.any_eq_true.mp hc
  rw [List.mem_range] at hi
  obtain ⟨k, hk⟩ := blockAt_of_blockAtB (abBlks_in hpr hab b hb)
  have := inRunB_of_blockAt hk hi
  rw [beq_iff_eq] at he
  rwa [e, show b.2.1 + ((b.2.2.take i).map (·.2)).sum = p.2 from he] at this

/-! ## Return labels by name -/

/-- A label ending in `.x` and digits (a return label's shape). -/
def retSfx (l : String) : Bool :=
  match l.toList.reverse.dropWhile Char.isDigit with
  | 'x' :: '.' :: _ => true
  | _ => false

/-- **A return label has the return labels' shape.** -/
theorem retSfx_ret (fn : String) (k : Nat) : retSfx s!".L{fn}.x{k}" = true := by
  have e : (s!".L{fn}.x{k}").toList.reverse =
      (Nat.toDigits 10 k).reverse ++ ('x' :: '.' :: (fn.toList.reverse ++ ['L', '.'])) := by
    simp [String.toList_append, Nat.toString_eq_repr, Nat.toList_repr]
    rfl
  rw [retSfx, e, List.dropWhile_append_of_pos (fun c hc =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) (List.mem_reverse.mp hc))]
  rfl

/-- The write abort's labels do not have the return labels' shape. -/
theorem abPos_retSfx : abPos.all (fun p => !retSfx p.1) = true := by decide

/-! ## The return address is off the write abort -/

/-- **A call's return address is none of the write abort's pcs**, in a
layout of cells with the runtime's code. -/
theorem blC2_notAb {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {okPc : Nat → Bool} {ph : Nat → Nat} {fr : Scc.Emit.X64.Frame} {ra pc : Int64} {zc : Nat} {g : Label}
    {k : Nat} (h : BlC2 cells okPc ph (_root_.Executable.labels exe).label fr ra pc zc g k) :
    pc + Int64.ofNat zc ∉ abPcs (_root_.Executable.labels exe).label := by
  rw [blC2_ret hp h, abPcs_eq, List.mem_map]
  rintro ⟨p, hp', he⟩
  refine pc_ne_of_inRunB hp (abPos_inRunB hpr hab p hp') h.2.2 ?_ he
  intro hpe
  have hl : p.1 = s!".L{fr.fn}.x{k}" := congrArg Prod.fst hpe
  have hn := List.all_eq_true.mp abPos_retSfx p hp'
  rw [hl, retSfx_ret] at hn
  cases hn

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.blC2_notAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blC2_notAb

end Spike.Lib.LowerX64
