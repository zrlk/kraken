/-
**A call of `print`'s argument block and its `call` inside `W2`** (x86-64;
the twin of `Spike/Lib/LowerA64/PrintArgW2.lean`): `PrintBlkW`'s first four
conjuncts (`Spike/Lib/LowerX64/PrintCallC2.lean`) at the per-pair facts
`W2` (`Spike/Lib/LowerX64/SFactsA2.lean`), from the block's chunks at the
code predicates (`PrintCodeC` at `CdC`, `BlC`).

On x86-64 the argument block is four pieces (`PBlk`): the cells before the
multiply, the multiply `imulq` (a flag node, unclassified, so its own node),
the cells after it, and the `call scc_rt_print`. The chunks (one per IR
instruction) cut across them: the third chunk holds the multiply's operand
loads, the multiply and its store.

- `okBlk_nt`, `runPhB_fall`, `blkPh_of_run`: a covered block has no branch
  but its last; a run's fall-through keeps its phase; a run's phase check;
- `PrintArgW`, `PrintArgW.imp`, `PrintBlkW.of`: the four pieces' states in a
  fragment, and with `print`'s blocks `PrintBlkW`;
- `printPre_zip`, `printPost_zip`, `print_ph`: the pieces' cells and phase
  checks from the chunks' run checks;
- `nodeW_w2Fi`: a flag instruction's node at its code inside `W2`;
- `printArgW_w2`: the four pieces inside `W2` at the frames `fs`, their
  states at `PlacedSE` (`hP`), in the abort phase's facts (`hab`);
- `posOff_print`, `nodeW_abFi`, `printArgW_ab`: the pieces keep the write
  abort's phase (`hab`), the chunks at `CdCL`, the `call` at a position off
  the write abort, its target `print`'s entry;
- `frOk2_ret`, `printJ_hJ`: `printArgW_w2`'s `hJ` at `printJ` from `FrOk2`
  at its control (`frOk2_printC` for a nonempty slice, `frOk2_ret` for an
  empty one).
-/
import Spike.Lib.LowerX64.PrintW2
import Spike.Lib.LowerX64.UserAbC
import Spike.Lib.LowerX64.LaneW2
import Spike.Lib.LowerX64.StubAbW2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND AS At cellOff okBlk CodeAt classify AI)
open Spike.Lib.X64.Rt (InstOk next_same nodeW_postO)
open Spike.Lib.X64.AllocG (dumN)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Flow.Ret0.Inst (cfacts_c0)
open Scc.Cert.Ph1X64 (runPhB runPhB_get blkPh_of_runPhB)
open Scc.Emit.X64 (i64 rel Item)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.LowerShape (printInsts)
open Spike.Lib.X64.WriteAb (Ab abPcs)

set_option linter.unusedSimpArgs false

/-! ## Covered blocks and runs -/

/-- **No branch before the last instruction** of a covered block. -/
theorem okBlk_nt {lo hi : Int} : ∀ {o : Spike.Lib.X64.SO} {blk : List (Directive × Nat)},
    okBlk lo hi o blk = true → ∀ k (hk : k < blk.length), k + 1 < blk.length →
      ∀ a, classify blk[k].1 = some a → a.isTerm = false
  | _, [], _, k, hk, _, _, _ => absurd hk (Nat.not_lt_zero k)
  | o, (d, z) :: ds, h, k, hk, hk1, a, ha => by
    unfold okBlk at h
    split at h
    · rename_i a' ha'
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨⟨-, hterm⟩, hrest⟩ := h
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero] at ha
        rw [ha'] at ha
        cases ha
        rcases hterm with h2 | h2
        · subst h2; simp at hk1
        · exact h2
      | succ k =>
        exact okBlk_nt hrest k (by simp at hk; omega) (by simp at hk1; omega) a (by simpa using ha)
    · cases h

/-- **A run's fall-through keeps its phase**: past a cell `k` of a run
passing `runPhB` that is no branch, the next pc has the run's phase. -/
theorem runPhB_fall {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra : Int64}
    {blk : List (Directive × Nat)} (h : runPhB okPc ph lab pc ra blk = true) {k : Nat} (hk : k < blk.length)
    (hnt : ∀ a, classify blk[k].1 = some a → a.isTerm = false) :
    ph (pc + Int64.ofNat (cellOff blk (k + 1))).toBitVec.toNat = ph pc.toBitVec.toNat := by
  obtain ⟨-, -, ht⟩ := runPhB_get h hk
  rw [Spike.Lib.X64.cellOff_succ hk, Int64.ofNat_add, ← Int64.add_assoc]
  refine ht _ ?_
  cases hc : classify blk[k].1 with
  | none => simp
  | some a =>
    have := hnt a hc
    cases a <;> simp_all [aiTgts, AI.isTerm]

/-- **A run's phase check** (`blkPh_of_runPhB` on the whole run), its
instructions classified (`hc`). -/
theorem blkPh_of_run {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra : Int64}
    {blk : List (Directive × Nat)} (h : runPhB okPc ph lab pc ra blk = true)
    (hc : ∀ d ∈ blk, (classify d.1).isSome = true) :
    blkPh okPc ph (fun _ => false) lab pc ra blk = true := by
  simpa [cellOff] using blkPh_of_runPhB (xs := []) (zs := []) (by simpa using h) hc

/-! ## The four pieces -/

section Pieces

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The argument block's states in `W₀`**, not moved by `K`, at the
block's cells `B` from the invariant `J` (`PrintBlkW` without `print`'s
blocks): along the cells before the multiply, at the multiply, along the
cells after it, at the `call`. -/
def PrintArgW (W₀ : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fr : Scc.Emit.X64.Frame) (B : PBlk) (J : AS → Ctl → Prop) : Prop :=
  BlkW W₀ K exe endPc R F (B.n0 fr J) B.pre ∧
    NodeW W₀ K exe endPc R F (B.nM (_root_.Executable.labels exe).label fr J) ∧
    BlkW W₀ K exe endPc R F (B.n2 (_root_.Executable.labels exe).label fr J) B.post ∧
    BlkW W₀ K exe endPc R F (B.n3 (_root_.Executable.labels exe).label fr J) [(callD, B.zc)]

/-- **The pieces inside `W`** from two, the second not moved. -/
theorem PrintArgW.imp {W1 W2 W : Frag isa} {K : State → State → Prop} {fr : Scc.Emit.X64.Frame} {B : PBlk}
    {J : AS → Ctl → Prop} (h1 : PrintArgW W1 K exe endPc R F fr B J)
    (h2 : PrintArgW W2 (fun _ _ => False) exe endPc R F fr B J) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    PrintArgW W K exe endPc R F fr B J :=
  ⟨Spike.Lib.X64.AllocG.BlkW.imp h1.1 h2.1 hw,
    fun s c hA => ⟨hw s c (h1.2.1 s c hA).1 (h2.2.1 s c hA).1, (h1.2.1 s c hA).2⟩,
    Spike.Lib.X64.AllocG.BlkW.imp h1.2.2.1 h2.2.2.1 hw, Spike.Lib.X64.AllocG.BlkW.imp h1.2.2.2 h2.2.2.2 hw⟩

/-- **`PrintBlkW` from the pieces and `print`'s blocks.** -/
theorem PrintBlkW.of {W₀ : Frag isa} {K : State → State → Prop} {fr : Scc.Emit.X64.Frame} {B : PBlk}
    {J : AS → Ctl → Prop} {P Q : Nat → Ctl → Prop} (h : PrintArgW W₀ K exe endPc R F fr B J)
    (hp : ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr J).J σC c →
      Spike.Lib.X64.PrintA.PrintAW σC.regs.rbp.toBitVec (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rdi)
        (σC.regs.get64 .rsi).toNat P Q W₀ K exe endPc (Spike.Lib.X64.PrintCall.pR (-(fr.size : Int) - 8 - 8) R)
        (Spike.Lib.X64.PrintCall.pF (-(fr.size : Int) - 8 - 8) R F)) :
    PrintBlkW W₀ K exe endPc R F fr B J P Q :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hp⟩

end Pieces

/-! ## The pieces' cells and phases -/

/-- The cells before the multiply, laid out. -/
theorem printPre_zip {lO lB lL lM l8 : List Item} {olo os : Int} {dO dB dL dM dI : Directive}
    (eO : dirs lO = [dO]) (eB : dirs lB = [dB]) (eL : dirs lL = [dL]) (eM : dirs lM = [dM]) (eI : dirs l8 = [dI])
    (a1 a2 a3 b1 b2 b3 b4 c1 c2 : Nat) :
    (preD lO lB lL lM l8 olo os).zip [a1, a2, a3, b1, b2, b3, b4, c1, c2] =
      [(dO, a1), (ext32D, a2), (stDir olo, a3)] ++ [(dB, b1), (dL, b2), (addD, b3), (stDir os, b4)] ++
        [(dM, c1), (dI, c2)] := by
  simp only [preD, dirs_append, eO, eB, eL, eM, eI, List.cons_append, List.nil_append, List.append_assoc,
    List.zip_cons_cons, List.zip_nil_right]

/-- The cells after the multiply, laid out. -/
theorem printPost_zip {lN lC lN' lC' lS lK : List Item} {ocap okk : Int}
    {dN dC dN' dC' dS dK : Directive} (eN : dirs lN = [dN]) (eC : dirs lC = [dC]) (eN' : dirs lN' = [dN'])
    (eC' : dirs lC' = [dC']) (eS : dirs lS = [dS]) (eK : dirs lK = [dK]) (c4 e1 e2 e3 e4 e5 e6 e7 e8 g1 g2 : Nat) :
    (postD lN lC lN' lC' lS lK ocap okk).zip [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2] =
      [(stDir ocap, c4)] ++ [(dN, e1), (dC, e2), (dN', e3), (dC', e4), (cmpD, e5), (movRsiD, e6), (cmovD .c, e7),
        (stDir okk, e8)] ++ [(dS, g1), (dK, g2)] := by
  simp only [postD, dirs_append, eN, eC, eN', eC', eS, eK, List.cons_append, List.nil_append,
    List.append_assoc, List.zip_cons_cons, List.zip_nil_right]

section Ph

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
  {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {ra : Int64}
  {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}

include hf h1 in
/-- **The pieces' phase checks** from the chunks' run checks (`CdC`) and
the call's (`BlC`): before the multiply, the multiply's pc off the sites
with its next pc in its phase, after it, the `call`. -/
theorem print_ph (hCd : ∀ pc blk, Cd pc blk → CdC cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {B : PBlk}
    (h : PrintCodeC fr Cd Bl kk pc n b o m cw B) :
    blkPh okPc ph (fun _ => false) lab B.pc ra B.pre = true ∧
      okPc B.pc1.toBitVec.toNat = true ∧ ph (B.pc1 + Int64.ofNat B.zM).toBitVec.toNat = ph B.pc1.toBitVec.toNat ∧
      blkPh okPc ph (fun _ => false) lab B.pc2 ra B.post = true ∧
      blkPh okPc ph (fun _ => false) lab B.pc3 ra [(callD, B.zc)] = true := by
  obtain ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, dO, dB, dL, dM, dI, dN, dC, dN', dC',
    dS, dK, a1, a2, a3, b1, b2, b3, b4, c1, c2, c3, c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2, zc,
    hlo, hs, hcap, hk, hO, hB, hL, hM, h8, hN, hC, hN', hC', hS, hK, eO, eB, eL, eM, eI, eN, eC, eN', eC', eS, eK,
    hc1, hc2, hc3, hc4, hc5, hbl, rfl⟩ := h
  have hz1 : [a1, a2, a3, b1, b2, b3, b4, c1, c2].length = (preD lO lB lL lM l8 olo os).length := by
    simp only [preD, dirs_append, eO, eB, eL, eM, eI, List.length_append, List.length_cons, List.length_nil]
  have hz2 : [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2].length = (postD lN lC lN' lC' lS lK ocap okk).length := by
    simp only [postD, dirs_append, eN, eC, eN', eC', eS, eK, List.length_append, List.length_cons, List.length_nil]
  have hpre := printPre_zip (olo := olo) (os := os) eO eB eL eM eI a1 a2 a3 b1 b2 b3 b4 c1 c2
  have hpost := printPost_zip (ocap := ocap) (okk := okk) eN eC eN' eC' eS eK c4 e1 e2 e3 e4 e5 e6 e7 e8 g1 g2
  have hok1 : okBlk (-(fr.size : Int)) 16 (oB fr) ((preD lO lB lL lM l8 olo os).zip
      [a1, a2, a3, b1, b2, b3, b4, c1, c2]) = true := (covP_printPre hf h1 hlo hs hO hB hL hM h8).ok hz1
  have hok2 : okBlk (-(fr.size : Int)) 16 (oB fr) ((postD lN lC lN' lC' lS lK ocap okk).zip
      [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2]) = true := (covP_printPost hf h1 hcap hk hN hC hN' hC' hS hK).ok hz2
  rw [hpre] at hok1
  rw [hpost] at hok2
  have cl1 := Spike.Lib.LowerX64.classify_of_okBlk hok1
  have cl2 := Spike.Lib.LowerX64.classify_of_okBlk hok2
  obtain ⟨-, -, -, -, -, -, r1⟩ := hCd _ _ hc1
  obtain ⟨-, -, -, -, -, -, r2⟩ := hCd _ _ hc2
  obtain ⟨-, -, -, -, -, -, r3⟩ := hCd _ _ hc3
  obtain ⟨-, -, -, -, -, -, r4⟩ := hCd _ _ hc4
  obtain ⟨-, -, -, -, -, -, r5⟩ := hCd _ _ hc5
  obtain ⟨-, -, -, -, -, -, hbph, -⟩ := hBl _ _ _ _ hbl
  -- the chunks' phase checks and fall-throughs
  have p1 := blkPh_of_run r1 fun d hd => cl1 d (List.mem_append_left _ (List.mem_append_left _ hd))
  have p2 := blkPh_of_run r2 fun d hd => cl1 d (List.mem_append_left _ (List.mem_append_right _ hd))
  have p3 := blkPh_of_runPhB (xs := []) (ys := [(dM, c1), (dI, c2)]) (zs := [(mulFI.toDir, c3), (stDir ocap, c4)])
    (by simpa using r3) fun d hd => cl1 d (List.mem_append_right _ hd)
  have q3 := blkPh_of_runPhB (xs := [(dM, c1), (dI, c2), (mulFI.toDir, c3)]) (ys := [(stDir ocap, c4)]) (zs := [])
    (by simpa using r3) fun d hd => cl2 d (List.mem_append_left _ (List.mem_append_left _ hd))
  have p4 := blkPh_of_run r4 fun d hd => cl2 d (List.mem_append_left _ (List.mem_append_right _ hd))
  have p5 := blkPh_of_run r5 fun d hd => cl2 d (List.mem_append_right _ hd)
  have hst : ∀ (off : Int) a, classify (stDir off) = some a → a.isTerm = false := by
    intro off a ha; cases ha; rfl
  have f1 := runPhB_fall r1 (k := 2) (by simp) (hst olo)
  have f2 := runPhB_fall r2 (k := 3) (by simp) (hst os)
  have f3 := runPhB_fall r3 (k := 3) (by simp) (hst ocap)
  have f4 := runPhB_fall r4 (k := 7) (by simp) (hst okk)
  obtain ⟨o3, g3, t3⟩ := runPhB_get r3 (k := 2) (by simp)
  obtain ⟨-, g3', -⟩ := runPhB_get r3 (k := 3) (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at t3
  rw [show classify mulFI.toDir = none from rfl] at t3
  have t3' := t3 _ (List.mem_singleton_self _)
  simp only [cellOff, List.take, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, List.length_cons, List.length_nil, List.cons_append,
    List.nil_append, List.append_nil, Int64.ofNat_add, Int64.add_assoc]
    at p1 p2 p3 q3 p4 p5 f1 f2 f3 f4 o3 g3 t3' g3' hbph
  have z0 : Int64.ofNat 0 = 0 := rfl
  simp only [z0, Int64.add_zero] at p3
  simp only [pblk, hpre, hpost]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine blkPh_append (blkPh_append ?_ ?_ ?_) ?_ ?_
    · exact p1
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
        Int64.add_assoc] using p2
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
        Int64.add_assoc] using f1
    · simpa only [List.map_cons, List.map_nil, List.map_append, List.sum_append, List.sum_cons, List.sum_nil,
        Nat.add_zero, Int64.ofNat_add, Int64.add_assoc, List.cons_append, List.nil_append, Int64.add_zero] using p3
    · simp only [List.map_cons, List.map_nil, List.map_append, List.sum_append, List.sum_cons, List.sum_nil,
        Nat.add_zero, Int64.ofNat_add, Int64.add_assoc, List.cons_append, List.nil_append]
      rw [f2, f1]
  · simpa only [List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using o3
  · simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc]
    rw [t3', g3]
  · refine blkPh_append (blkPh_append ?_ ?_ ?_) ?_ ?_
    · simpa only [List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using q3
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
        Int64.add_assoc] using p4
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
        Int64.add_assoc]
      rw [f3, g3']
    · simpa only [List.map_cons, List.map_nil, List.map_append, List.sum_append, List.sum_cons, List.sum_nil,
        Nat.add_zero, Int64.ofNat_add, Int64.add_assoc, List.cons_append, List.nil_append] using p5
    · simp only [List.map_cons, List.map_nil, List.map_append, List.sum_append, List.sum_cons, List.sum_nil,
        Nat.add_zero, Int64.ofNat_add, Int64.add_assoc, List.cons_append, List.nil_append]
      rw [f4, f3, g3']
  · simpa only [callD, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using hbph

end Ph

section Cov

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
  {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}

include hf h1 in
/-- **The pieces before and after the multiply are covered** at the frame's
offsets, and none of their instructions is a branch. -/
theorem printArg_ok {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {B : PBlk} (h : PrintCodeC fr Cd Bl kk pc n b o m cw B) :
    okBlk (-(fr.size : Int)) 16 (oB fr) B.pre = true ∧ okBlk (-(fr.size : Int)) 16 (oB fr) B.post = true ∧
      (∀ k (hk : k < B.pre.length) a, classify B.pre[k].1 = some a → a.isTerm = false) ∧
      (∀ k (hk : k < B.post.length) a, classify B.post[k].1 = some a → a.isTerm = false) := by
  obtain ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, dO, dB, dL, dM, dI, dN, dC, dN', dC',
    dS, dK, a1, a2, a3, b1, b2, b3, b4, c1, c2, c3, c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2, zc,
    hlo, hs, hcap, hk, hO, hB, hL, hM, h8, hN, hC, hN', hC', hS, hK, eO, eB, eL, eM, eI, eN, eC, eN', eC', eS, eK,
    -, -, -, -, -, -, rfl⟩ := h
  have hz1 : [a1, a2, a3, b1, b2, b3, b4, c1, c2].length = (preD lO lB lL lM l8 olo os).length := by
    simp only [preD, dirs_append, eO, eB, eL, eM, eI, List.length_append, List.length_cons, List.length_nil]
  have hz2 : [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2].length = (postD lN lC lN' lC' lS lK ocap okk).length := by
    simp only [postD, dirs_append, eN, eC, eN', eC', eS, eK, List.length_append, List.length_cons, List.length_nil]
  have hok1 := (covP_printPre hf h1 hlo hs hO hB hL hM h8).ok hz1
  have hok2 := (covP_printPost hf h1 hcap hk hN hC hN' hC' hS hK).ok hz2
  refine ⟨hok1, hok2, fun k hk a ha => ?_, fun k hk a ha => ?_⟩
  · rcases Nat.lt_or_ge (k + 1) (pblk pc (preD lO lB lL lM l8 olo os) [a1, a2, a3, b1, b2, b3, b4, c1, c2] c3
      (postD lN lC lN' lC' lS lK ocap okk) [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2] zc).pre.length with h' | h'
    · exact okBlk_nt hok1 k hk h' a ha
    · have hpre := printPre_zip (olo := olo) (os := os) eO eB eL eM eI a1 a2 a3 b1 b2 b3 b4 c1 c2
      simp only [pblk, hpre, List.length_append, List.length_cons, List.length_nil] at hk h' ha
      obtain rfl : k = 8 := by omega
      exact getOp_noTerm h8 eI a (by simpa using ha)
  · rcases Nat.lt_or_ge (k + 1) (pblk pc (preD lO lB lL lM l8 olo os) [a1, a2, a3, b1, b2, b3, b4, c1, c2] c3
      (postD lN lC lN' lC' lS lK ocap okk) [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2] zc).post.length with h' | h'
    · exact okBlk_nt hok2 k hk h' a ha
    · have hpost := printPost_zip (ocap := ocap) (okk := okk) eN eC eN' eC' eS eK c4 e1 e2 e3 e4 e5 e6 e7 e8 g1 g2
      simp only [pblk, hpost, List.length_append, List.length_cons, List.length_nil] at hk h' ha
      obtain rfl : k = 10 := by omega
      exact getOp_noTerm hK eK a (by simpa using ha)

end Cov

/-! ## The pieces inside `W2` -/

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt Ab : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

omit [Kraken.Executable.ValidLayout exe] in
/-- **A flag instruction's node at its code inside `W2`** at the frames
`fs`: `SFacts` from the instruction's silent step (`sfacts_fi`) at its code
`hcode`, off the sites (`hok`) with its next pc in its phase (`hph`);
nothing written, off a system call; its states at `PlacedSE` (`hP`), in the
abort phase's facts (`hab`). -/
theorem nodeW_w2Fi {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {fi : Spike.Lib.X64.FI}
    {z : Nat} {n : ND} (hcode : CdOf exe endPc n.pc [(fi.toDir, z)]) (hok : okPc n.pc.toBitVec.toNat = true)
    (hph : ph (n.pc + Int64.ofNat z).toBitVec.toNat = ph n.pc.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hab : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n)
    (hP : NodeW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    NodeW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n := by
  have hS : NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) :=
    nodeW_postO hI rfl hok hR hR8 hl hh hsub hFO fun s c σ hs hn _ hpc _ _ hJ' hPc hO =>
      sfacts_fi (hJ'.1 ▸ cfacts_c0) hPc ((hcode s hs hn).cell0 rfl rfl hpc) (next_same hI hpc hph) hO
  refine NodeW.w2E hp hS (fun s c hA => ?_) hJ
  have hc : CellAt s fi.toDir z := (hcode s hA.1 hA.2.1).cell0 rfl rfl hA.2.2.2.1
  obtain ⟨t, hex, hst⟩ := Spike.Lib.X64.exec_fi hc
  have hsy : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by cases fi <;> intro w w' h <;> cases h)
  refine ⟨⟨(hab s c hA).1, (hP s c hA).1, fun _ _ _ _ => wrOkA_of_noWr fun L hL => ?_,
    fun h => absurd h (by rw [hsy]; decide)⟩, fun _ h => h⟩
  rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [hex] at h <;> cases h <;> exact hst.elim

/-- **A call of `print`'s argument block and its `call` inside `W2`** at
the frames `fs` (`PrintBlkW`'s first four conjuncts): at the block's chunks
at the code predicates `CdC`, `BlC` (`hCd`, `hBl`, `PrintCodeC`), in any
region holding the frame and the return address's cell; its states at
`PlacedSE` (`hP`), in the abort phase's facts (`hab`); at an invariant whose controls
exclude `main`'s `ret` and are free of `ZBad` (`hJ`, e.g. `printJ_hJ`). -/
theorem printArgW_w2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdC cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {B : PBlk}
    (hB : PrintCodeC fr Cd Bl kk pc n b o m cw B) {Jn : AS → Ctl → Prop}
    (hab : PrintArgW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F fr B Jn)
    (hP : PrintArgW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F fr B Jn)
    (hJ : ∀ σ c, Jn σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    PrintArgW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F fr B Jn := by
  have h8 : (fr.size : Int) % 8 = 0 := by have := frame_mod8B hf; omega
  obtain ⟨hph1, hokM, hphM, hph2, hph3⟩ := print_ph hf h1 hCd hBl hB
  obtain ⟨hc1, hcM, hc2, hc3⟩ := hB.cdOf (fun _ _ h => codeAt_cdC hI (hCd _ _ h)) fun _ _ _ _ h => by
    obtain ⟨L, j, off, hpc, hb, -⟩ := hBl _ _ _ _ h
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
    rwa [hI.labOk, hpc] at this
  obtain ⟨hok1, hok2, hnt1, hnt2⟩ := printArg_ok hf h1 hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact blkW_w2BPE hI hR hR8 (by omega) hhi hl hh hsub hfit hFO hp (n := B.n0 fr Jn) hc1 hph1 hok1
      (noRet_of_noTerm hnt1) hab.1 hP.1 hJ
  · exact nodeW_w2Fi hI hcM hokM hphM hR hR8 hl hh hsub hFO hp hab.2.1 hP.2.1
      fun σ c ⟨σ0, hJ0, _⟩ => hJ σ0 c hJ0
  · exact blkW_w2BPE hI hR hR8 (by omega) hhi hl hh hsub hfit hFO hp hc2 hph2 hok2
      (noRet_of_noTerm hnt2) hab.2.2.1 hP.2.2.1 fun σ c ⟨σ0, fl, hJ0, _⟩ => hJ σ0 c hJ0
  · exact blkW_w2BPE hI hR hR8 hlo hhi hl hh hsub hfit hFO hp hc3 hph3
      (okBlk_callD (decide_eq_true (by simp only [PBlk.n3, oB]; omega))) rfl hab.2.2.2 hP.2.2.2
      fun σ c ⟨σ0, fl, hJ0, _⟩ => hJ σ0 c hJ0

end W

/-! ## The abort phase -/

section AbW

/-- **`print`'s entry is a position off the write abort**, in a layout with
`print`'s code. -/
theorem posOff_print {cells : List (Directive × Nat)} {lab : Label → Int64}
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) : PosOff cells lab (lab "scc_rt_print") :=
  ⟨"scc_rt_print", 0, by
    simpa [cellOff] using inRunB_of_blockAtB (Spike.Lib.X64.PrintG.printIn_spec hpr).1 (i := 0) (by decide),
    by decide, by simp⟩

variable {P : Int64 → Prop} {pc : Int64}

/-- A cell's offset in a prefix. -/
theorem cellOff_app_left {a b : List (Directive × Nat)} {i : Nat} (hi : i ≤ a.length) :
    cellOff (a ++ b) i = cellOff a i := by
  unfold cellOff; rw [List.take_append_of_le_length hi]

/-- A cell's offset past a prefix. -/
theorem cellOff_app_right {a b : List (Directive × Nat)} (i : Nat) :
    cellOff (a ++ b) (a.length + i) = (a.map (·.2)).sum + cellOff b i := by
  unfold cellOff
  rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, List.map_append,
    List.sum_append]

/-- **Every cell of `a ++ b` at `P`** from every cell of `a` and of `b`. -/
theorem pos_app {a b : List (Directive × Nat)} (ha : ∀ i < a.length, P (pc + Int64.ofNat (cellOff a i)))
    (hb : ∀ i < b.length, P (pc + Int64.ofNat (a.map (·.2)).sum + Int64.ofNat (cellOff b i))) :
    ∀ i < (a ++ b).length, P (pc + Int64.ofNat (cellOff (a ++ b) i)) := by
  intro i hi
  rcases Nat.lt_or_ge i a.length with h' | h'
  · rw [cellOff_app_left (Nat.le_of_lt h')]; exact ha i h'
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
    rw [cellOff_app_right, Int64.ofNat_add, ← Int64.add_assoc]
    exact hb j (by simp at hi; omega)

/-- **Every cell of a prefix at `P`.** -/
theorem pos_left {a b : List (Directive × Nat)} (h : ∀ i < (a ++ b).length, P (pc + Int64.ofNat (cellOff (a ++ b) i))) :
    ∀ i < a.length, P (pc + Int64.ofNat (cellOff a i)) := fun i hi => by
  have := h i (by simp; omega)
  rwa [cellOff_app_left (Nat.le_of_lt hi)] at this

/-- **Every cell past a prefix at `P`.** -/
theorem pos_right {a b : List (Directive × Nat)}
    (h : ∀ i < (a ++ b).length, P (pc + Int64.ofNat (cellOff (a ++ b) i))) :
    ∀ i < b.length, P (pc + Int64.ofNat (a.map (·.2)).sum + Int64.ofNat (cellOff b i)) := fun i hi => by
  have := h (a.length + i) (by simp; omega)
  rwa [cellOff_app_right, Int64.ofNat_add, ← Int64.add_assoc] at this

/-- **Every fall-through of a block without branches at `P`**: its cells'
and the pc right after it. -/
theorem tgts_of_pos {lab : Label → Int64} {ra : Int64} {blk : List (Directive × Nat)}
    (hnt : ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a → a.isTerm = false)
    (hpos : ∀ i < blk.length, P (pc + Int64.ofNat (cellOff blk i)))
    (hend : P (pc + Int64.ofNat (cellOff blk blk.length))) :
    ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a →
      ∀ t ∈ aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) ra a, P t := by
  intro k hk a ha t ht
  have key : aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) ra a =
      [pc + Int64.ofNat (cellOff blk (k + 1))] := by
    have := hnt k hk a ha
    rw [Spike.Lib.X64.cellOff_succ hk, Int64.ofNat_add, ← Int64.add_assoc]
    cases a <;> simp_all [aiTgts, AI.isTerm]
  rw [key, List.mem_singleton] at ht
  subst ht
  rcases Nat.lt_or_ge (k + 1) blk.length with h' | h'
  · exact hpos _ h'
  · rw [show k + 1 = blk.length by omega]; exact hend

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

omit [Executable.ValidLayout exe] in
/-- **A flag instruction's node keeps the write abort's phase** (as
`Spike.Lib.X64.AllocG.nodeW_ab_fi` at its code `hcode`): off the sites
(`hok`), its next pc none of the write abort's (`hnx`). -/
theorem nodeW_abFi {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {fi : Spike.Lib.X64.FI}
    {z : Nat} {n : ND} (hcode : CdOf exe endPc n.pc [(fi.toDir, z)]) (hok : okPc n.pc.toBitVec.toNat = true)
    (hnx : n.pc + Int64.ofNat z ∉ abPcs lab) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc : CellAt s fi.toDir z := (hcode s hs hn).cell0 rfl rfl hpc
  obtain ⟨t0, hex, hst⟩ := Spike.Lib.X64.exec_fi hc
  refine ⟨AbSt.ofLeaves hP.noTake (Scc.Sem.X64.atSyscall_false_of_cellAt hc ?_) fun t ht => ?_, fun _ h => h⟩
  · cases fi <;> intro w w' h <;> cases h
  · rw [hex] at ht
    cases ht
    exact (silent_facts (p := fun _ _ => True) (G := fun _ _ => True) (G' := fun _ _ => True)
      (fun _ ⟨_, h⟩ => h ▸ Spike.Lib.X64.AllocG.not_ab_after hpc hnx) hst).2.1

/-- **A call of `print`'s argument block and its `call` keep the write
abort's phase** (`printArgW_w2`'s `hab`, by `blkW_abSt_pos`, `nodeW_abFi`):
its chunks at the code predicate off the write abort's labels (`hCd`,
`CdCL`), its `call` at a position off the write abort (`hBl`), in a layout
with the runtime's code (`hpr`, `habI`). Every fall-through is a cell of a
chunk or the `call`, the `call`'s target `print`'s entry. -/
theorem printArgW_ab {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {B : PBlk}
    (hB : PrintCodeC fr Cd Bl kk pc n b o m cw B) {Jn : AS → Ctl → Prop} :
    PrintArgW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F fr B Jn := by
  have h8 : (fr.size : Int) % 8 = 0 := by have := frame_mod8B hf; omega
  have hCdC : ∀ pc blk, Cd pc blk → CdC cells okPc ph lab ra pc blk := fun _ _ h => (hCd _ _ h).toCdC
  have hBlC : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k := fun _ _ _ _ h => (hBl _ _ _ _ h).1
  obtain ⟨hph1, hokM, -, hph2, hph3⟩ := print_ph hf h1 hCdC hBlC hB
  obtain ⟨hc1, hcM, hc2, hc3⟩ := hB.cdOf (fun _ _ h => codeAt_cdC hI (hCdC _ _ h)) fun _ _ _ _ h => by
    obtain ⟨L, j, off, hpc, hb, -⟩ := hBlC _ _ _ _ h
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
    rwa [hI.labOk, hpc] at this
  obtain ⟨hok1, hok2, hnt1, hnt2⟩ := printArg_ok hf h1 hB
  -- every cell of the chunks, and the `call`, at a position off the write abort
  obtain ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, dO, dB, dL, dM, dI, dN, dC, dN', dC',
    dS, dK, a1, a2, a3, b1, b2, b3, b4, c1, c2, c3, c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2, zc,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, eO, eB, eL, eM, eI, eN, eC, eN', eC', eS, eK,
    hd1, hd2, hd3, hd4, hd5, hbl, rfl⟩ := hB
  have q := fun {pc : Int64} {blk : List (Directive × Nat)} (h : Cd pc blk) =>
    fun i (hi : i < blk.length) => posOff_of_subCdL (SubCd.whole (hCd _ _ h)) hi
  have q1 := q hd1
  have q2 := q hd2
  have q3 := q hd3
  have q4 := q hd4
  have q5 := q hd5
  have qb := (hBl _ _ _ _ hbl).2
  have hpre := printPre_zip (olo := olo) (os := os) eO eB eL eM eI a1 a2 a3 b1 b2 b3 b4 c1 c2
  have hpost := printPost_zip (ocap := ocap) (okk := okk) eN eC eN' eC' eS eK c4 e1 e2 e3 e4 e5 e6 e7 e8 g1 g2
  have q3l := pos_left (a := [(dM, c1), (dI, c2)]) (b := [(mulFI.toDir, c3), (stDir ocap, c4)]) q3
  have q3r := pos_right (a := [(dM, c1), (dI, c2), (mulFI.toDir, c3)]) (b := [(stDir ocap, c4)]) q3
  have hlab := hI.labOk
  subst hlab
  have nx : ∀ {t}, PosOff cells (_root_.Executable.labels exe).label t →
      t ∉ abPcs (_root_.Executable.labels exe).label := notAbPc_of_posOff hI.lays hpr habI
  -- the positions in the pieces' terms
  have Ppre : ∀ i < (pblk pc (preD lO lB lL lM l8 olo os) [a1, a2, a3, b1, b2, b3, b4, c1, c2] c3
      (postD lN lC lN' lC' lS lK ocap okk) [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2] zc).pre.length,
      PosOff cells (_root_.Executable.labels exe).label
        ((pblk pc (preD lO lB lL lM l8 olo os) [a1, a2, a3, b1, b2, b3, b4, c1, c2] c3
          (postD lN lC lN' lC' lS lK ocap okk) [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2] zc).pc +
        Int64.ofNat (cellOff (pblk pc (preD lO lB lL lM l8 olo os) [a1, a2, a3, b1, b2, b3, b4, c1, c2] c3
          (postD lN lC lN' lC' lS lK ocap okk) [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2] zc).pre i)) := by
    simp only [pblk, hpre]
    refine pos_app (pos_app q1 fun i hi => ?_) fun i hi => ?_
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
        Int64.add_assoc] using q2 i hi
    · simpa only [List.map_cons, List.map_nil, List.map_append, List.sum_append, List.sum_cons, List.sum_nil,
        Nat.add_zero, Int64.ofNat_add, Int64.add_assoc, List.cons_append, List.nil_append] using q3l i hi
  have Epre := q3 2 (by simp)
  have Ppost : ∀ i < (pblk pc (preD lO lB lL lM l8 olo os) [a1, a2, a3, b1, b2, b3, b4, c1, c2] c3
      (postD lN lC lN' lC' lS lK ocap okk) [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2] zc).post.length,
      PosOff cells (_root_.Executable.labels exe).label
        ((pblk pc (preD lO lB lL lM l8 olo os) [a1, a2, a3, b1, b2, b3, b4, c1, c2] c3
          (postD lN lC lN' lC' lS lK ocap okk) [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2] zc).pc2 +
        Int64.ofNat (cellOff (pblk pc (preD lO lB lL lM l8 olo os) [a1, a2, a3, b1, b2, b3, b4, c1, c2] c3
          (postD lN lC lN' lC' lS lK ocap okk) [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2] zc).post i)) := by
    simp only [pblk, hpost]
    refine pos_app (pos_app (fun i hi => ?_) fun i hi => ?_) fun i hi => ?_
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
        Int64.add_assoc] using q3r i hi
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
        Int64.add_assoc] using q4 i hi
    · simpa only [List.map_cons, List.map_nil, List.map_append, List.sum_append, List.sum_cons, List.sum_nil,
        Nat.add_zero, Int64.ofNat_add, Int64.add_assoc, List.cons_append, List.nil_append] using q5 i hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine blkW_abSt_pos hI hpr habI hc1 hok1 hR (by omega) hhi hph1 (noRet_of_noTerm hnt1)
      fun σ c _ k hk a ha t ht => .inl (tgts_of_pos hnt1 Ppre ?_ k hk a ha t ht)
    simp only [pblk, hpre, cellOff, List.take, List.map_cons, List.map_nil, List.map_append, List.sum_append,
      List.sum_cons, List.sum_nil, List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      Int64.ofNat_add, Int64.add_assoc, List.cons_append, List.nil_append] at Epre ⊢
    exact Epre
  · refine nodeW_abFi hI hcM hokM (nx ?_)
    have := Ppost 0 (by simp [pblk, hpost])
    simpa only [cellOff, List.take, List.map_nil, List.sum_nil, show Int64.ofNat 0 = 0 from rfl, Int64.add_zero,
      pblk, PBlk.nM, List.sum_cons, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using this
  · refine blkW_abSt_pos hI hpr habI hc2 hok2 hR (by omega) hhi hph2 (noRet_of_noTerm hnt2)
      fun σ c _ k hk a ha t ht => .inl (tgts_of_pos hnt2 Ppost ?_ k hk a ha t ht)
    simp only [pblk, hpost, cellOff, List.take, List.map_cons, List.map_nil, List.map_append, List.sum_append,
      List.sum_cons, List.sum_nil, List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      Int64.ofNat_add, Int64.add_assoc, List.cons_append, List.nil_append] at qb ⊢
    exact qb
  · refine blkW_abSt_pos hI hpr habI hc3 (okBlk_callD (lo := -(fr.size : Int) - 8) (hi := 16)
      (decide_eq_true (by simp only [PBlk.n3, oB]; omega))) hR hlo hhi hph3 rfl
      fun σ c _ k hk a ha t ht => .inl ?_
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    simp only [List.getElem_cons_zero, classify_callD, Option.some.injEq] at ha
    subst ha
    simp only [aiTgts, List.mem_singleton] at ht
    subst ht
    exact posOff_print hpr

end AbW

/-! ## The controls -/

/-- **`FrOk2` at a `ret`** inside `print`'s call: the caller's continuation
`e` and frames `fs` free of `ZBad` (`PrintWE`'s source after an empty
slice's body). -/
theorem frOk2_ret {a : CoreTerm.At} {env : TermRun.Env} {x : String} {e : Expr} {c1 : Ctl}
    {fs : List TermRun.Frame} (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) :
    FrOk2 ⟨.ret a, env, none⟩ (Spike.Lib.LowerNode.printFrame x e c1 :: fs) := by
  refine ⟨by simp [NoS], ?_⟩
  intro fr hfr
  rcases List.mem_cons.mp hfr with rfl | hfr
  · exact he
  · exact hfs fr hfr

/-- **The controls of `printJ` at `print`'s frames** (`printArgW_w2`'s
`hJ`): from `FrOk2` at its control `cE`, the frames nonempty. -/
theorem printJ_hJ {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {c1 cE : Ctl}
    {fr' : TermRun.Frame} {fs : List TermRun.Frame} (h : FrOk2 cE (fr' :: fs)) :
    ∀ σ c, printJ p lbl lsize fr fp ra tp c0 t env lits cs bufs c1 cE σ c →
      (fr' :: fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c (fr' :: fs) :=
  fun _ _ hc => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), hc.1 ▸ h⟩

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.print_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.print_ph

/-- info: 'Spike.Lib.LowerX64.printArgW_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printArgW_w2

/-- info: 'Spike.Lib.LowerX64.printArgW_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printArgW_ab
