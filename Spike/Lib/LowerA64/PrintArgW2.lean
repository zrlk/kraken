/-
**A call of `print`'s argument block and its `bl` inside `W2`** (AArch64):
`PrintBlkW`'s first conjunct (`Spike/Lib/LowerA64/PrintCallC2.lean`) at the
per-pair facts `W2` (`Spike/Lib/LowerA64/SFactsA2.lean`), from the block's
code (`print_code`'s one `CdOf`) and its phase check (`print_ph`, from the
code predicates' chunks `CdC`, `BlC`).

- `blkW_postOc`, `blkW_noWrC`, `blkW_noSysC`, `blkW_w2BPc`: as
  `Spike.Lib.A64.Rt.blkW_postO`, `Spike.Lib.A64.AllocG.blkW_noWr`,
  `blkW_noSys`, `blkW_w2BP` (`Spike/Lib/LowerA64/W2Body.lean`) at the
  block's code (`CdOf`) and its phase check at the node's pc, in place of
  its `blockAt`;
- `okBlk_ntL`, `okBlk_cls`, `nt_left`: a covered block's instructions are
  classified and none but the last is a branch;
- `blkPh_appendNT`, `blkPh_of_cdC`: the phase check of two blocks in a row,
  the first without a branch; a chunk's from the code predicate's run check;
- `printCode_unique`: `printInsts`' cells are a function of the operands;
- `printCode_okBlk`, `printCode_noRet`: the argument block with its `bl` is
  covered at the frame's offsets and has no `ret`;
- `print_ph`: the argument block's phase check from `InstsC2` at `CdC`, `BlC`;
- `printBlkW_w2`: the argument block and its `bl` inside `W2` at the frames
  `fs`, its states at `PlacedSE` (`hP`: placed, or the current frame in the
  output extern's model), in the abort phase's facts (`hab`);
- `cdOf_of_cdC`, `cdOf_of_blC`, `printBlkW_w2C`: the same at the code
  predicates `CdC`, `BlC` and `printInsts`' `InstsC2`;
- `print_chunks`: `printInsts`' chunks at `InstsC2`;
- `posOff_append`, `posOff_cdCL`, `posOff_printEntry`, `printBlkW_ab`: the
  block keeps the write abort's phase (`printBlkW_w2C`'s `hab`, by
  `blkW_abSt_pos`), its chunks at `CdCL`, its `bl` at a position off the
  write abort (`BlC2L`);
- `frOk2_ret`, `printJ_hJ`: `printBlkW_w2C`'s `hJ` at `printJ` from `FrOk2`
  at its control (`frOk2_printC` for a nonempty slice, `frOk2_ret` for an
  empty one).
-/
import Spike.Lib.LowerA64.W2Body
import Spike.Lib.LowerA64.PrintW2
import Spike.Lib.LowerA64.UserAbC

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At okBlk FStable AI)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.AllocG (dumN)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.LowerShape (printInsts)

/-! ## Covered blocks -/

/-- **No branch before the last instruction**: in a covered block `a ++ b`
with `b` nonempty, no instruction of `a` is a branch. -/
theorem okBlk_ntL {lo hi : Int} : ∀ {o : Spike.Lib.A64.Flow.SO} {a b : List Directive},
    okBlk lo hi o (a ++ b) = true → b ≠ [] →
    ∀ k (hk : k < a.length) x, Spike.Lib.A64.Flow.classify a[k] = some x → x.isTerm = false
  | _, [], _, _, _, k, hk, _, _ => absurd hk (Nat.not_lt_zero k)
  | o, d :: ds, b, h, hb, k, hk, x, hx => by
    rw [List.cons_append] at h
    unfold okBlk at h
    split at h
    · rename_i a ha
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨⟨-, hterm⟩, hrest⟩ := h
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero] at hx
        rw [ha] at hx
        cases hx
        rcases hterm with h2 | h2
        · exact absurd (List.append_eq_nil_iff.mp h2).2 hb
        · exact h2
      | succ k =>
        exact okBlk_ntL hrest hb k (by simp at hk; omega) x (by simpa using hx)
    · cases h

/-- **A covered block's instructions are classified.** -/
theorem okBlk_cls {lo hi : Int} : ∀ {o : Spike.Lib.A64.Flow.SO} {blk : List Directive},
    okBlk lo hi o blk = true → ∀ d ∈ blk, (Spike.Lib.A64.Flow.classify d).isSome = true
  | _, [], _, _, hd => absurd hd List.not_mem_nil
  | o, d :: ds, h, d', hd => by
    unfold okBlk at h
    split at h
    · rename_i a ha
      simp only [Bool.and_eq_true] at h
      rcases List.mem_cons.mp hd with rfl | hd
      · rw [ha]; rfl
      · exact okBlk_cls h.2 d' hd
    · cases h

/-- No branch in `a ++ b`: none in `a`. -/
theorem nt_left {a b : List Directive}
    (h : ∀ k (hk : k < (a ++ b).length) x, Spike.Lib.A64.Flow.classify (a ++ b)[k] = some x →
      x.isTerm = false) :
    ∀ k (hk : k < a.length) x, Spike.Lib.A64.Flow.classify a[k] = some x → x.isTerm = false := by
  intro k hk x hx
  exact h k (by simp; omega) x (by rw [List.getElem_append_left hk]; exact hx)

/-! ## Phase checks -/

section Ph

variable {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}

/-- **The phase check of two blocks in a row**, the first without a branch
(`hnt`): its last instruction falls through to the second's start, so the
second starts in the first's phase. -/
theorem blkPh_appendNT {pc ra : Int64} {a b : List Directive}
    (ha : blkPh okPc ph (fun _ => false) lab pc ra a = true)
    (hb : blkPh okPc ph (fun _ => false) lab (pc + Int64.ofNat (4 * a.length)) ra b = true)
    (hnt : ∀ k (hk : k < a.length) x, Spike.Lib.A64.Flow.classify a[k] = some x → x.isTerm = false) :
    blkPh okPc ph (fun _ => false) lab pc ra (a ++ b) = true := by
  refine Spike.Lib.A64.PrintG.blkPh_append ha hb ?_
  rcases Nat.eq_zero_or_pos a.length with h0 | hpos
  · rw [h0]; simp
  · have hk : a.length - 1 < a.length := by omega
    have key : ∀ (x : AI) (f : Int64), x.isTerm = false → aiTgts lab f ra x = [f] := by
      intro x f h; cases x <;> simp_all [AI.isTerm, aiTgts]
    have := List.all_eq_true.mp ha (a.length - 1) (List.mem_range.mpr hk)
    rw [List.getElem?_eq_getElem hk] at this
    cases hx : Spike.Lib.A64.Flow.classify a[a.length - 1] with
    | none => simp [hx] at this
    | some x =>
      simp only [hx, key x _ (hnt _ hk x hx), Bool.and_eq_true, beq_iff_eq, List.all_cons, List.all_nil,
        Bool.or_false, Bool.and_true] at this
      rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ', Nat.sub_add_cancel hpos] at this
      exact this.2

/-- **A chunk of the code predicate passes the phase check** at its pc,
its instructions classified (`hc`). -/
theorem blkPh_of_cdC {prog : List Directive} {ra pc : Int64} {blk : List Directive}
    (h : CdC prog okPc ph lab ra pc blk) (hc : ∀ d ∈ blk, (Spike.Lib.A64.Flow.classify d).isSome = true) :
    blkPh okPc ph (fun _ => false) lab pc ra blk = true := by
  obtain ⟨-, -, -, -, -, hrun⟩ := h
  simpa using Scc.Cert.Ph1A64.blkPh_of_runPhB (xs := []) (zs := []) (by simpa using hrun) hc

end Ph

/-! ## The argument block -/

section Arg

variable {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)

/-- **`printInsts`' cells are a function of the operands**: the cells'
instruction numbers name no label. -/
theorem printCode_unique {n : Nat} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {L L' : List Item} (h : PrintCode cx n b o m cw L) (h' : PrintCode cx n b o m cw L') : L = L' := by
  obtain ⟨i1, i2, i3, i4, l1, l2, l3, l4, l5, c1, c2, c3, c4, c5, rfl⟩ := h
  obtain ⟨j1, j2, j3, j4, m1, m2, m3, m4, m5, e1, e2, e3, e4, e5, rfl⟩ := h'
  have q1 : cx.inst i1 (.ext false .w32 (Scc.Lower.Inv.regName "lo" n) (.reg o)) =
      cx.inst j1 (.ext false .w32 (Scc.Lower.Inv.regName "lo" n) (.reg o)) := rfl
  have q2 : cx.inst i2 (.bin .add (Scc.Lower.Inv.regName "s" (n + 1)) b (.reg (Scc.Lower.Inv.regName "lo" n))) =
      cx.inst j2 (.bin .add (Scc.Lower.Inv.regName "s" (n + 1)) b (.reg (Scc.Lower.Inv.regName "lo" n))) := rfl
  have q3 : cx.inst i3 (.bin .mul (Scc.Lower.Inv.regName "cap" (n + 2)) m (Scc.Lower.imm 8)) =
      cx.inst j3 (.bin .mul (Scc.Lower.Inv.regName "cap" (n + 2)) m (Scc.Lower.imm 8)) := rfl
  have q4 : cx.inst i4 (.select .ult (Scc.Lower.Inv.regName "k" (n + 3)) cw
      (.reg (Scc.Lower.Inv.regName "cap" (n + 2))) cw (.reg (Scc.Lower.Inv.regName "cap" (n + 2)))) =
      cx.inst j4 (.select .ult (Scc.Lower.Inv.regName "k" (n + 3)) cw
      (.reg (Scc.Lower.Inv.regName "cap" (n + 2))) cw (.reg (Scc.Lower.Inv.regName "cap" (n + 2)))) := rfl
  rw [c1, e1] at q1
  rw [c2, e2] at q2
  rw [c3, e3] at q3
  rw [c4, e4] at q4
  rw [c5] at e5
  cases q1; cases q2; cases q3; cases q4; cases e5
  rfl

include hf h1 h16 in
/-- **The argument block with its `bl` is covered** at the frame's offsets. -/
theorem printCode_okBlk {n : Nat} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {L : List Item} (h : PrintCode cx n b o m cw L) :
    okBlk (-(cx.frame : Int)) 0 (oF cx) (directives L ++ blPrintD) = true := by
  obtain ⟨i1, i2, i3, i4, l1, l2, l3, l4, l5, q1, q2, q3, q4, q5, rfl⟩ := h
  simp only [oF, directives_append, List.append_assoc]
  rw [okBlk_inst_ext32 hf h1 h16 q1, okBlk_inst_bin hf h1 h16 (.inl rfl) q2,
    okBlk_inst_bin hf h1 h16 (.inr rfl) q3, okBlk_inst_select hf h1 h16 q4, okBlk_args2 hf h1 h16 q5]
  rfl

include hf h1 h16 in
/-- **The argument block with its `bl` has no `ret`**. -/
theorem printCode_noRet {n : Nat} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {L : List Item} (h : PrintCode cx n b o m cw L) : noRetBlk (directives L ++ blPrintD) = true := by
  have hok := printCode_okBlk hf h1 h16 h
  have hnt := okBlk_ntL hok (b := blPrintD) (by simp [blPrintD_eq])
  unfold noRetBlk
  rw [List.all_eq_true]
  intro d hd
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  rcases Nat.lt_or_ge k (directives L).length with hl | hl
  · rw [List.getElem_append_left hl]
    cases hx : Spike.Lib.A64.Flow.classify (directives L)[k] with
    | none => rfl
    | some x =>
      have := hnt k hl x hx
      cases x <;> first | rfl | cases this
  · have : k = (directives L).length := by simp [blPrintD_eq] at hk; omega
    subst this
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self, blPrintD_eq]
    rfl

/-- **`printInsts`' chunks at `InstsC2`**: its cells (`PrintCode`), each
cell's chunk at the code predicate `Cd` and the `bl scc_rt_print` at `Bl`,
each from the pc after the one before. -/
theorem print_chunks {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc') :
    ∃ l1 l2 l3 l4 l5 : List Item, PrintCode cx n b o m cw (l1 ++ l2 ++ l3 ++ l4 ++ l5) ∧
      Cd pc (directives l1) ∧
      Cd (pc + Int64.ofNat (4 * (directives l1).length)) (directives l2) ∧
      Cd (pc + Int64.ofNat (4 * (directives l1).length) + Int64.ofNat (4 * (directives l2).length))
        (directives l3) ∧
      Cd (pc + Int64.ofNat (4 * (directives l1).length) + Int64.ofNat (4 * (directives l2).length) +
        Int64.ofNat (4 * (directives l3).length)) (directives l4) ∧
      Cd (pc + Int64.ofNat (4 * (directives l1).length) + Int64.ofNat (4 * (directives l2).length) +
        Int64.ofNat (4 * (directives l3).length) + Int64.ofNat (4 * (directives l4).length)) (directives l5) ∧
      ∃ k', Bl (pc + Int64.ofNat (4 * (directives l1).length) + Int64.ofNat (4 * (directives l2).length) +
        Int64.ofNat (4 * (directives l3).length) + Int64.ofNat (4 * (directives l4).length) +
        Int64.ofNat (4 * (directives l5).length)) Scc.Lower.Names.print k' := by
  unfold printInsts at hi
  rw [InstsC2] at hi
  rcases hi with ⟨-, l1, c1, hc1, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨-, l2, c2, hc2, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨-, l3, c3, hc3, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨-, l4, c4, hc4, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨hc, -⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨a0, a1, l5, he, c5, hc5, hb5, -⟩
  · simp [Spike.Lib.LowerShape.isCall] at hc
  · simp at he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  simp only [Scc.IR.Inst.call.injEq, List.cons.injEq, and_true, true_and] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨l1, l2, l3, l4, l5, ⟨_, _, _, _, l1, l2, l3, l4, l5, c1, c2, c3, c4, c5, rfl⟩, hc1, hc2, hc3, hc4, hc5,
    _, hb5⟩

include hf h1 h16 in
/-- **The argument block's phase check** at its pc: its chunks pass the
code predicates' checks (`CdC`, `BlC`), each falls through to the next. -/
theorem print_ph {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {ra : Int64} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdC prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc') {L : List Item}
    (hL : PrintCode cx n b o m cw L) :
    blkPh okPc ph (fun _ => false) lab pc ra (directives L ++ blPrintD) = true := by
  unfold printInsts at hi
  rw [InstsC2] at hi
  rcases hi with ⟨-, l1, c1, hc1, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨-, l2, c2, hc2, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨-, l3, c3, hc3, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨-, l4, c4, hc4, hi⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he
  rw [InstsC2] at hi
  rcases hi with ⟨hc, -⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨a0, a1, l5, he, c5, hc5, hb5, -⟩
  · simp [Spike.Lib.LowerShape.isCall] at hc
  · simp at he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  simp only [Scc.IR.Inst.call.injEq, List.cons.injEq, and_true, true_and] at he
  obtain ⟨rfl, rfl⟩ := he
  have hPC : PrintCode cx n b o m cw (l1 ++ l2 ++ l3 ++ l4 ++ l5) :=
    ⟨_, _, _, _, l1, l2, l3, l4, l5, c1, c2, c3, c4, c5, rfl⟩
  obtain rfl := printCode_unique hL hPC
  have hok := printCode_okBlk hf h1 h16 hPC
  have hcl := okBlk_cls hok
  have hnt := okBlk_ntL hok (b := blPrintD) (by simp [blPrintD_eq])
  simp only [directives_append] at hnt hcl ⊢
  have cl : ∀ blk : List Directive, (∀ d ∈ blk, d ∈ directives l1 ++ directives l2 ++ directives l3 ++
      directives l4 ++ directives l5 ++ blPrintD) → ∀ d ∈ blk, (Spike.Lib.A64.Flow.classify d).isSome = true :=
    fun _ hs d hd => hcl d (hs d hd)
  obtain ⟨-, -, -, -, -, hbl, -⟩ := hBl _ _ _ hb5
  refine blkPh_appendNT (blkPh_appendNT (blkPh_appendNT (blkPh_appendNT (blkPh_appendNT ?_ ?_ ?_) ?_ ?_) ?_ ?_)
    ?_ ?_) ?_ hnt
  · exact blkPh_of_cdC (hCd _ _ hc1) (cl _ fun d hd => by simp [hd])
  · exact blkPh_of_cdC (hCd _ _ hc2) (cl _ fun d hd => by simp [hd])
  · exact nt_left (nt_left (nt_left (nt_left hnt)))
  · simp only [List.length_append, ← pc_add4]
    exact blkPh_of_cdC (hCd _ _ hc3) (cl _ fun d hd => by simp [hd])
  · exact nt_left (nt_left (nt_left hnt))
  · simp only [List.length_append, ← pc_add4]
    exact blkPh_of_cdC (hCd _ _ hc4) (cl _ fun d hd => by simp [hd])
  · exact nt_left (nt_left hnt)
  · simp only [List.length_append, ← pc_add4]
    exact blkPh_of_cdC (hCd _ _ hc5) (cl _ fun d hd => by simp [hd])
  · exact nt_left hnt
  · simp only [List.length_append, ← pc_add4]
    exact hbl

end Arg

/-! ## Blocks at their code -/

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt Ab : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

omit [Kraken.Executable.ValidLayout exe] in
/-- **A covered block at its code, the words of `rS` off its region from
the frame condition** (`hFO`), inside `SFacts`: as
`Spike.Lib.A64.Rt.blkW_postO` at the block's code `hcode` and its phase
check at the node's pc. -/
theorem blkW_postOc {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool} {ra : Int64}
    (hcode : CdOf exe endPc n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r,
      Spike.Lib.A64.Flow.classify blk[k] = some (AI.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  rw [← hI.labOk] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  refine blkW_sfacts hcode hok hR hal hlo hhi hC hpc hph' fun s m hF hD hc k hk s' hm _ _ => ?_
  subst hm
  exact Spike.Lib.A64.Rt.owned_off hR (by omega) hl hh hsub
    (Spike.Lib.A64.Flow.Ret0.stackOff_stable hfit _ _ (hFO _ hF) hD) hc

omit [Kraken.Executable.ValidLayout exe] in
/-- **A covered block's states at its code write nothing** (as
`Spike.Lib.A64.AllocG.blkW_noWr`). -/
theorem blkW_noWrC {n : ND} {blk : List Directive} {lo hi : Int}
    (hcode : CdOf exe endPc n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) :
    BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ _ k hk m hA' _
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨a, hca, haok, -⟩ := Spike.Lib.A64.Flow.okBlk_get (_root_.Executable.labels exe).label
    (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.A64.Flow.classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s he hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  obtain ⟨m', hex, -⟩ := Spike.Lib.A64.Flow.exec_ai haok hR hal hlo hhi hc hreg hA'
  exact noWr_done hex

omit [Kraken.Executable.ValidLayout exe] in
/-- **A covered block's states at its code are off a system call** (as
`blkW_noSys`). -/
theorem blkW_noSysC {n : ND} {blk : List Directive} {lo hi : Int}
    (hcode : CdOf exe endPc n.pc blk) (hok : okBlk lo hi n.o blk = true) :
    BlkW (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ _ k hk m _ _
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨a, hca, -, -⟩ := Spike.Lib.A64.Flow.okBlk_get (_root_.Executable.labels exe).label
    (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.A64.Flow.classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s he hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  refine Scc.Sem.A64.atSvc_false_of_cellAt hc fun imm h => ?_
  cases a <;> (try simp only [Spike.Lib.A64.Flow.AI.toDir] at h) <;> (try cases h)
  exact absurd (hreg _ _ rfl) (by simp [Spike.Lib.A64.Flow.RegOnly])

omit [Kraken.Executable.ValidLayout exe] in
/-- **A covered block at its code without a `ret` is inside `W2`** at the
frames `fs`, its states at `PlacedSE` (`hP`): as `blkW_w2BP` at the block's code
(`hcode`) and its phase check at the node's pc (`hph`). -/
theorem blkW_w2BPc {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List Directive} (hcode : CdOf exe endPc n.pc blk)
    (hph : blkPh okPc ph (fun _ => false) lab n.pc ra blk = true) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hP : BlkW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk := by
  have hS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) blk :=
    blkW_postOc (n := dumN n) (dead := fun _ => false) (ra := ra) hI hcode hok hR
      hal hlo hhi (fun _ _ h => h.1 ▸ cfacts_c0) hph (fun _ _ _ k hk r hr => (noRet_false hnr k hk r hr).elim)
      (fun _ _ _ => rfl) hl hh hsub hfit hFO
  have hWN : BlkW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.A64.AllocG.BlkW.imp (blkW_noWrC hcode hok hR hal hlo hhi) (blkW_noSysC hcode hok)
      fun _ _ h1 h2 => ⟨h1, h2⟩
  have hPW : BlkW (fun s c => PlacedSE Λ lbl s c fs ∧ (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false)
      (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.A64.AllocG.BlkW.imp hP hWN fun _ _ h1 h2 => ⟨h1, h2⟩
  refine BlkW.w2E hp hS ?_ hJ
  exact Spike.Lib.A64.AllocG.BlkW.imp hab hPW fun s c h1 h2 =>
    ⟨h1, h2.1, fun _ _ _ _ => wrOkA_of_noWr h2.2.1, fun h => absurd h (by rw [h2.2.2]; decide)⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **A call of `print`'s argument block and its `bl` inside `W2`** at the
frames `fs` (`PrintBlkW`'s first conjunct): at `printInsts`' cells `L`
(`hL`), the block's code from `pc` (`print_code`) and its phase check
(`print_ph`), in any region holding the frame; its states at `PlacedSE` (`hP`), in
the abort phase's facts (`hab`); at an invariant whose controls exclude
`main`'s `ret` and are free of `ZBad` (`hJ`). -/
theorem printBlkW_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {cx : FnCtx}
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    {n : Nat} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {L : List Item}
    (hL : PrintCode cx n b o m cw L) {pc ra : Int64} {Jn : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    (hcode : CdOf exe endPc pc (directives L ++ blPrintD))
    (hph : blkPh okPc ph (fun _ => false) lab pc ra (directives L ++ blPrintD) = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ⟨pc, oF cx, Jn⟩
      (directives L ++ blPrintD))
    (hP : BlkW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F ⟨pc, oF cx, Jn⟩
      (directives L ++ blPrintD))
    (hJ : ∀ σ c, Jn σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ⟨pc, oF cx, Jn⟩
      (directives L ++ blPrintD) :=
  blkW_w2BPc (n := ⟨pc, oF cx, Jn⟩) hI hR hal hlo hhi hl hh hsub hfit hFO hp hcode hph
    (printCode_okBlk hf h1 h16 hL) (printCode_noRet hf h1 h16 hL) hab hP hJ

/-- **A chunk of the code predicate is code** (`code_of` at its `blockAt`). -/
theorem cdOf_of_cdC {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {ra pc : Int64}
    {blk : List Directive} (h : CdC prog okPc ph lab ra pc blk) : CdOf exe endPc pc blk := by
  obtain ⟨-, L, j, hpc, hb, -⟩ := h
  exact Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := pc) (by rw [hI.labOk]; exact hpc)

/-- **A call's `bl` is code** (`code_of` at its `blockAt`). -/
theorem cdOf_of_blC {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {cx : FnCtx}
    {ra pc : Int64} {g : Label} {k : Nat} (h : BlC prog okPc ph lab cx ra pc g k) : CdOf exe endPc pc [blD g] := by
  obtain ⟨L, j, hpc, hb, -⟩ := h
  exact Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := pc) (by rw [hI.labOk]; exact hpc)

/-- **A call of `print`'s argument block and its `bl` inside `W2`** at the
code predicates `CdC`, `BlC` (`hCd`, `hBl`; `printBlkW_w2` at
`print_code`, `print_ph`): at `printInsts`' code from `pc` (`hi`) and its
cells `L` (`hL`). -/
theorem printBlkW_w2C {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {cx : FnCtx}
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdC prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc') {L : List Item}
    (hL : PrintCode cx n b o m cw L) {Jn : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ⟨pc, oF cx, Jn⟩
      (directives L ++ blPrintD))
    (hP : BlkW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F ⟨pc, oF cx, Jn⟩
      (directives L ++ blPrintD))
    (hJ : ∀ σ c, Jn σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ⟨pc, oF cx, Jn⟩
      (directives L ++ blPrintD) := by
  obtain ⟨L', hL', hcode, -⟩ := print_code (fun _ _ h => cdOf_of_cdC hI (hCd _ _ h))
    (fun _ _ _ h => cdOf_of_blC hI (hBl _ _ _ h)) hi
  obtain rfl := printCode_unique hL hL'
  exact printBlkW_w2 hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hL hcode
    (print_ph hf h1 h16 hCd hBl hi hL) hab hP hJ

end W

/-! ## The abort phase and the controls -/

/-- **A run of positions off the write abort, then another**: every
instruction of `a ++ b` is at a position off the write abort when every one
of `a` is and every one of `b` after `a` is. -/
theorem posOff_append {prog : List Directive} {lab : Label → Int64} {pc : Int64} {a b : List Directive}
    (ha : ∀ i < a.length, PosOff prog lab (pc + Int64.ofNat (4 * i)))
    (hb : ∀ i < b.length, PosOff prog lab (pc + Int64.ofNat (4 * a.length) + Int64.ofNat (4 * i))) :
    ∀ i < (a ++ b).length, PosOff prog lab (pc + Int64.ofNat (4 * i)) := by
  intro i hi
  rcases Nat.lt_or_ge i a.length with h | h
  · exact ha i h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    have := hb j (by simp at hi; omega)
    rwa [← Spike.Lib.A64.Flow.ofNat4_add] at this

/-- **A chunk of the code predicate off the write abort's labels is at
positions off the write abort.** -/
theorem posOff_cdCL {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {ra pc : Int64} {blk : List Directive} (h : CdCL prog okPc ph lab ra pc blk) :
    ∀ i < blk.length, PosOff prog lab (pc + Int64.ofNat (4 * i)) :=
  fun _ hi => posOff_of_subCdL (SubCd.whole h) hi

/-- **`print`'s entry is a position off the write abort**, in a program
with `print`'s code. -/
theorem posOff_printEntry {prog : List Directive} {lab : Label → Int64}
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) : PosOff prog lab (lab "scc_rt_print") :=
  ⟨"scc_rt_print", 0, Scc.Cert.Rt.A64.inRun_of_blockAt (Spike.Lib.A64.PrintG.printIn_spec hpr).1 (i := 0)
    (by decide), by decide, Spike.Lib.A64.Flow.ofNat4_zero _⟩

section AbW

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A call of `print`'s argument block and its `bl` keep the write
abort's phase** (`printBlkW_w2C`'s `hab`, by `blkW_abSt_pos`): its chunks at
the code predicate off the write abort's labels (`hCd`, `CdCL`), its `bl` at
a position off the write abort (`hBl`, e.g. `BlC2L`'s `toBlC2`, `posOff`),
in a program with the runtime's code (`hpr`, `habI`). Every fall-through is
a position of the block, the `bl`'s target `print`'s entry. -/
theorem printBlkW_ab {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k ∧ PosOff prog lab pc)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc') {L : List Item}
    (hL : PrintCode cx n b o m cw L) {Jn : Spike.Lib.A64.Flow.AS → Ctl → Prop} :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab lab) s) (fun _ _ => False) exe endPc R F
      ⟨pc, oF cx, Jn⟩ (directives L ++ blPrintD) := by
  have hCdC : ∀ pc blk, Cd pc blk → CdC prog okPc ph lab ra pc blk := fun _ _ h => (hCd _ _ h).toCdC
  have hBlC : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra pc g k := fun _ _ _ h => (hBl _ _ _ h).1
  obtain ⟨L', hL', hcode, -⟩ := print_code (fun _ _ h => cdOf_of_cdC hI (hCdC _ _ h))
    (fun _ _ _ h => cdOf_of_blC hI (hBlC _ _ _ h)) hi
  obtain rfl := printCode_unique hL hL'
  have hph := print_ph hf h1 h16 hCdC hBlC hi hL
  have hok := printCode_okBlk hf h1 h16 hL
  have hpos : ∀ i < (directives L ++ blPrintD).length, PosOff prog lab (pc + Int64.ofNat (4 * i)) := by
    obtain ⟨l1, l2, l3, l4, l5, hPC, hc1, hc2, hc3, hc4, hc5, k', hb5⟩ := print_chunks hi
    obtain rfl := printCode_unique hL hPC
    simp only [directives_append]
    refine posOff_append (posOff_append (posOff_append (posOff_append (posOff_append ?_ ?_) ?_) ?_) ?_) ?_
    · exact posOff_cdCL (hCd _ _ hc1)
    · exact posOff_cdCL (hCd _ _ hc2)
    · simp only [List.length_append, ← pc_add4]; exact posOff_cdCL (hCd _ _ hc3)
    · simp only [List.length_append, ← pc_add4]; exact posOff_cdCL (hCd _ _ hc4)
    · simp only [List.length_append, ← pc_add4]; exact posOff_cdCL (hCd _ _ hc5)
    · simp only [List.length_append, ← pc_add4]
      intro i hi
      have : i = 0 := by simp [blPrintD_eq] at hi; omega
      subst this
      rw [Spike.Lib.A64.Flow.ofNat4_zero]
      exact (hBl _ _ _ hb5).2
  refine blkW_abSt_pos hI hpr habI (fun s he hn => hcode s he hn) hok hR hal hlo hhi hph
    (printCode_noRet hf h1 h16 hL) ?_
  intro σ c _ k hk a ha t ht
  refine .inl ?_
  rcases Nat.lt_or_ge (k + 1) (directives L ++ blPrintD).length with h' | h'
  · obtain ⟨a', ha', -, hterm⟩ := Spike.Lib.A64.Flow.okBlk_get lab (am := ⟨pc, oF cx, σ⟩) hok hk
    rw [ha] at ha'
    cases ha'
    have hnt := hterm h'
    have key : ∀ f, aiTgts lab f ra a = [f] := by intro f; cases a <;> simp_all [AI.isTerm, aiTgts]
    rw [key, List.mem_singleton] at ht
    subst ht
    rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
    exact hpos _ h'
  · have hk' : k = (directives L).length := by simp [blPrintD_eq] at hk h' ⊢; omega
    subst hk'
    rw [List.getElem_append_right (Nat.le_refl _)] at ha
    simp only [Nat.sub_self, blPrintD_eq] at ha
    have h0 : Spike.Lib.A64.Flow.classify (.instr ⟨.W64, .BL (.label "scc_rt_print")⟩) =
        some (AI.bl "scc_rt_print") := rfl
    rw [List.getElem_cons_zero, h0] at ha
    cases ha
    simp only [aiTgts, List.mem_singleton] at ht
    subst ht
    exact posOff_printEntry hpr

end AbW

/-- **`FrOk2` at a `ret`** inside `print`'s call: the caller's continuation
`e` and frames `fs` free of `ZBad` (`PrintWE`'s source after an empty
slice's body). -/
theorem frOk2_ret {a : CoreTerm.At} {env : TermRun.Env} {x : String} {e : Expr} {c1 : Ctl} {fs : List TermRun.Frame}
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) :
    FrOk2 ⟨.ret a, env, none⟩ (Spike.Lib.LowerNode.printFrame x e c1 :: fs) := by
  refine ⟨by simp [NoS], ?_⟩
  intro fr hfr
  rcases List.mem_cons.mp hfr with rfl | hfr
  · exact he
  · exact hfs fr hfr

/-- **The controls of `printJ` at `print`'s frames** (`printBlkW_w2C`'s
`hJ`): from `FrOk2` at its control `cE`, the frames nonempty. -/
theorem printJ_hJ {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {cx : FnCtx} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {c1 cE : Ctl}
    {fr : TermRun.Frame} {fs : List TermRun.Frame} (h : FrOk2 cE (fr :: fs)) :
    ∀ σ c, printJ p lbl lsize cx fp ra tp c0 t env lits cs bufs c1 cE σ c →
      (fr :: fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c (fr :: fs) :=
  fun _ _ hc => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), hc.1 ▸ h⟩

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.print_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.print_ph

/-- info: 'Spike.Lib.LowerA64.printBlkW_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printBlkW_w2

/-- info: 'Spike.Lib.LowerA64.printBlkW_w2C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printBlkW_w2C

/-- info: 'Spike.Lib.LowerA64.printBlkW_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printBlkW_ab
