/-
**The code of `print`'s argument block and call in an `Accepted2` body**
(x86-64): `printInsts` (`Spike/Lib/LowerShapeC2.lean`) at `InstsC2`
(`Body2.lean`) as `print_block_segW`'s blocks
(`Spike/Lib/LowerX64/PrintCall.lean`).

`printInsts n b (.reg o) m c` is four plain instructions, each its own code
block (`lo := ext.w32 o`, `s := b + lo`, `cap := m · 8`,
`k := select (c < cap) c cap`), then `call [] print [s, k]`: the argument
loads into `%rdi`, `%rsi` and the call's block (`Bl`). Laid end to end
they are `pblk`'s cells: `preD` (the first two instructions and the
multiply's operand loads), the multiply, `postD` (the multiply's store, the
select, the argument loads) and `call scc_rt_print`.

- `emits_ext32`, `emits_addR`, `emits_mul`, `emits_selectU`: the four
  instructions' items;
- `getOps_two`: the call's argument loads;
- `insts_print`: `InstsC2` of `printInsts` as its five blocks;
- `print_code`: the blocks as `pblk`'s code, with the operands' loads and
  the fresh registers' slots.
- `PrintCodeC`, `print_codeC`, `PrintCodeC.cdOf`: the same with the block's
  cells' sizes the chunks', each chunk at the code predicate.
-/
import Spike.Lib.LowerX64.LaneC2
import Spike.Lib.LowerX64.PrintCall

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item ld st i64 i32 xr xm om or_ mem emitInst ins rax64 cc)
open Scc.Lower.InvX64
open Spike.Lib.LowerShape (isCall printInsts)
open Scc.Lower.Inv (regName)

set_option linter.unusedSimpArgs false

/-! ## The instructions' items -/

section Items

variable {fr : Scc.Emit.X64.Frame} {sm : Option Scc.IR.StackMap.Entry}

theorem emitInst_ext32_def (d : Scc.IR.Reg) (a : Scc.IR.Operand) :
    emitInst fr sm (.ext false .w32 d a) = (do ld fr a .rax; ins ext32D; st fr .rax d) := rfl

theorem emitInst_addR_def (d : Scc.IR.Reg) (a b : Scc.IR.Operand) :
    emitInst fr sm (.bin .add d a b) = (do ld fr a .rax; ld fr b .rcx; ins addD; st fr .rax d) := rfl

theorem emitInst_mul_def (d : Scc.IR.Reg) (a b : Scc.IR.Operand) :
    emitInst fr sm (.bin .mul d a b) =
      (do ld fr a .rax; ld fr b .rcx; ins (i64 (.imul none (xr .rax) (or_ .rcx))); st fr .rax d) := rfl

theorem emitInst_selectU_def (d : Scc.IR.Reg) (a b t f : Scc.IR.Operand) :
    emitInst fr sm (.select .ult d a b t f) = (do
      ld fr t .rdx; ld fr f .rsi; Scc.Emit.X64.cmpAB fr a b; ins movRsiD; ins (cmovD .c); st fr .rax d) := rfl

/-- **The items of `ext false .w32 d a`.** -/
theorem emits_ext32 {d : Scc.IR.Reg} {a : Scc.IR.Operand} {l : List Item}
    (h : Emits (emitInst fr sm (.ext false .w32 d a)) l) :
    ∃ la off, getOp fr .rax a = .ok la ∧ rsOf fr d = some off ∧ l = la ++ [Item.d ext32D, Item.d (stDir off)] := by
  have h0 := h {}
  rw [emitInst_ext32_def] at h0
  rcases ld_cases fr a .rax {} with ⟨la, ha, e1⟩ | ⟨e, e1⟩
  · rw [bind_ok e1, bind_ok (ins_eq _ _)] at h0
    rcases st_cases fr d _ with ⟨off, hd, -⟩ | ⟨e, e3⟩
    · exact ⟨la, off, ha, hd, emits_out h (emitInst_ext32_items ha hd sm {})⟩
    · rw [e3] at h0; cases h0
  · rw [bind_err e1] at h0; cases h0

/-- **The items of `bin .add d a b`.** -/
theorem emits_addR {d : Scc.IR.Reg} {a b : Scc.IR.Operand} {l : List Item}
    (h : Emits (emitInst fr sm (.bin .add d a b)) l) :
    ∃ la lb off, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧ rsOf fr d = some off ∧
      l = la ++ lb ++ [Item.d addD, Item.d (stDir off)] := by
  have h0 := h {}
  rw [emitInst_addR_def] at h0
  rcases ld_cases fr a .rax {} with ⟨la, ha, e1⟩ | ⟨e, e1⟩
  · rw [bind_ok e1] at h0
    rcases ld_cases fr b .rcx _ with ⟨lb, hb, e2⟩ | ⟨e, e2⟩
    · rw [bind_ok e2, bind_ok (ins_eq _ _)] at h0
      rcases st_cases fr d _ with ⟨off, hd, -⟩ | ⟨e, e3⟩
      · exact ⟨la, lb, off, ha, hb, hd, emits_out h (emitInst_add_items ha hb hd sm {})⟩
      · rw [e3] at h0; cases h0
    · rw [bind_err e2] at h0; cases h0
  · rw [bind_err e1] at h0; cases h0

/-- **The items of `bin .mul d a b`.** -/
theorem emits_mul {d : Scc.IR.Reg} {a b : Scc.IR.Operand} {l : List Item}
    (h : Emits (emitInst fr sm (.bin .mul d a b)) l) :
    ∃ la lb off, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧ rsOf fr d = some off ∧
      l = la ++ lb ++ [Item.d mulFI.toDir, Item.d (stDir off)] := by
  have h0 := h {}
  rw [emitInst_mul_def] at h0
  rcases ld_cases fr a .rax {} with ⟨la, ha, e1⟩ | ⟨e, e1⟩
  · rw [bind_ok e1] at h0
    rcases ld_cases fr b .rcx _ with ⟨lb, hb, e2⟩ | ⟨e, e2⟩
    · rw [bind_ok e2, bind_ok (ins_eq _ _)] at h0
      rcases st_cases fr d _ with ⟨off, hd, -⟩ | ⟨e, e3⟩
      · exact ⟨la, lb, off, ha, hb, hd, emits_out h (emitInst_mul_items ha hb hd sm {})⟩
      · rw [e3] at h0; cases h0
    · rw [bind_err e2] at h0; cases h0
  · rw [bind_err e1] at h0; cases h0

/-- **The items of `select .ult d a b t f`.** -/
theorem emits_selectU {d : Scc.IR.Reg} {a b t f : Scc.IR.Operand} {l : List Item}
    (h : Emits (emitInst fr sm (.select .ult d a b t f)) l) :
    ∃ lt lf la lb off, getOp fr .rdx t = .ok lt ∧ getOp fr .rsi f = .ok lf ∧ getOp fr .rax a = .ok la ∧
      getOp fr .rcx b = .ok lb ∧ rsOf fr d = some off ∧
      l = lt ++ lf ++ la ++ lb ++ [Item.d cmpD, Item.d movRsiD, Item.d (cmovD .c), Item.d (stDir off)] := by
  have h0 := h {}
  rw [emitInst_selectU_def] at h0
  simp only [Scc.Emit.X64.cmpAB, bind_assoc] at h0
  rcases ld_cases fr t .rdx {} with ⟨lt, ht, e1⟩ | ⟨e, e1⟩
  · rw [bind_ok e1] at h0
    rcases ld_cases fr f .rsi _ with ⟨lf, hf, e2⟩ | ⟨e, e2⟩
    · rw [bind_ok e2] at h0
      rcases ld_cases fr a .rax _ with ⟨la, ha, e3⟩ | ⟨e, e3⟩
      · rw [bind_ok e3] at h0
        rcases ld_cases fr b .rcx _ with ⟨lb, hb, e4⟩ | ⟨e, e4⟩
        · rw [bind_ok e4, bind_ok (ins_eq _ _), bind_ok (ins_eq _ _), bind_ok (ins_eq _ _)] at h0
          rcases st_cases fr d _ with ⟨off, hd, -⟩ | ⟨e, e5⟩
          · exact ⟨lt, lf, la, lb, off, ht, hf, ha, hb, hd, emits_out h (emitInst_select_items ht hf ha hb hd sm {})⟩
          · rw [e5] at h0; cases h0
        · rw [bind_err e4] at h0; cases h0
      · rw [bind_err e3] at h0; cases h0
    · rw [bind_err e2] at h0; cases h0
  · rw [bind_err e1] at h0; cases h0

/-- **The call's two argument loads**: `s` into `%rdi`, `k` into `%rsi`. -/
theorem getOps_two {s k : Scc.IR.Operand} {lw : List Item}
    (h : getOps fr ([s, k].zip Scc.Emit.X64.argRegs) = .ok lw) :
    ∃ ls lk, getOp fr .rdi s = .ok ls ∧ getOp fr .rsi k = .ok lk ∧ lw = ls ++ lk := by
  simp only [Scc.Emit.X64.argRegs, List.zip_cons_cons, List.zip_nil_left, getOps] at h
  cases hs : getOp fr .rdi s with
  | error e => simp [hs] at h
  | ok ls =>
    cases hk : getOp fr .rsi k with
    | error e => simp [hs, hk] at h
    | ok lk =>
      simp only [hs, hk] at h
      cases h
      exact ⟨ls, lk, rfl, rfl, by simp⟩

end Items

/-! ## The block's code -/

section Code

variable {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
  {Bl : Int64 → Nat → Label → Nat → Prop}

theorem dirs_cons_d (x : Directive) (l : List Item) : dirs (Item.d x :: l) = x :: dirs l := rfl

theorem dirs_nil : dirs [] = [] := rfl

/-- **A plain instruction's code** at `InstsC2`: its items' directives at
`pc`, the rest after them. -/
theorem insts_cons_plain {i : Scc.IR.Inst} {is : List Scc.IR.Inst} {k k' : Nat} {pc pc' : Int64}
    (hi : isCall i = false) (h : InstsC2 fr Cd Bl k pc (i :: is) k' pc') :
    ∃ l zs, Emits (emitInst fr none i) l ∧ zs.length = (dirs l).length ∧ Cd pc ((dirs l).zip zs) ∧
      InstsC2 fr Cd Bl k (pc + Int64.ofNat zs.sum) is k' pc' := by
  rcases h with ⟨-, h⟩ | ⟨_, _, _, _, _, _, _, _, rfl, -⟩ | ⟨_, _, _, _, _, _, _, rfl, -⟩ | ⟨_, _, _, _, rfl, -⟩
  · exact h
  all_goals simp [isCall] at hi

/-- **`print`'s call** at `InstsC2`: its argument loads at `pc`, the
call's block after them, the rest after it. -/
theorem insts_print_call {ws : List Scc.IR.Operand} {is : List Scc.IR.Inst} {k k' : Nat} {pc pc' : Int64}
    (h : InstsC2 fr Cd Bl k pc (.call [] Scc.Lower.Names.print ws :: is) k' pc') :
    ∃ lw zs zc, getOps fr (ws.zip Scc.Emit.X64.argRegs) = .ok lw ∧ zs.length = (dirs lw).length ∧
      Cd pc ((dirs lw).zip zs) ∧ Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.print k ∧
      InstsC2 fr Cd Bl (k + 1) (pc + Int64.ofNat zs.sum + Int64.ofNat zc) is k' pc' := by
  rcases h with ⟨hc, -⟩ | ⟨_, _, _, _, _, _, _, _, hi, -⟩ | ⟨_, _, _, _, _, _, _, hi, -⟩ |
    ⟨ws', lw, zs, zc, hi, -, hg, hz, hc, hb, hr⟩
  · simp [isCall] at hc
  · simp at hi
  · simp at hi
  · simp only [Scc.IR.Inst.call.injEq, true_and] at hi
    subst hi
    exact ⟨lw, zs, zc, hg, hz, hc, hb, hr⟩

/-- **`print`'s argument block and call as `pblk`'s code**: from
`InstsC2` of `printInsts n b (.reg o) m c` at `pc`, the fresh registers'
slots, the operands' loads `print_block_segW` asks for, and the block's
four pieces' code (before the multiply, the multiply, after it, the
`call`); the call's block's code from `hBl`. The counter goes up by one
(the call) and the code ends after the `call`. -/
theorem print_code {exe : _root_.Executable} {endPc : Int64} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → CdOf exe endPc pc [(i64 (.call (Scc.Emit.X64.rel g)), z)])
    {kk kk' : Nat} {pc pc' : Int64} {n : Nat} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m c : Scc.IR.Operand}
    (h : InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m c) kk' pc') :
    ∃ (olo os ocap okk : Int) (lO lB lL lM l8 lN lC lN' lC' lS lK : List Item) (zs1 zs2 : List Nat) (zM zc : Nat),
      rsOf fr (regName "lo" n) = some olo ∧ rsOf fr (regName "s" (n + 1)) = some os ∧
      rsOf fr (regName "cap" (n + 2)) = some ocap ∧ rsOf fr (regName "k" (n + 3)) = some okk ∧
      getOp fr .rax (.reg o) = .ok lO ∧ getOp fr .rax b = .ok lB ∧
      getOp fr .rcx (.reg (regName "lo" n)) = .ok lL ∧ getOp fr .rax m = .ok lM ∧
      getOp fr .rcx (Scc.Lower.imm 8) = .ok l8 ∧ getOp fr .rdx c = .ok lN ∧
      getOp fr .rsi (.reg (regName "cap" (n + 2))) = .ok lC ∧ getOp fr .rax c = .ok lN' ∧
      getOp fr .rcx (.reg (regName "cap" (n + 2))) = .ok lC' ∧ getOp fr .rdi (.reg (regName "s" (n + 1))) = .ok lS ∧
      getOp fr .rsi (.reg (regName "k" (n + 3))) = .ok lK ∧
      zs1.length = (preD lO lB lL lM l8 olo os).length ∧
      zs2.length = (postD lN lC lN' lC' lS lK ocap okk).length ∧
      CdOf exe endPc pc ((preD lO lB lL lM l8 olo os).zip zs1) ∧
      CdOf exe endPc (pc + Int64.ofNat zs1.sum) [(mulFI.toDir, zM)] ∧
      CdOf exe endPc (pc + Int64.ofNat zs1.sum + Int64.ofNat zM) ((postD lN lC lN' lC' lS lK ocap okk).zip zs2) ∧
      CdOf exe endPc (pc + Int64.ofNat zs1.sum + Int64.ofNat zM + Int64.ofNat zs2.sum) [(callD, zc)] ∧
      kk' = kk + 1 ∧ pc' = pc + Int64.ofNat zs1.sum + Int64.ofNat zM + Int64.ofNat zs2.sum + Int64.ofNat zc := by
  simp only [printInsts] at h
  obtain ⟨l1, zs1, hE1, hz1, hc1, h⟩ := insts_cons_plain rfl h
  obtain ⟨l2, zs2, hE2, hz2, hc2, h⟩ := insts_cons_plain rfl h
  obtain ⟨l3, zs3, hE3, hz3, hc3, h⟩ := insts_cons_plain rfl h
  obtain ⟨l4, zs4, hE4, hz4, hc4, h⟩ := insts_cons_plain rfl h
  obtain ⟨lw, zs5, zc, hg, hz5, hc5, hbl, h⟩ := insts_print_call h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨lO, olo, hO, hlo, rfl⟩ := emits_ext32 hE1
  obtain ⟨lB, lL, os, hB, hL, hs, rfl⟩ := emits_addR hE2
  obtain ⟨lM, l8, ocap, hM, h8, hcap, rfl⟩ := emits_mul hE3
  obtain ⟨lN, lC, lN', lC', okk, hN, hC, hN', hC', hk, rfl⟩ := emits_selectU hE4
  obtain ⟨lS, lK, hS, hK, rfl⟩ := getOps_two hg
  obtain ⟨dO, eO⟩ := dirs_getOp hO
  obtain ⟨dB, eB⟩ := dirs_getOp hB
  obtain ⟨dL, eL⟩ := dirs_getOp hL
  obtain ⟨dM, eM⟩ := dirs_getOp hM
  obtain ⟨d8, e8⟩ := dirs_getOp h8
  obtain ⟨dN, eN⟩ := dirs_getOp hN
  obtain ⟨dC, eC⟩ := dirs_getOp hC
  obtain ⟨dN', eN'⟩ := dirs_getOp hN'
  obtain ⟨dC', eC'⟩ := dirs_getOp hC'
  obtain ⟨dS, eS⟩ := dirs_getOp hS
  obtain ⟨dK, eK⟩ := dirs_getOp hK
  simp only [dirs_append, dirs_cons_d, dirs_nil, eO, eB, eL, eM, e8, eN, eC, eN', eC', eS, eK, List.cons_append,
    List.nil_append] at hz1 hz2 hz3 hz4 hz5 hc1 hc2 hc3 hc4 hc5
  have hpre : ∀ zs : List Nat, (preD lO lB lL lM l8 olo os).zip zs =
      [dO, ext32D, stDir olo, dB, dL, addD, stDir os, dM, d8].zip zs := by
    intro zs; simp only [preD, dirs_append, eO, eB, eL, eM, e8, List.cons_append, List.nil_append, List.append_assoc]
  have hpost : ∀ zs : List Nat, (postD lN lC lN' lC' lS lK ocap okk).zip zs =
      [stDir ocap, dN, dC, dN', dC', cmpD, movRsiD, cmovD .c, stDir okk, dS, dK].zip zs := by
    intro zs; simp only [postD, dirs_append, eN, eC, eN', eC', eS, eK, List.cons_append, List.nil_append,
      List.append_assoc]
  match zs1, zs2, zs3, zs4, zs5, hz1, hz2, hz3, hz4, hz5 with
  | [a1, a2, a3], [b1, b2, b3, b4], [c1, c2, c3, c4], [d1, d2, d3, d4, d5, d6, d7, d8'], [e1, e2],
      _, _, _, _, _ =>
    have C1 := hCd _ _ hc1
    have C2 := hCd _ _ hc2
    have C3 := hCd _ _ hc3
    have C4 := hCd _ _ hc4
    have C5 := hCd _ _ hc5
    have CB := hBl _ _ _ _ hbl
    simp only [List.zip_cons_cons, List.zip_nil_right, List.sum_cons, List.sum_nil, Nat.add_zero,
      Int64.ofNat_add, Int64.add_assoc] at C1 C2 C3 C4 C5 CB
    have big := cdOf_append (cdOf_append (cdOf_append (cdOf_append C1 (B := [_, _, _, _]) (by
        simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
          Int64.add_assoc] using C2)) (B := [_, _, _, _]) (by
        simpa only [List.map_cons, List.map_nil, List.map_append, List.cons_append, List.nil_append,
          List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using C3))
        (B := [_, _, _, _, _, _, _, _]) (by
        simpa only [List.map_cons, List.map_nil, List.map_append, List.cons_append, List.nil_append,
          List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using C4))
        (B := [_, _]) (by
        simpa only [List.map_cons, List.map_nil, List.map_append, List.cons_append, List.nil_append,
          List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using C5)
    simp only [List.cons_append, List.nil_append] at big
    refine ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, [a1, a2, a3, b1, b2, b3, b4, c1, c2],
      [c4, d1, d2, d3, d4, d5, d6, d7, d8', e1, e2], c3, zc, hlo, hs, hcap, hk, hO, hB, hL, hM, h8, hN, hC, hN',
      hC', hS, hK, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · simp only [preD, dirs_append, eO, eB, eL, eM, e8, List.length_append, List.length_cons, List.length_nil]
    · simp only [postD, dirs_append, eN, eC, eN', eC', eS, eK, List.length_append, List.length_cons,
        List.length_nil]
    · rw [hpre]
      have e := cdOf_sub (pre := []) (blk := [(dO, a1), (ext32D, a2), (stDir olo, a3), (dB, b1), (dL, b2),
        (addD, b3), (stDir os, b4), (dM, c1), (d8, c2)]) (post := [_, _, _, _, _, _, _, _, _, _, _, _])
        (by simpa only [List.cons_append, List.nil_append] using big)
      simpa only [List.zip_cons_cons, List.zip_nil_right, List.map_nil, List.sum_nil,
        Scc.Cert.Rt.X64.Print.off0] using e
    · have e := cdOf_sub (pre := [(dO, a1), (ext32D, a2), (stDir olo, a3), (dB, b1), (dL, b2),
        (addD, b3), (stDir os, b4), (dM, c1), (d8, c2)]) (blk := [_]) (post := [_, _, _, _, _, _, _, _, _, _, _])
        (by simpa only [List.cons_append, List.nil_append] using big)
      simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
        Int64.add_assoc] using e
    · rw [hpost]
      have e := cdOf_sub (pre := [(dO, a1), (ext32D, a2), (stDir olo, a3), (dB, b1), (dL, b2),
        (addD, b3), (stDir os, b4), (dM, c1), (d8, c2), (_, c3)]) (blk := [_, _, _, _, _, _, _, _, _, _, _])
        (post := []) (by simpa only [List.cons_append, List.nil_append, List.append_nil] using big)
      simpa only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using e
    · simpa only [callD, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using CB
    · simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc]

/-- **`printInsts`' code at `pc` as its chunks** (`print_codeC`): the fresh
registers' slots and the operands' loads (each one directive), each
instruction's chunk at the code predicate `Cd` with its cells' sizes, the
`call scc_rt_print` at `Bl` (the counter `kk`), and `B` the block laid out
from those sizes. Unlike `print_code`'s, the sizes are the chunks'. -/
def PrintCodeC (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) (kk : Nat) (pc : Int64) (n : Nat) (b : Scc.IR.Operand)
    (o : Scc.IR.Reg) (m c : Scc.IR.Operand) (B : PBlk) : Prop :=
  ∃ (olo os ocap okk : Int) (lO lB lL lM l8 lN lC lN' lC' lS lK : List Item)
    (dO dB dL dM dI dN dC dN' dC' dS dK : Directive)
    (a1 a2 a3 b1 b2 b3 b4 c1 c2 c3 c4 e1 e2 e3 e4 e5 e6 e7 e8 g1 g2 zc : Nat),
    rsOf fr (regName "lo" n) = some olo ∧ rsOf fr (regName "s" (n + 1)) = some os ∧
    rsOf fr (regName "cap" (n + 2)) = some ocap ∧ rsOf fr (regName "k" (n + 3)) = some okk ∧
    getOp fr .rax (.reg o) = .ok lO ∧ getOp fr .rax b = .ok lB ∧
    getOp fr .rcx (.reg (regName "lo" n)) = .ok lL ∧ getOp fr .rax m = .ok lM ∧
    getOp fr .rcx (Scc.Lower.imm 8) = .ok l8 ∧ getOp fr .rdx c = .ok lN ∧
    getOp fr .rsi (.reg (regName "cap" (n + 2))) = .ok lC ∧ getOp fr .rax c = .ok lN' ∧
    getOp fr .rcx (.reg (regName "cap" (n + 2))) = .ok lC' ∧ getOp fr .rdi (.reg (regName "s" (n + 1))) = .ok lS ∧
    getOp fr .rsi (.reg (regName "k" (n + 3))) = .ok lK ∧
    dirs lO = [dO] ∧ dirs lB = [dB] ∧ dirs lL = [dL] ∧ dirs lM = [dM] ∧ dirs l8 = [dI] ∧ dirs lN = [dN] ∧
    dirs lC = [dC] ∧ dirs lN' = [dN'] ∧ dirs lC' = [dC'] ∧ dirs lS = [dS] ∧ dirs lK = [dK] ∧
    Cd pc [(dO, a1), (ext32D, a2), (stDir olo, a3)] ∧
    Cd (pc + Int64.ofNat (a1 + a2 + a3)) [(dB, b1), (dL, b2), (addD, b3), (stDir os, b4)] ∧
    Cd (pc + Int64.ofNat (a1 + a2 + a3 + b1 + b2 + b3 + b4))
      [(dM, c1), (dI, c2), (mulFI.toDir, c3), (stDir ocap, c4)] ∧
    Cd (pc + Int64.ofNat (a1 + a2 + a3 + b1 + b2 + b3 + b4 + c1 + c2 + c3 + c4))
      [(dN, e1), (dC, e2), (dN', e3), (dC', e4), (cmpD, e5), (movRsiD, e6), (cmovD .c, e7), (stDir okk, e8)] ∧
    Cd (pc + Int64.ofNat (a1 + a2 + a3 + b1 + b2 + b3 + b4 + c1 + c2 + c3 + c4 + e1 + e2 + e3 + e4 + e5 + e6 +
      e7 + e8)) [(dS, g1), (dK, g2)] ∧
    Bl (pc + Int64.ofNat (a1 + a2 + a3 + b1 + b2 + b3 + b4 + c1 + c2 + c3 + c4 + e1 + e2 + e3 + e4 + e5 + e6 +
      e7 + e8 + g1 + g2)) zc Scc.Lower.Names.print kk ∧
    B = pblk pc (preD lO lB lL lM l8 olo os) [a1, a2, a3, b1, b2, b3, b4, c1, c2] c3
      (postD lN lC lN' lC' lS lK ocap okk) [c4, e1, e2, e3, e4, e5, e6, e7, e8, g1, g2] zc

/-- **`print`'s argument block and call as its chunks** (`PrintCodeC`):
from `InstsC2` of `printInsts n b (.reg o) m c` at `pc`, the block `B` laid
out from the chunks' sizes; the counter goes up by one (the call) and the
code ends after the `call`. -/
theorem print_codeC {kk kk' : Nat} {pc pc' : Int64} {n : Nat} {b : Scc.IR.Operand} {o : Scc.IR.Reg}
    {m c : Scc.IR.Operand} (h : InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m c) kk' pc') :
    ∃ B, PrintCodeC fr Cd Bl kk pc n b o m c B ∧ kk' = kk + 1 ∧ pc' = B.pc3 + Int64.ofNat B.zc := by
  simp only [printInsts] at h
  obtain ⟨l1, zs1, hE1, hz1, hc1, h⟩ := insts_cons_plain rfl h
  obtain ⟨l2, zs2, hE2, hz2, hc2, h⟩ := insts_cons_plain rfl h
  obtain ⟨l3, zs3, hE3, hz3, hc3, h⟩ := insts_cons_plain rfl h
  obtain ⟨l4, zs4, hE4, hz4, hc4, h⟩ := insts_cons_plain rfl h
  obtain ⟨lw, zs5, zc, hg, hz5, hc5, hbl, h⟩ := insts_print_call h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨lO, olo, hO, hlo, rfl⟩ := emits_ext32 hE1
  obtain ⟨lB, lL, os, hB, hL, hs, rfl⟩ := emits_addR hE2
  obtain ⟨lM, l8, ocap, hM, h8, hcap, rfl⟩ := emits_mul hE3
  obtain ⟨lN, lC, lN', lC', okk, hN, hC, hN', hC', hk, rfl⟩ := emits_selectU hE4
  obtain ⟨lS, lK, hS, hK, rfl⟩ := getOps_two hg
  obtain ⟨dO, eO⟩ := dirs_getOp hO
  obtain ⟨dB, eB⟩ := dirs_getOp hB
  obtain ⟨dL, eL⟩ := dirs_getOp hL
  obtain ⟨dM, eM⟩ := dirs_getOp hM
  obtain ⟨d8, e8⟩ := dirs_getOp h8
  obtain ⟨dN, eN⟩ := dirs_getOp hN
  obtain ⟨dC, eC⟩ := dirs_getOp hC
  obtain ⟨dN', eN'⟩ := dirs_getOp hN'
  obtain ⟨dC', eC'⟩ := dirs_getOp hC'
  obtain ⟨dS, eS⟩ := dirs_getOp hS
  obtain ⟨dK, eK⟩ := dirs_getOp hK
  simp only [dirs_append, dirs_cons_d, dirs_nil, eO, eB, eL, eM, e8, eN, eC, eN', eC', eS, eK, List.cons_append,
    List.nil_append] at hz1 hz2 hz3 hz4 hz5 hc1 hc2 hc3 hc4 hc5
  match zs1, zs2, zs3, zs4, zs5, hz1, hz2, hz3, hz4, hz5 with
  | [a1, a2, a3], [b1, b2, b3, b4], [c1, c2, c3, c4], [d1, d2, d3, d4, d5, d6, d7, d8'], [f1, f2],
      _, _, _, _, _ =>
    refine ⟨_, ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, dO, dB, dL, dM, d8, dN, dC, dN',
      dC', dS, dK, a1, a2, a3, b1, b2, b3, b4, c1, c2, c3, c4, d1, d2, d3, d4, d5, d6, d7, d8', f1, f2, zc, hlo, hs,
      hcap, hk, hO, hB, hL, hM, h8, hN, hC, hN', hC', hS, hK, eO, eB, eL, eM, e8, eN, eC, eN', eC', eS, eK, ?_, ?_,
      ?_, ?_, ?_, ?_, rfl⟩, rfl, ?_⟩
    all_goals simp only [List.zip_cons_cons, List.zip_nil_right, List.sum_cons, List.sum_nil, Nat.add_zero,
      Int64.ofNat_add, Int64.add_assoc, pblk] at hc1 hc2 hc3 hc4 hc5 hbl ⊢
    · exact hc1
    · exact hc2
    · exact hc3
    · exact hc4
    · exact hc5
    · exact hbl

/-- **The block's four pieces' code from its chunks** (`PrintCodeC`): before
the multiply, the multiply, after it, the `call`; the chunks' code from
`hCd`, the call's from `hBl`. -/
theorem PrintCodeC.cdOf {exe : _root_.Executable} {endPc : Int64}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → CdOf exe endPc pc [(i64 (.call (Scc.Emit.X64.rel g)), z)])
    {kk : Nat} {pc : Int64} {n : Nat} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m c : Scc.IR.Operand} {B : PBlk}
    (h : PrintCodeC fr Cd Bl kk pc n b o m c B) :
    CdOf exe endPc B.pc B.pre ∧ CdOf exe endPc B.pc1 [(mulFI.toDir, B.zM)] ∧ CdOf exe endPc B.pc2 B.post ∧
      CdOf exe endPc B.pc3 [(callD, B.zc)] := by
  obtain ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, dO, dB, dL, dM, d8, dN, dC, dN', dC',
    dS, dK, a1, a2, a3, b1, b2, b3, b4, c1, c2, c3, c4, d1, d2, d3, d4, d5, d6, d7, d8', e1, e2, zc,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, eO, eB, eL, eM, e8, eN, eC, eN', eC', eS, eK,
    hc1, hc2, hc3, hc4, hc5, hbl, rfl⟩ := h
  have C1 := hCd _ _ hc1
  have C2 := hCd _ _ hc2
  have C3 := hCd _ _ hc3
  have C4 := hCd _ _ hc4
  have C5 := hCd _ _ hc5
  have CB := hBl _ _ _ _ hbl
  simp only [Int64.ofNat_add, Int64.add_assoc] at C1 C2 C3 C4 C5 CB
  have big := cdOf_append (cdOf_append (cdOf_append (cdOf_append C1 (B := [_, _, _, _]) (by
      simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
        Int64.add_assoc] using C2)) (B := [_, _, _, _]) (by
      simpa only [List.map_cons, List.map_nil, List.map_append, List.cons_append, List.nil_append,
        List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using C3))
      (B := [_, _, _, _, _, _, _, _]) (by
      simpa only [List.map_cons, List.map_nil, List.map_append, List.cons_append, List.nil_append,
        List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using C4))
      (B := [_, _]) (by
      simpa only [List.map_cons, List.map_nil, List.map_append, List.cons_append, List.nil_append,
        List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using C5)
  simp only [List.cons_append, List.nil_append] at big
  have hpre : (preD lO lB lL lM l8 olo os).zip [a1, a2, a3, b1, b2, b3, b4, c1, c2] =
      [(dO, a1), (ext32D, a2), (stDir olo, a3), (dB, b1), (dL, b2), (addD, b3), (stDir os, b4), (dM, c1),
        (d8, c2)] := by
    simp only [preD, dirs_append, eO, eB, eL, eM, e8, List.cons_append, List.nil_append, List.append_assoc,
      List.zip_cons_cons, List.zip_nil_right]
  have hpost : (postD lN lC lN' lC' lS lK ocap okk).zip [c4, d1, d2, d3, d4, d5, d6, d7, d8', e1, e2] =
      [(stDir ocap, c4), (dN, d1), (dC, d2), (dN', d3), (dC', d4), (cmpD, d5), (movRsiD, d6), (cmovD .c, d7),
        (stDir okk, d8'), (dS, e1), (dK, e2)] := by
    simp only [postD, dirs_append, eN, eC, eN', eC', eS, eK, List.cons_append, List.nil_append,
      List.append_assoc, List.zip_cons_cons, List.zip_nil_right]
  simp only [pblk, hpre, hpost]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := cdOf_sub (pre := []) (blk := [(dO, a1), (ext32D, a2), (stDir olo, a3), (dB, b1), (dL, b2),
      (addD, b3), (stDir os, b4), (dM, c1), (d8, c2)]) (post := [_, _, _, _, _, _, _, _, _, _, _, _])
      (by simpa only [List.cons_append, List.nil_append] using big)
    simpa only [List.map_nil, List.sum_nil, Scc.Cert.Rt.X64.Print.off0] using e
  · have e := cdOf_sub (pre := [(dO, a1), (ext32D, a2), (stDir olo, a3), (dB, b1), (dL, b2),
      (addD, b3), (stDir os, b4), (dM, c1), (d8, c2)]) (blk := [_]) (post := [_, _, _, _, _, _, _, _, _, _, _])
      (by simpa only [List.cons_append, List.nil_append] using big)
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
      Int64.add_assoc] using e
  · have e := cdOf_sub (pre := [(dO, a1), (ext32D, a2), (stDir olo, a3), (dB, b1), (dL, b2),
      (addD, b3), (stDir os, b4), (dM, c1), (d8, c2), (_, c3)]) (blk := [_, _, _, _, _, _, _, _, _, _, _])
      (post := []) (by simpa only [List.cons_append, List.nil_append, List.append_nil] using big)
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
      Int64.add_assoc] using e
  · simpa only [callD, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] using CB

end Code

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.print_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.print_code
