/-
**An `Accepted2` block's code after its label gives `CodeC2`** (x86-64):
the `Accepted2` twin of `Spike/Lib/LowerX64/BlocksC1Code.lean`'s
`codeC_of_seg`, over `lowerC2`'s block shape (`InstC2`, `TermC2`,
`Spike/Lib/LowerShapeC2Shape.lean`), and of
`Spike/Lib/LowerA64/BlocksC2Seg.lean`.

- `emitInst2_allIns`, `emitTerm2_allIns`: the code of every non-call
  `InstC2` instruction and of every `TermC2` terminator is the same
  label-free items from every state (`Emits`), a terminator's not empty.
- `emitInst_callN1_inv`, `emitInst_callN0_inv`: a call of up to six words
  with one result (the allocator's) or none (the output call's): the
  arguments' loads (`getOps`), `callq`, the return label `.L<fn>.x<k>` at the
  label counter `k`, the result's store; the counter `k + 1` after it.
- `CodeC2.mono`: `CodeC2` is monotone in its call predicate (`BlC2.toBlC`).
- `HeadIns`, `code2_head`: the code of an `Accepted2` block's instructions
  and terminator begins with a non-label.
- `callSegX`: a call's code `lw`, `callq g`, the return label `.L<fn>.x<k>`,
  `R` in a segment gives `lw`'s piece at `CdCQ Q` (`l` of `Q`), the `callq` at `BlC2` (`R`
  beginning with a non-label), and the segment and run facts after the
  return label (`codeC_of_seg`'s call arm).
- `codeC2_of_seg`, `codeC2_block`: at `BlC2` (`Spike/Lib/LowerX64/AllocRa.lean`);
  `CdCQ`, `cdCQ_at`, `codeC2_of_segQ`, `codeC2_blockQ`: each piece after a
  label of a predicate `Q` (the block's and the return labels), at `CdCQ Q`;
  `CodeC2.monoCd`: monotone in the code predicate.

Where x86-64 differs from AArch64: as in `BlocksC1Code.lean`, the emitter
is a state monad (`Emits`), blocks are sized, the return label is the label
counter's `.L<fn>.x<k>`, and a run's position is a byte offset (`InRunB`).
-/
import Spike.Lib.LowerX64.PrintCallC2Code
import Spike.Lib.LowerX64.Body2SegX
import Spike.Lib.LowerX64.AllocRa
import Spike.Lib.LowerX64.EmitOut
import Spike.Lib.LowerShapeC2Shape

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Emit.X64 (S E Item emitInst emitTerm ld st ins labelOf cmpAB directives i64 rel argRegs retRegs
  callArgs safepoint)
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (blockAt labelGap after after_eq InRunB inRunB_of_blockAt)
open Scc.Cert.Code1X64 (segIn segIn_iff segIn_label blockAt_of_segIn labelGap_of_segIn blockItems blocksOk
  blocksOk_block)
open Scc.Cert.Ph1X64 (runsAux runPhB blkPh_of_runPhB runs runPh blocksPh blocksPh_blockPh segCells)
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.X64 (cellOff)
open Spike.Lib.LowerShape (isCall InstC2 TermC2 newBufCall xchgLoad xchgStore)

set_option linter.unusedSimpArgs false

/-! ## Instructions only -/

section Emit

variable {fr : Scc.Emit.X64.Frame}

/-- **The code of every non-call `InstC2` instruction** is the same items
from every state, label-free: a checked `+`, a saturating `-`, a lane's
load and store, the output block's `ext32`, `+`, `· 8` and unsigned
`min`. -/
theorem emitInst2_allIns {sm : Option Scc.IR.StackMap.Entry} {i : Scc.IR.Inst} (hi : InstC2 i)
    (hc : isCall i = false) {s s' : S} (h : emitInst fr sm i s = .ok ((), s')) :
    ∃ c, Emits (emitInst fr sm i) c ∧ AllIns c := by
  cases hi with
  | addChk d p q =>
    obtain ⟨la, lb, off, ha, hb, hd, -⟩ := emitInst_add_cases fr sm d p q s h
    rw [Scc.Lower.InvX64.emitInst_addChk]
    exact ⟨_, (emits_ld ha).seq ((emits_ld hb).seq ((emits_ins _).seq ((emits_ins _).seq (emits_st hd)))),
      by allIns_tac⟩
  | subSat d p q =>
    obtain ⟨la, lb, off, ha, hb, hd, -⟩ := emitInst_sub_cases fr sm d p q s h
    simp only [emitInst]
    exact ⟨_, (emits_ld ha).seq ((emits_ld hb).seq ((emits_ins _).seq ((emits_ins _).seq
      ((emits_ins _).seq (emits_st hd))))), by allIns_tac⟩
  | load d a =>
    rw [emitInst_xchgLoad] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨lb, hb⟩ := ld_ok h1
    obtain ⟨u2, s2, h2, h⟩ := bind_inv h
    obtain ⟨off, hd⟩ := st_ok h
    exact ⟨_, (emits_ld hb).seq ((emits_ins _).seq (emits_st hd)), by allIns_tac⟩
  | store a w =>
    rw [emitInst_xchgStore] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨lb, hb⟩ := ld_ok h1
    obtain ⟨u2, s2, h2, h⟩ := bind_inv h
    obtain ⟨lv, hv⟩ := ld_ok h2
    exact ⟨_, (emits_ld hb).seq ((emits_ld hv).seq (emits_ins _)), by allIns_tac⟩
  | ext d o =>
    rw [emitInst_ext32_def] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨la, ha⟩ := ld_ok h1
    obtain ⟨u2, s2, h2, h⟩ := bind_inv h
    obtain ⟨off, hd⟩ := st_ok h
    exact ⟨_, (emits_ld ha).seq ((emits_ins _).seq (emits_st hd)), by allIns_tac⟩
  | add d b r =>
    rw [emitInst_addR_def] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨la, ha⟩ := ld_ok h1
    obtain ⟨u2, s2, h2, h⟩ := bind_inv h
    obtain ⟨lb, hb⟩ := ld_ok h2
    obtain ⟨u3, s3, h3, h⟩ := bind_inv h
    obtain ⟨off, hd⟩ := st_ok h
    exact ⟨_, (emits_ld ha).seq ((emits_ld hb).seq ((emits_ins _).seq (emits_st hd))), by allIns_tac⟩
  | mul8 d m =>
    rw [emitInst_mul_def] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨la, ha⟩ := ld_ok h1
    obtain ⟨u2, s2, h2, h⟩ := bind_inv h
    obtain ⟨lb, hb⟩ := ld_ok h2
    obtain ⟨u3, s3, h3, h⟩ := bind_inv h
    obtain ⟨off, hd⟩ := st_ok h
    exact ⟨_, (emits_ld ha).seq ((emits_ld hb).seq ((emits_ins _).seq (emits_st hd))), by allIns_tac⟩
  | minU d c r =>
    rw [emitInst_selectU_def] at h ⊢
    simp only [cmpAB] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨lt, hlt⟩ := ld_ok h1
    obtain ⟨u2, s2, h2, h⟩ := bind_inv h
    obtain ⟨lf, hlf⟩ := ld_ok h2
    obtain ⟨u3, s3, h3, h⟩ := bind_inv h
    obtain ⟨u4, s4, h4, h3⟩ := bind_inv h3
    obtain ⟨la, hla⟩ := ld_ok h4
    obtain ⟨u5, s5, h5, h3⟩ := bind_inv h3
    obtain ⟨lb, hlb⟩ := ld_ok h5
    obtain ⟨u6, s6, h6, h⟩ := bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := bind_inv h
    obtain ⟨off, hd⟩ := st_ok h
    exact ⟨_, (emits_ld hlt).seq ((emits_ld hlf).seq (((emits_ld hla).seq ((emits_ld hlb).seq (emits_ins _))).seq
      ((emits_ins _).seq ((emits_ins _).seq (emits_st hd))))), by allIns_tac⟩
  | call d g w => simp [isCall] at hc
  | newBuf p h' kv u => simp [isCall, newBufCall] at hc
  | print a0 a1 => simp [isCall] at hc

/-- **The code of every `TermC2` terminator** is the same items from every
state, label-free and not empty: a `ret` of up to six words (their loads
into the result registers, the epilogue, `ret`) and an `if`'s `br`. -/
theorem emitTerm2_allIns {t : Scc.IR.Term} (ht : TermC2 t) {s s' : S} (h : emitTerm fr t s = .ok ((), s')) :
    ∃ c, Emits (emitTerm fr t) c ∧ AllIns c ∧ directives c ≠ [] := by
  cases ht with
  | ret ws =>
    by_cases hgt : ws.length > Scc.Emit.X64.retRegs.length
    · simp only [emitTerm, Scc.Emit.X64.loadArgs, hgt, ite_true] at h
      cases h
    have hl : Scc.Emit.X64.loadArgs fr Scc.Emit.X64.retRegs ws "ret" =
        (ldsLoop fr (ws.zip Scc.Emit.X64.retRegs) >>= fun _ => pure ()) := by
      simp only [Scc.Emit.X64.loadArgs, hgt, ite_false]
    have he : emitTerm fr (.ret ws) =
        ((ldsLoop fr (ws.zip Scc.Emit.X64.retRegs) >>= fun _ => pure ()) >>= fun _ =>
          (do Scc.Emit.X64.epilogue; Scc.Emit.X64.ins (Scc.Emit.X64.i64 .ret))) := by
      simp only [emitTerm, hl]
    rw [he] at h ⊢
    obtain ⟨u, s1, h1, -⟩ := bind_inv h
    obtain ⟨lw, hlw⟩ := ldsLoop_ok h1
    refine ⟨_, (ldsLoop_emits hlw).seq emits_retTail, allIns_append (allIns_getOps hlw) (by rfl), ?_⟩
    simp [directives_eq_dirs, dirs_append, epiItems, dirs]
  | br p q l l' =>
    simp only [emitTerm, cmpAB] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨u0, s0, h0, h1⟩ := bind_inv h1
    obtain ⟨la, ha⟩ := ld_ok h0
    obtain ⟨u2, s2, h2, h1⟩ := bind_inv h1
    obtain ⟨lb, hb⟩ := ld_ok h2
    refine ⟨_, ((emits_ld ha).seq ((emits_ld hb).seq (emits_ins _))).seq ((emits_ins _).seq (emits_ins _)),
      by allIns_tac, ?_⟩
    simp [directives_eq_dirs, dirs_append, dirs]

end Emit

/-! ## Calls of several words -/

section Calls

variable {fr : Scc.Emit.X64.Frame}

/-- **The code of a call of up to six words with one result** `call [d] f
args` (stack maps on) from a state `s`: the arguments' loads `lw` (`getOps`
into `%rdi`, `%rsi`, …), `callq f`, the return label `.L<fn>.x<k>` at the
label counter `k` of `s`, then `%rax`'s store into `d`'s slot `off`; the
counter is `k + 1` after it (`emitInst_call1_inv` of several words). -/
theorem emitInst_callN1_inv (hm : fr.maps = true) {sm : Option Scc.IR.StackMap.Entry}
    {d : Scc.IR.Reg} {f : Scc.IR.Sym} {args : List Scc.IR.Operand} (ha : args.length ≤ 6) {s s' : S}
    (h : emitInst fr sm (.call [d] f args) s = .ok ((), s')) :
    ∃ lw off mp, getOps fr (args.zip argRegs) = .ok lw ∧ rsOf fr d = some off ∧
      s' = { out := (lw ++ [Item.d (i64 (.call (rel f))), Item.d (.label s!".L{fr.fn}.x{s.next}")] ++
        [Item.d (stDir off)]).reverse ++ s.out, next := s.next + 1, maps := mp } := by
  have h0 : ¬ [d].length > retRegs.length := by simp [retRegs]
  simp only [emitInst, h0, ite_false] at h
  obtain ⟨u1, s1, h1, h⟩ := bind_inv h
  rw [callArgs_eq fr ha] at h1
  obtain ⟨lw, hw⟩ := ldsLoop_ok h1
  rw [ldsLoop_emits hw s] at h1
  cases h1
  obtain ⟨u2, s2, h2, h⟩ := bind_inv h
  cases h2
  obtain ⟨u3, s3, h3, h⟩ := bind_inv h
  have hs3 : ∃ mp, s3 = { out := Item.d (.label s!".L{fr.fn}.x{s.next}") :: Item.d (i64 (.call (rel f))) ::
      (lw.reverse ++ s.out), next := s.next + 1, maps := mp } := by
    unfold safepoint at h3
    simp only [hm, ite_true] at h3
    obtain ⟨l, t1, e1, h3⟩ := bind_inv h3
    cases e1
    obtain ⟨u, t2, e2, h3⟩ := bind_inv h3
    cases e2
    obtain ⟨st1, t3, e3, h3⟩ := bind_inv h3
    have := mapM_slotOff_state fr _ e3
    subst this
    obtain ⟨hp1, t4, e4, h3⟩ := bind_inv h3
    have := mapM_slotOff_state fr _ e4
    subst this
    cases h3
    exact ⟨_, rfl⟩
  obtain ⟨mp, rfl⟩ := hs3
  rw [stores_one_eq] at h
  obtain ⟨u4, s4, h4, h⟩ := bind_inv h
  obtain ⟨u5, s5, h5, h4⟩ := bind_inv h4
  obtain ⟨off, hd⟩ := st_ok h5
  rw [emits_st hd] at h5
  cases h5
  cases h4
  cases h
  refine ⟨lw, off, mp, hw, hd, ?_⟩
  simp [List.reverse_append, List.append_assoc]

/-- **The code of a call of up to six words with no result** `call [] f
args` (stack maps on) from a state `s`: the arguments' loads `lw`, `callq
f`, the return label `.L<fn>.x<k>` at the label counter `k` of `s`; the
counter is `k + 1` after it. -/
theorem emitInst_callN0_inv (hm : fr.maps = true) {sm : Option Scc.IR.StackMap.Entry}
    {f : Scc.IR.Sym} {args : List Scc.IR.Operand} (ha : args.length ≤ 6) {s s' : S}
    (h : emitInst fr sm (.call [] f args) s = .ok ((), s')) :
    ∃ lw mp, getOps fr (args.zip argRegs) = .ok lw ∧
      s' = { out := (lw ++ [Item.d (i64 (.call (rel f))), Item.d (.label s!".L{fr.fn}.x{s.next}")]).reverse ++
        s.out, next := s.next + 1, maps := mp } := by
  have h0 : ¬ ([] : List Scc.IR.Reg).length > retRegs.length := by simp
  simp only [emitInst, h0, ite_false] at h
  obtain ⟨u1, s1, h1, h⟩ := bind_inv h
  rw [callArgs_eq fr ha] at h1
  obtain ⟨lw, hw⟩ := ldsLoop_ok h1
  rw [ldsLoop_emits hw s] at h1
  cases h1
  obtain ⟨u2, s2, h2, h⟩ := bind_inv h
  cases h2
  obtain ⟨u3, s3, h3, h⟩ := bind_inv h
  have hs3 : ∃ mp, s3 = { out := Item.d (.label s!".L{fr.fn}.x{s.next}") :: Item.d (i64 (.call (rel f))) ::
      (lw.reverse ++ s.out), next := s.next + 1, maps := mp } := by
    unfold safepoint at h3
    simp only [hm, ite_true] at h3
    obtain ⟨l, t1, e1, h3⟩ := bind_inv h3
    cases e1
    obtain ⟨u, t2, e2, h3⟩ := bind_inv h3
    cases e2
    obtain ⟨st1, t3, e3, h3⟩ := bind_inv h3
    have := mapM_slotOff_state fr _ e3
    subst this
    obtain ⟨hp1, t4, e4, h3⟩ := bind_inv h3
    have := mapM_slotOff_state fr _ e4
    subst this
    cases h3
    exact ⟨_, rfl⟩
  obtain ⟨mp, rfl⟩ := hs3
  simp only [List.zip_nil_left, List.forIn_nil] at h
  cases h
  refine ⟨lw, mp, hw, ?_⟩
  simp [List.reverse_append, List.append_assoc]

/-- **The allocator's three arguments** `h`, `k`, `u` and the output call's
two are at most six. -/
theorem newBuf_args_le (h : Nat) (kv : UInt64) (u : Scc.IR.Operand) :
    [Scc.Lower.imm h, Scc.IR.Operand.imm kv, u].length ≤ 6 := by simp

end Calls

/-! ## The call predicate -/

/-- **`CodeC2` is monotone in its call predicate.** -/
theorem CodeC2.mono {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl Bl' : Int64 → Nat → Label → Nat → Prop} (hB : ∀ pc zc g k, Bl pc zc g k → Bl' pc zc g k) :
    ∀ {k : Nat} {pc : Int64} {is : List Scc.IR.Inst} {tm : Scc.IR.Term},
      CodeC2 fr Cd Bl k pc is tm → CodeC2 fr Cd Bl' k pc is tm
  | _, _, [], _, h => h
  | _, _, _ :: _, _, .inl ⟨hc, l, zs, hE, hz, hcd, h⟩ => .inl ⟨hc, l, zs, hE, hz, hcd, CodeC2.mono hB h⟩
  | _, _, _ :: _, _, .inr (.inl ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hcd, hb, hs, h⟩) =>
    .inr (.inl ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hcd, hB _ _ _ _ hb, hs, CodeC2.mono hB h⟩)
  | _, _, _ :: _, _, .inr (.inr (.inl ⟨d, ws, lw, off, zs, zc, z, hi, hn, hl, ho, hz, hcd, hb, hs, h⟩)) =>
    .inr (.inr (.inl ⟨d, ws, lw, off, zs, zc, z, hi, hn, hl, ho, hz, hcd, hB _ _ _ _ hb, hs, CodeC2.mono hB h⟩))
  | _, _, _ :: _, _, .inr (.inr (.inr ⟨ws, lw, zs, zc, hi, hn, hl, hz, hcd, hb, h⟩)) =>
    .inr (.inr (.inr ⟨ws, lw, zs, zc, hi, hn, hl, hz, hcd, hB _ _ _ _ hb, CodeC2.mono hB h⟩))

/-- **`CodeC2` is monotone in its code predicate.** -/
theorem CodeC2.monoCd {fr : Scc.Emit.X64.Frame} {Cd Cd' : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} (hC : ∀ pc blk, Cd pc blk → Cd' pc blk) :
    ∀ {k : Nat} {pc : Int64} {is : List Scc.IR.Inst} {tm : Scc.IR.Term},
      CodeC2 fr Cd Bl k pc is tm → CodeC2 fr Cd' Bl k pc is tm
  | _, _, [], _, .inl h => .inl h
  | _, _, [], _, .inr ⟨c, zs, hE, hz, hcd⟩ => .inr ⟨c, zs, hE, hz, hC _ _ hcd⟩
  | _, _, _ :: _, _, .inl ⟨hc, l, zs, hE, hz, hcd, h⟩ => .inl ⟨hc, l, zs, hE, hz, hC _ _ hcd, CodeC2.monoCd hC h⟩
  | _, _, _ :: _, _, .inr (.inl ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hcd, hb, hs, h⟩) =>
    .inr (.inl ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hC _ _ hcd, hb, hC _ _ hs, CodeC2.monoCd hC h⟩)
  | _, _, _ :: _, _, .inr (.inr (.inl ⟨d, ws, lw, off, zs, zc, z, hi, hn, hl, ho, hz, hcd, hb, hs, h⟩)) =>
    .inr (.inr (.inl ⟨d, ws, lw, off, zs, zc, z, hi, hn, hl, ho, hz, hC _ _ hcd, hb, hC _ _ hs,
      CodeC2.monoCd hC h⟩))
  | _, _, _ :: _, _, .inr (.inr (.inr ⟨ws, lw, zs, zc, hi, hn, hl, hz, hcd, hb, h⟩)) =>
    .inr (.inr (.inr ⟨ws, lw, zs, zc, hi, hn, hl, hz, hC _ _ hcd, hb, CodeC2.monoCd hC h⟩))

/-! ## The code's first directive -/

/-- A directive list beginning with a non-label. -/
def HeadIns (D : List Directive) : Prop := ∃ x r, D = x :: r ∧ x.isLabel = false

theorem headIns_of_all {D : List Directive} (h : D.all (fun d => !d.isLabel) = true) (hne : D ≠ []) :
    HeadIns D := by
  cases D with
  | nil => exact absurd rfl hne
  | cons d r =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact ⟨d, r, rfl, by simpa using h.1⟩

theorem headIns_append {A P : List Directive} (h : HeadIns A) : HeadIns (A ++ P) := by
  obtain ⟨x, r, rfl, hx⟩ := h
  exact ⟨x, r ++ P, rfl, hx⟩

theorem headIns_append_all {A P : List Directive} (hA : A.all (fun d => !d.isLabel) = true) (hP : HeadIns P) :
    HeadIns (A ++ P) := by
  cases A with
  | nil => simpa using hP
  | cons a A => exact headIns_append (P := P) (headIns_of_all hA (List.cons_ne_nil _ _))

/-- **An `Accepted2` block's code from an instruction on begins with a
non-label**: the code `c` its instructions `is` (`InstC2`, a stack map
each) and terminator (`TermC2`) emit from a state `s`. A non-call's code is
label-free, a call's begins with its label-free loads then `callq`, and a
terminator's is label-free and not empty. -/
theorem code2_head {fr : Scc.Emit.X64.Frame} (hm : fr.maps = true) {tm : Scc.IR.Term} (htm : TermC2 tm) :
    ∀ (is : List Scc.IR.Inst) (ms : List (Option Scc.IR.StackMap.Entry)) (s s' : S) (c : List Item),
      (∀ i ∈ is, InstC2 i) → is.length ≤ ms.length →
      (do instsCode fr is ms; emitTerm fr tm) s = .ok ((), s') → s'.out = c.reverse ++ s.out →
      HeadIns (directives c)
  | [], ms, s, s', c, _, _, h, hD => by
    obtain ⟨u, s1, hI, hT⟩ := bind_inv h
    rw [instsCode_nil] at hI
    cases hI
    obtain ⟨ct, et, act, hne⟩ := emitTerm2_allIns htm hT
    rw [et] at hT
    cases hT
    have hc : c = ct := by
      have h2 := List.append_cancel_right hD.symm
      rw [← List.reverse_reverse c, h2, List.reverse_reverse]
    subst hc
    exact headIns_of_all act hne
  | i :: is, ms, s, s', c, hs, hms, h, hD => by
    obtain ⟨m, ms, rfl⟩ : ∃ m ms', ms = m :: ms' := by
      cases ms with
      | nil => simp at hms
      | cons m ms' => exact ⟨m, ms', rfl⟩
    have hs' := List.forall_mem_cons.mp hs
    have hms' : is.length ≤ ms.length := by simp at hms; omega
    obtain ⟨u, s1, hI, hT⟩ := bind_inv h
    rw [instsCode_cons] at hI
    obtain ⟨u2, s2, hE, hI⟩ := bind_inv hI
    have hrest : (do instsCode fr is ms; emitTerm fr tm) s2 = .ok ((), s') := by
      rw [bind_ok hI]; exact hT
    obtain ⟨c', hc'⟩ := (Pre.bind' (instsCode_pre fr is ms) fun _ => emitTerm_pre fr tm).out _ _ _ hrest
    have hD' : s'.out = c'.reverse.reverse ++ s2.out := by rw [List.reverse_reverse]; exact hc'
    have ih := code2_head hm htm is ms s2 s' c'.reverse hs'.2 hms' hrest hD'
    -- the code `c` is the instruction's items `ci`, then `c'.reverse`
    have hsplit : ∀ ci : List Item, s2.out = ci.reverse ++ s.out → c = ci ++ c'.reverse := by
      intro ci hci
      have h1 : c.reverse ++ s.out = (c' ++ ci.reverse) ++ s.out := by rw [← hD, hc', hci, List.append_assoc]
      have h2 := List.append_cancel_right h1
      rw [← List.reverse_reverse c, h2]; simp
    -- a call's items: its loads, `callq`, then the rest
    have hcall : ∀ (lw r : List Item) (g : Label), AllIns lw →
        s2.out = (lw ++ Item.d (i64 (.call (rel g))) :: r).reverse ++ s.out → HeadIns (directives c) := by
      intro lw r g aw hci
      rw [hsplit _ hci, directives_eq_dirs, dirs_append, dirs_append]
      rw [List.append_assoc]
      refine headIns_append_all aw ⟨_, _, rfl, isLabel_callq g⟩
    by_cases hc : isCall i = false
    · obtain ⟨ci, ei, ai⟩ := emitInst2_allIns hs'.1 hc hE
      rw [ei] at hE
      cases hE
      rw [hsplit ci rfl, directives_eq_dirs, dirs_append]
      exact headIns_append_all ai ih
    · cases hs'.1 with
      | call d g w =>
        obtain ⟨lw, off, mp, hw, hd, aw, rfl⟩ := emitInst_call1_inv hm hE
        exact hcall lw [Item.d (.label s!".L{fr.fn}.x{s.next}"), Item.d (stDir off)] (Scc.Lower.Names.user g) aw
          (by simp)
      | newBuf p h' kv u =>
        obtain ⟨lw, off, mp, hw, hd, rfl⟩ := emitInst_callN1_inv hm (newBuf_args_le h' kv u) hE
        exact hcall lw [Item.d (.label s!".L{fr.fn}.x{s.next}"), Item.d (stDir off)] Scc.Lower.Names.alloc
          (allIns_getOps hw) (by simp [newBufCall])
      | print a0 a1 =>
        obtain ⟨lw, mp, hw, rfl⟩ := emitInst_callN0_inv hm (by simp) hE
        exact hcall lw [Item.d (.label s!".L{fr.fn}.x{s.next}")] Scc.Lower.Names.print (allIns_getOps hw)
          (by simp)
      | _ => exact absurd rfl hc

/-! ## A call in a segment -/

section Code

variable {fr : Scc.Emit.X64.Frame} {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
  {lab : Label → Int64} {ra : Int64}

/-- **A segment's label beginning with a non-label has a cell at offset
0** (`InRunB`). -/
theorem inRunB0_of_segIn {l : Label} {R zs : List Directive} (h : segIn cells l (R ++ zs) = true)
    (hR : HeadIns R) : InRunB cells l 0 := by
  obtain ⟨x, r, rfl, hx⟩ := hR
  obtain ⟨t', -, hY, hb⟩ := blockAt_of_segIn (xs := []) (ys := [x]) (zs := r ++ zs)
    (by simpa using h) rfl (by simp [hx])
  have hlen : 0 < ((t'.drop ([] : List Directive).length).take [x].length).length := by
    have := congrArg List.length hY
    rw [List.length_map] at this
    rw [this]; simp
  simpa using inRunB_of_blockAt hb hlen

/-- **A piece of a block's code at `pc` after a label of `Q`**: `CdC` with
its label `L` satisfying `Q` (`UserAbC`'s `CdCL` at `Q := (· ∉ abLabs)`). -/
def CdCQ (Q : Label → Prop) (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat)
    (lab : Label → Int64) (ra : Int64) (pc : Int64) (blk : List (Directive × Nat)) : Prop :=
  blk.all (fun c => !c.1.isLabel) = true ∧ ∃ L j off, Q L ∧ lab L + Int64.ofNat off = pc ∧
    blockAt cells L j off blk = true ∧ runPhB okPc ph lab pc ra blk = true

theorem CdCQ.toCdC {Q : Label → Prop} {pc : Int64} {blk : List (Directive × Nat)}
    (h : CdCQ Q cells okPc ph lab ra pc blk) : CdC cells okPc ph lab ra pc blk :=
  let ⟨hi, L, j, off, _, he, hb, hr⟩ := h
  ⟨hi, L, j, off, he, hb, hr⟩

/-- **`cdC_at` after a label of `Q`**: the piece is at `CdCQ Q` (its label
is the segment's, `l`). -/
theorem cdCQ_at {Q : Label → Prop} {l : Label} (hQ : Q l) {t : List (Directive × Nat)}
    (ht : after l cells = some t) {xs c zs : List Directive}
    (hseg : segIn cells l (xs ++ c ++ zs) = true) (hx : xs.all (fun d => !d.isLabel) = true)
    (hc : c.all (fun d => !d.isLabel) = true)
    (hph : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (c ++ zs).length),
      runPhB okPc ph lab (lab r.1) ra r.2 = true) :
    ∃ zc, zc.length = c.length ∧
      CdCQ Q cells okPc ph lab ra (lab l + Int64.ofNat (cellOff t xs.length)) (c.zip zc) ∧
      lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zc.sum =
        lab l + Int64.ofNat (cellOff t (xs ++ c).length) := by
  have hY := seg_slice ht hseg
  have hYe := zip_fst_snd ((t.drop xs.length).take c.length)
  rw [hY] at hYe
  have hlenT : (xs ++ c ++ zs).length ≤ t.length := by
    have := congrArg List.length (seg_take ht hseg)
    simp only [List.length_map, List.length_take] at this
    omega
  have hS := slice_noLabel hY hc
  refine ⟨((t.drop xs.length).take c.length).map (·.2), by simp; simp at hlenT; omega, ?_, ?_⟩
  · rw [hYe]
    refine ⟨List.all_eq_true.mpr fun d hd => by simp [hS d hd], l, xs.length, cellOff t xs.length, hQ, rfl, ?_,
      ?_⟩
    · obtain ⟨t', ht', -, hb⟩ := blockAt_of_segIn hseg hx hc
      rw [ht] at ht'
      cases ht'
      exact hb
    · rw [List.length_append, List.take_add, runsAux_shift _ _ _ _ hS] at hph
      obtain ⟨P, hP⟩ := runsAux_run0 l (((t.drop xs.length).take c.length).reverse ++ (t.take xs.length).reverse)
        (((t.drop xs.length).drop c.length).take zs.length)
      have hr := hph _ hP
      simp only [List.reverse_append, List.reverse_reverse] at hr
      have := runPhB_sub (xs := t.take xs.length) (ys := (t.drop xs.length).take c.length) (zs := P)
        (by simpa only [List.append_assoc] using hr)
      have e : cellOff (t.take xs.length ++ (t.drop xs.length).take c.length ++ P) (t.take xs.length).length =
          cellOff t xs.length := by
        unfold cellOff
        rw [List.append_assoc, List.take_left' rfl]
      rwa [e] at this
  · rw [List.length_append, pc_step]

/-- **A call in a segment** (`codeC_of_seg`'s call arm): the code `lw`,
`callq g`, the return label `.L<fn>.x<k>`, then `R` (beginning with a
non-label, `hR`) after the label-free `xs` in the segment after `l` (the
cells `t`), every run from there passing `runPhB` (`hph`) and in the phase
of `ra` (`hrl`): `lw`'s piece at `CdCQ Q` (`l` of `Q`, `hQ`) at some cell sizes `zl`, the `callq`
of `zc` bytes after it at `BlC2`, the return label's address, its cells,
and the segment and run facts after it for `R`. -/
theorem callSegX (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    {Q : Label → Prop} {l : Label} (hQ : Q l) {t : List (Directive × Nat)} (ht : after l cells = some t)
    {xs zs R : List Directive}
    {lw : List Item} {g : Label} {k : Nat}
    (hseg : segIn cells l (xs ++ directives lw ++
      (i64 (.call (rel g)) :: .label s!".L{fr.fn}.x{k}" :: R ++ zs)) = true)
    (hx : xs.all (fun d => !d.isLabel) = true) (aw : AllIns lw) (hR : HeadIns R)
    (hph : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take
      (directives lw ++ (i64 (.call (rel g)) :: .label s!".L{fr.fn}.x{k}" :: R ++ zs)).length),
      runPhB okPc ph lab (lab r.1) ra r.2 = true)
    (hrl : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take
      (directives lw ++ (i64 (.call (rel g)) :: .label s!".L{fr.fn}.x{k}" :: R ++ zs)).length),
      ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    ∃ zl zc, zl.length = (directives lw).length ∧
      CdCQ Q cells okPc ph lab ra (lab l + Int64.ofNat (cellOff t xs.length)) ((directives lw).zip zl) ∧
      BlC2 cells okPc ph lab fr ra (lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zl.sum) zc g k ∧
      lab s!".L{fr.fn}.x{k}" = lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zl.sum + Int64.ofNat zc ∧
      after s!".L{fr.fn}.x{k}" cells = some (t.drop ((xs ++ directives lw).length + 1 + 1)) ∧
      segIn cells s!".L{fr.fn}.x{k}" (R ++ zs) = true ∧
      (∀ r ∈ runsAux s!".L{fr.fn}.x{k}" [] ((t.drop ((xs ++ directives lw).length + 1 + 1)).take (R ++ zs).length),
        runPhB okPc ph lab (lab r.1) ra r.2 = true) ∧
      (∀ r ∈ runsAux s!".L{fr.fn}.x{k}" [] ((t.drop ((xs ++ directives lw).length + 1 + 1)).take (R ++ zs).length),
        ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) := by
  -- the first run is after `l`, in the phase of `ra`
  have hl : ph (lab l).toBitVec.toNat = ph ra.toBitVec.toNat := by
    obtain ⟨y, hy⟩ := runsAux_head l _ _
    exact hrl _ hy
  have aw' : (directives lw).all (fun d => !d.isLabel) = true := aw
  generalize hK : s!".L{fr.fn}.x{k}" = spK at hseg hph hrl ⊢
  generalize hC : i64 (.call (rel g)) = C at hseg hph hrl
  have hCl : C.isLabel = false := by rw [← hC]; exact isLabel_callq _
  -- the arguments' loads
  have hsegA : segIn cells l (xs ++ directives lw ++ (C :: .label spK :: R ++ zs)) = true := hseg
  have hphA := hph
  have hrlA := hrl
  obtain ⟨zl, hzl, hcdl, hpcl⟩ := cdCQ_at hQ ht (c := directives lw)
    (by simpa only [List.append_assoc] using hsegA) hx aw'
    (by simpa only [List.append_assoc] using hphA)
  have hSA := slice_noLabel (seg_slice ht hsegA) aw'
  rw [List.length_append, runs_step hSA, ← List.length_append] at hphA hrlA
  have hx1 : (xs ++ directives lw).all (fun d => !d.isLabel) = true := by
    rw [List.all_append, hx, aw']; rfl
  -- the `callq`
  have hsegB : segIn cells l ((xs ++ directives lw) ++ [C] ++ (.label spK :: R ++ zs)) = true := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hsegA
  obtain ⟨t', ht', hY1, hb⟩ := blockAt_of_segIn hsegB hx1 (by simp [hCl])
  rw [ht] at ht'
  cases ht'
  obtain ⟨⟨C', zc⟩, hS1⟩ : ∃ p, (t.drop (xs ++ directives lw).length).take 1 = [p] :=
    List.length_eq_one_iff.mp (by simpa using congrArg List.length hY1)
  rw [List.length_singleton, hS1] at hY1 hb
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hY1
  subst hY1
  have hx2 : ((xs ++ directives lw) ++ [C']).all (fun d => !d.isLabel) = true := by
    rw [List.all_append, hx1]; simp [hCl]
  have hsegL : segIn cells l (((xs ++ directives lw) ++ [C']) ++ .label spK :: (R ++ zs)) = true := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hsegA
  have hRS : segIn cells spK (R ++ zs) = true := segIn_label hsegL
  have hin := inRunB0_of_segIn hRS hR
  obtain ⟨t'', ht'', hg⟩ := labelGap_of_segIn hsegL hx2
  rw [ht] at ht''
  cases ht''
  have hoff : cellOff t ((xs ++ directives lw) ++ [C']).length = cellOff t (xs ++ directives lw).length + zc := by
    rw [List.length_append, List.length_singleton, cellOff_add, hS1]; simp
  rw [hoff, List.length_append, List.length_singleton] at hg
  -- the runs: the one through the `callq`, then those after the return label
  have hph2 := hphA
  have hrl2 := hrlA
  rw [show (C' :: .label spK :: R ++ zs).length = 1 + (.label spK :: R ++ zs).length by
    simp; omega, runs_step (by rw [hS1]; simp [hCl])] at hph2 hrl2
  have hYL := seg_slice ht (xs := (xs ++ directives lw) ++ [C']) (ys := [.label spK])
    (zs := R ++ zs) (by simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
      using hsegA)
  obtain ⟨⟨dl, z0⟩, hL1⟩ : ∃ p, (t.drop ((xs ++ directives lw) ++ [C']).length).take 1 = [p] :=
    List.length_eq_one_iff.mp (by simpa using congrArg List.length hYL)
  rw [List.length_singleton, hL1] at hYL
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hYL
  subst hYL
  rw [List.length_append, List.length_singleton] at hL1
  have htk : t.take ((xs ++ directives lw).length + 1) = t.take (xs ++ directives lw).length ++ [(C', zc)] := by
    rw [List.take_add, hS1]
  have hsplit : (t.drop ((xs ++ directives lw).length + 1)).take (1 + (R ++ zs).length) =
      (t.drop ((xs ++ directives lw).length + 1)).take 1 ++
        (t.drop ((xs ++ directives lw).length + 1 + 1)).take (R ++ zs).length := by
    rw [List.take_add, List.drop_drop]
  rw [show (Directive.label spK :: R ++ zs).length = 1 + (R ++ zs).length by
    simp; omega, hsplit, hL1, htk] at hph2 hrl2
  simp only [List.singleton_append, runsAux, List.mem_cons, forall_eq_or_imp] at hph2 hrl2
  obtain ⟨hfirst, hafter⟩ := hph2
  obtain ⟨-, hrafter⟩ := hrl2
  simp only [List.reverse_reverse] at hfirst
  have hblk := blkPh_of_runPhB (xs := t.take (xs ++ directives lw).length) (ys := [(C', zc)]) (zs := [])
    (by simpa using hfirst) (by rw [← hC]; simp [classify_callq])
  have e1 : cellOff (t.take (xs ++ directives lw).length ++ [(C', zc)] ++ [])
      (t.take (xs ++ directives lw).length).length = cellOff t (xs ++ directives lw).length := by
    unfold cellOff
    rw [List.append_assoc, List.take_left' rfl]
  rw [e1] at hblk
  -- the `callq`'s pc in the phase of `ra`
  have hpcph : ph (lab l + Int64.ofNat (cellOff t (xs ++ directives lw).length)).toBitVec.toNat =
      ph ra.toBitVec.toNat := by
    have hf : runPhB okPc ph lab (lab l) ra (t.take (xs ++ directives lw).length ++ [(C', zc)]) = true := by
      simpa using hfirst
    have h0 := (Scc.Cert.Ph1X64.runPhB_get (k := (t.take (xs ++ directives lw).length).length) hf (by simp)).2.1
    have e2 : cellOff (t.take (xs ++ directives lw).length ++ [(C', zc)]) (t.take (xs ++ directives lw).length).length =
        cellOff t (xs ++ directives lw).length := by
      unfold cellOff
      rw [List.take_left' rfl]
    rw [e2, hl] at h0
    exact h0
  -- the return label's address
  have hsp : lab spK = lab l + Int64.ofNat (cellOff t (xs ++ directives lw).length) + Int64.ofNat zc := by
    rw [hgap _ _ _ _ hg, Int64.ofNat_add, Int64.add_assoc]
  have ht2 := after_label hsegL ht
  rw [List.length_append, List.length_singleton] at ht2
  -- the return label in the phase of `ra`
  have hrlS : ∀ r ∈ runsAux spK [] ((t.drop ((xs ++ directives lw).length + 1 + 1)).take (R ++ zs).length),
      ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
    simpa [Nat.add_assoc] using hrafter
  have hspk : ph (lab spK).toBitVec.toNat = ph ra.toBitVec.toNat := by
    obtain ⟨y, hy⟩ := runsAux_head spK _ _
    exact hrlS _ hy
  subst hC hK
  rw [← hpcl] at hblk hpcph
  refine ⟨zl, zc, hzl, hcdl, ⟨⟨l, (xs ++ directives lw).length, cellOff t (xs ++ directives lw).length, hpcl.symm,
    hb, hg, hblk, by rw [hpcl, ← hsp]; exact hspk⟩, hpcph, hin⟩, by rw [hpcl]; exact hsp, ht2, hRS,
    by simpa [Nat.add_assoc] using hafter, hrlS⟩

/-- **An `Accepted2` block's code after its label gives `CodeC2`**: the
code `code` its instructions `is` (`InstC2`, a stack map each, `ms`) and
terminator `tm` (`TermC2`) emit from a state `s` (the label counter
`s.next`), after the label-free `xs` and before `zs` in the segment after
`l` (`segIn`; the cells `t`), every run from there passing `runPhB` at `lab`
(`hph`) and in the phase of `ra` (`hrl`); the stack maps on (`hm`), and
`lab` following the labels' gaps (`hgap`). Each call's return label starts
a new run. Each piece at `CdCQ Q`, for `l` and every return label of `Q`
(`hQK`). -/
theorem codeC2_of_segQ (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    {tm : Scc.IR.Term} (htm : TermC2 tm) {Q : Label → Prop} (hQK : ∀ k : Nat, Q s!".L{fr.fn}.x{k}") :
    ∀ (is : List Scc.IR.Inst) (ms : List (Option Scc.IR.StackMap.Entry)) (s s' : S) (code : List Item)
      (l : Label) (t : List (Directive × Nat)) (xs zs : List Directive), Q l →
      (∀ i ∈ is, InstC2 i) → is.length ≤ ms.length →
      (do instsCode fr is ms; emitTerm fr tm) s = .ok ((), s') → s'.out = code.reverse ++ s.out →
      after l cells = some t → segIn cells l (xs ++ directives code ++ zs) = true →
      xs.all (fun d => !d.isLabel) = true →
      (∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (directives code ++ zs).length),
        runPhB okPc ph lab (lab r.1) ra r.2 = true) →
      (∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (directives code ++ zs).length),
        ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) →
      CodeC2 fr (CdCQ Q cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) s.next
        (lab l + Int64.ofNat (cellOff t xs.length)) is tm
  | [], ms, s, s', code, l, t, xs, zs, hQ, _, _, h, hD, ht, hseg, hx, hph, _ => by
    obtain ⟨u, s1, hI, hT⟩ := bind_inv h
    rw [instsCode_nil] at hI
    cases hI
    obtain ⟨ct, et, act, -⟩ := emitTerm2_allIns htm hT
    rw [et] at hT
    cases hT
    have hc : code = ct := by
      have h1 : code.reverse ++ s.out = ct.reverse ++ s.out := hD.symm
      have h2 := List.append_cancel_right h1
      rw [← List.reverse_reverse code, h2, List.reverse_reverse]
    subst hc
    obtain ⟨zc, hz, hcd, -⟩ := cdCQ_at hQ ht hseg hx act hph
    exact Or.inr ⟨code, zc, et, hz, hcd⟩
  | i :: is, ms, s, s', code, l, t, xs, zs, hQ, hs, hms, h, hD, ht, hseg, hx, hph, hrl => by
    obtain ⟨m, ms, rfl⟩ : ∃ m ms', ms = m :: ms' := by
      cases ms with
      | nil => simp at hms
      | cons m ms' => exact ⟨m, ms', rfl⟩
    have hs' := List.forall_mem_cons.mp hs
    have hms' : is.length ≤ ms.length := by simp at hms; omega
    obtain ⟨u, s1, hI, hT⟩ := bind_inv h
    rw [instsCode_cons] at hI
    obtain ⟨u2, s2, hE, hI⟩ := bind_inv hI
    have hrest : (do instsCode fr is ms; emitTerm fr tm) s2 = .ok ((), s') := by
      rw [bind_ok hI]; exact hT
    obtain ⟨c', hc'⟩ := (Pre.bind' (instsCode_pre fr is ms) fun _ => emitTerm_pre fr tm).out _ _ _ hrest
    have hD' : s'.out = c'.reverse.reverse ++ s2.out := by rw [List.reverse_reverse]; exact hc'
    by_cases hc : isCall i = false
    · -- an instruction other than a call: label-free items
      obtain ⟨ci, ei, ai⟩ := emitInst2_allIns hs'.1 hc hE
      rw [ei] at hE
      cases hE
      have hcode : code = ci ++ c'.reverse := by
        have h1 : code.reverse ++ s.out = (c' ++ ci.reverse) ++ s.out := by
          rw [← hD, hc', List.append_assoc]
        have h2 := List.append_cancel_right h1
        rw [← List.reverse_reverse code, h2]; simp
      subst hcode
      have hdd : directives (ci ++ c'.reverse) = directives ci ++ directives c'.reverse := dirs_append _ _
      rw [hdd] at hseg hph
      have hseg1 : segIn cells l (xs ++ directives ci ++ (directives c'.reverse ++ zs)) = true := by
        simpa only [List.append_assoc] using hseg
      have hph1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (directives ci ++ (directives c'.reverse ++ zs)).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by
        simpa only [List.append_assoc] using hph
      have hrl1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (directives ci ++ (directives c'.reverse ++ zs)).length),
          ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
        rw [hdd] at hrl
        simpa only [List.append_assoc] using hrl
      obtain ⟨zc, hz, hcd, hpc⟩ := cdCQ_at hQ ht hseg1 hx ai hph1
      have hS := slice_noLabel (seg_slice ht hseg1) ai
      rw [List.length_append, runs_step hS] at hph1 hrl1
      have := codeC2_of_segQ hm hgap htm hQK is ms _ s' c'.reverse l t (xs ++ directives ci) zs hQ hs'.2 hms' hrest
        hD' ht
        (by simpa only [List.append_assoc] using hseg1) (by rw [List.all_append, hx, ai]; rfl)
        (by rw [List.length_append]; exact hph1) (by rw [List.length_append]; exact hrl1)
      refine Or.inl ⟨hc, ci, zc, by rw [emitInst_sm hc none m]; exact ei, hz, hcd, ?_⟩
      rw [hpc]
      exact this
    · -- a call: its arguments' loads `lw`, `callq g`, the return label, its stores `sr`
      have hcall : ∀ (lw sr : List Item) (g : Label) (mp : List (String × List Int × List Int)), AllIns lw →
          AllIns sr → s2 = { out := (lw ++ [Item.d (i64 (.call (rel g))),
            Item.d (.label s!".L{fr.fn}.x{s.next}")] ++ sr).reverse ++ s.out, next := s.next + 1, maps := mp } →
          ∃ zl zc zr, zl.length = (dirs lw).length ∧
            CdCQ Q cells okPc ph lab ra (lab l + Int64.ofNat (cellOff t xs.length)) ((dirs lw).zip zl) ∧
            BlC2 cells okPc ph lab fr ra (lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zl.sum) zc g
              s.next ∧
            zr.length = (dirs sr).length ∧
            CdCQ Q cells okPc ph lab ra (lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zl.sum +
              Int64.ofNat zc) ((dirs sr).zip zr) ∧
            CodeC2 fr (CdCQ Q cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) (s.next + 1)
              (lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zl.sum + Int64.ofNat zc +
                Int64.ofNat zr.sum) is tm := by
        intro lw sr g mp aw asr hs2
        subst hs2
        have hcode : code = (lw ++ [Item.d (i64 (.call (rel g))), Item.d (.label s!".L{fr.fn}.x{s.next}")] ++ sr) ++
            c'.reverse := by
          have h1 : code.reverse ++ s.out = (c' ++ (lw ++ [Item.d (i64 (.call (rel g))),
              Item.d (.label s!".L{fr.fn}.x{s.next}")] ++ sr).reverse) ++ s.out := by
            rw [← hD, hc']; simp
          have h2 := List.append_cancel_right h1
          rw [← List.reverse_reverse code, h2]; simp
        subst hcode
        have hhead : HeadIns (directives sr ++ directives c'.reverse) :=
          headIns_append_all asr (code2_head hm htm is ms _ s' c'.reverse hs'.2 hms' hrest hD')
        have asr' : (directives sr).all (fun d => !d.isLabel) = true := asr
        generalize hDd : directives c'.reverse = D at hseg hph hrl hhead
        have hdd : directives ((lw ++ [Item.d (i64 (.call (rel g))), Item.d (.label s!".L{fr.fn}.x{s.next}")] ++ sr) ++
            c'.reverse) = directives lw ++ i64 (.call (rel g)) :: .label s!".L{fr.fn}.x{s.next}" ::
              (directives sr ++ D) := by
          rw [← hDd]
          simp only [directives_eq_dirs, dirs_append, List.append_assoc]
          rfl
        rw [hdd] at hseg hph hrl
        obtain ⟨zl, zc, hzl, hcdl, hbl, hsp, ht2, hRS, hrs, hrls⟩ := callSegX (R := directives sr ++ D) hgap hQ ht
          (by simpa only [List.append_assoc, List.cons_append] using hseg) hx aw hhead
          (by simpa only [List.append_assoc, List.cons_append] using hph)
          (by simpa only [List.append_assoc, List.cons_append] using hrl)
        generalize hT2 : t.drop ((xs ++ directives lw).length + 1 + 1) = T at ht2 hrs hrls
        -- the stores
        have hsegS : segIn cells s!".L{fr.fn}.x{s.next}" ([] ++ directives sr ++ (D ++ zs)) = true := by
          simpa only [List.nil_append, List.append_assoc] using hRS
        have hphS : ∀ r ∈ runsAux s!".L{fr.fn}.x{s.next}" (T.take ([] : List Directive).length).reverse
            ((T.drop ([] : List Directive).length).take (directives sr ++ (D ++ zs)).length),
            runPhB okPc ph lab (lab r.1) ra r.2 = true := by
          simpa only [List.append_assoc, List.length_nil, List.take_zero, List.reverse_nil, List.drop_zero]
            using hrs
        have hrlS : ∀ r ∈ runsAux s!".L{fr.fn}.x{s.next}" (T.take ([] : List Directive).length).reverse
            ((T.drop ([] : List Directive).length).take (directives sr ++ (D ++ zs)).length),
            ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
          simpa only [List.append_assoc, List.length_nil, List.take_zero, List.reverse_nil, List.drop_zero]
            using hrls
        obtain ⟨zr, hzr, hcdr, hpcr⟩ := cdCQ_at (hQK s.next) ht2 hsegS rfl asr' hphS
        have hSS := slice_noLabel (seg_slice ht2 hsegS) asr'
        rw [List.length_append, runs_step hSS] at hphS hrlS
        -- the rest of the block, after the stores
        have := codeC2_of_segQ hm hgap htm hQK is ms _ s' c'.reverse _ T (directives sr) zs (hQK s.next) hs'.2 hms'
          hrest hD' ht2
          (by rw [hDd]; simpa using hsegS) asr' (by rw [hDd]; simpa using hphS) (by rw [hDd]; simpa using hrlS)
        simp only [List.length_nil, List.nil_append, Spike.Lib.X64.cellOff_zero] at hpcr hcdr
        refine ⟨zl, zc, zr, hzl, hcdl, hbl, hzr, ?_, ?_⟩
        · rw [← hsp]; simpa [directives_eq_dirs] using hcdr
        · rw [← hsp]; rw [← hpcr] at this; simpa using this
      cases hs'.1 with
      | call d g w =>
        obtain ⟨lw, off, mp, hw, hd, aw, hs2⟩ := emitInst_call1_inv hm hE
        obtain ⟨zl, zc, zr, hzl, hcdl, hbl, hzr, hcdr, hcode⟩ := hcall lw [Item.d (stDir off)] _ mp aw
          (allIns_d rfl) hs2
        obtain ⟨z, rfl⟩ := length_one hzr
        exact .inr (.inl ⟨d, g, w, lw, off, zl, zc, z, rfl, hw, hd, hzl, hcdl, hbl, hcdr, by simpa using hcode⟩)
      | newBuf p h' kv u =>
        obtain ⟨lw, off, mp, hw, hd, hs2⟩ := emitInst_callN1_inv hm (newBuf_args_le h' kv u) hE
        obtain ⟨zl, zc, zr, hzl, hcdl, hbl, hzr, hcdr, hcode⟩ := hcall lw [Item.d (stDir off)] _ mp
          (allIns_getOps hw) (allIns_d rfl) hs2
        obtain ⟨z, rfl⟩ := length_one hzr
        exact .inr (.inr (.inl ⟨p, _, lw, off, zl, zc, z, rfl, rfl, hw, hd, hzl, hcdl, hbl, hcdr,
          by simpa using hcode⟩))
      | print a0 a1 =>
        obtain ⟨lw, mp, hw, hs2⟩ := emitInst_callN0_inv hm (by simp) hE
        obtain ⟨zl, zc, zr, hzl, hcdl, hbl, hzr, -, hcode⟩ := hcall lw [] Scc.Lower.Names.print mp
          (allIns_getOps hw) allIns_nil (by rw [hs2]; simp)
        obtain rfl : zr = [] := List.eq_nil_of_length_eq_zero hzr
        exact .inr (.inr (.inr ⟨[a0, a1], lw, zl, zc, rfl, rfl, hw, hzl, hcdl, hbl, by simpa using hcode⟩))
      | _ => exact absurd rfl hc

/-- **`codeC2_of_segQ` at `CdC`** (any label). -/
theorem codeC2_of_seg (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    {tm : Scc.IR.Term} (htm : TermC2 tm)
    (is : List Scc.IR.Inst) (ms : List (Option Scc.IR.StackMap.Entry)) (s s' : S) (code : List Item)
    (l : Label) (t : List (Directive × Nat)) (xs zs : List Directive)
    (hs : ∀ i ∈ is, InstC2 i) (hms : is.length ≤ ms.length)
    (h : (do instsCode fr is ms; emitTerm fr tm) s = .ok ((), s')) (hD : s'.out = code.reverse ++ s.out)
    (ht : after l cells = some t) (hseg : segIn cells l (xs ++ directives code ++ zs) = true)
    (hx : xs.all (fun d => !d.isLabel) = true)
    (hph : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (directives code ++ zs).length),
      runPhB okPc ph lab (lab r.1) ra r.2 = true)
    (hrl : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (directives code ++ zs).length),
      ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CodeC2 fr (CdC cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) s.next
      (lab l + Int64.ofNat (cellOff t xs.length)) is tm :=
  CodeC2.monoCd (fun _ _ h => CdCQ.toCdC h)
    (codeC2_of_segQ (Q := fun _ => True) hm hgap htm (fun _ => trivial) is ms s s' code l t xs zs trivial hs hms
      h hD ht hseg hx hph hrl)

end Code

/-! ## From the placement checks -/

section Place

variable {fr : Scc.Emit.X64.Frame} {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
  {lab : Label → Int64} {ra : Int64} {lo : Nat}

/-- **A placed block of `lowerC2`'s shape gives `CodeC2`** at its label, its
label counter from `n` (`codeC_block`'s twin): its code after the label
(`segIn`) and its runs' phase facts at the code labels (`labC`), every label
read resolving, which `lab` agrees with (`hlab`); every instruction with a
stack map (`hms`). Each piece at `CdCQ Q`, for the block's label and every
return label of `Q` (`hQ`, `hQK`). -/
theorem codeC2_blockQ (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {Q : Label → Prop} (hQK : ∀ k : Nat, Q s!".L{fr.fn}.x{k}")
    {b : Scc.IR.Block} (hQ : Q (labelOf fr.fn b.label)) (hs : Spike.Lib.LowerShape.BlockC2 b)
    {ms : List (Option Scc.IR.StackMap.Entry)}
    (hms : b.insts.length ≤ ms.length) {n n' : Nat} {code : List Item}
    (hc : blockItems fr n b ms = .ok (code, n'))
    (hseg : segIn cells (labelOf fr.fn b.label) (directives code) = true)
    (hph : ∀ r ∈ runs (labelOf fr.fn b.label) (segCells cells (labelOf fr.fn b.label) (directives code).length),
      runPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) ra r = true ∧
        ph (labC lo cells r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CodeC2 fr (CdCQ Q cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) n (lab (labelOf fr.fn b.label))
      b.insts b.term := by
  unfold blockItems at hc
  split at hc
  · next s heq =>
    cases hc
    obtain ⟨i, hi, -, -⟩ := segIn_iff.mp hseg
    obtain ⟨t, ht⟩ : ∃ t, after (labelOf fr.fn b.label) cells = some t := ⟨_, by rw [after_eq, hi]; rfl⟩
    have hsc : ∀ m, segCells cells (labelOf fr.fn b.label) m = t.take m := by
      intro m; unfold segCells; rw [ht]
    have := codeC2_of_segQ (okPc := okPc) (ph := ph) (ra := ra) (lab := lab) hm hgap hs.2 hQK b.insts ms
      { next := n } s s.out.reverse (labelOf fr.fn b.label) t [] [] hQ hs.1 hms
      (by rw [← blockCode_eq]; exact heq) (by simp) ht (by simpa using hseg) rfl
      (fun r hr => by
        have h' := (hph r (by rw [hsc]; simpa [runs] using hr)).1
        simp only [runPh, Bool.and_eq_true] at h'
        obtain ⟨⟨hres, hlabs⟩, hrun⟩ := h'
        rw [labC_eq hlab hres, runPhB_congr fun L hL => labC_eq hlab (List.all_eq_true.mp hlabs L hL)] at hrun
        exact hrun)
      (fun r hr => by
        have h' := hph r (by rw [hsc]; simpa [runs] using hr)
        simp only [runPh, Bool.and_eq_true] at h'
        obtain ⟨⟨⟨hres, -⟩, -⟩, hp⟩ := h'
        rw [labC_eq hlab hres] at hp
        exact hp)
    simpa [Spike.Lib.X64.cellOff_zero] using this
  · cases hc

/-- **`codeC2_blockQ` at `CdC`** (any label). -/
theorem codeC2_block (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {b : Scc.IR.Block} (hs : Spike.Lib.LowerShape.BlockC2 b) {ms : List (Option Scc.IR.StackMap.Entry)}
    (hms : b.insts.length ≤ ms.length) {n n' : Nat} {code : List Item}
    (hc : blockItems fr n b ms = .ok (code, n'))
    (hseg : segIn cells (labelOf fr.fn b.label) (directives code) = true)
    (hph : ∀ r ∈ runs (labelOf fr.fn b.label) (segCells cells (labelOf fr.fn b.label) (directives code).length),
      runPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) ra r = true ∧
        ph (labC lo cells r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CodeC2 fr (CdC cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) n (lab (labelOf fr.fn b.label))
      b.insts b.term :=
  CodeC2.monoCd (fun _ _ h => CdCQ.toCdC h)
    (codeC2_blockQ (Q := fun _ => True) hm hgap hlab (fun _ => trivial) trivial hs hms hc hseg hph)

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.codeC2_of_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms codeC2_of_seg

end Spike.Lib.LowerX64
