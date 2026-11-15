/-
**The directives of an `Accepted2` block's code** (AArch64): the code of
each `InstC2` instruction and `TermC2` terminator is a piece (`PieceD`:
nonempty, starting with an instruction, every label followed by an
instruction, every direct branch to a known target), so a block's code
after its label is a piece ending with an instruction, and a function's
blocks concatenate into a body (`BodyD`) whose direct branches go to the
overflow abort (only where a checked `+` occurs) or to a block label of the
function.

- `inst_c2`, `inst_call_piece`, `term_c2`: the pieces;
- `instsItems_c2`, `blockItems_c2`, `blockCode_eq`: a block's code;
- `BodyD`, `body_c2`: the blocks' codes (`codesFromN`), with every block's
  label in them.
-/
import Spike.Lib.LowerA64.G1TgInst

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Emit.A64
open Scc.Cert.Rt.A64 (isIns)
open Scc.Cert.Code1A64 (instsItems blockItems)
open Spike.Lib.LowerShape (InstC2 TermC2 BlockC2)

/-! ## Directives of item lists -/

theorem directives_append' (l l' : List Item) : directives (l ++ l') = directives l ++ directives l' := by
  simp [directives, List.filterMap_append]

theorem directives_nil : directives [] = [] := rfl

theorem directives_cons_d (d : Directive) (its : List Item) : directives (.d d :: its) = d :: directives its := rfl

theorem directives_cons_lbl (L : Label) (its : List Item) : directives (lbl L :: its) = .label L :: directives its :=
  rfl

theorem directives_cons_raw (s : String) (its : List Item) : directives (.raw s :: its) = directives its := rfl

theorem directives_cons_comment (s : String) (its : List Item) : directives (.comment s :: its) = directives its :=
  rfl

/-- The directives of items ending with plain items end with an
instruction. -/
theorem getLast_directives_plain {A : List Item} {its : List Item} (h : PlainI its) (hne : its ≠ [])
    (d : Directive) (hd : (directives (A ++ its)).getLast? = some d) : isIns d = true := by
  rw [directives_append'] at hd
  exact getLast_append_plain h hne d hd

theorem PieceD.ofPlain_append {Tg : Label → Prop} {A B : List Item} (hA : PlainI A) (hne : A ≠ []) (hB : PlainI B) :
    PieceD Tg (directives (A ++ B)) :=
  PieceD.ofPlain (hA.append hB) fun h => hne (List.append_eq_nil_iff.mp h).1

/-- A tail then a piece is a piece. -/
theorem TailD.append_piece {Tg : Label → Prop} {A B : List Directive} (hA : TailD Tg A) (hB : PieceD Tg B) :
    PieceD Tg (A ++ B) where
  ne := fun h => hB.ne (List.append_eq_nil_iff.mp h).2
  head := (hA.append hB.toTail).head
  fol := (hA.append hB.toTail).fol
  tgt := (hA.append hB.toTail).tgt

/-- The last of `A ++ B` for nonempty `B`. -/
theorem getLast?_append_of_ne {α : Type} {A B : List α} (hB : B ≠ []) : (A ++ B).getLast? = B.getLast? := by
  rw [List.getLast?_append]
  cases hb : B.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hb) hB
  | some b => rfl

/-! ## The `Accepted2` instructions -/

/-- **A call's code is a piece** for a nonempty argument list: the
arguments' loads, `bl`, the safepoint label (with maps) and the results'
stores. -/
theorem inst_call_piece {c : FnCtx} {k : Nat} {ds : List Scc.IR.Reg} {f : Scc.IR.Sym} {args : List Scc.IR.Operand}
    (hargs : args ≠ []) {code : List Item} (h : c.inst k (.call ds f args) = .ok code) {Tg : Label → Prop} :
    PieceD Tg (directives code) := by
  simp only [FnCtx.inst] at h
  split at h
  · obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    have hbl : PlainI [call f] := PlainI.single _ rfl
    have hA : PieceD Tg (directives (l1 ++ [call f])) := PieceD.ofPlain_append (callArgs_plain h1) (callArgs_ne hargs h1) hbl
    split
    · rw [show l1 ++ [call f] ++ [lbl (c.local s!"sp{k}")] ++ l3 = (l1 ++ [call f]) ++ lbl (c.local s!"sp{k}") :: l3 by
        simp, directives_append', directives_cons_lbl]
      exact hA.append_label (fun d hd => getLast_directives_plain hbl (by simp) d hd) _ (TailD.ofPlain (setResults_plain h3))
    · rw [List.append_nil, directives_append']
      exact hA.append (TailD.ofPlain (setResults_plain h3))
  · cases h

/-- **An `Accepted2` instruction's code is a piece**, its direct branch (a
checked `+`'s) to the overflow abort. -/
theorem inst_c2 {c : FnCtx} {k : Nat} {i : Scc.IR.Inst} (hi : InstC2 i) {code : List Item}
    (h : c.inst k i = .ok code) {Tg : Label → Prop}
    (hovf : (∃ d a b, i = .addChk d a b) → Tg (c.local "abort_overflow")) : PieceD Tg (directives code) := by
  cases hi with
  | addChk d a b =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    have hT := hovf ⟨d, a, b, rfl⟩
    rw [show l1 ++ l2 ++ addChecked .X9 .X9 .X10 (c.local "abort_overflow") ++ [lbl (c.local s!"x{k}")] ++ l3 =
        (l1 ++ l2 ++ addChecked .X9 .X9 .X10 (c.local "abort_overflow")) ++ lbl (c.local s!"x{k}") :: l3 by simp,
      directives_append', directives_cons_lbl]
    have hadd : TailD Tg (directives (addChecked .X9 .X9 .X10 (c.local "abort_overflow"))) := by
      refine ⟨fun d hd => ?_, rfl, fun d hd T hT' => ?_⟩
      · cases hd; rfl
      · simp only [addChecked, ins, directives, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
          List.mem_nil_iff, or_false] at hd
        rcases hd with rfl | rfl
        · cases hT'
        · cases hT'; exact hT
    refine PieceD.append_label ?_ ?_ _ (TailD.ofPlain (setReg_plain h3))
    · rw [directives_append', directives_append']
      exact ((PieceD.ofPlain (getOp_plain h1) (getOp_ne h1)).append (TailD.ofPlain (getOp_plain h2))).append hadd
    · intro d hd
      rw [directives_append', getLast?_append_of_ne (by simp [addChecked, ins, directives])] at hd
      simp only [addChecked, ins, directives, List.filterMap_cons, List.filterMap_nil, List.getLast?_cons_cons,
        List.getLast?_singleton, Option.some.injEq] at hd
      subst hd; rfl
  | subSat d a b =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact PieceD.ofPlain
      ((((getOp_plain h1).append (getOp_plain h2)).append (subSat_plain _ _ _)).append (setReg_plain h3))
      (by simp [getOp_ne h1])
  | call d g w => exact inst_call_piece (by simp) h
  | newBuf p hh kv u => exact inst_call_piece (by simp) h
  | print a0 a1 => exact inst_call_piece (by simp) h
  | load d a =>
    simp only [Spike.Lib.LowerShape.xchgLoad, FnCtx.inst, pure_bind] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact PieceD.ofPlain (((getReg_plain h1).append (plainLoad_plain _ _)).append (setReg_plain h3))
      (by simp [getReg_ne h1])
  | store a w =>
    simp only [Spike.Lib.LowerShape.xchgStore, FnCtx.inst, pure_bind] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    ok_fin h
    exact PieceD.ofPlain (((getOp_plain h1).append (getReg_plain h2)).append (strOff_plain _ _ _ _))
      (by simp [getOp_ne h1])
  | ext d o =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact PieceD.ofPlain (((getOp_plain h1).append (extOp_plain _ _)).append (setReg_plain h3))
      (by simp [getOp_ne h1])
  | add d b s =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact PieceD.ofPlain
      ((((getOp_plain h1).append (getOp_plain h2)).append (binOp_plain _)).append (setReg_plain h3))
      (by simp [getOp_ne h1])
  | mul8 d m =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact PieceD.ofPlain
      ((((getOp_plain h1).append (getOp_plain h2)).append (binOp_plain _)).append (setReg_plain h3))
      (by simp [getOp_ne h1])
  | minU d cc s =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    obtain ⟨l4, h4, h⟩ := ok_bind h
    obtain ⟨l5, h5, h⟩ := ok_bind h
    ok_fin h
    refine PieceD.ofPlain ?_ (by simp [getOp_ne h1])
    exact ((((((getOp_plain h1).append (getOp_plain h2)).append (PlainI.single _ rfl)).append
      (getOp_plain h3)).append (getOp_plain h4)).append (PlainI.single _ rfl)).append (setReg_plain h5)

/-- **An `Accepted2` terminator's code is a piece ending with an
instruction**, its direct branches (an `if`'s) to block labels. -/
theorem term_c2 {c : FnCtx} {k : Nat} {t : Scc.IR.Term} (ht : TermC2 t) {code : List Item}
    (h : c.term k t = .ok code) {Tg : Label → Prop} (hbl : ∀ l L, c.blockLabel l = .ok L → Tg L) :
    PieceD Tg (directives code) ∧ ∀ d, (directives code).getLast? = some d → isIns d = true := by
  cases ht with
  | ret vs =>
    simp only [FnCtx.term] at h
    split at h
    · cases h
    · generalize hF : forIn (m := Except String) (vs.zip argRegs) ([] : List Item) _ = F at h
      cases F with
      | error e => cases h
      | ok out =>
        have hout : PlainI out := by
          refine forIn_inv PlainI hF .nil ?_
          intro x _ s hs r hr
          simp only [bind, Except.bind] at hr
          cases ho : c.getOp x.2 x.1 with
          | error e => rw [ho] at hr; cases hr
          | ok l' =>
            rw [ho] at hr
            simp only [pure, Except.pure, Except.ok.injEq] at hr
            subst hr
            exact hs.append (getOp_plain ho)
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        rw [show out ++ c.leave ++ [lbl (c.local s!"x{k}"), ret] = (out ++ c.leave) ++ lbl (c.local s!"x{k}") :: [ret] by
          simp, directives_append', directives_cons_lbl]
        have hA : PieceD Tg (directives (out ++ c.leave)) :=
          PieceD.ofPlain (hout.append (leave_plain c)) (by simp [leave_ne c])
        refine ⟨hA.append_label (fun d hd => getLast_directives_plain (leave_plain c) (leave_ne c) d hd) _
          (TailD.ofPlain (PlainI.single _ rfl)), ?_⟩
        intro d hd
        rw [getLast?_append_of_ne (by simp)] at hd
        simp only [ret, ins, directives, List.filterMap_cons, List.filterMap_nil, List.getLast?_cons_cons,
          List.getLast?_singleton, Option.some.injEq] at hd
        subst hd; rfl
  | br p q tl fl =>
    simp only [FnCtx.term] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨Lt, hLt, h⟩ := ok_bind h
    obtain ⟨Lf, hLf, h⟩ := ok_bind h
    ok_fin h
    have htl : TailD Tg (directives [cmpReg .W64 .X9 .X10, jcc (condCode .eq) Lt, jmp Lf]) := by
      refine ⟨fun d hd => ?_, rfl, fun d hd T hT => ?_⟩
      · cases hd; rfl
      · simp only [cmpReg, jcc, jmp, ins, directives, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
          List.mem_nil_iff, or_false] at hd
        rcases hd with rfl | rfl | rfl
        · cases hT
        · cases hT; exact hbl _ _ hLt
        · cases hT; exact hbl _ _ hLf
    rw [directives_append', directives_append']
    refine ⟨((PieceD.ofPlain (getOp_plain h1) (getOp_ne h1)).append (TailD.ofPlain (getOp_plain h2))).append htl, ?_⟩
    intro d hd
    rw [getLast?_append_of_ne (by simp [cmpReg, jcc, jmp, ins, directives])] at hd
    simp only [cmpReg, jcc, jmp, ins, directives, List.filterMap_cons, List.filterMap_nil, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.some.injEq] at hd
    subst hd; rfl

/-! ## A block's code -/

/-- **The instructions' code is a tail** (every label followed by an
instruction, the direct branches to the overflow abort). -/
theorem instsItems_c2 {c : FnCtx} {Tg : Label → Prop} : ∀ {k : Nat} {is : List Scc.IR.Inst},
    (∀ i ∈ is, InstC2 i) → ∀ {code : List Item}, instsItems c k is = .ok code →
    ((∃ i ∈ is, ∃ d a b, i = .addChk d a b) → Tg (c.local "abort_overflow")) → TailD Tg (directives code)
  | _, [], _, code, h, _ => by
    simp only [instsItems, Except.ok.injEq] at h
    subst h
    exact TailD.nil
  | k, i :: is, hi, code, h, hovf => by
    simp only [instsItems] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    ok_fin h
    rw [directives_append']
    refine (inst_c2 (hi i List.mem_cons_self) h1 fun he => hovf ⟨i, List.mem_cons_self, he⟩).toTail.append
      (instsItems_c2 (fun j hj => hi j (List.mem_cons_of_mem _ hj)) h2 fun ⟨j, hj, he⟩ =>
        hovf ⟨j, List.mem_cons_of_mem _ hj, he⟩)

/-- **An `Accepted2` block's code after its label is a piece ending with an
instruction.** -/
theorem blockItems_c2 {c : FnCtx} {k : Nat} {b : Scc.IR.Block} (hb : BlockC2 b) {code : List Item}
    (h : blockItems c k b = .ok code) {Tg : Label → Prop}
    (hovf : (∃ i ∈ b.insts, ∃ d a b, i = .addChk d a b) → Tg (c.local "abort_overflow"))
    (hbl : ∀ l L, c.blockLabel l = .ok L → Tg L) :
    PieceD Tg (directives code) ∧ ∀ d, (directives code).getLast? = some d → isIns d = true := by
  unfold blockItems at h
  obtain ⟨l1, h1, h⟩ := ok_bind h
  obtain ⟨l2, h2, h⟩ := ok_bind h
  ok_fin h
  obtain ⟨hp, hl⟩ := term_c2 hb.2 h2 hbl
  rw [directives_append']
  refine ⟨(instsItems_c2 hb.1 h1 hovf).append_piece hp, fun d hd => hl d ?_⟩
  rwa [getLast?_append_of_ne hp.ne] at hd

/-- **A block's items** (`blockCode`): its label then its code. -/
theorem blockCode_eq {c : FnCtx} {k : Nat} {b : Scc.IR.Block} {code : List Item} (h : blockCode c k b = .ok code) :
    ∃ L body, c.blockLabel b.label = .ok L ∧ blockItems c k b = .ok body ∧ code = lbl L :: body := by
  unfold blockCode at h
  obtain ⟨L, hL, h⟩ := ok_bind h
  obtain ⟨body, hbody, h⟩ := ok_bind h
  ok_fin h
  exact ⟨L, body, hL, hbody, rfl⟩

/-! ## The blocks' codes -/

/-- **A body**: every label followed by an instruction, ending with an
instruction (if nonempty), every direct branch to `Tg`. -/
structure BodyD (Tg : Label → Prop) (D : List Directive) : Prop where
  fol : labFollowed D = true
  last : ∀ d, D.getLast? = some d → isIns d = true
  tgt : ∀ d ∈ D, ∀ T, dirTgt d = some T → Tg T

theorem BodyD.nil {Tg : Label → Prop} : BodyD Tg [] := ⟨rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem BodyD.append {Tg : Label → Prop} {A B : List Directive} (hA : BodyD Tg A) (hB : BodyD Tg B) :
    BodyD Tg (A ++ B) where
  fol := labFollowed_append hA.fol hB.fol fun a ha _ _ => by rw [hA.last a ha]; rfl
  last d hd := by
    cases hb : B.getLast? with
    | none => rw [List.getLast?_append, hb, Option.none_or] at hd; exact hA.last d hd
    | some x => rw [List.getLast?_append, hb, Option.some_or, Option.some.injEq] at hd; subst hd; exact hB.last x hb
  tgt d hd := (List.mem_append.mp hd).elim (hA.tgt d) (hB.tgt d)

/-- A label then a piece ending with an instruction is a body. -/
theorem BodyD.label {Tg : Label → Prop} (L : Label) {D : List Directive} (hD : PieceD Tg D)
    (hl : ∀ d, D.getLast? = some d → isIns d = true) : BodyD Tg (.label L :: D) where
  fol := by
    cases D with
    | nil => exact absurd rfl hD.ne
    | cons d ds => rw [labFollowed_cons_cons, hD.fol, hD.head d rfl]; rfl
  last d hd := by
    cases D with
    | nil => exact absurd rfl hD.ne
    | cons x xs => exact hl d (by simpa using hd)
  tgt d hd T hT := by
    rcases List.mem_cons.mp hd with rfl | hd
    · cases hT
    · exact hD.tgt d hd T hT

/-- A body then plain items. -/
theorem BodyD.append_plain {Tg : Label → Prop} {A : List Directive} (hA : BodyD Tg A) {its : List Item}
    (h : PlainI its) : BodyD Tg (A ++ directives its) where
  fol := (hA.fol : labFollowed A = true) |> fun hf =>
    labFollowed_append hf (TailD.ofPlain (Tg := Tg) h).fol fun a ha _ _ => by rw [hA.last a ha]; rfl
  last d hd := by
    cases hl : (directives its).getLast? with
    | none => rw [List.getLast?_append, hl, Option.none_or] at hd; exact hA.last d hd
    | some x =>
      rw [List.getLast?_append, hl, Option.some_or, Option.some.injEq] at hd
      subst hd
      exact (directives_plain h _ (List.mem_of_getLast? hl)).1
  tgt d hd := (List.mem_append.mp hd).elim (hA.tgt d) ((TailD.ofPlain (Tg := Tg) h).tgt d)

theorem BodyD.mono {Tg Tg' : Label → Prop} (h : ∀ T, Tg T → Tg' T) {D : List Directive} (hD : BodyD Tg D) :
    BodyD Tg' D := ⟨hD.fol, hD.last, fun d hd T hT => h T (hD.tgt d hd T hT)⟩

/-- **The `Accepted2` blocks' codes form a body** holding every block's
label, its direct branches to the overflow abort (only where a checked `+`
occurs) and to block labels. -/
theorem body_c2 {c : FnCtx} {Tg : Label → Prop}
    (hbl : ∀ l L, c.blockLabel l = .ok L → Tg L) :
    ∀ {k : Nat} {bs : List Scc.IR.Block}, (∀ b ∈ bs, BlockC2 b) → ∀ {bodyL : List (List Item)},
    codesFromN (fun k b => blockCode c k b) blockAdv k bs = .ok bodyL →
    ((∃ b ∈ bs, ∃ i ∈ b.insts, ∃ d a b', i = .addChk d a b') → Tg (c.local "abort_overflow")) →
    BodyD Tg (directives bodyL.flatten) ∧
      ∀ b ∈ bs, ∀ L, c.blockLabel b.label = .ok L → Directive.label L ∈ directives bodyL.flatten
  | _, [], _, bodyL, h, _ => by
    simp only [codesFromN, Except.ok.injEq] at h
    subst h
    exact ⟨BodyD.nil, fun b hb => by simp at hb⟩
  | k, b :: bs, hbs, bodyL, h, hovf => by
    simp only [codesFromN] at h
    obtain ⟨ys, hys, h⟩ := ok_bind h
    obtain ⟨xs, hxs, h⟩ := ok_bind h
    ok_fin h
    obtain ⟨L, body, hL, hbody, rfl⟩ := blockCode_eq hys
    obtain ⟨hp, hl⟩ := blockItems_c2 (hbs b List.mem_cons_self) hbody
      (fun ⟨i, hi, he⟩ => hovf ⟨b, List.mem_cons_self, i, hi, he⟩) hbl
    obtain ⟨ih, ihm⟩ := body_c2 hbl (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb')) hxs
      fun ⟨b', hb', he⟩ => hovf ⟨b', List.mem_cons_of_mem _ hb', he⟩
    rw [List.flatten_cons, directives_append', directives_cons_lbl]
    refine ⟨(BodyD.label L hp hl).append ih, fun b' hb' L' hL' => ?_⟩
    rcases List.mem_cons.mp hb' with rfl | hb'
    · rw [hL] at hL'
      cases hL'
      exact List.mem_append_left _ List.mem_cons_self
    · exact List.mem_append_right _ (ihm b' hb' L' hL')

end Spike.Lib.LowerA64
