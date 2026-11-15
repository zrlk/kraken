/-
**The labels of a function's output** (AArch64, `emitFunc`): every label
of a function's items is its name, a local label of its context or one an
instruction places (`emitFunc_labels`, from `inst_itemOk`/`term_itemOk`);
so a runtime function (`FnRt`: `scc_rt_` names) has no user label (`wcL`),
and an `Accepted2` user function's directives form a `UserPart`: its name's
label, then a body in which every label is followed by an instruction,
ending with an instruction, every direct branch going to a local label of
the function present in the body (`userFunc_part`).

- `fnLabs`, `emitFunc_allOk`, `emitFunc_labels`, `emitFunc_textN`;
- `wcL_rt`, `wcL_local_rt`, `rtFunc_noWc`;
- `cloneSites_c2`, `hasAddChk_of_mem`, `userFunc_part`.
-/
import Spike.Lib.LowerA64.G1TgBlock

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Emit.A64
open Scc.Cert.Rt.A64 (isIns)
open Scc.Cert.Code1A64 (instsItems blockItems hasAddChk)
open Spike.Lib.LowerShape (InstC2 TermC2 BlockC2)
open Spike.Lib.RtLabs (instLabs RtName FnRt)
open Spike.Lib.A64.AllocG (abLabs)

/-! ## Every label of a function's items -/

/-- The labels a function's instructions place, after its name. -/
def fnLabs (f : Scc.IR.Func) : List Label := f.name :: f.blocks.flatMap fun b => b.insts.flatMap instLabs

/-- A block label is a local label of its context. -/
theorem blockLabel_local' {c : FnCtx} {l : Scc.IR.Label} {L : Label} (h : c.blockLabel l = .ok L) :
    ∃ s, L = c.local s := by
  unfold FnCtx.blockLabel at h
  split at h
  · next bi _ =>
    cases h
    exact ⟨s!"{bi}_{sanitize l}", by simp [FnCtx.local, String.append_assoc]; rfl⟩
  · cases h

/-- A block label's IR label is one of the context's blocks. -/
theorem blockLabel_mem {c : FnCtx} {l : Scc.IR.Label} {L : Label} (h : c.blockLabel l = .ok L) : l ∈ c.blocks := by
  unfold FnCtx.blockLabel at h
  split at h
  · next bi hbi =>
    by_cases hm : l ∈ c.blocks
    · exact hm
    · rw [← List.idxOf?_eq_none_iff] at hm
      rw [hm] at hbi
      cases hbi
  · cases h

theorem PlainI.flatMap {α : Type} {l : List α} {g : α → List Item} (h : ∀ x, PlainI (g x)) : PlainI (l.flatMap g) :=
  fun it hit => by
    obtain ⟨x, -, hx⟩ := List.mem_flatMap.mp hit
    exact h x it hx

theorem allocOf_ok (c : FnCtx) (G : List Label) (cs : Bool) : AllOk c G (allocOf c cs) := by
  unfold allocOf
  split
  · exact (((((AllOk.ite (AllOk.cons (.local _ _ _) .nil) .nil).append (AllOk.ofPlain (addImm_plain _ _ _))).append
      (AllOk.cons (.ins _ _ _) .nil)).append (AllOk.ofPlain (ldrOff_plain _ _ _ _))).append
      (AllOk.cons (.ins _ _ _) (AllOk.cons (.ins _ _ _) (AllOk.cons (.ins _ _ _) .nil))))
  · exact AllOk.ofPlain (addImm_plain _ _ _)

theorem saveOf_plain (c : FnCtx) : PlainI (saveOf c) :=
  ((strOff_plain _ _ _ _).append (strOff_plain _ _ _ _)).append (addImm_plain _ _ _)

theorem abortStubOf_ok (c : FnCtx) (G : List Label) (abortFn suffix : String) (kind : Scc.IR.AbortKind) :
    AllOk c G (abortStubOf c abortFn suffix kind) :=
  (((AllOk.cons (.local _ _ _) .nil).append (AllOk.ofPlain (movImm_plain _ _))).append (AllOk.cons (.ins _ _ _) .nil)).append
    (.halt _ _ _)

theorem growStubOf_ok (c : FnCtx) (G : List Label) : AllOk c G (growStubOf c) := by
  unfold growStubOf
  refine (((((((((((((AllOk.cons (.local _ _ _) .nil).append (AllOk.ofPlain (addImm_plain _ _ _))).append
    (AllOk.ofPlain (PlainI.flatMap fun _ => strOff_plain _ _ _ _))).append (AllOk.ofPlain (strOff_plain _ _ _ _))).append
    (AllOk.ofPlain (strOff_plain _ _ _ _))).append (AllOk.ofPlain (addImm_plain _ _ _))).append
    (AllOk.ofPlain (movImm_plain _ _))).append (AllOk.cons (.ins _ _ _) (AllOk.cons (.local _ _ _) .nil))).append
    (AllOk.ofPlain (PlainI.flatMap fun _ => ldrOff_plain _ _ _ _))).append (AllOk.ofPlain (ldrOff_plain _ _ _ _))).append
    (AllOk.ofPlain (ldrOff_plain _ _ _ _))).append (AllOk.ofPlain (addImm_plain _ _ _))).append
    (AllOk.cons (.ins _ _ _) .nil))

theorem childStub_ok (c : FnCtx) (G : List Label) (k : Nat) (entry : Scc.IR.Sym) : AllOk c G (c.childStub k entry) := by
  unfold FnCtx.childStub
  refine ((((AllOk.cons (.local _ _ _) (AllOk.cons (.ins _ _ _) .nil)).append ?_).append
    (AllOk.ite (AllOk.ofPlain (movImm_plain _ _)) .nil)).append (AllOk.cons (.ins _ _ _) .nil)).append (.halt _ _ _)
  intro it hit
  obtain ⟨⟨t, a⟩, -, hx⟩ := List.mem_filterMap.mp hit
  dsimp only at hx
  by_cases hp : (c.spawnArgs.any fun x => x.2 == t) = true
  · rw [ite_eq_left hp] at hx; cases hx; exact .ins _ _ _
  · rw [ite_eq_right hp] at hx; cases hx

theorem stubsOf_ok (c : FnCtx) (G : List Label) (f : Scc.IR.Func) (abortFn : String) (growth : Option Scc.IR.Growth) :
    AllOk c G (stubsOf c f abortFn growth) := by
  unfold stubsOf
  refine (AllOk.ite (AllOk.ite (growStubOf_ok c G) (abortStubOf_ok c G _ _ _)) .nil).append
    ((AllOk.ite (abortStubOf_ok c G _ _ _) .nil).append ?_)
  intro it hit
  obtain ⟨x, -, hx⟩ := List.mem_flatMap.mp hit
  exact childStub_ok c G x.1 x.2 it hx

theorem instsItems_ok (c : FnCtx) : ∀ {k : Nat} {is : List Scc.IR.Inst} {code : List Item},
    instsItems c k is = .ok code → AllOk c (is.flatMap instLabs) code
  | _, [], code, h => by
    simp only [instsItems, Except.ok.injEq] at h
    subst h; exact .nil
  | k, i :: is, code, h => by
    simp only [instsItems] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    ok_fin h
    rw [List.flatMap_cons]
    exact ((inst_itemOk c k i h1).mono fun L hL => List.mem_append_left _ hL).append
      ((instsItems_ok c h2).mono fun L hL => List.mem_append_right _ hL)

theorem blockItems_ok (c : FnCtx) {k : Nat} {b : Scc.IR.Block} {code : List Item} (h : blockItems c k b = .ok code) :
    AllOk c (b.insts.flatMap instLabs) code := by
  unfold blockItems at h
  obtain ⟨l1, h1, h⟩ := ok_bind h
  obtain ⟨l2, h2, h⟩ := ok_bind h
  ok_fin h
  exact (instsItems_ok c h1).append ((term_itemOk c _ _ h2).mono fun L hL => by simp at hL)

theorem body_ok (c : FnCtx) : ∀ {k : Nat} {bs : List Scc.IR.Block} {bodyL : List (List Item)},
    codesFromN (fun k b => blockCode c k b) blockAdv k bs = .ok bodyL →
    AllOk c (bs.flatMap fun b => b.insts.flatMap instLabs) bodyL.flatten
  | _, [], bodyL, h => by
    simp only [codesFromN, Except.ok.injEq] at h
    subst h; exact .nil
  | k, b :: bs, bodyL, h => by
    simp only [codesFromN] at h
    obtain ⟨ys, hys, h⟩ := ok_bind h
    obtain ⟨xs, hxs, h⟩ := ok_bind h
    ok_fin h
    obtain ⟨L, body, hL, hbody, rfl⟩ := blockCode_eq hys
    obtain ⟨s, rfl⟩ := blockLabel_local' hL
    rw [List.flatten_cons, List.flatMap_cons]
    exact (AllOk.cons (.local _ _ _) ((blockItems_ok c hbody).mono fun L hL => List.mem_append_left _ hL)).append
      ((body_ok c hxs).mono fun L hL => List.mem_append_right _ hL)

/-- **Every item of a function's output** after its two assembler lines is
a directive or a comment, its label (if one) the function's name, a local
label of its context or one its instructions place. -/
theorem emitFunc_allOk {abortFn : String} {growth : Option Scc.IR.Growth} {areas : List (Scc.IR.Sym × Nat)} {fi : Nat}
    {f : Scc.IR.Func} {items : List Item} {sps : List Safepoint}
    (h : emitFunc abortFn growth areas fi f = .ok (items, sps)) :
    ∃ rest, items = [.raw ".p2align 2", .raw s!".type {f.name}, %function"] ++ rest ∧
      AllOk (fnCtx abortFn growth areas fi f) (fnLabs f) rest := by
  obtain ⟨params, bodyL, hparams, hbody, rfl⟩ := emitFunc_items h
  refine ⟨[lbl f.name] ++ allocOf (fnCtx abortFn growth areas fi f) f.checkStack ++ saveOf (fnCtx abortFn growth areas fi f) ++
    params ++ bodyL.flatten ++ stubsOf (fnCtx abortFn growth areas fi f) f abortFn growth, by simp, ?_⟩
  exact (((((AllOk.cons (.mem _ List.mem_cons_self) .nil).append (allocOf_ok _ _ _)).append
    (AllOk.ofPlain (saveOf_plain _))).append (AllOk.ofPlain hparams)).append
    ((body_ok _ hbody).mono fun L hL => List.mem_cons_of_mem _ hL)).append (stubsOf_ok _ _ _ _ _)

/-- **Every label of a function's output** is its name, a local label of
its context or one its instructions place. -/
theorem emitFunc_labels {abortFn : String} {growth : Option Scc.IR.Growth} {areas : List (Scc.IR.Sym × Nat)} {fi : Nat}
    {f : Scc.IR.Func} {items : List Item} {sps : List Safepoint}
    (h : emitFunc abortFn growth areas fi f = .ok (items, sps)) {L : Label} (hL : Directive.label L ∈ directives items) :
    L = f.name ∨ (∃ s, L = (fnCtx abortFn growth areas fi f).local s) ∨
      L ∈ f.blocks.flatMap fun b => b.insts.flatMap instLabs := by
  obtain ⟨rest, rfl, hok⟩ := emitFunc_allOk h
  simp only [List.cons_append, List.nil_append, directives_cons_raw] at hL
  obtain ⟨it, hit, hd⟩ := List.mem_filterMap.mp hL
  rcases hok it hit with ⟨d, rfl, hd'⟩ | ⟨s, rfl⟩
  · cases hd
    rcases hd' L rfl with hs | hm
    · exact .inr (.inl hs)
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact .inl rfl
      · exact .inr (.inr hm)
  · cases hd

/-- **Every item of a function's output keeps `.text`.** -/
theorem emitFunc_textN {abortFn : String} {growth : Option Scc.IR.Growth} {areas : List (Scc.IR.Sym × Nat)} {fi : Nat}
    {f : Scc.IR.Func} {items : List Item} {sps : List Safepoint}
    (h : emitFunc abortFn growth areas fi f = .ok (items, sps)) : ∀ it ∈ items, textN it = true := by
  obtain ⟨rest, rfl, hok⟩ := emitFunc_allOk h
  intro it hit
  simp only [List.cons_append, List.nil_append, List.mem_cons] at hit
  rcases hit with rfl | rfl | hit
  · decide
  · exact textN_type _
  · rcases hok it hit with ⟨d, rfl, -⟩ | ⟨s, rfl⟩
    · rfl
    · rfl

/-- **A function's directives start with its name's label.** -/
theorem emitFunc_directives {abortFn : String} {growth : Option Scc.IR.Growth} {areas : List (Scc.IR.Sym × Nat)}
    {fi : Nat} {f : Scc.IR.Func} {items : List Item} {sps : List Safepoint}
    (h : emitFunc abortFn growth areas fi f = .ok (items, sps)) :
    ∃ P', directives items = .label f.name :: P' := by
  obtain ⟨params, bodyL, -, -, rfl⟩ := emitFunc_items h
  refine ⟨directives (allocOf (fnCtx abortFn growth areas fi f) f.checkStack ++ saveOf (fnCtx abortFn growth areas fi f) ++
    params ++ bodyL.flatten ++ stubsOf (fnCtx abortFn growth areas fi f) f abortFn growth), ?_⟩
  rw [show ∀ A B C D E : List Item, [Item.raw ".p2align 2", .raw s!".type {f.name}, %function", lbl f.name] ++ A ++ B ++ C ++
    D ++ E = [Item.raw ".p2align 2", .raw s!".type {f.name}, %function", lbl f.name] ++ (A ++ B ++ C ++ D ++ E) from
    fun _ _ _ _ _ => by simp]
  rfl

/-! ## The runtime's functions: no user label -/

/-- A `scc_rt_` name is no user label. -/
theorem wcL_rt (r : String) : wcL ("scc_rt_" ++ r) = false := by
  unfold wcL
  rw [String.toList_append]
  rfl

/-- A local label of a context named `scc_rt_…` is no user label. -/
theorem wcL_local_rt (c : FnCtx) {r : String} (hn : c.name = "scc_rt_" ++ r) (sfx : String) :
    wcL (c.local sfx) = false := by
  have e : (c.local sfx).toList = ['.', 'L'] ++
      (Nat.toDigits 10 c.fi ++ ('_' :: ((sanitize c.name).toList ++ '.' :: sfx.toList))) := by
    simp [FnCtx.local, FnCtx.prefix, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr]
    rfl
  have es : (sanitize c.name).toList = ['s', 'c', 'c', '_', 'r', 't', '_'] ++ (sanitize r).toList := by
    rw [hn]
    simp only [sanitize, String.toList_map, String.toList_append, List.map_append]
    rfl
  unfold wcL
  rw [e, es]
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
    List.take_zero]
  rw [List.dropWhile_append_of_pos (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)]
  simp

/-- **A runtime function's output has no user label.** -/
theorem rtFunc_noWc {abortFn : String} {growth : Option Scc.IR.Growth} {areas : List (Scc.IR.Sym × Nat)} {fi : Nat}
    {f : Scc.IR.Func} (hf : FnRt f) {items : List Item} {sps : List Safepoint}
    (h : emitFunc abortFn growth areas fi f = .ok (items, sps)) :
    ∀ L, Directive.label L ∈ directives items → wcL L = false := by
  intro L hL
  rcases emitFunc_labels h hL with rfl | ⟨s, rfl⟩ | hm
  · obtain ⟨r, hr⟩ := hf.1
    rw [hr]; exact wcL_rt r
  · obtain ⟨r, hr⟩ := hf.1
    exact wcL_local_rt _ (r := r) hr s
  · obtain ⟨b, hb, hi⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi, hl⟩ := List.mem_flatMap.mp hi
    obtain ⟨r, hr⟩ := hf.2 b hb i hi L hl
    rw [hr]; exact wcL_rt r

/-! ## A user function: a `UserPart` -/

/-- An `Accepted2` function has no `clone`. -/
theorem cloneSites_c2 {f : Scc.IR.Func} (hb : ∀ b ∈ f.blocks, BlockC2 b) : cloneSites f = [] := by
  unfold cloneSites
  suffices ∀ (bs : List Scc.IR.Block), (∀ b ∈ bs, BlockC2 b) → ∀ acc : Nat × List (Nat × Scc.IR.Sym),
      (bs.foldl (fun (acc : Nat × List (Nat × Scc.IR.Sym)) b =>
        let r := b.insts.foldl (fun (acc : Nat × List (Nat × Scc.IR.Sym)) i =>
          (acc.1 + 1, match i with
            | .clone _ _ _ e _ => acc.2 ++ [(acc.1, e)]
            | _ => acc.2)) acc
        (r.1 + 1, r.2)) acc).2 = acc.2 by
    exact this f.blocks hb (0, [])
  intro bs
  induction bs with
  | nil => intro _ acc; rfl
  | cons b bs ih =>
    intro hbs acc
    rw [List.foldl_cons, ih (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb'))]
    have hi := (hbs b List.mem_cons_self).1
    clear ih hbs
    show (List.foldl _ acc b.insts).2 = acc.2
    generalize b.insts = is at hi
    induction is generalizing acc with
    | nil => rfl
    | cons i is ih =>
      rw [List.foldl_cons, ih (hi := fun j hj => hi j (List.mem_cons_of_mem _ hj))]
      cases hi i List.mem_cons_self <;> rfl

/-- A checked `+` in a block makes `hasAddChk`. -/
theorem hasAddChk_of_mem {f : Scc.IR.Func} {b : Scc.IR.Block} (hb : b ∈ f.blocks) {i : Scc.IR.Inst} (hi : i ∈ b.insts)
    {d : Scc.IR.Reg} {a b' : Scc.IR.Operand} (he : i = .addChk d a b') : hasAddChk f = true := by
  subst he
  unfold hasAddChk
  rw [List.any_eq_true]
  exact ⟨b, hb, by rw [List.any_eq_true]; exact ⟨_, hi, rfl⟩⟩

/-- The targets a user function's code branches to. -/
def UTg (c : FnCtx) (f : Scc.IR.Func) (T : Label) : Prop :=
  T = c.local "stack_grow" ∨ T = c.local "stack_check" ∨
  (hasAddChk f = true ∧ (T = c.local "abort_overflow" ∨ T = c.local "abort_overflow_halt")) ∨
  ∃ b ∈ f.blocks, c.blockLabel b.label = .ok T

/-- The frame allocation of a stack-checked function with maps: a body
branching to `stack_grow`, holding `stack_check`. -/
theorem allocOf_body {c : FnCtx} (hm : c.maps = true) {f : Scc.IR.Func} :
    BodyD (UTg c f) (directives (allocOf c true)) ∧ Directive.label (c.local "stack_check") ∈ directives (allocOf c true) := by
  unfold allocOf
  rw [hm]
  simp only [↓reduceIte]
  rw [show ∀ A B C D : List Item, [lbl (c.local "stack_check")] ++ A ++ B ++ C ++ D =
    lbl (c.local "stack_check") :: (A ++ B ++ C ++ D) from fun _ _ _ _ => by simp, directives_cons_lbl,
    directives_append', directives_append', directives_append']
  have hr : PlainI [readTp .X10] := PlainI.single _ rfl
  have htl : TailD (UTg c f) (directives [cmpReg .W64 .X9 .X10, jcc .CC (c.local "stack_grow"), movSp spW64 (xs .X9)]) := by
    refine ⟨fun d hd => ?_, rfl, fun d hd T hT => ?_⟩
    · cases hd; rfl
    · simp only [cmpReg, jcc, movSp, ins, directives, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
        List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · cases hT
      · cases hT; exact .inl rfl
      · cases hT
  refine ⟨BodyD.label _ ((((TailD.ofPlain (addImm_plain _ _ _)).append_piece
    (PieceD.ofPlain hr (by simp))).append (TailD.ofPlain (ldrOff_plain _ _ _ _))).append htl) ?_,
    List.mem_cons_self⟩
  intro d hd
  rw [getLast?_append_of_ne (by simp [cmpReg, jcc, movSp, ins, directives])] at hd
  simp only [cmpReg, jcc, movSp, ins, directives, List.filterMap_cons, List.filterMap_nil, List.getLast?_cons_cons,
    List.getLast?_singleton, Option.some.injEq] at hd
  subst hd; rfl

/-- The grow stub: a body branching to `stack_check`, holding `stack_grow`. -/
theorem growStubOf_body (c : FnCtx) (f : Scc.IR.Func) :
    BodyD (UTg c f) (directives (growStubOf c)) ∧ Directive.label (c.local "stack_grow") ∈ directives (growStubOf c) := by
  unfold growStubOf
  rw [show ∀ A B C D E F G H I J K : List Item,
      [lbl (c.local "stack_grow")] ++ A ++ B ++ C ++ D ++ E ++ F ++ [call Scc.IR.StackMap.morestackSym, lbl (c.local "sp_check")] ++
        G ++ H ++ I ++ J ++ K =
      lbl (c.local "stack_grow") :: ((A ++ B ++ C ++ D ++ E ++ F ++ [call Scc.IR.StackMap.morestackSym]) ++
        lbl (c.local "sp_check") :: (G ++ H ++ I ++ J ++ K)) from fun _ _ _ _ _ _ _ _ _ _ _ => by simp,
    directives_cons_lbl, directives_append', directives_cons_lbl]
  have hpre : PlainI (addImm spW64 spW64 (-80) ++ (argRegs.zipIdx.flatMap fun (r, i) => strOff .W64 r spW64 (8 * i)) ++
      strOff .W64 .X29 spW64 64 ++ strOff .W64 .X30 spW64 72 ++ addImm (xs .X29) spW64 64 ++ movImm .X0 c.frame) :=
    (((((addImm_plain _ _ _).append (PlainI.flatMap fun _ => strOff_plain _ _ _ _)).append (strOff_plain _ _ _ _)).append
      (strOff_plain _ _ _ _)).append (addImm_plain _ _ _)).append (movImm_plain _ _)
  have hpost : PlainI ((argRegs.zipIdx.flatMap fun (r, i) => ldrOff .W64 r spW64 (8 * i)) ++ ldrOff .W64 .X29 spW64 64 ++
      ldrOff .W64 .X30 spW64 72 ++ addImm spW64 spW64 80) :=
    (((PlainI.flatMap fun _ => ldrOff_plain _ _ _ _).append (ldrOff_plain _ _ _ _)).append (ldrOff_plain _ _ _ _)).append
      (addImm_plain _ _ _)
  have hcall : PlainI [call Scc.IR.StackMap.morestackSym] := PlainI.single _ rfl
  have hjmp : TailD (UTg c f) (directives [jmp (c.local "stack_check")]) := by
    refine ⟨fun d hd => ?_, rfl, fun d hd T hT => ?_⟩
    · cases hd; rfl
    · simp only [jmp, ins, directives, List.filterMap_cons, List.filterMap_nil, List.mem_cons, List.mem_nil_iff,
        or_false] at hd
      subst hd
      cases hT; exact .inr (.inl rfl)
  have htail : TailD (UTg c f) (directives (((argRegs.zipIdx.flatMap fun (r, i) => ldrOff .W64 r spW64 (8 * i)) ++
      ldrOff .W64 .X29 spW64 64 ++ ldrOff .W64 .X30 spW64 72 ++ addImm spW64 spW64 80) ++ [jmp (c.local "stack_check")])) := by
    rw [directives_append']; exact (TailD.ofPlain hpost).append hjmp
  have hpiece : PieceD (UTg c f) (directives ((addImm spW64 spW64 (-80) ++
      (argRegs.zipIdx.flatMap fun (r, i) => strOff .W64 r spW64 (8 * i)) ++ strOff .W64 .X29 spW64 64 ++
      strOff .W64 .X30 spW64 72 ++ addImm (xs .X29) spW64 64 ++ movImm .X0 c.frame) ++
      [call Scc.IR.StackMap.morestackSym])) := by
    rw [directives_append']; exact (TailD.ofPlain hpre).append_piece (PieceD.ofPlain hcall (by simp))
  refine ⟨BodyD.label _ (PieceD.append_label hpiece (fun d hd => getLast_directives_plain hcall (by simp) d hd) _ htail) ?_,
    List.mem_cons_self⟩
  intro d hd
  simp only [directives_append'] at hd
  rw [getLast?_append_of_ne (by simp), ← List.cons_append, getLast?_append_of_ne (by simp [jmp, ins, directives])] at hd
  simp only [jmp, ins, directives, List.filterMap_cons, List.filterMap_nil, List.getLast?_singleton,
    Option.some.injEq] at hd
  subst hd; rfl

/-- The overflow abort stub: a body branching to its halt, holding
`abort_overflow` and `abort_overflow_halt`. -/
theorem abortStubOf_body {c : FnCtx} {f : Scc.IR.Func} (hf : hasAddChk f = true) (abortFn : String) :
    BodyD (UTg c f) (directives (abortStubOf c abortFn "abort_overflow" .overflow)) ∧
      Directive.label (c.local "abort_overflow") ∈ directives (abortStubOf c abortFn "abort_overflow" .overflow) ∧
      Directive.label (c.local "abort_overflow_halt") ∈ directives (abortStubOf c abortFn "abort_overflow" .overflow) := by
  unfold abortStubOf halt
  rw [show ∀ A : List Item, [lbl (c.local "abort_overflow")] ++ A ++ [call abortFn] ++
      [lbl (c.local ("abort_overflow" ++ "_halt")), jmp (c.local ("abort_overflow" ++ "_halt"))] =
      lbl (c.local "abort_overflow") :: ((A ++ [call abortFn]) ++
        lbl (c.local ("abort_overflow" ++ "_halt")) :: [jmp (c.local ("abort_overflow" ++ "_halt"))]) from fun _ => by simp,
    directives_cons_lbl, directives_append', directives_cons_lbl]
  have hcall : PlainI [call abortFn] := PlainI.single _ rfl
  have hjmp : TailD (UTg c f) (directives [jmp (c.local ("abort_overflow" ++ "_halt"))]) := by
    refine ⟨fun d hd => ?_, rfl, fun d hd T hT => ?_⟩
    · cases hd; rfl
    · simp only [jmp, ins, directives, List.filterMap_cons, List.filterMap_nil, List.mem_cons, List.mem_nil_iff,
        or_false] at hd
      subst hd
      cases hT; exact .inr (.inr (.inl ⟨hf, .inr rfl⟩))
  have hpiece : PieceD (UTg c f) (directives (movImm .X0 Scc.IR.AbortKind.overflow.code ++ [call abortFn])) := by
    rw [directives_append']; exact (TailD.ofPlain (movImm_plain _ _)).append_piece (PieceD.ofPlain hcall (by simp))
  refine ⟨BodyD.label _ (PieceD.append_label hpiece (fun d hd => getLast_directives_plain hcall (by simp) d hd) _ hjmp) ?_,
    List.mem_cons_self, ?_⟩
  · intro d hd
    rw [getLast?_append_of_ne (by simp)] at hd
    simp only [jmp, ins, directives, List.filterMap_cons, List.filterMap_nil, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.some.injEq] at hd
    subst hd; rfl
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)

/-- **An `Accepted2` user function's directives form a `UserPart`**: for a
context whose local labels are user labels off the write abort's
(`hloc`) and a name that is no user label (`hname`). -/
theorem userFunc_part {abortFn : String} {g : Scc.IR.Growth} {areas : List (Scc.IR.Sym × Nat)} {fi : Nat}
    {f : Scc.IR.Func} (hcs : f.checkStack = true) (hb : ∀ b ∈ f.blocks, BlockC2 b) (hname : wcL f.name = false)
    (hloc : ∀ s, wcL ((fnCtx abortFn (some g) areas fi f).local s) = true ∧
      (fnCtx abortFn (some g) areas fi f).local s ∉ abLabs)
    {items : List Item} {sps : List Safepoint} (h : emitFunc abortFn (some g) areas fi f = .ok (items, sps)) :
    UserPart (directives items) := by
  obtain ⟨params, bodyL, hparams, hbody, rfl⟩ := emitFunc_items h
  generalize hc : fnCtx abortFn (some g) areas fi f = c at hloc hbody ⊢
  have hm : c.maps = true := by rw [← hc]; rfl
  have hblocks : c.blocks = f.blocks.map (·.label) := by rw [← hc]; rfl
  -- the body
  have hbl : ∀ l L, c.blockLabel l = .ok L → UTg c f L := by
    intro l L hL
    have hmem := blockLabel_mem hL
    rw [hblocks, List.mem_map] at hmem
    obtain ⟨b, hb', rfl⟩ := hmem
    exact .inr (.inr (.inr ⟨b, hb', hL⟩))
  obtain ⟨hB, hBm⟩ := body_c2 hbl hb hbody fun ⟨b, hb', i, hi, d, a, b', he⟩ =>
    .inr (.inr (.inl ⟨hasAddChk_of_mem hb' hi he, .inl rfl⟩))
  -- the stubs
  have hstubs : BodyD (UTg c f) (directives (stubsOf c f abortFn (some g))) ∧
      Directive.label (c.local "stack_grow") ∈ directives (stubsOf c f abortFn (some g)) ∧
      (hasAddChk f = true → Directive.label (c.local "abort_overflow") ∈ directives (stubsOf c f abortFn (some g)) ∧
        Directive.label (c.local "abort_overflow_halt") ∈ directives (stubsOf c f abortFn (some g))) := by
    unfold stubsOf
    rw [hcs, cloneSites_c2 hb]
    simp only [ite_true, Option.isSome_some, List.flatMap_nil, List.append_nil, directives_append']
    obtain ⟨hg, hgm⟩ := growStubOf_body c f
    refine ⟨hg.append ?_, List.mem_append_left _ hgm, fun ha => ?_⟩
    · split
      · exact (abortStubOf_body (by assumption) abortFn).1
      · exact BodyD.nil
    · rw [ha]
      simp only [ite_true]
      obtain ⟨-, h1, h2⟩ := abortStubOf_body (c := c) ha abortFn
      exact ⟨List.mem_append_right _ h1, List.mem_append_right _ h2⟩
  obtain ⟨hA, hAm⟩ := allocOf_body (f := f) hm
  rw [hcs]
  -- the whole
  simp only [List.cons_append, List.nil_append, directives_cons_raw, directives_cons_lbl, directives_append']
  have hP : BodyD (UTg c f) (directives (allocOf c true) ++ directives (saveOf c) ++ directives params ++
      directives bodyL.flatten ++ directives (stubsOf c f abortFn (some g))) :=
    (((hA.append_plain (saveOf_plain c)).append_plain hparams).append hB).append hstubs.1
  refine ⟨f.name, _, rfl, hname, hP.fol, hP.last, fun d hd T hT => ?_⟩
  have hT' := hP.tgt d hd T hT
  have hin : Directive.label T ∈ directives (allocOf c true) ++ directives (saveOf c) ++ directives params ++
      directives bodyL.flatten ++ directives (stubsOf c f abortFn (some g)) := by
    rcases hT' with rfl | rfl | ⟨ha, rfl | rfl⟩ | ⟨b, hb', hL⟩
    · exact List.mem_append_right _ hstubs.2.1
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hAm)))
    · exact List.mem_append_right _ (hstubs.2.2 ha).1
    · exact List.mem_append_right _ (hstubs.2.2 ha).2
    · exact List.mem_append_left _ (List.mem_append_right _ (hBm b hb' T hL))
  have hs : ∃ s, T = c.local s := by
    rcases hT' with rfl | rfl | ⟨-, rfl | rfl⟩ | ⟨b, -, hL⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact blockLabel_local' hL
  obtain ⟨s, rfl⟩ := hs
  exact ⟨(hloc s).1, (hloc s).2, hin⟩

end Spike.Lib.LowerA64
