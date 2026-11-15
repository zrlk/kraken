/-
**The branch-target check passes on every `Accepted2` program** (AArch64):
`tgOkB` on scc's output (`Spike/Lib/LowerA64/UserTgt.lean`), for every
configuration, without deciding it on the program.

The output is the header, the runtime functions' and the user functions'
directives, the grow trampoline and the text's end label
(`emitPost_items`, `textDirectives_split`). The runtime functions have no
user label (`rtFunc_noWc`, from `rtFuncs_names`), each user function's
directives form a `UserPart` (`userFunc_part`), and the trampoline's labels
are the runtime's; so the output has the local invariant `TgInv`
(`tgInv_of_parts`) and passes the check (`tgOkB_of_tgInv`). Where the
lowering fails the output is empty and passes trivially.

- `mapM_ok_mem`, `directives_flatMap`, `morestack_labels`, `rtFuncs_len`;
- `funcs2_c2`: a user function's shape (`func2`, every block `BlockC2`);
- `tgOkB_accepted2`: the statement (`TgOkBGen`).
-/
import Spike.Lib.LowerA64.G1TgFunc
import Spike.Lib.LowerProgC2

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Emit.A64
open Scc.Cert.Rt.A64 (isIns)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.LowerShape (InstC2 TermC2 BlockC2 ResC2 func2 lowerC2_resC2)
open Spike.Lib.LowerNode (Pairwise2 LowC2 compiled2 funcs2 lowerAll_accepted2_a64)
open Spike.Lib.RtLabs (FnRt rtFuncs_names)
open Spike.Lib.A64.AllocG (abLabs)

/-! ## Lists -/

/-- A member of a successful `mapM` comes from a successful element. -/
theorem mapM_ok_mem {α β : Type} {f : α → Except String β} : ∀ {l : List α} {rs : List β}, l.mapM f = .ok rs →
    ∀ r ∈ rs, ∃ x ∈ l, f x = .ok r
  | [], rs, h, r, hr => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp at hr
  | x :: l, rs, h, r, hr => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => simp [hx, bind, Except.bind] at h
    | ok b =>
      cases hl : l.mapM f with
      | error e => simp [hx, hl, bind, Except.bind] at h
      | ok bs =>
        simp only [hx, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨y, hy, hfy⟩ := mapM_ok_mem hl r hr
          exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- `mapM` in `Except` keeps the length. -/
theorem mapM_ok_length {α β : Type} {f : α → Except String β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | x :: xs, r, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => simp [hx, bind, Except.bind] at h
    | ok b =>
      cases hxs : xs.mapM f with
      | error e => simp [hx, hxs, bind, Except.bind] at h
      | ok bs =>
        simp only [hx, hxs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [mapM_ok_length hxs]

/-- The directives of a `flatMap` are the flattened directives. -/
theorem directives_flatMap {α : Type} (g : α → List Item) : ∀ (l : List α),
    directives (l.flatMap g) = (l.map fun x => directives (g x)).flatten
  | [] => rfl
  | x :: l => by rw [List.flatMap_cons, directives_append', directives_flatMap g l]; rfl

/-- No label among plain items' directives. -/
theorem no_label_of_plain {its : List Item} (h : PlainI its) {L : Label} (hL : Directive.label L ∈ directives its) :
    False := by
  have := (directives_plain h _ hL).1
  rw [isIns_label] at this
  cases this

/-! ## The runtime -/

/-- **The runtime has 18 functions.** -/
theorem rtFuncs_len {arch : Scc.Arch} {lay : Scc.Layout} {e : Scc.Frontend.Entry} {sw : Nat} {m : List Bool}
    {rt : List Scc.IR.Func} (h : Scc.Lower.Inv.rtFuncs arch lay e sw m = .ok rt) : rt.length = 18 := by
  unfold Scc.Lower.Inv.rtFuncs at h
  rw [mapM_ok_length h]
  simp [Scc.Lower.Runtime.abortKinds]

/-- **The grow trampoline's labels** are its symbol and its return label. -/
theorem morestack_labels (g : Scc.IR.Growth) {L : Label} (h : Directive.label L ∈ directives (morestack g)) :
    L = Scc.IR.StackMap.morestackSym ∨ L = Scc.IR.StackMap.msRetLabel := by
  unfold morestack at h
  simp only [directives_append', List.mem_append, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · simp only [lbl, directives, List.filterMap_cons, List.filterMap_nil, List.mem_cons, List.mem_nil_iff, or_false,
      Directive.label.injEq] at h
    exact .inl h
  · exact (no_label_of_plain (addImm_plain _ _ _) h).elim
  · exact (no_label_of_plain (strOff_plain _ _ _ _) h).elim
  · exact (no_label_of_plain (strOff_plain _ _ _ _) h).elim
  · exact (no_label_of_plain (addImm_plain _ _ _) h).elim
  · simp [movReg, call, addReg, movSp, ins, directives] at h
  · exact (no_label_of_plain (ldrOff_plain _ _ _ _) h).elim
  · exact (no_label_of_plain (ldrOff_plain _ _ _ _) h).elim
  · exact (no_label_of_plain (addImm_plain _ _ _) h).elim
  · simp only [lbl, ret, ins, directives, List.filterMap_cons, List.filterMap_nil, List.mem_cons, List.mem_nil_iff,
      or_false, Directive.label.injEq, reduceCtorEq] at h
    exact .inr h

/-- Plain items keep `.text`. -/
theorem textN_of_plain {its : List Item} (h : PlainI its) {it : Item} (hit : it ∈ its) : textN it = true := by
  obtain ⟨d, rfl, -, -⟩ := h it hit
  rfl

/-- The grow trampoline's items keep `.text`. -/
theorem morestack_textN (g : Scc.IR.Growth) : ∀ it ∈ morestack g, textN it = true := by
  intro it hit
  unfold morestack at hit
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, or_assoc] at hit
  rcases hit with rfl | rfl | rfl | hit | hit | hit | hit | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hit | hit |
    hit | rfl | rfl
  · decide
  · exact textN_type _
  all_goals first
    | rfl
    | (apply textN_of_plain _ hit
       first | exact addImm_plain _ _ _ | exact strOff_plain _ _ _ _ | exact ldrOff_plain _ _ _ _)

/-- The header's items keep `.text`. -/
theorem linuxHead_textN (P : Scc.IR.Program) : ∀ it ∈ linuxHead P, textN it = true := by
  intro it hit
  simp only [linuxHead, List.mem_cons, List.mem_nil_iff, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | rfl

/-- The header's directives. -/
theorem directives_linuxHead (P : Scc.IR.Program) :
    directives (linuxHead P) = [.label Scc.IR.StackMap.textStartSym, .label "_start", .instr ⟨.W64, .B (.label P.start)⟩] :=
  rfl

/-! ## The user functions -/

/-- **A user function of an `Accepted2` program** at index `j` of `funcs2`:
`func2` of a user name, stack-checked, every block `BlockC2`. -/
theorem funcs2_c2 {p : CoreTerm.Prog} {obj : Scc.ObjLayout} {ws : List Spike.Lib.LowerNode.Low2}
    (hws : Pairwise2 (LowC2 p obj) (compiled2 p) ws) {j : Nat} {f : Scc.IR.Func} (hj : (funcs2 p ws)[j]? = some f) :
    (∃ n, f.name = Scc.Lower.Names.user n) ∧ f.checkStack = true ∧ ∀ b ∈ f.blocks, BlockC2 b := by
  unfold funcs2 at hj
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hj
  rw [List.getElem_zipWith] at hget
  have hj' : j < (compiled2 p).length := by simp only [List.length_zipWith] at hlt; omega
  obtain ⟨-, -, hlow⟩ := hws.get j hj'
  have hres := lowerC2_resC2 _ _ _ _ _ _ _ hlow
  subst hget
  refine ⟨⟨_, rfl⟩, rfl, fun b hb => ?_⟩
  simp only [func2, List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact ⟨hres.1, hres.2.1⟩
  · exact hres.2.2 b hb

/-- A user name is no user label (`wcL`). -/
theorem wcL_user (n : String) : wcL (Scc.Lower.Names.user n) = false := by
  unfold wcL Scc.Lower.Names.user
  rw [String.toList_append]
  rfl

/-! ## The check -/

/-- **The branch-target check on every `Accepted2` program**, at every
configuration (`TgOkBStmt`'s body). -/
def TgOkBGen : Prop :=
  ∀ (cfg : Scc.Config) (p : CoreTerm.Prog), Scc.Lower.Accepted2 p = true →
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true

/-- **The branch-target check passes on scc's output of every `Accepted2`
program**, at every configuration. -/
theorem tgOkB_accepted2 (cfg : Scc.Config) (p : CoreTerm.Prog) (hp : Scc.Lower.Accepted2 p = true) :
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true := by
  cases he : Scc.Lower.A64.lowerAll? cfg p with
  | error err =>
    have : Scc.Lower.A64.lowerAll cfg p = default := by simp [Scc.Lower.A64.lowerAll, he]
    rw [this]
    decide
  | ok e =>
    have hle : Scc.Lower.A64.lowerAll cfg p = e := by simp [Scc.Lower.A64.lowerAll, he]
    obtain ⟨ws, rt, hws, hrt, -, hir, -⟩ := lowerAll_accepted2_a64 cfg hp he
    rw [hle] at hir ⊢
    obtain ⟨items, sps, hem, hprog⟩ := lowerAll?_prog he
    rw [hir] at hem
    generalize hP : Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws) = P at hem
    obtain ⟨areas, rs, -, hmap, hpost⟩ := emitItemsMaps_items hem
    have hg : P.growth = some { grow := Scc.Lower.Names.grow, release := Scc.Lower.Names.stackRelease } := by
      rw [← hP]; rfl
    have hh : P.host = .linux := by rw [← hP]; rfl
    have hfuncs : P.funcs = rt ++ funcs2 p ws := by rw [← hP]; rfl
    obtain ⟨ds, hds, hitems⟩ := emitPost_items hg hh hpost
    generalize hG : ({ grow := Scc.Lower.Names.grow, release := Scc.Lower.Names.stackRelease } : Scc.IR.Growth) = g
      at hitems hg
    have hrs : ∀ r ∈ rs, ∃ x ∈ P.funcs.zipIdx, emitFunc P.abortFn (some g) areas x.2 x.1 = .ok r := by
      intro r hr
      obtain ⟨x, hx, hfx⟩ := mapM_ok_mem hmap r hr
      exact ⟨x, hx, by rw [← hg]; exact hfx⟩
    have hrtlen := rtFuncs_len hrt
    -- every function: a runtime function (no user label) or a user function (a `UserPart`)
    have hfn : ∀ r ∈ rs, (∀ it ∈ r.1, textN it = true) ∧ PartOk (directives r.1) ∧
        ∃ L P', directives r.1 = .label L :: P' := by
      intro r hr
      obtain ⟨⟨f, fi⟩, hx, hfx⟩ := hrs r hr
      obtain ⟨r1, r2⟩ := r
      refine ⟨emitFunc_textN hfx, ?_, ?_⟩
      · rw [List.mem_zipIdx_iff_getElem?, hfuncs] at hx
        simp only at hx
        by_cases hfi : fi < rt.length
        · rw [List.getElem?_append_left hfi] at hx
          exact .inl (rtFunc_noWc (rtFuncs_names hrt f (List.mem_of_getElem? hx)) hfx)
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hfi)] at hx
          obtain ⟨⟨n, hn⟩, hcs, hb⟩ := funcs2_c2 hws hx
          refine .inr (userFunc_part hcs hb (by rw [hn]; exact wcL_user n) (fun s => ⟨?_, ?_⟩) hfx)
          · exact wcL_local (fnCtx P.abortFn (some g) areas fi f) (n := n) hn s
          · exact local_not_abLabs (cx := fnCtx P.abortFn (some g) areas fi f) (by simp only [fnCtx]; omega) s
      · obtain ⟨P', hP'⟩ := emitFunc_directives hfx
        exact ⟨_, P', hP'⟩
    -- the output's instruction list
    have htext : Out.prog (Out.ofEmitted e) =
        directives (linuxHead P) ++ ((rs.map fun r => directives r.1).flatten ++
          (directives (morestack g) ++ [.label Scc.IR.StackMap.textEndSym])) := by
      show e.prog = _
      rw [hprog, hitems, textDirectives_split ?_ hds]
      · rw [directives_append', directives_append', directives_append', directives_flatMap]
        simp only [List.append_assoc]
        rfl
      · intro it hit
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hit
        rcases hit with ((hit | hit) | hit) | rfl
        · exact linuxHead_textN P it hit
        · obtain ⟨r, hr, hit⟩ := List.mem_flatMap.mp hit
          exact (hfn r hr).1 it hit
        · exact morestack_textN g it hit
        · rfl
    rw [htext]
    apply tgOkB_of_tgInv
    refine tgInv_of_parts _ (directives (linuxHead P))
      ((rs.map fun r => directives r.1) ++ [directives (morestack g) ++ [.label Scc.IR.StackMap.textEndSym]])
      (by simp) ?_ ?_ ?_
    · -- the header
      intro i hi L0 hL0 hw hab
      rw [List.getElem?_append_left hi, directives_linuxHead] at hL0
      rw [directives_linuxHead, List.length_cons, List.length_cons, List.length_singleton] at hi
      match i, hi, hL0 with
      | 0, _, hL0 =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Directive.label.injEq] at hL0
        subst hL0
        exact absurd hw (by decide)
      | 1, _, hL0 =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq, Directive.label.injEq] at hL0
        subst hL0
        exact absurd hw (by decide)
      | 2, _, hL0 =>
        simp at hL0
    · -- each part
      intro Q hQ
      rw [List.mem_append, List.mem_map, List.mem_singleton] at hQ
      rcases hQ with ⟨r, hr, rfl⟩ | rfl
      · exact (hfn r hr).2.1
      · refine .inl fun L hL => ?_
        rw [List.mem_append, List.mem_singleton, Directive.label.injEq] at hL
        rcases hL with hL | rfl
        · rcases morestack_labels g hL with rfl | rfl <;> decide
        · decide
    · -- each part starts with a label
      intro Q hQ d hd
      rw [List.mem_append, List.mem_map, List.mem_singleton] at hQ
      rcases hQ with ⟨r, hr, rfl⟩ | rfl
      · obtain ⟨L, P', hP'⟩ := (hfn r hr).2.2
        rw [hP'] at hd
        cases hd; rfl
      · have : (directives (morestack g) ++ [Directive.label Scc.IR.StackMap.textEndSym]).head? =
            some (.label Scc.IR.StackMap.morestackSym) := rfl
        rw [this] at hd
        cases hd; rfl

/-- `tgOkB_accepted2` is `TgOkBGen`. -/
theorem tgOkBGen : TgOkBGen := tgOkB_accepted2

/-- info: 'Spike.Lib.LowerA64.tgOkB_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tgOkB_accepted2

end Spike.Lib.LowerA64
