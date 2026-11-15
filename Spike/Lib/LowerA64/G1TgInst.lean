/-
**The items of the emitter's instructions** (AArch64, `Scc.Emit.A64`): the
helpers write plain instructions (`PlainI`: no label, no direct branch), so
the items of each IR instruction and terminator hold only the labels the
emitter names (the context's local labels, a system call's or a site's) and
the direct branches the emitter writes.

- `PlainI`, the helpers' and the context's operand loads and stores;
- `ItemOk`, `inst_itemOk`, `term_itemOk`: every item of an instruction's or
  a terminator's code is a directive or a comment, its label a local label
  or one the instruction places;
- the `Accepted2` instructions (`InstC2`) and terminators (`TermC2`):
  their directives start with an instruction, every label of them is
  followed by an instruction (a call's safepoint label last at most), and
  their direct branches go to the overflow abort or a block label
  (`InstD`, `inst_c2`, `term_c2`).
-/
import Spike.Lib.LowerA64.G1TgSeg
import Spike.Lib.LowerA64.G1TgEmit
import Spike.Lib.G1TgRtLabs
import Spike.Lib.LowerShapeC2Shape

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Emit.A64
open Scc.Cert.Rt.A64 (isIns)
open Spike.Lib.LowerShape (InstC2 TermC2)

/-! ## Every item of an instruction's code -/

/-- **An item of a function's code**: a directive or a comment, its label
(if one) a local label of `c` or one of `G`. -/
def ItemOk (c : FnCtx) (G : List Label) (it : Item) : Prop :=
  (∃ d, it = .d d ∧ ∀ L, d = .label L → (∃ s, L = c.local s) ∨ L ∈ G) ∨ ∃ s, it = .comment s

/-- Every item of a list is `ItemOk`. -/
def AllOk (c : FnCtx) (G : List Label) (its : List Item) : Prop := ∀ it ∈ its, ItemOk c G it

theorem AllOk.ofPlain {c : FnCtx} {G : List Label} {its : List Item} (h : PlainI its) : AllOk c G its :=
  fun it hit => by
    obtain ⟨d, rfl, hi, -⟩ := h it hit
    exact .inl ⟨d, rfl, fun L hL => by subst hL; cases hi⟩

theorem AllOk.nil {c : FnCtx} {G : List Label} : AllOk c G [] := fun _ h => by simp at h

theorem AllOk.append {c : FnCtx} {G : List Label} {A B : List Item} (hA : AllOk c G A) (hB : AllOk c G B) :
    AllOk c G (A ++ B) := fun it h => (List.mem_append.mp h).elim (hA it) (hB it)

theorem AllOk.cons {c : FnCtx} {G : List Label} {it : Item} {A : List Item} (h : ItemOk c G it) (hA : AllOk c G A) :
    AllOk c G (it :: A) := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact hA x hx

theorem AllOk.ite {c : FnCtx} {G : List Label} {p : Prop} [Decidable p] {A B : List Item} (hA : AllOk c G A)
    (hB : AllOk c G B) : AllOk c G (if p then A else B) := by
  split
  · exact hA
  · exact hB

theorem AllOk.mono {c : FnCtx} {G G' : List Label} (hG : ∀ L ∈ G, L ∈ G') {its : List Item} (h : AllOk c G its) :
    AllOk c G' its := fun it hit => by
  rcases h it hit with ⟨d, rfl, hd⟩ | hc
  · exact .inl ⟨d, rfl, fun L hL => (hd L hL).imp id (hG L)⟩
  · exact .inr hc

theorem ItemOk.local (c : FnCtx) (G : List Label) (s : String) : ItemOk c G (lbl (c.local s)) :=
  .inl ⟨_, rfl, fun L hL => .inl ⟨s, by cases hL; rfl⟩⟩

theorem ItemOk.mem (c : FnCtx) {G : List Label} {L : Label} (h : L ∈ G) : ItemOk c G (lbl L) :=
  .inl ⟨_, rfl, fun L' hL => .inr (by cases hL; exact h)⟩

theorem ItemOk.ins (c : FnCtx) (G : List Label) {w : RegWidth} (op : Operation w) : ItemOk c G (ins op) :=
  .inl ⟨_, rfl, fun L hL => by cases hL⟩

theorem ItemOk.comment (c : FnCtx) (G : List Label) (s : String) : ItemOk c G (.comment s) := .inr ⟨s, rfl⟩

theorem AllOk.halt (c : FnCtx) (G : List Label) (s : String) : AllOk c G (halt (c.local s)) :=
  .cons (.local c G s) (.cons (.ins c G _) .nil)

/-- A loop loading operands into registers appends plain instructions. -/
theorem forIn_getOp_plain {c : FnCtx} {β : Type} {l : List β} {f : β → Scc.IR.Operand} {g : β → XReg}
    {out : List Item} {init : List Item} (hi : PlainI init)
    (hF : forIn l init (fun x out => do
      let l ← c.getOp (g x) (f x)
      pure (ForInStep.yield (out ++ l))) = .ok out) : PlainI out := by
  refine forIn_inv PlainI hF hi ?_
  intro x _ s hs r hr
  simp only [bind, Except.bind] at hr
  cases ho : c.getOp (g x) (f x) with
  | error e => rw [ho] at hr; cases hr
  | ok l' =>
    rw [ho] at hr
    simp only [pure, Except.pure, Except.ok.injEq] at hr
    subst hr
    exact hs.append (getOp_plain ho)

/-- The final `return` of an instruction's code. -/
macro "ok_fin" h:ident : tactic =>
  `(tactic| (simp only [pure, Except.pure, Except.ok.injEq] at $h:ident; subst $h:ident))

/-- **Every item of an instruction's code** is a directive or a comment,
its label a local label of the context or one the instruction places
(`instLabs`). -/
theorem inst_itemOk (c : FnCtx) (k : Nat) (i : Scc.IR.Inst) {code : List Item} (h : c.inst k i = .ok code) :
    AllOk c (Spike.Lib.RtLabs.instLabs i) code := by
  cases i with
  | mov d s =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    ok_fin h
    exact (AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (setReg_plain h2))
  | bin op d a b =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact (((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getOp_plain h2))).append
      (AllOk.ofPlain (binOp_plain op))).append (AllOk.ofPlain (setReg_plain h3))
  | un op d a =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact ((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (unOp_plain op))).append
      (AllOk.ofPlain (setReg_plain h3))
  | ext sg w d a =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact ((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (extOp_plain sg w))).append
      (AllOk.ofPlain (setReg_plain h3))
  | setc cc d a b =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact (((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getOp_plain h2))).append
      (.cons (.ins _ _ _) (.cons (.ins _ _ _) .nil))).append (AllOk.ofPlain (setReg_plain h3))
  | select cc d a b t f =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    obtain ⟨l4, h4, h⟩ := ok_bind h
    obtain ⟨l5, h5, h⟩ := ok_bind h
    ok_fin h
    exact ((((((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getOp_plain h2))).append
      (.cons (.ins _ _ _) .nil)).append (AllOk.ofPlain (getOp_plain h3))).append
      (AllOk.ofPlain (getOp_plain h4))).append (.cons (.ins _ _ _) .nil)).append (AllOk.ofPlain (setReg_plain h5))
  | addChk d a b =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact ((((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getOp_plain h2))).append
      (.cons (.ins _ _ _) (.cons (.ins _ _ _) .nil))).append (.cons (.local _ _ _) .nil)).append
      (AllOk.ofPlain (setReg_plain h3))
  | subSat d a b =>
    simp only [FnCtx.inst] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact (((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getOp_plain h2))).append
      (AllOk.ofPlain (subSat_plain _ _ _))).append (AllOk.ofPlain (setReg_plain h3))
  | la d s =>
    simp only [FnCtx.inst] at h
    split at h
    · obtain ⟨l3, h3, h⟩ := ok_bind h
      ok_fin h
      exact (AllOk.ofPlain (addrOf_plain _ _)).append (AllOk.ofPlain (setReg_plain h3))
    · cases h
  | getTp d =>
    simp only [FnCtx.inst] at h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact .cons (.ins _ _ _) (AllOk.ofPlain (setReg_plain h3))
  | load o w d a =>
    cases o <;> simp only [FnCtx.inst] at h
    · obtain ⟨l1, h1, h⟩ := ok_bind h
      obtain ⟨body, hb, h⟩ := ok_bind h
      obtain ⟨l3, h3, h⟩ := ok_bind h
      ok_fin h
      simp only [pure, Except.pure, Except.ok.injEq] at hb
      subst hb
      exact ((AllOk.ofPlain (getReg_plain h1)).append (AllOk.ofPlain (plainLoad_plain _ _))).append
        (AllOk.ofPlain (setReg_plain h3))
    · obtain ⟨l1, h1, h⟩ := ok_bind h
      obtain ⟨body, hb, h⟩ := ok_bind h
      obtain ⟨l3, h3, h⟩ := ok_bind h
      ok_fin h
      simp only [pure, Except.pure, Except.ok.injEq] at hb
      subst hb
      exact ((AllOk.ofPlain (getReg_plain h1)).append ((AllOk.ite .nil (AllOk.ofPlain (addImm_plain _ _ _))).append
        (.cons (.ins _ _ _) .nil))).append (AllOk.ofPlain (setReg_plain h3))
    · obtain ⟨l1, h1, h⟩ := ok_bind h
      obtain ⟨body, hb, -⟩ := ok_bind h
      cases hb
  | store o w a v =>
    cases o with
    | plain =>
      simp only [FnCtx.inst, pure_bind] at h
      obtain ⟨l1, h1, h⟩ := ok_bind h
      cases w <;> (try simp only at h)
      all_goals first
        | (obtain ⟨l2, h2, h⟩ := ok_bind h
           ok_fin h
           exact ((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getReg_plain h2))).append
             (AllOk.ofPlain (strOff_plain _ _ _ _)))
        | (obtain ⟨l2, h2, h⟩ := ok_bind h
           ok_fin h
           exact ((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getAddr_plain h2))).append
             (AllOk.ofPlain (subWordStoreDyn_plain _ _)))
    | rel =>
      simp only [FnCtx.inst, pure_bind] at h
      obtain ⟨l1, h1, h⟩ := ok_bind h
      cases w <;> (try simp only at h)
      all_goals first
        | (obtain ⟨l2, h2, h⟩ := ok_bind h
           ok_fin h
           exact ((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getAddr_plain h2))).append
             (.cons (.ins _ _ _) .nil))
        | (obtain ⟨l2, h2, h⟩ := ok_bind h
           ok_fin h
           exact ((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getAddr_plain h2))).append
             (AllOk.ofPlain (subWordStoreDyn_plain _ _)))
    | acq =>
      simp only [FnCtx.inst] at h
      obtain ⟨l1, h1, h⟩ := ok_bind h
      obtain ⟨rel, hr, -⟩ := ok_bind h
      cases hr
  | rmw op d a v =>
    cases op <;> simp only [FnCtx.inst] at h <;>
      obtain ⟨l1, h1, h⟩ := ok_bind h <;> obtain ⟨l2, h2, h⟩ := ok_bind h <;> obtain ⟨l3, h3, h⟩ := ok_bind h <;>
      ok_fin h <;>
      exact (((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getAddr_plain h2))).append
        (.cons (.ins _ _ _) .nil)).append (AllOk.ofPlain (setReg_plain h3))
  | fence f =>
    simp only [FnCtx.inst] at h
    ok_fin h
    exact .cons (.ins _ _ _) .nil
  | call ds f args =>
    simp only [FnCtx.inst] at h
    split at h
    · obtain ⟨l1, h1, h⟩ := ok_bind h
      obtain ⟨l3, h3, h⟩ := ok_bind h
      ok_fin h
      exact (((AllOk.ofPlain (callArgs_plain h1)).append (.cons (.ins _ _ _) .nil)).append
        (AllOk.ite (.cons (.local _ _ _) .nil) .nil)).append (AllOk.ofPlain (setResults_plain h3))
    · cases h
  | syscall d nr args l =>
    cases l with
    | none =>
      simp only [FnCtx.inst, pure_bind] at h
      obtain ⟨l1, h1, h⟩ := ok_bind h
      obtain ⟨l3, h3, h⟩ := ok_bind h
      ok_fin h
      exact ((((AllOk.ofPlain (getArgs_plain h1)).append (AllOk.ofPlain (movImm_plain _ _))).append .nil).append
        (.cons (.ins _ _ _) .nil)).append (AllOk.ofPlain (setReg_plain h3))
    | some l =>
      simp only [FnCtx.inst] at h
      split at h
      · simp only [pure_bind] at h
        obtain ⟨l1, h1, h⟩ := ok_bind h
        obtain ⟨l3, h3, h⟩ := ok_bind h
        ok_fin h
        exact ((((AllOk.ofPlain (getArgs_plain h1)).append (AllOk.ofPlain (movImm_plain _ _))).append
          (.cons (.mem _ (by simp [Spike.Lib.RtLabs.instLabs])) .nil)).append
          (.cons (.ins _ _ _) .nil)).append (AllOk.ofPlain (setReg_plain h3))
      · obtain ⟨_, h', -⟩ := ok_bind h
        cases h'
  | clone d stack tls entry arg =>
    simp only [FnCtx.inst] at h
    try dsimp only at h
    split at h
    · obtain ⟨spawn, hsp, h⟩ := ok_bind h
      obtain ⟨l1, h1, h⟩ := ok_bind h
      obtain ⟨l2, h2, h⟩ := ok_bind h
      obtain ⟨l3, h3, h⟩ := ok_bind h
      obtain ⟨l4, h4, h⟩ := ok_bind h
      ok_fin h
      have hspawn : PlainI spawn := by
        refine forIn_inv PlainI hsp .nil ?_
        intro x _ s hs r hr
        simp only [bind, Except.bind] at hr
        cases ho : c.getReg x.2 x.1 with
        | error e => rw [ho] at hr; cases hr
        | ok l' =>
          rw [ho] at hr
          simp only [pure, Except.pure, Except.ok.injEq] at hr
          subst hr
          exact hs.append (getReg_plain ho)
      exact (((((((((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getOp_plain h2))).append
        (AllOk.ofPlain (getOp_plain h3))).append (AllOk.ofPlain hspawn)).append
        (AllOk.ofPlain (movImm_plain _ _))).append (AllOk.ofPlain (movImm_plain _ _))).append
        (AllOk.ofPlain (movImm_plain _ _))).append (AllOk.ofPlain (syscall_plain _))).append
        (.cons (.ins _ _ _) (.cons (.local _ _ _) .nil))).append (AllOk.ofPlain (setReg_plain h4))
    · obtain ⟨_, h', -⟩ := ok_bind h
      cases h'
  | slotAddr d s =>
    simp only [FnCtx.inst] at h
    obtain ⟨off, ho, h⟩ := ok_bind h
    obtain ⟨l3, h3, h⟩ := ok_bind h
    ok_fin h
    exact (AllOk.ofPlain (addImm_plain _ _ _)).append (AllOk.ofPlain (setReg_plain h3))
  | site s args =>
    simp only [FnCtx.inst] at h
    try dsimp only at h
    split at h
    · obtain ⟨l1, h1, h⟩ := ok_bind h
      ok_fin h
      exact (AllOk.ofPlain (getArgs_plain h1)).append
        (.cons (.mem _ (by simp [Spike.Lib.RtLabs.instLabs])) (.cons (.ins _ _ _) .nil))
    · obtain ⟨_, h', -⟩ := ok_bind h
      cases h'
  | comment s =>
    simp only [FnCtx.inst] at h
    ok_fin h
    exact .cons (.comment _ _ _) .nil

/-- **Every item of a terminator's code** is a directive or a comment, its
label a local label of the context. -/
theorem term_itemOk (c : FnCtx) (k : Nat) (t : Scc.IR.Term) {code : List Item} (h : c.term k t = .ok code) :
    AllOk c [] code := by
  cases t with
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
        exact ((AllOk.ofPlain hout).append (AllOk.ofPlain (leave_plain c))).append
          (.cons (.local _ _ _) (.cons (.ins _ _ _) .nil))
  | jmp l =>
    simp only [FnCtx.term] at h
    obtain ⟨L, hL, h⟩ := ok_bind h
    ok_fin h
    exact .cons (.ins _ _ _) .nil
  | br cc a b t f =>
    simp only [FnCtx.term] at h
    obtain ⟨l1, h1, h⟩ := ok_bind h
    obtain ⟨l2, h2, h⟩ := ok_bind h
    obtain ⟨Lt, ht, h⟩ := ok_bind h
    obtain ⟨Lf, hf, h⟩ := ok_bind h
    ok_fin h
    exact ((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getOp_plain h2))).append
      (.cons (.ins _ _ _) (.cons (.ins _ _ _) (.cons (.ins _ _ _) .nil)))
  | tail f args =>
    simp only [FnCtx.term] at h
    try dsimp only at h
    split at h
    all_goals first
      | (obtain ⟨_, h', -⟩ := ok_bind h; cases h')
      | (split at h
         all_goals first
           | (obtain ⟨_, h', -⟩ := ok_bind h; cases h')
           | (obtain ⟨l1, h1, h⟩ := ok_bind h
              ok_fin h
              exact ((AllOk.ofPlain (callArgs_plain h1)).append (AllOk.ofPlain (leave_plain c))).append
                (.cons (.ins _ _ _) .nil)))
  | switchTo stack tls f arg =>
    simp only [FnCtx.term] at h
    try dsimp only at h
    split at h
    all_goals first
      | (obtain ⟨_, h', -⟩ := ok_bind h; cases h')
      | (obtain ⟨l1, h1, h⟩ := ok_bind h
         obtain ⟨l2, h2, h⟩ := ok_bind h
         obtain ⟨l3, h3, h⟩ := ok_bind h
         ok_fin h
         exact ((((((AllOk.ofPlain (getOp_plain h1)).append (AllOk.ofPlain (getOp_plain h2))).append
           (AllOk.ofPlain (getOp_plain h3))).append (.cons (.ins _ _ _) (.cons (.ins _ _ _) .nil))).append
           (AllOk.ite (AllOk.ofPlain (movImm_plain _ _)) .nil)).append (.cons (.ins _ _ _) .nil)).append
           (.halt _ _ _))
  | unreachable =>
    simp only [FnCtx.term] at h
    ok_fin h
    exact .halt _ _ _

/-! ## The `Accepted2` instructions' directives -/

/-- The directives of plain items are instructions without direct
targets. -/
theorem directives_plain {its : List Item} (h : PlainI its) :
    ∀ d ∈ directives its, isIns d = true ∧ dirTgt d = none := by
  intro d hd
  obtain ⟨it, hit, hd⟩ := List.mem_filterMap.mp hd
  obtain ⟨d', rfl, hi, ht⟩ := h it hit
  cases hd
  exact ⟨hi, ht⟩

/-- The directives of nonempty plain items are nonempty. -/
theorem directives_plain_ne {its : List Item} (h : PlainI its) (hne : its ≠ []) : directives its ≠ [] := by
  cases its with
  | nil => exact absurd rfl hne
  | cons it its =>
    obtain ⟨d, rfl, -, -⟩ := h it List.mem_cons_self
    simp [directives]

/-- **The directives of a piece of a block's code**: nonempty, starting
with an instruction, every label followed by an instruction, every direct
branch to `Tg`. -/
structure PieceD (Tg : Label → Prop) (D : List Directive) : Prop where
  ne : D ≠ []
  head : ∀ d, D.head? = some d → isIns d = true
  fol : labFollowed D = true
  tgt : ∀ d ∈ D, ∀ T, dirTgt d = some T → Tg T

/-- **The directives of a tail of a piece** (possibly empty): starting with
an instruction, every label followed by an instruction, every direct branch
to `Tg`. -/
structure TailD (Tg : Label → Prop) (D : List Directive) : Prop where
  head : ∀ d, D.head? = some d → isIns d = true
  fol : labFollowed D = true
  tgt : ∀ d ∈ D, ∀ T, dirTgt d = some T → Tg T

theorem PieceD.toTail {Tg : Label → Prop} {D : List Directive} (h : PieceD Tg D) : TailD Tg D :=
  ⟨h.head, h.fol, h.tgt⟩

theorem TailD.ofPlain {Tg : Label → Prop} {its : List Item} (h : PlainI its) : TailD Tg (directives its) where
  head d hd := (directives_plain h d (List.mem_of_mem_head? hd)).1
  fol := labFollowed_of_all (List.all_eq_true.mpr fun d hd => (directives_plain h d hd).1)
  tgt d hd T hT := by rw [(directives_plain h d hd).2] at hT; cases hT

theorem PieceD.ofPlain {Tg : Label → Prop} {its : List Item} (h : PlainI its) (hne : its ≠ []) :
    PieceD Tg (directives its) :=
  let t := TailD.ofPlain (Tg := Tg) h
  ⟨directives_plain_ne h hne, t.head, t.fol, t.tgt⟩

theorem TailD.nil {Tg : Label → Prop} : TailD Tg [] := ⟨fun _ h => by simp at h, rfl, fun _ h => by simp at h⟩

theorem TailD.append {Tg : Label → Prop} {A B : List Directive} (hA : TailD Tg A) (hB : TailD Tg B) :
    TailD Tg (A ++ B) where
  head d hd := by
    cases A with
    | nil => exact hB.head d (by simpa using hd)
    | cons a rest => exact hA.head d (by simpa using hd)
  fol := labFollowed_append hA.fol hB.fol fun a _ b hb => by rw [hB.head b hb]; simp
  tgt d hd := (List.mem_append.mp hd).elim (hA.tgt d) (hB.tgt d)

theorem PieceD.append {Tg : Label → Prop} {A B : List Directive} (hA : PieceD Tg A) (hB : TailD Tg B) :
    PieceD Tg (A ++ B) :=
  let t := hA.toTail.append hB
  ⟨by cases A with | nil => exact absurd rfl hA.ne | cons _ _ => simp, t.head, t.fol, t.tgt⟩

theorem PieceD.append_piece {Tg : Label → Prop} {A B : List Directive} (hA : PieceD Tg A) (hB : PieceD Tg B) :
    PieceD Tg (A ++ B) := hA.append hB.toTail

/-- A label after a piece ending with an instruction, then a tail. -/
theorem PieceD.append_label {Tg : Label → Prop} {A B : List Directive} (hA : PieceD Tg A)
    (hl : ∀ d, A.getLast? = some d → isIns d = true) (L : Label) (hB : TailD Tg B) :
    PieceD Tg (A ++ .label L :: B) where
  ne := by cases A with | nil => exact absurd rfl hA.ne | cons _ _ => simp
  head d hd := by
    cases A with
    | nil => exact absurd rfl hA.ne
    | cons a rest => exact hA.head d (by simpa using hd)
  fol := by
    refine labFollowed_append hA.fol ?_ fun a ha b _ => by rw [hl a ha]; simp
    cases B with
    | nil => rfl
    | cons b bs =>
      rw [labFollowed_cons_cons, hB.fol, hB.head b rfl]
      simp
  tgt d hd T hT := by
    rw [List.mem_append, List.mem_cons] at hd
    rcases hd with hd | rfl | hd
    · exact hA.tgt d hd T hT
    · cases hT
    · exact hB.tgt d hd T hT

theorem PieceD.mono {Tg Tg' : Label → Prop} (h : ∀ T, Tg T → Tg' T) {D : List Directive} (hD : PieceD Tg D) :
    PieceD Tg' D := ⟨hD.ne, hD.head, hD.fol, fun d hd T hT => h T (hD.tgt d hd T hT)⟩

theorem TailD.mono {Tg Tg' : Label → Prop} (h : ∀ T, Tg T → Tg' T) {D : List Directive} (hD : TailD Tg D) :
    TailD Tg' D := ⟨hD.head, hD.fol, fun d hd T hT => h T (hD.tgt d hd T hT)⟩

/-- The last directive of a piece ending with plain items is an
instruction. -/
theorem getLast_append_plain {A : List Directive} {its : List Item} (h : PlainI its) (hne : its ≠ [])
    (d : Directive) (hd : (A ++ directives its).getLast? = some d) : isIns d = true := by
  cases hl : (directives its).getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) (directives_plain_ne h hne)
  | some x =>
    rw [List.getLast?_append, hl, Option.some_or, Option.some.injEq] at hd
    subst hd
    exact (directives_plain h _ (List.mem_of_getLast? hl)).1

/-! ### Nonempty pieces -/

theorem movImm_ne (d : XReg) (n : Int) : movImm d n ≠ [] := by
  unfold movImm; dsimp only; split <;> simp

theorem ldrOff_ne (w : RegWidth) (rt : XReg) (base : RegOrSp .W64) (off : Int) : ldrOff w rt base off ≠ [] := by
  unfold ldrOff; split
  · simp
  · split
    · simp
    · simp

theorem getReg_ne {c : FnCtx} {t : XReg} {r : Scc.IR.Reg} {l : List Item} (h : c.getReg t r = .ok l) : l ≠ [] := by
  unfold FnCtx.getReg at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ldrOff_ne _ _ _ _

theorem getOp_ne {c : FnCtx} {t : XReg} {o : Scc.IR.Operand} {l : List Item} (h : c.getOp t o = .ok l) : l ≠ [] := by
  cases o with
  | reg r => exact getReg_ne h
  | imm v =>
    simp only [FnCtx.getOp, Except.ok.injEq] at h
    subst h
    exact movImm_ne _ _

theorem leave_ne (c : FnCtx) : c.leave ≠ [] := by
  unfold FnCtx.leave
  have := ldrOff_ne .W64 .X29 spW64 (c.frame - 16)
  cases h : ldrOff .W64 .X29 spW64 (c.frame - 16) with
  | nil => exact absurd h this
  | cons _ _ => simp

theorem argRegs_eq : argRegs = [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7] := rfl

/-- The register arguments' loads of a nonempty argument list are
nonempty. -/
theorem getArgs_ne {c : FnCtx} {args : List Scc.IR.Operand} (hne : args ≠ []) {l : List Item}
    (h : c.getArgs args = .ok l) : l ≠ [] := by
  unfold FnCtx.getArgs at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · cases args with
    | nil => exact absurd rfl hne
    | cons a rest =>
      rw [argRegs_eq, List.zip_cons_cons, List.forIn_cons] at h
      simp only [bind, Except.bind] at h
      cases ho : c.getOp .X0 a with
      | error e => rw [ho] at h; cases h
      | ok l0 =>
        rw [ho] at h
        simp only [pure, Except.pure, List.nil_append] at h
        generalize hF : forIn (m := Except String) (rest.zip [XReg.X1, .X2, .X3, .X4, .X5, .X6, .X7]) l0 _ = F at h
        cases F with
        | error e => cases h
        | ok out =>
          simp only [Except.ok.injEq] at h
          subst h
          refine forIn_inv (fun l : List Item => l ≠ []) hF (getOp_ne ho) ?_
          intro x _ s hs r hr
          try simp only [bind, Except.bind] at hr
          cases ho' : c.getOp x.2 x.1 with
          | error e => rw [ho'] at hr; cases hr
          | ok l' =>
            rw [ho'] at hr
            simp only [Except.ok.injEq] at hr
            subst hr
            show s ++ l' ≠ []
            simp [hs]

/-- The call arguments of a nonempty argument list are nonempty. -/
theorem callArgs_ne {c : FnCtx} {args : List Scc.IR.Operand} (hne : args ≠ []) {base : Nat} {l : List Item}
    (h : c.callArgs args base = .ok l) : l ≠ [] := by
  unfold FnCtx.callArgs at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · generalize hF : forIn (m := Except String) ((args.drop argRegs.length).zipIdx) ([] : List Item) _ = F at h
    cases F with
    | error e => cases h
    | ok out =>
      cases hg : c.getArgs (args.take argRegs.length) with
      | error e => simp [hg] at h
      | ok l2 =>
        simp only [hg, pure, Except.pure, Except.ok.injEq] at h
        subst h
        have : args.take argRegs.length ≠ [] := by
          cases args with
          | nil => exact absurd rfl hne
          | cons a rest => simp [argRegs_eq]
        have := getArgs_ne this hg
        simp [this]

end Spike.Lib.LowerA64
