import Spike.Lib.Src.NJLB
import Spike.Lib.SlotRepAt
import Spike.Lib.Src.AbortImm2
import Spike.Lib.LowerShapeC2
import Spike.Lib.Src.GroupShape
import Spike.Lib.Src.GroupAlg
import Spike.Lib.Src.GroupPl

/-!
**`main`'s entry after the setup block, at the source** (ISA-neutral): the
body's entry node's source facts of a code block whose parameter is bound
to words `wsA` represented at the parameter's placement (`ofEnv2 (env2 d
na)`); for `main` the pair of the setup block's result and the thread
word, its result's words carried from the setup function's return
placements (`RetJS`'s operands, valued by the result registers) to
`main`'s parameter registers by position.

- `nL`, `grpL_drop`: a layout's operand count, `grpL` consuming exactly it;
- `grpL_transport`: words at the placements a layout makes of operands
  `os` (under `val`) are at those it makes of `os'` (under `val'`) when the
  two agree position by position on the layout's operands;
- `entry2G_rep`, `entry2G_njB`, `entry2G_slotRep`: the entry's source facts
  from the parameter's words at its placement (any parameter type);
- `wordsRep_mainArg`: the pair parameter's words at its placement, from the
  setup result's words at a return's placements and the thread word;
- `wordsSmall_of_rep`: words at placements are small numbers;
- `slotRep_setupCont`: the setup block's continuation (`let a = (r, me);
  tail main a`) placed, `r` at the result's placements, `me` at the last.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv lookupS SRep WordPl WordsRep WordRep grp group)
open Scc.Sem (ValRep)
open Scc.Lower (LitV shapeOf params2)
open Scc.IR (Operand)

/-! ## Grouping by position -/

/-- **The operands a layout's placements take** (a locative two). -/
def nL : LitV → Nat
  | .nil => 0
  | .leaf _ => 1
  | .loc => 2
  | .node l r => nL l + nL r

/-- **`grpL` consumes exactly the layout's operands.** -/
theorem grpL_drop : ∀ (L : LitV) (os : List Operand) (p : List WordPl) (r : List Operand),
    grpL L os = some (p, r) → nL L ≤ os.length ∧ r = os.drop (nL L)
  | .nil, os, p, r, h => by
    simp only [grpL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [nL]
  | .leaf _, [], _, _, h => by simp [grpL] at h
  | .leaf _, o :: os, p, r, h => by
    simp only [grpL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [nL]
  | .loc, [], _, _, h | .loc, [_], _, _, h => by simp [grpL] at h
  | .loc, b :: o :: os, p, r, h => by
    simp only [grpL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [nL]
  | .node l rr, os, p, r, h => by
    simp only [grpL] at h
    cases ha : grpL l os with
    | none => simp [ha] at h
    | some x =>
      obtain ⟨p1, os1⟩ := x
      cases hb : grpL rr os1 with
      | none => simp [ha, hb] at h
      | some y =>
        obtain ⟨p2, os2⟩ := y
        simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨h1, rfl⟩ := grpL_drop l os p1 os1 ha
        obtain ⟨h2, rfl⟩ := grpL_drop rr _ p2 os2 hb
        simp only [List.length_drop] at h2
        refine ⟨by simp only [nL]; omega, ?_⟩
        rw [List.drop_drop]; simp only [nL]

/-- **Placements by position**: the words at the placements a layout `L`
makes of `os` under `val` are at those it makes of `os'` under `val'` when
the layout's operands agree (`hv`), position by position. -/
theorem grpL_transport {lbl : WeakMem.AllocLabel → Option Nat} {val val' : Operand → Option Nat} :
    ∀ (L : LitV) (os os' : List Operand) (p p' : List WordPl) (r r' : List Operand),
    grpL L os = some (p, r) → grpL L os' = some (p', r') →
    (os.take (nL L)).map val = (os'.take (nL L)).map val' →
    ∀ ws, WordsRep lbl val ws p → WordsRep lbl val' ws p'
  | .nil, os, os', p, p', r, r', h, h', _, ws, hw => by
    simp only [grpL, Option.some.injEq, Prod.mk.injEq] at h h'
    obtain ⟨rfl, -⟩ := h
    obtain ⟨rfl, -⟩ := h'
    match ws, hw with
    | [], _ => trivial
  | .leaf _, [], _, _, _, _, _, h, _, _, _, _ => by simp [grpL] at h
  | .leaf _, _ :: _, [], _, _, _, _, _, h', _, _, _ => by simp [grpL] at h'
  | .leaf _, o :: os, o' :: os', p, p', r, r', h, h', hv, ws, hw => by
    simp only [grpL, Option.some.injEq, Prod.mk.injEq] at h h'
    obtain ⟨rfl, -⟩ := h
    obtain ⟨rfl, -⟩ := h'
    simp only [nL, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.cons.injEq,
      and_true] at hv
    match ws, hw with
    | [w], ⟨⟨v, hvo, hr⟩, _⟩ => exact ⟨⟨v, hv ▸ hvo, hr⟩, trivial⟩
  | .loc, [], _, _, _, _, _, h, _, _, _, _ | .loc, [_], _, _, _, _, _, h, _, _, _, _ => by simp [grpL] at h
  | .loc, _ :: _ :: _, [], _, _, _, _, _, h', _, _, _
  | .loc, _ :: _ :: _, [_], _, _, _, _, _, h', _, _, _ => by simp [grpL] at h'
  | .loc, b :: o :: os, b' :: o' :: os', p, p', r, r', h, h', hv, ws, hw => by
    simp only [grpL, Option.some.injEq, Prod.mk.injEq] at h h'
    obtain ⟨rfl, -⟩ := h
    obtain ⟨rfl, -⟩ := h'
    simp only [nL, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.cons.injEq,
      and_true] at hv
    match ws, hw with
    | [w], ⟨⟨vb, vo, hb, ho, hr⟩, _⟩ => exact ⟨⟨vb, vo, hv.1 ▸ hb, hv.2 ▸ ho, hr⟩, trivial⟩
  | .node l rr, os, os', p, p', r, r', h, h', hv, ws, hw => by
    simp only [grpL] at h h'
    cases ha : grpL l os with
    | none => simp [ha] at h
    | some x =>
    obtain ⟨p1, os1⟩ := x
    cases hb : grpL rr os1 with
    | none => simp [ha, hb] at h
    | some y =>
    obtain ⟨p2, os2⟩ := y
    cases ha' : grpL l os' with
    | none => simp [ha'] at h'
    | some x' =>
    obtain ⟨p1', os1'⟩ := x'
    cases hb' : grpL rr os1' with
    | none => simp [ha', hb'] at h'
    | some y' =>
    obtain ⟨p2', os2'⟩ := y'
    simp only [ha, hb, ha', hb', Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h h'
    obtain ⟨rfl, -⟩ := h
    obtain ⟨rfl, -⟩ := h'
    obtain ⟨hl1, rfl⟩ := grpL_drop l os p1 os1 ha
    obtain ⟨hl1', rfl⟩ := grpL_drop l os' p1' os1' ha'
    simp only [nL, List.take_add, List.map_append] at hv
    obtain ⟨hv1, hv2⟩ := List.append_inj hv (by simp; omega)
    have hlen := hw.length
    rw [← List.take_append_drop p1.length ws] at hw ⊢
    have hp1 : (ws.take p1.length).length = p1.length := by
      simp only [List.length_take, List.length_append] at hlen ⊢; omega
    have hw1 : WordsRep lbl val (ws.take p1.length) p1 := by
      simpa [List.take_append_of_le_length (Nat.le_of_eq hp1.symm), hp1] using hw.take p1.length
    have hw2 : WordsRep lbl val (ws.drop p1.length) p2 := by
      have := hw.drop p1.length
      simpa [List.drop_append_of_le_length (Nat.le_of_eq hp1.symm), hp1] using this
    exact (grpL_transport l os os' p1 p1' _ _ ha ha' hv1 _ hw1).append
      (grpL_transport rr _ _ p2 p2' _ _ hb hb' hv2 _ hw2)

/-! ## The entry -/

/-- **The entry environment at the parameter's placement**: the parameter
bound to words `wsA` at its placement in the slot file (`hrep`). -/
theorem entry2G_rep {lbl : WeakMem.AllocLabel → Option Nat} {d : Decl} {na : Nat}
    {env : TermRun.Env} {wsA : List TermRun.Word} (henv : env = [(d.arg, d.argTy, wsA)])
    {val : Operand → Option Nat}
    (hrep : WordsRep lbl val wsA ((group d.argTy ((Spike.Lib.LowerShape.paramsR d na).map .reg)).getD [])) :
    SRep lbl val (ofEnv2 (Spike.Lib.LowerShape.env2 d na)) env := by
  subst henv
  intro y t pls hl
  rw [lookupS_ofEnv2] at hl
  by_cases hy : d.arg = y
  · subst hy
    simp only [Spike.Lib.LowerShape.env2, List.find?, beq_self_eq_true, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨wsA, by simp [TermRun.lookupE], hrep⟩
  · have hy' : (d.arg == y) = false := by simpa using hy
    simp [Spike.Lib.LowerShape.env2, hy'] at hl

/-- **The body's entry node's `NJB`** at the entry control `cE` (the body,
no hold, the parameter bound to `wsA` at its placement, its layout's
number words and slices at a ghost memory meeting `MemB`, its numbers
small), at the entry's layouts and no known values or buffers. -/
theorem entry2G_njB {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {d : Decl} {na : Nat} {cE : Ctl} {wsA : List TermRun.Word}
    (hterm : cE.term = d.body) (hhold : cE.hold = none) (henv : cE.env = [(d.arg, d.argTy, wsA)])
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64}
    (hrep : WordsRep lbl (opdVal rs sl) wsA
      ((group d.argTy ((Spike.Lib.LowerShape.paramsR d na).map .reg)).getD []))
    (hc : Compat d.argTy (shapeOf d.argTy) = true) (hn : NumL (shapeOf d.argTy) wsA)
    {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {B : Nat}
    (hs : SliceL (SlP L sm) (shapeOf d.argTy) wsA) (hm : MemB L sm B) (hS : WordsSmall wsA) :
    NJB p lbl rs ((params2 d).map (·, shapeOf d.argTy)) [] [] L sm lsize B d.body
      (ofEnv2 (Spike.Lib.LowerShape.env2 d na)) sl cE := by
  refine NJB.of_nodeJ ⟨hterm, hhold, entry2G_rep henv hrep⟩ ?_ ?_ hm ?_
  · rw [henv]; exact EnvLit.entry hc hn
  · rw [henv]; exact EnvB.entry hs
  · rw [henv]
    intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact hS

/-- **The body's entry node's `SlotRepAt`** at the entry control `cE`,
from the walk's facts at the entry. -/
theorem entry2G_slotRep {lbl : WeakMem.AllocLabel → Option Nat} {i : Expr → String → Nat → Option Nat}
    {d : Decl} {na : Nat} {cE : Ctl} {wsA : List TermRun.Word}
    (hterm : cE.term = d.body) (hhold : cE.hold = none) (henv : cE.env = [(d.arg, d.argTy, wsA)])
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64}
    (hrep : WordsRep lbl (opdVal rs sl) wsA
      ((group d.argTy ((Spike.Lib.LowerShape.paramsR d na).map .reg)).getD []))
    (htot : ∀ y ∈ Scc.Sem.exprFv d.body, (lookupS (ofEnv2 (Spike.Lib.LowerShape.env2 d na)) y).isSome)
    (hb : LocBaseRegAt (ofEnv2 (Spike.Lib.LowerShape.env2 d na)) d.body)
    (hi : ImmIn i (ofEnv2 (Spike.Lib.LowerShape.env2 d na)) d.body) :
    SlotRepAt i lbl rs sl cE :=
  SlotRepAt.of_nodeJ (t := d.body) ⟨hterm, hhold, entry2G_rep henv hrep⟩ htot hb hi

/-! ## `main`'s pair parameter -/

/-- **`main`'s pair parameter at its placement**: `d`'s parameter the pair
of `S` and the thread pointer (`hd`), grouped at its registers `prs`
(`hg`, `prs` valued `vals k` at position `k`, `hprs`); the setup result's
words `ws` at the placements a return's type `t` makes of operands `ops`
(`hg0`, `t`'s layout `L0` that of `S` up to literals, `hc0`, `he0`), each
operand `k` valued `vals k` (`hops`, `val0`; asked only below the last
register); the thread word `meW` at `vals` of the last register (`hme`).
The placements split as `S`'s `pu` (holding all but the last register,
the words `ws` there) and the last register's `o` (the word `meW`). -/
theorem wordsRep_mainArg {lbl : WeakMem.AllocLabel → Option Nat} {d : Decl} {S : Ty}
    (hd : d.argTy = .prod S (.ptr .pub .void)) (hcS : Compat S (shapeOf S) = true)
    {prs : List Operand} {pls : List WordPl} (hg : group d.argTy prs = some pls)
    {val : Operand → Option Nat} {vals : Nat → Nat}
    (hprs : ∀ k (hk : k < prs.length), val prs[k] = some (vals k))
    {t : Ty} {L0 : LitV} {ops : List Operand} {pls0 : List WordPl} {val0 : Operand → Option Nat}
    {ws : List TermRun.Word} (hg0 : group t ops = some pls0) (hc0 : Compat t L0 = true)
    (he0 : L0.erase = shapeOf S)
    (hops : ∀ k (hk : k < ops.length), k + 1 < prs.length → val0 ops[k] = some (vals k))
    (hw0 : WordsRep lbl val0 ws pls0) {meW : TermRun.Word} (hme : ValRep lbl meW.val (vals (prs.length - 1))) :
    ∃ pu o, pls = pu ++ [.one o] ∧ prs = pu.flatMap WordPl.opds ++ [o] ∧ WordsRep lbl val ws pu ∧
      WordRep lbl val meW (.one o) := by
  -- the result's operands at `S`'s layout
  have hgL0 : grpL (shapeOf S) ops = some (pls0, []) := by
    have h1 : groupL (shapeOf S) ops = some pls0 := by
      rw [← he0, groupL_erase, ← group_grpL hc0, hg0]
    simp only [groupL] at h1
    split at h1
    · rename_i p' hgl; simp only [Option.some.injEq] at h1; subst h1; exact hgl
    · simp at h1
  obtain ⟨hn0, hr0⟩ := grpL_drop _ _ _ _ hgL0
  have hlen0 : ops.length = nL (shapeOf S) := by
    have := congrArg List.length hr0; simp at this; omega
  -- the parameter's registers at the pair's layout
  have hgp : grp (.prod S (.ptr .pub .void)) prs = some (pls, []) := by
    rw [hd] at hg
    simp only [group] at hg
    split at hg
    · rename_i p' hgl; simp only [Option.some.injEq] at hg; subst hg; exact hgl
    · simp at hg
  simp only [grp] at hgp
  cases ha : grp S prs with
  | none => simp [ha] at hgp
  | some x =>
  obtain ⟨pu, os1⟩ := x
  cases hb : grp (.ptr .pub .void) os1 with
  | none => simp [ha, hb] at hgp
  | some y =>
  obtain ⟨pw, os2⟩ := y
  simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at hgp
  obtain ⟨rfl, rfl⟩ := hgp
  have hop := grp_opds S prs pu os1 ha
  rw [grp_grpL S (shapeOf S) hcS] at ha
  obtain ⟨hn1, rfl⟩ := grpL_drop _ _ _ _ ha
  -- the thread pointer's one operand
  obtain ⟨o, ho, rfl⟩ : ∃ o, prs.drop (nL (shapeOf S)) = [o] ∧ pw = [.one o] := by
    match hq : prs.drop (nL (shapeOf S)), hb with
    | [o], hb' =>
      simp only [grp, Option.some.injEq, Prod.mk.injEq] at hb'
      exact ⟨o, rfl, hb'.1.symm⟩
    | [], hb' => simp [grp] at hb'
    | _ :: _ :: _, hb' => simp [grp] at hb'
  rw [ho] at hop
  have hlenp : prs.length = nL (shapeOf S) + 1 := by
    have := congrArg List.length ho; simp at this; omega
  have hvmap : (ops.take (nL (shapeOf S))).map val0 = (prs.take (nL (shapeOf S))).map val := by
    apply List.ext_getElem
    · simp; omega
    · intro k h1 h2
      simp only [List.getElem_map, List.getElem_take]
      simp only [List.length_map, List.length_take] at h1 h2
      rw [hops k (by omega) (by omega), hprs k (by omega)]
  refine ⟨pu, o, rfl, hop.symm, grpL_transport _ ops prs pls0 pu [] _ hgL0 ha hvmap ws hw0,
    vals (prs.length - 1), ?_, hme⟩
  have hk : nL (shapeOf S) < prs.length := by omega
  have : o = prs[nL (shapeOf S)] := by
    have := congrArg (·[0]?) ho
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
    rw [List.getElem?_eq_getElem hk] at this
    exact (Option.some.inj this).symm
  rw [this, hprs _ hk, hlenp, Nat.add_sub_cancel]

/-- **Words at placements are small**: a number at a one-operand placement
is below `2^64` (`ValRep`), none is at a locative's. -/
theorem wordsSmall_of_rep {lbl : WeakMem.AllocLabel → Option Nat} {val : Operand → Option Nat} :
    ∀ {ws : List TermRun.Word} {pls : List WordPl}, WordsRep lbl val ws pls → WordsSmall ws
  | [], _, _ => fun _ h => by cases h
  | _ :: _, [], h => h.elim
  | w :: ws, pl :: pls, ⟨hw, hr⟩ => by
    intro w' hw' n hn
    rcases List.mem_cons.1 hw' with rfl | hw'
    · cases pl with
      | one o =>
        obtain ⟨v, -, hv⟩ := hw
        rw [hn] at hv; exact hv.1
      | loc b off =>
        obtain ⟨vb, vo, -, -, hv⟩ := hw
        rw [hn] at hv; exact hv.elim
    · exact wordsSmall_of_rep hr w' hw' n hn

/-! ## The setup block's continuation -/

/-- **The setup block's continuation placed** (`SlotRepAt` at the control
`let a = (r, me); tail main a` the setup function's `ret` returns into):
`r` bound to words `ws` at placements `pu`, `me` (`hme`, in the caller's
environment `env`) to `meW` at `.one o`, every operand of `pu` and `o` a
register (`hreg`: no immediates, register bases). -/
theorem slotRep_setupCont {i : Expr → String → Nat → Option Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} {env : TermRun.Env} {tr tm : Ty}
    {ws : List TermRun.Word} {meW : TermRun.Word} {pu : List WordPl} {o : Operand}
    (hme : TermRun.lookupE env "me" = some (tm, [meW])) (hw : WordsRep lbl (opdVal rs sl) ws pu)
    (hmw : WordRep lbl (opdVal rs sl) meW (.one o))
    (hreg : ∀ q ∈ pu.flatMap WordPl.opds ++ [o], ∃ r, q = .reg r) :
    SlotRepAt i lbl rs sl
      ⟨.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a")), ("r", tr, ws) :: env, none⟩ := by
  have hl : ∀ x, lookupS [("r", tr, pu), ("me", tm, [.one o])] x =
      if x = "r" then some (tr, pu) else if x = "me" then some (tm, [.one o]) else none := by
    intro x
    by_cases h1 : x = "r"
    · subst h1; rfl
    · by_cases h2 : x = "me"
      · subst h2; rfl
      · have h1' : ("r" == x) = false := by simp; exact Ne.symm h1
        have h2' : ("me" == x) = false := by simp; exact Ne.symm h2
        simp [lookupS, List.find?, h1', h2', h1, h2]
  have hfv : Scc.Sem.exprFv (.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a"))) =
      ["r", "me"] := by decide
  have hpu : ∀ q, (∃ pl ∈ pu, q ∈ pl.opds) → ∃ r, q = .reg r := fun q ⟨pl, hpl, hq⟩ =>
    hreg q (List.mem_append_left _ (List.mem_flatMap.2 ⟨pl, hpl, hq⟩))
  have ho : ∃ r, o = .reg r := hreg o (by simp)
  refine ⟨[("r", tr, pu), ("me", tm, [.one o])], ?_, ?_, ?_, ?_⟩
  · intro x t pls hx
    rw [hl] at hx
    by_cases h1 : x = "r"
    · subst h1
      simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨ws, by simp [TermRun.lookupE], hw⟩
    · by_cases h2 : x = "me"
      · subst h2
        simp only [h1, ite_false, ite_true, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        refine ⟨[meW], ?_, hmw, trivial⟩
        simpa [TermRun.lookupE, List.find?] using hme
      · simp [h1, h2] at hx
  · intro y hy
    rw [hfv] at hy
    rw [hl]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> simp
  · intro y hy ty pls hx b off hb
    rw [hfv] at hy
    rw [hl] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hpu b ⟨_, hb, by simp [WordPl.opds]⟩
    · simp only [show ("me" = "r") = False from by decide, ite_false, ite_true, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      simp at hb
  · intro x k v hx
    rw [hl] at hx
    by_cases h1 : x = "r"
    · subst h1
      simp only [ite_true, Option.bind_some] at hx
      obtain ⟨r, hr⟩ := hpu (.imm v) ⟨_, List.mem_of_getElem? hx, by simp [WordPl.opds]⟩
      cases hr
    · by_cases h2 : x = "me"
      · subst h2
        simp only [h1, ite_false, ite_true, Option.bind_some] at hx
        match k, hx with
        | 0, hx =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, WordPl.one.injEq] at hx
          subst hx
          obtain ⟨r, hr⟩ := ho
          cases hr
      · simp [h1, h2] at hx

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.grpL_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.grpL_transport

/-- info: 'Spike.Lib.LowerNode.entry2G_njB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.entry2G_njB

/-- info: 'Spike.Lib.LowerNode.entry2G_slotRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.entry2G_slotRep

/-- info: 'Spike.Lib.LowerNode.wordsRep_mainArg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.wordsRep_mainArg

/-- info: 'Spike.Lib.LowerNode.slotRep_setupCont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.slotRep_setupCont
