/-
**The source-side facts at a larger level** (ISA-neutral): a fresh
allocation extends the level, its placement `lbl` by a label `l` unplaced
in it (`AllocReach.upd lbl l b`) and its sizes `lsize` by `l`'s
(`AllocReach.updN lsize l n`). The facts of a suspended frame or carried in
a frame condition, stated at `(lbl, lsize)`, hold at the larger level:
every placed label keeps its base, and every size grows (`LvlLe`), when the
fresh label had no size (`lsize l = 0`, which every reachable level keeps
off its placement from one that does: `Reach.lsize_none`).

- `LvlLe`, `lvlLe_upd`, `LvlLe.refl`, `LvlLe.trans`: one level below another;
  a fresh allocation's level above its own.
- `Reach.lsize_none`: an unplaced label has no size at every reachable level
  when it has none at the first.
- `SRep.mono_lbl`, `SlotRepAt.mono_lbl`, `AbSrcL.mono_lbl`: the placement
  facts at more placed labels (`NodeJE.mono_lbl` is `Src/NodeJEMono.lean`'s).
- `EnvQ.mono`, `NJB.mono`: the walk's facts at larger sizes, the node
  invariant at a larger level (the same labels, memory and bound).

`EnvLit` and `RetL` mention neither the placement nor the sizes.
-/
import Spike.Lib.Src.GroupOpds
import Spike.Lib.Src.NodeJEMono
import Spike.Lib.SlotRepAt
import Spike.Lib.AllocReach

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib.Form (SEnv SRep NodeJE WordsRep)

/-! ## Levels -/

/-- **The level `(lbl, lsize)` below `(lbl', lsize')`**: every placed label
placed alike, every size at most the larger level's. -/
def LvlLe (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lbl' : WeakMem.AllocLabel → Option Nat) (lsize' : WeakMem.AllocLabel → Nat) : Prop :=
  (∀ l b, lbl l = some b → lbl' l = some b) ∧ ∀ l, lsize l ≤ lsize' l

theorem LvlLe.refl (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) :
    LvlLe lbl lsize lbl lsize :=
  ⟨fun _ _ h => h, fun _ => Nat.le_refl _⟩

theorem LvlLe.trans {lbl lbl' lbl'' : WeakMem.AllocLabel → Option Nat}
    {lsize lsize' lsize'' : WeakMem.AllocLabel → Nat} (h : LvlLe lbl lsize lbl' lsize')
    (h' : LvlLe lbl' lsize' lbl'' lsize'') : LvlLe lbl lsize lbl'' lsize'' :=
  ⟨fun l b hl => h'.1 l b (h.1 l b hl), fun l => Nat.le_trans (h.2 l) (h'.2 l)⟩

/-- **A fresh allocation's level is above its own**: the label `l` unplaced
(`hl`) and without size (`hz`), placed at `b` with `n` words. -/
theorem lvlLe_upd {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {l : WeakMem.AllocLabel} (hl : lbl l = none) (hz : lsize l = 0) (b n : Nat) :
    LvlLe lbl lsize (AllocReach.upd lbl l b) (AllocReach.updN lsize l n) := by
  refine ⟨fun l' b' h' => ?_, fun l' => ?_⟩
  · unfold AllocReach.upd
    by_cases he : l' = l
    · subst he; rw [hl] at h'; cases h'
    · simp only [he, ite_false]; exact h'
  · unfold AllocReach.updN
    by_cases he : l' = l
    · subst he; rw [hz]; exact Nat.zero_le _
    · simp only [he, ite_false]; exact Nat.le_refl _

/-- **An unplaced label has no size at every reachable level** when every
unplaced label has none at the first. -/
theorem Reach.lsize_none {ar : Arena} {L0 L : WeakMem.AllocLabel → Option Nat}
    {ls0 ls : WeakMem.AllocLabel → Nat}
    (h0 : ∀ l, L0 l = none → ls0 l = 0) (h : AllocReach.Reach ar L0 ls0 L ls) :
    ∀ l, L l = none → ls l = 0 := by
  induction h with
  | base => exact h0
  | @step L ls l' b' n' _ _ _ ih =>
    intro l hl
    unfold AllocReach.upd at hl
    unfold AllocReach.updN
    by_cases he : l = l'
    · simp only [he, ite_true] at hl; cases hl
    · simp only [he, ite_false] at hl ⊢; exact ih l hl

/-! ## Placement facts at more placed labels -/

variable {lbl lbl' : WeakMem.AllocLabel → Option Nat} {lsize lsize' : WeakMem.AllocLabel → Nat}

/-- **The environment at more placed labels.** -/
theorem SRep.mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b) {val : Scc.IR.Operand → Option Nat}
    {s : SEnv} {env : TermRun.Env} (h : SRep lbl val s env) : SRep lbl' val s env := fun x t pls hx =>
  let ⟨ws, he, hw⟩ := h x t pls hx
  ⟨ws, he, WordsRep.mono_lbl hl hw⟩

/-- **A control placed in the slots at more placed labels.** -/
theorem SlotRepAt.mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b) {i : Expr → String → Nat → Option Nat}
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} {c : Ctl} (h : SlotRepAt i lbl rs sl c) :
    SlotRepAt i lbl' rs sl c :=
  let ⟨s, hs, ht, hb, hi⟩ := h
  ⟨s, SRep.mono_lbl hl hs, ht, hb, hi⟩

/-- **The source at the overflow abort at more placed labels.** -/
theorem AbSrcL.mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b) {rs : Scc.IR.Reg → Option Int}
    {lits : List (String × Scc.Lower.LitV)} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl}
    (h : AbSrcL lbl rs lits s sl c) :
    AbSrcL lbl' rs lits s sl c :=
  ⟨h.1, h.2.1, SRep.mono_lbl hl h.2.2.1, h.2.2.2⟩

/-! ## The walk's facts at larger sizes -/

/-- **The caller's facts against the walk at larger sizes** (the same
labels and memory). -/
theorem EnvQ.mono (hz : ∀ l, lsize l ≤ lsize' l) {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} {env : TermRun.Env} (h : EnvQ lits cs bufs lsize env) :
    EnvQ lits cs bufs lsize' env :=
  let ⟨hl, hs, L, sm, B, hb, hm⟩ := h
  ⟨hl, hs, L, sm, B, hb.mono (fun _ h => h) (fun _ h => h) fun l _ => hz l, hm⟩

/-- **The node invariant with buffers and slices at a larger level** (the
same labels `L`, memory `sm` and bound `B`). -/
theorem NJB.mono (hv : LvlLe lbl lsize lbl' lsize') {p : Prog} {rs : Scc.IR.Reg → Option Int}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
    {sm : WeakMem.Memory} {B : Nat} {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl}
    (h : NJB p lbl rs lits cs bufs L sm lsize B t s sl c) : NJB p lbl' rs lits cs bufs L sm lsize' B t s sl c :=
  let ⟨c', hr, hj, hl, hb, hm, hs⟩ := h
  ⟨c', hr, Spike.Lib.Form.NodeJE.mono_lbl hv.1 hj, hl, hb.mono (fun _ h => h) (fun _ h => h) fun l _ => hv.2 l,
    hm, hs⟩

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.lvlLe_upd' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.lvlLe_upd

/-- info: 'Spike.Lib.LowerNode.NJB.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.NJB.mono

/-- info: 'Spike.Lib.LowerNode.EnvQ.mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.EnvQ.mono
