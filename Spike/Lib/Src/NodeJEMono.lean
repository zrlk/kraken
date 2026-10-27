import Spike.Lib.FormE
import Scc.Sem.MemRel

/-!
**The node invariant at more placed labels** (ISA-neutral). Placing one
more label (`lbl'` agreeing with `lbl` wherever `lbl` places one) keeps
every word's representation (`MemRel.valRep_mono`, and a locative's base
and offset), so the node invariant up to the buffers' literal lengths
(`NodeJE`) holds at `lbl'`: a fresh label's continuation after a buffer
allocation, at the label map extended by the new label.

- `LocRep.mono_lbl`, `WordRep.mono_lbl`, `WordsRep.mono_lbl`: one word, one
  placement, a list;
- `SRepE.mono_lbl`, `NodeJE.mono_lbl`: the environment and the node.
-/

namespace Spike.Lib.Form

open CoreLang CoreTerm

variable {lbl lbl' : WeakMem.AllocLabel → Option Nat} {val : Scc.IR.Operand → Option Nat}

/-- **A locative's base and offset at more placed labels.** -/
theorem LocRep.mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b) {v : WeakMem.Val} {vb vo : Nat}
    (h : LocRep lbl v vb vo) : LocRep lbl' v vb vo := by
  cases v with
  | loc a tag => exact ⟨h.1, hl _ _ h.2.1, h.2.2⟩
  | undef => trivial
  | _ => exact h.elim

/-- **A word at its placement at more placed labels.** -/
theorem WordRep.mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b) {w : TermRun.Word} {pl : WordPl}
    (h : WordRep lbl val w pl) : WordRep lbl' val w pl := by
  cases pl with
  | one o =>
    obtain ⟨v, hv, hr⟩ := h
    exact ⟨v, hv, Scc.Sem.MemRel.valRep_mono hl hr⟩
  | loc b off =>
    obtain ⟨vb, vo, hb, ho, hr⟩ := h
    exact ⟨vb, vo, hb, ho, LocRep.mono_lbl hl hr⟩

/-- **Words at their placements at more placed labels.** -/
theorem WordsRep.mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b) :
    ∀ {ws : List TermRun.Word} {pls : List WordPl}, WordsRep lbl val ws pls → WordsRep lbl' val ws pls
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨WordRep.mono_lbl hl h1, WordsRep.mono_lbl hl h2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **The environment up to the erasure at more placed labels.** -/
theorem SRepE.mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b) {s : SEnv} {env : TermRun.Env}
    (h : SRepE lbl val s env) : SRepE lbl' val s env := fun x t pls hx =>
  let ⟨t', ws, he, ht, hw⟩ := h x t pls hx
  ⟨t', ws, he, ht, WordsRep.mono_lbl hl hw⟩

/-- **The node invariant up to the erasure at more placed labels.** -/
theorem NodeJE.mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b) {rs : Scc.IR.Reg → Option Int}
    {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : NodeJE lbl rs t s sl c) :
    NodeJE lbl' rs t s sl c :=
  ⟨h.1, h.2.1, SRepE.mono_lbl hl h.2.2⟩

end Spike.Lib.Form

/-- info: 'Spike.Lib.Form.WordsRep.mono_lbl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Form.WordsRep.mono_lbl

/-- info: 'Spike.Lib.Form.NodeJE.mono_lbl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Form.NodeJE.mono_lbl
