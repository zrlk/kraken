/-
**A user function's direct jumps go to its own labels** (x86-64): every
`jmp` or `jcc` to a label (`dirTgt`) in the items `emitFuncAt` emits for a
user function whose blocks have `lowerC2`'s shape and branch to its blocks
goes to a label of those items, a user run's label (`WcL`) none of the write
abort's (`abLabs`).

- `tgIn`, `tg_step`: items whose direct jump targets are among given
  labels, step by step;
- `emitInst_tg`, `emitTerm_tg`: `lowerC2`'s instructions jump to the
  overflow stub only, its terminators to their targets' labels only;
- `emitFunc_tg`: a function's items jump to `tgLabs` only;
- `userFunc_tgts`: the targets of a user function's items.
-/
import Spike.Lib.LowerX64.G1TgLabs
import Spike.Lib.LowerX64.G1TgEmit
import Spike.Lib.LowerX64.UserLabs
import Spike.Lib.LowerShapeC2Br

namespace Spike.Lib.LowerX64

open Kraken
open Scc.Emit.X64
open Spike.Lib.X64.AllocG (abLabs)
open Spike.Lib.LowerShape (InstC2 TermC2 BlockC2 termTgts)

/-! ## Items jumping to given labels -/

/-- **An item whose direct jump target, if any, is among `Ls`.** -/
def tgIn (Ls : List String) : Item → Bool
  | .d d => match dirTgt d with
    | some T => decide (T ∈ Ls)
    | none => true
  | _ => true

/-- A `jcc` to a label of `Ls` jumps to `Ls`. -/
theorem tgIn_jcc {Ls : List String} {cc : CondCode} {L : String} (h : L ∈ Ls) :
    tgIn Ls (.d (i64 (.jcc cc L))) = true := by
  simp [tgIn, dirTgt, i64, op, h]

/-- A `jmp` to a label of `Ls` jumps to `Ls`. -/
theorem tgIn_jmp {Ls : List String} {L : String} (h : L ∈ Ls) :
    tgIn Ls (.d (i64 (.jmp (rel L)))) = true := by
  simp [tgIn, dirTgt, i64, op, rel, h]

theorem freshL_tg (Ls : List String) (fn : String) : PreP (tgIn Ls) (freshL fn) :=
  PreP.of_out fun s a s' h => by cases h; rfl
theorem recordMap_tg (Ls : List String) (l : String) (st hp : List Int) : PreP (tgIn Ls) (recordMap l st hp) :=
  PreP.of_out fun s a s' h => by cases h; rfl
theorem slotOff_tg (Ls : List String) (fr : Frame) (r : Scc.IR.Reg) : PreP (tgIn Ls) (fr.slotOff r) := by
  unfold Frame.slotOff
  split
  · exact PreP.pure' _
  · exact PreP.throw' _
theorem slot_tg (Ls : List String) (fr : Frame) (r : Scc.IR.Reg) : PreP (tgIn Ls) (fr.slot r) := by
  unfold Frame.slot
  exact PreP.bind' (slotOff_tg Ls fr r) fun _ => PreP.pure' _

/-- One step of a `PreP (tgIn Ls)` proof of an emitter action. -/
macro "tg_step" : tactic => `(tactic| first
  | (with_reducible exact PreP.pure' _) | (with_reducible exact PreP.throw' _)
  | (with_reducible exact PreP.item' (tgIn_jcc (by assumption)))
  | (with_reducible exact PreP.item' (tgIn_jmp (by assumption)))
  | (with_reducible exact PreP.item' rfl)
  | (exact PreP.item' rfl)
  | (with_reducible exact PreP.get')
  | (with_reducible exact freshL_tg _ _) | (with_reducible exact recordMap_tg _ _ _ _)
  | (with_reducible exact slotOff_tg _ _ _) | (with_reducible exact slot_tg _ _ _)
  | (unfold ins) | (unfold lbl) | (unfold dir) | (unfold sysc) | (unfold ud2) | (unfold movFs)
  | (unfold ld) | (unfold st) | (unfold movRR) | (unfold movl) | (unfold zero32) | (unfold callSym)
  | (unfold jmpTo) | (unfold cmpAB) | (unfold loadArgs) | (unfold callArgs) | (unfold safepoint)
  | (unfold epilogue)
  | (with_reducible apply PreP.bind') | (with_reducible apply PreP.forIn') | (with_reducible apply PreP.mapM')
  | (intro _) | (split))

/-! ## The instructions, the terminators, the function -/

/-- **An instruction of `lowerC2`'s shape jumps to the overflow stub only**,
where it is a checked `+`. -/
theorem emitInst_tg {Ls : List String} (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) {i : Scc.IR.Inst}
    (hi : InstC2 i) (hov : ∀ d p q, i = .addChk d p q → labelOf fr.fn "ovf" ∈ Ls) :
    PreP (tgIn Ls) (emitInst fr sm i) := by
  cases hi
  case addChk d p q =>
    have h := hov d p q rfl
    simp only [emitInst]
    repeat tg_step
  all_goals simp only [emitInst, Spike.Lib.LowerShape.newBufCall, Spike.Lib.LowerShape.xchgLoad,
    Spike.Lib.LowerShape.xchgStore]
  all_goals repeat tg_step

/-- **A terminator of `lowerC2`'s shape jumps to its targets' labels only.** -/
theorem emitTerm_tg {Ls : List String} (fr : Frame) {t : Scc.IR.Term}
    (ht : TermC2 t) (hL : ∀ L ∈ termTgts t, labelOf fr.fn L ∈ Ls) :
    PreP (tgIn Ls) (emitTerm fr t) := by
  cases ht
  case ret ws =>
    simp only [emitTerm]
    repeat tg_step
  case br p q l1 l2 =>
    have h1 := hL l1 (by simp [termTgts])
    have h2 := hL l2 (by simp [termTgts])
    simp only [emitTerm]
    repeat tg_step


section
variable {f : Scc.IR.Func} {Ls : List String}
  (hblk : ∀ b ∈ f.blocks, BlockC2 b)
  (hov : ∀ b ∈ f.blocks, ∀ i ∈ b.insts, ∀ d p q, i = .addChk d p q → labelOf f.name "ovf" ∈ Ls)
  (hbl : ∀ b ∈ f.blocks, ∀ L ∈ termTgts b.term, labelOf f.name L ∈ Ls)

include hblk hov in
/-- An instruction of the blocks loop jumps to `Ls` only. -/
theorem emitInst_blk_tg (fr : Frame) (hfn : fr.fn = f.name)
    {ms : List (List (Option Scc.IR.StackMap.Entry))} {x : Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)}
    {y : Scc.IR.Inst × Option Scc.IR.StackMap.Entry} (hy : y ∈ x.1.insts.zip x.2) (hx : x ∈ f.blocks.zip ms) :
    PreP (tgIn Ls) (emitInst fr y.2 y.1) :=
  emitInst_tg fr y.2 ((hblk x.1 (List.of_mem_zip hx).1).1 y.1 (List.of_mem_zip hy).1)
    (fun d p q e => hfn ▸ hov x.1 (List.of_mem_zip hx).1 y.1 (List.of_mem_zip hy).1 d p q e)

include hblk hbl in
/-- A terminator of the blocks loop jumps to `Ls` only. -/
theorem emitTerm_blk_tg (fr : Frame) (hfn : fr.fn = f.name)
    {ms : List (List (Option Scc.IR.StackMap.Entry))} {x : Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)}
    (hx : x ∈ f.blocks.zip ms) : PreP (tgIn Ls) (emitTerm fr x.1.term) :=
  emitTerm_tg fr (hblk x.1 (List.of_mem_zip hx).1).2 (fun L hL => hfn ▸ hbl x.1 (List.of_mem_zip hx).1 L hL)

end

set_option hygiene false in
/-- A `PreP (tgIn Ls)` proof of `emitFunc`, step by step (reading the hypotheses `hblk`, `hov`, `hbl`). -/
macro "tg_fn_tac" : tactic => `(tactic| repeat (first
  | (exact emitInst_blk_tg hblk hov _ rfl ‹_› ‹_›)
  | (exact emitTerm_blk_tg hblk hbl _ rfl ‹_›)
  | (with_reducible apply PreP.forIn_mem)
  | tg_step | (dsimp only)))

section
variable (a : Scc.IR.Sym) (ar : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func) (Ls : List String)
  (hpar : ¬ f.params.length > Scc.IR.maxArgs)
  (hblk : ∀ b ∈ f.blocks, BlockC2 b)
  (hov : ∀ b ∈ f.blocks, ∀ i ∈ b.insts, ∀ d p q, i = .addChk d p q → labelOf f.name "ovf" ∈ Ls)
  (hbl : ∀ b ∈ f.blocks, ∀ L ∈ termTgts b.term, labelOf f.name L ∈ Ls)
include hpar hblk hov hbl

set_option linter.unusedSimpArgs false in
/-- `emitFunc` jumps to `Ls` only (growth `none`, stack check `false`). -/
theorem emitFunc_tg_none_false (hcs : f.checkStack = false) : PreP (tgIn Ls) (emitFunc a none ar f) := by
  unfold emitFunc
  simp only [hpar, hcs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  tg_fn_tac

set_option linter.unusedSimpArgs false in
/-- `emitFunc` jumps to `Ls` only (growth `none`, stack check `true`). -/
theorem emitFunc_tg_none_true (hcs : f.checkStack = true) (hstk : labelOf f.name "stk" ∈ Ls) :
    PreP (tgIn Ls) (emitFunc a none ar f) := by
  unfold emitFunc
  simp only [hpar, hcs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  tg_fn_tac

set_option linter.unusedSimpArgs false in
/-- `emitFunc` jumps to `Ls` only (growth `some`, stack check `false`). -/
theorem emitFunc_tg_some_false (gr : Scc.IR.Growth) (hcs : f.checkStack = false) :
    PreP (tgIn Ls) (emitFunc a (some gr) ar f) := by
  unfold emitFunc
  simp only [hpar, hcs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  tg_fn_tac

set_option linter.unusedSimpArgs false in
/-- `emitFunc` jumps to `Ls` only (growth `some`, stack check `true`). -/
theorem emitFunc_tg_some_true (gr : Scc.IR.Growth) (hcs : f.checkStack = true)
    (hstk : labelOf f.name "stk" ∈ Ls) (hchk : labelOf f.name "chk" ∈ Ls) :
    PreP (tgIn Ls) (emitFunc a (some gr) ar f) := by
  unfold emitFunc
  simp only [hpar, hcs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  tg_fn_tac

end

/-- Each label of `tgLabs` is a label of the function's (`labelOf f.name x`). -/
theorem tgLabs_labelOf {g} {f : Scc.IR.Func} {T : String} (h : T ∈ tgLabs g f) : ∃ x, T = labelOf f.name x := by
  unfold tgLabs at h
  simp only [List.mem_append, List.mem_map] at h
  rcases h with ((⟨b, -, rfl⟩ | h) | h) | h
  · exact ⟨_, rfl⟩
  all_goals (split at h <;> simp only [List.mem_singleton, List.not_mem_nil] at h)
  all_goals first | exact ⟨_, h⟩ | exact h.elim

/-- **`emitFunc` jumps to `tgLabs` only** (blocks of `lowerC2`'s shape whose
branches go to blocks of the function). -/
theorem emitFunc_tg (a g ar) (f : Scc.IR.Func) (hpar : ¬ f.params.length > Scc.IR.maxArgs)
    (hblk : ∀ b ∈ f.blocks, BlockC2 b)
    (hbr : ∀ b ∈ f.blocks, ∀ L ∈ termTgts b.term, ∃ b' ∈ f.blocks, b'.label = L) :
    PreP (tgIn (tgLabs g f)) (emitFunc a g ar f) := by
  have hov : ∀ b ∈ f.blocks, ∀ i ∈ b.insts, ∀ d p q, i = .addChk d p q →
      labelOf f.name "ovf" ∈ tgLabs g f := by
    intro b hb i hi d p q e
    subst e
    have hany : f.blocks.any (·.insts.any fun | .addChk .. => true | _ => false) = true :=
      List.any_eq_true.mpr ⟨b, hb, List.any_eq_true.mpr ⟨_, hi, rfl⟩⟩
    unfold tgLabs
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    split
    · exact List.mem_singleton_self _
    · exact absurd hany ‹_›
  have hbl : ∀ b ∈ f.blocks, ∀ L ∈ termTgts b.term, labelOf f.name L ∈ tgLabs g f := by
    intro b hb L hL
    obtain ⟨b', hb', rfl⟩ := hbr b hb L hL
    unfold tgLabs
    simp only [List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl ⟨b', hb', rfl⟩))
  cases g <;> cases hcs : f.checkStack
  · exact emitFunc_tg_none_false a ar f _ hpar hblk hov hbl hcs
  · exact emitFunc_tg_none_true a ar f _ hpar hblk hov hbl hcs (by unfold tgLabs; simp [hcs])
  · exact emitFunc_tg_some_false a ar f _ hpar hblk hov hbl _ hcs
  · exact emitFunc_tg_some_true a ar f _ hpar hblk hov hbl _ hcs (by unfold tgLabs; simp [hcs])
      (by unfold tgLabs; simp [hcs])

/-- **A user function's direct jumps go to labels of its own code**, each a
user run's label (`WcL`) none of the write abort's. -/
theorem userFunc_tgts {p : Scc.IR.Program} {areas} {f : Scc.IR.Func} {n : Nat} {r}
    (h : Scc.Emit.X64.emitFuncAt p areas f n = .ok r) (g : String) (hname : f.name = Scc.Lower.Names.user g)
    (hblk : ∀ b ∈ f.blocks, Spike.Lib.LowerShape.BlockC2 b)
    (hbr : ∀ b ∈ f.blocks, ∀ L ∈ Spike.Lib.LowerShape.termTgts b.term, ∃ b' ∈ f.blocks, b'.label = L) :
    ∀ d ∈ dOf r.1, ∀ T, dirTgt d = some T → WcL T ∧ T ∉ abLabs ∧ Directive.label T ∈ dOf r.1 := by
  unfold emitFuncAt at h
  cases hr : (emitFunc p.abortFn p.growth areas f).run {} with
  | error e => rw [hr] at h; cases h
  | ok v =>
    obtain ⟨⟨⟩, s⟩ := v
    rw [hr] at h
    cases h
    have h' : emitFunc p.abortFn p.growth areas f {} = .ok ((), s) := hr
    have hpar : ¬ f.params.length > Scc.IR.maxArgs := by
      intro hpar
      unfold emitFunc at h'
      simp only [hpar, ite_true] at h'
      obtain ⟨_, _, h1, -⟩ := bind_inv_E h'
      cases h1
    obtain ⟨c, hc, hp⟩ := (emitFunc_tg p.abortFn p.growth areas f hpar hblk hbr).out _ _ _ h'
    simp only [List.append_nil] at hc
    intro d hd T hT
    obtain ⟨it, hit, e⟩ := List.mem_filterMap.mp hd
    cases it with
    | d x =>
      simp only [Option.some.injEq] at e
      subst e
      have hin := hp _ (by rw [hc] at hit; exact List.mem_reverse.mp hit)
      simp only [tgIn, hT, decide_eq_true_eq] at hin
      obtain ⟨y, rfl⟩ := tgLabs_labelOf hin
      rw [hname] at hin ⊢
      obtain ⟨hab, hw⟩ := labelOf_user_usr g y
      refine ⟨hw, hab, List.mem_filterMap.mpr ⟨Item.d (.label _), List.mem_reverse.mpr ?_, rfl⟩⟩
      have := emitFunc_tgLabs h' _ (hname ▸ hin)
      rw [hname] at this
      exact this
    | _ => cases e

/-- info: 'Spike.Lib.LowerX64.userFunc_tgts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms userFunc_tgts

end Spike.Lib.LowerX64
