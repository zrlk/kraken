/-
**The labels of an `Accepted2` function's code** (x86-64): the emitter's
code of each `InstC2` instruction and `TermC2` terminator
(`Spike/Lib/LowerShapeC2Shape.lean`), and so of a function of such blocks,
keeps every label of the output but the last followed by a non-label; a
function's code ends with a non-label.

A Hoare triple over the emitter (`HT P Q x`) reads the output's directives
(`dOf`, the last first): `LfA` (every label but the last followed by a
non-label, `labFollowed` of the directives in order) and `LfB` (`LfA`, the
last directive no label). An instruction's code takes `LfA` to `LfA` (its
first directive is no label, though a call may end with its safepoint's
label), a terminator's `LfA` to `LfB` (it ends with `ret` or `jmp`); a
label needs `LfB` before it.

- `HT`, `LfA`, `LfB` and their rules (`HT.bind'`, `HT.forIn'`,
  `HT.forIn_mem`, the primitive actions);
- `inst_lf`, `term_lf`: an instruction's and a terminator's code;
- `emitFunc_lf`: a function's code, from `LfB` to `LfB`;
- `emitFunc_first`, `emitFuncAt_lf`: a function's directives are its
  name's label, then directives passing `labFollowed` and ending with a
  non-label (the label-follow half of `UserPart`).
-/
import Spike.Lib.LowerX64.G1TgEmit
import Spike.Lib.LowerShapeC2Br

namespace Spike.Lib.LowerX64

open Kraken
open Scc.Emit.X64
open Spike.Lib.LowerShape (InstC2 TermC2 BlockC2)

/-! ## Hoare triples on the output's directives -/

/-- **A Hoare triple on the output's directives** (the last first): from a
state whose output's directives satisfy `P`, a successful run leaves an
output whose directives satisfy `Q`. -/
structure HT (P Q : List Directive → Prop) {α : Type} (x : E α) : Prop where
  run : ∀ (s : S) (a : α) (s' : S), x s = .ok (a, s') → P (dOf s.out) → Q (dOf s'.out)

/-- **Every label but the last is followed by a non-label** (the
directives the last first). -/
def LfA (R : List Directive) : Prop := labFollowed R.reverse = true

/-- **`LfA` and the last directive no label.** -/
def LfB (R : List Directive) : Prop := LfA R ∧ ∀ d, R.head? = some d → nLab d = true

theorem LfB.toA {R : List Directive} (h : LfB R) : LfA R := h.1

theorem lfA_nil : LfA [] := rfl
theorem lfB_nil : LfB [] := ⟨rfl, fun _ h => by cases h⟩

/-- A non-label after `LfA`: `LfB`. -/
theorem lfB_cons {R : List Directive} {d : Directive} (h : LfA R) (hd : nLab d = true) : LfB (d :: R) := by
  refine ⟨?_, fun d' e => by cases e; exact hd⟩
  unfold LfA
  rw [List.reverse_cons]
  exact labFollowed_append h (labFollowed_singleton d) (fun a _ b hb => by cases hb; simp [hd])

/-- A label after `LfB`: `LfA`. -/
theorem lfA_label {R : List Directive} {l : Label} (h : LfB R) : LfA (.label l :: R) := by
  unfold LfA
  rw [List.reverse_cons]
  refine labFollowed_append h.1 (labFollowed_singleton _) (fun a ha b _ => ?_)
  rw [List.getLast?_reverse] at ha
  simp [h.2 a ha]

namespace HT

variable {P Q R : List Directive → Prop}

theorem bind' {α β : Type} {x : E α} {f : α → E β} (hx : HT P Q x) (hf : ∀ a, HT Q R (f a)) :
    HT P R (x >>= f) := by
  refine ⟨fun s b s' h hp => ?_⟩
  obtain ⟨a, s1, h1, h2⟩ := bind_inv_E h
  exact (hf a).run s1 b s' h2 (hx.run s a s1 h1 hp)

theorem throw' {α : Type} (e : String) : HT P Q (throw e : E α) := ⟨fun s a s' h _ => by cases h⟩

/-- A failing action before a continuation. -/
theorem throw_bind {α β : Type} (e : String) (f : α → E β) : HT P Q ((throw e : E α) >>= f) :=
  ⟨fun s a s' h _ => by cases h⟩

/-- A failing action, its postcondition its precondition (fixing a
postcondition left open by `bind'`). -/
theorem throw_self {α : Type} (e : String) : HT P P (throw e : E α) := throw' e

/-- Actions leaving the output's directives alone. -/
theorem of_dOf {α : Type} {x : E α} (h : ∀ s a s', x s = .ok (a, s') → dOf s'.out = dOf s.out)
    (hPQ : ∀ R, P R → Q R) : HT P Q x :=
  ⟨fun s a s' e hp => by rw [h s a s' e]; exact hPQ _ hp⟩

theorem forIn' {β σ : Type} (f : β → σ → E (ForInStep σ)) (hf : ∀ b st, HT P P (f b st)) :
    ∀ (l : List β) (init : σ), HT P P (forIn l init f)
  | [], init => of_dOf (fun s a s' h => by simp at h; cases h; rfl) (fun _ h => h)
  | b :: l, init => by
    rw [List.forIn_cons]
    refine bind' (hf b init) fun r => ?_
    cases r with
    | done st => exact of_dOf (fun s a s' h => by cases h; rfl) (fun _ h => h)
    | yield st => exact forIn' f hf l st

/-- A loop whose body keeps `P` at each element of the list. -/
theorem forIn_mem {β σ : Type} (f : β → σ → E (ForInStep σ)) :
    ∀ (l : List β), (∀ b ∈ l, ∀ st, HT P P (f b st)) → ∀ (init : σ), HT P P (forIn l init f)
  | [], _, init => of_dOf (fun s a s' h => by simp at h; cases h; rfl) (fun _ h => h)
  | b :: l, hf, init => by
    rw [List.forIn_cons]
    refine bind' (hf b (List.mem_cons_self ..) init) fun r => ?_
    cases r with
    | done st => exact of_dOf (fun s a s' h => by cases h; rfl) (fun _ h => h)
    | yield st => exact forIn_mem f l (fun b' hb' => hf b' (List.mem_cons_of_mem _ hb')) st

end HT

/-! ### The primitive actions -/

/-- An action leaving the output's directives alone. -/
def Neu {α : Type} (x : E α) : Prop := ∀ s a s', x s = .ok (a, s') → dOf s'.out = dOf s.out

theorem Neu.AA {α : Type} {x : E α} (h : Neu x) : HT LfA LfA x := HT.of_dOf h fun _ h => h
theorem Neu.BB {α : Type} {x : E α} (h : Neu x) : HT LfB LfB x := HT.of_dOf h fun _ h => h
theorem Neu.BA {α : Type} {x : E α} (h : Neu x) : HT LfB LfA x := HT.of_dOf h fun _ h => h.1

theorem neu_pure {α : Type} (a : α) : Neu (pure a : E α) := fun s b s' h => by cases h; rfl
theorem neu_get : Neu (get : E S) := fun s b s' h => by cases h; rfl
theorem neu_freshL (fn : String) : Neu (freshL fn) := fun s b s' h => by cases h; rfl
theorem neu_recordMap (l : String) (st hp : List Int) : Neu (recordMap l st hp) := fun s b s' h => by cases h; rfl
theorem neu_slotOff (fr : Frame) (r : Scc.IR.Reg) : Neu (fr.slotOff r) := by
  intro s b s' h
  unfold Frame.slotOff at h
  cases hf : List.find? (fun x => x.fst == r) fr.slots with
  | none => rw [hf] at h; cases h
  | some v => obtain ⟨_, k⟩ := v; rw [hf] at h; cases h; rfl
theorem neu_slot (fr : Frame) (r : Scc.IR.Reg) : Neu (fr.slot r) := by
  intro s b s' h
  unfold Frame.slot at h
  obtain ⟨_, s1, h1, h2⟩ := bind_inv_E h
  cases h2
  exact neu_slotOff fr r _ _ _ h1
theorem neu_mapM_slotOff (fr : Frame) : ∀ (l : List Scc.IR.Reg), Neu (l.mapM fr.slotOff)
  | [] => fun s b s' h => by simp at h; cases h; rfl
  | r :: l => by
    intro s b s' h
    rw [List.mapM_cons] at h
    obtain ⟨_, s1, h1, h⟩ := bind_inv_E h
    obtain ⟨_, s2, h2, h⟩ := bind_inv_E h
    cases h
    rw [neu_mapM_slotOff fr l _ _ _ h2, neu_slotOff fr r _ _ _ h1]
theorem neu_dir (s0 : String) : Neu (item (.dir s0)) := fun s b s' h => by cases h; rfl
theorem neu_comment (s0 : String) : Neu (item (.comment s0)) := fun s b s' h => by cases h; rfl
theorem neu_blank : Neu (item .blank) := fun s b s' h => by cases h; rfl

/-- A non-label directive item: `LfB` after `LfA`. -/
theorem ins_AB {d : Directive} (hd : nLab d = true) : HT LfA LfB (item (.d d)) :=
  ⟨fun s a s' h hp => by cases h; exact lfB_cons hp hd⟩
theorem ins_BB {d : Directive} (hd : nLab d = true) : HT LfB LfB (item (.d d)) :=
  ⟨fun s a s' h hp => by cases h; exact lfB_cons hp.1 hd⟩
theorem ins_AA {d : Directive} (hd : nLab d = true) : HT LfA LfA (item (.d d)) :=
  ⟨fun s a s' h hp => by cases h; exact (lfB_cons hp hd).1⟩
theorem ins_BA {d : Directive} (hd : nLab d = true) : HT LfB LfA (item (.d d)) :=
  ⟨fun s a s' h hp => by cases h; exact (lfB_cons hp.1 hd).1⟩

/-- A label item: `LfA` after `LfB`. -/
theorem lbl_BA (l : Label) : HT LfB LfA (item (.d (.label l))) :=
  ⟨fun s a s' h hp => by cases h; exact lfA_label hp⟩

/-- One step of an `HT` proof of an emitter action over `LfA`/`LfB`, but
for loops. -/
macro "ht_step0" : tactic => `(tactic| first
  | (with_reducible exact lbl_BA _)
  | (with_reducible exact ins_AB rfl) | (with_reducible exact ins_BB rfl)
  | (with_reducible exact ins_AA rfl) | (with_reducible exact ins_BA rfl)
  | (exact HT.throw_bind _ _) | (exact HT.throw_self _) | (refine ⟨fun _ _ _ h _ => ?_⟩; cases h; done)
  | (with_reducible exact Neu.AA (neu_pure _)) | (with_reducible exact Neu.BB (neu_pure _))
  | (with_reducible exact Neu.BA (neu_pure _))
  | (with_reducible exact Neu.AA neu_get) | (with_reducible exact Neu.BB neu_get)
  | (with_reducible exact Neu.AA (neu_freshL _)) | (with_reducible exact Neu.BB (neu_freshL _))
  | (with_reducible exact Neu.AA (neu_recordMap _ _ _)) | (with_reducible exact Neu.BB (neu_recordMap _ _ _))
  | (with_reducible exact Neu.AA (neu_slotOff _ _)) | (with_reducible exact Neu.BB (neu_slotOff _ _))
  | (with_reducible exact Neu.AA (neu_slot _ _)) | (with_reducible exact Neu.BB (neu_slot _ _))
  | (with_reducible exact Neu.AA (neu_mapM_slotOff _ _)) | (with_reducible exact Neu.BB (neu_mapM_slotOff _ _))
  | (with_reducible exact Neu.AA (neu_dir _)) | (with_reducible exact Neu.BB (neu_dir _))
  | (with_reducible exact Neu.AA (neu_comment _)) | (with_reducible exact Neu.BB (neu_comment _))
  | (with_reducible exact Neu.AA neu_blank) | (with_reducible exact Neu.BB neu_blank)
  | (unfold ins) | (unfold lbl) | (unfold dir) | (unfold sysc) | (unfold ud2) | (unfold movFs)
  | (unfold ld) | (unfold st) | (unfold movRR) | (unfold movl) | (unfold zero32) | (unfold callSym)
  | (unfold jmpTo) | (unfold cmpAB) | (unfold loadArgs) | (unfold callArgs) | (unfold safepoint)
  | (unfold epilogue)
  | (with_reducible apply HT.bind')
  | (intro _) | (dsimp only) | (split))

/-- One step of an `HT` proof of an emitter action over `LfA`/`LfB`. -/
macro "ht_step" : tactic => `(tactic| first | ht_step0 | (with_reducible apply HT.forIn'))

/-! ## An instruction's and a terminator's code -/

/-- The code of each `InstC2` instruction keeps `LfA`. -/
macro "inst_lf_tac" : tactic => `(tactic|
  (simp only [emitInst, Spike.Lib.LowerShape.newBufCall, Spike.Lib.LowerShape.xchgLoad,
      Spike.Lib.LowerShape.xchgStore]; repeat ht_step))

theorem inst_lf_addChk (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg) (p q : Scc.IR.Operand) :
    HT LfA LfA (emitInst fr sm (.addChk d p q)) := by inst_lf_tac
theorem inst_lf_subSat (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg) (p q : Scc.IR.Operand) :
    HT LfA LfA (emitInst fr sm (.subSat d p q)) := by inst_lf_tac
theorem inst_lf_call (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg) (g : String) (w : Scc.IR.Operand) :
    HT LfA LfA (emitInst fr sm (.call [d] (Scc.Lower.Names.user g) [w])) := by inst_lf_tac
theorem inst_lf_newBuf (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (p : Scc.IR.Reg) (h : Nat) (kv : UInt64) (u : Scc.IR.Operand) :
    HT LfA LfA (emitInst fr sm (Spike.Lib.LowerShape.newBufCall p h kv u)) := by inst_lf_tac
theorem inst_lf_load (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg) (a : Scc.IR.Addr) :
    HT LfA LfA (emitInst fr sm (Spike.Lib.LowerShape.xchgLoad d a)) := by inst_lf_tac
theorem inst_lf_store (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (a : Scc.IR.Addr) (w : Scc.IR.Operand) :
    HT LfA LfA (emitInst fr sm (Spike.Lib.LowerShape.xchgStore a w)) := by inst_lf_tac
theorem inst_lf_ext (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg) (o : Scc.IR.Operand) :
    HT LfA LfA (emitInst fr sm (.ext false .w32 d o)) := by inst_lf_tac
theorem inst_lf_add (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg) (b : Scc.IR.Operand) (s : Scc.IR.Reg) :
    HT LfA LfA (emitInst fr sm (.bin .add d b (.reg s))) := by inst_lf_tac
theorem inst_lf_mul8 (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg) (m : Scc.IR.Operand) :
    HT LfA LfA (emitInst fr sm (.bin .mul d m (Scc.Lower.imm 8))) := by inst_lf_tac
theorem inst_lf_minU (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg) (c : Scc.IR.Operand) (s : Scc.IR.Reg) :
    HT LfA LfA (emitInst fr sm (.select .ult d c (.reg s) c (.reg s))) := by inst_lf_tac
theorem inst_lf_print (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (a0 a1 : Scc.IR.Operand) :
    HT LfA LfA (emitInst fr sm (.call [] Scc.Lower.Names.print [a0, a1])) := by inst_lf_tac

/-- **An `Accepted2` instruction's code keeps `LfA`**: it starts with a
non-label (and may end with a safepoint's label). -/
theorem inst_lf {fr : Frame} {sm : Option Scc.IR.StackMap.Entry} {i : Scc.IR.Inst} (hi : InstC2 i) :
    HT LfA LfA (emitInst fr sm i) := by
  cases hi
  · exact inst_lf_addChk ..
  · exact inst_lf_subSat ..
  · exact inst_lf_call ..
  · exact inst_lf_newBuf ..
  · exact inst_lf_load ..
  · exact inst_lf_store ..
  · exact inst_lf_ext ..
  · exact inst_lf_add ..
  · exact inst_lf_mul8 ..
  · exact inst_lf_minU ..
  · exact inst_lf_print ..

/-- **An `Accepted2` terminator's code takes `LfA` to `LfB`**: it starts
with a non-label and ends with `ret` or `jmp`. -/
theorem term_lf {fr : Frame} {t : Scc.IR.Term} (ht : TermC2 t) : HT LfA LfB (emitTerm fr t) := by
  cases ht <;> simp only [emitTerm] <;> repeat ht_step

/-! ## A function's code -/

/-- `emitFunc`'s code takes `LfB` to `LfB` (growth `none`, stack check `false`). -/
theorem emitFunc_lf_none_false (a : Scc.IR.Sym) (ar : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func)
    (hcs : f.checkStack = false) (hblk : ∀ b ∈ f.blocks, BlockC2 b) : HT LfB LfB (emitFunc a none ar f) := by
  unfold emitFunc
  by_cases hpar : f.params.length > Scc.IR.maxArgs
  · simp only [hpar, ite_true]; exact HT.throw_bind _ _
  simp only [hpar, hcs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  repeat (first
    | ht_step0
    | (apply inst_lf; apply (hblk _ (List.of_mem_zip ‹(_, _) ∈ f.blocks.zip _›).1).1
       exact (List.of_mem_zip ‹(_, _) ∈ List.zip _ _›).1)
    | (apply term_lf; exact (hblk _ (List.of_mem_zip ‹(_, _) ∈ f.blocks.zip _›).1).2)
    | (apply HT.forIn_mem; intro ⟨_, _⟩ _ _)
    | (apply HT.forIn_mem; intro _ _ _))

/-- `emitFunc`'s code takes `LfB` to `LfB` (growth `none`, stack check `true`). -/
theorem emitFunc_lf_none_true (a : Scc.IR.Sym) (ar : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func)
    (hcs : f.checkStack = true) (hblk : ∀ b ∈ f.blocks, BlockC2 b) : HT LfB LfB (emitFunc a none ar f) := by
  unfold emitFunc
  by_cases hpar : f.params.length > Scc.IR.maxArgs
  · simp only [hpar, ite_true]; exact HT.throw_bind _ _
  simp only [hpar, hcs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  repeat (first
    | ht_step0
    | (apply inst_lf; apply (hblk _ (List.of_mem_zip ‹(_, _) ∈ f.blocks.zip _›).1).1
       exact (List.of_mem_zip ‹(_, _) ∈ List.zip _ _›).1)
    | (apply term_lf; exact (hblk _ (List.of_mem_zip ‹(_, _) ∈ f.blocks.zip _›).1).2)
    | (apply HT.forIn_mem; intro ⟨_, _⟩ _ _)
    | (apply HT.forIn_mem; intro _ _ _))

/-- `emitFunc`'s code takes `LfB` to `LfB` (growth `some`, stack check `false`). -/
theorem emitFunc_lf_some_false (a : Scc.IR.Sym) (gr : Scc.IR.Growth) (ar : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func)
    (hcs : f.checkStack = false) (hblk : ∀ b ∈ f.blocks, BlockC2 b) : HT LfB LfB (emitFunc a (some gr) ar f) := by
  unfold emitFunc
  by_cases hpar : f.params.length > Scc.IR.maxArgs
  · simp only [hpar, ite_true]; exact HT.throw_bind _ _
  simp only [hpar, hcs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  repeat (first
    | ht_step0
    | (apply inst_lf; apply (hblk _ (List.of_mem_zip ‹(_, _) ∈ f.blocks.zip _›).1).1
       exact (List.of_mem_zip ‹(_, _) ∈ List.zip _ _›).1)
    | (apply term_lf; exact (hblk _ (List.of_mem_zip ‹(_, _) ∈ f.blocks.zip _›).1).2)
    | (apply HT.forIn_mem; intro ⟨_, _⟩ _ _)
    | (apply HT.forIn_mem; intro _ _ _))

/-- `emitFunc`'s code takes `LfB` to `LfB` (growth `some`, stack check `true`). -/
theorem emitFunc_lf_some_true (a : Scc.IR.Sym) (gr : Scc.IR.Growth) (ar : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func)
    (hcs : f.checkStack = true) (hblk : ∀ b ∈ f.blocks, BlockC2 b) : HT LfB LfB (emitFunc a (some gr) ar f) := by
  unfold emitFunc
  by_cases hpar : f.params.length > Scc.IR.maxArgs
  · simp only [hpar, ite_true]; exact HT.throw_bind _ _
  simp only [hpar, hcs, Option.isSome, ↓reduceIte]
  repeat (first
    | ht_step0
    | (apply inst_lf; apply (hblk _ (List.of_mem_zip ‹(_, _) ∈ f.blocks.zip _›).1).1
       exact (List.of_mem_zip ‹(_, _) ∈ List.zip _ _›).1)
    | (apply term_lf; exact (hblk _ (List.of_mem_zip ‹(_, _) ∈ f.blocks.zip _›).1).2)
    | (apply HT.forIn_mem; intro ⟨_, _⟩ _ _)
    | (apply HT.forIn_mem; intro _ _ _))

/-- **A function's code of `Accepted2` blocks takes `LfB` to `LfB`**:
every label but the last is followed by a non-label, and the code ends with
a non-label (`ret`, `jmp` or `ud2`). -/
theorem emitFunc_lf (a : Scc.IR.Sym) (g : Option Scc.IR.Growth) (ar : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func)
    (hblk : ∀ b ∈ f.blocks, BlockC2 b) : HT LfB LfB (emitFunc a g ar f) := by
  cases g <;> cases hcs : f.checkStack
  · exact emitFunc_lf_none_false a ar f hcs hblk
  · exact emitFunc_lf_none_true a ar f hcs hblk
  · exact emitFunc_lf_some_false a _ ar f hcs hblk
  · exact emitFunc_lf_some_true a _ ar f hcs hblk

/-- A bind of `E` whose continuation appends `P` items. -/
theorem PreP.out_bind {P : Item → Bool} {α β : Type} {x : E α} {f : α → E β} (hf : ∀ a, PreP P (f a))
    {s s' : S} {b : β} (h : (x >>= f) s = .ok (b, s')) :
    ∃ a s1 c, x s = .ok (a, s1) ∧ s'.out = c ++ s1.out := by
  obtain ⟨a, s1, h1, h2⟩ := bind_inv_E h
  obtain ⟨c, hc, -⟩ := (hf a).out _ _ _ h2
  exact ⟨a, s1, c, h1, hc⟩

/-- **A function's first directive is its name's label** (from an output
with no directive). -/
theorem emitFunc_first {a g ar} {f : Scc.IR.Func} {s s' : S} {u : Unit}
    (h : emitFunc a g ar f s = .ok (u, s')) (hs : dOf s.out = []) :
    ∃ c, dOf s'.out = c ++ [.label f.name] := by
  unfold emitFunc at h
  split at h
  · obtain ⟨_, _, h1, -⟩ := bind_inv_E h
    cases h1
  · obtain ⟨_, s1, h1, h⟩ := bind_inv_E h
    obtain ⟨_, s2, h2, h⟩ := bind_inv_E h
    obtain ⟨_, s3, h3, h⟩ := bind_inv_E h
    obtain ⟨_, s4, c, h4, hc⟩ := PreP.out_bind (P := textN) (fun _ => by repeat prep_fn_step) h
    cases h1; cases h2; cases h3; cases h4
    refine ⟨dOf c, ?_⟩
    rw [hc]
    simp only [dOf, List.filterMap_append, List.filterMap_cons] at hs ⊢
    rw [hs]

/-- The tail of a list passing `labFollowed` passes. -/
theorem labFollowed_tail : ∀ {d : Directive} {ds : List Directive}, labFollowed (d :: ds) = true →
    labFollowed ds = true
  | _, [], _ => rfl
  | _, _ :: _, h => by
    rw [labFollowed_cons_cons, Bool.and_eq_true] at h
    exact h.2

/-- **A function's directives** (`emitFuncAt`, every block of `Accepted2`
shape): its name's label, then directives in which every label is
followed by a non-label, ending with a non-label. -/
theorem emitFuncAt_lf {p : Scc.IR.Program} {areas} {f : Scc.IR.Func} {n : Nat} {r}
    (h : emitFuncAt p areas f n = .ok r) (hblk : ∀ b ∈ f.blocks, BlockC2 b) :
    ∃ P', dOf r.1 = .label f.name :: P' ∧ labFollowed P' = true ∧
      ∀ d, P'.getLast? = some d → nLab d = true := by
  unfold emitFuncAt at h
  cases hr : (emitFunc p.abortFn p.growth areas f).run {} with
  | error e => rw [hr] at h; cases h
  | ok v =>
    obtain ⟨⟨⟩, s⟩ := v
    rw [hr] at h
    cases h
    have h' : emitFunc p.abortFn p.growth areas f {} = .ok ((), s) := hr
    have hlf := (emitFunc_lf p.abortFn p.growth areas f hblk).run _ _ _ h' lfB_nil
    obtain ⟨c, hc⟩ := emitFunc_first h' rfl
    have hrev : dOf s.out.reverse = (dOf s.out).reverse := by
      simp only [dOf, List.filterMap_reverse]
    have hd : dOf s.out.reverse = .label f.name :: c.reverse := by
      rw [hrev, hc, List.reverse_append]; rfl
    refine ⟨c.reverse, hd, ?_, fun d hd' => ?_⟩
    · have h1 := hlf.1
      unfold LfA at h1
      rw [← hrev, hd] at h1
      exact labFollowed_tail h1
    · apply hlf.2 d
      rw [← List.getLast?_reverse, ← hrev, hd]
      rw [List.getLast?_cons, hd']
      rfl

/-- info: 'Spike.Lib.LowerX64.emitFuncAt_lf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms emitFuncAt_lf

end Spike.Lib.LowerX64
