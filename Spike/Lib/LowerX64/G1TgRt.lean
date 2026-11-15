/-
**The runtime's functions place no user function's label** (x86-64): every
label scc's x86-64 emitter places for a function `f` (`emitFunc`) is `f`'s
name, a local label `.L{f.name}…` (`labelOf`, `childL`, `freshL`), or a
global label one of `f`'s instructions names (`instLabs`: a system call's
trap label, a site's label). The runtime's functions and their instructions'
labels are `scc_rt_` names (`rtFuncs_names`), so none of their labels
begins `.Lwc_` (`WcL`).

- `labP`, `labP_mono`, `labP_lbl`, `labP_mem`: the items whose labels have a
  property;
- `PreP.mono`, `PreP.bindR`, `PreP.forInM`: `PreP` weakened, through a bind
  whose first action's results have a property, through a loop whose body
  holds at the list's members;
- `emitInst_labs`, `emitTerm_labs`, `emitFunc_labs`, `emitFuncAt_labs`: the
  labels of an instruction's, a terminator's and a function's code;
- `not_wcL_append`, `rtFunc_noWcL`: a runtime function's code places no
  `WcL` label.
-/
import Spike.Lib.LowerX64.EmitLabels
import Spike.Lib.LowerX64.UserAbC
import Spike.Lib.G1TgRtLabs

namespace Spike.Lib.LowerX64

open Scc.Emit.X64
open Spike.Lib.RtLabs (instLabs RtName FnRt rtFuncs_names)

/-! ## Items whose labels have a property -/

/-- **An item whose label (if it is one) has `Q`.** -/
noncomputable def labP (Q : String → Prop) : Item → Bool
  | .d (.label L) => @decide (Q L) (Classical.propDecidable _)
  | _ => true

/-- `labP` along an implication. -/
theorem labP_mono {Q Q' : String → Prop} (h : ∀ L, Q L → Q' L) : ∀ it, labP Q it = true → labP Q' it = true
  | .d (.label L), hit => @decide_eq_true _ (Classical.propDecidable _)
      (h L (@of_decide_eq_true _ (Classical.propDecidable _) hit))
  | .d (.instr _), _ => rfl
  | .d (.byteArray _), _ => rfl
  | .comment _, _ => rfl
  | .blank, _ => rfl
  | .raw _, _ => rfl
  | .dir _, _ => rfl

/-- A label with `Q`. -/
theorem labP_lbl {Q : String → Prop} {L : String} (h : Q L) : PreP (labP Q) (lbl L) :=
  PreP.item' (@decide_eq_true _ (Classical.propDecidable _) h)

/-- The labels of items with `labP Q` have `Q`. -/
theorem labP_mem {Q : String → Prop} {items : List Item} (h : ∀ it ∈ items, labP Q it = true) {L : String}
    (hL : Directive.label L ∈ dOf items) : Q L := by
  obtain ⟨it, hit, he⟩ := List.mem_filterMap.mp hL
  cases it with
  | d x =>
    simp only [Option.some.injEq] at he
    subst he
    exact @of_decide_eq_true _ (Classical.propDecidable _) (h _ hit)
  | _ => simp at he

/-! ## `PreP` combinators -/

/-- `PreP` along an implication. -/
theorem PreP.mono {P P' : Item → Bool} {α : Type} {x : E α} (h : ∀ it, P it = true → P' it = true)
    (hx : PreP P x) : PreP P' x :=
  ⟨fun s a s' e => let ⟨c, hc, hp⟩ := hx.out s a s' e; ⟨c, hc, fun it hi => h it (hp it hi)⟩⟩

/-- `PreP` of a bind whose first action's results have `R`, the rest `PreP`
at those. -/
theorem PreP.bindR {P : Item → Bool} {α β : Type} {x : E α} {f : α → E β} {R : α → Prop} (hx : PreP P x)
    (hr : ∀ s a s', x s = .ok (a, s') → R a) (hf : ∀ a, R a → PreP P (f a)) : PreP P (x >>= f) := by
  refine ⟨fun s b s' h => ?_⟩
  obtain ⟨a, s1, h1, h2⟩ := bind_inv_E h
  obtain ⟨c1, e1, p1⟩ := hx.out s a s1 h1
  obtain ⟨c2, e2, p2⟩ := (hf a (hr s a s1 h1)).out s1 b s' h2
  refine ⟨c2 ++ c1, by rw [e2, e1, List.append_assoc], fun it hi => ?_⟩
  rcases List.mem_append.mp hi with hi | hi
  · exact p2 it hi
  · exact p1 it hi

/-- `PreP` of a loop whose body is `PreP` at the list's members. -/
theorem PreP.forInM {P : Item → Bool} {β σ : Type} (f : β → σ → E (ForInStep σ)) :
    ∀ (l : List β), (∀ b ∈ l, ∀ st, PreP P (f b st)) → ∀ init : σ, PreP P (forIn l init f)
  | [], _, init => by simpa using PreP.pure' (P := P) init
  | b :: l, hf, init => by
    rw [List.forIn_cons]
    refine PreP.bind' (hf b (List.mem_cons_self ..) init) fun r => ?_
    cases r with
    | done st => exact PreP.pure' st
    | yield st => exact PreP.forInM f l (fun b' hb' => hf b' (List.mem_cons_of_mem _ hb')) st

/-! ## The emitter's actions -/

theorem freshL_anyP {P : Item → Bool} (fn : String) : PreP P (freshL fn) :=
  PreP.of_out fun s a s' h => by cases h; rfl
theorem recordMap_anyP {P : Item → Bool} (l : String) (st hp : List Int) : PreP P (recordMap l st hp) :=
  PreP.of_out fun s a s' h => by cases h; rfl
theorem slotOff_anyP {P : Item → Bool} (fr : Frame) (r : Scc.IR.Reg) : PreP P (fr.slotOff r) := by
  unfold Frame.slotOff
  split
  · exact PreP.pure' _
  · exact PreP.throw' _
theorem slot_anyP {P : Item → Bool} (fr : Frame) (r : Scc.IR.Reg) : PreP P (fr.slot r) := by
  unfold Frame.slot
  exact PreP.bind' (slotOff_anyP fr r) fun _ => PreP.pure' _

/-- `freshL fn`'s label is local to `fn`. -/
theorem freshL_res {fn : String} {s : S} {a : String} {s' : S} (h : freshL fn s = .ok (a, s')) :
    ∃ t, a = ".L" ++ fn ++ t := by
  cases h
  exact ⟨".x" ++ toString s.next, by simp only [String.append_assoc]; rfl⟩

/-- `labelOf fn l` is local to `fn`. -/
theorem labelOf_pre (fn : String) (l : Scc.IR.Label) : ∃ t, labelOf fn l = ".L" ++ fn ++ t :=
  ⟨"." ++ l, by simp only [labelOf, String.append_assoc]; rfl⟩

/-- An instruction has every `labP`. -/
theorem labP_ins {Q : String → Prop} (d : Directive) (hd : ∀ L, d ≠ .label L) : PreP (labP Q) (ins d) := by
  cases d with
  | label L => exact absurd rfl (hd L)
  | instr _ => exact PreP.item' rfl
  | byteArray _ => exact PreP.item' rfl
theorem labP_comment {Q : String → Prop} (s : String) : PreP (labP Q) (item (.comment s)) := PreP.item' rfl
theorem labP_blank {Q : String → Prop} : PreP (labP Q) (item .blank) := PreP.item' rfl
theorem labP_dir {Q : String → Prop} (s : String) : PreP (labP Q) (dir s) := PreP.item' rfl

/-- One step of a `PreP (labP Q)` proof of an emitter action. -/
macro "labp_step" : tactic => `(tactic| first
  | (with_reducible exact PreP.pure' _) | (with_reducible exact PreP.throw' _)
  | (with_reducible exact PreP.get')
  | (with_reducible exact recordMap_anyP _ _ _)
  | (with_reducible exact slotOff_anyP _ _) | (with_reducible exact slot_anyP _ _)
  | (with_reducible refine PreP.bindR (freshL_anyP _) (fun _ _ _ h => freshL_res h) fun _ _ => ?_)
  | ((with_reducible refine labP_ins _ ?_) <;> (intro _ h; cases h))
  | (with_reducible exact labP_comment _) | (with_reducible exact labP_blank) | (with_reducible exact labP_dir _)
  | (with_reducible exact labP_lbl (Or.inl ‹_›))
  | (with_reducible exact labP_lbl (Or.inl (labelOf_pre _ _)))
  | (with_reducible exact labP_lbl (Or.inr (by simp only [instLabs, List.mem_singleton])))
  | (unfold sysc) | (unfold ud2) | (unfold movFs)
  | (unfold ld) | (unfold st) | (unfold movRR) | (unfold movl) | (unfold zero32) | (unfold callSym)
  | (unfold jmpTo) | (unfold cmpAB) | (unfold loadArgs) | (unfold callArgs) | (unfold safepoint)
  | (unfold epilogue)
  | (with_reducible apply PreP.bind') | (with_reducible apply PreP.forIn') | (with_reducible apply PreP.mapM')
  | (intro _) | (split))

/-- **An instruction's labels** are local to the frame's function or the
instruction's own (`instLabs`). -/
theorem emitInst_labs (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (i : Scc.IR.Inst) :
    PreP (labP fun L => (∃ t, L = ".L" ++ fr.fn ++ t) ∨ L ∈ instLabs i) (emitInst fr sm i) := by
  cases i <;> simp only [emitInst] <;> repeat labp_step

/-- **A terminator's labels** are local to the frame's function. -/
theorem emitTerm_labs {R : String → Prop} (fr : Frame) (t : Scc.IR.Term) :
    PreP (labP fun L => (∃ t, L = ".L" ++ fr.fn ++ t) ∨ R L) (emitTerm fr t) := by
  cases t <;> simp only [emitTerm] <;> repeat labp_step

/-- **The labels of a function's code**: local to it, its name, or an
instruction's own (`instLabs`) in one of its blocks. -/
def FnLab (f : Scc.IR.Func) (L : String) : Prop :=
  (∃ t, L = ".L" ++ f.name ++ t) ∨ L = f.name ∨ ∃ b ∈ f.blocks, ∃ i ∈ b.insts, L ∈ instLabs i

theorem fnLab_inst {f : Scc.IR.Func} {fr : Frame} (hfn : fr.fn = f.name) {b : Scc.IR.Block} (hb : b ∈ f.blocks)
    {i : Scc.IR.Inst} (hi : i ∈ b.insts) :
    ∀ L, ((∃ t, L = ".L" ++ fr.fn ++ t) ∨ L ∈ instLabs i) → FnLab f L := by
  rintro L (h | h)
  · exact .inl (hfn ▸ h)
  · exact .inr (.inr ⟨b, hb, i, hi, h⟩)

theorem fnLab_term {f : Scc.IR.Func} {fr : Frame} (hfn : fr.fn = f.name) :
    ∀ L, ((∃ t, L = ".L" ++ fr.fn ++ t) ∨ False) → FnLab f L := by
  rintro L (h | h)
  · exact .inl (hfn ▸ h)
  · exact h.elim

/-- An instruction of a block of `f`, in the block loop's zips. -/
theorem emitInst_fn_labs {f : Scc.IR.Func} {fr : Frame} (hfn : fr.fn = f.name)
    {bm : Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)} (hb : bm ∈ f.blocks.zip (Scc.IR.StackMap.callMaps f))
    {im : Scc.IR.Inst × Option Scc.IR.StackMap.Entry} (hi : im ∈ bm.1.insts.zip bm.2) :
    PreP (labP (FnLab f)) (emitInst fr im.2 im.1) :=
  PreP.mono (labP_mono (fnLab_inst hfn (List.of_mem_zip hb).1 (List.of_mem_zip hi).1)) (emitInst_labs _ _ _)

theorem fnLab_name (f : Scc.IR.Func) : FnLab f f.name := .inr (.inl rfl)
theorem fnLab_loc {f : Scc.IR.Func} {L : String} (h : ∃ t, L = ".L" ++ f.name ++ t) : FnLab f L := .inl h
theorem childL_pre (fn e : String) : ∃ t, childL fn e = ".L" ++ fn ++ t := labelOf_pre _ _

/-- One step of a `PreP (labP (FnLab f))` proof of `emitFunc`. -/
macro "labp_fn_step" : tactic => `(tactic| first
  | (with_reducible exact PreP.pure' _) | (with_reducible exact PreP.throw' _)
  | (with_reducible exact PreP.get')
  | (with_reducible exact recordMap_anyP _ _ _)
  | (with_reducible exact slotOff_anyP _ _) | (with_reducible exact slot_anyP _ _)
  | (with_reducible refine PreP.bindR (freshL_anyP _) (fun _ _ _ h => freshL_res h) fun _ _ => ?_)
  | ((with_reducible refine labP_ins _ ?_) <;> (intro _ h; cases h))
  | (with_reducible exact labP_comment _) | (with_reducible exact labP_blank) | (with_reducible exact labP_dir _)
  | (with_reducible exact labP_lbl (fnLab_name _))
  | (with_reducible exact labP_lbl (fnLab_loc ‹_›))
  | (with_reducible exact labP_lbl (fnLab_loc (labelOf_pre _ _)))
  | (with_reducible exact labP_lbl (fnLab_loc (childL_pre _ _)))
  | (with_reducible exact PreP.mono (labP_mono (fnLab_term rfl)) (emitTerm_labs _ _))
  | (with_reducible exact emitInst_fn_labs rfl ‹_› ‹_›)
  | (with_reducible apply PreP.forInM)
  | (unfold sysc) | (unfold ud2) | (unfold movFs)
  | (unfold ld) | (unfold st) | (unfold movRR) | (unfold movl) | (unfold zero32) | (unfold callSym)
  | (unfold jmpTo) | (unfold cmpAB) | (unfold loadArgs) | (unfold callArgs) | (unfold safepoint)
  | (unfold epilogue)
  | (with_reducible apply PreP.bind') | (with_reducible apply PreP.mapM')
  | (intro _) | (split))

set_option maxHeartbeats 1600000 in
/-- **A function's labels** (`FnLab`). -/
theorem emitFunc_labs (a g ar) (f : Scc.IR.Func) : PreP (labP (FnLab f)) (emitFunc a g ar f) := by
  simp only [emitFunc]
  apply PreP.ite'
  all_goals repeat labp_fn_step

/-- **`emitFuncAt`'s labels** (`FnLab`). -/
theorem emitFuncAt_labs {p : Scc.IR.Program} {areas : List (Scc.IR.Sym × Nat)} {f : Scc.IR.Func} {n : Nat}
    {r : List Item × Nat × List Map} (h : emitFuncAt p areas f n = .ok r) :
    ∀ L, Directive.label L ∈ dOf r.1 → FnLab f L := by
  unfold emitFuncAt at h
  cases hr : (emitFunc p.abortFn p.growth areas f).run {} with
  | error e => rw [hr] at h; cases h
  | ok v =>
    obtain ⟨⟨⟩, s⟩ := v
    rw [hr] at h
    cases h
    have h' : emitFunc p.abortFn p.growth areas f {} = .ok ((), s) := hr
    obtain ⟨c, hc, hp⟩ := (emitFunc_labs _ _ _ f).out _ _ _ h'
    simp only [List.append_nil] at hc
    intro L hL
    refine labP_mem (fun it hi => hp it ?_) hL
    rw [hc] at hi
    exact List.mem_reverse.mp hi

/-! ## The runtime's functions -/

/-- A `scc_rt_` name is no `WcL` label. -/
theorem not_wcL_rt (x : String) : ¬ WcL ("scc_rt_" ++ x) := by
  unfold WcL
  simp only [String.toList_append]
  intro h
  have := congrArg (·.head?) h
  simp at this

/-- A label local to a `scc_rt_` name is no `WcL` label. -/
theorem not_wcL_loc_rt (x t : String) : ¬ WcL (".L" ++ ("scc_rt_" ++ x) ++ t) := by
  unfold WcL
  simp only [String.toList_append]
  intro h
  have := congrArg (·[2]?) h
  simp at this

/-- **A runtime function's code places no `WcL` label**: its labels are its
name, local to it, or its instructions' (`emitFuncAt_labs`), all `scc_rt_`
names or local to one (`rtFuncs_names`). -/
theorem rtFunc_noWcL {arch lay e sw m} {rt : List Scc.IR.Func}
    (hrt : Scc.Lower.Inv.rtFuncs arch lay e sw m = .ok rt) {f : Scc.IR.Func} (hf : f ∈ rt)
    {p : Scc.IR.Program} {areas : List (Scc.IR.Sym × Nat)} {n : Nat} {r : List Scc.Emit.X64.Item × Nat × List Scc.Emit.X64.Map}
    (h : Scc.Emit.X64.emitFuncAt p areas f n = .ok r) :
    ∀ L, Directive.label L ∈ dOf r.1 → ¬ WcL L := by
  intro L hL
  obtain ⟨⟨x, hx⟩, hi⟩ := rtFuncs_names hrt f hf
  rcases emitFuncAt_labs h L hL with ⟨t, rfl⟩ | rfl | ⟨b, hb, i, hi', hl⟩
  · rw [hx]; exact not_wcL_loc_rt x t
  · rw [hx]; exact not_wcL_rt x
  · obtain ⟨y, rfl⟩ := hi b hb i hi' L hl
    exact not_wcL_rt y

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.emitFuncAt_labs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.emitFuncAt_labs

/-- info: 'Spike.Lib.LowerX64.rtFunc_noWcL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.rtFunc_noWcL
