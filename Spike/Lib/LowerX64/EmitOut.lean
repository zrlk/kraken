/-
**The x86-64 emitter only appends to its output** (`Scc.Emit.X64`): an
action `x : E α` that succeeds from a state `s` leaves an output that is
some items `c` (last first) followed by `s.out` (`Pre x`). Closed under
`pure`, `>>=`, `for … in`, `mapM` and `if`/`match`; `item`, `ins`, `lbl`,
`freshL`, `recordMap` and the frame's slot lookups have it, and so every
instruction's code (`emitInst_pre`) and every terminator's (`emitTerm_pre`).

- `instsCode`, `blockCode_eq`: a block's code is its instructions' loop
  (`instsCode`) then its terminator's.
- `instsCode_split`: the loop over `is1 ++ i :: is2` (with as many
  stack maps) runs `is1`'s, then `i`'s, then `is2`'s, each appending.
- `emitInst_call_inv`: a call's code (stack maps on) is its argument moves,
  `call g`, the return label `.L<fn>.x<k>`, then its result stores.
-/
import Scc.Cert.Code1X64

namespace Spike.Lib.LowerX64

open Scc.Emit.X64

/-- **`x` only appends to the output**: from any state it succeeds from,
the new output is some items (last first) followed by the old one. -/
structure Pre {α : Type} (x : E α) : Prop where
  out : ∀ (s : S) (a : α) (s' : S), x s = .ok (a, s') → ∃ c : List Item, s'.out = c ++ s.out

namespace Pre

theorem pure' {α : Type} (a : α) : Pre (pure a : E α) := by
  refine ⟨fun s b s' h => ?_⟩
  cases h
  exact ⟨[], rfl⟩

theorem bind' {α β : Type} {x : E α} {f : α → E β} (hx : Pre x) (hf : ∀ a, Pre (f a)) : Pre (x >>= f) := by
  refine ⟨fun s b s' h => ?_⟩
  have : StateT.bind x f s = .ok (b, s') := h
  unfold StateT.bind at this
  cases e : x s with
  | error err => rw [e] at this; cases this
  | ok r =>
    obtain ⟨a, s1⟩ := r
    rw [e] at this
    obtain ⟨c1, h1⟩ := hx.out s a s1 e
    obtain ⟨c2, h2⟩ := (hf a).out s1 b s' this
    exact ⟨c2 ++ c1, by rw [h2, h1, List.append_assoc]⟩

theorem throw' {α : Type} (e : String) : Pre (throw e : E α) := by
  refine ⟨fun s a s' h => ?_⟩
  cases h

theorem item' (it : Item) : Pre (item it) := by
  refine ⟨fun s a s' h => ?_⟩
  cases h
  exact ⟨[it], rfl⟩

theorem get' : Pre (get : E S) := by
  refine ⟨fun s a s' h => ?_⟩
  cases h
  exact ⟨[], rfl⟩

theorem ite' {α : Type} {c : Prop} [Decidable c] {x y : E α} (hx : Pre x) (hy : Pre y) :
    Pre (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem forIn' {β σ : Type} (f : β → σ → E (ForInStep σ)) (hf : ∀ b st, Pre (f b st)) :
    ∀ (l : List β) (init : σ), Pre (forIn l init f)
  | [], init => by simpa using pure' init
  | b :: l, init => by
    rw [List.forIn_cons]
    refine bind' (hf b init) fun r => ?_
    cases r with
    | done st => exact pure' st
    | yield st => exact forIn' f hf l st

theorem mapM' {β γ : Type} (f : β → E γ) (hf : ∀ b, Pre (f b)) : ∀ l : List β, Pre (l.mapM f)
  | [] => by simpa using pure' ([] : List γ)
  | b :: l => by
    rw [List.mapM_cons]
    exact bind' (hf b) fun c => bind' (mapM' f hf l) fun cs => pure' _

end Pre

theorem freshL_pre (fn : String) : Pre (freshL fn) := by
  refine ⟨fun s a s' h => ?_⟩
  cases h
  exact ⟨[], rfl⟩

theorem recordMap_pre (l : String) (st hp : List Int) : Pre (recordMap l st hp) := by
  refine ⟨fun s a s' h => ?_⟩
  cases h
  exact ⟨[], rfl⟩

theorem slotOff_pre (fr : Frame) (r : Scc.IR.Reg) : Pre (fr.slotOff r) := by
  unfold Frame.slotOff
  split
  · exact Pre.pure' _
  · exact Pre.throw' _

theorem slot_pre (fr : Frame) (r : Scc.IR.Reg) : Pre (fr.slot r) := by
  unfold Frame.slot
  exact Pre.bind' (slotOff_pre fr r) fun _ => Pre.pure' _

/-- One step of `pre_tac`. -/
macro "pre_step" : tactic => `(tactic| first
  | (with_reducible exact Pre.pure' _) | (with_reducible exact Pre.throw' _)
  | (with_reducible exact Pre.item' _) | (with_reducible exact Pre.get')
  | (with_reducible exact freshL_pre _) | (with_reducible exact recordMap_pre _ _ _)
  | (with_reducible exact slotOff_pre _ _) | (with_reducible exact slot_pre _ _)
  | (unfold ins) | (unfold lbl) | (unfold dir) | (unfold sysc) | (unfold ud2) | (unfold movFs)
  | (unfold ld) | (unfold st) | (unfold movRR) | (unfold movl) | (unfold zero32) | (unfold callSym)
  | (unfold jmpTo) | (unfold cmpAB) | (unfold loadArgs) | (unfold callArgs) | (unfold safepoint)
  | (unfold epilogue)
  | (with_reducible apply Pre.bind') | (with_reducible apply Pre.forIn') | (with_reducible apply Pre.mapM')
  | (intro _) | (split))

/-- Discharge `Pre` of an emitter action by its structure. -/
macro "pre_tac" : tactic => `(tactic| repeat pre_step)

theorem emitInst_pre (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (i : Scc.IR.Inst) :
    Pre (emitInst fr sm i) := by
  cases i <;> simp only [emitInst] <;> pre_tac

theorem emitTerm_pre (fr : Frame) (t : Scc.IR.Term) : Pre (emitTerm fr t) := by
  cases t <;> simp only [emitTerm] <;> pre_tac

/-! ## A block's instructions -/

/-- **A block's instructions' code**: the loop of `blockCode`, each
instruction with its stack map. -/
def instsCode (fr : Frame) (is : List Scc.IR.Inst) (ms : List (Option Scc.IR.StackMap.Entry)) : E Unit :=
  for (i, sm) in is.zip ms do emitInst fr sm i

theorem blockCode_eq (fr : Frame) (b : Scc.IR.Block) (ms : List (Option Scc.IR.StackMap.Entry)) :
    Scc.Cert.Code1X64.blockCode fr b ms = (do instsCode fr b.insts ms; emitTerm fr b.term) := by
  simp [Scc.Cert.Code1X64.blockCode, instsCode]

theorem instsCode_nil (fr : Frame) (ms : List (Option Scc.IR.StackMap.Entry)) (s : S) :
    instsCode fr [] ms s = .ok ((), s) := by
  simp [instsCode]; rfl

theorem instsCode_cons (fr : Frame) (i : Scc.IR.Inst) (is : List Scc.IR.Inst) (m : Option Scc.IR.StackMap.Entry)
    (ms : List (Option Scc.IR.StackMap.Entry)) :
    instsCode fr (i :: is) (m :: ms) = (do emitInst fr m i; instsCode fr is ms) := by
  simp only [instsCode, List.zip_cons_cons, List.forIn_cons, bind_assoc, pure_bind]

theorem instsCode_pre (fr : Frame) (is : List Scc.IR.Inst) (ms : List (Option Scc.IR.StackMap.Entry)) :
    Pre (instsCode fr is ms) := by
  unfold instsCode
  refine Pre.bind' (Pre.forIn' _ (fun b st => ?_) _ _) fun _ => Pre.pure' _
  obtain ⟨i, sm⟩ := b
  exact Pre.bind' (emitInst_pre fr sm i) fun _ => Pre.pure' _

/-- A bind of `E` that succeeds: its first action's result and state, from
which the continuation succeeds. -/
theorem bind_inv_E {α β : Type} {x : E α} {f : α → E β} {s s' : S} {b : β}
    (h : (x >>= f) s = .ok (b, s')) : ∃ a s1, x s = .ok (a, s1) ∧ f a s1 = .ok (b, s') := by
  have h' : StateT.bind x f s = .ok (b, s') := h
  unfold StateT.bind at h'
  cases e : x s with
  | error err => rw [e] at h'; cases h'
  | ok r => obtain ⟨a, s1⟩ := r; rw [e] at h'; exact ⟨a, s1, rfl, h'⟩

/-- A bind of `E` whose first action succeeds runs the continuation. -/
theorem bind_ok_E {α β : Type} {x : E α} {f : α → E β} {s s' : S} {a : α} (h : x s = .ok (a, s')) :
    (x >>= f) s = f a s' := by
  show StateT.bind x f s = _
  simp only [StateT.bind, h]; rfl

/-- **The code of instructions split at one**: with a stack map for each of
`is1` and the one after, the loop over `is1 ++ i :: is2` runs `is1`'s, then
`i`'s with its map, then `is2`'s with the rest. -/
theorem instsCode_split (fr : Frame) (i : Scc.IR.Inst) (is2 : List Scc.IR.Inst) :
    ∀ {is1 : List Scc.IR.Inst} {ms : List (Option Scc.IR.StackMap.Entry)} {s s' : S}
      (hl : is1.length < ms.length), instsCode fr (is1 ++ i :: is2) ms s = .ok ((), s') →
      ∃ s1 s2, instsCode fr is1 ms s = .ok ((), s1) ∧ emitInst fr ms[is1.length] i s1 = .ok ((), s2) ∧
        instsCode fr is2 (ms.drop (is1.length + 1)) s2 = .ok ((), s')
  | [], [], _, _, hl, _ => by simp at hl
  | [], m :: ms, s, s', _, h => by
    rw [List.nil_append, instsCode_cons] at h
    obtain ⟨u, s2, h1, h2⟩ := bind_inv_E h
    exact ⟨s, s2, instsCode_nil fr _ s, h1, by simpa using h2⟩
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | j :: is1, m :: ms, s, s', hl, h => by
    rw [List.cons_append, instsCode_cons] at h
    obtain ⟨u, t, h1, h2⟩ := bind_inv_E h
    obtain ⟨s1, s2, e1, e2, e3⟩ := instsCode_split fr i is2 (by simpa using hl) h2
    refine ⟨s1, s2, ?_, by simpa using e2, by simpa using e3⟩
    rw [instsCode_cons, bind_ok_E h1]
    exact e1

/-! ## A call's code -/

/-- The slot offsets' lookups leave the state as it is. -/
theorem mapM_slotOff_state (fr : Frame) :
    ∀ (l : List Scc.IR.Reg) {s : S} {a : List Int} {s' : S}, (l.mapM fr.slotOff) s = .ok (a, s') → s' = s
  | [], s, a, s', h => by
    simp only [List.mapM_nil] at h
    cases h; rfl
  | r :: l, s, a, s', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, t, h1, h2⟩ := bind_inv_E h
    have ht : t = s := by
      unfold Frame.slotOff at h1
      cases hf : List.find? (fun x => x.fst == r) fr.slots with
      | none => rw [hf] at h1; cases h1
      | some v => obtain ⟨_, k⟩ := v; rw [hf] at h1; cases h1; rfl
    subst ht
    obtain ⟨bs, t', h3, h4⟩ := bind_inv_E h2
    have := mapM_slotOff_state fr l h3
    subst this
    cases h4; rfl

theorem callArgs_pre (fr : Frame) (args : List Scc.IR.Operand) (what : String) :
    Pre (callArgs fr args what) := by
  unfold callArgs; pre_tac

theorem stores_pre (fr : Frame) (l : List (Scc.IR.Reg × Reg64)) :
    Pre (forIn (m := E) l PUnit.unit fun (x : Scc.IR.Reg × Reg64) (_ : PUnit) => do
      st fr x.2 x.1; pure (ForInStep.yield PUnit.unit)) := by
  refine Pre.forIn' _ (fun b _ => ?_) _ _
  exact Pre.bind' (by unfold st; pre_tac) fun _ => Pre.pure' _

/-- **The code of a `call`**, with the stack maps on: the arguments' loads
`ca`, the `call`, the safepoint label `.L{fn}.x{k}` (`k` the label counter
after the loads), the results' stores `sr`. -/
theorem emitInst_call_inv {fr : Frame} (hm : fr.maps = true) {sm : Option Scc.IR.StackMap.Entry}
    {ds : List Scc.IR.Reg} {g : Scc.IR.Sym} {args : List Scc.IR.Operand} {s s' : S}
    (h : emitInst fr sm (.call ds g args) s = .ok ((), s')) :
    ∃ (ca sr : List Item) (k : Nat), s'.out =
      (ca ++ [Item.d (i64 (.call (rel g))), Item.d (.label s!".L{fr.fn}.x{k}")] ++ sr).reverse ++ s.out := by
  simp only [emitInst] at h
  split at h
  · obtain ⟨_, _, h0, -⟩ := bind_inv_E h
    cases h0
  obtain ⟨u1, s1, h1, h⟩ := bind_inv_E h
  obtain ⟨cA, hA⟩ := (callArgs_pre fr args _).out _ _ _ h1
  obtain ⟨u2, s2, h2, h⟩ := bind_inv_E h
  have hs2 : s2 = { s1 with out := Item.d (i64 (.call (rel g))) :: s1.out } := by
    cases h2; rfl
  subst hs2
  obtain ⟨u3, s3, h3, h⟩ := bind_inv_E h
  have hs3 : ∃ k : Nat, s3.out = Item.d (.label s!".L{fr.fn}.x{k}") :: Item.d (i64 (.call (rel g))) :: s1.out := by
    unfold safepoint at h3
    simp only [hm, ite_true] at h3
    obtain ⟨l, t1, e1, h3⟩ := bind_inv_E h3
    cases e1
    obtain ⟨u, t2, e2, h3⟩ := bind_inv_E h3
    cases e2
    obtain ⟨st1, t3, e3, h3⟩ := bind_inv_E h3
    have := mapM_slotOff_state fr _ e3
    subst this
    obtain ⟨hp1, t4, e4, h3⟩ := bind_inv_E h3
    have := mapM_slotOff_state fr _ e4
    subst this
    cases h3
    exact ⟨s1.next, rfl⟩
  obtain ⟨k, hk⟩ := hs3
  obtain ⟨cS, hS⟩ := (Pre.bind' (stores_pre fr (ds.zip retRegs)) fun _ => Pre.pure' ()).out _ _ _ h
  refine ⟨cA.reverse, cS.reverse, k, ?_⟩
  rw [hS, hk, hA]
  simp

end Spike.Lib.LowerX64
