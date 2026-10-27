import Spike.Lib.Src.LowerEnvImm2Of

/-!
# The lowering's placement trace is in its walk

`lowerExpr cx env e`, run from a state with an open block, adds to the
placement trace (`BState.marks`) only points of `lowerEnvs2 cx env n e`, `n`
the state's counter (`lowerExpr_marks`): the walk visits every (environment,
term) point the lowering records.

- `HM h m`: from a state whose source point is `h`, `m` keeps it and every
  mark it adds is at `h` (the builder steps below `lowerExpr`: `emit` and
  `startBlock` mark the source point being lowered; `lowerOp` and every
  step it uses, by the `hm` tactic).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower

section Marks

/-- **From source point `h`, `m` keeps it and marks only at it.** -/
def HM {α : Type} (h : Option Point) (m : B α) : Prop :=
  ∀ s a s', s.here = h → m s = .ok (a, s') → s'.here = h ∧ ∀ mk ∈ s'.marks, mk ∈ s.marks ∨ h = some mk.2

theorem bind_ok_inv {α β : Type} {m : B α} {f : α → B β} {s s'' : BState} {b : β}
    (h : (m >>= f) s = .ok (b, s'')) : ∃ a s', m s = .ok (a, s') ∧ f a s' = .ok (b, s'') := by
  rcases hm : m s with e | ⟨a, s'⟩
  · rw [bind_error hm] at h; cases h
  · rw [Scc.Lower.Inv.bind_ok hm] at h; exact ⟨a, s', rfl, h⟩

theorem HM.bind {α β : Type} {h : Option Point} {m : B α} {f : α → B β} (hm : HM h m) (hf : ∀ a, HM h (f a)) :
    HM h (m >>= f) := by
  intro s b s'' hs hr
  obtain ⟨a, s', h1, h2⟩ := bind_ok_inv hr
  obtain ⟨e1, m1⟩ := hm s a s' hs h1
  obtain ⟨e2, m2⟩ := hf a s' b s'' e1 h2
  refine ⟨e2, fun mk hk => ?_⟩
  rcases m2 mk hk with hk | hk
  · exact m1 mk hk
  · exact Or.inr hk

theorem HM.pure {α : Type} {h : Option Point} (a : α) : HM h (Pure.pure a : B α) := by
  intro s b s' hs hr
  cases hr
  exact ⟨hs, fun mk hk => Or.inl hk⟩

theorem HM.throw {α : Type} {h : Option Point} (e : String) : HM h (MonadExcept.throw e : B α) := by
  intro s b s' _ hr; cases hr

theorem HM.get {α : Type} {h : Option Point} {g : BState → B α} (hg : ∀ s0, s0.here = h → HM h (g s0)) :
    HM h (get >>= g) :=
  fun s a s' hs hr => hg s hs s a s' hs hr

theorem HM.modify {h : Option Point} {f : BState → BState} (hf : ∀ s, (f s).here = s.here ∧ (f s).marks = s.marks) :
    HM h (modify f) := by
  intro s a s' hs hr
  rw [Scc.Lower.Inv.modify_eq] at hr
  cases hr
  obtain ⟨h1, h2⟩ := hf s
  exact ⟨h1.trans hs, fun mk hk => Or.inl (h2 ▸ hk)⟩

theorem hm_markAt {h : Option Point} {n : Node} {p : Point} (hp : h = some p) : HM h (markAt n p) := by
  intro s a s' hs hr
  cases hr
  refine ⟨hs, fun mk hk => ?_⟩
  simp only [Array.mem_push, List.mem_toArray, List.mem_filter, Array.mem_toList_iff] at hk
  rcases hk with hk | rfl
  · exact Or.inl hk.1
  · exact Or.inr hp

theorem hm_fresh {h : Option Point} (hint : String) : HM h (fresh hint) := by
  intro s a s' hs hr
  rw [Scc.Lower.Inv.fresh_eq] at hr
  cases hr
  exact ⟨hs, fun mk hk => Or.inl hk⟩

theorem hm_freshLabel {h : Option Point} (hint : String) : HM h (freshLabel hint) := by
  intro s a s' hs hr
  rw [Scc.Lower.Inv.freshLabel_eq] at hr
  cases hr
  exact ⟨hs, fun mk hk => Or.inl hk⟩

theorem HM.forIn {α β : Type} {h : Option Point} (xs : List α) (b : β) {f : α → β → B (ForInStep β)}
    (hf : ∀ a b, HM h (f a b)) : HM h (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact HM.pure b
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine HM.bind (hf x b) fun r => ?_
    cases r with
    | done b' => exact HM.pure b'
    | yield b' => exact ih b'

theorem HM.mapM {α β : Type} {h : Option Point} (xs : List α) {f : α → B β} (hf : ∀ a, HM h (f a)) :
    HM h (xs.mapM f) := by
  induction xs with
  | nil => exact HM.pure []
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact HM.bind (hf x) fun a => HM.bind ih fun as => HM.pure _

/-- The steps proved `HM` so far (extended after each lemma). -/
syntax "hm_leaf" : tactic
macro_rules | `(tactic| hm_leaf) => `(tactic| fail "no leaf")

syntax "hm_core" : tactic
macro_rules
  | `(tactic| hm_core) => `(tactic| first
      | with_reducible (first
        | hm_leaf
        | exact HM.pure _
        | exact HM.throw _
        | exact hm_fresh _
        | exact hm_freshLabel _
        | (apply HM.modify; intro _; (try split) <;> exact ⟨rfl, rfl⟩)
        | (apply hm_markAt; simp_all)
        | apply HM.get
        | apply HM.bind
        | apply HM.forIn
        | apply HM.mapM
        | split))

/-- Decompose a builder program into its steps, for `HM`. -/
macro "hm" : tactic => `(tactic| repeat' (first | with_reducible intro _ | hm_core))

theorem hm_emit (h : Option Point) (i : Inst) : HM h (emit i) := by
  unfold emit; hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_emit)

theorem hm_terminate (h : Option Point) (t : Term) : HM h (terminate t) := by
  unfold terminate; hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_terminate)

theorem hm_startBlock (h : Option Point) (l : Label) : HM h (startBlock l) := by
  unfold startBlock; hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_startBlock)

theorem hm_binR (h : Option Point) (op : BinOp) (a b : Operand) (hint : String) :
    HM h (binR op a b hint) := by
  unfold binR <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_binR)

theorem hm_needSome (h : Option Point) {α : Type} (o : Option α) (msg : String) :
    HM h (needSome o msg) := by
  unfold needSome <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_needSome)

theorem hm_words (h : Option Point) (t : Ty) :
    HM h (words t) := by
  unfold words <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_words)

theorem hm_regOf (h : Option Point) (t : Ty) :
    HM h (regOf t) := by
  unfold regOf <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_regOf)

theorem hm_countsOf (h : Option Point) (o : Scc.ObjLayout) (t : Ty) :
    HM h (countsOf o t) := by
  unfold countsOf <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_countsOf)

theorem hm_header (h : Option Point) (o : Scc.ObjLayout) (k : Scc.Obj.HeaderKind) (n m : Nat) :
    HM h (header o k n m) := by
  unfold header <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_header)

theorem hm_evalAt (h : Option Point) (env : Env) (a : At) :
    HM h (evalAt env a) := by
  cases a <;> simp only [evalAt, lookupV] <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_evalAt)

theorem hm_one (h : Option Point) (ws : List Operand) (what : String) :
    HM h (one ws what) := by
  unfold one <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_one)

theorem hm_evalOne (h : Option Point) (env : Env) (a : At) (what : String) :
    HM h (evalOne env a what) := by
  unfold evalOne <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_evalOne)

theorem hm_inReg (h : Option Point) (o : Operand) (hint : String) :
    HM h (inReg o hint) := by
  unfold inReg <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_inReg)

theorem hm_markHeap (h : Option Point) (r : Reg) : HM h (markHeap r) := by
  unfold markHeap; apply HM.modify; intro _; split <;> exact ⟨rfl, rfl⟩
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_markHeap)

theorem hm_markScalar (h : Option Point) (r : Reg) : HM h (markScalar r) := by
  unfold markScalar; apply HM.modify; intro _; split <;> exact ⟨rfl, rfl⟩
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_markScalar)

theorem hm_markWords (h : Option Point) (t : Ty) (ws : List Operand) :
    HM h (markWords t ws) := by
  unfold markWords <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_markWords)

theorem hm_refOf (h : Option Point) (ws : List Operand) (what : String) :
    HM h (refOf ws what) := by
  unfold refOf <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_refOf)

theorem hm_offAdd (h : Option Point) (a b : Operand) :
    HM h (offAdd a b) := by
  unfold offAdd <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_offAdd)

theorem hm_offMul (h : Option Point) (i : Operand) (c : Nat) :
    HM h (offMul i c) := by
  unfold offMul <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_offMul)

theorem hm_cellAddrs (h : Option Point) (o : Scc.ObjLayout) (base off : Operand) (u : Ty) :
    HM h (cellAddrs o base off u) := by
  unfold cellAddrs <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_cellAddrs)

theorem hm_loadAt (h : Option Point) (o : Order) (as : List Addr) (hint : String) :
    HM h (loadAt o as hint) := by
  unfold loadAt <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_loadAt)

theorem hm_storeAt (h : Option Point) (o : Order) (as : List Addr) (ws : List Operand) :
    HM h (storeAt o as ws) := by
  unfold storeAt <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_storeAt)

theorem hm_slotLoc (h : Option Point) (base off i : Operand) (u : Ty) :
    HM h (slotLoc base off i u) := by
  unfold slotLoc <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_slotLoc)

theorem hm_mask (h : Option Point) (w : Wd) (a : Operand) :
    HM h (mask w a) := by
  unfold mask <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_mask)

theorem hm_sext (h : Option Point) (w : Wd) (a : Operand) :
    HM h (sext w a) := by
  unfold sext <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_sext)

theorem hm_fval (h : Option Point) (sg : Bool) (w : Wd) (a : Operand) :
    HM h (fval sg w a) := by
  unfold fval <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_fval)

theorem hm_fop (h : Option Point) (sg : Bool) (w : Wd) (o : FOp) (x y : Operand) :
    HM h (fop sg w o x y) := by
  unfold fop <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_fop)

theorem hm_fcmp (h : Option Point) (sg : Bool) (w : Wd) (o : FCmp) (x y : Operand) :
    HM h (fcmp sg w o x y) := by
  unfold fcmp <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_fcmp)

theorem hm_fop1 (h : Option Point) (w : Wd) (o : FOp1) (x : Operand) :
    HM h (fop1 w o x) := by
  unfold fop1 <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_fop1)

theorem hm_cvt (h : Option Point) (src : Ty) (w : Wd) (x : Operand) :
    HM h (cvt src w x) := by
  unfold cvt <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_cvt)

theorem hm_laneShift (h : Option Point) (w : Wd) (j : Operand) :
    HM h (laneShift w j) := by
  unfold laneShift <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_laneShift)

theorem hm_lane (h : Option Point) (w : Wd) (x j : Operand) :
    HM h (lane w x j) := by
  unfold lane <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_lane)

theorem hm_setLane (h : Option Point) (w : Wd) (x j v : Operand) :
    HM h (setLane w x j v) := by
  unfold setLane <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_setLane)

theorem hm_bitOp (h : Option Point) (o : BitOp) :
    HM h (bitOp o) := by
  unfold bitOp <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_bitOp)

theorem hm_callBlock (h : Option Point) (cx : Scc.Lower.Ctx) (f : String) (args : List Operand) (nres : Nat) :
    HM h (callBlock cx f args nres) := by
  unfold callBlock <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_callBlock)

theorem hm_tcbLayout (h : Option Point) (o : Scc.ObjLayout) (T : Ty) :
    HM h (tcbLayout o T) := by
  unfold tcbLayout <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_tcbLayout)

theorem hm_spawn (h : Option Point) (o : Scc.ObjLayout) (f : String) (T : Ty) (args : List Operand) :
    HM h (spawn o f T args) := by
  unfold spawn <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_spawn)

theorem hm_lowerOp (h : Option Point) (cx : Scc.Lower.Ctx) (env : Env) (x : String) (op : Op) :
    HM h (lowerOp cx env x op) := by
  cases op <;> simp only [lowerOp] <;> hm
macro_rules | `(tactic| hm_leaf) => `(tactic| apply hm_lowerOp)

theorem hm_splitStep (h : Option Point) (env : Env) (a : At) : HM h (splitStep env a) := by
  unfold splitStep; hm

theorem hm_ifStep (h : Option Point) (env : Env) (a b : At) : HM h (ifStep env a b) := by
  unfold ifStep; hm

/-! ## The trace's points are the walk's -/

/-- `p` is a point of walk `W`. -/
def InW (W : List (Expr × Env × Nat)) (p : Point) : Prop := ∃ q ∈ W, (q.2.1, q.1) = p

theorem InW.head {W : List (Expr × Env × Nat)} {e : Expr} {env : Env} {n : Nat} (h : (e, env, n) ∈ W) :
    InW W (env, e) := ⟨_, h, rfl⟩

theorem InW.cons {W : List (Expr × Env × Nat)} {q : Expr × Env × Nat} {p : Point} (h : InW W p) :
    InW (q :: W) p :=
  let ⟨r, hr, he⟩ := h; ⟨r, List.mem_cons_of_mem _ hr, he⟩

theorem InW.append_left {W V : List (Expr × Env × Nat)} {p : Point} (h : InW W p) : InW (W ++ V) p :=
  let ⟨r, hr, he⟩ := h; ⟨r, List.mem_append_left _ hr, he⟩

theorem InW.append_right {W V : List (Expr × Env × Nat)} {p : Point} (h : InW V p) : InW (W ++ V) p :=
  let ⟨r, hr, he⟩ := h; ⟨r, List.mem_append_right _ hr, he⟩

/-- The walk starts at its own point. -/
theorem mem_lowerEnvs2_head (cx : Scc.Lower.Ctx) (env : Env) (n : Nat) (e : Expr) :
    (e, env, n) ∈ lowerEnvs2 cx env n e := by
  cases e <;> simp [lowerEnvs2]

theorem inW_here {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {e : Expr} {p : Point} (h : some (env, e) = some p) :
    InW (lowerEnvs2 cx env n e) p := by
  cases h; exact InW.head (mem_lowerEnvs2_head cx env n e)

theorem marks_of_hm {α : Type} {P : Point} {m : B α} (hm : HM (some P) m) {s : BState} {a : α} {s' : BState}
    (hr : m { s with here := some P } = .ok (a, s')) : ∀ mk ∈ s'.marks, mk ∈ s.marks ∨ some P = some mk.2 :=
  (hm _ a s' rfl hr).2

theorem markAt_ok {n : Node} {p : Point} {s s' : BState} {a : Unit} (h : markAt n p s = .ok (a, s')) :
    s'.next = s.next ∧ s'.cur = s.cur ∧ s'.here = s.here ∧
      ∀ mk ∈ s'.marks, (mk ∈ s.marks ∧ (mk.1 != n) = true) ∨ mk = (n, p) := by
  cases h
  refine ⟨rfl, rfl, rfl, fun mk hk => ?_⟩
  simp only [Array.mem_push, List.mem_toArray, List.mem_filter, Array.mem_toList_iff] at hk
  exact hk

theorem terminate_ok {t : Term} {s s' : BState} {a : Unit} (h : terminate t s = .ok (a, s')) :
    s'.next = s.next ∧ s'.marks = s.marks := by
  unfold terminate at h; rw [Scc.Lower.Inv.modify_eq] at h; cases h; constructor <;> split <;> rfl

/-- `startBlock l` adds marks only at `l`'s start. -/
theorem startBlock_marks (l : Label) (s t : BState) (h : startBlock l s = .ok ((), t)) :
    ∀ mk ∈ t.marks, mk ∈ s.marks ∨ mk.1 = .block l := by
  unfold startBlock at h
  rcases hc : s.cur with _ | ⟨l', is⟩ <;> rcases hh : s.here with _ | p <;>
    simp [hc, hh, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, Except.bind, terminate,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Except.pure, StateT.pure, pure, markAt] at h <;>
    subst h <;> simp <;>
    (intro a b c hk; first | exact Or.inl hk | (rcases hk with ⟨hk, -⟩ | ⟨hk, -⟩ <;> simp [hk]))

theorem block_bne_self (l : Label) : (Node.block l != Node.block l) = false := by
  have : (Node.block l == Node.block l) = true := by show (l == l) = true; simp
  show (!(Node.block l == Node.block l)) = false
  rw [this]; rfl

/-- `startBlock l; markAt (.block l) p`: the old marks, and one at `p`. -/
theorem startMark_marks {l : Label} {p : Point} {s t u : BState} {a : Unit} (h1 : startBlock l s = .ok ((), t))
    (h2 : markAt (.block l) p t = .ok (a, u)) : ∀ mk ∈ u.marks, mk ∈ s.marks ∨ mk.2 = p := by
  intro mk hk
  rcases (markAt_ok h2).2.2.2 mk hk with ⟨hk, hb⟩ | rfl
  · rcases startBlock_marks l s t h1 mk hk with hk | hk
    · exact Or.inl hk
    · rw [hk, block_bne_self] at hb; cases hb
  · exact Or.inr rfl

/-- **The lowering marks only points of its walk**: run from a state with an
open block, every mark `lowerExpr cx env e` adds is at a point of
`lowerEnvs2 cx env n e`, `n` the state's counter. -/
theorem lowerExpr_marks (cx : Scc.Lower.Ctx) (e : Expr) : ∀ (env : Env) (s s' : BState), s.cur.isSome = true →
    lowerExpr cx env e s = .ok ((), s') →
    ∀ mk ∈ s'.marks, mk ∈ s.marks ∨ InW (lowerEnvs2 cx env s.next e) mk.2 := by
  induction e with
  | let_ x op e ih =>
    intro env s s' hc hr
    have h0 : setHere (env, Expr.let_ x op e) s = .ok ((), { s with here := some (env, .let_ x op e) }) := rfl
    rw [lowerExpr, Scc.Lower.Inv.bind_ok h0] at hr
    have hc1 : ∀ P : Point, (BState.cur { s with here := some P }).isSome = true := fun _ => hc
    obtain ⟨⟨t, ws⟩, s2, h1, hr⟩ := bind_ok_inv hr
    try dsimp only at hr
    obtain ⟨hh2, hm2⟩ := hm_lowerOp _ cx env x op _ _ s2 rfl h1
    have hc2 : s2.cur.isSome = true := kc_lowerOp cx env x op _ _ s2 (hc1 _) h1
    have cont : ∀ s3 : BState, s3.next = s2.next → s3.cur = s2.cur → s3.here = s2.here →
        (∀ mk ∈ s3.marks, mk ∈ s2.marks ∨ mk.2 = ((x, t, ws) :: env, e)) →
        (markWords t ws >>= fun _ => lowerExpr cx ((x, t, ws) :: env) e) s3 = .ok ((), s') →
        ∀ mk ∈ s'.marks, mk ∈ s.marks ∨ InW (lowerEnvs2 cx env s.next (.let_ x op e)) mk.2 := by
      intro s3 hn3 hcur3 hh3 hm3 hr
      obtain ⟨_, s4, h4, hr⟩ := bind_ok_inv hr
      have hc3 : s3.cur.isSome = true := by rw [hcur3]; exact hc2
      have hc4 := kc_markWords t ws s3 _ s4 hc3 h4
      obtain ⟨-, hm4⟩ := hm_markWords _ t ws s3 _ s4 (hh3.trans hh2) h4
      have hr4 := resp_markWords t ws s2 s3 ⟨hn3.symm, by rw [hcur3]⟩
      rcases h4' : markWords t ws s2 with _ | ⟨u, s4'⟩ <;> rw [h4', h4] at hr4 <;> simp only [ResRel] at hr4
      obtain ⟨-, hn4, -⟩ := hr4
      have hl : letStep cx env x op e s = .ok ((t, ws), s4') := by
        unfold letStep
        exact (Scc.Lower.Inv.bind_ok h0).trans ((Scc.Lower.Inv.bind_ok h1).trans
          ((Scc.Lower.Inv.bind_ok h4').trans rfl))
      have hrun : runB (letStep cx env x op e) s.next = some ((t, ws), s4.next) :=
        (runB_some_iff (resp_letStep cx env x op e) (s := s) hc).2 ⟨s4', hl, hn4⟩
      have hW : lowerEnvs2 cx env s.next (.let_ x op e) =
          (.let_ x op e, env, s.next) :: lowerEnvs2 cx ((x, t, ws) :: env) s4.next e := by
        rw [lowerEnvs2, hrun]
      intro mk hk
      rcases ih _ s4 s' hc4 hr mk hk with hk | hk
      · rcases hm4 mk hk with hk | hk
        · rcases hm3 mk hk with hk | hk
          · rcases hm2 mk hk with hk | hk
            · exact Or.inl hk
            · exact Or.inr (inW_here hk)
          · right; rw [hW, hk]; exact InW.cons (InW.head (mem_lowerEnvs2_head _ _ _ _))
        · exact Or.inr (inW_here hk)
      · right; rw [hW]; exact InW.cons hk
    cases op
    all_goals first
      | exact cont s2 rfl rfl rfl (fun mk h => Or.inl h) hr
      | skip
    dsimp only at hr
    split at hr
    · obtain ⟨d, s3, hg, hr⟩ := bind_ok_inv hr
      cases hg
      revert hr
      generalize Array.back? _ = o
      rcases o with _ | ⟨_ | _, _⟩ <;> intro hr
      · exact cont s2 rfl rfl rfl (fun mk h => Or.inl h) hr
      · exact cont s2 rfl rfl rfl (fun mk h => Or.inl h) hr
      · obtain ⟨_, s3, hm, hr⟩ := bind_ok_inv hr
        obtain ⟨n3, c3, h3, m3⟩ := markAt_ok hm
        exact cont s3 n3 c3 h3 (fun mk hk => (m3 mk hk).imp (·.1) (congrArg Prod.snd)) hr
    · exact cont s2 rfl rfl rfl (fun mk h => Or.inl h) hr
  | split a x y e ih =>
    intro env s s' hc hr
    have h0 : setHere (env, Expr.split a x y e) s = .ok ((), { s with here := some (env, .split a x y e) }) := rfl
    rw [lowerExpr, Scc.Lower.Inv.bind_ok h0] at hr
    have hc1 : ∀ P : Point, (BState.cur { s with here := some P }).isSome = true := fun _ => hc
    obtain ⟨⟨t, ws⟩, s2, h2, hr⟩ := bind_ok_inv hr
    try dsimp only at hr
    obtain ⟨⟨u, w⟩, s3, h3, hr⟩ := bind_ok_inv hr
    try dsimp only at hr
    obtain ⟨k, s4, h4, hr⟩ := bind_ok_inv hr
    try dsimp only at hr
    have hl : splitStep env a { s with here := some (env, .split a x y e) } = .ok ((u, w, ws, k), s4) := by
      unfold splitStep
      exact (Scc.Lower.Inv.bind_ok h2).trans ((Scc.Lower.Inv.bind_ok h3).trans
        ((Scc.Lower.Inv.bind_ok h4).trans rfl))
    have hc4 := kc_splitStep env a _ _ s4 (hc1 _) hl
    obtain ⟨-, hm4⟩ := hm_splitStep _ env a _ _ s4 rfl hl
    have hrun : runB (splitStep env a) s.next = some ((u, w, ws, k), s4.next) :=
      (runB_some_iff (resp_splitStep env a) (hc1 _)).2
        ⟨s4, hl, rfl⟩
    intro mk hk
    rcases ih _ s4 s' hc4 hr mk hk with hk | hk
    · rcases hm4 mk hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr (inW_here hk)
    · right; rw [lowerEnvs2, hrun]; exact InW.cons hk
  | unpack a i x e ih =>
    intro env s s' hc hr
    have h0 : setHere (env, Expr.unpack a i x e) s = .ok ((), { s with here := some (env, .unpack a i x e) }) :=
      rfl
    rw [lowerExpr, Scc.Lower.Inv.bind_ok h0] at hr
    have hc1 : ∀ P : Point, (BState.cur { s with here := some P }).isSome = true := fun _ => hc
    obtain ⟨⟨t, ws⟩, s2, h2, hr⟩ := bind_ok_inv hr
    try dsimp only at hr
    have hc2 := kc_evalAt env a _ _ s2 (hc1 _) h2
    obtain ⟨-, hm2⟩ := hm_evalAt _ env a _ _ s2 rfl h2
    split at hr
    · subst_vars
      have hrun : runB (evalAt env a) s.next = some ((_, ws), s2.next) :=
        (runB_some_iff (resp_evalAt env a) (hc1 _)).2 ⟨s2, h2, rfl⟩
      intro mk hk
      rcases ih _ s2 s' hc2 hr mk hk with hk | hk
      · rcases hm2 mk hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr (inW_here hk)
      · right; rw [lowerEnvs2, hrun]; exact InW.cons hk
    · cases hr
  | unpackT a α x e ih =>
    intro env s s' hc hr
    have h0 : setHere (env, Expr.unpackT a α x e) s =
        .ok ((), { s with here := some (env, .unpackT a α x e) }) := rfl
    rw [lowerExpr, Scc.Lower.Inv.bind_ok h0] at hr
    have hc1 : ∀ P : Point, (BState.cur { s with here := some P }).isSome = true := fun _ => hc
    obtain ⟨⟨t, ws⟩, s2, h2, hr⟩ := bind_ok_inv hr
    try dsimp only at hr
    have hc2 := kc_evalAt env a _ _ s2 (hc1 _) h2
    obtain ⟨-, hm2⟩ := hm_evalAt _ env a _ _ s2 rfl h2
    split at hr
    · subst_vars
      have hrun : runB (evalAt env a) s.next = some ((_, ws), s2.next) :=
        (runB_some_iff (resp_evalAt env a) (hc1 _)).2 ⟨s2, h2, rfl⟩
      intro mk hk
      rcases ih _ s2 s' hc2 hr mk hk with hk | hk
      · rcases hm2 mk hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr (inW_here hk)
      · right; rw [lowerEnvs2, hrun]; exact InW.cons hk
    · cases hr
  | ifeq a b yes no ihy ihn =>
    intro env s s' hc hr
    have h0 : setHere (env, Expr.ifeq a b yes no) s =
        .ok ((), { s with here := some (env, .ifeq a b yes no) }) := rfl
    rw [lowerExpr, Scc.Lower.Inv.bind_ok h0] at hr
    have hc1 : ∀ P : Point, (BState.cur { s with here := some P }).isSome = true := fun _ => hc
    obtain ⟨p, s2, h2, hr⟩ := bind_ok_inv hr
    obtain ⟨q, s3, h3, hr⟩ := bind_ok_inv hr
    obtain ⟨ly, s4, h4, hr⟩ := bind_ok_inv hr
    obtain ⟨ln, s5, h5, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s6, h6, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s7, h7, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s8, h8, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s9, h9, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s10, h10, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s11, h11, hr⟩ := bind_ok_inv hr
    have hl : ifStep env a b { s with here := some (env, .ifeq a b yes no) } = .ok ((), s5) := by
      unfold ifStep
      exact (Scc.Lower.Inv.bind_ok h2).trans ((Scc.Lower.Inv.bind_ok h3).trans
        ((Scc.Lower.Inv.bind_ok h4).trans ((Scc.Lower.Inv.bind_ok h5).trans rfl)))
    obtain ⟨-, hm5⟩ := hm_ifStep _ env a b _ _ s5 rfl hl
    have hrun : runB (ifStep env a b) s.next = some ((), s5.next) :=
      (runB_some_iff (resp_ifStep env a b) (hc1 _)).2
        ⟨s5, hl, rfl⟩
    obtain ⟨hn6, hk6⟩ := terminate_ok h6
    have hm8 := startMark_marks h7 h8
    obtain ⟨s7', h7', hn7, hc7⟩ := startBlock_shape ly s6
    rw [h7'] at h7; cases h7
    obtain ⟨hn8, hc8, -, -⟩ := markAt_ok h8
    have hc8' : s8.cur.isSome = true := by rw [hc8]; exact hc7
    have hrunY : runB (lowerExpr cx env yes) s8.next = _ :=
      (runB_some_iff (resp_lowerExpr cx yes env) hc8').2 ⟨s9, h9, rfl⟩
    have hm11 := startMark_marks h10 h11
    obtain ⟨s10', h10', hn10, hc10⟩ := startBlock_shape ln s9
    rw [h10'] at h10; cases h10
    obtain ⟨hn11, hc11, -, -⟩ := markAt_ok h11
    have hc11' : s11.cur.isSome = true := by rw [hc11]; exact hc10
    have hn85 : s8.next = s5.next := hn8.trans (hn7.trans hn6)
    have hW : lowerEnvs2 cx env s.next (.ifeq a b yes no) = (.ifeq a b yes no, env, s.next) ::
        (lowerEnvs2 cx env s8.next yes ++ lowerEnvs2 cx env s11.next no) := by
      rw [lowerEnvs2, hrun]
      dsimp only
      rw [← hn85, hrunY]
      dsimp only
      rw [hn11, hn10]
    intro mk hk
    rw [hW]
    rcases ihn _ s11 s' hc11' hr mk hk with hk | hk
    · rcases hm11 mk hk with hk | hk
      · rcases ihy _ s8 s9 hc8' h9 mk hk with hk | hk
        · rcases hm8 mk hk with hk | hk
          · rw [hk6] at hk
            rcases hm5 mk hk with hk | hk
            · exact Or.inl hk
            · exact Or.inr ⟨_, List.mem_cons_self .., Option.some.inj hk⟩
          · right; rw [hk]; exact InW.cons (InW.append_left (InW.head (mem_lowerEnvs2_head _ _ _ _)))
        · exact Or.inr (InW.cons (InW.append_left hk))
      · right; rw [hk]; exact InW.cons (InW.append_right (InW.head (mem_lowerEnvs2_head _ _ _ _)))
    · exact Or.inr (InW.cons (InW.append_right hk))
  | _ =>
    intro env s s' _ hr
    rw [lowerExpr, Scc.Lower.Inv.bind_ok (show setHere _ s = .ok ((), { s with here := some _ }) from rfl)] at hr
    try dsimp only at hr
    refine fun mk hk => (marks_of_hm ?_ hr mk hk).imp id inW_here
    hm
    all_goals contradiction

end Marks

end Spike.Lib.LowerNode
