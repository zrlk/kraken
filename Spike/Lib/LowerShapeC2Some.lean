/-
**The closed form `lowerC2` exists for every compiled block of an
`Accepted2` program the lowering accepts** (ISA-neutral).

`lowerC2` (`Spike/Lib/LowerShapeC2.lean`) covers fewer shapes than the term
lowering `lowerExpr` accepts: one-word operands of `+`, `-`, `if` and a call
of a code block, a code block returning an `Int`, `newBuf`'s count an
immediate, a lane store's buffer a register base with an immediate offset
and its value one word, the extern's slice offset a register. On an
`Accepted2` body these follow from `lowerExpr`'s success with the invariants
the program's checks give along the walk:

* `Rel`/`BufInv` (`Spike/Lib/Src/ImmIn2.lean`): the words agree with the
  walk's literal layout (`litWalk2`), so a call's operand has its callee's
  parameter layout (`callsOk2`): one word for a code block (`Int → Int`,
  `plain2`), the owned slice's four for the extern;
* `CsW`: a value known before run time (`body2`'s `cs`) is one immediate;
* `BufW`: a buffer (`body2`'s `bufs`) is a register base and an immediate
  offset;
* `LocR`: outside the setup block a locative's words are registers (no
  `newBuf` there; every locative comes from the parameter).

`lowerC2_isSome`: from `lowerExpr`'s success on a `body2` body under these
invariants, `lowerC2` is defined. `accepted2_lowerC2`: on a compiled block
of an `Accepted2` program whose `lowerDeclMarks` succeeds, the hypotheses of
`lowerDeclMarks_lowerC2` hold; `accepted2_lowerDeclMarks` its result.
-/
import Spike.Lib.LowerShapeC2
import Spike.Lib.Src.ExternUnit

namespace Spike.Lib.LowerShape

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Spike.Lib.LowerNode (Post Post.bind Post.bind' Post.pure Post.throw Post.mono Post.and post_needSome post_words
  post_lookupV post_one post_cellAddrs post_loadAt IsReg flatL Compat AgreeW AgreeW.length AgreeW.take_drop
  compat_prodOf valWords_compat Rel RelE BufInv bufTy find?_cons_name lookup_cons_name lookup_unbuf
  post_evalAt atom1_var let_step layQ CxOK OpQ bind_ok_inv)

set_option linter.unusedSimpArgs false

/-! ## Builder steps backwards -/

theorem post_true {α : Type} (m : B α) : Post m fun _ => True := fun _ _ _ _ => trivial

theorem throw_ok {α : Type} {e : String} {s : BState} {a : α} {s' : BState}
    (h : (throw e : B α) s = .ok (a, s')) : False := by
  have e' : (throw e : B α) s = (Except.error e : Except String (α × BState)) := rfl
  rw [e'] at h; cases h

theorem post_evalAtV (env : Env) (a : At) : Post (evalAt env a) fun v => atomV env a = some v := by
  cases a with
  | var x =>
    refine Post.mono (post_lookupV env x) fun r ⟨b, hb, hr⟩ => ?_
    obtain ⟨y, t, ws⟩ := b
    subst hr
    simp [atomV, hb]
  | lit n =>
    show Post (if n ≥ 2 ^ 64 then _ else _) _
    split
    · exact Post.throw
    · rename_i hn; exact Post.pure (by simp [atomV, hn])
  | unit => exact Post.pure rfl

theorem evalAt_inv {env : Env} {a : At} {s s' : BState} {v : Ty × List Operand}
    (h : evalAt env a s = .ok (v, s')) : atomV env a = some v ∧ s' = s := by
  have hv := post_evalAtV env a s v s' h
  rw [evalAt_eq hv s] at h
  cases h; exact ⟨hv, rfl⟩

theorem post_evalOneV (env : Env) (a : At) (what : String) :
    Post (evalOne env a what) fun p => ∃ t, atomV env a = some (t, [p]) := by
  unfold evalOne
  exact Post.bind (post_evalAtV env a) fun r hr => Post.mono (post_one _ _) fun p hp => ⟨r.1, by rw [hr, ← hp]⟩

theorem evalOne_inv {env : Env} {a : At} {what : String} {s s' : BState} {p : Operand}
    (h : evalOne env a what s = .ok (p, s')) : (∃ t, atomV env a = some (t, [p])) ∧ s' = s := by
  obtain ⟨t, ht⟩ := post_evalOneV env a what s p s' h
  rw [evalOne_eq ht what s] at h
  cases h; exact ⟨⟨t, ht⟩, rfl⟩

theorem needSome_inv {α : Type} {o : Option α} {msg : String} {s s' : BState} {a : α}
    (h : needSome o msg s = .ok (a, s')) : o = some a ∧ s' = s := by
  have ho := post_needSome o msg s a s' h
  rw [needSome_eq ho msg s] at h
  cases h; exact ⟨ho, rfl⟩

theorem words_inv {t : Ty} {s s' : BState} {k : Nat} (h : words t s = .ok (k, s')) :
    Scc.Obj.valWords t = some k ∧ s' = s := by
  have hk := post_words t s k s' h
  rw [words_eq hk s] at h
  cases h; exact ⟨hk, rfl⟩

theorem post_markWords (t : Ty) (ws : List Operand) :
    Post (markWords t ws) fun _ => ∃ sc hp, markR t ws = some (sc, hp) := by
  unfold markWords
  refine Post.bind (post_needSome _ _) fun bs hb => ?_
  by_cases hl : bs.length = ws.length
  · exact Post.mono (post_true _) fun _ _ =>
      ⟨(markSplit bs ws).1, (markSplit bs ws).2, by simp [markR, hb, hl]⟩
  · have hne : (bs.length != ws.length) = true := by simpa using hl
    simp only [hne, ite_true]
    first
      | exact Post.throw
      | exact Post.bind Post.throw fun _ _ => Post.throw
      | exact Post.bind' fun _ => Post.throw

theorem post_countsOf (o : Scc.ObjLayout) (t : Ty) : Post (countsOf o t) fun c => countsO o t = some c := by
  unfold countsOf regOf
  refine Post.bind (P := fun r => Scc.Obj.regOf t = some r) ?_ fun r hr => ?_
  · split
    · rename_i r' h; exact Post.pure h
    · exact Post.throw
  · split
    · rename_i c hc
      split
      · rename_i he
        exact Post.pure (by simp [countsO, hr, hc, beq_iff_eq.1 he])
      · exact Post.throw
    · exact Post.throw

theorem post_header (o : Scc.ObjLayout) (k : Scc.Obj.HeaderKind) (n m : Nat) :
    Post (header o k n m) fun h => Scc.Obj.header0 o k n m = some h := by
  unfold header
  split
  · rename_i h hh; exact Post.pure hh
  · exact Post.throw

theorem post_storeAt (o : Order) (as : List Addr) (ws : List Operand) :
    Post (storeAt o as ws) fun _ => as.length = ws.length := by
  unfold storeAt
  by_cases hl : as.length = ws.length
  · exact Post.mono (post_true _) fun _ _ => hl
  · have hne : (as.length != ws.length) = true := by simpa using hl
    simp only [hne, ite_true]
    first
      | exact Post.throw
      | exact Post.bind Post.throw fun _ _ => Post.throw
      | exact Post.bind' fun _ => Post.throw

theorem post_slotLoc (base off i : Operand) (u : Ty) :
    Post (slotLoc base off i u) fun _ => ∃ r, Scc.Obj.regOf u = some r := by
  unfold slotLoc regOf
  refine Post.bind (P := fun r => Scc.Obj.regOf u = some r) ?_ fun r hr => Post.mono (post_true _) fun _ _ => ⟨r, hr⟩
  split
  · rename_i r' h; exact Post.pure h
  · exact Post.throw

/-! ## The lowering's operations backwards -/

theorem post_add2 (cx : Scc.Lower.Ctx) (env : Env) (x : String) (a b : At) :
    Post (lowerOp cx env x (.add a b)) fun _ =>
      ∃ ta p tb q, atomV env a = some (ta, [p]) ∧ atomV env b = some (tb, [q]) := by
  simp only [lowerOp]
  exact Post.bind (post_evalOneV _ _ _) fun p ⟨ta, hp⟩ => Post.bind (post_evalOneV _ _ _) fun q ⟨tb, hq⟩ =>
    Post.mono (post_true _) fun _ _ => ⟨ta, p, tb, q, hp, hq⟩

theorem post_sub2 (cx : Scc.Lower.Ctx) (env : Env) (x : String) (a b : At) :
    Post (lowerOp cx env x (.sub a b)) fun _ =>
      ∃ ta p tb q, atomV env a = some (ta, [p]) ∧ atomV env b = some (tb, [q]) := by
  simp only [lowerOp]
  exact Post.bind (post_evalOneV _ _ _) fun p ⟨ta, hp⟩ => Post.bind (post_evalOneV _ _ _) fun q ⟨tb, hq⟩ =>
    Post.mono (post_true _) fun _ _ => ⟨ta, p, tb, q, hp, hq⟩

theorem post_pureOp (cx : Scc.Lower.Ctx) (env : Env) (x : String) {op : Op} (hp : isPure op = true) :
    Post (lowerOp cx env x op) fun v => pureOp env op = some v := by
  cases op with
  | atom a => exact post_evalAtV env a
  | nameI a => exact post_evalAtV env a
  | pack a i τ =>
    simp only [lowerOp]
    exact Post.bind (post_evalAtV env a) fun r hr => Post.pure (by simp [pureOp, hr])
  | pair a b =>
    simp only [lowerOp]
    exact Post.bind (post_evalAtV env a) fun r hr => Post.bind (post_evalAtV env b) fun r' hr' =>
      Post.pure (by simp [pureOp, hr, hr'])
  | asLanes sg w a =>
    simp only [lowerOp]
    exact Post.bind (post_evalOneV env a _) fun p ⟨t, hp⟩ => Post.pure (by simp [pureOp, hp])
  | _ => simp [isPure] at hp

/-- A call's operand (`evalAt`), with any property `P` of its successful runs. -/
theorem post_call_arg (cx : Scc.Lower.Ctx) (env : Env) (x g : String) (is : List String) (a : At) (ts : List Ty)
    {P : Ty × List Operand → Prop} (hP : Post (evalAt env a) P) :
    Post (lowerOp cx env x (.call g is a ts)) fun _ => ∃ v, P v := by
  simp only [lowerOp]
  exact Post.bind' fun _ => Post.bind hP fun v hv => Post.mono (post_true _) fun _ _ => ⟨v, hv⟩

theorem post_newBuf2 (cx : Scc.Lower.Ctx) (env : Env) (x : String) (c : At) (τ : Ty) :
    Post (lowerOp cx env x (.newBuf c τ)) fun _ => ∃ tk w en em h, atomV env c = some (tk, [w]) ∧
      countsO cx.obj τ = some (en, em) ∧ Scc.Obj.header0 cx.obj .array en em = some h ∧
      en + em ≤ 2 * (Scc.Frontend.words τ).getD (en + em) := by
  simp only [lowerOp]
  refine Post.bind (post_evalOneV _ _ _) fun w ⟨tk, hw⟩ => ?_
  refine Post.bind (post_countsOf _ _) fun c hc => ?_
  obtain ⟨en, em⟩ := c
  refine Post.bind (post_header _ _ _ _) fun h hh => Post.bind' fun _ => ?_
  by_cases hle : en + em ≤ 2 * (Scc.Frontend.words τ).getD (en + em)
  · exact Post.mono (post_true _) fun _ _ => ⟨tk, w, en, em, h, hw, hc, hh, hle⟩
  · simp only [hle, ite_false]
    first
      | exact Post.throw
      | exact Post.bind Post.throw fun _ _ => Post.throw
      | exact Post.bind' fun _ => Post.throw

theorem post_xchg2 (cx : Scc.Lower.Ctx) (env : Env) (x : String) (b i v : At) :
    Post (lowerOp cx env x (.xchgAt b i v)) fun _ => ∃ t bw tj j μ u r sl tv vs, atomV env b = some (t, bw) ∧
      atomV env i = some (tj, [j]) ∧ bufElem t = some (μ, u) ∧ Scc.Obj.regOf u = some r ∧
      Scc.Obj.slots u 0 0 = some sl ∧ atomV env v = some (tv, vs) ∧ sl.length = vs.length := by
  simp only [lowerOp]
  refine Post.bind (post_evalAtV _ _) fun ⟨t, bw⟩ hb => Post.bind' fun ⟨base, off⟩ => ?_
  refine Post.bind (post_evalOneV _ _ _) fun j ⟨tj, hj⟩ => ?_
  refine Post.bind (post_needSome _ _) fun ⟨μ, u⟩ he => ?_
  refine Post.bind (post_slotLoc _ _ _ _) fun ⟨base', off'⟩ ⟨r, hr⟩ => ?_
  refine Post.bind (post_evalAtV _ _) fun ⟨tv, vs⟩ hv => ?_
  refine Post.bind (post_cellAddrs _ _ _ _) fun as ⟨sl, hsl, hl⟩ => Post.bind' fun _ => ?_
  refine Post.bind (post_storeAt _ _ _) fun _ hst => Post.mono (post_true _) fun _ _ =>
    ⟨t, bw, tj, j, μ, u, r, sl, tv, vs, hb, hj, he, hr, hsl, hv, by rw [← hl, hst]⟩

/-! ## Invariants along the walk -/

/-- **A value known before run time is one immediate**: every variable of
`cs` (`body2`'s known values) is bound to one immediate word. -/
def CsW (env : Env) (cs : List (String × Nat)) : Prop :=
  ∀ x k, cs.lookup x = some k → ∃ b v, env.find? (·.1 == x) = some b ∧ b.2.2 = [.imm v]

/-- **A buffer is a register base and an immediate offset**: every variable
of `bufs` (`body2`'s buffers). -/
def BufW (env : Env) (bufs : List (String × Nat)) : Prop :=
  ∀ x k, bufs.lookup x = some k → ∃ b q o, env.find? (·.1 == x) = some b ∧ b.2.2 = [.reg q, .imm o]

/-- The words at a layout's locative positions (`flatL`'s `none`) are
registers. -/
def LocW : List Operand → List (Option (Option Nat)) → Prop
  | [], [] => True
  | w :: ws, f :: fs => (f = none → IsReg w) ∧ LocW ws fs
  | _, _ => False

/-- **Every bound locative's words are registers**, against the walk's
layout `lits`. -/
def LocR (env : Env) (lits : List (String × LitV)) : Prop :=
  ∀ x b L, env.find? (·.1 == x) = some b → lits.lookup x = some L → LocW b.2.2 (flatL L)

/-- A call's operand layout against its callee's parameter layout
(`callsOk2`'s check at one point). -/
def callQ (p : Prog) (q : Expr × List (String × LitV)) : Bool :=
  match q.1 with
  | .let_ _ (.call g _ a _) _ => (litAt q.2 a).erase == argShape p g
  | _ => true

theorem LocW.append : ∀ {a c : List Operand} {b d : List (Option (Option Nat))}, LocW a b → LocW c d →
    LocW (a ++ c) (b ++ d)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, h, h' => ⟨h.1, h.2.append h'⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem LocW.take_drop : ∀ {ws : List Operand} {c d : List (Option (Option Nat))}, LocW ws (c ++ d) →
    LocW (ws.take c.length) c ∧ LocW (ws.drop c.length) d
  | ws, [], d, h => ⟨by cases ws <;> trivial, by simpa using h⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, _ :: _, _, h => by
    obtain ⟨h1, h2⟩ := LocW.take_drop h.2
    exact ⟨⟨h.1, h1⟩, h2⟩

theorem locW_of_regs : ∀ {ws : List Operand} {fs : List (Option (Option Nat))}, (∀ w ∈ ws, IsReg w) →
    AgreeW ws fs → LocW ws fs
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, h, ha =>
    ⟨fun _ => h _ (List.mem_cons_self ..), locW_of_regs (fun w hw => h w (List.mem_cons_of_mem _ hw)) ha.2⟩
  | [], _ :: _, _, ha => ha.elim
  | _ :: _, [], _, ha => ha.elim

theorem LocR.cons {env : Env} {lits : List (String × LitV)} (h : LocR env lits) {x : String} {t : Ty}
    {ws : List Operand} {L : LitV} (hw : LocW ws (flatL L)) : LocR ((x, t, ws) :: env) ((x, L) :: lits) := by
  intro y b L' hb hL
  rw [find?_cons_name] at hb
  rw [lookup_cons_name] at hL
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, Option.some.injEq] at hb hL
    subst hb hL
    exact hw
  · simp only [hxy, ↓reduceIte, Ne.symm hxy] at hb hL
    exact h y b L' hb hL

theorem CsW.sub {env : Env} {cs : List (String × Nat)} (h : CsW env cs) (i : String) : CsW env (unbuf i cs) := by
  intro y k hy
  rw [lookup_unbuf] at hy
  split at hy
  · cases hy
  · exact h y k hy

theorem CsW.cons {env : Env} {cs : List (String × Nat)} (h : CsW env cs) (x : String) (t : Ty)
    (ws : List Operand) : CsW ((x, t, ws) :: env) (unbuf x cs) := by
  intro y k hy
  rw [lookup_unbuf] at hy
  split at hy
  · cases hy
  · rename_i hyx
    obtain ⟨b, v, hb, hv⟩ := h y k hy
    exact ⟨b, v, by rw [find?_cons_name]; simp only [Ne.symm hyx, ↓reduceIte]; exact hb, hv⟩

theorem CsW.bind {env : Env} {cs : List (String × Nat)} (h : CsW env cs) (x : String) (t : Ty)
    {ws : List Operand} {o : Option Nat} (hw : ∀ k, o = some k → ∃ v, ws = [.imm v]) :
    CsW ((x, t, ws) :: env) (bindC x o cs) := by
  cases o with
  | none => exact h.cons x t ws
  | some k =>
    intro y k' hy
    simp only [bindC] at hy
    rw [lookup_cons_name] at hy
    split at hy
    · rename_i hyx
      subst hyx
      obtain ⟨v, hv⟩ := hw k rfl
      exact ⟨(y, t, ws), v, by rw [find?_cons_name]; simp, hv⟩
    · exact h.cons x t ws y k' hy

theorem BufW.sub {env : Env} {bufs : List (String × Nat)} (h : BufW env bufs) (i : String) :
    BufW env (unbuf i bufs) := by
  intro y k hy
  rw [lookup_unbuf] at hy
  split at hy
  · cases hy
  · exact h y k hy

theorem BufW.cons {env : Env} {bufs : List (String × Nat)} (h : BufW env bufs) (x : String) (t : Ty)
    (ws : List Operand) : BufW ((x, t, ws) :: env) (unbuf x bufs) := by
  intro y k hy
  rw [lookup_unbuf] at hy
  split at hy
  · cases hy
  · rename_i hyx
    obtain ⟨b, q, o, hb, hv⟩ := h y k hy
    exact ⟨b, q, o, by rw [find?_cons_name]; simp only [Ne.symm hyx, ↓reduceIte]; exact hb, hv⟩

theorem BufW.new {env : Env} {bufs : List (String × Nat)} (h : BufW env bufs) (x : String) (t : Ty)
    (q : Reg) (o : UInt64) (k : Nat) : BufW ((x, t, [.reg q, .imm o]) :: env) ((x, k) :: unbuf x bufs) := by
  intro y k' hy
  rw [lookup_cons_name] at hy
  split at hy
  · rename_i hyx
    subst hyx
    exact ⟨(y, t, [.reg q, .imm o]), q, o, by rw [find?_cons_name]; simp, rfl⟩
  · exact h.cons x t _ y k' hy

theorem atomV_var {env : Env} {y : String} {v : Ty × List Operand} (h : atomV env (.var y) = some v) :
    ∃ b, env.find? (·.1 == y) = some b ∧ v = (b.2.1, b.2.2) := by
  simp only [atomV, Option.map_eq_some_iff] at h
  obtain ⟨⟨z, t, ws⟩, hf, rfl⟩ := h
  exact ⟨_, hf, rfl⟩

theorem atomV_lit {env : Env} {n : Nat} {v : Ty × List Operand} (h : atomV env (.lit n) = some v) :
    v = (.intS (.lit n), [imm n]) := by
  simp only [atomV] at h
  split at h
  · cases h
  · exact (Option.some.inj h).symm

/-- A value known before run time (`constOf`) is one immediate. -/
theorem atomV_const {env : Env} {cs : List (String × Nat)} (hc : CsW env cs) {a : At} {k : Nat}
    (hk : constOf cs a = some k) {t : Ty} {ws : List Operand} (ha : atomV env a = some (t, ws)) :
    ∃ v, ws = [.imm v] := by
  cases a with
  | var y =>
    obtain ⟨b, hb, hv⟩ := atomV_var ha
    obtain ⟨b', v, hb', hw⟩ := hc y k hk
    rw [hb] at hb'; cases hb'
    cases hv
    exact ⟨v, hw⟩
  | lit n =>
    have := atomV_lit ha
    cases this
    exact ⟨_, rfl⟩
  | unit => simp [constOf] at hk

/-- An atom's words against its layout: its locative words registers. -/
theorem locW_atom {env : Env} {lits : List (String × LitV)} {scope : List String} (hR : Rel env lits scope)
    (hL : LocR env lits) {a : At} (ha : ∀ y, a = .var y → y ∈ scope) {t : Ty} {ws : List Operand}
    (hv : atomV env a = some (t, ws)) : LocW ws (flatL (litAt lits a)) := by
  cases a with
  | var y =>
    obtain ⟨b, hb, hbv⟩ := atomV_var hv
    cases hbv
    obtain ⟨L, hL'⟩ := Option.isSome_iff_exists.1 (hR.2 y (ha y rfl))
    simp only [litAt, hL', Option.getD_some]
    exact hL y b L hb hL'
  | lit n =>
    have := atomV_lit hv
    cases this
    exact ⟨fun h => (by cases h), trivial⟩
  | unit =>
    simp only [atomV, Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨-, rfl⟩ := hv
    trivial

/-- A one-word layout (`Int`'s) has one word. -/
theorem one_word {L : LitV} (he : L.erase = .leaf none) {ws : List Operand} (hA : AgreeW ws (flatL L)) :
    ∃ w, ws = [w] := by
  cases L <;> simp [LitV.erase] at he
  rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp [flatL, AgreeW] at hA
  exact ⟨w, rfl⟩

theorem shapeOf_ownSlice :
    shapeOf Scc.Frontend.ownSliceTy = .node (.node .loc (.leaf none)) (.leaf none) := rfl

/-- **The owned slice's words**: four, its offset word a register when its
locative words are. -/
theorem slice_words {L : LitV} (he : L.erase = shapeOf Scc.Frontend.ownSliceTy) {ws : List Operand}
    (hA : AgreeW ws (flatL L)) (hW : LocW ws (flatL L)) : ∃ b o m c, ws = [b, .reg o, m, c] := by
  rw [shapeOf_ownSlice] at he
  rcases L with _ | _ | _ | ⟨_ | _ | _ | ⟨l1, l2⟩, r⟩ <;> simp [LitV.erase] at he
  obtain ⟨⟨h1, h2⟩, h3⟩ := he
  cases l1 <;> simp [LitV.erase] at h1
  cases l2 <;> simp [LitV.erase] at h2
  cases r <;> simp [LitV.erase] at h3
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp [flatL, AgreeW] at hA
  obtain ⟨o, rfl⟩ := hW.2.1 rfl
  exact ⟨w0, o, w2, w3, rfl⟩

theorem pureOp_pair {env : Env} {a b : At} {v : Ty × List Operand} (h : pureOp env (.pair a b) = some v) :
    ∃ t ws u us, atomV env a = some (t, ws) ∧ atomV env b = some (u, us) ∧ v = (.prod t u, ws ++ us) := by
  simp only [pureOp] at h
  cases ha : atomV env a with
  | none => simp [ha] at h
  | some q =>
    obtain ⟨t, ws⟩ := q
    cases hb : atomV env b with
    | none => simp [ha, hb] at h
    | some q' =>
      obtain ⟨u, us⟩ := q'
      simp [ha, hb] at h
      exact ⟨t, ws, u, us, rfl, rfl, h.symm⟩

theorem pureOp_pack {env : Env} {a : At} {i : String} {τ : Ty} {v : Ty × List Operand}
    (h : pureOp env (.pack a i τ) = some v) : ∃ t ws, atomV env a = some (t, ws) ∧ v = (τ, ws) := by
  simp only [pureOp, Option.map_eq_some_iff] at h
  obtain ⟨⟨t, ws⟩, ha, rfl⟩ := h
  exact ⟨t, ws, ha, rfl⟩

theorem pureOp_asLanes {env : Env} {sg : Bool} {w : Wd} {a : At} {v : Ty × List Operand}
    (h : pureOp env (.asLanes sg w a) = some v) : ∃ t o, atomV env a = some (t, [o]) ∧ v = (.lanes sg w, [o]) := by
  simp only [pureOp] at h
  cases ha : atomV env a with
  | none => simp [ha] at h
  | some q =>
    obtain ⟨t, ws⟩ := q
    rcases ws with _ | ⟨o, _ | ⟨_, _⟩⟩ <;> simp [ha] at h
    exact ⟨t, o, rfl, h.symm⟩

/-! ## `lowerC2` from `lowerExpr` -/

/-- **`lowerC2` is defined where `lowerExpr` succeeds** (no depth counter)
on a `body2` body (context `cx2`), its environment against the walk's
literal layout (`Rel`, `BufInv`), known values immediates (`CsW`), buffers
a register base and an immediate offset (`BufW`), locatives in registers
outside the setup block (`LocR`), every point of the walk with its layout
and call checks (`layQ`, `callQ`), from an open block; `hU`: an ordinary
callee is a code block `Int → Int`, not an extern; `hP`: where the extern
may be called, not in the setup block, the extern is `ownSliceTy → Unit`. -/
theorem lowerC2_isSome {cx : Scc.Lower.Ctx} (hf : cx.frames = none) {p : Prog} (hcx : CxOK cx p) {cx2 : Cx2}
    (hU : ∀ g, callee2 cx2 g = true → cx.externs.find? (·.1 == g) = none ∧
      ∃ dg, p.find? (·.name == g) = some dg ∧ dg.retTy = .int ∧ dg.argTy = .int)
    (hP : cx2.ext = true → cx2.earlier.contains "print" = true → cx2.alloc = false ∧
      (cx.externs.find? (·.1 == "print")).isSome = true ∧
      ∃ dp, p.find? (·.name == "print") = some dp ∧ dp.retTy = .unit ∧ dp.argTy = Scc.Frontend.ownSliceTy) :
    ∀ (e : Expr) (cs bufs : List (String × Nat)) (scope : List String) (env : Env)
      (lits : List (String × LitV)) (s s' : BState),
      body2 cx2 cs bufs scope e = true → Rel env lits scope → BufInv env bufs → BufW env bufs → CsW env cs →
      (cx2.alloc = false → LocR env lits) → (∀ q ∈ litWalk2 p lits e, layQ q = true ∧ callQ p q = true) →
      s.cur.isSome = true → lowerExpr cx env e s = .ok ((), s') →
      ∀ l k, (lowerC2 cx env s.next l k e).isSome = true := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro cs bufs scope env lits s s' hb hR hB hBW hCs hLoc hW hcur h l k
    obtain ⟨⟨l0, is0⟩, hc⟩ := Option.isSome_iff_exists.1 hcur
    have hW0 := hW _ (by rw [litWalk2]; exact List.mem_cons_self ..)
    have hWt : ∀ q ∈ litWalk2 p ((x, opLit p lits op) :: lits) e, layQ q = true ∧ callQ p q = true :=
      fun q hq => hW q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)
    obtain ⟨_, _, -, hpost⟩ := let_step hcx hb hR hB hW0.1
    have hc1 : ({ s with here := some (env, Expr.let_ x op e) } : BState).cur = some (l0, is0) := hc
    cases op with
    | add a b =>
      simp only [body2, Bool.and_eq_true] at hb
      rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
      obtain ⟨⟨t0, ws0⟩, s2, h1, -⟩ := bind_ok_inv h
      have hQ := hpost _ _ _ h1
      obtain ⟨ta, pa, tb, qb, ha, hb'⟩ := post_add2 cx env x a b _ _ _ h1
      have hf1 := lowerOp_add cx env x ha hb' hc1
      rw [hf1] at h1; cases h1
      rw [bind_ok hf1, bind_ok (markWords_scalar1 rfl _)] at h
      have hI := ih _ _ _ _ _ _ _ hb.2 (hR.cons hQ.1) (hB.cons x _ _) (hBW.cons x _ _) (hCs.cons x _ _)
        (fun h0 => (hLoc h0).cons (locW_of_regs (by simp [IsReg]) hQ.1.2)) hWt (by simp [hc]) h l (k + 1)
      dsimp only at hI
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
      simp [lowerC2, ha, hb', hr']
    | sub a b =>
      simp only [body2, Bool.and_eq_true] at hb
      rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
      obtain ⟨⟨t0, ws0⟩, s2, h1, -⟩ := bind_ok_inv h
      have hQ := hpost _ _ _ h1
      obtain ⟨ta, pa, tb, qb, ha, hb'⟩ := post_sub2 cx env x a b _ _ _ h1
      have hf1 := lowerOp_sub cx env x ha hb' hc1
      rw [hf1] at h1; cases h1
      rw [bind_ok hf1, bind_ok (markWords_scalar1 rfl _)] at h
      have hI := ih _ _ _ _ _ _ _ hb.2 (hR.cons hQ.1) (hB.cons x _ _) (hBW.cons x _ _) (hCs.cons x _ _)
        (fun h0 => (hLoc h0).cons (locW_of_regs (by simp [IsReg]) hQ.1.2)) hWt (by simp [hc]) h l (k + 1)
      dsimp only at hI
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
      simp [lowerC2, ha, hb', hr']
    | call g is' a ts =>
      simp only [body2, Bool.and_eq_true] at hb
      obtain ⟨⟨hsel, ha1⟩, hbe⟩ := hb
      have hcq : (litAt lits a).erase = argShape p g := by simpa [callQ] using hW0.2
      rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
      obtain ⟨⟨t0, ws0⟩, s2, h1, -⟩ := bind_ok_inv h
      have hQ := hpost _ _ _ h1
      obtain ⟨⟨t, ws⟩, hav, hInv⟩ := post_call_arg cx env x g is' a ts
        (Post.and (post_evalAtV env a) (post_evalAt hR (atom1_var ha1))) _ _ _ h1
      split at hsel
      · rename_i hpr
        simp only [Bool.and_eq_true] at hsel
        simp only [Bool.and_eq_true, beq_iff_eq] at hpr
        obtain ⟨hext, rfl⟩ := hpr
        obtain ⟨halloc, hxs, dp, hdp, hrt, hat⟩ := hP hext hsel.1.1
        obtain ⟨xe, hx⟩ := Option.isSome_iff_exists.1 hxs
        have hdp' : cx.prog.find? (·.name == "print") = some dp := by rw [hcx.prog]; exact hdp
        have hsh : (litAt lits a).erase = shapeOf Scc.Frontend.ownSliceTy := by
          rw [hcq, ← hat]; simp [argShape, hdp]
        obtain ⟨b, o, m, c, rfl⟩ := slice_words hsh hInv.2 (locW_atom hR (hLoc halloc) (atom1_var ha1) hav)
        have hf1 := lowerOp_print cx env x "print" is' ts hx hdp' hrt hav hc1 rfl
        rw [hf1] at h1; cases h1
        rw [bind_ok hf1] at h
        simp only [hx, Option.isNone_some, Bool.false_eq_true, ite_false] at h
        have hmw : ∀ s : BState, markWords .unit [] s = .ok ((), s) := fun _ => rfl
        rw [bind_ok (hmw _)] at h
        have hI := ih _ _ _ _ _ _ _ hbe (hR.cons hQ.1) (hB.cons x _ _) (hBW.cons x _ _) (hCs.cons x _ _)
          (fun h0 => (hLoc h0).cons (locW_of_regs (by simp) hQ.1.2)) hWt (by simp [hc]) h l (k + 5)
        dsimp only at hI
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
        simp [lowerC2, hx, hdp', hrt, hav, hr']
      · simp only [Bool.and_eq_true] at hsel
        obtain ⟨hx, dg, hdg, hrt, hat⟩ := hU g hsel.1.1
        have hdg' : cx.prog.find? (·.name == g) = some dg := by rw [hcx.prog]; exact hdg
        have hsh : (litAt lits a).erase = .leaf none := by rw [hcq]; simp [argShape, hdg, hat, shapeOf]
        obtain ⟨w, rfl⟩ := one_word hsh hInv.2
        have hf1 := lowerOp_call (is' := is') (ts := ts) env x g hdg' hrt hav (callBlock_none g w hf hx hc1 rfl)
        rw [hf1] at h1; cases h1
        rw [bind_ok hf1] at h
        simp only [hx, Option.isNone_none, ite_true] at h
        rw [get_bind] at h
        simp only [markOp_back] at h
        rw [bind_ok (markAt_eq _ _ _), bind_ok (markWords_scalar1 rfl _)] at h
        have hI := ih _ _ _ _ _ _ _ hbe (hR.cons hQ.1) (hB.cons x _ _) (hBW.cons x _ _) (hCs.cons x _ _)
          (fun h0 => (hLoc h0).cons (locW_of_regs (by simp [IsReg]) hQ.1.2)) hWt (by simp [hc]) h l (k + 1)
        dsimp only at hI
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
        simp [lowerC2, hx, hdg', hrt, hav, hr']
    | newBuf c τ =>
      simp only [body2, Bool.and_eq_true] at hb
      obtain ⟨⟨⟨halloc, -⟩, hτ⟩, hm⟩ := hb
      split at hm
      · rename_i kk hkk
        simp only [Bool.and_eq_true] at hm
        rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
        obtain ⟨⟨t0, ws0⟩, s2, h1, -⟩ := bind_ok_inv h
        have hQ := hpost _ _ _ h1
        obtain ⟨tk, w, en, em, hh, hcv, hcn, hhh, hw⟩ := post_newBuf2 cx env x c τ _ _ _ h1
        obtain ⟨kv, hkv⟩ := atomV_const hCs hkk hcv
        simp only [List.cons.injEq, and_true] at hkv
        subst hkv
        have hf1 := lowerOp_newBuf cx env x hcv hcn hhh hw hc1 rfl
        rw [hf1] at h1; cases h1
        rw [bind_ok hf1] at h
        obtain ⟨_, _, hmw, -⟩ := bind_ok_inv h
        obtain ⟨sc, hq, hmr⟩ := post_markWords _ _ _ _ _ hmw
        rw [bind_ok (markWords_eq hmr _)] at h
        have hI := ih _ _ _ _ _ _ _ hm.2 (hR.cons hQ.1) (hB.new x hτ _ kk) (hBW.new x _ _ _ kk) (hCs.cons x _ _)
          (fun h0 => by rw [halloc] at h0; cases h0) hWt (by simp [hc]) h l (k + 1)
        dsimp only at hI
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
        simp [lowerC2, hcv, hcn, hhh, hw, hmr, hr']
      · cases hm
    | xchgAt b i v =>
      rcases b with b | b | _ <;> rcases i with i | i | _ <;> try (simp [body2] at hb; done)
      simp only [body2, Bool.and_eq_true] at hb
      obtain ⟨⟨⟨-, hk⟩, -⟩, hbc⟩ := hb
      split at hk
      · rename_i kk hbk
        obtain ⟨e0, τ, he0, ht0, hτ⟩ := hB b kk hbk
        obtain ⟨e1, q, o, he1, hw1⟩ := hBW b kk hbk
        rw [he0] at he1; cases he1
        rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
        obtain ⟨⟨t0, ws0⟩, s2, h1, -⟩ := bind_ok_inv h
        have hQ := hpost _ _ _ h1
        obtain ⟨t, bw, tj, j, μ, u, r, sl, tv, vs, hbv, hiv, hbe, hr, hsl, hvv, hlen⟩ :=
          post_xchg2 cx env x _ _ v _ _ _ h1
        obtain ⟨b0, hb0, hbt⟩ := atomV_var hbv
        rw [he0] at hb0; cases hb0
        simp only [Prod.mk.injEq] at hbt
        obtain ⟨rfl, rfl⟩ := hbt
        rw [ht0] at hbe
        simp only [bufTy, bufElem, Option.some.injEq, Prod.mk.injEq] at hbe
        obtain ⟨rfl, rfl⟩ := hbe
        have hj := atomV_lit hiv
        simp only [Prod.mk.injEq, List.cons.injEq, and_true] at hj
        obtain ⟨rfl, rfl⟩ := hj
        have hs1 : sl = [(false, 0)] := by
          cases τ <;> simp [elem2] at hτ <;> simp [Scc.Obj.slots] at hsl <;> first | exact hsl.symm | exact hsl
        subst hs1
        obtain ⟨w, rfl⟩ : ∃ w, vs = [w] := by
          rcases vs with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp at hlen
          exact ⟨w, rfl⟩
        obtain ⟨nu, mu⟩ := r
        have hbe' : bufElem e0.2.1 = some (.own, τ) := by rw [ht0]; rfl
        have hrf : refO e0.2.2 = some (.reg q, .imm o) := by rw [hw1]; rfl
        have hf1 := lowerOp_xchg cx env x hbv hrf hiv hbe' hr hvv hsl hc1
        rw [hf1] at h1; cases h1
        rw [bind_ok hf1] at h
        obtain ⟨_, _, hmw, -⟩ := bind_ok_inv h
        obtain ⟨sc, hq', hmr⟩ := post_markWords _ _ _ _ _ hmw
        rw [bind_ok (markWords_eq hmr _)] at h
        have hI := ih _ _ _ _ _ _ _ hbc (hR.cons hQ.1) (hB.cons x _ _) (hBW.cons x _ _) (hCs.cons x _ _)
          (fun h0 => (hLoc h0).cons (locW_of_regs (by simp [IsReg]) hQ.1.2)) hWt (by simp [hc]) h l (k + 2)
        dsimp only at hI
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
        simp [lowerC2, hbv, hrf, hiv, hbe', hr, hvv, hsl, hmr, hr', imm]
      · cases hk
    | atom a =>
      simp only [body2, Bool.and_eq_true] at hb
      rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
      obtain ⟨⟨t0, ws0⟩, s2, h1, -⟩ := bind_ok_inv h
      have hQ := hpost _ _ _ h1
      have hv : atomV env a = some (t0, ws0) := post_pureOp cx env x (op := .atom a) rfl _ _ _ h1
      have hf1 := lowerOp_pure cx env x (op := .atom a) rfl hv { s with here := some (env, .let_ x (.atom a) e) }
      rw [hf1] at h1; cases h1
      rw [bind_ok hf1] at h
      obtain ⟨_, _, hmw, -⟩ := bind_ok_inv h
      obtain ⟨sc, hq, hmr⟩ := post_markWords _ _ _ _ _ hmw
      rw [bind_ok (markWords_eq hmr _)] at h
      have hI := ih _ _ _ _ _ _ _ hb.2 (hR.cons hQ.1) (hB.cons x _ _) (hBW.cons x _ _)
        (hCs.bind x _ fun _ hk => atomV_const hCs hk hv)
        (fun h0 => (hLoc h0).cons (locW_atom hR (hLoc h0) (atom1_var hb.1) hv)) hWt (by simp [hc]) h l k
      dsimp only at hI
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
      rw [lowerC2_let_pure rfl]
      simp [pureOp, hv, hmr, hr']
    | nameI a =>
      simp only [body2, Bool.and_eq_true] at hb
      rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
      obtain ⟨⟨t0, ws0⟩, s2, h1, -⟩ := bind_ok_inv h
      have hQ := hpost _ _ _ h1
      have hv : atomV env a = some (t0, ws0) := post_pureOp cx env x (op := .nameI a) rfl _ _ _ h1
      have hf1 := lowerOp_pure cx env x (op := .nameI a) rfl hv { s with here := some (env, .let_ x (.nameI a) e) }
      rw [hf1] at h1; cases h1
      rw [bind_ok hf1] at h
      obtain ⟨_, _, hmw, -⟩ := bind_ok_inv h
      obtain ⟨sc, hq, hmr⟩ := post_markWords _ _ _ _ _ hmw
      rw [bind_ok (markWords_eq hmr _)] at h
      have hI := ih _ _ _ _ _ _ _ hb.2 (hR.cons hQ.1) (hB.cons x _ _) (hBW.cons x _ _)
        (hCs.bind x _ fun _ hk => atomV_const hCs hk hv)
        (fun h0 => (hLoc h0).cons (locW_atom hR (hLoc h0) (atom1_var hb.1) hv)) hWt (by simp [hc]) h l k
      dsimp only at hI
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
      rw [lowerC2_let_pure rfl]
      simp [pureOp, hv, hmr, hr']
    | pack a i' τ =>
      simp only [body2, Bool.and_eq_true] at hb
      rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
      obtain ⟨⟨t0, ws0⟩, s2, h1, -⟩ := bind_ok_inv h
      have hQ := hpost _ _ _ h1
      have hv := post_pureOp cx env x (op := .pack a i' τ) rfl _ _ _ h1
      have hf1 := lowerOp_pure cx env x (op := .pack a i' τ) rfl hv
        { s with here := some (env, .let_ x (.pack a i' τ) e) }
      rw [hf1] at h1; cases h1
      rw [bind_ok hf1] at h
      obtain ⟨_, _, hmw, -⟩ := bind_ok_inv h
      obtain ⟨sc, hq, hmr⟩ := post_markWords _ _ _ _ _ hmw
      rw [bind_ok (markWords_eq hmr _)] at h
      obtain ⟨ta, wa, hav, hvv⟩ := pureOp_pack hv
      simp only [Prod.mk.injEq] at hvv
      obtain ⟨rfl, rfl⟩ := hvv
      have hI := ih _ _ _ _ _ _ _ hb.2 (hR.cons hQ.1) (hB.cons x _ _) (hBW.cons x _ _) (hCs.cons x _ _)
        (fun h0 => (hLoc h0).cons (locW_atom hR (hLoc h0) (atom1_var hb.1) hav)) hWt (by simp [hc]) h l k
      dsimp only at hI
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
      rw [lowerC2_let_pure rfl]
      simp [hv, hmr, hr']
    | pair a b =>
      simp only [body2, Bool.and_eq_true] at hb
      rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
      obtain ⟨⟨t0, ws0⟩, s2, h1, -⟩ := bind_ok_inv h
      have hQ := hpost _ _ _ h1
      have hv := post_pureOp cx env x (op := .pair a b) rfl _ _ _ h1
      have hf1 := lowerOp_pure cx env x (op := .pair a b) rfl hv { s with here := some (env, .let_ x (.pair a b) e) }
      rw [hf1] at h1; cases h1
      rw [bind_ok hf1] at h
      obtain ⟨_, _, hmw, -⟩ := bind_ok_inv h
      obtain ⟨sc, hq, hmr⟩ := post_markWords _ _ _ _ _ hmw
      rw [bind_ok (markWords_eq hmr _)] at h
      obtain ⟨ta, wa, tb, wb, hav, hbv, hvv⟩ := pureOp_pair hv
      simp only [Prod.mk.injEq] at hvv
      obtain ⟨rfl, rfl⟩ := hvv
      have hI := ih _ _ _ _ _ _ _ hb.2 (hR.cons hQ.1) (hB.cons x _ _) (hBW.cons x _ _) (hCs.cons x _ _)
        (fun h0 => (hLoc h0).cons ((locW_atom hR (hLoc h0) (atom1_var hb.1.1) hav).append
          (locW_atom hR (hLoc h0) (atom1_var hb.1.2) hbv))) hWt (by simp [hc]) h l k
      dsimp only at hI
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
      rw [lowerC2_let_pure rfl]
      simp [hv, hmr, hr']
    | asLanes sg w a =>
      simp only [body2, Bool.and_eq_true] at hb
      rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
      obtain ⟨⟨t0, ws0⟩, s2, h1, -⟩ := bind_ok_inv h
      have hQ := hpost _ _ _ h1
      have hv := post_pureOp cx env x (op := .asLanes sg w a) rfl _ _ _ h1
      have hf1 := lowerOp_pure cx env x (op := .asLanes sg w a) rfl hv
        { s with here := some (env, .let_ x (.asLanes sg w a) e) }
      rw [hf1] at h1; cases h1
      rw [bind_ok hf1] at h
      obtain ⟨_, _, hmw, -⟩ := bind_ok_inv h
      obtain ⟨sc, hq, hmr⟩ := post_markWords _ _ _ _ _ hmw
      rw [bind_ok (markWords_eq hmr _)] at h
      obtain ⟨ta, o, hav, hvv⟩ := pureOp_asLanes hv
      simp only [Prod.mk.injEq] at hvv
      obtain ⟨rfl, rfl⟩ := hvv
      have hI := ih _ _ _ _ _ _ _ hb.2 (hR.cons hQ.1) (hB.cons x _ _) (hBW.cons x _ _) (hCs.cons x _ _)
        (fun h0 => (hLoc h0).cons ⟨fun h => (by cases h), trivial⟩) hWt (by simp [hc]) h l k
      dsimp only at hI
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
      rw [lowerC2_let_pure rfl]
      simp [hv, hmr, hr']
    | _ => simp [body2] at hb
  | split a x y e ih =>
    intro cs bufs scope env lits s s' hb hR hB hBW hCs hLoc hW hcur h l k
    obtain ⟨⟨l0, is0⟩, hc⟩ := Option.isSome_iff_exists.1 hcur
    simp only [body2, Bool.and_eq_true] at hb
    rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
    obtain ⟨⟨t, ws⟩, s2, h1, h⟩ := bind_ok_inv h
    have hI0 := post_evalAt hR (atom1_var hb.1) _ _ _ h1
    obtain ⟨hav, rfl⟩ := evalAt_inv h1
    obtain ⟨⟨u, w⟩, s3, h2, h⟩ := bind_ok_inv h
    obtain ⟨hpu, rfl⟩ := needSome_inv h2
    obtain ⟨nu, s4, h3, h⟩ := bind_ok_inv h
    obtain ⟨hnu, rfl⟩ := words_inv h3
    obtain ⟨L1, L2, hla, hc1, hc2⟩ := compat_prodOf hpu hI0.1
    have hk : nu = (flatL L1).length := by
      have := valWords_compat hc1
      rw [hnu] at this
      exact Option.some.inj this
    have hA := hI0.2
    simp only at hA
    rw [hla] at hA
    obtain ⟨hA1, hA2⟩ := AgreeW.take_drop (c := flatL L1) (d := flatL L2) hA
    subst hk
    have hlw : litWalk2 p lits (.split a x y e) =
        (.split a x y e, lits) :: litWalk2 p ((y, L2) :: (x, L1) :: lits) e := by
      rw [litWalk2, hla]
    have hI := ih _ _ _ _ _ _ _ hb.2 ((hR.cons ⟨hc1, hA1⟩).cons ⟨hc2, hA2⟩) ((hB.cons x _ _).cons y _ _)
      ((hBW.cons x _ _).cons y _ _) ((hCs.cons x _ _).cons y _ _)
      (fun h0 => by
        have hl := locW_atom hR (hLoc h0) (atom1_var hb.1) hav
        rw [hla] at hl
        obtain ⟨hl1, hl2⟩ := LocW.take_drop (c := flatL L1) (d := flatL L2) hl
        exact ((hLoc h0).cons hl1).cons hl2)
      (fun q hq => hW q (by rw [hlw]; exact List.mem_cons_of_mem _ hq)) (by simp [hc]) h l k
    dsimp only at hI
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
    simp [lowerC2, hav, hpu, hnu, hr']
  | unpack a i x e ih =>
    intro cs bufs scope env lits s s' hb hR hB hBW hCs hLoc hW hcur h l k
    obtain ⟨⟨l0, is0⟩, hc⟩ := Option.isSome_iff_exists.1 hcur
    simp only [body2, Bool.and_eq_true] at hb
    rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
    obtain ⟨⟨t, ws⟩, s2, h1, h⟩ := bind_ok_inv h
    have hI0 := post_evalAt hR (atom1_var hb.1) _ _ _ h1
    obtain ⟨hav, rfl⟩ := evalAt_inv h1
    cases t with
    | iex b =>
      have hIb : Spike.Lib.LowerNode.Inv b ws (litAt lits a) := ⟨by
        have := hI0.1; simp only [Compat, Bool.and_eq_true] at this; exact this.2, hI0.2⟩
      have hI := ih _ _ _ _ _ _ _ hb.2 (hR.cons hIb) ((hB.sub i).cons x _ _) ((hBW.sub i).cons x _ _)
        ((hCs.sub i).cons x _ _) (fun h0 => (hLoc h0).cons (locW_atom hR (hLoc h0) (atom1_var hb.1) hav))
        (fun q hq => hW q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)) (by simp [hc]) h l k
      dsimp only at hI
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hI
      simp [lowerC2, hav, hr']
    | _ => exact (throw_ok h).elim
  | ifeq a b yes no ihy ihn =>
    intro cs bufs scope env lits s s' hb hR hB hBW hCs hLoc hW hcur h l k
    obtain ⟨⟨l0, is0⟩, hc⟩ := Option.isSome_iff_exists.1 hcur
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨ha1, hb1⟩, hby⟩, hbn⟩ := hb
    rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
    obtain ⟨pa, _, h1, h'⟩ := bind_ok_inv h
    obtain ⟨⟨ta, hpa⟩, rfl⟩ := evalOne_inv h1
    obtain ⟨qb, _, h2, -⟩ := bind_ok_inv h'
    obtain ⟨⟨tb, hqb⟩, -⟩ := evalOne_inv h2
    rw [bind_ok (evalOne_eq hpa _ _), bind_ok (evalOne_eq hqb _ _), bind_ok (freshLabel_eq _ _),
      bind_ok (freshLabel_eq _ _), bind_ok (terminate_eq _ (by simpa using hc)),
      bind_ok (startBlock_eq _ rfl rfl), bind_ok (markAt_eq _ _ _)] at h
    obtain ⟨_, s5, hy, h⟩ := bind_ok_inv h
    have hWy : ∀ q ∈ litWalk2 p lits yes, layQ q = true ∧ callQ p q = true := fun q hq =>
      hW q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hq))
    have hWn : ∀ q ∈ litWalk2 p lits no, layQ q = true ∧ callQ p q = true := fun q hq =>
      hW q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hq))
    have hIy := ihy cs bufs scope env lits _ _ hby hR hB hBW hCs hLoc hWy (by simp) hy
      (labName "then" s.next) 0
    obtain ⟨ry, hry⟩ := Option.isSome_iff_exists.1 hIy
    have hye := lowerExpr_lowerC2 cx hf yes env _ (labName "then" s.next) #[] ry rfl hry
    rw [hye] at hy; cases hy
    rw [bind_ok (startBlock_eq _ rfl rfl), bind_ok (markAt_eq _ _ _)] at h
    have hIn := ihn cs bufs scope env lits _ _ hbn hR hB hBW hCs hLoc hWn (by simp) h
      (labName "else" (s.next + 1)) 0
    dsimp only at hIn
    obtain ⟨rn, hrn⟩ := Option.isSome_iff_exists.1 hIn
    have hry' : lowerC2 cx env (s.next + 2) (labName "then" s.next) 0 yes = some ry := by
      simpa [Nat.add_assoc] using hry
    simp [lowerC2, hpa, hqb, hry', hrn]
  | ret a =>
    intro cs bufs scope env lits s s' hb hR hB hBW hCs hLoc hW hcur h l k
    rw [lowerExpr] at h; simp only [setHere] at h; rw [bind_ok (modify_eq _ _)] at h
    obtain ⟨⟨t, ws⟩, s2, h1, -⟩ := bind_ok_inv h
    obtain ⟨hav, -⟩ := evalAt_inv h1
    simp [lowerC2, hav]
  | _ =>
    intro cs bufs scope env lits s s' hb
    simp [body2] at hb

/-! ## From `Accepted2` -/

/-- **The blocks before a block of `decls2`**: with distinct names, every
block is `decl2` with distinct earlier names, each of `E` or of the
program. -/
theorem decl2_nodup {s : Option Ty} {x : Bool} :
    ∀ {E : List String} {ds : Prog}, decls2 E s x ds = true → (ds.map (·.name)).Nodup → E.Nodup →
      (∀ g ∈ E, g ∉ ds.map (·.name)) →
      ∀ d ∈ ds, ∃ E', decl2 E' s x d = true ∧ E'.Nodup ∧ ∀ g ∈ E', g ∈ E ∨ g ∈ ds.map (·.name)
  | _, [], _, _, _, _, d, hd => absurd hd List.not_mem_nil
  | E, d' :: ds, h, hn, hE, hd, d, hm => by
    simp only [decls2, Bool.and_eq_true] at h
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨E, h.1, hE, fun g hg => .inl hg⟩
    · have hnE : d'.name ∉ E := fun hh => hd _ hh (List.mem_cons_self ..)
      obtain ⟨E', h1, h2, h3⟩ := decl2_nodup h.2 hn.2 (List.nodup_cons.2 ⟨hnE, hE⟩)
        (fun g hg => by
          rcases List.mem_cons.1 hg with rfl | hg
          · exact hn.1
          · exact fun hh => hd g hg (List.mem_cons_of_mem _ hh)) d hm
      refine ⟨E', h1, h2, fun g hg => ?_⟩
      rcases h3 g hg with hg | hg
      · rcases List.mem_cons.1 hg with rfl | hg
        · exact .inr (List.mem_cons_self ..)
        · exact .inl hg
      · exact .inr (List.mem_cons_of_mem _ hg)

/-- **A compiled block's body and its context** (`decl2`, not the extern or
its loop): `body2` from its parameters, the reserved names and the extern's
presence the program's, its earlier blocks among `E`'s, and the setup block
(the one with buffers) unable to name the extern. -/
theorem body_cx2 {p : Prog} {E : List String} {d : Decl}
    (h : decl2 E (setupOf p) (hasPrint p) d = true) (hE : E.Nodup)
    (hne : isPrintExt d = false) (hnl : ¬(hasPrint p = true ∧ d.name = "printL"))
    (hs : ∀ t, setupOf p = some t → simpleTy t = true) :
    ∃ cx2 : Cx2, body2 cx2 [] [] (params2 d) d.body = true ∧ (d.argTy = .unit ∨ simpleTy d.argTy = true) ∧
      cx2.excl = reserved (setupOf p) (hasPrint p) ∧ cx2.ext = hasPrint p ∧ (∀ g ∈ cx2.earlier, g ∈ E) ∧
      (cx2.alloc = true → cx2.earlier.contains "print" = false) := by
  have hx : (hasPrint p && d.name == "printL") = false := by
    cases hp : hasPrint p <;> simp_all
  unfold decl2 at h
  simp only [hne, hx, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · simp only [main2, Bool.and_eq_true] at h
    refine ⟨_, h.2, ?_, rfl, rfl, fun g hg => hg, fun h => by cases h⟩
    have h1 := h.1.2
    rcases hsp : setupOf p with _ | t
    · simp only [hsp, beq_iff_eq] at h1; left; exact h1
    · simp only [hsp, beq_iff_eq] at h1; right; rw [h1]; simp [simpleTy, hs t hsp]
  · split at h
    · split at h
      · simp only [setup2, Bool.and_eq_true, beq_iff_eq] at h
        have hu : d.argTy = .unit := h.1.1.1.1.2
        have hp : params2 d = [] := by simp [params2, hu]
        refine ⟨_, by rw [hp]; exact h.2, Or.inl hu, rfl, rfl, fun g hg => List.mem_of_mem_erase hg, fun _ => ?_⟩
        simp [hE.mem_erase_iff]
      · simp only [plain2, Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨_, h.2, Or.inr (by rw [h.1.2]; rfl), rfl, rfl, fun g hg => hg, fun h => by cases h⟩
    · simp only [plain2, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨_, h.2, Or.inr (by rw [h.1.2]; rfl), rfl, rfl, fun g hg => hg, fun h => by cases h⟩

/-- **An ordinary callee is a code block `Int → Int`**, not an extern. -/
theorem callee_plain {p : Prog} (hp : Accepted2 p = true) {cx2 : Cx2}
    (hex : cx2.excl = reserved (setupOf p) (hasPrint p)) (hearl : ∀ g ∈ cx2.earlier, g ∈ p.map (·.name))
    {g : String} (hg : callee2 cx2 g = true) :
    (Scc.Frontend.externs p).find? (·.1 == g) = none ∧
      ∃ dg, p.find? (·.name == g) = some dg ∧ dg.retTy = .int ∧ dg.argTy = .int := by
  have hn := Spike.Lib.LowerNode.nodup_of_accepted2 hp
  have hds : decls2 [] (setupOf p) (hasPrint p) p = true := by
    simp only [Accepted2, Bool.and_eq_true] at hp
    exact hp.1.1.1.1.1.1.1.2
  simp only [callee2, callee1, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq,
    Bool.not_eq_true', hex] at hg
  obtain ⟨⟨hgE, hgm⟩, hgx⟩ := hg
  obtain ⟨d0, hd0, hd0n⟩ := List.mem_map.1 (hearl g hgE)
  obtain ⟨dg, hdg⟩ := Option.isSome_iff_exists.1
    (List.find?_isSome.2 ⟨d0, hd0, by simp [hd0n]⟩ : (p.find? (·.name == g)).isSome = true)
  have hdm := List.mem_of_find?_eq_some hdg
  have hdn : dg.name = g := by simpa using List.find?_some hdg
  have hres : ∀ n, n ∈ reserved (setupOf p) (hasPrint p) → g ≠ n := by
    intro n hn' hgn
    subst hgn
    have : (reserved (setupOf p) (hasPrint p)).contains g = true := List.contains_iff_mem.2 hn'
    rw [hgx] at this; cases this
  obtain ⟨E, hE⟩ := Spike.Lib.LowerNode.decl2_of_decls2 hds dg hdm
  have hpl : plain2 E (reserved (setupOf p) (hasPrint p)) (hasPrint p) dg = true := by
    unfold decl2 at hE
    split at hE
    · rename_i hpe
      have hpr : hasPrint p = true := List.any_eq_true.2 ⟨dg, hdm, hpe⟩
      have hnm : dg.name = "print" := by
        simp only [isPrintExt, Bool.and_eq_true, beq_iff_eq] at hpe; exact hpe.1.1.1.1
      exact absurd (hdn ▸ hnm) (hres "print" (by simp [reserved, hpr]))
    · split at hE
      · rename_i hpl
        simp only [Bool.and_eq_true, beq_iff_eq] at hpl
        exact absurd (hdn ▸ hpl.2) (hres "printL" (by simp [reserved, hpl.1]))
      · split at hE
        · rename_i hm
          exact absurd (hdn ▸ (by simpa using hm)) hgm
        · split at hE
          · rename_i t ht
            split at hE
            · rename_i hr
              exact absurd (hdn ▸ (by simpa using hr)) (hres "rodata" (by simp [reserved, ht]))
            · exact hE
          · exact hE
  simp only [plain2, Bool.and_eq_true, beq_iff_eq] at hpl
  refine ⟨?_, dg, hdg, hpl.1.1.2, hpl.1.2⟩
  cases hf : (Scc.Frontend.externs p).find? (·.1 == g) with
  | none => rfl
  | some _ =>
    have := Spike.Lib.LowerNode.externs_unit hn dg hdm (by rw [hdn, hf]; rfl)
    rw [hpl.1.1.2] at this; cases this

/-- **The extern**, when the program has it: an extern of the frontend's,
`ownSliceTy → Unit`. -/
theorem print_ext {p : Prog} (hp : Accepted2 p = true) (hpr : hasPrint p = true) :
    ((Scc.Frontend.externs p).find? (·.1 == "print")).isSome = true ∧
      ∃ dp, p.find? (·.name == "print") = some dp ∧ dp.retTy = .unit ∧ dp.argTy = Scc.Frontend.ownSliceTy := by
  have hn := Spike.Lib.LowerNode.nodup_of_accepted2 hp
  obtain ⟨dp, hm, hi⟩ := List.any_eq_true.1 hpr
  have hi' := hi
  simp only [isPrintExt, Bool.and_eq_true, beq_iff_eq, printOwnSig_eq, Option.some.injEq] at hi'
  have hnm : dp.name = "print" := hi'.1.1.1.1
  refine ⟨List.find?_isSome.2 ⟨(dp.name, .print), List.mem_filterMap.2 ⟨dp, hm, by
    rw [Spike.Lib.LowerNode.externOf_of_isPrintExt hi]; rfl⟩, by simp [hnm]⟩, ?_⟩
  obtain ⟨dp', hdp'⟩ := Option.isSome_iff_exists.1
    (List.find?_isSome.2 ⟨dp, hm, by simp [hnm]⟩ : (p.find? (·.name == "print")).isSome = true)
  have hdm := List.mem_of_find?_eq_some hdp'
  have hdn : dp'.name = "print" := by simpa using List.find?_some hdp'
  have := Spike.Lib.LowerNode.eq_of_name_nodup hn hdm hm (hdn.trans hnm.symm)
  subst this
  exact ⟨dp', hdp', hi'.2, hi'.1.2⟩

/-- `callsOk2`'s check at a point of a block's walk gives `callQ`. -/
theorem callQ_of_callsOk2 {p : Prog} (hc : callsOk2 p = true) {d : Decl} (hd : d ∈ p) {q : Expr × List (String × LitV)}
    (hq : q ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body) : callQ p q = true := by
  have hq' := List.all_eq_true.mp (List.all_eq_true.mp hc d hd) q hq
  obtain ⟨e, lits⟩ := q
  unfold callQ
  dsimp only at hq' ⊢
  split
  · simpa using hq'
  · rfl

/-! ## A compiled block -/

/-- **The closed form of a compiled block of an `Accepted2` program**: on a
block the lowering compiles (not among the frontend's externs, the
`compiled` filter of `lowerWithMarks`) whose `lowerDeclMarks` succeeds, the
hypotheses of `lowerDeclMarks_lowerC2` hold: the parameter's and result's
word counts within the argument and result registers, the parameter's
marking, and the body's closed form from the parameter's environment. -/
theorem accepted2_lowerC2 {p : Prog} (hp : Accepted2 p = true) {d : Decl} (hd : d ∈ p)
    (hc : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false) {obj : Scc.ObjLayout}
    {fm : Func × Array (Node × Point)} (hl : lowerDeclMarks p (Scc.Frontend.externs p) d obj = .ok fm) :
    ∃ na nr sc hq r, Scc.Obj.valWords d.argTy = some na ∧ na ≤ maxArgs ∧ Scc.Obj.valWords d.retTy = some nr ∧
      nr ≤ maxRets ∧ markR d.argTy ((paramsR d na).map .reg) = some (sc, hq) ∧
      lowerC2 { prog := p, externs := Scc.Frontend.externs p, fn := d.name, obj } (env2 d na) 0 "entry" 0 d.body =
        some r := by
  have hn := Spike.Lib.LowerNode.nodup_of_accepted2 hp
  have hp' := hp
  simp only [Accepted2, Bool.and_eq_true] at hp'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hds⟩, hsp⟩, -⟩, hlay⟩, -⟩, hcalls⟩, -⟩, -⟩ := hp'
  have hne := Spike.Lib.LowerNode.isPrintExt_false_of_compiled hd hc
  have hnl : ¬(hasPrint p = true ∧ d.name = "printL") := by
    rintro ⟨hpr, hnm⟩
    obtain ⟨E, hE⟩ := Spike.Lib.LowerNode.decl2_of_decls2 hds d hd
    unfold decl2 at hE
    simp only [hne, hpr, hnm, Bool.false_eq_true, ↓reduceIte, Bool.true_and, beq_self_eq_true] at hE
    have hx : Scc.Frontend.externOf d = some .print := by
      unfold Scc.Frontend.externOf
      simp [hnm, hE]
    have : ((Scc.Frontend.externs p).any (·.1 == d.name)) = true :=
      List.any_eq_true.2 ⟨(d.name, .print), List.mem_filterMap.2 ⟨d, hd, by rw [hx]; rfl⟩, by simp⟩
    rw [hc] at this; cases this
  obtain ⟨E, hE, hEn, hEm⟩ := decl2_nodup hds hn List.nodup_nil (by simp) d hd
  obtain ⟨cx2, hb, harg, hex, hext, hearl, halloc⟩ :=
    body_cx2 hE hEn hne hnl (Spike.Lib.LowerNode.setup_simple hds hsp)
  have hearl' : ∀ g ∈ cx2.earlier, g ∈ p.map (·.name) := fun g hg => by
    rcases hEm g (hearl g hg) with h | h
    · cases h
    · exact h
  have hcx : CxOK { prog := p, externs := Scc.Frontend.externs p, fn := d.name, obj } p :=
    ⟨rfl, fun d' hd' => by
      obtain ⟨E', hE'⟩ := Spike.Lib.LowerNode.decl2_of_decls2 hds d' hd'
      exact Spike.Lib.LowerNode.retTy_decl2 hE', Spike.Lib.LowerNode.externs_unit hn⟩
  have hU := fun g hg => callee_plain hp hex hearl' (g := g) hg
  have hP : cx2.ext = true → cx2.earlier.contains "print" = true → cx2.alloc = false ∧
      ((Scc.Frontend.externs p).find? (·.1 == "print")).isSome = true ∧
      ∃ dp, p.find? (·.name == "print") = some dp ∧ dp.retTy = .unit ∧ dp.argTy = Scc.Frontend.ownSliceTy := by
    intro he hcp
    refine ⟨?_, print_ext hp (hext ▸ he)⟩
    cases ha : cx2.alloc
    · rfl
    · rw [halloc ha] at hcp; cases hcp
  unfold lowerDeclMarks at hl
  rcases hv : Scc.Obj.valWords d.argTy with _ | na <;> simp only [hv] at hl
  · cases hl
  simp only [pure, Except.pure, bind, Except.bind] at hl
  split at hl
  · cases hl
  rename_i hna
  split at hl
  · rename_i nr hnr
    split at hl
    · cases hl
    rename_i hnr'
    obtain ⟨s', hs', -⟩ := Spike.Lib.LowerNode.buildFuncMarks_ok hl
    obtain ⟨_, s1, h1, h⟩ := bind_ok_inv hs'
    obtain ⟨_, s2, h2, h⟩ := bind_ok_inv h
    obtain ⟨sc, hq, hmr⟩ := post_markWords _ _ _ _ _ h1
    rw [markWords_eq hmr] at h1; cases h1
    rw [markAt_eq] at h2; cases h2
    have hps : ∀ o ∈ (paramsR d na).map Operand.reg, IsReg o := fun o ho => by
      simp only [List.mem_map] at ho; obtain ⟨r, -, rfl⟩ := ho; exact ⟨r, rfl⟩
    have hpl : Scc.Obj.valWords d.argTy = some ((paramsR d na).map Operand.reg).length := by
      simp [hv, paramsR]
    have hR : Rel (env2 d na) ((params2 d).map (·, shapeOf d.argTy)) (params2 d) := by
      by_cases hu : d.argTy = .unit
      · have hp0 : params2 d = [] := by simp [params2, hu]
        have h0 : (paramsR d na).map Operand.reg = [] := by
          rw [hu] at hpl
          simp only [Scc.Obj.valWords, Scc.Obj.slots, Option.map_some, Option.some.injEq] at hpl
          exact List.length_eq_zero_iff.1 hpl.symm
        rw [hp0]
        refine ⟨fun x b hb => ⟨fun L hL => (by simp at hL), fun _ => ?_⟩, fun x hx => (by simp at hx)⟩
        simp only [env2] at hb
        rw [find?_cons_name] at hb
        split at hb
        · cases hb; exact ⟨hu, h0⟩
        · cases hb
      · have hs : simpleTy d.argTy = true := harg.resolve_left hu
        have hp1 : params2 d = [d.arg] := by simp [params2, hu]
        rw [hp1]
        have hcp := Spike.Lib.LowerNode.compat_shapeOf d.argTy 0 0 hs (Spike.Lib.LowerNode.slots_of_valWords hpl)
        have hi : Spike.Lib.LowerNode.Inv d.argTy ((paramsR d na).map Operand.reg) (shapeOf d.argTy) :=
          ⟨hcp, Spike.Lib.LowerNode.agreeW_regs hps (by
            have := valWords_compat hcp; rw [hpl] at this; exact Option.some.inj this)⟩
        refine ⟨Spike.Lib.LowerNode.relE_nil.cons hi, fun x hx => ?_⟩
        simp only [List.mem_singleton] at hx
        subst hx
        simp
    have hLoc : LocR (env2 d na) ((params2 d).map (·, shapeOf d.argTy)) := by
      intro y b L hb hL
      have hb' := hb
      simp only [env2] at hb'
      rw [find?_cons_name] at hb'
      split at hb'
      · cases hb'; exact locW_of_regs hps ((hR.1 y _ hb).1 L hL).2
      · cases hb'
    have hW : ∀ q ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body,
        layQ q = true ∧ callQ p q = true := fun q hq =>
      ⟨List.all_eq_true.mp hlay q (List.mem_flatMap.2 ⟨d, hd, hq⟩), callQ_of_callsOk2 hcalls hd hq⟩
    have hsome := lowerC2_isSome rfl hcx hU hP d.body [] [] (params2 d) (env2 d na) _ _ _ hb hR
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ => hLoc) hW rfl h
      "entry" 0
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hsome
    exact ⟨na, nr, sc, hq, r, rfl, by omega, hnr, by omega, hmr, hr⟩
  · cases hl

/-- **The lowering of a compiled block of an `Accepted2` program** is
`func2` with the trace `marks2` of its body's closed form
(`accepted2_lowerC2`, `lowerDeclMarks_lowerC2`). -/
theorem accepted2_lowerDeclMarks {p : Prog} (hp : Accepted2 p = true) {d : Decl} (hd : d ∈ p)
    (hc : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false) {obj : Scc.ObjLayout}
    {fm : Func × Array (Node × Point)} (hl : lowerDeclMarks p (Scc.Frontend.externs p) d obj = .ok fm) :
    ∃ na sc hq r,
      lowerC2 { prog := p, externs := Scc.Frontend.externs p, fn := d.name, obj } (env2 d na) 0 "entry" 0 d.body =
        some r ∧ fm = (func2 (Names.user d.name) (paramsR d na) sc hq r, marks2 d na r) := by
  obtain ⟨na, nr, sc, hq, r, hna, ha, hnr, hr, hm, hlr⟩ := accepted2_lowerC2 hp hd hc hl
  refine ⟨na, sc, hq, r, hlr, ?_⟩
  rw [lowerDeclMarks_lowerC2 p _ obj hna ha hnr hr hm hlr] at hl
  cases hl; rfl

end Spike.Lib.LowerShape
