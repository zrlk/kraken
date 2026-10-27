import Spike.Lib.Src.ImmIn

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower (B BState Env LitV shapeOf simpleTy litAt opLit litWalk2 lowerOp evalAt evalOne lookupV one
  needSome words prodOf Cx2 body2 unbuf elem2 retShape litWalks2 wordLit imms2Of immsCoherent2 layoutOk2
  params2 callBlock)

/-! ## Bindings against the walk's -/

/-- The buffer type `newBuf` gives. -/
def bufTy (τ : Ty) : Ty := .refine (.loc .own (.array (.lit 0) τ)) (.ini (.lit 0))

/-- **The lowering's bindings against the walk's**: a binding whose name has
literal words in `lits` agrees with them (`Inv`); any other is a `Unit` with
no word (the parameter of a `Unit` block). -/
def RelE (env : Env) (lits : List (String × LitV)) : Prop :=
  ∀ x b, env.find? (·.1 == x) = some b →
    (∀ L, lits.lookup x = some L → Inv b.2.1 b.2.2 L) ∧ (lits.lookup x = none → b.2.1 = .unit ∧ b.2.2 = [])

/-- `RelE`, every variable of `scope` with literal words. -/
def Rel (env : Env) (lits : List (String × LitV)) (scope : List String) : Prop :=
  RelE env lits ∧ ∀ x ∈ scope, (lits.lookup x).isSome = true

/-- **The buffers of `body2`** are bound to `newBuf`'s type of a one-word
element. -/
def BufInv (env : Env) (bufs : List (String × Nat)) : Prop :=
  ∀ b k, bufs.lookup b = some k → ∃ e τ, env.find? (·.1 == b) = some e ∧ e.2.1 = bufTy τ ∧ elem2 τ = true

theorem find?_cons_name (x y : String) (t : Ty) (ws : List Operand) (env : Env) :
    ((x, t, ws) :: env).find? (·.1 == y) = if x = y then some (x, t, ws) else env.find? (·.1 == y) := by
  by_cases h : x = y
  · simp [List.find?, h]
  · simp [List.find?, h, beq_false_of_ne h]

theorem lookup_cons_name {β : Type} (x y : String) (L : β) (l : List (String × β)) :
    ((x, L) :: l).lookup y = if y = x then some L else l.lookup y := by
  by_cases h : y = x
  · simp [List.lookup, h]
  · simp [List.lookup, h, beq_false_of_ne h]

theorem lookup_mem' {β : Type} {x : String} {L : β} : ∀ {l : List (String × β)}, l.lookup x = some L → (x, L) ∈ l
  | [], h => by cases h
  | (y, M) :: l, h => by
    rw [lookup_cons_name] at h
    split at h
    · rename_i hxy; subst hxy; cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem' h)

theorem lookup_unbuf (x b : String) : ∀ bufs : List (String × Nat),
    (unbuf x bufs).lookup b = if b = x then none else bufs.lookup b
  | [] => by simp [unbuf]
  | (c, k) :: l => by
    have ih := lookup_unbuf x b l
    unfold unbuf at ih ⊢
    by_cases hc : c = x
    · subst hc
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih, lookup_cons_name]
      by_cases hb : b = c <;> simp [hb]
    · simp only [List.filter_cons, bne_iff_ne, ne_eq, hc, not_false_eq_true, ↓reduceIte, lookup_cons_name, ih]
      by_cases hb : b = c
      · subst hb; simp [hc]
      · simp [hb]

theorem RelE.cons {env : Env} {lits : List (String × LitV)} (h : RelE env lits) {x : String} {t : Ty}
    {ws : List Operand} {L : LitV} (hi : Inv t ws L) : RelE ((x, t, ws) :: env) ((x, L) :: lits) := by
  intro y b hb
  rw [find?_cons_name] at hb
  rw [lookup_cons_name]
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, Option.some.injEq] at hb ⊢
    subst hb
    exact ⟨fun L' hL => by cases hL; exact hi, fun h => by cases h⟩
  · simp only [hxy, ↓reduceIte, Ne.symm hxy] at hb ⊢
    exact h y b hb

theorem Rel.cons {env : Env} {lits : List (String × LitV)} {scope : List String} (h : Rel env lits scope)
    {x : String} {t : Ty} {ws : List Operand} {L : LitV} (hi : Inv t ws L) :
    Rel ((x, t, ws) :: env) ((x, L) :: lits) (x :: scope) := by
  refine ⟨h.1.cons hi, fun y hy => ?_⟩
  rw [lookup_cons_name]
  by_cases hxy : y = x
  · simp [hxy]
  · simp only [hxy, ↓reduceIte]
    exact h.2 y (by simpa [hxy] using hy)

theorem BufInv.sub {env : Env} {bufs : List (String × Nat)} (h : BufInv env bufs) (i : String) :
    BufInv env (unbuf i bufs) := by
  intro b k hb
  rw [lookup_unbuf] at hb
  split at hb
  · cases hb
  · exact h b k hb

theorem BufInv.cons {env : Env} {bufs : List (String × Nat)} (h : BufInv env bufs) (x : String) (t : Ty)
    (ws : List Operand) : BufInv ((x, t, ws) :: env) (unbuf x bufs) := by
  intro b k hb
  rw [lookup_unbuf] at hb
  split at hb
  · cases hb
  · rename_i hbx
    obtain ⟨e, τ, he, h1, h2⟩ := h b k hb
    exact ⟨e, τ, by rw [find?_cons_name]; simp only [Ne.symm hbx, ↓reduceIte]; exact he, h1, h2⟩

theorem BufInv.new {env : Env} {bufs : List (String × Nat)} (h : BufInv env bufs) (x : String) {τ : Ty}
    (hτ : elem2 τ = true) (ws : List Operand) (k : Nat) :
    BufInv ((x, bufTy τ, ws) :: env) ((x, k) :: unbuf x bufs) := by
  intro b k' hb
  rw [lookup_cons_name] at hb
  split at hb
  · rename_i hbx; subst hbx
    exact ⟨(b, bufTy τ, ws), τ, by rw [find?_cons_name]; simp, rfl, hτ⟩
  · exact h.cons x _ ws b k' hb

/-! ## The lowering's steps against the walk -/

theorem atom1_var {scope : List String} {a : At} (h : Scc.Lower.atom1 scope a = true) :
    ∀ x, a = .var x → x ∈ scope := by
  rintro x rfl
  simpa [Scc.Lower.atom1, Scc.Lower.atom0] using h

theorem slots_of_valWords {t : Ty} {k : Nat} (h : Scc.Obj.valWords t = some k) :
    (Scc.Obj.slots t 0 0).isSome = true := by
  unfold Scc.Obj.valWords at h
  cases hs : Scc.Obj.slots t 0 0 <;> simp_all

theorem post_evalAt {env : Env} {lits : List (String × LitV)} {scope : List String} (hR : Rel env lits scope)
    {a : At} (ha : ∀ x, a = .var x → x ∈ scope) :
    Post (evalAt env a) fun r => Inv r.1 r.2 (litAt lits a) := by
  cases a with
  | var x =>
    show Post (lookupV env x) _
    refine Post.mono (post_lookupV env x) fun r ⟨b, hb, hr⟩ => ?_
    subst hr
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.1 (hR.2 x (ha x rfl))
    simp only [litAt, hL, Option.getD_some]
    exact (hR.1 x b hb).1 L hL
  | lit n =>
    show Post (if n ≥ 2 ^ 64 then _ else _) _
    split
    · exact Post.throw
    · rename_i hn
      refine Post.pure ⟨rfl, fun v o hv ho => ?_, trivial⟩
      simp only [Option.some.injEq] at ho
      subst ho
      simp only [Scc.Lower.imm, Operand.imm.injEq] at hv
      subst hv
      simp only [Option.some.injEq]
      exact (Nat.mod_eq_of_lt (by omega)).symm
  | unit => exact Post.pure ⟨rfl, trivial⟩

theorem post_evalOne {env : Env} {lits : List (String × LitV)} {scope : List String} (hR : Rel env lits scope)
    {a : At} (ha : ∀ x, a = .var x → x ∈ scope) (what : String) :
    Post (evalOne env a what) fun w => AgreeW [w] (flatL (litAt lits a)) := by
  unfold evalOne
  exact Post.bind (post_evalAt hR ha) fun r hr => Post.mono (post_one _ _) fun w hw => hw ▸ hr.2

/-- A one-word result in a register. -/
theorem post_add (cx : Scc.Lower.Ctx) (env : Env) (x : String) (a b : At) :
    Post (lowerOp cx env x (.add a b)) fun r => ∃ d, r = (.int, [.reg d]) := by
  simp only [lowerOp]
  repeat' first | exact Post.pure ⟨_, rfl⟩ | refine Post.bind' fun _ => ?_

theorem post_sub (cx : Scc.Lower.Ctx) (env : Env) (x : String) (a b : At) :
    Post (lowerOp cx env x (.sub a b)) fun r => ∃ d, r = (.int, [.reg d]) := by
  simp only [lowerOp]
  repeat' first | exact Post.pure ⟨_, rfl⟩ | refine Post.bind' fun _ => ?_

theorem post_newBuf (cx : Scc.Lower.Ctx) (env : Env) (x : String) (n : At) (τ : Ty) :
    Post (lowerOp cx env x (.newBuf n τ)) fun r => ∃ q, r = (bufTy τ, [.reg q, Scc.Lower.imm 0]) := by
  simp only [lowerOp]
  repeat' first | exact Post.pure ⟨_, rfl⟩ | refine Post.bind' fun _ => ?_ | split | dsimp only

theorem post_callBlock (cx : Scc.Lower.Ctx) (f : String) (args : List Operand) (nres : Nat) :
    Post (callBlock cx f args nres) fun rs => (rs = [] ∧ (cx.externs.find? (·.1 == f)).isSome = true) ∨
      (rs.length = nres ∧ ∀ r ∈ rs, IsReg r) := by
  unfold callBlock
  split
  · rename_i heq
    refine Post.mono (P := fun rs => rs = []) ?_ fun rs h => Or.inl ⟨h, by simp [heq]⟩
    repeat' first | exact Post.pure rfl | exact Post.throw | refine Post.bind' fun _ => ?_ | split | dsimp only
  · refine Post.mono (P := fun rs => rs.length = nres ∧ ∀ r ∈ rs, IsReg r) ?_ fun rs h => Or.inr h
    dsimp only
    repeat' first
      | exact Post.pure rfl
      | exact Post.throw
      | refine Post.bind (Post.mapM (P := fun _ => True) _ fun _ => fun _ _ _ _ => trivial) fun ds hds =>
          Post.mono (P := fun rs => rs = ds.map .reg) ?_ fun rs h => ⟨by rw [h, List.length_map, hds.1,
            List.length_range], by rw [h]; intro r hr; obtain ⟨d, -, rfl⟩ := List.mem_map.1 hr; exact ⟨d, rfl⟩⟩
      | refine Post.bind' fun _ => ?_
      | split

theorem post_xchgAt (cx : Scc.Lower.Ctx) {env : Env} (x b : String) (i : Nat) (v : At)
    {e : String × Ty × List Operand} {τ : Ty} (he : env.find? (·.1 == b) = some e) (ht : e.2.1 = bufTy τ)
    (hτ : elem2 τ = true) :
    Post (lowerOp cx env x (.xchgAt (.var b) (.lit i) v)) fun r => r.1 = τ ∧ r.2.length = 1 ∧ ∀ o ∈ r.2, IsReg o := by
  simp only [lowerOp]
  refine Post.bind (post_lookupV env b) fun r ⟨e1, he1, hr⟩ => ?_
  rw [he] at he1; cases he1; subst hr
  dsimp only
  rw [ht]
  refine Post.bind' fun _ => Post.bind' fun _ => Post.bind (post_needSome _ _) fun mu hmu => ?_
  simp only [bufTy, Scc.Lower.bufElem, Option.some.injEq] at hmu
  subst hmu
  refine Post.bind' fun _ => Post.bind' fun _ => Post.bind (post_cellAddrs _ _ _ _) fun as ⟨sl, hsl, hl⟩ =>
    Post.bind (post_loadAt _ _ _) fun old ⟨hol, hreg⟩ => Post.bind' fun _ => Post.pure ⟨rfl, ?_, hreg⟩
  rw [hol, hl]
  cases τ <;> simp [elem2] at hτ <;> simp [Scc.Obj.slots] at hsl <;> subst hsl <;> rfl

/-! ## One `let` -/

/-- The layout checks of `layoutOk2` at one point. -/
def layQ (q : Expr × List (String × LitV)) : Bool :=
  match q.1 with
  | .let_ _ (.pack a _ τ) _ => (litAt q.2 a).erase == shapeOf τ && simpleTy τ && (Scc.Obj.valWords τ).isSome
  | .let_ _ (.asLanes _ _ a) _ => match litAt q.2 a with | .leaf _ => true | _ => false
  | _ => true

theorem layoutOk2_eq (p : Prog) : layoutOk2 p = (litWalks2 p).all layQ := rfl

/-- **The lowering's context against the program**: its program, every
block's result type with `shapeOf`'s layout, an extern's result `Unit`. -/
structure CxOK (cx : Scc.Lower.Ctx) (p : Prog) : Prop where
  prog : cx.prog = p
  ret : ∀ d ∈ p, simpleTy d.retTy = true
  ext : ∀ d ∈ p, (cx.externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit

/-- What the lowering of `let x = op` gives, against the walk: words with
`op`'s literal words, and the buffers `bufs'` still bound to buffers. -/
def OpQ (p : Prog) (lits : List (String × LitV)) (env : Env) (bufs' : List (String × Nat)) (x : String) (op : Op)
    (r : Ty × List Operand) : Prop :=
  Inv r.1 r.2 (opLit p lits op) ∧ BufInv ((x, r.1, r.2) :: env) bufs'

theorem inv_reg (d : Reg) : Inv .int [.reg d] (.leaf none) := ⟨rfl, by simp [AgreeW, flatL]⟩

theorem let_step {cx : Scc.Lower.Ctx} {p : Prog} (hcx : CxOK cx p) {cx2 : Cx2} {cs bufs : List (String × Nat)}
    {scope : List String} {x : String} {op : Op} {e : Expr} {env : Env} {lits : List (String × LitV)}
    (hb : body2 cx2 cs bufs scope (.let_ x op e) = true) (hR : Rel env lits scope) (hB : BufInv env bufs)
    (hL : layQ (.let_ x op e, lits) = true) :
    ∃ cs' bufs', body2 cx2 cs' bufs' (x :: scope) e = true ∧
      Post (lowerOp cx env x op) (OpQ p lits env bufs' x op) := by
  cases op <;> try (simp [body2] at hb; done)
  case atom a =>
    simp only [body2, Bool.and_eq_true] at hb
    exact ⟨_, _, hb.2, Post.mono (post_evalAt hR (atom1_var hb.1)) fun r hr => ⟨hr, hB.cons x _ _⟩⟩
  case nameI a =>
    simp only [body2, Bool.and_eq_true] at hb
    exact ⟨_, _, hb.2, Post.mono (post_evalAt hR (atom1_var hb.1)) fun r hr => ⟨hr, hB.cons x _ _⟩⟩
  case add a b =>
    simp only [body2, Bool.and_eq_true] at hb
    exact ⟨_, _, hb.2, Post.mono (post_add cx env x a b) fun r ⟨d, hd⟩ => by
      subst hd; exact ⟨inv_reg d, hB.cons x _ _⟩⟩
  case sub a b =>
    simp only [body2, Bool.and_eq_true] at hb
    exact ⟨_, _, hb.2, Post.mono (post_sub cx env x a b) fun r ⟨d, hd⟩ => by
      subst hd; exact ⟨inv_reg d, hB.cons x _ _⟩⟩
  case pair a b =>
    simp only [body2, Bool.and_eq_true] at hb
    refine ⟨_, _, hb.2, ?_⟩
    simp only [lowerOp]
    refine Post.bind (post_evalAt hR (atom1_var hb.1.1)) fun r1 h1 => ?_
    refine Post.bind (post_evalAt hR (atom1_var hb.1.2)) fun r2 h2 => ?_
    refine Post.pure ⟨⟨?_, h1.2.append h2.2⟩, hB.cons x _ _⟩
    simp only [opLit, Compat, h1.1, h2.1, Bool.and_self]
  case pack a i τ =>
    simp only [body2, Bool.and_eq_true] at hb
    simp only [layQ, Bool.and_eq_true, beq_iff_eq] at hL
    refine ⟨_, _, hb.2, ?_⟩
    simp only [lowerOp]
    refine Post.bind (post_evalAt hR (atom1_var hb.1)) fun r h => Post.pure ⟨⟨?_, h.2⟩, hB.cons x _ _⟩
    show Compat τ (litAt lits a) = true
    rw [← compat_erase, hL.1.1]
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hL.2
    exact compat_shapeOf τ 0 0 hL.1.2 (slots_of_valWords hk)
  case asLanes sg w a =>
    simp only [body2, Bool.and_eq_true] at hb
    refine ⟨_, _, hb.2, ?_⟩
    simp only [layQ] at hL
    split at hL
    · rename_i o hla
      simp only [lowerOp]
      refine Post.bind (post_evalOne hR (atom1_var hb.1) _) fun w' hw => Post.pure ⟨⟨rfl, ?_⟩, hB.cons x _ _⟩
      show AgreeW [w'] (flatL (.leaf (litAt lits a).one))
      rw [hla] at hw ⊢
      exact hw
    · cases hL
  case call g is a ts =>
    simp only [body2, Bool.and_eq_true] at hb
    refine ⟨_, _, hb.2, ?_⟩
    simp only [lowerOp]
    refine Post.bind (post_needSome _ _) fun d hd => Post.bind' fun r => ?_
    refine Post.bind (post_words _) fun k hk => Post.bind (post_callBlock cx g _ k) fun rs hrs =>
      Post.pure ⟨?_, hB.cons x _ _⟩
    rw [hcx.prog] at hd
    have hm := List.mem_of_find?_eq_some hd
    have hn : d.name = g := by simpa using List.find?_some hd
    show Inv d.retTy rs (retShape p g)
    simp only [retShape, hd]
    rcases hrs with ⟨rfl, hx⟩ | ⟨hl, hr⟩
    · rw [hcx.ext d hm (hn ▸ hx)]; exact ⟨rfl, trivial⟩
    · have hc := compat_shapeOf d.retTy 0 0 (hcx.ret d hm) (slots_of_valWords hk)
      refine ⟨hc, agreeW_regs hr ?_⟩
      have := valWords_compat hc
      rw [hk] at this
      rw [hl]; exact Option.some.inj this
  case newBuf n τ =>
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨_, _⟩, hτ⟩, hm⟩ := hb
    split at hm
    · rename_i k _
      simp only [Bool.and_eq_true] at hm
      exact ⟨_, _, hm.2, Post.mono (post_newBuf cx env x n τ) fun r ⟨q, hq⟩ => by
        subst hq
        exact ⟨⟨rfl, by simp [AgreeW, flatL, opLit]⟩, hB.new x hτ _ k⟩⟩
    · cases hm
  case xchgAt b i v =>
    rcases b with b | b | _ <;> rcases i with i | i | _ <;> try (simp [body2] at hb; done)
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨_, hk⟩, _⟩, hb⟩ := hb
    split at hk
    · rename_i k hbk
      obtain ⟨e0, τ, he0, ht0, hτ⟩ := hB b k hbk
      refine ⟨_, _, hb, Post.mono (post_xchgAt cx x b i v he0 ht0 hτ) fun r ⟨h1, h2, h3⟩ => ⟨⟨?_, ?_⟩, hB.cons x _ _⟩⟩
      · show Compat r.1 (.leaf none) = true
        rw [h1]; cases τ <;> simp [elem2] at hτ <;> rfl
      · exact agreeW_regs h3 (by rw [h2]; rfl)
    · cases hk

theorem post_letStep {cx : Scc.Lower.Ctx} {env : Env} {x : String} {op : Op} {e : Expr}
    {Q : Ty × List Operand → Prop} (h : Post (lowerOp cx env x op) Q) : Post (letStep cx env x op e) Q := by
  unfold letStep
  exact Post.bind' fun _ => Post.bind h fun r hr => Post.bind' fun _ => Post.pure hr

/-! ## A pair split -/

theorem post_splitStep {env : Env} {lits : List (String × LitV)} {scope : List String} (hR : Rel env lits scope)
    {a : At} (ha : ∀ x, a = .var x → x ∈ scope) :
    Post (splitStep env a) fun r => ∃ l rr, litAt lits a = .node l rr ∧ Inv r.1 (r.2.2.1.take r.2.2.2) l ∧
      Inv r.2.1 (r.2.2.1.drop r.2.2.2) rr := by
  unfold splitStep
  refine Post.bind (post_evalAt hR ha) fun r hr => ?_
  obtain ⟨t, ws⟩ := r
  dsimp only at hr ⊢
  refine Post.bind (post_needSome _ _) fun uw huw => ?_
  obtain ⟨u, w⟩ := uw
  dsimp only
  refine Post.bind (post_words _) fun k hk => Post.pure ?_
  obtain ⟨l, rr, hL, hcl, hcr⟩ := compat_prodOf huw hr.1
  have hk' : k = (flatL l).length := by
    have := valWords_compat hcl
    rw [hk] at this
    exact Option.some.inj this
  have hw := hr.2
  rw [hL] at hw
  obtain ⟨h1, h2⟩ := AgreeW.take_drop (c := flatL l) (d := flatL rr) hw
  subst hk'
  exact ⟨l, rr, hL, ⟨hcl, h1⟩, ⟨hcr, h2⟩⟩

/-! ## The walk -/

/-- **The lowering's walk against the source's**: at each point of
`lowerEnvs2` on an `Accepted2` body, the walk `litWalk2` has the same term
with literal words that the lowering's environment agrees with. -/
theorem walk_inv {cx : Scc.Lower.Ctx} {p : Prog} (hcx : CxOK cx p) (cx2 : Cx2) (e : Expr) :
    ∀ (cs bufs : List (String × Nat)) (scope : List String) (env : Env) (lits : List (String × LitV)) (n : Nat),
      body2 cx2 cs bufs scope e = true → Rel env lits scope → BufInv env bufs →
      (∀ q ∈ litWalk2 p lits e, layQ q = true) →
      ∀ q ∈ lowerEnvs2 cx env n e, ∃ lits', (q.1, lits') ∈ litWalk2 p lits e ∧ RelE q.2.1 lits' := by
  induction e
  case let_ x op e ih =>
    intro cs bufs scope env lits n hb hR hB hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, by rw [litWalk2]; exact List.mem_cons_self .., hR.1⟩
    · obtain ⟨cs', bufs', hb', hop⟩ := let_step hcx hb hR hB (hL _ (by rw [litWalk2]; exact List.mem_cons_self ..))
      split at hq
      · rename_i hr
        have hQ := post_runB (post_letStep (e := e) hop) hr
        obtain ⟨lits', h1, h2⟩ := ih cs' bufs' (x :: scope) _ _ _ hb' (hR.cons hQ.1) hQ.2
          (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)) q hq
        exact ⟨lits', by rw [litWalk2]; exact List.mem_cons_of_mem _ h1, h2⟩
      · simp at hq
  case split a x y e ih =>
    intro cs bufs scope env lits n hb hR hB hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, by rw [litWalk2]; exact List.mem_cons_self .., hR.1⟩
    · simp only [body2, Bool.and_eq_true] at hb
      split at hq
      · rename_i hr
        obtain ⟨l, rr, hla, h1, h2⟩ := post_runB (post_splitStep hR (atom1_var hb.1)) hr
        have hlw : litWalk2 p lits (.split a x y e) =
            (.split a x y e, lits) :: litWalk2 p ((y, rr) :: (x, l) :: lits) e := by
          rw [litWalk2, hla]
        obtain ⟨lits', h1', h2'⟩ := ih _ _ (y :: x :: scope) _ _ _ hb.2 ((hR.cons h1).cons h2)
          ((hB.cons x _ _).cons y _ _) (fun q hq => hL q (by rw [hlw]; exact List.mem_cons_of_mem _ hq)) q hq
        exact ⟨lits', by rw [hlw]; exact List.mem_cons_of_mem _ h1', h2'⟩
      · simp at hq
  case unpack a i x e ih =>
    intro cs bufs scope env lits n hb hR hB hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, by rw [litWalk2]; exact List.mem_cons_self .., hR.1⟩
    · simp only [body2, Bool.and_eq_true] at hb
      split at hq
      · rename_i hr
        have hI := post_runB (post_evalAt hR (atom1_var hb.1)) hr
        have hI' : Inv _ _ (litAt lits a) := ⟨by
          have := hI.1; simp only [Compat, Bool.and_eq_true] at this; exact this.2, hI.2⟩
        obtain ⟨lits', h1, h2⟩ := ih _ _ (x :: scope) _ _ _ hb.2 (hR.cons hI') ((hB.sub i).cons x _ _)
          (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)) q hq
        exact ⟨lits', by rw [litWalk2]; exact List.mem_cons_of_mem _ h1, h2⟩
      · simp at hq
  case ifeq a b yes no ihy ihn =>
    intro cs bufs scope env lits n hb hR hB hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, by rw [litWalk2]; exact List.mem_cons_self .., hR.1⟩
    · simp only [body2, Bool.and_eq_true] at hb
      split at hq
      · rw [List.mem_append] at hq
        rcases hq with hq | hq
        · obtain ⟨lits', h1, h2⟩ := ihy _ _ _ _ _ _ hb.1.2 hR hB
            (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hq))) q hq
          exact ⟨lits', by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ h1), h2⟩
        · split at hq
          · obtain ⟨lits', h1, h2⟩ := ihn _ _ _ _ _ _ hb.2 hR hB
              (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hq))) q hq
            exact ⟨lits', by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ h1), h2⟩
          · simp at hq
      · simp at hq
  all_goals
    intro cs bufs scope env lits n hb hR hB hL q hq
    first
      | (simp [body2] at hb; done)
      | (simp only [lowerEnvs2, List.mem_singleton] at hq
         subst hq
         exact ⟨lits, by simp [litWalk2], hR.1⟩)

/-! ## The immediate table -/

/-- **Every one-word immediate of the lowering's environment is `i`'s entry
at `t`**, words regrouped per source word by `Form.group`. -/
def ImmIn2 (i : Expr → String → Nat → Option Nat) (env : Env) (t : Expr) : Prop :=
  ∀ x b pls k v, env.find? (·.1 == x) = some b → Spike.Lib.Form.group b.2.1 b.2.2 = some pls →
    pls[k]? = some (Spike.Lib.Form.WordPl.one (.imm v)) → i t x k = some v.toNat

theorem immIn2_of_rel {p : Prog} (hc : immsCoherent2 p = true) {t : Expr} {lits : List (String × LitV)}
    (hw : (t, lits) ∈ litWalks2 p) {env : Env} (hR : RelE env lits) : ImmIn2 (imms2Of p) env t := by
  intro x b pls k v hb hg hk
  cases hl : lits.lookup x with
  | none =>
    obtain ⟨h1, h2⟩ := (hR x b hb).2 hl
    rw [h1, h2] at hg
    simp only [Spike.Lib.Form.group, Spike.Lib.Form.grp, Option.some.injEq] at hg
    subst hg; simp at hk
  | some L =>
    have hw' := group_inv ((hR x b hb).1 L hl) hg hk
    have hq := List.all_eq_true.mp (List.all_eq_true.mp hc _ hw) _ (lookup_mem' hl)
    have hkl : k < L.words.length := (List.getElem?_eq_some_iff.1 hw').1
    have := List.all_eq_true.mp hq k (List.mem_range.2 hkl)
    have hwl : wordLit lits x k = some v.toNat := by simp [wordLit, hl, hw']
    simp only [hwl, beq_iff_eq] at this
    exact this

theorem relE_nil : RelE [] [] := fun _ _ h => by cases h

/-- **At each point of the lowering's walk of an `Accepted2` body, the
lowering's environment has its immediates in `imms2Of p`**: `d` a block of
`p` with a `body2` body from its parameters, the parameter `Unit` or of a
`simpleTy` type and bound to registers `ps`, the context `CxOK`. -/
theorem immIn_lowerEnvs2 {p : Prog} (hc : immsCoherent2 p = true) (hlay : layoutOk2 p = true)
    {cx : Scc.Lower.Ctx} (hcx : CxOK cx p) {d : Decl} (hd : d ∈ p) {cx2 : Cx2}
    (hb : body2 cx2 [] [] (params2 d) d.body = true) (harg : d.argTy = .unit ∨ simpleTy d.argTy = true)
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body, ImmIn2 (imms2Of p) q.2.1 q.1 := by
  intro q hq
  have hR : Rel [(d.arg, d.argTy, ps)] ((params2 d).map (·, shapeOf d.argTy)) (params2 d) := by
    by_cases hu : d.argTy = .unit
    · have hp : params2 d = [] := by simp [params2, hu]
      have h0 : ps = [] := by
        rw [hu] at hpl
        simp only [Scc.Obj.valWords, Scc.Obj.slots, Option.map_some, List.length_nil, Option.some.injEq] at hpl
        exact List.length_eq_zero_iff.1 hpl.symm
      rw [hp]
      refine ⟨fun x b hb => ⟨fun L hL => (by simp at hL), fun _ => ?_⟩, fun x hx => (by simp at hx)⟩
      rw [find?_cons_name] at hb
      split at hb
      · cases hb; exact ⟨hu, h0⟩
      · cases hb
    · have hs : simpleTy d.argTy = true := harg.resolve_left hu
      have hp : params2 d = [d.arg] := by simp [params2, hu]
      rw [hp]
      have hcp := compat_shapeOf d.argTy 0 0 hs (slots_of_valWords hpl)
      have hi : Inv d.argTy ps (shapeOf d.argTy) := ⟨hcp, agreeW_regs hps (by
        have := valWords_compat hcp; rw [hpl] at this; exact Option.some.inj this)⟩
      refine ⟨relE_nil.cons hi, fun x hx => ?_⟩
      simp only [List.mem_singleton] at hx
      subst hx
      simp
  obtain ⟨lits', h1, h2⟩ := walk_inv hcx cx2 d.body [] [] _ _ _ n hb hR (fun b k h => by cases h)
    (fun q hq => List.all_eq_true.mp hlay q (List.mem_flatMap.2 ⟨d, hd, hq⟩)) q hq
  exact immIn2_of_rel hc (List.mem_flatMap.2 ⟨d, hd, h1⟩) h2

/-! ## From `Accepted2` -/

theorem decl2_of_decls2 {s : Option Ty} {x : Bool} :
    ∀ {E : List String} {p : Prog}, Scc.Lower.decls2 E s x p = true → ∀ d ∈ p, ∃ E', Scc.Lower.decl2 E' s x d = true
  | _, [], _, d, hd => absurd hd List.not_mem_nil
  | E, d' :: ds, h, d, hd => by
    simp only [Scc.Lower.decls2, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨E, h.1⟩
    · exact decl2_of_decls2 h.2 d hd

/-- **The blocks of `decl2` return a `simpleTy`.** -/
theorem retTy_decl2 {E : List String} {s : Option Ty} {x : Bool} {d : Decl} (h : Scc.Lower.decl2 E s x d = true) :
    simpleTy d.retTy = true := by
  unfold Scc.Lower.decl2 at h
  split at h
  · rename_i hp
    simp only [Scc.Lower.isPrintExt, Bool.and_eq_true, beq_iff_eq] at hp
    rw [hp.2]; rfl
  · split at h
    · rw [Scc.Frontend.declIs_eq h]; rfl
    · split at h
      · simp only [Scc.Lower.main2, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1.1.2]; rfl
      · split at h
        · split at h
          · simp only [Scc.Lower.setup2, Bool.and_eq_true, beq_iff_eq] at h
            rw [h.1.1.1.2]; exact h.1.2.1
          · simp only [Scc.Lower.plain2, Bool.and_eq_true, beq_iff_eq] at h
            rw [h.1.1.2]; rfl
        · simp only [Scc.Lower.plain2, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1.1.2]; rfl

theorem plain2_body {E excl : List String} {x : Bool} {d : Decl} (h : Scc.Lower.plain2 E excl x d = true) :
    ∃ cx2, body2 cx2 [] [] (params2 d) d.body = true ∧ (d.argTy = .unit ∨ simpleTy d.argTy = true) := by
  simp only [Scc.Lower.plain2, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨_, h.2, Or.inr (by rw [h.1.2]; rfl)⟩

/-- **A compiled block of `decl2`** (not the extern or its loop) has a
`body2` body from its parameters, its parameter `Unit` or a `simpleTy`. -/
theorem body_decl2 {E : List String} {s : Option Ty} {x : Bool} {d : Decl} (h : Scc.Lower.decl2 E s x d = true)
    (hne : Scc.Lower.isPrintExt d = false) (hnl : ¬(x = true ∧ d.name = "printL"))
    (hs : ∀ t, s = some t → simpleTy t = true) :
    ∃ cx2, body2 cx2 [] [] (params2 d) d.body = true ∧ (d.argTy = .unit ∨ simpleTy d.argTy = true) := by
  have hx : (x && d.name == "printL") = false := by
    cases x <;> simp_all
  unfold Scc.Lower.decl2 at h
  simp only [hne, hx, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · simp only [Scc.Lower.main2, Bool.and_eq_true] at h
    refine ⟨_, h.2, ?_⟩
    have h1 := h.1.2
    split at h1
    · rename_i _ t
      right
      simp only [beq_iff_eq] at h1
      rw [h1]; simp [simpleTy, hs t rfl]
    · left; simpa using h1
  · split at h
    · split at h
      · simp only [Scc.Lower.setup2, Bool.and_eq_true, beq_iff_eq] at h
        have hu : d.argTy = .unit := h.1.1.1.1.2
        have hp : params2 d = [] := by simp [params2, hu]
        exact ⟨_, by rw [hp]; exact h.2, Or.inl hu⟩
      · exact plain2_body h
    · exact plain2_body h

/-- With a setup block, its result is a `simpleTy`. -/
theorem setup_simple {p : Prog} {x : Bool} (hds : Scc.Lower.decls2 [] (Scc.Lower.setupOf p) x p = true)
    (hsp : Scc.Lower.setupPresent p = true) : ∀ t, Scc.Lower.setupOf p = some t → simpleTy t = true := by
  intro t ht
  simp only [Scc.Lower.setupPresent, ht] at hsp
  obtain ⟨r, hr, hn⟩ := List.any_eq_true.1 hsp
  have hn' : r.name = "rodata" := by simpa using hn
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds r hr
  rw [ht] at hE
  have h1 : Scc.Lower.isPrintExt r = false := by simp [Scc.Lower.isPrintExt, hn']
  unfold Scc.Lower.decl2 at hE
  simp only [h1, hn', Bool.false_eq_true, ↓reduceIte] at hE
  simp only [Scc.Lower.setup2, show ("rodata" == "printL") = false by decide,
    show ("rodata" == "main") = false by decide, show ("rodata" == "rodata") = true by decide, Bool.false_eq_true,
    and_false, ↓reduceIte, Bool.and_eq_true] at hE
  exact hE.1.2.1

/-- **At each point of the lowering's walk of a compiled block of an
`Accepted2` program, the lowering's environment has its immediates in
`imms2Of p`** (`ImmIn2`): the analogue of `immIn_imms1OfC`. `d` is any block
but the extern and its loop, lowered from its parameter bound to registers
`ps` (`lowerDeclMarks`), the lowering's context on `p` (`cx.prog = p`) with
the externs' results `Unit`. -/
theorem immIn_imms2Of {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cx : Scc.Lower.Ctx} (hprog : cx.prog = p)
    (hext : ∀ d ∈ p, (cx.externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL"))
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body, ImmIn2 (imms2Of p) q.2.1 q.1 := by
  simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hds⟩, hsp⟩, hc⟩, hlay⟩, -⟩, -⟩, -⟩, -⟩ := hp
  have hcx : CxOK cx p := ⟨hprog, fun d' hd' => by
    obtain ⟨E, hE⟩ := decl2_of_decls2 hds d' hd'
    exact retTy_decl2 hE, hext⟩
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  obtain ⟨cx2, hb, harg⟩ := body_decl2 hE hne hnl (setup_simple hds hsp)
  exact immIn_lowerEnvs2 hc hlay hcx hd hb harg hps hpl n

end Spike.Lib.LowerNode
