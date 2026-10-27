import WeakCore.TermExtStep
/-! # TermLiveProv — the protocols a program names, and their provenance along runs (item 37 S2)

`protosOf p` lists every protocol program `p` names. `ProgTyped p c` says every protocol in a runtime type or in the
code of a thread of `c` is one of them. `progTyped_stepsE` keeps it along EM0 runs (`StepsE`): the runtime closes
types by substitution (`close σs`, `TermRun.enter`) and builds new ones only from env types, `σs`, the op's own type
annotations and the program's signatures, so every protocol it ever puts in a type comes from one of those.
The general form `ProgTypedM M` (any list `M ⊇ protosOf p`) serves scenario starts, whose kids carry type arguments
that are scenario data rather than program text (user rule). -/

namespace TermLiveL3
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep

/-! ### S2: protocols a program mentions, and the provenance invariant -/

def protosTy : Ty → List Proto
  | .prod a b | .sum a b | .code a b _ => protosTy a ++ protosTy b
  | .array _ t | .ptr _ t | .ptrOpt _ t | .loc _ t | .mu t | .tex _ t | .iall t | .iex t | .refine t _ => protosTy t
  | .word _ P => [P]
  | .tok _ st => (st.map (·.1)).toList
  | .epair _ (.word P) | .tokE _ (.word P) _ => [P]
  | _ => []

def protosOp : Op → List Proto
  | .inl o _ | .inr o _ | .null _ o | .fold _ o | .newBuf _ o | .pack _ _ o | .zero o => protosTy o
  | .mkWord _ P _ _ => [P]
  | .packT _ σ t => protosTy σ ++ protosTy t
  | .call _ _ _ ts => ts.flatMap protosTy
  | .spawn _ _ T ts => protosTy T ++ ts.flatMap protosTy
  | .mkTicket _ N P _ _ => [N, P]
  | .mkEPair _ (.word P) _ _ => [P]
  | _ => []

def protosExpr : Expr → List Proto
  | .let_ _ op e => protosOp op ++ protosExpr e
  | .split _ _ _ e | .unpack _ _ _ e | .unpackT _ _ _ e | .region _ _ _ _ e | .openPub _ _ _ _ e => protosExpr e
  | .case _ _ e₁ _ e₂ | .ifnull _ e₁ _ e₂ | .parity _ _ e₁ e₂ | .ifeq _ _ e₁ e₂ => protosExpr e₁ ++ protosExpr e₂
  | .cas _ _ _ _ _ _ ok fail | .casp _ _ _ _ _ _ _ _ ok fail => protosExpr ok ++ protosExpr fail
  | .ret _ => []
  | .tail _ _ _ ts => ts.flatMap protosTy

/-- Every protocol program `p` names: in signatures and bodies (`Robust.mapDecl`'s traversal, plus epoch counters).
It must grow when static data (Route S) adds start-configuration protocols outside the program text. -/
def protosOf (p : Prog) : List Proto :=
  p.flatMap fun d => protosTy d.argTy ++ protosTy d.retTy ++ protosExpr d.body

/-- Every protocol in thread `th`'s runtime types and code is one `p` names. -/
def ThProv (p : Prog) (th : TTh) : Prop :=
  (∀ P ∈ protosExpr th.term, P ∈ protosOf p) ∧ (∀ σ ∈ th.σs, ∀ P ∈ protosTy σ, P ∈ protosOf p) ∧
  (∀ b ∈ th.env, ∀ P ∈ protosTy b.2.1, P ∈ protosOf p) ∧
  ∀ f ∈ th.stack, (∀ P ∈ protosExpr f.body, P ∈ protosOf p) ∧ (∀ P ∈ protosTy f.ty, P ∈ protosOf p) ∧
    (∀ σ ∈ f.σs, ∀ P ∈ protosTy σ, P ∈ protosOf p) ∧ ∀ b ∈ f.env, ∀ P ∈ protosTy b.2.1, P ∈ protosOf p

/-- The provenance invariant: every thread of `c` satisfies `ThProv p`. -/
def ProgTyped (p : Prog) (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ThProv p th

/-! ### Proofs: substitution, ops, thread steps, machine moves -/

theorem protosTy_shiftT (c : Nat) (t : Ty) : protosTy (t.shiftT c) = protosTy t := by
  induction t generalizing c with
  | epair r P => cases P <;> rfl
  | tokE r P e => cases P <;> rfl
  | tvar k => simp only [Ty.shiftT]; split <;> rfl
  | _ => simp_all [Ty.shiftT, protosTy]

theorem protosTy_shiftI (c : Nat) (t : Ty) : protosTy (t.shiftI c) = protosTy t := by
  induction t generalizing c with
  | epair r P => cases P <;> rfl
  | tokE r P e => cases P <;> rfl
  | tok r st => cases st <;> rfl
  | _ => simp_all [Ty.shiftI, protosTy]

theorem protosTy_shiftTN (n : Nat) (t : Ty) : protosTy (shiftTN n t) = protosTy t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shiftTN, protosTy_shiftT, ih]

theorem protosTy_shiftIN (n : Nat) (t : Ty) : protosTy (shiftIN n t) = protosTy t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shiftIN, protosTy_shiftI, ih]

theorem protosTy_substT {P : Proto} (t : Ty) : ∀ (j : Nat) (s : Ty),
    P ∈ protosTy (Ty.substT j s t) → P ∈ protosTy t ∨ P ∈ protosTy s := by
  induction t with
  | tvar k =>
      intro j s h; simp only [Ty.substT] at h
      split at h
      · exact .inr h
      · split at h <;> exact .inl h
  | prod a b iha ihb | sum a b iha ihb | code a b _ iha ihb =>
      intro j s h
      simp only [Ty.substT, protosTy, List.mem_append] at h ⊢
      rcases h with h | h
      · exact (iha j s h).imp .inl id
      · exact (ihb j s h).imp .inr id
  | array _ t ih | ptr _ t ih | ptrOpt _ t ih | loc _ t ih | refine t _ ih =>
      intro j s h; simp only [Ty.substT, protosTy] at h ⊢; exact ih j s h
  | mu t ih | tex _ t ih =>
      intro j s h; simp only [Ty.substT, protosTy] at h ⊢
      exact (ih _ _ h).imp id (fun h => by rwa [protosTy_shiftT] at h)
  | iall t ih | iex t ih =>
      intro j s h; simp only [Ty.substT, protosTy] at h ⊢
      exact (ih _ _ h).imp id (fun h => by rwa [protosTy_shiftI] at h)
  | _ => intro j s h; exact .inl h

/-- Protocols of `substTs σs c d t` come from `t` or from the `σs`. -/
theorem protosTy_substTs {P : Proto} (σs : List Ty) (t : Ty) : ∀ (c d : Nat),
    P ∈ protosTy (substTs σs c d t) → P ∈ protosTy t ∨ ∃ σ ∈ σs, P ∈ protosTy σ := by
  induction t with
  | tvar k =>
      intro c d h; simp only [substTs] at h
      split at h
      · exact .inl h
      · split at h
        · rename_i σ hσ
          rw [protosTy_shiftIN, protosTy_shiftTN] at h
          exact .inr ⟨σ, List.mem_of_getElem? hσ, h⟩
        · exact .inl h
  | prod a b iha ihb | sum a b iha ihb | code a b _ iha ihb =>
      intro c d h
      simp only [substTs, protosTy, List.mem_append] at h ⊢
      rcases h with h | h
      · exact (iha c d h).imp .inl id
      · exact (ihb c d h).imp .inr id
  | array _ t ih | ptr _ t ih | ptrOpt _ t ih | loc _ t ih | refine t _ ih | mu t ih | tex _ t ih
    | iall t ih | iex t ih =>
      intro c d h; simp only [substTs, protosTy] at h ⊢; exact ih _ _ h
  | _ => intro c d h; exact .inl h

theorem protosTy_close {P : Proto} {σs : List Ty} {t : Ty} (h : P ∈ protosTy (close σs t)) :
    P ∈ protosTy t ∨ ∃ σ ∈ σs, P ∈ protosTy σ := protosTy_substTs σs t 0 0 h

/-- Every protocol in `t` satisfies `Q`. -/
def TyIn (Q : Proto → Prop) (t : Ty) : Prop := ∀ P ∈ protosTy t, Q P

theorem tyIn_nil {Q : Proto → Prop} {t : Ty} (h : protosTy t = []) : TyIn Q t := by
  intro P hP; rw [h] at hP; cases hP

theorem evalAt_tyIn {Q : Proto → Prop} {env : Env} (henv : ∀ b ∈ env, TyIn Q b.2.1) {a : At} {t : Ty}
    {ws : List Word} (h : evalAt env a = some (t, ws)) : TyIn Q t := by
  cases a with
  | var x =>
      simp only [evalAt, lookupE, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, he⟩ := h
      have := henv b (List.mem_of_find?_eq_some hb)
      rw [he] at this; exact this
  | lit n => simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact tyIn_nil rfl
  | unit => simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact tyIn_nil rfl

theorem cellOf_tyIn {Q : Proto → Prop} {t u : Ty} {μ : Mode} (h : cellOf t = some (μ, u)) (ht : TyIn Q t) :
    TyIn Q u := by
  cases t <;> simp only [cellOf, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (obtain ⟨-, rfl⟩ := h; exact ht)

theorem bufElem_tyIn {Q : Proto → Prop} {t u : Ty} {μ : Mode} (h : bufElem t = some (μ, u)) (ht : TyIn Q t) :
    TyIn Q u := by
  unfold bufElem at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · obtain ⟨-, rfl⟩ := h; exact ht
  · obtain ⟨-, rfl⟩ := h; exact ht

theorem unfold1_tyIn {Q : Proto → Prop} {u : Ty} (ht : TyIn Q u) : TyIn Q (unfold1 u) := by
  unfold unfold1
  split
  · rename_i t
    intro P hP
    rcases protosTy_substT t 0 _ hP with h | h
    · exact ht P h
    · exact ht P h
  · exact ht

theorem compOff_tyIn {Q : Proto → Prop} : ∀ (p : List Nat) {u c : Ty} {o : Nat}, compOff u p = some (c, o) →
    TyIn Q u → TyIn Q c
  | [], u, c, o, h, ht => by
      simp only [compOff, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ht
  | j :: p, u, c, o, h, ht => by
      cases u with
      | prod a b => ?_
      | _ => simp [compOff] at h
      have ha : TyIn Q a := fun P hP => ht P (by simp [protosTy, hP])
      have hb : TyIn Q b := fun P hP => ht P (by simp [protosTy, hP])
      match j, h with
      | 0, h => simp only [compOff] at h; exact compOff_tyIn p h ha
      | 1, h =>
          simp only [compOff] at h
          cases h2 : compOff b p with
          | none => cases h1 : accs a <;> simp [h1, h2] at h
          | some co =>
              obtain ⟨c', o'⟩ := co
              have : c = c' := by cases h1 : accs a <;> simp [h1, h2] at h; exact h.1.symm
              subst this; exact compOff_tyIn p h2 hb
      | _ + 2, h => simp [compOff] at h

theorem lookupE_tyIn {Q : Proto → Prop} {env : Env} (henv : ∀ b ∈ env, TyIn Q b.2.1) {y : String} {t : Ty}
    {ws : List Word} (h : lookupE env y = some (t, ws)) : TyIn Q t := evalAt_tyIn (a := .var y) henv h

theorem tyIn_close {Q : Proto → Prop} {σs : List Ty} (hσ : ∀ σ ∈ σs, TyIn Q σ) {t : Ty} (ht : TyIn Q t) :
    TyIn Q (close σs t) := by
  intro P hP
  rcases protosTy_close hP with h | ⟨σ, hσm, h⟩
  · exact ht P h
  · exact hσ σ hσm P h

theorem tyIn_prod {Q : Proto → Prop} {a b : Ty} (ha : TyIn Q a) (hb : TyIn Q b) : TyIn Q (.prod a b) := by
  intro P hP; simp only [protosTy, List.mem_append] at hP; exact hP.elim (ha P) (hb P)

theorem tyIn_sum {Q : Proto → Prop} {a b : Ty} (ha : TyIn Q a) (hb : TyIn Q b) : TyIn Q (.sum a b) := by
  intro P hP; simp only [protosTy, List.mem_append] at hP; exact hP.elim (ha P) (hb P)

theorem unfold1_eq_tyIn {Q : Proto → Prop} {u v : Ty} (h : unfold1 u = v) (ht : TyIn Q u) : TyIn Q v :=
  h ▸ unfold1_tyIn ht

theorem fetchRtTy_tyIn {Q : Proto → Prop} {t : Ty} (ht : TyIn Q t) : TyIn Q (fetchRtTy t) := by
  unfold fetchRtTy
  split
  · rename_i r P hw
    split
    · intro P' hP
      simp only [fetchEpochTy, protosTy, List.nil_append, List.mem_singleton] at hP
      subst hP
      apply ht
      unfold wordOf at hw
      split at hw <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hw <;>
        (obtain ⟨-, rfl⟩ := hw; simp [protosTy])
    · exact tyIn_nil rfl
  · exact tyIn_nil rfl

theorem find?_tyIn {Q : Proto → Prop} {p : Prog} (hp : ∀ d ∈ p, TyIn Q d.argTy ∧ TyIn Q d.retTy) {f : String}
    {d : Decl} (h : p.find? (·.name == f) = some d) : ∀ k : CodeKind, TyIn Q (.code d.argTy d.retTy k) := by
  intro k
  have := hp d (List.mem_of_find?_eq_some h)
  intro P hP; simp only [protosTy, List.mem_append] at hP; exact hP.elim (this.1 P) (this.2 P)

open Lean Meta Elab Tactic in
/-- Forward reasoning for `evalOp_tyIn`: add the `TyIn` facts every `evalAt`/`lookupE`/`cellOf`/... hypothesis gives. -/
local elab "lv_eo_fwd" : tactic => do
  for _ in [0, 1, 2] do
    let hs ← withMainContext do
      let lctx ← getLCtx
      let mut out := #[]
      for d in lctx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        match ty.eq? with
        | some (_, lhs, _) =>
            match lhs.getAppFn.constName? with
            | some n => out := out.push (d.fvarId, n)
            | none => pure ()
        | none => pure ()
      pure out
    for (h, n) in hs do
      let mk : Option (Term → TacticM Term) :=
        if n == ``evalAt then some fun t => `(evalAt_tyIn $(mkIdent `henv) $t)
        else if n == ``lookupE then some fun t => `(lookupE_tyIn $(mkIdent `henv) $t)
        else if n == ``cellOf then some fun t => `(cellOf_tyIn $t (by assumption))
        else if n == ``bufElem then some fun t => `(bufElem_tyIn $t (by assumption))
        else if n == ``compOff then some fun t => `(compOff_tyIn _ $t (by assumption))
        else if n == ``unfold1 then some fun t => `(unfold1_eq_tyIn $t (by assumption))
        else if n == ``List.find? then some fun t => `(find?_tyIn $(mkIdent `hp) $t)
        else none
      if let some mk := mk then
        let s ← saveState
        try
          withMainContext do
            let hsyn ← Term.exprToSyntax (mkFVar h)
            let pf ← mk hsyn
            evalTactic (← `(tactic| have := $pf))
        catch _ => s.restore

set_option hygiene false in
local macro "lv_eo_fin" : tactic => `(tactic| (lv_eo_fwd; (try dsimp only); first
    | (intro P hP; simp [protosTy] at hP; done)
    | exact tyIn_close hσ (fun P hP => hop P (by simp [protosOp, hP]))
    | (simp only [protosOp, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_singleton,
        forall_eq_or_imp, forall_eq, List.not_mem_nil] at hop; simp_all [TyIn, protosTy]; done)
    | exact fetchRtTy_tyIn (evalAt_tyIn henv ‹_›)
    | exact ‹∀ k : CodeKind, TyIn _ (.code _ _ k)› _
    | exact tyIn_prod (by assumption) (by assumption)
    | exact tyIn_sum (by assumption) (tyIn_close hσ (fun P hP => hop P (by simp [protosOp, hP])))
    | exact tyIn_sum (tyIn_close hσ (fun P hP => hop P (by simp [protosOp, hP]))) (by assumption)
    | exact tyIn_sum (evalAt_tyIn henv ‹_›) (tyIn_close hσ (fun P hP => hop P (by simp [protosOp, hP])))
    | exact tyIn_sum (tyIn_close hσ (fun P hP => hop P (by simp [protosOp, hP]))) (evalAt_tyIn henv ‹_›)
    | fail "lv_eo_fin"))

set_option hygiene false in
local macro "lv_eo_main" : tactic => `(tactic| (simp only [evalOp] <;> (repeat' split) <;>
    simp [ol, Option.bind_eq_some_iff, List.mem_map, List.mem_flatMap, List.mem_filterMap] <;>
    intros <;> subst_vars <;>
    first
    | (intro P hP; simp [protosTy] at hP; done)
    | exact evalAt_tyIn henv ‹_›
    | exact lookupE_tyIn henv ‹_›
    | (exact tyIn_close hσ (fun P hP => hop P (by simp [protosOp, hP])))
    | ((iterate 3 (all_goals (try (rename_i h; revert h; (repeat' split) <;>
          simp [Option.bind_eq_some_iff] <;> intros <;> subst_vars)))) <;> lv_eo_fin)))

set_option maxHeartbeats 1000000 in
/-- The runtime type an op binds has only protocols of the env, the `σs`, the op, or the program's signatures. -/
theorem evalOp_tyIn {Q : Proto → Prop} {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {x : St × Ty × List Word}
    (henv : ∀ b ∈ env, TyIn Q b.2.1) (hσ : ∀ σ ∈ σs, TyIn Q σ) (hop : ∀ P ∈ protosOp op, Q P)
    (hp : ∀ d ∈ g.p, TyIn Q d.argTy ∧ TyIn Q d.retTy)
    (hx : x ∈ evalOp g env σs s op) : TyIn Q x.2.1 := by
  revert hx
  cases op
  case mkEPair r P v0 v1 => cases P <;> lv_eo_main
  case pair a b =>
    simp only [evalOp]; simp [ol, Option.bind_eq_some_iff]; intros; subst_vars
    exact tyIn_prod (evalAt_tyIn henv ‹evalAt env a = _›) (evalAt_tyIn henv ‹evalAt env b = _›)
  case inl τ a =>
    simp only [evalOp]; split <;> simp [List.mem_map, List.mem_flatMap]; intros; subst_vars
    exact tyIn_sum (evalAt_tyIn henv ‹evalAt env a = _›) (tyIn_close hσ (fun P hP => hop P (by simp [protosOp, hP])))
  case inr τ a =>
    simp only [evalOp]; split <;> simp [List.mem_map, List.mem_flatMap]; intros; subst_vars
    exact tyIn_sum (tyIn_close hσ (fun P hP => hop P (by simp [protosOp, hP]))) (evalAt_tyIn henv ‹evalAt env a = _›)
  case fop | fcmp | fop1 | lane | setLane =>
    simp only [evalOp]; simp [ol, Option.bind_eq_some_iff]
    intros; subst_vars
    rename_i h; revert h
    simp only [or_imp, forall_exists_index, and_imp]
    (try refine ⟨?_, ?_⟩) <;> intros <;> subst_vars <;> exact tyIn_nil rfl
  all_goals lv_eo_main

/-- `ThProv` at an arbitrary protocol list `M`. -/
def ThProvM (M : List Proto) (th : TTh) : Prop :=
  (∀ P ∈ protosExpr th.term, P ∈ M) ∧ (∀ σ ∈ th.σs, ∀ P ∈ protosTy σ, P ∈ M) ∧
  (∀ b ∈ th.env, ∀ P ∈ protosTy b.2.1, P ∈ M) ∧
  ∀ f ∈ th.stack, (∀ P ∈ protosExpr f.body, P ∈ M) ∧ (∀ P ∈ protosTy f.ty, P ∈ M) ∧
    (∀ σ ∈ f.σs, ∀ P ∈ protosTy σ, P ∈ M) ∧ ∀ b ∈ f.env, ∀ P ∈ protosTy b.2.1, P ∈ M

theorem mem_protosOf {p : Prog} {d : Decl} (hd : d ∈ p) :
    TyIn (· ∈ protosOf p) d.argTy ∧ TyIn (· ∈ protosOf p) d.retTy ∧ ∀ P ∈ protosExpr d.body, P ∈ protosOf p := by
  refine ⟨fun P hP => ?_, fun P hP => ?_, fun P hP => ?_⟩ <;>
    exact List.mem_flatMap.2 ⟨d, hd, by simp [hP]⟩

theorem tyIn_substT {Q : Proto → Prop} {j : Nat} {s t : Ty} (ht : TyIn Q t) (hs : TyIn Q s) :
    TyIn Q (Ty.substT j s t) := fun P hP => (protosTy_substT t j s hP).elim (ht P) (hs P)

theorem tyIn_retOf {Q : Proto → Prop} {a b : Ty} (ha : TyIn Q a) (hb : TyIn Q b) : TyIn Q (retOf a b) := by
  unfold retOf; split
  · intro P hP; exact ha P (by simp [protosTy, hP])
  · exact hb

/-- Pieces of a thread's code: every protocol of a sub-expression is one of the whole. -/
theorem sub_of {M : List Proto} {e e' : Expr} (h : ∀ P ∈ protosExpr e, P ∈ M) (hs : ∀ P ∈ protosExpr e', P ∈ protosExpr e) :
    ∀ P ∈ protosExpr e', P ∈ M := fun P hP => h P (hs P hP)

theorem withS_thProvM {M : List Proto} {th : TTh} {s : St} : ThProvM M (withS th s) ↔ ThProvM M th := Iff.rfl

theorem enter_thProvM {M : List Proto} {g : G} (hM : ∀ P ∈ protosOf g.p, P ∈ M) {th th' : TTh} {f : String}
    {ts : List Ty} {a : At} (hts : ∀ t ∈ ts, TyIn (· ∈ M) t) (h : enter g th f ts a = some th') (hσ : ∀ σ ∈ th.σs, TyIn (· ∈ M) σ)
    (hS : ∀ fr ∈ th.stack, (∀ P ∈ protosExpr fr.body, P ∈ M) ∧ (∀ P ∈ protosTy fr.ty, P ∈ M) ∧
      (∀ σ ∈ fr.σs, ∀ P ∈ protosTy σ, P ∈ M) ∧ ∀ b ∈ fr.env, ∀ P ∈ protosTy b.2.1, P ∈ M) :
    ThProvM M th' := by
  simp only [enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨d, hd, ⟨rt, ws⟩, -, rfl⟩ := h
  have hdm := mem_protosOf (List.mem_of_find?_eq_some hd)
  have hσ' : ∀ σ ∈ (ts.map (close th.σs)).reverse, TyIn (· ∈ M) σ := by
    intro σ hm
    simp only [List.mem_reverse, List.mem_map] at hm
    obtain ⟨t, ht, rfl⟩ := hm
    exact tyIn_close hσ (hts t ht)
  refine ⟨fun P hP => hM P (hdm.2.2 P hP), hσ', ?_, hS⟩
  intro b hb
  simp only [List.mem_singleton] at hb
  subst hb
  exact tyIn_close hσ' (fun P hP => hM P (hdm.1 P hP))

theorem mem_ol {α : Type} {o : Option α} {y : α} : y ∈ ol o ↔ o = some y := by
  cases o <;> simp [ol, eq_comm]

theorem env_cons {M : List Proto} {env : Env} (hE : ∀ b ∈ env, ∀ P ∈ protosTy b.2.1, P ∈ M)
    {b' : String × Ty × List Word} (hb : TyIn (· ∈ M) b'.2.1) : ∀ b ∈ b' :: env, ∀ P ∈ protosTy b.2.1, P ∈ M := by
  intro b hm; simp only [List.mem_cons] at hm; rcases hm with rfl | hm
  · exact hb
  · exact hE b hm

theorem tyIn_of_sub {Q : Proto → Prop} {a b : Ty} (ha : TyIn Q a) (h : ∀ P ∈ protosTy b, P ∈ protosTy a) : TyIn Q b :=
  fun P hP => ha P (h P hP)

local macro "lv_tsub" : tactic =>
  `(tactic| (intro P hP; simp only [protosExpr, List.mem_append]; first | exact hP | exact .inl hP | exact .inr hP))

theorem evalAt_sub {Q : Proto → Prop} {env : Env} (hE : ∀ b ∈ env, TyIn Q b.2.1) {a : At} {t : Ty}
    {ws : List Word} (h : evalAt env a = some (t, ws)) {t' : Ty} (hs : ∀ P ∈ protosTy t', P ∈ protosTy t) :
    TyIn Q t' := tyIn_of_sub (evalAt_tyIn hE h) hs

theorem ite_thProvM {M : List Proto} {c : Prop} [Decidable c] {A B : TTh} (hA : ThProvM M A) (hB : ThProvM M B) :
    ThProvM M (if c then A else B) := by
  split
  · exact hA
  · exact hB

set_option maxHeartbeats 2000000 in
theorem tstep_thProvM {M : List Proto} {g : G} (hM : ∀ P ∈ protosOf g.p, P ∈ M) {mem : WeakMem.Memory}
    {pairs : List WeakMem.Ts} {th : TTh} {y : WeakMem.Memory × List WeakMem.Ts × TTh} (hth : ThProvM M th)
    (hy : y ∈ tstep g mem pairs th) : ThProvM M y.2.2 := by
  obtain ⟨hT, hσ, hE, hS⟩ := hth
  have hp : ∀ d ∈ g.p, TyIn (· ∈ M) d.argTy ∧ TyIn (· ∈ M) d.retTy := fun d hd =>
    have h := mem_protosOf hd
    ⟨fun P hP => hM P (h.1 P hP), fun P hP => hM P (h.2.1 P hP)⟩
  unfold tstep at hy
  split at hy
  · -- call
    rename_i x f is a ts e heq
    rw [heq] at hT
    simp only [mem_ol, Option.map_eq_some_iff, Option.bind_eq_some_iff] at hy
    obtain ⟨th', ⟨fr, hfr, hen⟩, rfl⟩ := hy
    have hts : ∀ t ∈ ts, TyIn (· ∈ M) t := fun t ht P hP =>
      hT P (by simp only [protosExpr, protosOp, List.mem_append, List.mem_flatMap]; exact .inl ⟨t, ht, hP⟩)
    simp only [callFrame, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hfr
    obtain ⟨d, hd, rfl⟩ := hfr
    have hσ' : ∀ σ ∈ (ts.map (close th.σs)).reverse, TyIn (· ∈ M) σ := by
      intro σ hm
      simp only [List.mem_reverse, List.mem_map] at hm
      obtain ⟨t, ht, rfl⟩ := hm
      exact tyIn_close hσ (hts t ht)
    refine enter_thProvM hM hts hen hσ ?_
    intro f' hf'
    simp only [List.mem_cons] at hf'
    rcases hf' with rfl | hf'
    · exact ⟨sub_of (e' := e) hT (fun P hP => by simp only [protosExpr, List.mem_append]; exact .inr hP),
        tyIn_close hσ' (hp d (List.mem_of_find?_eq_some hd)).2, hσ, hE⟩
    · exact hS f' hf'
  · -- callc
    rename_i x f a e heq
    rw [heq] at hT
    split at hy
    · rename_i tf w hf
      split at hy
      · split at hy
        · rename_i d _
          simp only [mem_ol, Option.map_eq_some_iff, Option.bind_eq_some_iff] at hy
          obtain ⟨th', ⟨fr, hfr, hen⟩, rfl⟩ := hy
          simp only [callFrame, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at hfr
          obtain ⟨d', hd', rfl⟩ := hfr
          refine enter_thProvM hM (ts := []) (fun t ht => by cases ht) hen hσ ?_
          intro f' hf'
          simp only [List.mem_cons] at hf'
          rcases hf' with rfl | hf'
          · refine ⟨sub_of (e' := e) hT (fun P hP => by simp only [protosExpr, List.mem_append]; exact .inr hP),
              ?_, hσ, hE⟩
            exact tyIn_retOf (evalAt_tyIn hE hf)
              (tyIn_close (fun σ hm => by simp at hm) (hp d' (List.mem_of_find?_eq_some hd')).2)
          · exact hS f' hf'
        · cases hy
      · cases hy
    · cases hy
  · -- let (op)
    rename_i x op e hn1 hn2 heq
    rw [heq] at hT
    simp only [List.mem_map] at hy
    obtain ⟨⟨s', t, ws⟩, hm, rfl⟩ := hy
    have ht := evalOp_tyIn (Q := (· ∈ M)) (op := op) hE hσ
      (fun P hP => hT P (by simp only [protosExpr, List.mem_append]; exact .inl hP)) hp hm
    exact ⟨sub_of (e' := e) hT (fun P hP => by simp only [protosExpr, List.mem_append]; exact .inr hP), hσ,
      env_cons hE ht, hS⟩
  · -- split
    rename_i a x y e heq
    rw [heq] at hT
    split at hy
    · rename_i u w ws hev
      split at hy
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        subst hy
        have h1 := evalAt_tyIn hE hev
        exact ⟨sub_of (e' := e) hT (by lv_tsub), hσ,
          env_cons (env_cons hE (tyIn_of_sub h1 (by intro P hP; simp [protosTy, hP])))
            (tyIn_of_sub h1 (by intro P hP; simp [protosTy, hP])), hS⟩
      · cases hy
    · cases hy
  · -- unpack
    rename_i a i x e heq
    rw [heq] at hT
    split at hy
    · rename_i b ws hev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      exact ⟨sub_of (e' := e) hT (by lv_tsub), hσ, env_cons hE (evalAt_sub hE hev (by intro P hP; simpa [protosTy] using hP)), hS⟩
    · cases hy
  · -- unpackT
    rename_i a α x e heq
    rw [heq] at hT
    split at hy
    · rename_i κ b ws hev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      refine ⟨sub_of (e' := e) hT (by lv_tsub), ?_, env_cons hE (tyIn_substT (evalAt_sub hE hev (by intro P hP; simpa [protosTy] using hP)) (tyIn_nil rfl)), hS⟩
      intro σ hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact tyIn_nil rfl
      · exact hσ σ hm
    · cases hy
  · -- region
    rename_i a r pn tn e heq
    rw [heq] at hT
    split at hy
    · rename_i μ u ws hev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      exact ⟨sub_of (e' := e) hT (by lv_tsub), hσ, env_cons (env_cons hE (evalAt_sub hE hev (by intro P hP; simpa [protosTy] using hP))) (tyIn_nil rfl), hS⟩
    · rename_i μ u ψ ws hev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      exact ⟨sub_of (e' := e) hT (by lv_tsub), hσ, env_cons (env_cons hE (evalAt_sub hE hev (by intro P hP; simpa [protosTy] using hP))) (tyIn_nil rfl), hS⟩
    · cases hy
  · -- openPub
    rename_i a r pn cn e heq
    rw [heq] at hT
    split at hy
    · rename_i μ u ws hev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      exact ⟨sub_of (e' := e) hT (by lv_tsub), hσ, env_cons (env_cons hE (evalAt_sub hE hev (by intro P hP; simpa [protosTy] using hP))) (tyIn_nil rfl), hS⟩
    · cases hy
  · -- case
    rename_i a x e₁ y e₂ heq
    rw [heq] at hT
    split at hy
    · rename_i t u w ws hev
      simp only [List.mem_flatMap, List.mem_map] at hy
      obtain ⟨⟨s1, j, q⟩, -, hy⟩ := hy
      have hu := evalAt_sub (t' := u) hE hev (by intro P hP; simp [protosTy, hP])
      have hw := evalAt_sub (t' := w) hE hev (by intro P hP; simp [protosTy, hP])
      by_cases hj : j < (armsOf u).length
      · simp only [hj, ite_true] at hy
        obtain ⟨⟨s2, q'⟩, -, rfl⟩ := hy
        exact ⟨sub_of (e' := e₁) hT (by lv_tsub), hσ, env_cons hE hu, hS⟩
      · simp only [hj, ite_false] at hy
        obtain ⟨⟨s2, q'⟩, -, rfl⟩ := hy
        exact ⟨sub_of (e' := e₂) hT (by lv_tsub), hσ, env_cons hE hw, hS⟩
    · cases hy
  · -- ifnull
    rename_i a e₁ y e₂ heq
    rw [heq] at hT
    split at hy
    · rename_i μ u w hev
      split at hy
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        subst hy
        exact ⟨sub_of (e' := e₁) hT (by lv_tsub), hσ, hE, hS⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        subst hy
        exact ⟨sub_of (e' := e₂) hT (by lv_tsub), hσ,
          env_cons hE (evalAt_sub hE hev (by intro P hP; simpa [protosTy] using hP)), hS⟩
      · cases hy
    · cases hy
  · -- parity
    rename_i a k ev od heq
    rw [heq] at hT
    split at hy
    · split at hy
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        subst hy
        refine ⟨?_, hσ, hE, hS⟩
        dsimp only
        split
        · exact sub_of (e' := ev) hT (by lv_tsub)
        · exact sub_of (e' := od) hT (by lv_tsub)
      · cases hy
    · cases hy
  · -- ifeq
    rename_i a b yes no heq
    rw [heq] at hT
    split at hy
    · split at hy
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        subst hy
        refine ⟨?_, hσ, hE, hS⟩
        dsimp only
        split
        · exact sub_of (e' := yes) hT (by lv_tsub)
        · exact sub_of (e' := no) hT (by lv_tsub)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        subst hy
        refine ⟨?_, hσ, hE, hS⟩
        dsimp only
        split
        · exact sub_of (e' := yes) hT (by lv_tsub)
        · exact sub_of (e' := no) hT (by lv_tsub)
      · cases hy
    · cases hy
  · -- cas
    rename_i acq rel w e v t ok fail heq
    rw [heq] at hT
    split at hy
    · split at hy
      · simp only [List.mem_map] at hy
        obtain ⟨⟨mem', th'⟩, -, rfl⟩ := hy
        exact ite_thProvM
          ⟨sub_of (e' := ok) hT (by lv_tsub), hσ, env_cons hE (tyIn_nil rfl), hS⟩
          ⟨sub_of (e' := fail) hT (by lv_tsub), hσ, hE, hS⟩
      · cases hy
    · cases hy
  · -- casp
    rename_i acq rel w e0 e1 v0 v1 t ok fail heq
    rw [heq] at hT
    split at hy
    · split at hy
      · simp only [List.mem_map] at hy
        obtain ⟨⟨mem', pairs', th'⟩, -, rfl⟩ := hy
        exact ite_thProvM
          ⟨sub_of (e' := ok) hT (by lv_tsub), hσ, env_cons hE (tyIn_nil rfl), hS⟩
          ⟨sub_of (e' := fail) hT (by lv_tsub), hσ, hE, hS⟩
      · cases hy
    · cases hy
  · -- ret
    split at hy
    · rename_i f rest ty ws hst hev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      have hf := hS f (by rw [hst]; exact List.mem_cons_self ..)
      refine ⟨hf.1, hf.2.2.1, env_cons hf.2.2.2 hf.2.1, fun f' hf' => hS f' (by rw [hst]; exact List.mem_cons_of_mem _ hf')⟩
    · cases hy
  · -- tail
    rename_i f is a ts heq
    rw [heq] at hT
    simp only [mem_ol, Option.map_eq_some_iff] at hy
    obtain ⟨th', hen, rfl⟩ := hy
    exact enter_thProvM hM (fun t ht P hP => hT P (by simp only [protosExpr, List.mem_flatMap]; exact ⟨t, ht, hP⟩))
      hen hσ hS

/-- `ProgTyped` at an arbitrary protocol list `M`. -/
def ProgTypedM (M : List Proto) (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ThProvM M th

theorem progTypedM_set {M : List Proto} {c : Cfg} {i : Nat} {y : TTh} (hc : ProgTypedM M c) (hy : ThProvM M y)
    {j : Nat} {t : TTh} (h : (c.ths.set! i y)[j]? = some t) : ThProvM M t := by
  rcases set_get_cases h with ⟨-, rfl⟩ | ⟨-, h⟩
  · exact hy
  · exact hc j t h

theorem progTypedM_step {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {M : List Proto}
    (hM : ∀ P ∈ protosOf p, P ∈ M) {c c' : Cfg} (hc : ProgTypedM M c) (h : Step p k arch c c') :
    ProgTypedM M c' := by
  cases h with
  | thread i hs _ =>
      unfold threadSteps at hs
      split at hs
      · cases hs
      · rename_i th hth
        simp only [List.mem_map] at hs
        obtain ⟨⟨mem, pairs, th'⟩, hm, rfl⟩ := hs
        have := tstep_thProvM (g := gOf p k arch c i) hM (hc i th hth) hm
        intro j t hj
        exact progTypedM_set hc this hj
  | prom i a v w _ _ _ =>
      intro j t hj
      unfold promise at hj
      split at hj
      · exact hc j t hj
      · rename_i th hth
        exact progTypedM_set (y := { th with promises := th.promises ++ [c.mem.size] }) hc (hc i th hth) hj

theorem progTypedM_spawn {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap : Nat} {M : List Proto}
    {c c' : Cfg} (hc : ProgTypedM M c) (h : Spawn p k arch cap c c') : ProgTypedM M c' := by
  cases h with
  | mk i x f a T ts e th rt ws h1 h2 h3 h4 h5 =>
      obtain ⟨hT, hσ, hE, hS⟩ := hc i th h1
      rw [h2] at hT
      simp only [protosExpr, protosOp, List.mem_append, List.mem_flatMap] at hT
      intro j t hj
      simp only [spawnCfg, spawnT, Array.getElem?_push] at hj
      split at hj
      · simp only [Option.some.injEq] at hj
        subst hj
        unfold ThProvM
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro P hP
          simp only [spawnKid, protosExpr, List.mem_flatMap] at hP
          exact hT P (.inl (.inr hP))
        · intro σ hσ; simp [spawnKid] at hσ
        · intro b hb
          simp only [spawnKid, List.mem_singleton] at hb
          subst hb
          exact fun P hP => hT P (.inl (.inl hP))
        · intro f hf; simp [spawnKid] at hf
      · refine progTypedM_set (y := spawnPar c i th x e) hc ⟨fun P hP => hT P (.inr hP), hσ, ?_, hS⟩ hj
        intro b hb
        simp only [spawnPar, withS, List.mem_cons] at hb
        rcases hb with rfl | hb
        · intro P hP; simp [protosTy] at hP
        · exact hE b hb

/-- (D4) `wake` changes only permits, which `ProgTypedM` does not read. -/
theorem progTypedM_wake {M : List Proto} {c : Cfg} (i : Nat) (v : WeakMem.Ts) (n : ExtName) (ws : List Word)
    (hc : ProgTypedM M c) : ProgTypedM M (wake c i v n ws) := fun j t hj => by
  rcases wake_get c i v n ws j with h | ⟨th, u, h1, h2⟩
  · rw [h] at hj; exact hc j t hj
  · rw [h2] at hj; cases hj; exact hc j th h1

theorem progTypedM_ext {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {M : List Proto}
    {c c' : Cfg} (hc : ProgTypedM M c) (h : Ext p k arch c c') : ProgTypedM M c' := by
  cases h with
  | mk i x n a e th rt ws rs h1 h2 h3 h4 h5 h6 =>
      obtain ⟨hT, hσ, hE, hS⟩ := hc i th h1
      rw [h2] at hT
      simp only [protosExpr, protosOp, List.nil_append] at hT
      have hnew : ∀ (t : Ty), protosTy t = [] → ∀ ws' (w : WeakMem.VState) (b : Option WeakMem.Ts),
          ThProvM M { th with term := e, env := (x, t, ws') :: th.env, vs := w, permit := b } :=
        fun t ht ws' _ _ => ⟨hT, hσ, fun b hb => by
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · intro P hP; rw [ht] at hP; cases hP
          · exact hE b hb, hS⟩
      refine progTypedM_wake i _ n ws ?_
      intro j t hj
      unfold extCfg at hj
      split at hj
      · unfold curCfg at hj
        split at hj
        · exact progTypedM_set hc (hnew .tid rfl _ _ _) hj
        · refine progTypedM_set hc ?_ hj
          refine ⟨hT, hσ, fun b hb => ?_, hS⟩
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · intro P hP; simp [protosTy] at hP
          · exact hE b hb
      · exact progTypedM_set hc (hnew _ (by cases n <;> rfl) _ _ _) hj

/-- **S2.** Provenance along an EM0 run, for any protocol list containing the program's. -/
theorem progTypedM_stepsE {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap : Nat} {M : List Proto}
    (hM : ∀ P ∈ protosOf p, P ∈ M) {c0 c : Cfg} (h0 : ProgTypedM M c0) (hr : StepsE p k arch cap c0 c) :
    ProgTypedM M c :=
  stepsG_pres (fun _ _ hs hc => progTypedM_step hM hc hs)
    (fun _ _ hs hc => hs.elim (progTypedM_spawn hc) (progTypedM_ext hc)) hr h0

theorem thProv_iff {p : Prog} {th : TTh} : ThProv p th ↔ ThProvM (protosOf p) th := Iff.rfl

theorem progTyped_iff {p : Prog} {c : Cfg} : ProgTyped p c ↔ ProgTypedM (protosOf p) c := Iff.rfl

/-- **S2.** `ProgTyped` along EM0 runs. -/
theorem progTyped_stepsE {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap : Nat} {c0 c : Cfg}
    (h0 : ProgTyped p c0) (hr : StepsE p k arch cap c0 c) : ProgTyped p c :=
  progTypedM_stepsE (fun _ h => h) h0 hr

end TermLiveL3
#print axioms TermLiveL3.protosTy_substTs
#print axioms TermLiveL3.evalOp_tyIn
#print axioms TermLiveL3.tstep_thProvM
#print axioms TermLiveL3.progTypedM_stepsE
#print axioms TermLiveL3.progTyped_stepsE
