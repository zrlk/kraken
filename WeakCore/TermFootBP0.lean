import WeakCore.TermFootNG
import WeakCore.TermPtrRtsDefs
import WeakCore.TermOwnG0Defs

/-! # TermFootBP0 (FootBP): the stepper export `FootBP` and its generic lemmas

`FootBP g E' th r` (text): (1) a counted word of the result environment naming a label
the step allocates is either in an old binding or names a box of `E'`; (2) a label `th` publishes
has a frontier in `E'`.
-/

namespace TermFootBP0
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermPlant
open TermPtrRts TermOwnG0Defs
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- Clause (1) of `FootBP`, from allocation count `n` and old environment `env`. -/
def FootB1 (g : G) (n : Nat) (env : Env) (r : Memory × List Ts × TTh) (E' : TEnv) : Prop :=
  ∀ l, FreshIn g n r.2.2.nalloc l → ∀ b ∈ r.2.2.env, ∀ w ∈ pubWords b.2.1 b.2.2, Names l w →
    E'.box l ≠ none ∨ b ∈ env

/-- **The stepper export `FootBP`**. -/
def FootBP (g : G) (E' : TEnv) (th : TTh) (r : Memory × List Ts × TTh) : Prop :=
  (∀ l, FreshIn g th.nalloc r.2.2.nalloc l → ∀ b ∈ r.2.2.env, ∀ w ∈ pubWords b.2.1 b.2.2, Names l w →
    E'.box l ≠ none ∨ b ∈ th.env) ∧
  (∀ l, PubAt th l → E'.pfr l ≠ none)

/-- The producers' witness predicate: `E.sto` kept and clause (1) at the result `(mem, pairs, th')`. -/
def QB (E : TEnv) (g : G) (n : Nat) (env : Env) (mem : Memory) (pairs : List Ts) (th' : TTh) (E' : TEnv) : Prop :=
  TermFootNP.StoEq E E' ∧ FootB1 g n env (mem, pairs, th') E'

theorem footBP_of {g : G} {E' : TEnv} {th : TTh} {r : Memory × List Ts × TTh}
    (h1 : FootB1 g th.nalloc th.env r E') (h2 : ∀ l, PubAt th l → E'.pfr l ≠ none) : FootBP g E' th r :=
  ⟨h1, h2⟩

theorem footB1_nalloc {g : G} {n : Nat} {env : Env} {r : Memory × List Ts × TTh} {E' : TEnv}
    (h : r.2.2.nalloc ≤ n) : FootB1 g n env r E' := by
  intro l ⟨j, h1, h2, _⟩
  exact absurd (Nat.lt_of_lt_of_le h2 h) (Nat.not_lt_of_le h1)

theorem footB1_cons {g : G} {n : Nat} {env : Env} {r : Memory × List Ts × TTh} {E' : TEnv}
    {b0 : String × Ty × List Word} (henv : r.2.2.env = b0 :: env)
    (h0 : ∀ l, FreshIn g n r.2.2.nalloc l → ∀ w ∈ pubWords b0.2.1 b0.2.2, Names l w → E'.box l ≠ none) :
    FootB1 g n env r E' := by
  intro l hl b hb w hw hn
  rw [henv] at hb
  rcases List.mem_cons.1 hb with e | hb
  · subst e; exact .inl (h0 l hl w hw hn)
  · exact .inr hb

theorem freshIn_one {g : G} {n n' : Nat} {l : AllocLabel} (h : FreshIn g n n' l) (hn : n' ≤ n + 1) :
    l = freshLabel g.lbase g.n g.i n := by
  obtain ⟨j, h1, h2, rfl⟩ := h
  have : j = n := by omega
  rw [this]

/-- A box producer: the new binding's words name (at a fresh label) only the new box. -/
theorem footB1_box {g : G} {n : Nat} {env : Env} {r : Memory × List Ts × TTh} {E' : TEnv}
    {b0 : String × Ty × List Word} (henv : r.2.2.env = b0 :: env) (hn : r.2.2.nalloc ≤ n + 1)
    (hb : E'.box (freshLabel g.lbase g.n g.i n) ≠ none) : FootB1 g n env r E' :=
  footB1_cons henv fun l hl _ _ _ => by rw [freshIn_one hl hn]; exact hb

theorem nalloc_alloc_boxE {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc} {ws : List Word}
    {s : St} {r : St × Word} {b : Bool} (hpl : PromLt s) (hr : r ∈ alloc k arch lbl us ws s) :
    (if b then fenceS r.1 .st else r.1).nalloc = s.nalloc + 1 := by
  have h := (alloc_growsP hpl r hr).2.2.1
  cases b <;> simp [fenceS, h]

/-- `new`: the result binds an `own` reference, which counts no word. -/
theorem footB1_new {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {a : At} {e : Expr}
    {r : Memory × List Ts × TTh} {E' : TEnv} (hterm : th.term = .let_ x (.new a) e)
    (hr : r ∈ tstep g mem pairs th) : FootB1 g th.nalloc th.env r E' := by
  simp only [tstep, hterm, List.mem_map] at hr
  obtain ⟨⟨s', t, ws⟩, hev, rfl⟩ := hr
  refine footB1_cons (b0 := (x, t, ws)) rfl fun l _ w hw _ => ?_
  simp only [evalOp] at hev
  split at hev
  · simp at hev
  · split at hev
    · simp at hev
    · simp only [List.mem_map] at hev
      obtain ⟨_, _, he⟩ := hev
      cases he
      have h0 : ∀ u (vs : List Word), pubWords (.ptr .own u) vs = [] := fun u vs => by
        simp only [pubWords, sNo, mPub]; rfl
      rw [h0] at hw
      cases hw

/-- `newBuf`: the result binds an `own` buffer locative, which counts no word. -/
theorem footB1_newBuf {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {n : At} {τ : Ty}
    {e : Expr} {r : Memory × List Ts × TTh} {E' : TEnv} (hterm : th.term = .let_ x (.newBuf n τ) e)
    (hr : r ∈ tstep g mem pairs th) : FootB1 g th.nalloc th.env r E' := by
  simp only [tstep, hterm, List.mem_map] at hr
  obtain ⟨⟨s', t, ws⟩, hev, rfl⟩ := hr
  refine footB1_cons (b0 := (x, t, ws)) rfl fun l _ w hw _ => ?_
  simp only [evalOp, ol] at hev
  have ht : ∃ k i, t = Ty.refine (.loc .own (.array (.lit k) (close th.σs τ))) (.ini (.lit i)) := by
    revert hev
    cases h1 : evalAt th.env n with
    | none => simp
    | some v =>
      cases h2 : numOf v.2 with
      | none => simp [h2]
      | some k =>
        cases h3 : accs (close th.σs τ) with
        | none => simp
        | some us =>
          simp only [h2, Option.bind_some, Option.pure_def, Option.toList_some, List.mem_singleton,
            Prod.mk.injEq, Option.bind_eq_bind]
          intro h
          exact ⟨k, _, h.2.1⟩
  obtain ⟨k, i, rfl⟩ := ht
  simp [pubWords, sNo, mPub] at hw

/-- A `publish` names only its operand's label. -/
theorem pubAt_eq {th : TTh} {x : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word} {ad : Address}
    (hterm : th.term = .let_ x (.publish a) e) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) {l : AllocLabel} (h : PubAt th l) : l = ad.label := by
  obtain ⟨y, a', e', rt', ws', ad', h1, h2, h3, rfl⟩ := h
  rw [hterm] at h1
  cases h1
  rw [hea] at h2
  cases h2
  rw [hws] at h3
  simp only [List.cons.injEq, Val.loc.injEq, and_true] at h3
  rw [h3]

theorem pubAt_not {th : TTh} {x : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word}
    (hterm : th.term = .let_ x (.publish a) e) (hea : evalAt th.env a = some (rt, ws))
    (hws : ∀ ad, ws.map (·.val) ≠ [.loc ad 0]) {l : AllocLabel} : ¬ PubAt th l := by
  rintro ⟨y, a', e', rt', ws', ad', h1, h2, h3, rfl⟩
  rw [hterm] at h1
  cases h1
  rw [hea] at h2
  cases h2
  exact hws _ h3

/-- Off `publish`, no label is published. -/
theorem pubAt_nopub {th : TTh} (h : ∀ x a e, th.term ≠ .let_ x (.publish a) e) {l : AllocLabel} :
    ¬ PubAt th l := by
  rintro ⟨y, a', e', -, -, -, h1, -⟩
  exact h _ _ _ h1

#print axioms footBP_of
#print axioms footB1_nalloc
#print axioms footB1_cons
#print axioms freshIn_one
#print axioms footB1_box
#print axioms nalloc_alloc_boxE
#print axioms footB1_new
#print axioms footB1_newBuf
#print axioms pubAt_eq
#print axioms pubAt_not
#print axioms pubAt_nopub

end TermFootBP0
