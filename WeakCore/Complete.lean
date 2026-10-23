/-
# Complete — how far the checker is from the declarative judgement

`checkProg_sound` (CoreTyping) is one direction: the checker accepts ⇒ `Typed`.
The converse is false, by design, and this file says exactly where.

§1 (step D) proves, by kernel evaluation and explicit derivations, one witness
per gap: a term that is `Typed` and that the checker refuses.

  * W1 `noDrop`.  Linear tokens (row 29) are a liveness rule, not part of
    `Typed`: a block may end holding a token that has a move out.
  * W2 `ifeq` may learn nothing.  `2·n = 2` cannot be recorded as a fact, so
    the checker refuses; the judgement types the `yes` branch with no fact.
  * W3 `ifeqRec` has no occurs check.  Recording `n = n + 1` makes the facts
    unsatisfiable, after which semantic entailment proves anything: here
    `ret 5` at return type `Int(0)`.
  * W4 `parity` asks for semantic `EqI`.  On a variable that already has a
    fact (`n = 4`), `norm` gives `4`, not a variable, so the checker refuses;
    the judgement splits `n` anyway (the new fact shadows the old one).

Not witnessed here, because they are not refusals but extra *outputs*: `addI`
on indexed operands forgets the sum, and `loadTorn` while holding the token.
Each lets a derivation reach a context the checker never computes; `TypedA`
excludes them by selecting rules as the checker does.

§2–§5 (step A) give the algorithmic judgement and pin the checker to it:

  * §2 `TyEqA`/`SubA`: type equality and subsumption with the checker's index
    equality, still inductive.  `subA_iff`/`tyEqA_iff`: `sub`/`tyEq` decide
    them exactly, so the order in which `sub` tries its cases loses nothing.
  * §3 `OpTA`/`TypedA`: `OpT`/`Typed` with the checker's arithmetic, context
    lookups and rule selection, without the permissive extras of §1, and with
    `noDrop` at `ret`/`tail`.  Subsumption, type equality, `fold` and the
    `SubA a ∨ SubA b` premises stay declarative.
  * §4 `checkProg_complete`: the checker accepts every `ProgTA` program; and
    `ProgTA.toProgT`/`TypedA.toTyped`, through the checker.
  * §5 `checkProg_iff`/`check_iff`: the checker accepts exactly `TypedA`, so
    `Typed` ⊋ `TypedA` = checker, and §1 is the difference.  For whole
    programs: `progT_not_checked` (W1 as a one-block program `w1Prog`) and
    `progTA_strict : (∀ p, ProgTA p → ProgT p) ∧ ∃ p, ProgT p ∧ ¬ ProgTA p`.

Choices that fix the output context (which fact `ifeq` records, which torn
licence, `classify`'s parameter) cannot stay existential in `TypedA`: the
checker's normaliser is syntactic in the facts, so contexts with equivalent
facts are not interchangeable for it.

Build:  LEAN_PATH=build lean -o build/Complete.olean Complete.lean
-/

import WeakCore.CoreTyping

namespace Complete

open CoreLang CoreTerm CoreTyping

/-! ## §1. Witnesses: typed, and refused -/

/-! ### W1 — a linear token left at `ret` -/

/-- One region index `r`, and a token at `badSeqP`'s taken state `2·0 + 1`,
which has a move back to the free state: a token that can be given back. -/
def w1Cx : Cx :=
  { inames := ["r"], vars := [("t", .tok (.var 0) (some (badSeqP, .lit 1)), true)], ret := .unit }

def w1 : Expr := .ret .unit

theorem w1_typed : Typed [] w1Cx w1 :=
  .ret (a := .unit) (t := .unit) (c₁ := w1Cx) rfl (noLeak_sound (u := ()) rfl) (.eq .refl)

theorem w1_refused : accepts (check [] w1Cx w1) = false := by decide +kernel
-- The reason (strings do not reduce in the kernel, so this is evaluated):
#guard rejects (check [] w1Cx w1) "still holds a token"

/-! ### W2 — `ifeq` that cannot record its equality -/

def w2Cx : Cx :=
  { inames := ["n"], vars := [("a", .intS (.smul 2 (.var 0)), true)], ret := .unit }

def w2 : Expr := .ifeq (.var "a") (.lit 2) (.ret .unit) (.ret .unit)

theorem w2_typed : Typed [] w2Cx w2 :=
  .ifeq (i := .smul 2 (.var 0)) (j := .lit 2)
    (intIdx_sound rfl) (intIdx_sound rfl)
    (check_sound _ _ _ (ok_of_accepts (by decide +kernel)))
    (noCx_sound rfl rfl)
    (check_sound _ _ _ (ok_of_accepts (by decide +kernel)))

theorem w2_refused : accepts (check [] w2Cx w2) = false := by decide +kernel
-- The reason (strings do not reduce in the kernel, so this is evaluated):
#guard rejects (check [] w2Cx w2) "cannot record the equality"

/-! ### W3 — no occurs check: `n = n + 1`, then anything -/

def w3Cx : Cx :=
  { inames := ["n"], vars := [("a", .intS (.var 0), true), ("b", .intS (.add (.var 0) (.lit 1)), true)],
    ret := .intS (.lit 0) }

def w3 : Expr := .ifeq (.var "a") (.var "b") (.ret (.lit 5)) (.ret (.lit 0))

/-- The `yes` branch: the facts say `n = n + 1`, which no valuation satisfies. -/
theorem w3_yes : Typed [] { w3Cx with facts := (0, .add (.var 0) (.lit 1)) :: w3Cx.facts } (.ret (.lit 5)) :=
  .ret (t := .intS (.lit 5)) rfl (noLeak_sound (u := ()) rfl)
    (.eq (.intS (Or.inr ⟨rfl, fun ρ hs => by
      have h := hs 0 (.add (.var 0) (.lit 1)) rfl
      simp [ev] at h⟩)))

theorem w3_typed : Typed [] w3Cx w3 :=
  .ifeqRec (i := .var 0) (j := .add (.var 0) (.lit 1)) (t := .add (.var 0) (.lit 1)) (v := 0)
    (intIdx_sound rfl) (intIdx_sound rfl)
    (Or.inl ⟨fun _ _ => rfl, fun _ _ => rfl⟩) w3_yes .same
    (check_sound _ _ _ (ok_of_accepts (by decide +kernel)))

theorem w3_refused : accepts (check [] w3Cx w3) = false := by decide +kernel
-- The reason (strings do not reduce in the kernel, so this is evaluated):
#guard rejects (check [] w3Cx w3) "cannot record the equality"

/-! ### W4 — `parity` on a variable that already has a fact -/

def w4Cx : Cx :=
  { inames := ["n"], facts := [(0, .lit 4)], vars := [("a", .intS (.var 0), true)], ret := .unit }

def w4 : Expr := .parity (.var "a") "k" (.ret .unit) (.ret .unit)

theorem w4_typed : Typed [] w4Cx w4 :=
  .parity (i := .var 0) (v := 0) (intIdx_sound rfl) (fun _ _ => rfl)
    (check_sound _ _ _ (ok_of_accepts (by decide +kernel)))
    (check_sound _ _ _ (ok_of_accepts (by decide +kernel)))

theorem w4_refused : accepts (check [] w4Cx w4) = false := by decide +kernel
-- The reason (strings do not reduce in the kernel, so this is evaluated):
#guard rejects (check [] w4Cx w4) "not a free variable"

/-- The four gaps, together: `Typed` is strictly larger than the checker. -/
theorem typed_not_checked :
    (Typed [] w1Cx w1 ∧ accepts (check [] w1Cx w1) = false) ∧
    (Typed [] w2Cx w2 ∧ accepts (check [] w2Cx w2) = false) ∧
    (Typed [] w3Cx w3 ∧ accepts (check [] w3Cx w3) = false) ∧
    (Typed [] w4Cx w4 ∧ accepts (check [] w4Cx w4) = false) :=
  ⟨⟨w1_typed, w1_refused⟩, ⟨w2_typed, w2_refused⟩, ⟨w3_typed, w3_refused⟩, ⟨w4_typed, w4_refused⟩⟩

#print axioms typed_not_checked

/-! ### A whole program: `ProgT` holds and `checkProg` refuses

W1 at the level of programs.  One code block, index `r`, argument
`t : Tok[r, badSeqP, 1]`; its body context is exactly `w1Cx`, and its body
returns without giving the token back. -/

def w1D : Decl :=
  { name := "drop", idx := ["r"], arg := "t", argTy := .tok (.var 0) (some (badSeqP, .lit 1)),
    retTy := .unit, body := w1 }

def w1Prog : Prog := [w1D]

theorem w1D_cx : declCx w1D = w1Cx := rfl

theorem w1Prog_typed : ProgT w1Prog := by
  intro d hd
  simp only [w1Prog, List.mem_singleton] at hd
  subst hd
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  rw [w1D_cx]
  exact .ret (a := .unit) (t := .unit) (c₁ := w1Cx) rfl (noLeak_sound (u := ()) rfl) (.eq .refl)

theorem w1Prog_refused : accepts (checkProg w1Prog) = false := by decide +kernel
#guard rejects (checkProg w1Prog) "still holds a token"

/-- **`ProgT` is strictly larger than what the checker accepts**, for whole
programs, not only for terms in a context. -/
theorem progT_not_checked : ∃ p, ProgT p ∧ accepts (checkProg p) = false :=
  ⟨w1Prog, w1Prog_typed, w1Prog_refused⟩

#print axioms progT_not_checked

/-! ## §2. Type equality and subsumption with the checker's index equality

`TyEqS`/`SubS` with `IEq`'s semantic `EqI` replaced by the checker's `eqI`
(and `LeI` by `leI`): `TyEqA`/`SubA`.  They stay inductive, so each says which
derivations exist, not how `tyEq`/`sub` search for one.  Then:

  * `tyEq_complete`/`sub_complete`: every derivation is found — the order in
    which `sub` tries its cases loses nothing;
  * `tyEqA_of`/`subA_of`: and only those (the soundness proofs, re-aimed);
  * `TyEqA.toS`/`SubA.toS`: each is a special case of the semantic relation. -/

def IEqA (cx : Cx) (d : Nat) (i j : Idx) : Prop := i = j ∨ (d = 0 ∧ cx.eqI i j = true)

inductive MEqA (cx : Cx) (d : Nat) : Mode → Mode → Prop
  | own : MEqA cx d .own .own
  | pub : MEqA cx d .pub .pub
  | rgn {r s} : IEqA cx d r s → MEqA cx d (.rgn r) (.rgn s)

inductive TyEqA (cx : Cx) : Nat → Ty → Ty → Prop
  | refl {d a} : TyEqA cx d a a
  | intS {d i j} : IEqA cx d i j → TyEqA cx d (.intS i) (.intS j)
  | prod {d a b a' b'} : TyEqA cx d a a' → TyEqA cx d b b' → TyEqA cx d (.prod a b) (.prod a' b')
  | sum {d a b a' b'} : TyEqA cx d a a' → TyEqA cx d b b' → TyEqA cx d (.sum a b) (.sum a' b')
  | code {d a b a' b'} : TyEqA cx d a a' → TyEqA cx d b b' → TyEqA cx d (.code a b) (.code a' b')
  | array {d i j t u} : IEqA cx d i j → TyEqA cx d t u → TyEqA cx d (.array i t) (.array j u)
  | ptr {d μ ν t u} : MEqA cx d μ ν → TyEqA cx d t u → TyEqA cx d (.ptr μ t) (.ptr ν u)
  | ptrOpt {d μ ν t u} : MEqA cx d μ ν → TyEqA cx d t u → TyEqA cx d (.ptrOpt μ t) (.ptrOpt ν u)
  | loc {d μ ν t u} : MEqA cx d μ ν → TyEqA cx d t u → TyEqA cx d (.loc μ t) (.loc ν u)
  | word {d r s P} : IEqA cx d r s → TyEqA cx d (.word r P) (.word s P)
  | word2 {d r s} {P : Proto2} : IEqA cx d r s → TyEqA cx d (.word2 r P) (.word2 s P)
  | tok2 {d r s a b a' b'} {P : Proto2} : IEqA cx d r s → IEqA cx d a a' → IEqA cx d b b' →
      TyEqA cx d (.tok2 r P a b) (.tok2 s P a' b')
  | epair {d r s} {P : ECounter} : IEqA cx d r s → TyEqA cx d (.epair r P) (.epair s P)
  | tokE {d r s a a'} {P : ECounter} : IEqA cx d r s → IEqA cx d a a' → TyEqA cx d (.tokE r P a) (.tokE s P a')
  | tokNone {d r s} : IEqA cx d r s → TyEqA cx d (.tok r none) (.tok s none)
  | tokSome {d r s a b} {P : Proto} : IEqA cx d r s → IEqA cx d a b →
      TyEqA cx d (.tok r (some (P, a))) (.tok s (some (P, b)))
  | share {d r s} : IEqA cx d r s → TyEqA cx d (.share r) (.share s)
  | cap {d c r s} : IEqA cx d r s → TyEqA cx d (.cap c r) (.cap c s)
  | mu {d t u} : TyEqA cx d t u → TyEqA cx d (.mu t) (.mu u)
  | tex {d κ t u} : TyEqA cx d t u → TyEqA cx d (.tex κ t) (.tex κ u)
  | iall {d t u} : TyEqA cx (d + 1) t u → TyEqA cx d (.iall t) (.iall u)
  | iex {d t u} : TyEqA cx (d + 1) t u → TyEqA cx d (.iex t) (.iex u)
  | refine {d t u ψ} : TyEqA cx d t u → TyEqA cx d (.refine t ψ) (.refine u ψ)
  | refineIni {d t u i j} : IEqA cx d i j → TyEqA cx d t u →
      TyEqA cx d (.refine t (.ini i)) (.refine u (.ini j))

inductive SubA (cx : Cx) : Ty → Ty → Prop
  | eq {σ τ} : TyEqA cx 0 σ τ → SubA cx σ τ
  | intS {i} : SubA cx (.intS i) .int
  | refine {t ψ u} : SubA cx t u → SubA cx (.refine t ψ) u
  | iniWeak {t u i j} : TyEqA cx 0 t u → cx.leI j i = true →
      SubA cx (.refine t (.ini i)) (.refine u (.ini j))
  | nonNull {μ ν t u} : MEqA cx 0 μ ν → TyEqA cx 0 t u → SubA cx (.ptr μ t) (.ptrOpt ν u)
  | prod {a b a' b'} : SubA cx a a' → SubA cx b b' → SubA cx (.prod a b) (.prod a' b')
  | sum {a b a' b'} : SubA cx a a' → SubA cx b b' → SubA cx (.sum a b) (.sum a' b')
  | cap {c c' r s} : c.le c' = true → IEqA cx 0 r s → SubA cx (.cap c r) (.cap c' s)

theorem ieqA_iff {cx : Cx} {d : Nat} {i j : Idx} : IEqA cx d i j ↔ ieqD cx d i j = true := by
  unfold IEqA ieqD; simp

theorem meqA_iff {cx : Cx} {d : Nat} {μ ν : Mode} : MEqA cx d μ ν ↔ meqD cx d μ ν = true := by
  constructor
  · intro h; cases h with
    | own => rfl
    | pub => rfl
    | rgn h => exact ieqA_iff.1 h
  · intro h; cases μ <;> cases ν <;> simp [meqD] at h
    · exact .own
    · exact .pub
    · exact .rgn (ieqA_iff.2 h)

theorem IEqA.toS {cx : Cx} {d : Nat} {i j : Idx} (h : IEqA cx d i j) : IEq cx d i j :=
  ieqD_sound (ieqA_iff.1 h)

theorem MEqA.toS {cx : Cx} {d : Nat} {μ ν : Mode} (h : MEqA cx d μ ν) : MEq cx d μ ν :=
  meqD_sound (meqA_iff.1 h)

theorem tyEq_refl (cx : Cx) : ∀ (a : Ty) (d : Nat), tyEq cx d a a = true := by
  intro a
  induction a with
  | intS i => intro d; simp [tyEq, ieqD]
  | prod a b iha ihb => intro d; simp [tyEq, iha, ihb]
  | sum a b iha ihb => intro d; simp [tyEq, iha, ihb]
  | code a b iha ihb => intro d; simp [tyEq, iha, ihb]
  | array i t ih => intro d; simp [tyEq, ieqD, ih]
  | ptr μ t ih => intro d; cases μ <;> simp [tyEq, meqD, ieqD, ih]
  | ptrOpt μ t ih => intro d; cases μ <;> simp [tyEq, meqD, ieqD, ih]
  | loc μ t ih => intro d; cases μ <;> simp [tyEq, meqD, ieqD, ih]
  | word r P => intro d; simp [tyEq, ieqD]
  | word2 r P => intro d; simp [tyEq, ieqD]
  | tok2 r P i j => intro d; simp [tyEq, ieqD]
  | epair r P => intro d; simp [tyEq, ieqD]
  | tokE r P e => intro d; simp [tyEq, ieqD]
  | share r => intro d; simp [tyEq, ieqD]
  | cap c r => intro d; simp [tyEq, ieqD]
  | tok r i => intro d; rcases i with _ | ⟨P, a⟩ <;> simp [tyEq, ieqD]
  | mu t ih => intro d; simp [tyEq, ih]
  | tex κ t ih => intro d; simp [tyEq, ih]
  | iall t ih => intro d; simp [tyEq, ih]
  | iex t ih => intro d; simp [tyEq, ih]
  | refine t ψ ih => intro d; simp [tyEq, ih]
  | _ => intro d; simp [tyEq]

theorem tyEq_complete {cx : Cx} {d : Nat} {a b : Ty} (h : TyEqA cx d a b) : tyEq cx d a b = true := by
  induction h with
  | refl => exact tyEq_refl cx _ _
  | intS h => simpa [tyEq] using ieqA_iff.1 h
  | prod _ _ ih1 ih2 => simp [tyEq, ih1, ih2]
  | sum _ _ ih1 ih2 => simp [tyEq, ih1, ih2]
  | code _ _ ih1 ih2 => simp [tyEq, ih1, ih2]
  | array h _ ih => simp [tyEq, ieqA_iff.1 h, ih]
  | ptr h _ ih => simp [tyEq, meqA_iff.1 h, ih]
  | ptrOpt h _ ih => simp [tyEq, meqA_iff.1 h, ih]
  | loc h _ ih => simp [tyEq, meqA_iff.1 h, ih]
  | word h => simp [tyEq, ieqA_iff.1 h]
  | word2 h => simp [tyEq, ieqA_iff.1 h]
  | tok2 h1 h2 h3 => simp [tyEq, ieqA_iff.1 h1, ieqA_iff.1 h2, ieqA_iff.1 h3]
  | epair h => simp [tyEq, ieqA_iff.1 h]
  | tokE h1 h2 => simp [tyEq, ieqA_iff.1 h1, ieqA_iff.1 h2]
  | tokNone h => simp [tyEq, ieqA_iff.1 h]
  | tokSome h1 h2 => simp [tyEq, ieqA_iff.1 h1, ieqA_iff.1 h2]
  | share h => simpa [tyEq] using ieqA_iff.1 h
  | cap h => simp [tyEq, ieqA_iff.1 h]
  | mu _ ih => simpa [tyEq] using ih
  | tex _ ih => simp [tyEq, ih]
  | iall _ ih => simpa [tyEq] using ih
  | iex _ ih => simpa [tyEq] using ih
  | refine _ ih => simp [tyEq, ih]
  | refineIni h _ ih => simp [tyEq, iniEq, ieqA_iff.1 h, ih]

theorem tyEqA_of (cx : Cx) : ∀ (d : Nat) (a b : Ty), tyEq cx d a b = true → TyEqA cx d a b := by
  intro d a b h
  induction a generalizing d b with
  | unit | void | int | tvar _ | fix _ _ | lanes _ _ | tid =>
      cases b <;> simp_all [tyEq] <;> first | exact .refl | skip
  | intS i =>
      cases b <;> simp [tyEq] at h
      exact .intS (ieqA_iff.2 h)
  | prod a₁ a₂ ih₁ ih₂ =>
      cases b <;> simp [tyEq] at h
      exact .prod (ih₁ _ _ h.1) (ih₂ _ _ h.2)
  | sum a₁ a₂ ih₁ ih₂ =>
      cases b <;> simp [tyEq] at h
      exact .sum (ih₁ _ _ h.1) (ih₂ _ _ h.2)
  | code a₁ a₂ ih₁ ih₂ =>
      cases b <;> simp [tyEq] at h
      exact .code (ih₁ _ _ h.1) (ih₂ _ _ h.2)
  | array i t ih =>
      cases b <;> simp [tyEq] at h
      exact .array (ieqA_iff.2 h.1) (ih _ _ h.2)
  | ptr μ t ih =>
      cases b <;> simp [tyEq] at h
      exact .ptr (meqA_iff.2 h.1) (ih _ _ h.2)
  | ptrOpt μ t ih =>
      cases b <;> simp [tyEq] at h
      exact .ptrOpt (meqA_iff.2 h.1) (ih _ _ h.2)
  | loc μ t ih =>
      cases b <;> simp [tyEq] at h
      exact .loc (meqA_iff.2 h.1) (ih _ _ h.2)
  | word r P =>
      cases b <;> simp [tyEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact .word (ieqA_iff.2 h1)
  | word2 r P =>
      cases b <;> simp [tyEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact .word2 (ieqA_iff.2 h1)
  | tok2 r P i j =>
      cases b <;> simp [tyEq] at h
      obtain ⟨⟨⟨h1, rfl⟩, h2⟩, h3⟩ := h
      exact .tok2 (ieqA_iff.2 h1) (ieqA_iff.2 h2) (ieqA_iff.2 h3)
  | epair r P =>
      cases b <;> simp [tyEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact .epair (ieqA_iff.2 h1)
  | tokE r P e =>
      cases b <;> simp [tyEq] at h
      obtain ⟨⟨h1, rfl⟩, h2⟩ := h
      exact .tokE (ieqA_iff.2 h1) (ieqA_iff.2 h2)
  | tok r i =>
      cases b <;> simp [tyEq] at h
      rename_i s j
      obtain ⟨h1, h2⟩ := h
      rcases i with _ | ⟨P, a⟩ <;> rcases j with _ | ⟨Q, b⟩ <;> simp at h2
      · exact .tokNone (ieqA_iff.2 h1)
      · obtain ⟨rfl, h2⟩ := h2
        exact .tokSome (ieqA_iff.2 h1) (ieqA_iff.2 h2)
  | share r =>
      cases b <;> simp [tyEq] at h
      exact .share (ieqA_iff.2 h)
  | cap c r =>
      cases b <;> simp [tyEq] at h
      obtain ⟨rfl, h2⟩ := h
      exact .cap (ieqA_iff.2 h2)
  | mu t ih =>
      cases b <;> simp [tyEq] at h
      exact .mu (ih _ _ h)
  | iall t ih =>
      cases b <;> simp [tyEq] at h
      exact .iall (ih _ _ h)
  | iex t ih =>
      cases b <;> simp [tyEq] at h
      exact .iex (ih _ _ h)
  | tex κ t ih =>
      cases b <;> simp [tyEq] at h
      obtain ⟨rfl, h2⟩ := h
      exact .tex (ih _ _ h2)
  | refine t ψ ih =>
      cases b <;> simp [tyEq] at h
      rename_i u χ
      obtain ⟨h1, h2⟩ := h
      rcases h1 with rfl | h1
      · exact .refine (ih _ _ h2)
      · cases ψ <;> cases χ <;> simp [iniEq] at h1
        exact .refineIni (ieqA_iff.2 h1) (ih _ _ h2)

theorem TyEqA.toS {cx : Cx} {d : Nat} {a b : Ty} (h : TyEqA cx d a b) : TyEqS cx d a b :=
  tyEq_sound cx d a b (tyEq_complete h)

theorem sub_complete {cx : Cx} {σ τ : Ty} (h : SubA cx σ τ) : sub cx σ τ = true := by
  induction h with
  | eq h => unfold sub; simp [tyEq_complete h]
  | intS => unfold sub; simp
  | @refine t ψ u _ ih =>
      unfold sub
      cases ψ <;> cases u <;> simp [ih]
      rename_i χ _
      cases χ <;> simp [ih]
  | iniWeak h1 h2 => unfold sub; simp [tyEq_complete h1, h2]
  | nonNull h1 h2 => unfold sub; simp [meqA_iff.1 h1, tyEq_complete h2]
  | prod _ _ ih1 ih2 => unfold sub; simp [ih1, ih2]
  | sum _ _ ih1 ih2 => unfold sub; simp [ih1, ih2]
  | cap h1 h2 => unfold sub; simp [h1, ieqA_iff.1 h2]

theorem subA_of (cx : Cx) : ∀ (σ τ : Ty), sub cx σ τ = true → SubA cx σ τ := by
  intro σ
  induction σ with
  | refine t ψ ih =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEqA_of cx 0 _ _ h)
      · cases ψ <;> cases τ <;> (try exact .refine (ih _ h))
        all_goals (rename_i χ; cases χ <;> (try exact .refine (ih _ h)))
        all_goals
          simp only [Bool.or_eq_true, Bool.and_eq_true] at h
          rcases h with ⟨h1, h2⟩ | h
          · exact .iniWeak (tyEqA_of cx 0 _ _ h1) h2
          · exact .refine (ih _ h)
  | prod a b iha ihb =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEqA_of cx 0 _ _ h)
      · cases τ <;> simp at h
        exact .prod (iha _ h.1) (ihb _ h.2)
  | sum a b iha ihb =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEqA_of cx 0 _ _ h)
      · cases τ <;> simp at h
        exact .sum (iha _ h.1) (ihb _ h.2)
  | intS i =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEqA_of cx 0 _ _ h)
      · cases τ <;> simp at h
        exact .intS
  | ptr μ t ih =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEqA_of cx 0 _ _ h)
      · cases τ <;> cases μ <;> (try simp at h)
        all_goals (try (rename_i ν _; cases ν <;> (try simp at h)))
        all_goals first
          | exact .nonNull (meqA_iff.2 h.1) (tyEqA_of cx 0 _ _ h.2)
          | exact .nonNull .own (tyEqA_of cx 0 _ _ h)
          | exact .nonNull .pub (tyEqA_of cx 0 _ _ h)
          | exact .nonNull (.rgn (ieqA_iff.2 h.1)) (tyEqA_of cx 0 _ _ h.2)
  | ptrOpt μ t ih =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEqA_of cx 0 _ _ h)
      · cases τ <;> cases μ <;> (try simp at h)
        all_goals (try (rename_i ν _; cases ν <;> (try simp at h)))
  | loc μ t ih =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEqA_of cx 0 _ _ h)
      · cases τ <;> cases μ <;> (try simp at h)
        all_goals (try (rename_i ν _; cases ν <;> (try simp at h)))
  | cap c r =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEqA_of cx 0 _ _ h)
      · cases τ <;> simp at h
        exact .cap h.1 (ieqA_iff.2 h.2)
  | _ =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEqA_of cx 0 _ _ h)
      · cases τ <;> simp at h

theorem SubA.toS {cx : Cx} {σ τ : Ty} (h : SubA cx σ τ) : SubS cx σ τ :=
  sub_sound cx σ τ (sub_complete h)

theorem subA_iff {cx : Cx} {σ τ : Ty} : SubA cx σ τ ↔ sub cx σ τ = true :=
  ⟨sub_complete, subA_of cx σ τ⟩

theorem tyEqA_iff {cx : Cx} {d : Nat} {a b : Ty} : TyEqA cx d a b ↔ tyEq cx d a b = true :=
  ⟨tyEq_complete, tyEqA_of cx d a b⟩

#print axioms subA_iff
#print axioms tyEqA_iff

/-! ## §3. The algorithmic judgement `OpTA`/`TypedA`

One rule per path on which the checker succeeds, read off `checkOp`/`check`:
`OpT`/`Typed` with these changes, and no others.

  * **Arithmetic is the checker's**: `eqI`/`ltI`/`leI`, `norm` and the `Lin`
    tests, `classifyM`/`pstep`/`shareMove` for protocol states.
  * **Context lookups are the checker's** (`hasTok`, `sealedR`, `noLeak`,
    `xchgCell`, `tornLicence`, `lendCx`, …): CoreTyping already shares `use`,
    `bind` and `peek` with the checker, and these are of the same kind.
  * **Rule selection is the checker's**: `addI` only when an operand has no
    index; `loadCap` only without a token or share, `loadTorn` only without a
    capability either; `storeCap` only without a token; `ifeq` records the
    fact the checker records, or none when the two sides normalise equal.
  * **The permissive extras are gone** (§1): `ifeq` learning nothing when it
    could learn, `ifeqRec` without the occurs check, `parity` by `EqI`.
  * **`noDrop` is a premise** of `ret` and `tail`.

What stays declarative: subsumption and type equality (`SubA`, `TyEqA`,
`FoldOKA`), and the disjunctions `SubA a ∨ SubA b` the checker decides by
trying `a` first.  These are the choices that do not fix the output context;
the others (which fact, which licence, which parameter) do, and the checker is
syntactic in its facts, so they cannot be left open. -/

inductive FoldOKA (cx : Cx) : Ty → Ty → Prop
  | ptr {μ ν : Mode} {u s : Ty} : MEqA cx 0 μ ν → TyEqA cx 0 u (unfold1 (.mu s)) →
      FoldOKA cx (.ptr μ u) (.ptr ν (.mu s))
  | ptrOpt {μ ν : Mode} {u s : Ty} : MEqA cx 0 μ ν → TyEqA cx 0 u (unfold1 (.mu s)) →
      FoldOKA cx (.ptrOpt μ u) (.ptrOpt ν (.mu s))
  | loc {μ ν : Mode} {u s : Ty} : MEqA cx 0 μ ν → TyEqA cx 0 u (unfold1 (.mu s)) →
      FoldOKA cx (.loc μ u) (.loc ν (.mu s))

inductive OpTA (p : Prog) : Cx → String → Op → Cx → Prop
  | atom {cx c₁ c' : Cx} {x : String} {a : At} {t : Ty} :
      cx.use a = .ok (t, c₁) → c₁.bind x t = .ok c' → OpTA p cx x (.atom a) c'
  | pair {cx c₁ c₂ c' : Cx} {x : String} {a b : At} {t u : Ty} :
      cx.use a = .ok (t, c₁) → c₁.use b = .ok (u, c₂) → c₂.bind x (.prod t u) = .ok c' →
      OpTA p cx x (.pair a b) c'
  | inl {cx c₁ c' : Cx} {x : String} {a : At} {t τ : Ty} :
      τ.wf cx.ke.length 0 = true → cx.use a = .ok (t, c₁) → c₁.bind x (.sum t τ) = .ok c' →
      OpTA p cx x (.inl τ a) c'
  | inr {cx c₁ c' : Cx} {x : String} {a : At} {t τ : Ty} :
      τ.wf cx.ke.length 0 = true → cx.use a = .ok (t, c₁) → c₁.bind x (.sum τ t) = .ok c' →
      OpTA p cx x (.inr τ a) c'
  | addS {cx c' : Cx} {x : String} {a b : At} {t u : Ty} {i j : Idx} :
      cx.peek a = .ok t → cx.peek b = .ok u → intOf t = some (some i) → intOf u = some (some j) →
      cx.bind x (.intS (.add i j)) = .ok c' → OpTA p cx x (.add a b) c'
  | addI {cx c' : Cx} {x : String} {a b : At} {t u : Ty} {o o' : Option Idx} :
      cx.peek a = .ok t → cx.peek b = .ok u → intOf t = some o → intOf u = some o' →
      (o = none ∨ o' = none) → cx.bind x .int = .ok c' → OpTA p cx x (.add a b) c'
  | subS {cx c' : Cx} {x : String} {a b : At} {t u : Ty} {i j : Idx} {ni nj : Lin} :
      cx.peek a = .ok t → cx.peek b = .ok u → intOf t = some (some i) → intOf u = some (some j) →
      cx.norm i = some ni → cx.norm j = some nj → Lin.leB nj ni = true →
      cx.bind x (.intS (ni.diff nj).toIdx) = .ok c' → OpTA p cx x (.sub a b) c'
  | new {cx c₁ c' : Cx} {x : String} {a : At} {t : Ty} :
      cx.use a = .ok (t, c₁) → t.secondClass = false → c₁.bind x (.ptr .own t) = .ok c' →
      OpTA p cx x (.new a) c'
  | publish {cx c₁ c' : Cx} {x : String} {a : At} {u : Ty} :
      cx.use a = .ok (.ptr .own u, c₁) → Ty.sharedOKIn c₁.ke (.ptr .pub u) = true →
      c₁.bind x (.ptr .pub u) = .ok c' → OpTA p cx x (.publish a) c'
  | publishBuf {cx c₁ c' : Cx} {x : String} {a : At} {n k : Idx} {u : Ty} :
      cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) →
      Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true →
      c₁.bind x (.refine (.loc .pub (.array n u)) (.ini k)) = .ok c' → OpTA p cx x (.publish a) c'
  | intoRgn {cx c₁ c' : Cx} {x rn : String} {a : At} {r : Idx} {u : Ty} :
      cx.idx rn = .ok r → cx.use a = .ok (.ptr .own u, c₁) → rgnCellOK c₁.ke u = true →
      c₁.bind x (.ptr (.rgn r) u) = .ok c' → OpTA p cx x (.intoRgn rn a) c'
  | intoRgnBuf {cx c₁ c' : Cx} {x rn : String} {a : At} {r n k : Idx} {u : Ty} :
      cx.idx rn = .ok r → cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) →
      rgnCellOK c₁.ke (.array n u) = true →
      c₁.bind x (.refine (.loc (.rgn r) (.array n u)) (.ini k)) = .ok c' → OpTA p cx x (.intoRgn rn a) c'
  | newBuf {cx c' : Cx} {x : String} {n : At} {τ : Ty} {k : Idx} :
      τ.wf cx.ke.length cx.inames.length = true → τ.secondClass = false →
      cx.opaqueOK τ = true → τ.arrFree = true → intIdx cx n = .ok k →
      cx.bind x (.refine (.loc .own (.array k τ))
        (.ini (if zeroableIn [] cx.ke τ then k else .lit 0))) = .ok c' → OpTA p cx x (.newBuf n τ) c'
  | idxOwn {cx c₁ c' : Cx} {x : String} {b i : At} {t t' u : Ty} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → intIdx cx i = .ok j → cx.ltI j n = true →
      cx.ltI j k = true → cx.opaqueOK u = true → cx.use b = .ok (t', c₁) →
      c₁.bind x (.loc .own u) = .ok c' →
      OpTA p cx x (.idx b i) c'
  | idxShared {cx c' : Cx} {x : String} {b i : At} {t u : Ty} {μ : Mode} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (μ, n, u, k) → μ ≠ .own → intIdx cx i = .ok j →
      cx.ltI j n = true → cx.ltI j k = true → cx.opaqueOK u = true → cx.bind x (.loc μ u) = .ok c' →
      OpTA p cx x (.idx b i) c'
  | bufInit {cx c₁ c₂ c' : Cx} {x : String} {b i v : At} {t tv u : Ty} {n k j : Idx} :
      cx.use b = .ok (t, c₁) → bufOf t = some (.own, n, u, k) → intIdx c₁ i = .ok j → c₁.eqI j k = true →
      c₁.ltI k n = true → c₁.use v = .ok (tv, c₂) → SubA c₂ tv u →
      c₂.bind x (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1)))) = .ok c' →
      OpTA p cx x (.bufInit b i v) c'
  | null {cx c' : Cx} {x : String} {μ : Mode} {τ : Ty} :
      (Ty.ptrOpt μ τ).wf cx.ke.length cx.inames.length = true →
      cx.bind x (.ptrOpt μ τ) = .ok c' → OpTA p cx x (.null μ τ) c'
  | fold {cx c₁ c' : Cx} {x : String} {a : At} {t τ : Ty} :
      τ.wf cx.ke.length cx.inames.length = true → cx.use a = .ok (t, c₁) → FoldOKA c₁ t τ →
      c₁.bind x τ = .ok c' → OpTA p cx x (.fold a τ) c'
  | fldOwn {cx c₁ c' : Cx} {x : String} {i : Nat} {a : At} {t t' u c1 c2 : Ty} :
      cx.peek a = .ok t → cellOf t = some (.own, u) → unfold1 u = .prod c1 c2 →
      (i ≠ 0 → cx.opaqueOK c1 = true) →
      cx.use a = .ok (t', c₁) → c₁.bind x (.loc .own (if i == 0 then c1 else c2)) = .ok c' →
      OpTA p cx x (.fld i a) c'
  | fldShared {cx c' : Cx} {x : String} {i : Nat} {a : At} {t u c1 c2 : Ty} {μ : Mode} :
      cx.peek a = .ok t → cellOf t = some (μ, u) → μ ≠ .own → unfold1 u = .prod c1 c2 →
      (i ≠ 0 → cx.opaqueOK c1 = true) →
      cx.bind x (.loc μ (if i == 0 then c1 else c2)) = .ok c' → OpTA p cx x (.fld i a) c'
  | loadWord {cx c' : Cx} {x w : String} {acq : Bool} {t : Ty} {rP : Idx × Proto} :
      cx.peek (.var w) = .ok t → wordOf t = some rP → rP.2.ghost = false →
      (observeCx cx x w acq).bind x (.intS (.var 0)) = .ok c' → OpTA p cx x (.load acq (.var w)) c'
  | loadOwn {cx c' : Cx} {x : String} {acq : Bool} {a : At} {t u : Ty} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.own, u) → affine cx.ke u = false →
      cx.bind x u = .ok c' → OpTA p cx x (.load acq a) c'
  | loadPub {cx c' : Cx} {x : String} {acq : Bool} {a : At} {t u : Ty} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.pub, u) → affine cx.ke u = false →
      (Ty.sensitiveIn cx.ke u = true → acq = true) →
      cx.bind x u = .ok c' → OpTA p cx x (.load acq a) c'
  | loadRgn {cx c' : Cx} {x : String} {acq : Bool} {a : At} {t u : Ty} {r : Idx} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.rgn r, u) →
      (cx.hasTok r || cx.hasShare r) = true → affine cx.ke (adapt r u) = false →
      cx.bind x (adapt r u) = .ok c' → OpTA p cx x (.load acq a) c'
  | loadCap {cx c' : Cx} {x : String} {acq : Bool} {a : At} {t u : Ty} {r : Idx} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.rgn r, u) →
      (cx.hasTok r || cx.hasShare r) = false → cx.hasCap r false = true →
      (Ty.sensitiveIn cx.ke (adapt r u) = true → acq = true) → affine cx.ke (adapt r u) = false →
      cx.bind x (adapt r u) = .ok c' → OpTA p cx x (.load acq a) c'
  | loadTorn {cx : Cx} {x w : String} {acq : Bool} {a : At} {t u : Ty} {r s : Idx} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.rgn r, u) →
      (cx.hasTok r || cx.hasShare r) = false → cx.hasCap r false = false →
      tornLicence cx r = .ok (w, s) →
      cx.vars.any (·.1 == x) = false → cx.torn.any (·.x == x) = false →
      OpTA p cx x (.load acq a) { cx with torn := ⟨x, adapt r u, w, s, .opn⟩ :: cx.torn }
  | storeWordGive {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v tk : At} {t : Ty} {r r' i j : Idx}
      {P : Proto} {c c₂ : Nat} {k k' : Lin} {cl cl' : Clause} :
      cx.peek a = .ok t → wordOf t = some (r, P) → cx.use tk = .ok (.tok r' (some (P, i)), c₁) →
      c₁.eqI r r' = true → intIdx c₁ v = .ok j →
      classifyM c₁ P i = .ok (c, k) → classifyM c₁ P j = .ok (c₂, k') →
      clauseM P c = .ok cl → clauseM P c₂ = .ok cl' →
      cl.holds = false → pstep P c k c₂ k' = true → cl'.holds = true → (rel || P.ghost) = true →
      c₁.bind x .unit = .ok c' → OpTA p cx x (.store rel a v (some tk)) c'
  | storeWordKeep {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v tk : At} {t : Ty} {r r' i j : Idx}
      {P : Proto} {c c₂ : Nat} {k k' : Lin} {cl cl' : Clause} :
      cx.peek a = .ok t → wordOf t = some (r, P) → cx.use tk = .ok (.tok r' (some (P, i)), c₁) →
      c₁.eqI r r' = true → intIdx c₁ v = .ok j →
      classifyM c₁ P i = .ok (c, k) → classifyM c₁ P j = .ok (c₂, k') →
      clauseM P c = .ok cl → clauseM P c₂ = .ok cl' →
      cl.holds = false → pstep P c k c₂ k' = true → cl'.holds = false → P.ticket = false →
      c₁.bind x (.tok r' (some (P, j))) = .ok c' → OpTA p cx x (.store rel a v (some tk)) c'
  | storeWordHand {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v tk : At} {t : Ty} {r r' i j : Idx}
      {P : Proto} {c c₂ : Nat} {k k' : Lin} {cl cl' : Clause} :
      cx.peek a = .ok t → wordOf t = some (r, P) → cx.use tk = .ok (.tok r' (some (P, i)), c₁) →
      c₁.eqI r r' = true → intIdx c₁ v = .ok j →
      classifyM c₁ P i = .ok (c, k) → classifyM c₁ P j = .ok (c₂, k') →
      clauseM P c = .ok cl → clauseM P c₂ = .ok cl' →
      cl.holds = false → pstep P c k c₂ k' = true → cl'.holds = false → P.ticket = true → rel = true →
      c₁.bind x .unit = .ok c' → OpTA p cx x (.store rel a v (some tk)) c'
  | storeOwn {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v : At} {tok : Option At} {t u tv : Ty} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.own, u) → Ty.wordFreeIn cx.ke u = true →
      cx.use v = .ok (tv, c₁) → SubA c₁ tv u → c₁.bind x .unit = .ok c' → OpTA p cx x (.store rel a v tok) c'
  | storePub {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v : At} {tok : Option At} {t u tv : Ty} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.pub, u) → Ty.wordFreeIn cx.ke u = true →
      cx.use v = .ok (tv, c₁) → SubA c₁ tv u → (Ty.sensitiveIn c₁.ke u = true → rel = true) →
      c₁.bind x .unit = .ok c' → OpTA p cx x (.store rel a v tok) c'
  | storeRgn {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v : At} {tok : Option At} {t u tv : Ty}
      {r : Idx} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.rgn r, u) → Ty.wordFreeIn cx.ke u = true →
      cx.use v = .ok (tv, c₁) → c₁.hasTok r = true → c₁.sealedR r = true →
      (SubA c₁ tv u ∨ SubA c₁ tv (adapt r u)) →
      c₁.bind x .unit = .ok c' → OpTA p cx x (.store rel a v tok) c'
  | storeCap {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v : At} {tok : Option At} {t u tv : Ty}
      {r : Idx} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.rgn r, u) → Ty.wordFreeIn cx.ke u = true →
      cx.use v = .ok (tv, c₁) → c₁.hasTok r = false → c₁.hasCap r true = true →
      (Ty.sensitiveIn c₁.ke u = true → rel = true) → (SubA c₁ tv u ∨ SubA c₁ tv (adapt r u)) →
      c₁.bind x .unit = .ok c' → OpTA p cx x (.store rel a v tok) c'
  | fence {cx c' : Cx} {x : String} {f : Fence} :
      (fenceCx cx f).bind x .unit = .ok c' → OpTA p cx x (.fence f) c'
  | mkWord {cx c₁ c' : Cx} {x rn : String} {P : Proto} {v tk : At} {r r' j : Idx} {c : Nat} {k : Lin}
      {cl : Clause} :
      cx.idx rn = .ok r → pwf P = true → cx.use tk = .ok (.tok r' none, c₁) → c₁.eqI r r' = true →
      intIdx c₁ v = .ok j → classifyM c₁ P j = .ok (c, k) → clauseM P c = .ok cl → P.ghost = false →
      cl.holds = true → c₁.bind x (.word r P) = .ok c' → OpTA p cx x (.mkWord rn P v tk) c'
  | mkWordGhost {cx c₁ c' : Cx} {x rn : String} {P : Proto} {v tk : At} {r r' j : Idx} {c : Nat}
      {k : Lin} {cl : Clause} :
      cx.idx rn = .ok r → pwf P = true → cx.use tk = .ok (.tok r' none, c₁) → c₁.eqI r r' = true →
      intIdx c₁ v = .ok j → classifyM c₁ P j = .ok (c, k) → clauseM P c = .ok cl → P.ghost = true →
      cl.holds = false → c₁.bind x (.prod (.word r P) (.tok r (some (P, j)))) = .ok c' →
      OpTA p cx x (.mkWord rn P v tk) c'
  | mkWord2 {cx c₁ c' : Cx} {x rn : String} {P : Proto2} {v0 v1 tk : At} {r r' j0 j1 : Idx}
      {c : Nat} {k0 k1 : Lin} {cl : Clause2} :
      cx.idx rn = .ok r → pwf2 P = true → cx.use tk = .ok (.tok r' none, c₁) → c₁.eqI r r' = true →
      intIdx c₁ v0 = .ok j0 → intIdx c₁ v1 = .ok j1 → classify2M c₁ P j0 j1 = .ok (c, k0, k1) →
      clause2M P c = .ok cl → cl.holds = true → c₁.bind x (.word2 r P) = .ok c' →
      OpTA p cx x (.mkWord2 rn P v0 v1 tk) c'
  | ldp {cx c' : Cx} {x w n0 n1 : String} {acq : Bool} {t : Ty} :
      cx.peek (.var w) = .ok t → pairRef t = true →
      ((cx.push n0).push n1).bind x (.prod (.intS (.var 1)) (.intS (.var 0))) = .ok c' →
      OpTA p cx x (.ldp acq (.var w) n0 n1) c'
  | mkEPair {cx c' : Cx} {x rn : String} {P : ECounter} {v0 v1 : At} {r j0 j1 : Idx} :
      cx.idx rn = .ok r → pwfE P = true → intIdx cx v0 = .ok j0 → intIdx cx v1 = .ok j1 →
      cx.bind x (.epair r P) = .ok c' → OpTA p cx x (.mkEPair rn P v0 v1) c'
  | mkTicket {cx c₁ c' : Cx} {x rn : String} {N P : Proto} {v tk : At} {r r' j : Idx} :
      cx.idx rn = .ok r → pwf N = true → N.epoch = true → pwf P = true → P.ticket = true →
      cx.use tk = .ok (.tok r' none, c₁) → c₁.eqI r r' = true → intIdx c₁ v = .ok j →
      c₁.bind x (.prod (.word r N) (.word r P)) = .ok c' → OpTA p cx x (.mkTicket rn N P v tk) c'
  | claim {cx c₁ c' : Cx} {x w : String} {tk : At} {t : Ty} {r r' j m : Idx} {P : Proto} {Q : ECounter} :
      cx.peek (.var w) = .ok t → wordOf t = some (r, P) → P.ticket = true →
      cx.use tk = .ok (.tokE r' Q j, c₁) → c₁.eqI r r' = true → sawFor c₁ w j = some m →
      c₁.bind x (.tok r (some (P, m))) = .ok c' → OpTA p cx x (.claim (.var w) tk) c'
  | fetchCell {cx c₁ c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {tw tv : Ty} :
      cx.peek a = .ok tw → wordOf tw = none → casCellTy cx tw = .ok .int →
      cx.use v = .ok (tv, c₁) → SubA c₁ tv .int → c₁.bind x .int = .ok c' →
      OpTA p cx x (.fetch o acq rel a v) c'
  | fetchEpoch {cx c' : Cx} {x : String} {acq rel : Bool} {a v : At} {tw : Ty} {r j : Idx} {P : Proto} :
      cx.peek a = .ok tw → wordOf tw = some (r, P) → intIdx cx v = .ok j → P.epoch = true →
      acq = true → cx.eqI j (.lit 1) = true → cx.bind x (fetchEpochTy r P) = .ok c' →
      OpTA p cx x (.fetch .add acq rel a v) c'
  | fetchShare {cx c' : Cx} {x : String} {acq rel : Bool} {a v : At} {tw : Ty} {r j : Idx} {P : Proto}
      {d : Nat} :
      cx.peek a = .ok tw → wordOf tw = some (r, P) → intIdx cx v = .ok j → P.epoch = false →
      cx.constIdx j = .ok d → cx.eqI j (.lit d) = true → fetchOK P d = true → cx.bind x .int = .ok c' →
      OpTA p cx x (.fetch .add acq rel a v) c'
  | stpGive {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v0 v1 tk : At} {t : Ty}
      {r r' i0 i1 j0 j1 : Idx} {P : Proto2} {c c₂ : Nat} {k0 k1 k0' k1' : Lin} {cl cl' : Clause2} :
      cx.peek a = .ok t → word2Of t = some (r, P) → cx.use tk = .ok (.tok2 r' P i0 i1, c₁) →
      c₁.eqI r r' = true → intIdx c₁ v0 = .ok j0 → intIdx c₁ v1 = .ok j1 →
      classify2M c₁ P i0 i1 = .ok (c, k0, k1) → classify2M c₁ P j0 j1 = .ok (c₂, k0', k1') →
      clause2M P c = .ok cl → clause2M P c₂ = .ok cl' →
      cl.holds = false → pstep2 P c k0 k1 c₂ k0' k1' = true → cl'.holds = true → rel = true →
      c₁.bind x .unit = .ok c' → OpTA p cx x (.stp rel a v0 v1 tk) c'
  | stpKeep {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v0 v1 tk : At} {t : Ty}
      {r r' i0 i1 j0 j1 : Idx} {P : Proto2} {c c₂ : Nat} {k0 k1 k0' k1' : Lin} {cl cl' : Clause2} :
      cx.peek a = .ok t → word2Of t = some (r, P) → cx.use tk = .ok (.tok2 r' P i0 i1, c₁) →
      c₁.eqI r r' = true → intIdx c₁ v0 = .ok j0 → intIdx c₁ v1 = .ok j1 →
      classify2M c₁ P i0 i1 = .ok (c, k0, k1) → classify2M c₁ P j0 j1 = .ok (c₂, k0', k1') →
      clause2M P c = .ok cl → clause2M P c₂ = .ok cl' →
      cl.holds = false → pstep2 P c k0 k1 c₂ k0' k1' = true → cl'.holds = false →
      c₁.bind x (.tok2 r' P j0 j1) = .ok c' → OpTA p cx x (.stp rel a v0 v1 tk) c'
  | pack {cx c₁ c' : Cx} {x wn : String} {a : At} {w : Idx} {body t : Ty} :
      cx.idx wn = .ok w → (Ty.iex body).wf cx.ke.length cx.inames.length = true → cx.use a = .ok (t, c₁) →
      noLeak c₁ t = .ok () → SubA c₁ t (instT [w] 0 body) → c₁.bind x (.iex body) = .ok c' →
      OpTA p cx x (.pack a wn (.iex body)) c'
  | packT {cx c₁ c' : Cx} {x : String} {a : At} {σ body t : Ty} {κ : Kind} :
      body.guardT 0 = true → (Ty.tex κ body).wf cx.ke.length 0 = true → admitsIn cx κ σ = true →
      cx.use a = .ok (t, c₁) → noLeak c₁ t = .ok () → SubA c₁ t (Ty.substT 0 σ body) →
      c₁.bind x (.tex κ body) = .ok c' → OpTA p cx x (.packT a σ (.tex κ body)) c'
  | validate {cx c' : Cx} {x y : String} {tn : Torn} {v : Idx} :
      cx.torn.find? (·.x == y) = some tn → tn.φ = .rechecked v → cx.eqI v tn.s = true →
      affine cx.ke tn.ty = false → cx.bind x tn.ty = .ok c' → OpTA p cx x (.validate y) c'
  | call {cx c₁ c' : Cx} {x f : String} {is : List String} {a : At} {ts : List Ty} {d : Decl}
      {at_ rt t : Ty} :
      p.find f = .ok d → instantiate cx d is ts = .ok (at_, rt) → cx.use a = .ok (t, c₁) →
      noLeak c₁ t = .ok () → SubA c₁ t at_ → c₁.bind x rt = .ok c' → OpTA p cx x (.call f is a ts) c'
  /-- `OpT.spawn` with the checker's subsumption (`SubA`). -/
  | spawn {cx c₁ c' : Cx} {x f : String} {a : At} {T : Ty} {ts : List Ty} {t : Ty} {d : Decl} {at_ rt : Ty} :
      cx.use a = .ok (t, c₁) → SubA c₁ t T → (affine c₁.ke t || affine c₁.ke T) = false →
      T.wf c₁.ke.length 0 = true → ts.all (·.wf c₁.ke.length 0) = true →
      TermClose.tb 0 T = true → ts.all (TermClose.tb 0) = true →
      TermScope.drf T = true → ts.all TermScope.drf = true →
      TermScope.wrapOK T = true → ts.all TermScope.argOK = true →
      p.find f = .ok d → instantiate { vars := [("a", T, true)], ret := .unit } d [] ts = .ok (at_, rt) →
      tailCheck p { vars := [("a", T, true)], ret := rt } f [] (.var "a") ts = .ok () →
      (TermClose.tb 0 rt && TermTv.mg rt && TermTv.noIallV rt) = true →
      c₁.bind x .tid = .ok c' → OpTA p cx x (.spawn f a T ts) c'
  /-- (E1) `OpT.ext` with the checker's subsumption (`SubA`). -/
  | ext {cx c₁ c' : Cx} {x : String} {n : ExtName} {a : At} {t : Ty} :
      cx.use a = .ok (t, c₁) → SubA c₁ t n.sig.1 → c₁.bind x n.sig.2 = .ok c' → OpTA p cx x (.ext n a) c'
  | borrow {cx c₁ c' : Cx} {x y : String} {c : Cap} {a : At} {t t' : Ty} {r : Idx} :
      varOf a = .ok y → cx.peek a = .ok t → lendOf cx c t = .ok r → cx.use a = .ok (t', c₁) →
      { c₁ with lent := y :: c₁.lent }.bind x (.cap c r) = .ok c' → OpTA p cx x (.borrow c a) c'
  | freeze {cx c₁ c' : Cx} {x : String} {a : At} {r : Idx} :
      cx.use a = .ok (.tok r none, c₁) → c₁.sealedR r = true → c₁.bind x (.cap .frz r) = .ok c' →
      OpTA p cx x (.freeze a) c'
  | endBorrow {cx c' : Cx} {x y : String} {a : At} :
      varOf a = .ok y → cx.lent.contains y = true → (cx.endCx y).bind x .unit = .ok c' →
      OpTA p cx x (.endBorrow a) c'
  | xchg {cx c₁ c' : Cx} {x : String} {a v : At} {t u o tv : Ty} :
      cx.peek a = .ok t → xchgCell cx t = .ok (u, o) → cx.use v = .ok (tv, c₁) →
      (SubA c₁ tv u ∨ SubA c₁ tv o) → c₁.bind x o = .ok c' → OpTA p cx x (.xchg a v) c'
  | fnptr {cx c' : Cx} {x f : String} {d : Decl} :
      p.find f = .ok d → d.tparams = [] → d.idx = [] →
      cx.bind x (.code d.argTy d.retTy) = .ok c' → OpTA p cx x (.fnptr f) c'
  | callc {cx c₁ c' : Cx} {x : String} {f a : At} {tf σ τ t : Ty} :
      cx.peek f = .ok tf → codeOf tf = some (σ, τ) → cx.use a = .ok (t, c₁) → noLeak c₁ t = .ok () →
      SubA c₁ t σ → c₁.bind x τ = .ok c' → OpTA p cx x (.callc f a) c'
  | rem {cx c' : Cx} {x : String} {a n : At} {ta : Ty} {o : Option Idx} {j : Idx} {v : Nat} :
      cx.peek a = .ok ta → intOf ta = some o → intIdx cx n = .ok j → (cx.norm j).bind Lin.succVar? = some v →
      { (cx.push (x ++ "_d")).push x with
          facts := (v + 2, .add (.var 0) (.var 1)) :: ((cx.push (x ++ "_d")).push x).facts }.bind x
        (.intS (.var 0)) = .ok c' → OpTA p cx x (.rem a n) c'
  | nameI {cx c' : Cx} {x : String} {a : At} {j : Idx} :
      intIdx cx a = .ok j →
      { cx.push x with facts := (0, j.shift 0) :: (cx.push x).facts }.bind x (.intS (.var 0)) = .ok c' →
      OpTA p cx x (.nameI a) c'
  | xchgAt {cx c₁ c' : Cx} {x : String} {b i v : At} {t tv u : Ty} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → Ty.wordFreeIn cx.ke u = true → intIdx cx i = .ok j →
      cx.ltI j n = true → cx.ltI j k = true →
      cx.use v = .ok (tv, c₁) → SubA c₁ tv u → c₁.bind x u = .ok c' → OpTA p cx x (.xchgAt b i v) c'
  | loadAt {cx c' : Cx} {x : String} {b i : At} {t u : Ty} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → intIdx cx i = .ok j → cx.ltI j n = true →
      cx.ltI j k = true → affine cx.ke u = false → cx.bind x u = .ok c' → OpTA p cx x (.loadAt b i) c'
  | bits {cx c' : Cx} {x : String} {o : BitOp} {a b : At} {ta tb : Ty} {oa ob : Option Idx} :
      cx.peek a = .ok ta → cx.peek b = .ok tb → intOf ta = some oa → intOf tb = some ob →
      cx.bind x .int = .ok c' → OpTA p cx x (.bits o a b) c'
  | bit1 {cx c' : Cx} {x : String} {o : BitOp1} {a : At} {ta : Ty} {oa : Option Idx} :
      cx.peek a = .ok ta → intOf ta = some oa → cx.bind x .int = .ok c' → OpTA p cx x (.bit1 o a) c'
  | vmatch {cx c' : Cx} {x : String} {lo hi b : At} {t1 t2 t3 : Ty} {o1 o2 o3 : Option Idx} :
      cx.peek lo = .ok t1 → cx.peek hi = .ok t2 → cx.peek b = .ok t3 →
      intOf t1 = some o1 → intOf t2 = some o2 → intOf t3 = some o3 →
      cx.bind x .int = .ok c' → OpTA p cx x (.vmatch lo hi b) c'
  | band {cx c' : Cx} {x : String} {a m : At} {ta : Ty} {o : Option Idx} {j : Idx} {v : Nat} :
      cx.peek a = .ok ta → intOf ta = some o → intIdx cx m = .ok j → (cx.norm j).bind Lin.asVar? = some v →
      { (cx.push (x ++ "_d")).push x with
          facts := (v + 2, .add (.var 0) (.var 1)) :: ((cx.push (x ++ "_d")).push x).facts }.bind x
        (.intS (.var 0)) = .ok c' → OpTA p cx x (.band a m) c'
  | zero {cx c' : Cx} {x : String} {τ : Ty} :
      τ.wf cx.ke.length cx.inames.length = true → τ.secondClass = false →
      zeroableIn [] cx.ke τ = true → cx.bind x τ = .ok c' → OpTA p cx x (.zero τ) c'
  | xchgAtF {cx c₁ c' : Cx} {x : String} {b i v : At} {q : List Nat} {t tv u c : Ty} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → compTy u q = some c →
      cx.opaqueOK u = true →
      Ty.wordFreeIn cx.ke c = true → intIdx cx i = .ok j → cx.ltI j n = true → cx.ltI j k = true →
      cx.use v = .ok (tv, c₁) → SubA c₁ tv c → c₁.bind x c = .ok c' → OpTA p cx x (.xchgAtF b i q v) c'
  | loadAtF {cx c' : Cx} {x : String} {b i : At} {q : List Nat} {t u c : Ty} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → compTy u q = some c →
      cx.opaqueOK u = true →
      intIdx cx i = .ok j → cx.ltI j n = true → cx.ltI j k = true →
      affine cx.ke c = false → cx.bind x c = .ok c' → OpTA p cx x (.loadAtF b i q) c'
  | cvt {cx c' : Cx} {x : String} {sg : Bool} {w : Wd} {a : At} {ta : Ty} :
      cx.peek a = .ok ta → cvtSrc ta = true → cx.bind x (.fix sg w) = .ok c' → OpTA p cx x (.cvt sg w a) c'
  | toInt {cx c' : Cx} {x : String} {a : At} {ta : Ty} :
      cx.peek a = .ok ta → toIntSrc ta = true → cx.bind x .int = .ok c' → OpTA p cx x (.toInt a) c'
  | asLanes {cx c' : Cx} {x : String} {sg : Bool} {w : Wd} {a : At} {ta : Ty} :
      cx.peek a = .ok ta → (intOf ta).isSome = true → cx.bind x (.lanes sg w) = .ok c' →
      OpTA p cx x (.asLanes sg w a) c'
  | fop {cx c' : Cx} {x : String} {o : FOp} {a b : At} {ta tb : Ty} {q : Bool × Wd} :
      cx.peek a = .ok ta → cx.peek b = .ok tb → fixOf ta = some q → fixOf tb = some q →
      cx.bind x (.fix q.1 q.2) = .ok c' → OpTA p cx x (.fop o a b) c'
  | fcmp {cx c' : Cx} {x : String} {o : FCmp} {a b : At} {ta tb : Ty} {q : Bool × Wd} :
      cx.peek a = .ok ta → cx.peek b = .ok tb → fixOf ta = some q → fixOf tb = some q →
      cx.bind x .int = .ok c' → OpTA p cx x (.fcmp o a b) c'
  | fop1 {cx c' : Cx} {x : String} {o : FOp1} {a : At} {ta : Ty} {q : Bool × Wd} :
      cx.peek a = .ok ta → fixOf ta = some q → cx.bind x (.fix q.1 q.2) = .ok c' → OpTA p cx x (.fop1 o a) c'
  | lane {cx c' : Cx} {x : String} {a j : At} {ta tj : Ty} {q : Bool × Wd} :
      cx.peek a = .ok ta → lanesOf ta = some q → cx.peek j = .ok tj → (intOf tj).isSome = true →
      cx.bind x (.fix q.1 q.2) = .ok c' → OpTA p cx x (.lane a j) c'
  | setLane {cx c' : Cx} {x : String} {a j v : At} {ta tj tv : Ty} {q : Bool × Wd} :
      cx.peek a = .ok ta → lanesOf ta = some q → cx.peek j = .ok tj → (intOf tj).isSome = true →
      cx.peek v = .ok tv → fixOf tv = some q → cx.bind x (.lanes q.1 q.2) = .ok c' →
      OpTA p cx x (.setLane a j v) c'
  | ldlw {cx c' : Cx} {x : String} {b wi j : At} {t u tj : Ty} {n k jw : Idx} {q : Bool × Wd} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → lanesOf u = some q → intIdx cx wi = .ok jw →
      cx.ltI jw n = true → cx.ltI jw k = true → cx.peek j = .ok tj → (intOf tj).isSome = true →
      cx.bind x (.fix q.1 q.2) = .ok c' → OpTA p cx x (.ldlw b wi j) c'
  | stlw {cx c' : Cx} {x : String} {b wi j v : At} {t u tj tv : Ty} {n k jw : Idx} {q : Bool × Wd} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → lanesOf u = some q → intIdx cx wi = .ok jw →
      cx.ltI jw n = true → cx.ltI jw k = true → cx.peek j = .ok tj → (intOf tj).isSome = true →
      cx.peek v = .ok tv → fixOf tv = some q → cx.bind x .unit = .ok c' → OpTA p cx x (.stlw b wi j v) c'
  | ldl {cx c' : Cx} {x : String} {b i : At} {t u : Ty} {n k j : Idx} {q : Bool × Wd} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → lanesOf u = some q → intIdx cx i = .ok j →
      cx.ltI j (.smul q.2.lanes n) = true → cx.ltI j (.smul q.2.lanes k) = true →
      cx.bind x (.fix q.1 q.2) = .ok c' → OpTA p cx x (.ldl b i) c'
  | stl {cx c' : Cx} {x : String} {b i v : At} {t u tv : Ty} {n k j : Idx} {q : Bool × Wd} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → lanesOf u = some q → intIdx cx i = .ok j →
      cx.ltI j (.smul q.2.lanes n) = true → cx.ltI j (.smul q.2.lanes k) = true →
      cx.peek v = .ok tv → fixOf tv = some q → cx.bind x .unit = .ok c' → OpTA p cx x (.stl b i v) c'

inductive TypedA (p : Prog) : Cx → Expr → Prop
  | let_ {cx c₁ : Cx} {x : String} {op : Op} {e : Expr} :
      OpTA p cx x op c₁ → TypedA p c₁ e → TypedA p cx (.let_ x op e)
  | split {cx c₁ c₂ c₃ : Cx} {a : At} {x y : String} {e : Expr} {u v : Ty} :
      cx.use a = .ok (.prod u v, c₁) → c₁.bind x u = .ok c₂ → c₂.bind y v = .ok c₃ →
      TypedA p c₃ e → TypedA p cx (.split a x y e)
  | unpack {cx c₁ c₂ : Cx} {a : At} {i x : String} {e : Expr} {b : Ty} :
      cx.use a = .ok (.iex b, c₁) → (c₁.push i).bind x b = .ok c₂ → TypedA p c₂ e →
      TypedA p cx (.unpack a i x e)
  | unpackT {cx c₁ c₂ : Cx} {a : At} {α x : String} {e : Expr} {κ : Kind} {b : Ty} :
      cx.use a = .ok (.tex κ b, c₁) → b.guardT 0 = true → (c₁.pushT κ).bind x b = .ok c₂ →
      TypedA p c₂ e → TypedA p cx (.unpackT a α x e)
  | region {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn tn : String} {e : Expr} {u : Ty} :
      cx.use a = .ok (.ptr .own u, c₁) → rgnCellOK c₁.ke u = true →
      (c₁.push rn).bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0)) = .ok c₂ →
      c₂.bind tn (.tok (.var 0) none) = .ok c₃ → TypedA p c₃ e → TypedA p cx (.region a rn pn tn e)
  | regionBuf {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn tn : String} {e : Expr} {n k : Idx} {u : Ty} :
      cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) →
      rgnCellOK c₁.ke (.array n u) = true →
      (c₁.push rn).bind pn (.refine (.loc (.rgn (.var 0)) ((Ty.array n u).shiftI 0)) ((Pred.ini k).shift 0)) = .ok c₂ →
      c₂.bind tn (.tok (.var 0) none) = .ok c₃ → TypedA p c₃ e → TypedA p cx (.region a rn pn tn e)
  | openPub {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn cn : String} {e : Expr} {u : Ty} :
      cx.use a = .ok (.ptr .pub u, c₁) →
      (c₁.push rn).bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0)) = .ok c₂ →
      c₂.bind cn (.cap .pub (.var 0)) = .ok c₃ → TypedA p c₃ e → TypedA p cx (.openPub a rn pn cn e)
  | case {cx c₁ c₂ c₃ : Cx} {a : At} {x y : String} {e₁ e₂ : Expr} {u v : Ty} :
      cx.use a = .ok (.sum u v, c₁) → c₁.bind x u = .ok c₂ → TypedA p c₂ e₁ →
      c₁.bind y v = .ok c₃ → TypedA p c₃ e₂ → TypedA p cx (.case a x e₁ y e₂)
  | ifnull {cx c₁ c₂ : Cx} {a : At} {y : String} {e₁ e₂ : Expr} {μ : Mode} {u : Ty} :
      cx.use a = .ok (.ptrOpt μ u, c₁) → TypedA p c₁ e₁ →
      c₁.bind y (.ptr μ u) = .ok c₂ → TypedA p c₂ e₂ → TypedA p cx (.ifnull a e₁ y e₂)
  | parity {cx : Cx} {a : At} {k : String} {ev od : Expr} {i : Idx} {v : Nat} :
      intIdx cx a = .ok i → (cx.norm i).bind Lin.asVar? = some v →
      TypedA p { cx.push k with facts := (v + 1, .smul 2 (.var 0)) :: (cx.push k).facts } ev →
      TypedA p { cx.push k with facts := (v + 1, .add (.smul 2 (.var 0)) (.lit 1)) :: (cx.push k).facts } od →
      TypedA p cx (.parity a k ev od)
  | ifeqPlain {cx : Cx} {a b : At} {yes no : Expr} :
      plainEq cx a b = true → TypedA p cx yes → TypedA p cx no → TypedA p cx (.ifeq a b yes no)
  /-- The two sides normalise equal: nothing to record, and no `no` branch. -/
  | ifeqSame {cx : Cx} {a b : At} {yes no : Expr} {i j : Idx} {ni : Lin} :
      plainEq cx a b = false → intIdx cx a = .ok i → intIdx cx b = .ok j → cx.norm i = some ni → cx.norm j = some ni →
      TypedA p cx yes → TypedA p (noCx cx ni ni) no → TypedA p cx (.ifeq a b yes no)
  | ifeqL {cx : Cx} {a b : At} {yes no : Expr} {i j : Idx} {ni nj : Lin} {v : Nat} :
      plainEq cx a b = false → intIdx cx a = .ok i → intIdx cx b = .ok j → cx.norm i = some ni → cx.norm j = some nj →
      ni ≠ nj → ni.asVar? = some v → nj.mentions v = false →
      TypedA p { cx with facts := (v, nj.toIdx) :: cx.facts } yes → TypedA p (noCx cx ni nj) no →
      TypedA p cx (.ifeq a b yes no)
  | ifeqR {cx : Cx} {a b : At} {yes no : Expr} {i j : Idx} {ni nj : Lin} {v : Nat} :
      plainEq cx a b = false → intIdx cx a = .ok i → intIdx cx b = .ok j → cx.norm i = some ni → cx.norm j = some nj →
      ni ≠ nj → ni.asVar? = none → nj.asVar? = some v → ni.mentions v = false →
      TypedA p { cx with facts := (v, ni.toIdx) :: cx.facts } yes → TypedA p (noCx cx ni nj) no →
      TypedA p cx (.ifeq a b yes no)
  | ifeqZero {cx : Cx} {a b : At} {yes no : Expr} {i j : Idx} {ni nj : Lin} {u : Nat} :
      plainEq cx a b = false → intIdx cx a = .ok i → intIdx cx b = .ok j → cx.norm i = some ni → cx.norm j = some nj →
      ni ≠ nj → ni.asVar? = none → nj.asVar? = none → zeroVar ni nj = some u →
      TypedA p { cx with facts := (u, .lit 0) :: cx.facts } yes → TypedA p (noCx cx ni nj) no →
      TypedA p cx (.ifeq a b yes no)
  | casCell {cx c₁ c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw u te tv : Ty} :
      cx.peek w = .ok tw → wordOf tw = none → casCellTy cx tw = .ok u → u.rawWords = some 1 →
      affine cx.ke u = false → cx.peek e = .ok te → cx.use v = .ok (tv, c₁) →
      SubA c₁ te u → SubA c₁ tv u → (Ty.sensitiveIn c₁.ke u = true → acq = true ∧ rel = true) →
      c₁.bind t .unit = .ok c₂ → TypedA p c₂ ok → TypedA p c₁ fail →
      TypedA p cx (.cas acq rel w e v t ok fail)
  | casShare {cx c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i j : Idx} {P : Proto} {c c' : Nat} {k k' : Lin} {cl cl' : Clause} :
      cx.peek w = .ok tw → wordOf tw = some (r, P) → P.epoch = false → P.ghost = false →
      intIdx cx e = .ok i → intIdx cx v = .ok j →
      classifyM cx P i = .ok (c, k) → classifyM cx P j = .ok (c', k') →
      clauseM P c = .ok cl → clauseM P c' = .ok cl' →
      cl.holds = true → pstep P c k c' k' = true → cl'.holds = true →
      lendCx cx acq rel r (shareMove P c k c' k') t = .ok c₂ → TypedA p c₂ ok → TypedA p cx fail →
      TypedA p cx (.cas acq rel w e v t ok fail)
  | casTake {cx c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i j : Idx} {P : Proto} {c c' : Nat} {k k' : Lin} {cl cl' : Clause} :
      cx.peek w = .ok tw → wordOf tw = some (r, P) → P.epoch = false → P.ghost = false →
      intIdx cx e = .ok i → intIdx cx v = .ok j →
      classifyM cx P i = .ok (c, k) → classifyM cx P j = .ok (c', k') →
      clauseM P c = .ok cl → clauseM P c' = .ok cl' →
      cl.holds = true → pstep P c k c' k' = true → cl'.holds = false → P.lends.contains c = false →
      P.lendsDown.contains c = false → acq = true →
      cx.bind t (.tok r (some (P, j))) = .ok c₂ →
      TypedA p (if monotone P then { c₂ with unsealed := r :: c₂.unsealed } else c₂) ok →
      TypedA p cx fail → TypedA p cx (.cas acq rel w e v t ok fail)
  | casEpoch {cx c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i j : Idx} {P : Proto} {c c' : Nat} {k k' : Lin} :
      cx.peek w = .ok tw → wordOf tw = some (r, P) → P.epoch = true → acq = true →
      intIdx cx e = .ok i → intIdx cx v = .ok j →
      classifyM cx P i = .ok (c, k) → classifyM cx P j = .ok (c', k') → pstep P c k c' k' = true →
      cx.bind t (.tokE r (.word P) j) = .ok c₂ → TypedA p c₂ ok → TypedA p cx fail →
      TypedA p cx (.cas acq rel w e v t ok fail)
  | caspE {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 : Idx} {P : ECounter} :
      cx.peek w = .ok tw → word2Of tw = none → epairOf tw = some (r, P) → rel = true →
      intIdx cx e0 = .ok i0 → intIdx cx e1 = .ok i1 → intIdx cx v0 = .ok j0 → intIdx cx v1 = .ok j1 →
      cx.hasTokE r P j0 = true → cx.bind t .unit = .ok c₂ → TypedA p c₂ ok → TypedA p cx fail →
      TypedA p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)
  | caspBump {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 : Idx} {P : Proto2} {c c' : Nat} {k0 k1 k0' k1' : Lin} {cl cl' : Clause2} :
      cx.peek w = .ok tw → word2Of tw = some (r, P) →
      intIdx cx e0 = .ok i0 → intIdx cx e1 = .ok i1 → intIdx cx v0 = .ok j0 → intIdx cx v1 = .ok j1 →
      classify2M cx P i0 i1 = .ok (c, k0, k1) → classify2M cx P j0 j1 = .ok (c', k0', k1') →
      clause2M P c = .ok cl → clause2M P c' = .ok cl' →
      cl.holds = true → pstep2 P c k0 k1 c' k0' k1' = true → cl'.holds = true →
      bump2 P k0 k0' = true → acq = true →
      cx.bind t (.tokE r (.pair P) j0) = .ok c₂ → TypedA p c₂ ok → TypedA p cx fail →
      TypedA p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)
  | caspMove {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 : Idx} {P : Proto2} {c c' : Nat} {k0 k1 k0' k1' : Lin} {cl cl' : Clause2} :
      cx.peek w = .ok tw → word2Of tw = some (r, P) →
      intIdx cx e0 = .ok i0 → intIdx cx e1 = .ok i1 → intIdx cx v0 = .ok j0 → intIdx cx v1 = .ok j1 →
      classify2M cx P i0 i1 = .ok (c, k0, k1) → classify2M cx P j0 j1 = .ok (c', k0', k1') →
      clause2M P c = .ok cl → clause2M P c' = .ok cl' →
      cl.holds = true → pstep2 P c k0 k1 c' k0' k1' = true → cl'.holds = true →
      bump2 P k0 k0' = false →
      cx.bind t .unit = .ok c₂ → TypedA p c₂ ok → TypedA p cx fail →
      TypedA p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)
  | caspTake {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 : Idx} {P : Proto2} {c c' : Nat} {k0 k1 k0' k1' : Lin} {cl cl' : Clause2} :
      cx.peek w = .ok tw → word2Of tw = some (r, P) →
      intIdx cx e0 = .ok i0 → intIdx cx e1 = .ok i1 → intIdx cx v0 = .ok j0 → intIdx cx v1 = .ok j1 →
      classify2M cx P i0 i1 = .ok (c, k0, k1) → classify2M cx P j0 j1 = .ok (c', k0', k1') →
      clause2M P c = .ok cl → clause2M P c' = .ok cl' →
      cl.holds = true → pstep2 P c k0 k1 c' k0' k1' = true → cl'.holds = false → acq = true →
      cx.bind t (.tok2 r P j0 j1) = .ok c₂ → TypedA p c₂ ok → TypedA p cx fail →
      TypedA p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)
  | ret {cx c₁ : Cx} {a : At} {t : Ty} :
      cx.use a = .ok (t, c₁) → noLeak c₁ t = .ok () → noDrop c₁ = .ok () → SubA c₁ t c₁.ret →
      TypedA p cx (.ret a)
  | tail {cx c₁ : Cx} {f : String} {is : List String} {a : At} {ts : List Ty} {d : Decl} {at_ rt t : Ty} :
      p.find f = .ok d → instantiate cx d is ts = .ok (at_, rt) → cx.use a = .ok (t, c₁) →
      noLeak c₁ t = .ok () → noDrop c₁ = .ok () → SubA c₁ t at_ → SubA c₁ rt c₁.ret →
      TypedA p cx (.tail f is a ts)

/-! ## §4. Completeness: the checker accepts every `TypedA` term -/

theorem foldOk_complete {cx : Cx} {t τ : Ty} (h : FoldOKA cx t τ) : foldOk cx t τ = true := by
  cases h with
  | ptr h1 h2 => simp [foldOk, meqA_iff.1 h1, tyEq_complete h2]
  | ptrOpt h1 h2 => simp [foldOk, meqA_iff.1 h1, tyEq_complete h2]
  | loc h1 h2 => simp [foldOk, meqA_iff.1 h1, tyEq_complete h2]

theorem checkOp_complete {p : Prog} {cx : Cx} {x : String} {op : Op} {c' : Cx}
    (h : OpTA p cx x op c') : checkOp p cx x op = .ok c' := by
  cases h
  case fence => rename_i f h; exact h
  case spawn =>
    rename_i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    simp only [checkOp, h1, bind, Except.bind, sub_complete h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15, Bool.not_true, Bool.or_self, Bool.and_self, Bool.false_eq_true, ↓reduceIte]
    exact h16
  case loadWord =>
    rename_i w acq t rP h1 h2 h3 h4
    obtain ⟨r, P⟩ := rP
    simp only at h3
    simp only [checkOp, h1, h2, h3, bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
    exact h4
  case fold =>
    rename_i h1 h2 h3 h4
    simp [checkOp, h1, h2, foldOk_complete h3, h4]
  case addI =>
    rename_i hpa hpb hia hib hor hb
    simp only [checkOp, hpa, hpb, hia, hib, bind, Except.bind]
    split <;> simp_all
  all_goals (try simp only [subA_iff] at *)
  all_goals (try (simp [checkOp, *]; done))
  all_goals (try (simp [checkOp, *]; assumption))
  all_goals (try simp only [Bool.or_eq_false_iff, Bool.or_eq_true, Option.isSome_iff_ne_none,
    List.contains_iff_mem] at *)
  all_goals (try (simp [checkOp, *, bind, Except.bind, pure, Except.pure, -bind_ok_iff]; done))
  all_goals (try simp [checkOp, *, bind, Except.bind, pure, Except.pure, -bind_ok_iff])
  all_goals (try assumption)
  all_goals (try (intro hh; simp_all))
  -- `fld` on an own cell: the locative uses the reference up (`(·.2) <$> use`).
  -- (`fld`'s D4 premise `i ≠ 0 → opaqueOK c1` is left as a goal: close it by assumption.)
  all_goals (simp only [beq_iff_eq] at *; simp [checkOp, *, Functor.map, Except.map] <;> assumption)

theorem check_complete {p : Prog} {cx : Cx} {e : Expr} (h : TypedA p cx e) : check p cx e = .ok () := by
  induction h
  case let_ hop _ ih => simp [check, checkOp_complete hop, ih]
  case casTake =>
    rename_i hpw hwo hep hg hie hiv hc hc' hcl hcl' hh hps hh' hl hld ha hb _ _ ihok ihf
    subst ha
    simp at hl hld
    split at ihok <;> simp [check, *, bind, Except.bind, pure, Except.pure, -bind_ok_iff]
  all_goals (try simp only [subA_iff] at *)
  all_goals (try (simp [check, tailCheck, *]; done))
  all_goals (try (simp [check, tailCheck, *, bind, Except.bind, pure, Except.pure, -bind_ok_iff]; done))
  all_goals (try simp [check, tailCheck, *])
  -- `casCell`'s acq/rel side condition: the `if` either contradicts it or is skipped.
  all_goals (split <;> simp_all)

/-- A code block in the algorithmic judgement: `DeclT` with `TypedA`. -/
def DeclTA (p : Prog) (d : Decl) : Prop :=
  d.argTy.wf d.tparams.length d.idx.length = true ∧ d.retTy.wf d.tparams.length d.idx.length = true ∧
  d.argTy.scTop = true ∧ d.retTy.secondClass = false ∧
  TypedA p (declCx d) d.body

def ProgTA (p : Prog) : Prop := ∀ d ∈ p, DeclTA p d

theorem checkDecl_complete {p : Prog} {d : Decl} (h : DeclTA p d) : checkDecl p d = .ok () := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have := check_complete h5
  simp [checkDecl, h1, h2, h3, h4, declCx] at this ⊢
  exact this

theorem forM_ok_all {α : Type} (f : α → M Unit) :
    ∀ l : List α, (∀ a ∈ l, f a = .ok ()) → l.forM f = .ok ()
  | [], _ => rfl
  | a :: as, h => by
      have ih := forM_ok_all f as (fun b hb => h b (by simp [hb]))
      have ha := h a (by simp)
      show (f a >>= fun _ => as.forM f) = .ok ()
      rw [ha]; exact ih

/-- **Completeness.**  The checker accepts every program of the algorithmic
judgement. -/
theorem checkProg_complete {p : Prog} (h : ProgTA p) : checkProg p = .ok () :=
  forM_ok_all _ p (fun d hd => checkDecl_complete (h d hd))

/-- The algorithmic judgement is a special case of the declarative one: through
the checker, by completeness then soundness. -/
theorem TypedA.toTyped {p : Prog} {cx : Cx} {e : Expr} (h : TypedA p cx e) : Typed p cx e :=
  check_sound p e cx (check_complete h)

theorem ProgTA.toProgT {p : Prog} (h : ProgTA p) : ProgT p :=
  checkProg_sound p (checkProg_complete h)


/-! ## §5. The converse: every program the checker accepts is in `TypedA`

`checkOp_sound`/`check_sound` (CoreTyping §5), re-aimed at `OpTA`/`TypedA`: the
arithmetic is no longer converted to entailment, and the rule-selection
premises are the branch conditions the proof already has in hand. -/

theorem foldOKA_of {cx : Cx} {t τ : Ty} (h : foldOk cx t τ = true) : FoldOKA cx t τ := by
  unfold foldOk at h
  split at h <;> (try simp only [Bool.and_eq_true] at h)
  · exact .ptr (meqA_iff.2 h.1) (tyEqA_of _ _ _ _ h.2)
  · exact .ptrOpt (meqA_iff.2 h.1) (tyEqA_of _ _ _ _ h.2)
  · exact .loc (meqA_iff.2 h.1) (tyEqA_of _ _ _ _ h.2)
  · simp at h

set_option maxHeartbeats 800000 in
theorem checkOp_alg (p : Prog) (cx : Cx) (x : String) (op : Op) (cx' : Cx)
    (h : checkOp p cx x op = .ok cx') : OpTA p cx x op cx' := by
  cases op with
  | spawn f a T ts =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      have nor : ∀ {b c : Bool}, (!b || !c) = false → b = true ∧ c = true := by
        intro b c h; cases b <;> cases c <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)
      dsimp only at h
      generalize hsb : sub c₁ t T = sb at h
      cases sb
      · cases h
      rw [if_neg (by decide)] at h
      generalize hb2 : (affine c₁.ke t || affine c₁.ke T) = b2 at h
      cases b2
      case true => cases h
      rw [if_neg (by decide)] at h
      generalize hb3 : (!Ty.wf c₁.ke.length 0 T || !ts.all fun x => Ty.wf c₁.ke.length 0 x) = b3 at h
      cases b3
      case true => cases h
      rw [if_neg (by decide)] at h
      generalize hb4 : (!TermClose.tb 0 T || !ts.all (TermClose.tb 0)) = b4 at h
      cases b4
      case true => cases h
      rw [if_neg (by decide)] at h
      generalize hb5 : (!TermScope.drf T || !ts.all TermScope.drf) = b5 at h
      cases b5
      case true => cases h
      rw [if_neg (by decide)] at h
      generalize hb6 : (!TermScope.wrapOK T || !ts.all TermScope.argOK) = b6 at h
      cases b6
      case true => cases h
      rw [if_neg (by decide)] at h
      simp only [bind_ok_iff] at h
      obtain ⟨d, hd, ⟨at_, rt⟩, hi, u, hc, h⟩ := h
      generalize hb7 : (TermClose.tb 0 rt && TermTv.mg rt && TermTv.noIallV rt) = b7 at h
      cases b7
      · cases h
      rw [if_neg (by decide)] at h
      obtain ⟨hW1, hW2⟩ := nor hb3
      obtain ⟨hT1, hT2⟩ := nor hb4
      obtain ⟨hD1, hD2⟩ := nor hb5
      obtain ⟨hK1, hK2⟩ := nor hb6
      exact .spawn h1 (subA_of _ _ _ hsb) hb2 hW1 hW2 hT1 hT2 hD1 hD2 hK1 hK2 hd hi hc hb7 h
  | ext n a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      dsimp only at h
      generalize hsb : sub c₁ t n.sig.1 = sb at h
      cases sb
      · cases h
      rw [if_neg (by decide)] at h
      exact .ext h1 (subA_of _ _ _ hsb) h
  | atom a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h2⟩ := h
      exact .atom h1 h2
  | pair a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, ⟨u, c₂⟩, h2, h3⟩ := h
      exact .pair h1 h2 h3
  | inl τ a =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        simp only [bind_ok_iff] at h
        obtain ⟨⟨t, c₁⟩, h1, h2⟩ := h
        exact .inl (by simpa using hw) h1 h2
  | inr τ a =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        simp only [bind_ok_iff] at h
        obtain ⟨⟨t, c₁⟩, h1, h2⟩ := h
        exact .inr (by simpa using hw) h1 h2
  | add a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, u, hu, h⟩ := h
      rcases hot : intOf t with _ | ⟨_ | i⟩ <;> rcases hou : intOf u with _ | ⟨_ | j⟩ <;>
        simp only [hot, hou] at h
      all_goals first
        | (simp at h; done)
        | exact .addS ht hu hot hou h
        | exact .addI ht hu hot hou (by simp) h
  | sub a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, u, hu, h⟩ := h
      split at h
      · rename_i i j hi hj
        split at h
        · rename_i ni nj hni hnj
          split at h
          · rename_i hle
            exact .subS ht hu hi hj hni hnj hle h
          · simp at h
        · simp at h
      · simp at h
  | new a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · simp at h
      · rename_i hs
        exact .new h1 (by simpa using hs) h
  | publish a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      split at h
      · rename_i u heq
        split at h
        · simp only at heq; subst heq; exact .publish h1 (by assumption) h
        · simp at h
      · rename_i n u k heq
        split at h
        · simp only at heq; subst heq; exact .publishBuf h1 (by assumption) h
        · simp at h
      · simp at h
  | intoRgn rn a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨r, hr, ⟨t, c₁⟩, h1, h⟩ := h
      split at h
      · rename_i u heq
        split at h
        · simp only at heq; subst heq; exact .intoRgn hr h1 (by assumption) h
        · simp at h
      · rename_i n u k heq
        split at h
        · simp only at heq; subst heq; exact .intoRgnBuf hr h1 (by assumption) h
        · simp at h
      · simp at h
  | newBuf n τ =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        split at h
        · simp at h
        · rename_i hsc
          split at h
          · simp at h
          · rename_i hop
            split at h
            · simp at h
            · rename_i har
              simp only [bind_ok_iff] at h
              obtain ⟨k, hk, h⟩ := h
              exact .newBuf (by simpa using hw) (by simpa using hsc) (by simpa using hop) (by simpa using har) (hk) h
  | idx b i =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i c hc
        obtain ⟨μ, n, u, k⟩ := c
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i hn
          split at h
          · simp at h
          · rename_i hk
            split at h
            · simp at h
            rename_i hop
            split at h
            · rename_i hown
              simp only [bind_ok_iff, map_ok_iff] at h
              obtain ⟨c₁, ⟨⟨t', c₁'⟩, hu1, rfl⟩, h⟩ := h
              simp only [beq_iff_eq] at hown; subst hown
              exact .idxOwn ht hc (hj) ((by simpa using hn))
                ((by simpa using hk)) (by simpa using hop) hu1 h
            · rename_i hown
              simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
              exact .idxShared ht hc (by simpa using hown) (hj)
                ((by simpa using hn)) ((by simpa using hk)) (by simpa using hop) h
      · simp at h
  | bufInit b i v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      split at h
      · rename_i n u k hc
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i he
          split at h
          · simp at h
          · rename_i hl
            simp only [bind_ok_iff] at h
            obtain ⟨⟨tv, c₂⟩, h2, h⟩ := h
            split at h
            · simp at h
            · rename_i hs
              exact .bufInit h1 hc (hj) ((by simpa using he))
                ((by simpa using hl)) h2 (subA_of _ _ _ (by simpa using hs)) h
      · simp at h
      · simp at h
  | null μ τ =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        exact .null (by simpa using hw) h
  | fold a τ =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        simp only [bind_ok_iff] at h
        obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
        split at h
        · rename_i hok; exact .fold (by simpa using hw) h1 (foldOKA_of hok) h
        · simp at h
  | fld i a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i μu hc
        obtain ⟨μ, u⟩ := μu
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        split at h
        · rename_i c1 c2 hu
          simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
          split at h
          · simp at h
          rename_i hop
          split at h
          · rename_i hown
            simp only [bind_ok_iff, map_ok_iff] at h
            obtain ⟨c₁, ⟨⟨t', c₁'⟩, hu1, rfl⟩, h⟩ := h
            simp only [beq_iff_eq] at hown; subst hown
            exact .fldOwn ht hc hu (by simpa using hop) hu1 h
          · rename_i hown
            simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
            exact .fldShared ht hc (by simpa using hown) hu (by simpa using hop) h
        · simp at h
      · simp at h
  | load acq a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · split at h
        · simp at h
        · rename_i hg
          exact .loadWord ht (by assumption) (by simpa using hg) h
      · simp at h
      · rename_i hw
        split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i ha
            exact .loadOwn ht hw (by assumption) (ne_true ha) h
        · split at h
          · simp at h
          · rename_i ha
            split at h
            · simp at h
            · rename_i hs
              exact .loadPub ht hw (by assumption) (by simpa using ha) (fun hsen => by simpa [hsen] using hs) h
        · rename_i r u hc
          split at h
          · rename_i htok
            split at h
            · simp at h
            · rename_i ha
              exact .loadRgn ht hw hc (htok) (by simpa using ha) h
          · rename_i hnt
            split at h
            · rename_i hcap
              split at h
              · simp at h
              · rename_i hs
                split at h
                · simp at h
                · rename_i ha
                  exact .loadCap ht hw hc (ne_true hnt) (hcap) (fun hsen => by simpa [hsen] using hs)
                    (by simpa using ha) h
            · rename_i hncap
              simp only [bind_ok_iff] at h
              obtain ⟨⟨w, s⟩, hl, h⟩ := h
              split at h
              · simp at h
              · rename_i hfresh
                simp only [pure_ok_iff] at h; subst h
                simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hfresh
                exact .loadTorn ht hw hc (ne_true hnt) (ne_true hncap) (hl) hfresh.1 hfresh.2
  | store rel a v tok =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i r P hw
        split at h
        · rename_i tk
          simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
          obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
          try dsimp only at h
          split at h <;> (try (simp at h; done))
          rename_i r' Q i'
          split at h <;> (try (simp at h; done))
          rename_i he
          split at h <;> (try (simp at h; done))
          rename_i hq
          obtain rfl : Q = P := by simpa using hq
          simp only [bind_ok_iff, pure_ok_iff, exists_eq_left', Prod.exists] at h
          obtain ⟨j, hj, c, k, hc, c', k', hc', cl, hcl, cl', hcl', h⟩ := h
          try dsimp only at h
          split at h <;> (try (simp at h; done))
          rename_i hnh
          split at h <;> (try (simp at h; done))
          rename_i hps
          split at h
          · rename_i hh'
            split at h <;> (try (simp at h; done))
            rename_i hrel
            exact .storeWordGive ht hw h1 ((by simpa using he)) (hj)
              (hc) (hc') (hcl)
              (hcl') (by simpa using hnh) ((by simpa using hps))
              hh' (by revert hrel; cases rel <;> simp) h
          · rename_i hh'
            split at h
            · rename_i htk
              split at h <;> (try (simp at h; done))
              rename_i hrel
              exact .storeWordHand ht hw h1 ((by simpa using he)) (hj)
                (hc) (hc') (hcl)
                (hcl') (by simpa using hnh) ((by simpa using hps))
                (by simpa using hh') htk (by simpa using hrel) h
            · rename_i htk
              exact .storeWordKeep ht hw h1 ((by simpa using he)) (hj)
                (hc) (hc') (hcl)
                (hcl') (by simpa using hnh) ((by simpa using hps))
                (by simpa using hh') (by simpa using htk) h
        · simp at h
      · rename_i hw
        split at h
        · simp at h
        · rename_i μ u hc
          split at h
          · simp at h
          rename_i hwf
          have hwf : Ty.wordFreeIn cx.ke u = true := by simpa using hwf
          simp only [bind_ok_iff] at h
          obtain ⟨⟨tv, c₁⟩, h1, h⟩ := h
          cases μ with
          | own =>
              simp only at h
              split at h
              · exact .storeOwn ht hw hc hwf h1 (subA_of _ _ _ (by assumption)) h
              · simp at h
          | pub =>
              simp only at h
              split at h
              · simp at h
              · rename_i hs
                split at h
                · simp at h
                · rename_i hsr
                  exact .storePub ht hw hc hwf h1 (subA_of _ _ _ (by simpa using hs))
                    (fun hsen => by simpa [hsen] using hsr) h
          | rgn r =>
              simp only at h
              split at h
              · rename_i ht1
                split at h
                · simp at h
                · rename_i ht2
                  split at h
                  · rename_i hs
                    simp only [Bool.or_eq_true] at hs
                    exact .storeRgn ht hw hc hwf h1
                      (by simpa using ht1) (by simpa using ht2)
                      (hs.imp (subA_of _ _ _) (subA_of _ _ _)) h
                  · simp at h
              · rename_i hnt
                split at h
                · rename_i hcap
                  split at h
                  · simp at h
                  · rename_i hsr
                    split at h
                    · rename_i hs
                      simp only [Bool.or_eq_true] at hs
                      exact .storeCap ht hw hc hwf h1 (ne_true hnt) (hcap)
                        (fun hsen => by simpa [hsen] using hsr)
                        (hs.imp (subA_of _ _ _) (subA_of _ _ _)) h
                    · simp at h
                · simp at h
  | fence f => exact .fence h
  | mkWord rn P v tk =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      split at h
      · simp at h
      · rename_i hp
        simp only [bind_ok_iff] at h
        obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
        try dsimp only at h
        split at h
        · rename_i r'
          split at h
          · simp at h
          · rename_i he
            simp only [bind_ok_iff, pure_ok_iff, exists_eq_left', Prod.exists] at h
            obtain ⟨j, hj, c, k, hc, cl, hcl, h⟩ := h
            try dsimp only at h
            split at h
            · rename_i hg
              split at h
              · simp at h
              · rename_i hh
                exact .mkWordGhost hr (by simpa using hp) h1 ((by simpa using he))
                  (hj) (hc) (hcl) hg (by simpa using hh) h
            · rename_i hg
              split at h
              · simp at h
              · rename_i hh
                exact .mkWord hr (by simpa using hp) h1 ((by simpa using he)) (hj)
                  (hc) (hcl) (by simpa using hg) (by simpa using hh) h
        · simp at h
        · simp at h
  | mkWord2 rn P v0 v1 tk =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      split at h
      · simp at h
      · rename_i hp
        simp only [bind_ok_iff] at h
        obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
        try dsimp only at h
        split at h
        · rename_i r'
          split at h
          · simp at h
          · rename_i he
            simp only [bind_ok_iff, pure_ok_iff, exists_eq_left', Prod.exists] at h
            obtain ⟨j0, hj0, j1, hj1, c, k0, k1, hc, cl, hcl, h⟩ := h
            try dsimp only at h
            split at h
            · simp at h
            · rename_i hh
              exact .mkWord2 hr (by simpa using hp) h1 (by simpa using he) hj0 hj1 hc hcl
                (by simpa using hh) h
        · simp at h
        · simp at h
  | ldp acq a n0 n1 =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i hp
        split at h
        · exact .ldp ht hp h
        · simp at h
      · simp at h
  | mkEPair rn P v0 v1 =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      split at h <;> (try (simp at h; done))
      rename_i hp
      simp only [bind_ok_iff] at h
      obtain ⟨j0, hj0, j1, hj1, h⟩ := h
      exact .mkEPair hr (by simpa using hp) hj0 hj1 h
  | mkTicket rn N P v tk =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      split at h <;> (try (simp at h; done))
      rename_i hN
      obtain ⟨hN1, hN2⟩ : pwf N = true ∧ N.epoch = true := by simpa using hN
      split at h <;> (try (simp at h; done))
      rename_i hP
      obtain ⟨hP1, hP2⟩ : pwf P = true ∧ P.ticket = true := by simpa using hP
      simp only [bind_ok_iff] at h
      obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i r'
        split at h
        · simp at h
        · rename_i he
          simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
          obtain ⟨j, hj, h⟩ := h
          exact .mkTicket hr hN1 hN2 hP1 hP2 h1 (by simpa using he) hj h
      · simp at h
      · simp at h
  | claim a tk =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · split at h <;> (try (simp at h; done))
        rename_i htk
        simp only [bind_ok_iff] at h
        obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
        try dsimp only at h
        split at h
        · split at h
          · simp at h
          · rename_i he
            simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
            split at h
            · rename_i hs
              exact .claim ht (by assumption) (by simpa using htk) h1 (by simpa using he) hs h
            · simp at h
        · simp at h
      · simp at h
      · simp at h
  | fetch o acq rel a v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨tw, htw, h⟩ := h
      split at h
      · rename_i hw
        simp only [bind_ok_iff] at h
        obtain ⟨u, hc, h⟩ := h
        split at h <;> (try (simp at h; done))
        rename_i hu
        simp only [bind_ok_iff, Prod.exists] at h
        obtain ⟨tv, c₁, h1, h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i hs
        have hu' : u = .int := by simpa using hu
        subst hu'
        exact .fetchCell htw hw hc h1 (subA_iff.2 (by simpa using hs)) h
      · rename_i r P hw
        split at h <;> (try (simp at h; done))
        rename_i ho
        have ho' : o = .add := by simpa using ho
        subst ho'
        simp only [bind_ok_iff] at h
        obtain ⟨j, hj, h⟩ := h
        cases hep : P.epoch
        case true =>
          simp only [hep, ↓reduceIte] at h
          split at h <;> (try (simp at h; done))
          rename_i hacq
          split at h <;> (try (simp at h; done))
          rename_i he
          exact .fetchEpoch htw hw hj hep (by simpa using hacq) (by simpa using he) h
        case false =>
          simp only [hep, Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at h
          obtain ⟨d, hd, h⟩ := h
          split at h <;> (try (simp at h; done))
          rename_i he
          split at h <;> (try (simp at h; done))
          rename_i hok
          exact .fetchShare htw hw hj hep hd (by simpa using he) (by simpa using hok) h
  | stp rel a v0 v1 tk =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i r P hw
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i r' Q i0' i1'
        split at h <;> (try (simp at h; done))
        rename_i he
        split at h <;> (try (simp at h; done))
        rename_i hq
        obtain rfl : Q = P := by simpa using hq
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left', Prod.exists] at h
        obtain ⟨j0, hj0, j1, hj1, c, k0, k1, hc, c', k0', k1', hc', cl, hcl, cl', hcl', h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i hnh
        split at h <;> (try (simp at h; done))
        rename_i hps
        split at h
        · rename_i hh'
          split at h <;> (try (simp at h; done))
          rename_i hrel
          exact .stpGive ht hw h1 (by simpa using he) hj0 hj1 hc hc' hcl hcl'
            (by simpa using hnh) (by simpa using hps) hh' (by simpa using hrel) h
        · rename_i hh'
          exact .stpKeep ht hw h1 (by simpa using he) hj0 hj1 hc hc' hcl hcl'
            (by simpa using hnh) (by simpa using hps) (by simpa using hh') h
  | pack a wn τ =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨w, hw, h⟩ := h
      split at h
      · rename_i body
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        split at h
        · simp at h
        · rename_i hwf
          simp only [bind_ok_iff] at h
          obtain ⟨⟨t, c₁⟩, h1, u, hn, h⟩ := h
          try dsimp only at h
          split at h
          · exact .pack hw (by simpa using hwf) h1 (hn) (subA_of _ _ _ (by assumption)) h
          · simp at h
      · simp at h
  | packT a σ τ =>
      simp only [checkOp] at h
      split at h
      · rename_i κ body
        split at h
        · simp at h
        · rename_i hg
          split at h
          · simp at h
          · rename_i hwf
            split at h
            · simp at h
            · rename_i had
              simp only [bind_ok_iff] at h
              obtain ⟨⟨t, c₁⟩, h1, u, hn, h⟩ := h
              try dsimp only at h
              split at h
              · exact .packT (by simpa using hg) (by simpa using hwf) (by simpa using had) h1
                  (hn) (subA_of _ _ _ (by assumption)) h
              · simp at h
      · simp at h
  | validate y =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i tn htn
        split at h
        · rename_i v hv
          split at h
          · simp at h
          · rename_i he
            split at h
            · simp at h
            · rename_i ha
              exact .validate htn hv ((by simpa using he)) (by simpa using ha) h
        · simp at h
        · simp at h
  | call f is a ts =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨d, hd, ⟨at_, rt⟩, hi, ⟨t, c₁⟩, h1, u, hn, h⟩ := h
      split at h
      · simp at h
      · rename_i hs
        exact .call hd hi h1 (hn) (subA_of _ _ _ (by simpa using hs)) h
  | borrow c a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨y, hy, t, ht, r, hr, ⟨t', c₁⟩, h1, h⟩ := h
      exact .borrow hy ht hr h1 h
  | endBorrow a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨y, hy, h⟩ := h
      split at h
      · simp at h
      · rename_i hl
        exact .endBorrow hy (by simpa using hl) h
  | xchg a v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, ⟨u, o⟩, hx, ⟨tv, c₁⟩, h1, h⟩ := h
      split at h
      · simp at h
      · rename_i hs
        have hs' : sub c₁ tv u = true ∨ sub c₁ tv o = true := by
          revert hs; cases sub c₁ tv u <;> cases sub c₁ tv o <;> simp
        exact .xchg ht (hx) h1
          (hs'.elim (fun e => .inl (subA_of _ _ _ e)) (fun e => .inr (subA_of _ _ _ e))) h
  | fnptr f =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨d, hd, h⟩ := h
      split at h
      · simp at h
      · rename_i hm
        have hm' : d.tparams = [] ∧ d.idx = [] := by simpa using hm
        exact .fnptr hd hm'.1 hm'.2 h
  | callc f a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨tf, htf, h⟩ := h
      split at h
      · rename_i σ τ hc
        simp only [bind_ok_iff] at h
        obtain ⟨⟨t, c₁⟩, h1, u, hn, h⟩ := h
        split at h
        · simp at h
        · rename_i hs
          exact .callc htf hc h1 (hn) (subA_of _ _ _ (by simpa using hs)) h
      · simp at h
  | rem a n =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, hta, h⟩ := h
      split at h
      · simp at h
      · rename_i hi
        simp only [bind_ok_iff] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i v hv
          cases e : intOf ta with
          | none => simp [e] at hi
          | some o => exact .rem hta e (hj) hv h
  | nameI a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨j, hj, h⟩ := h
      exact .nameI (hj) h
  | xchgAt b i v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i n u k hc
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        split at h
        · simp at h
        rename_i hwf
        simp only [bind_ok_iff] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i hn
          split at h
          · simp at h
          · rename_i hk
            simp only [bind_ok_iff] at h
            obtain ⟨⟨tv, c₁⟩, h1, h⟩ := h
            split at h
            · simp at h
            · rename_i hs
              exact .xchgAt ht hc (by simpa using hwf) (hj) ((by simpa using hn))
                ((by simpa using hk)) h1 (subA_of _ _ _ (by simpa using hs)) h
      · simp at h
      · simp at h
  | loadAt b i =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i n u k hc
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i hn
          split at h
          · simp at h
          · rename_i hk
            split at h
            · simp at h
            · rename_i ha
              exact .loadAt ht hc (hj) ((by simpa using hn))
                ((by simpa using hk)) (by simpa using ha) h
      · simp at h
      · simp at h
  | bits o a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, hta, tb, htb, h⟩ := h
      split at h
      · rename_i oa ob ea eb
        exact .bits hta htb ea eb h
      · simp at h
  | bit1 o a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, hta, h⟩ := h
      split at h
      · rename_i oa ea
        exact .bit1 hta ea h
      · simp at h
  | vmatch lo hi b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t1, h1, t2, h2, t3, h3, h⟩ := h
      split at h
      · rename_i o1 o2 o3 e1 e2 e3
        exact .vmatch h1 h2 h3 e1 e2 e3 h
      · simp at h
  | band a m =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, hta, h⟩ := h
      split at h
      · simp at h
      · rename_i hi
        simp only [bind_ok_iff] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i v hv
          cases e : intOf ta with
          | none => simp [e] at hi
          | some o => exact .band hta e (hj) hv h
  | zero τ =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        split at h
        · simp at h
        · rename_i hs
          split at h
          · simp at h
          · rename_i hz
            exact .zero (by simpa using hw) (by simpa using hs) (by simpa using hz) h
  | xchgAtF b i q v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i n u k hc
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        split at h
        · simp at h
        · rename_i c hq
          split at h
          · simp at h
          rename_i hop
          split at h
          · simp at h
          rename_i hwf
          simp only [bind_ok_iff] at h
          obtain ⟨j, hj, h⟩ := h
          split at h
          · simp at h
          · rename_i hn
            split at h
            · simp at h
            · rename_i hk
              simp only [bind_ok_iff] at h
              obtain ⟨⟨tv, c₁⟩, h1, h⟩ := h
              split at h
              · simp at h
              · rename_i hs
                exact .xchgAtF ht hc hq (by simpa using hop) (by simpa using hwf) (hj) ((by simpa using hn))
                  ((by simpa using hk)) h1 (subA_of _ _ _ (by simpa using hs)) h
      · simp at h
      · simp at h
  | loadAtF b i q =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i n u k hc
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        split at h
        · simp at h
        · rename_i c hq
          split at h
          · simp at h
          rename_i hop
          simp only [bind_ok_iff] at h
          obtain ⟨j, hj, h⟩ := h
          split at h
          · simp at h
          · rename_i hn
            split at h
            · simp at h
            · rename_i hk
              split at h
              · simp at h
              · rename_i ha
                exact .loadAtF ht hc hq (by simpa using hop) (hj) ((by simpa using hn))
                  ((by simpa using hk)) (by simpa using ha) h
      · simp at h
      · simp at h
  | cvt sg w a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i hc
        exact .cvt ht (by simpa using hc) h
  | toInt a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i hc
        exact .toInt ht (by simpa using hc) h
  | asLanes sg w a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i hc
        exact .asLanes ht (by simpa [Option.isSome_iff_ne_none] using hc) h
  | fop o a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, tb, htb, h⟩ := h
      split at h
      · simp at h
      · rename_i q hq
        split at h
        · simp at h
        · rename_i hq'
          exact .fop ht htb hq (by simpa using hq') h
  | fcmp o a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, tb, htb, h⟩ := h
      split at h
      · simp at h
      · rename_i q hq
        split at h
        · simp at h
        · rename_i hq'
          exact .fcmp ht htb hq (by simpa using hq') h
  | fop1 o a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i q hq
        exact .fop1 ht hq h
  | lane a j =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i q hq
        simp only [bind_ok_iff] at h
        obtain ⟨tj, htj, h⟩ := h
        split at h
        · simp at h
        · rename_i hl
          exact .lane ht hq htj (by simpa [Option.isSome_iff_ne_none] using hl) h
  | setLane a j v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i q hq
        simp only [bind_ok_iff] at h
        obtain ⟨tj, htj, h⟩ := h
        split at h
        · simp at h
        · rename_i hl
          simp only [bind_ok_iff] at h
          obtain ⟨tv, htv, h⟩ := h
          split at h
          · simp at h
          · rename_i hv
            exact .setLane ht hq htj (by simpa [Option.isSome_iff_ne_none] using hl) htv
              (by simpa using hv) h
  | ldlw b wi j =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i μ n u k hb
        split at h
        · simp at h
        · rename_i hμ
          have hμ' : μ = .own := by simpa using hμ
          subst hμ'
          split at h
          · simp at h
          · rename_i q hq
            simp only [bind_ok_iff] at h
            obtain ⟨jw, hj, h⟩ := h
            split at h
            · simp at h
            · rename_i hn
              split at h
              · simp at h
              · rename_i hk
                simp only [bind_ok_iff] at h
                obtain ⟨tj, htj, h⟩ := h
                split at h
                · simp at h
                · rename_i hl
                  exact .ldlw ht hb hq (hj) ((by simpa using hn))
                    ((by simpa using hk)) htj
                    (by simpa [Option.isSome_iff_ne_none] using hl) h
  | stlw b wi j v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i μ n u k hb
        split at h
        · simp at h
        · rename_i hμ
          have hμ' : μ = .own := by simpa using hμ
          subst hμ'
          split at h
          · simp at h
          · rename_i q hq
            simp only [bind_ok_iff] at h
            obtain ⟨jw, hj, h⟩ := h
            split at h
            · simp at h
            · rename_i hn
              split at h
              · simp at h
              · rename_i hk
                simp only [bind_ok_iff] at h
                obtain ⟨tj, htj, h⟩ := h
                split at h
                · simp at h
                · rename_i hl
                  simp only [bind_ok_iff] at h
                  obtain ⟨tv, htv, h⟩ := h
                  split at h
                  · simp at h
                  · rename_i hv
                    exact .stlw ht hb hq (hj) ((by simpa using hn))
                      ((by simpa using hk)) htj
                      (by simpa [Option.isSome_iff_ne_none] using hl) htv (by simpa using hv) h
  | ldl b i =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i μ n u k hb
        split at h
        · simp at h
        · rename_i hμ
          have hμ' : μ = .own := by simpa using hμ
          subst hμ'
          split at h
          · simp at h
          · rename_i q hq
            simp only [bind_ok_iff] at h
            obtain ⟨j, hj, h⟩ := h
            split at h
            · simp at h
            · rename_i hn
              split at h
              · simp at h
              · rename_i hk
                exact .ldl ht hb hq (hj) ((by simpa using hn))
                  ((by simpa using hk)) h
  | stl b i v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i μ n u k hb
        split at h
        · simp at h
        · rename_i hμ
          have hμ' : μ = .own := by simpa using hμ
          subst hμ'
          split at h
          · simp at h
          · rename_i q hq
            simp only [bind_ok_iff] at h
            obtain ⟨j, hj, h⟩ := h
            split at h
            · simp at h
            · rename_i hn
              split at h
              · simp at h
              · rename_i hk
                simp only [bind_ok_iff] at h
                obtain ⟨tv, htv, h⟩ := h
                split at h
                · simp at h
                · rename_i hv
                  exact .stl ht hb hq (hj) ((by simpa using hn))
                    ((by simpa using hk)) htv (by simpa using hv) h
  | freeze a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
      split at h
      · split at h
        · simp at h
        · rename_i hs
          subst_vars
          exact .freeze h1 (by simpa using hs) h
      · simp at h
      · simp at h

theorem check_alg (p : Prog) : ∀ (e : Expr) (cx : Cx), check p cx e = .ok () → TypedA p cx e := by
  intro e
  induction e with
  | let_ x op e ih =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨c₁, h1, h2⟩ := h
      exact .let_ (checkOp_alg p cx x op c₁ h1) (ih c₁ h2)
  | split a x y e ih =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u v
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
        exact .split h1 h2 h3 (ih c₃ h4)
      · simp at h
  | unpack a i x e ih =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i b
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, h3⟩ := h
        exact .unpack h1 h2 (ih c₂ h3)
      · simp at h
  | unpackT a α x e ih =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i κ b
        split at h
        · simp at h
        · rename_i hg
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h2, h3⟩ := h
          exact .unpackT h1 (by simpa using hg) h2 (ih c₂ h3)
      · simp at h
  | region a rn pn tn e ih =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u
        split at h
        · simp at h
        · rename_i hs
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
          exact .region h1 (by simpa using hs) h2 h3 (ih c₃ h4)
      · split at h
        · simp at h
        · rename_i hs
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
          exact .regionBuf h1 (by simpa using hs) h2 h3 (ih c₃ h4)
      · simp at h
  | openPub a rn pn cn e ih =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
        exact .openPub h1 h2 h3 (ih c₃ h4)
      · simp at h
  | case a x e₁ y e₂ ih₁ ih₂ =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u v
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, _, h3, c₃, h4, h5⟩ := h
        exact .case h1 h2 (ih₁ c₂ h3) h4 (ih₂ c₃ h5)
      · simp at h
  | ifnull a e₁ y e₂ ih₁ ih₂ =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i μ u
        simp only [bind_ok_iff] at h
        obtain ⟨_, h2, c₂, h3, h4⟩ := h
        exact .ifnull h1 (ih₁ c₁ h2) h3 (ih₂ c₂ h4)
      · simp at h
  | parity a k ev od ihe iho =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨i, hi, h⟩ := h
      split at h
      · rename_i v hv
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        obtain ⟨_, h1, h2⟩ := h
        exact .parity (hi) hv (ihe _ h1) (iho _ h2)
      · simp at h
  | ifeq a b yes no ihy ihn =>
      intro cx h
      simp only [check] at h
      split at h
      · rename_i hpe
        simp only [bind_ok_iff] at h
        obtain ⟨_, h1, h2⟩ := h
        exact .ifeqPlain (hpe) (ihy cx h1) (ihn cx h2)
      rename_i hnpe
      have hnpe' := ne_true hnpe
      simp only [bind_ok_iff] at h
      obtain ⟨i, hi, j, hj, h⟩ := h
      split at h
      · rename_i ni nj hni hnj
        split at h
        · rename_i heq
          simp only [beq_iff_eq] at heq; subst heq
          simp only [bind_ok_iff] at h
          obtain ⟨_, h1, h2⟩ := h
          exact .ifeqSame hnpe' hi hj hni hnj (ihy cx h1) (ihn _ h2)
        · rename_i hne
          have hne' : ni ≠ nj := by simpa using hne
          rcases hva : ni.asVar? with _ | v <;> rcases hvb : nj.asVar? with _ | v' <;>
            simp only [hva, hvb] at h
          · split at h
            · rename_i u hz
              simp only [bind_ok_iff] at h
              obtain ⟨_, h1, h2⟩ := h
              exact .ifeqZero hnpe' hi hj hni hnj hne' hva hvb hz (ihy _ h1) (ihn _ h2)
            · simp at h
          · split at h <;> (try (simp at h; done))
            rename_i hm
            simp only [bind_ok_iff] at h
            obtain ⟨_, h1, h2⟩ := h
            exact .ifeqR hnpe' hi hj hni hnj hne' hva hvb (ne_true hm) (ihy _ h1) (ihn _ h2)
          all_goals
            split at h <;> (try (simp at h; done))
            rename_i hm
            simp only [bind_ok_iff] at h
            obtain ⟨_, h1, h2⟩ := h
            exact .ifeqL hnpe' hi hj hni hnj hne' hva (ne_true hm) (ihy _ h1) (ihn _ h2)
      · simp at h
  | cas acq rel w e v t ok fail ihok ihf =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨tw, htw, h⟩ := h
      split at h
      · rename_i hw
        simp only [bind_ok_iff] at h
        obtain ⟨u, hc, h⟩ := h
        split at h <;> (try (simp at h; done))
        rename_i hraw
        split at h <;> (try (simp at h; done))
        rename_i haff
        simp only [bind_ok_iff, Prod.exists] at h
        obtain ⟨te, hte, tv, c₁, h1, h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i hse
        split at h <;> (try (simp at h; done))
        rename_i hsv
        split at h <;> (try (simp at h; done))
        rename_i hsens
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, _, h3, h4⟩ := h
        exact .casCell htw hw (hc) (by simpa using hraw) (by simpa using haff) hte h1
          (subA_of _ _ _ (by simpa using hse)) (subA_of _ _ _ (by simpa using hsv))
          (fun hs => by simpa [hs] using hsens) h2 (ihok c₂ h3) (ihf c₁ h4)
      · rename_i r P hw
        cases hep : P.epoch
        case true =>
          simp only [hep, ↓reduceIte] at h
          split at h <;> (try (simp at h; done))
          rename_i hacq
          simp only [bind_ok_iff, Prod.exists] at h
          obtain ⟨i, hi, j, hj, c, k, hc, c', k', hc', h⟩ := h
          try dsimp only at h
          split at h <;> (try (simp at h; done))
          rename_i hps
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h3, _, h4, h2⟩ := h
          exact .casEpoch htw hw hep (by simpa using hacq) hi hj hc hc' (by simpa using hps) h3
            (ihok c₂ h4) (ihf cx h2)
        simp only [hep, Bool.false_eq_true, ↓reduceIte] at h
        cases hg : P.ghost
        case true => simp only [hg, ↓reduceIte] at h; simp at h
        simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
        simp only [bind_ok_iff, Prod.exists] at h
        obtain ⟨i, hi, j, hj, c, k, hc, c', k', hc', cl, hcl, cl', hcl', h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i hh
        split at h <;> (try (simp at h; done))
        rename_i hps
        split at h
        · rename_i hh'
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h3, _, h4, h2⟩ := h
          exact .casShare htw hw hep (by simpa using hg) (hi) (hj)
            (hc) (hc') (hcl)
            (hcl') (by simpa using hh) ((by simpa using hps))
            hh' (h3) (ihok c₂ h4) (ihf cx h2)
        · rename_i hh'
          split at h <;> (try (simp at h; done))
          rename_i hlend
          split at h <;> (try (simp at h; done))
          rename_i hacq
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h3, _, h4, h2⟩ := h
          exact .casTake htw hw hep (by simpa using hg) (hi) (hj)
            (hc) (hc') (hcl)
            (hcl') (by simpa using hh) ((by simpa using hps))
            (by simpa using hh')
            (by simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hlend; exact hlend.1)
            (by simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hlend; exact hlend.2)
            (by simpa using hacq) h3 (ihok _ h4) (ihf cx h2)
  | casp acq rel w e0 e1 v0 v1 t ok fail ihok ihf =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨tw, htw, h⟩ := h
      split at h
      · rename_i hw2
        split at h
        · simp at h
        · rename_i r P hw
          split at h <;> (try (simp at h; done))
          rename_i hrel
          simp only [bind_ok_iff] at h
          obtain ⟨i0, hi0, i1, hi1, j0, hj0, j1, hj1, h⟩ := h
          try dsimp only at h
          split at h <;> (try (simp at h; done))
          rename_i htk
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h3, _, h4, h2⟩ := h
          exact .caspE htw hw2 hw (by simpa using hrel) hi0 hi1 hj0 hj1 (by simpa using htk) h3
            (ihok c₂ h4) (ihf cx h2)
      · rename_i r P hw
        simp only [bind_ok_iff, Prod.exists] at h
        obtain ⟨i0, hi0, i1, hi1, j0, hj0, j1, hj1, c, k0, k1, hc, c', k0', k1', hc', cl, hcl, cl', hcl', h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i hh
        split at h <;> (try (simp at h; done))
        rename_i hps
        split at h
        · rename_i hh'
          split at h
          · rename_i hb
            split at h <;> (try (simp at h; done))
            rename_i hacq
            simp only [bind_ok_iff] at h
            obtain ⟨c₂, h3, _, h4, h2⟩ := h
            exact .caspBump htw hw hi0 hi1 hj0 hj1 hc hc' hcl hcl' (by simpa using hh)
              (by simpa using hps) hh' hb (by simpa using hacq) h3 (ihok c₂ h4) (ihf cx h2)
          · rename_i hb
            simp only [bind_ok_iff] at h
            obtain ⟨c₂, h3, _, h4, h2⟩ := h
            exact .caspMove htw hw hi0 hi1 hj0 hj1 hc hc' hcl hcl' (by simpa using hh)
              (by simpa using hps) hh' (by simpa using hb) h3 (ihok c₂ h4) (ihf cx h2)
        · rename_i hh'
          split at h <;> (try (simp at h; done))
          rename_i hacq
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h3, _, h4, h2⟩ := h
          exact .caspTake htw hw hi0 hi1 hj0 hj1 hc hc' hcl hcl' (by simpa using hh)
            (by simpa using hps) (by simpa using hh') (by simpa using hacq) h3 (ihok c₂ h4) (ihf cx h2)
  | ret a =>
      intro cx h
      simp only [check, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, u, hn, u', hnd, h⟩ := h
      try dsimp only at h
      split at h
      · simp at h
      · rename_i hs
        exact .ret h1 (hn) hnd (subA_of _ _ _ (by simpa using hs))
  | tail f is a ts =>
      intro cx h
      simp only [check, tailCheck, bind_ok_iff] at h
      obtain ⟨d, hd, ⟨at_, rt⟩, hi, ⟨t, c₁⟩, h1, u, hn, u', hnd, h⟩ := h
      try dsimp only at h
      split at h
      · simp at h
      · rename_i hs
        split at h
        · simp at h
        · rename_i hr
          exact .tail hd hi h1 (hn) hnd (subA_of _ _ _ (by simpa using hs))
            (subA_of _ _ _ (by simpa using hr))

theorem checkDecl_alg {p : Prog} {d : Decl} (h : checkDecl p d = .ok ()) : DeclTA p d := by
  unfold checkDecl at h
  simp only at h
  split at h
  · simp at h
  · rename_i hwf
    split at h
    · simp at h
    · rename_i hsc
      simp at hwf hsc
      exact ⟨hwf.1, hwf.2, hsc.1, hsc.2, check_alg p d.body _ h⟩

/-- **The algorithmic judgement is exactly the checker.** -/
theorem checkProg_iff {p : Prog} : checkProg p = .ok () ↔ ProgTA p :=
  ⟨fun h d hd => checkDecl_alg (CoreTyping.forM_ok _ p h d hd), checkProg_complete⟩

theorem check_iff {p : Prog} {cx : Cx} {e : Expr} : check p cx e = .ok () ↔ TypedA p cx e :=
  ⟨check_alg p e cx, check_complete⟩

/-- And so `ProgTA` (= the checker, `checkProg_iff`) is a strict subset of
`ProgT`: here is a `ProgT` program that is not `ProgTA`. -/
theorem w1Prog_not_alg : ¬ ProgTA w1Prog := fun h => by
  have := checkProg_complete h
  have h2 := w1Prog_refused
  rw [this] at h2
  simp [accepts] at h2

/-- `ProgTA ⊊ ProgT`. -/
theorem progTA_strict : (∀ p, ProgTA p → ProgT p) ∧ ∃ p, ProgT p ∧ ¬ ProgTA p :=
  ⟨fun _ h => h.toProgT, w1Prog, w1Prog_typed, w1Prog_not_alg⟩

#print axioms progTA_strict
#print axioms checkProg_iff
#print axioms check_iff
#print axioms checkProg_complete
#print axioms ProgTA.toProgT

end Complete
