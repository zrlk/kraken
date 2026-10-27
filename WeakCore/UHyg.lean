/-
# UHyg — hygiene of UnElab configurations (the invariant `UInv`)

`UInv U c`: `U` has no reserved user name (`noReserved U`), and in every thread every `%`-name `tmp j` the
thread can still meet — in its term (binders, operand variables, the `ldp`/`validate` names of a `let` head), in
its environment's keys, and per stack frame in the frame's body, return binder and saved environment — has
`j` below the counter of the block it lives in (`th.ctr`, resp. the frame's `ctr`).  So the next temporaries
`tmp ctr, tmp (ctr+1), …` are fresh for the thread.

* `okName n s`: `s = tmp j → j < n`; `uNames e`: the names of `e` that `noReservedE` checks;
  `HygE n e := ∀ s ∈ uNames e, okName n s`.
* `noReservedE e → HygE n e` (`hygE_of_noRes`); the layer of a hygienic term is hygienic at its new counter
  (`layer_letOp_hyg`, `layer_head_hyg`); `ustep` preserves `ThInv` (`ustep_inv`).
* `UInv` is preserved by every U move (`UStep.inv`, `USpawn.inv`, `UExt.inv`, `StepsU.inv`), holds at the
  wrapper start `startU` (whose image is the core's `startW (elabProg U)`), hence on every reachable
  configuration (`uInv_reach`).
-/
import WeakCore.UElabSim
import WeakCore.TermStartW

set_option linter.unusedSimpArgs false

namespace UnElab
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep TermStartW
open WeakMem (Memory Ts VState AllocLabel Address Val Arch)

/-! ## Names -/

theorem tmp_inj {i j : Nat} (h : tmp i = tmp j) : i = j := by
  unfold tmp at h
  have h' : toString i = toString j := by simpa using h
  exact Nat.repr_inj.mp h'

theorem tmp_isReserved (j : Nat) : reserved (tmp j) = true := by
  unfold reserved tmp; simp

/-- `s` is not a temporary at or above `n`. -/
def okName (n : Nat) (s : String) : Prop := ∀ j, s = tmp j → j < n

theorem okName_mono {n m : Nat} {s : String} (h : okName n s) (hnm : n ≤ m) : okName m s :=
  fun j hj => Nat.lt_of_lt_of_le (h j hj) hnm

theorem okName_tmp {j n : Nat} (h : j < n) : okName n (tmp j) := by
  intro i hi
  rw [← tmp_inj hi]
  exact h

theorem okName_of_res {n : Nat} {s : String} (h : reserved s = false) : okName n s := by
  intro j hj
  subst hj
  simp [tmp_isReserved] at h

/-- The names an atom mentions. -/
def atNames : At → List String
  | .var x => [x]
  | _ => []

mutual
def argNames : UArg → List String
  | .at a => atNames a
  | .op _ args => argsNames args
def argsNames : List UArg → List String
  | [] => []
  | a :: r => argNames a ++ argsNames r
end

def patNames : UPat → List String
  | .bind (some x) => [x]
  | .bind none => []
  | .pair p q => patNames p ++ patNames q

/-- The names of a `let` head that bind or name variables (`noResHead`'s). -/
def headNames : Op → List String
  | .ldp _ _ n0 n1 => [n0, n1]
  | .validate y => [y]
  | _ => []

/-- The names of a term that `noReservedE` checks; the operands come first. -/
def uNames : UExpr → List String
  | .let_ x h args e => argsNames args ++ (patNames (.bind x) ++ (headNames h ++ uNames e))
  | .split a p q e => argNames a ++ (patNames p ++ (patNames q ++ uNames e))
  | .unpack a i x e => argNames a ++ (i :: x :: uNames e)
  | .unpackT a al x e => argNames a ++ (al :: x :: uNames e)
  | .region a r p t e => argNames a ++ (r :: p :: t :: uNames e)
  | .openPub a r p c e => argNames a ++ (r :: p :: c :: uNames e)
  | .case a x e₁ y e₂ => argNames a ++ (x :: y :: (uNames e₁ ++ uNames e₂))
  | .ifnull a e₁ x e₂ => argNames a ++ (x :: (uNames e₁ ++ uNames e₂))
  | .parity a k ev od => argNames a ++ (k :: (uNames ev ++ uNames od))
  | .ifeq a b yes no => argsNames [a, b] ++ (uNames yes ++ uNames no)
  | .cas _ _ w e v t ok fail => argsNames [w, e, v] ++ (t :: (uNames ok ++ uNames fail))
  | .casp _ _ w e0 e1 v0 v1 t ok fail => argsNames [w, e0, e1, v0, v1] ++ (t :: (uNames ok ++ uNames fail))
  | .ret a => argNames a ++ []
  | .tail _ _ a _ => argNames a ++ []

/-- **Hygiene of a U term at counter `n`**: no checked name is a temporary at or above `n`. -/
def HygE (n : Nat) (e : UExpr) : Prop := ∀ s ∈ uNames e, okName n s

theorem HygE.mono {n m : Nat} {e : UExpr} (h : HygE n e) (hnm : n ≤ m) : HygE m e :=
  fun s hs => okName_mono (h s hs) hnm

/-! ## Reserved-freeness gives hygiene -/

mutual
theorem argNames_noRes : ∀ {a : UArg}, noResArg a = true → ∀ s ∈ argNames a, reserved s = false
  | .at a, h, s, hs => by
      cases a <;> simp_all [noResArg, okAt, argNames, atNames]
  | .op _ args, h, s, hs => by
      simp only [noResArg, Bool.and_eq_true] at h
      simp only [argNames] at hs
      exact argsNames_noRes h.2 s hs
theorem argsNames_noRes : ∀ {as : List UArg}, noResArgs as = true → ∀ s ∈ argsNames as, reserved s = false
  | [], _, s, hs => by simp [argsNames] at hs
  | a :: r, h, s, hs => by
      simp only [noResArgs, Bool.and_eq_true] at h
      simp only [argsNames, List.mem_append] at hs
      rcases hs with hs | hs
      · exact argNames_noRes h.1 s hs
      · exact argsNames_noRes h.2 s hs
end

theorem patNames_noRes : ∀ {p : UPat}, noResPat p = true → ∀ s ∈ patNames p, reserved s = false
  | .bind (some x), h, s, hs => by simp_all [noResPat, patNames]
  | .bind none, _, s, hs => by simp [patNames] at hs
  | .pair p q, h, s, hs => by
      simp only [noResPat, Bool.and_eq_true] at h
      simp only [patNames, List.mem_append] at hs
      rcases hs with hs | hs
      · exact patNames_noRes h.1 s hs
      · exact patNames_noRes h.2 s hs

theorem headNames_noRes {h : Op} (hh : noResHead h = true) : ∀ s ∈ headNames h, reserved s = false := by
  intro s hs
  cases h <;> simp [noResHead, headNames] at hh hs
  all_goals first
    | (subst hs; exact hh)
    | (rcases hs with rfl | rfl
       · exact hh.1
       · exact hh.2)

theorem uNames_noRes : ∀ {e : UExpr}, noReservedE e = true → ∀ s ∈ uNames e, reserved s = false := by
  intro e
  induction e with
  | let_ x h args e ih =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append] at hs
    rcases hs with hs | hs | hs | hs
    · exact argsNames_noRes hn.1.2 s hs
    · exact patNames_noRes hn.1.1.1 s hs
    · exact headNames_noRes hn.1.1.2 s hs
    · exact ih hn.2 s hs
  | split a p q e ih =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append] at hs
    rcases hs with hs | hs | hs | hs
    · exact argNames_noRes hn.1.1.1 s hs
    · exact patNames_noRes hn.1.1.2 s hs
    · exact patNames_noRes hn.1.2 s hs
    · exact ih hn.2 s hs
  | ifeq a b yes no ih1 ih2 =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append] at hs
    rcases hs with hs | hs | hs
    · exact argsNames_noRes (by simp [noResArgs, hn.1.1.1, hn.1.1.2]) s hs
    · exact ih1 hn.1.2 s hs
    · exact ih2 hn.2 s hs
  | cas acq rel w e v t ok fail ih1 ih2 =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append, List.mem_cons] at hs
    rcases hs with hs | hs | hs | hs
    · exact argsNames_noRes hn.1.1.1 s hs
    · subst hs; simpa using hn.1.1.2
    · exact ih1 hn.1.2 s hs
    · exact ih2 hn.2 s hs
  | casp acq rel w e0 e1 v0 v1 t ok fail ih1 ih2 =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append, List.mem_cons] at hs
    rcases hs with hs | hs | hs | hs
    · exact argsNames_noRes hn.1.1.1 s hs
    · subst hs; simpa using hn.1.1.2
    · exact ih1 hn.1.2 s hs
    · exact ih2 hn.2 s hs
  | ret a =>
    intro hn s hs
    simp only [noReservedE] at hn
    simp only [uNames, List.append_nil] at hs
    exact argNames_noRes hn s hs
  | tail f is a ts =>
    intro hn s hs
    simp only [noReservedE] at hn
    simp only [uNames, List.append_nil] at hs
    exact argNames_noRes hn s hs
  | unpack a i x e ih =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append, List.mem_cons] at hs
    rcases hs with hs | rfl | rfl | hs
    · exact argNames_noRes hn.1.1.1 s hs
    · simpa using hn.1.1.2
    · simpa using hn.1.2
    · exact ih hn.2 s hs
  | unpackT a i x e ih =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append, List.mem_cons] at hs
    rcases hs with hs | rfl | rfl | hs
    · exact argNames_noRes hn.1.1.1 s hs
    · simpa using hn.1.1.2
    · simpa using hn.1.2
    · exact ih hn.2 s hs
  | region a r p t e ih =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append, List.mem_cons] at hs
    rcases hs with hs | rfl | rfl | rfl | hs
    · exact argNames_noRes hn.1.1.1.1 s hs
    · simpa using hn.1.1.1.2
    · simpa using hn.1.1.2
    · simpa using hn.1.2
    · exact ih hn.2 s hs
  | openPub a r p t e ih =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append, List.mem_cons] at hs
    rcases hs with hs | rfl | rfl | rfl | hs
    · exact argNames_noRes hn.1.1.1.1 s hs
    · simpa using hn.1.1.1.2
    · simpa using hn.1.1.2
    · simpa using hn.1.2
    · exact ih hn.2 s hs
  | case a x e₁ y e₂ ih1 ih2 =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append, List.mem_cons] at hs
    rcases hs with hs | rfl | rfl | hs | hs
    · exact argNames_noRes hn.1.1.1.1 s hs
    · simpa using hn.1.1.1.2
    · simpa using hn.1.1.2
    · exact ih1 hn.1.2 s hs
    · exact ih2 hn.2 s hs
  | ifnull a e₁ x e₂ ih1 ih2 =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append, List.mem_cons] at hs
    rcases hs with hs | rfl | hs | hs
    · exact argNames_noRes hn.1.1.1 s hs
    · simpa using hn.1.1.2
    · exact ih1 hn.1.2 s hs
    · exact ih2 hn.2 s hs
  | parity a x e₁ e₂ ih1 ih2 =>
    intro hn s hs
    simp only [noReservedE, Bool.and_eq_true] at hn
    simp only [uNames, List.mem_append, List.mem_cons] at hs
    rcases hs with hs | rfl | hs | hs
    · exact argNames_noRes hn.1.1.1 s hs
    · simpa using hn.1.1.2
    · exact ih1 hn.1.2 s hs
    · exact ih2 hn.2 s hs

theorem hygE_of_noRes {e : UExpr} (h : noReservedE e = true) (n : Nat) : HygE n e :=
  fun s hs => okName_of_res (uNames_noRes h s hs)

/-! ## Focus and layers keep hygiene -/

mutual
theorem peelArg_names {t : String} : ∀ {a : UArg} {o : Op} {a' : UArg},
    peelArg (.var t) a = some (o, a') → ∀ s ∈ argNames a', s ∈ argNames a ∨ s = t
  | .at _, _, _, h => by simp [peelArg] at h
  | .op hd args, o, a', h => by
      simp only [peelArg] at h
      split at h
      · rename_i r hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro s hs
        simp only [argNames] at hs ⊢
        exact peelArgs_names hr s hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro s hs
        simp [argNames, atNames] at hs
        exact Or.inr hs
theorem peelArgs_names {t : String} : ∀ {as : List UArg} {o : Op} {as' : List UArg},
    peelArgs (.var t) as = some (o, as') → ∀ s ∈ argsNames as', s ∈ argsNames as ∨ s = t
  | [], _, _, h => by simp [peelArgs] at h
  | a :: rest, o, as', h => by
      simp only [peelArgs] at h
      split at h
      · rename_i r hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro s hs
        simp only [argsNames, List.mem_append] at hs ⊢
        rcases hs with hs | hs
        · rcases peelArg_names hr s hs with h1 | h1
          · exact Or.inl (Or.inl h1)
          · exact Or.inr h1
        · exact Or.inl (Or.inr hs)
      · cases hp : peelArgs (.var t) rest with
        | none => simp [hp] at h
        | some r =>
          simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          intro s hs
          simp only [argsNames, List.mem_append] at hs ⊢
          rcases hs with hs | hs
          · exact Or.inl (Or.inl hs)
          · rcases peelArgs_names hp s hs with h1 | h1
            · exact Or.inl (Or.inr h1)
            · exact Or.inr h1
end

theorem names_app {A A' B : List String} {t : String} (h : ∀ s ∈ A', s ∈ A ∨ s = t) :
    ∀ s ∈ A' ++ B, s ∈ A ++ B ∨ s = t := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases h s hs with h1 | h1
    · exact Or.inl (List.mem_append_left _ h1)
    · exact Or.inr h1
  · exact Or.inl (List.mem_append_right _ hs)

theorem focus_names {k : Nat} {e : UExpr} {o : Op} {e' : UExpr} (hf : focus (.var (tmp k)) e = some (o, e')) :
    ∀ s ∈ uNames e', s ∈ uNames e ∨ s = tmp k := by
  cases e with
  | ifeq a b yes no =>
    simp only [focus, Option.map_eq_some_iff] at hf
    obtain ⟨⟨o0, as'⟩, hr, hre⟩ := hf
    simp only [Prod.mk.injEq] at hre
    obtain ⟨rfl, rfl⟩ := hre
    have := getD_two (UArg.at .unit) ((peelArgs_length hr).trans rfl)
    simp only [uNames]
    rw [this]
    exact names_app (peelArgs_names hr)
  | cas acq rel w e v t ok fail =>
    simp only [focus, Option.map_eq_some_iff] at hf
    obtain ⟨⟨o0, as'⟩, hr, hre⟩ := hf
    simp only [Prod.mk.injEq] at hre
    obtain ⟨rfl, rfl⟩ := hre
    have := getD_three (UArg.at .unit) ((peelArgs_length hr).trans rfl)
    simp only [uNames]
    rw [this]
    exact names_app (peelArgs_names hr)
  | casp acq rel w e0 e1 v0 v1 t ok fail =>
    simp only [focus, Option.map_eq_some_iff] at hf
    obtain ⟨⟨o0, as'⟩, hr, hre⟩ := hf
    simp only [Prod.mk.injEq] at hre
    obtain ⟨rfl, rfl⟩ := hre
    have := getD_five (UArg.at .unit) ((peelArgs_length hr).trans rfl)
    simp only [uNames]
    rw [this]
    exact names_app (peelArgs_names hr)
  | let_ x h args e =>
    simp only [focus, Option.map_eq_some_iff] at hf
    obtain ⟨⟨o0, as'⟩, hr, hre⟩ := hf
    simp only [Prod.mk.injEq] at hre
    obtain ⟨rfl, rfl⟩ := hre
    exact names_app (peelArgs_names hr)
  | _ =>
    simp only [focus, Option.map_eq_some_iff] at hf
    obtain ⟨⟨o0, a'⟩, hr, hre⟩ := hf
    simp only [Prod.mk.injEq] at hre
    obtain ⟨rfl, rfl⟩ := hre
    exact names_app (peelArg_names hr)

theorem focus_hyg {k : Nat} {e : UExpr} {o : Op} {e' : UExpr} (he : HygE k e)
    (hf : focus (.var (tmp k)) e = some (o, e')) : HygE (k + 1) e' := by
  intro s hs
  rcases focus_names hf s hs with h1 | h1
  · exact okName_mono (he s h1) (Nat.le_succ k)
  · subst h1; exact okName_tmp (Nat.lt_succ_self k)

theorem patBinder_ok {k : Nat} {p : UPat} (hp : ∀ s ∈ patNames p, okName k s) :
    k ≤ (patBinder p k).2 ∧ okName (patBinder p k).2 (patBinder p k).1 := by
  cases p with
  | bind x =>
    cases x with
    | none => exact ⟨Nat.le_succ k, okName_tmp (Nat.lt_succ_self k)⟩
    | some y => exact ⟨Nat.le_refl k, hp y (by simp [patNames])⟩
  | pair p q => exact ⟨Nat.le_succ k, okName_tmp (Nat.lt_succ_self k)⟩

theorem wrap_hyg {j : Nat} {b : String} {p : UPat} {E : UExpr} (hb : okName j b)
    (hp : ∀ s ∈ patNames p, okName j s) (hE : HygE j E) : HygE j (wrap b p E) := by
  cases p with
  | bind x => exact hE
  | pair p q =>
    intro s hs
    simp only [wrap, uNames, argNames, atNames, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    rcases hs with rfl | hs | hs | hs
    · exact hb
    · exact hp s (by simp [patNames, hs])
    · exact hp s (by simp [patNames, hs])
    · exact hE s hs

/-- A `let` layer of a hygienic term: its binder and continuation are hygienic at the new counter. -/
theorem layer_letOp_hyg {k : Nat} {e : UExpr} {x : String} {o : Op} {j : Nat} {e' : UExpr} (he : HygE k e)
    (hl : layer k e = .letOp x o j e') : k ≤ j ∧ okName j x ∧ HygE j e' := by
  unfold layer at hl
  split at hl
  · rename_i r hr
    simp only [ULayer.letOp.injEq] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨Nat.le_succ k, okName_tmp (Nat.lt_succ_self k), focus_hyg he hr⟩
  · cases e <;> simp only [headLayer, reduceCtorEq, ULayer.letOp.injEq] at hl
    rename_i xo h args e0 _
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    simp only [HygE, uNames, List.mem_append, or_imp, forall_and] at he
    have hb := patBinder_ok (p := .bind xo) he.2.1
    exact ⟨hb.1, hb.2, fun s hs => okName_mono (he.2.2.2 s hs) hb.1⟩

theorem getD_hyg {j : Nat} {d : UExpr} (hd : HygE j d) :
    ∀ (l : List UExpr) (i : Nat), (∀ c ∈ l, HygE j c) → HygE j (l.getD i d)
  | [], _, _ => by simpa using hd
  | c :: l, 0, h => by simpa using h c (by simp)
  | c :: l, i + 1, h => by
      simpa using getD_hyg hd l i (fun c' hc' => h c' (by simp [hc']))

theorem hygE_unit (j : Nat) : HygE j (.ret (.at .unit)) := by
  intro s hs; simp [uNames, argNames, atNames] at hs

theorem pickU_hyg {j : Nat} {conts : List UExpr} (h : ∀ c ∈ conts, HygE j c) (t : Expr) :
    HygE j (pickU conts t) := by
  unfold pickU
  split
  · split
    · exact getD_hyg (hygE_unit j) conts 1 h
    · exact getD_hyg (hygE_unit j) conts 0 h
  · exact getD_hyg (hygE_unit j) conts 0 h

/-- A head layer of a hygienic term: its binders and continuations are hygienic at the new counter. -/
theorem layer_head_hyg {k : Nat} {e : UExpr} {h : Expr} {conts : List UExpr} {j : Nat} (he : HygE k e)
    (hl : layer k e = .head h conts j) :
    k ≤ j ∧ (∀ b ∈ binders h, okName j b) ∧ ∀ c ∈ conts, HygE j c := by
  unfold layer at hl
  split at hl
  · simp at hl
  · cases e <;> simp only [headLayer, reduceCtorEq, ULayer.head.injEq] at hl
    case split a p q e0 _ =>
      obtain ⟨rfl, rfl, rfl⟩ := hl
      simp only [HygE, uNames, List.mem_append, or_imp, forall_and] at he
      have h1 := patBinder_ok he.2.1
      have h2 := patBinder_ok (p := q) (k := (patBinder p k).2) (fun s hs => okName_mono (he.2.2.1 s hs) h1.1)
      have hkj := Nat.le_trans h1.1 h2.1
      refine ⟨hkj, ?_, ?_⟩
      · intro b hb
        simp only [binders, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact okName_mono h1.2 h2.1
        · exact h2.2
      · intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        refine wrap_hyg (okName_mono h1.2 h2.1) (fun s hs => okName_mono (he.2.1 s hs) hkj) ?_
        exact wrap_hyg h2.2 (fun s hs => okName_mono (he.2.2.1 s hs) hkj)
          (fun s hs => okName_mono (he.2.2.2 s hs) hkj)
    all_goals
      obtain ⟨rfl, rfl, rfl⟩ := hl
      refine ⟨Nat.le_refl _, ?_, ?_⟩
      all_goals
        simp only [HygE, uNames, List.mem_append, List.mem_cons, or_imp, forall_and, forall_eq] at he
        simp_all [binders, HygE]

/-! ## Threads -/

/-- A stack frame: body, return binder and saved environment hygienic at the frame's counter. -/
def FrOk (f : UFrame) : Prop := HygE f.ctr f.body ∧ okName f.ctr f.x ∧ ∀ y ∈ f.env, okName f.ctr y.1

/-- **The thread invariant**: term and environment keys hygienic at the thread's counter, every frame `FrOk`. -/
def ThInv (th : UTTh) : Prop :=
  HygE th.ctr th.term ∧ (∀ y ∈ th.env, okName th.ctr y.1) ∧ ∀ f ∈ th.stack, FrOk f

theorem thInv_back {th : UTTh} {t : TTh} {e : UExpr} {j : Nat} (hth : ThInv th) (hj : th.ctr ≤ j)
    (he : HygE j e) (henv : ∀ y ∈ t.env, okName j y.1 ∨ y ∈ th.env) : ThInv (backTh th t e j) := by
  refine ⟨he, ?_, hth.2.2⟩
  intro y hy
  rcases henv y hy with h1 | h1
  · exact h1
  · exact okName_mono (hth.2.1 y h1) hj

theorem uEnter_inv {U : UProg} (hU : noReserved U = true) {th th' : UTTh} {f : String} {ts : List Ty} {a : At}
    (hst : ∀ fr ∈ th.stack, FrOk fr) (h : uEnter U th f ts a = some th') : ThInv th' := by
  unfold uEnter at h
  cases hd : U.find? (·.name == f) with
  | none => simp [hd] at h
  | some d =>
    cases hw : evalAt th.env a with
    | none => simp [hd, hw] at h
    | some w =>
      simp only [hd, hw, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      subst h
      have hdU := (List.all_eq_true.mp hU) d (List.mem_of_find?_eq_some hd)
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hdU
      refine ⟨hygE_of_noRes hdU.2 0, ?_, hst⟩
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      exact okName_of_res hdU.1

theorem uCallFrame_ok {U : UProg} {th : UTTh} {f : String} {ts : List Ty} {x : String} {e : UExpr} {j : Nat}
    {fr : UFrame} (hth : ThInv th) (hj : th.ctr ≤ j) (hx : okName j x) (he : HygE j e)
    (h : uCallFrame U th f ts x e j = some fr) : FrOk fr := by
  unfold uCallFrame at h
  cases hd : U.find? (·.name == f) with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨he, hx, fun y hy => okName_mono (hth.2.1 y hy) hj⟩

/-- **`ustep` keeps the thread invariant** (for a program with no reserved user name). -/
theorem ustep_inv {U : UProg} (hU : noReserved U = true) {g : G} {mem : Memory} {pairs : List Ts} {th : UTTh}
    {r : Memory × List Ts × UTTh} (hth : ThInv th) (hr : r ∈ ustep U g mem pairs th) : ThInv r.2.2 := by
  unfold ustep at hr
  split at hr
  · -- call
    rename_i x f is a ts j e heq
    obtain ⟨hkj, hx, he⟩ := layer_letOp_hyg hth.1 heq
    cases hfr : uCallFrame U th f ts x e j with
    | none => simp [hfr, ol] at hr
    | some fr =>
      have hok := uCallFrame_ok hth hkj hx he hfr
      cases hen : uEnter U { th with stack := fr :: th.stack } f ts a with
      | none => simp [hfr, hen, ol] at hr
      | some th' =>
        simp only [hfr, hen, Option.bind_some, Option.map_some, ol, Option.toList_some, List.mem_singleton] at hr
        subst hr
        refine uEnter_inv hU ?_ hen
        intro f' hf'
        simp only [List.mem_cons] at hf'
        rcases hf' with rfl | hf'
        · exact hok
        · exact hth.2.2 f' hf'
  · -- callc
    rename_i x f a j e heq
    obtain ⟨hkj, hx, he⟩ := layer_letOp_hyg hth.1 heq
    split at hr
    · split at hr
      · split at hr
        · rename_i _ tf _ _ _ _ _ _ d _
          cases hfr : uCallFrame U th d.name [] x e j with
          | none => simp [hfr, ol] at hr
          | some fr =>
            have hok := uCallFrame_ok hth hkj hx he hfr
            cases hen : uEnter U { th with stack := { fr with ty := retOf tf fr.ty } :: th.stack } d.name [] a with
            | none => simp [hfr, hen, ol] at hr
            | some th' =>
              simp only [hfr, hen, Option.bind_some, Option.map_some, ol, Option.toList_some,
                List.mem_singleton] at hr
              subst hr
              refine uEnter_inv hU ?_ hen
              intro f' hf'
              simp only [List.mem_cons] at hf'
              rcases hf' with rfl | hf'
              · exact hok
              · exact hth.2.2 f' hf'
        · simp at hr
      · simp at hr
    · simp at hr
  · -- other let: the sentinel `tstep`
    rename_i x o j e h1 h2 heq
    obtain ⟨hkj, hx, he⟩ := layer_letOp_hyg hth.1 heq
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    have hcv : coreView th (.let_ x o S0) = { toCoreTh th with term := .let_ x o S0, stack := [] } := rfl
    rw [hcv] at hr0
    have henv := tstep_head_env (.let_ x o S0) (notCall_of h1 h2) (toCoreTh th) hr0
    refine thInv_back hth hkj he ?_
    intro y hy
    rcases henv y hy with h3 | h3
    · simp only [binders, List.mem_cons, List.not_mem_nil, or_false] at h3
      exact Or.inl (h3 ▸ hx)
    · exact Or.inr h3
  · -- head: the sentinel `tstep`
    rename_i h conts j heq
    obtain ⟨hkj, hb, hc⟩ := layer_head_hyg hth.1 heq
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    have hcv : coreView th h = { toCoreTh th with term := h, stack := [] } := rfl
    rw [hcv] at hr0
    have henv := tstep_head_env h (layer_head heq) (toCoreTh th) hr0
    refine thInv_back hth hkj (pickU_hyg hc _) ?_
    intro y hy
    rcases henv y hy with h3 | h3
    · exact Or.inl (hb _ h3)
    · exact Or.inr h3
  · -- ret
    split at hr
    · rename_i f rest _ ws heq2 _
      simp only [List.mem_singleton] at hr
      subst hr
      have hst := hth.2.2
      rw [heq2] at hst
      obtain ⟨hb, hx, henv⟩ := hst f (by simp)
      refine ⟨hb, ?_, fun f' hf' => hst f' (by simp [hf'])⟩
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact henv y hy
    · simp at hr
  · -- tail
    rename_i f is a ts heq
    cases hen : uEnter U th f ts a with
    | none => simp [hen, ol] at hr
    | some th' =>
      simp only [hen, Option.map_some, ol, Option.toList_some, List.mem_singleton] at hr
      subst hr
      exact uEnter_inv hU hth.2.2 hen

/-! ## Configurations -/

/-- **The configuration invariant**: no reserved user name in `U`, and every thread satisfies `ThInv`. -/
def UInv (U : UProg) (c : UCfg) : Prop :=
  noReserved U = true ∧ ∀ (i : Nat) (th : UTTh), c.ths[i]? = some th → ThInv th

theorem get_set! {α : Type} {a : Array α} {i j : Nat} {v t : α} (h : (a.set! i v)[j]? = some t) :
    a[j]? = some t ∨ t = v := by
  simp only [Array.set!, Array.getElem?_setIfInBounds] at h
  split at h
  · split at h
    · exact Or.inr (Option.some.inj h).symm
    · simp at h
  · exact Or.inl h

theorem get_set!_self {α : Type} (a : Array α) (i : Nat) (v d : α) :
    ((a.set! i v)[i]?).getD d = if i < a.size then v else d := by
  by_cases hi : i < a.size
  · simp [Array.set!, Array.getElem?_setIfInBounds, hi]
  · simp [Array.set!, Array.getElem?_setIfInBounds, hi]

theorem get_push {α : Type} {a : Array α} {j : Nat} {v t : α} (h : (a.push v)[j]? = some t) :
    a[j]? = some t ∨ t = v := by
  simp only [Array.getElem?_push] at h
  split at h
  · exact Or.inr (Option.some.inj h).symm
  · exact Or.inl h

theorem uInv_set {U : UProg} {c : UCfg} {i : Nat} {th : UTTh} (hc : UInv U c) (hth : ThInv th)
    (ths : Array UTTh) (hths : ths = c.ths.set! i th) : ∀ (j : Nat) (t : UTTh), ths[j]? = some t → ThInv t := by
  subst hths
  intro j t ht
  rcases get_set! ht with h1 | h1
  · exact hc.2 j t h1
  · exact h1 ▸ hth

theorem uThreadSteps_inv {U : UProg} {k : Promises.Knobs} {arch : Arch} {c c' : UCfg} {i : Nat}
    (hc : UInv U c) (h : c' ∈ uThreadSteps U k arch c i) : UInv U c' := by
  unfold uThreadSteps at h
  cases hth : c.ths[i]? with
  | none => simp [hth] at h
  | some th =>
    simp only [hth, List.mem_map] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact ⟨hc.1, uInv_set hc (ustep_inv hc.1 (hc.2 i th hth) hr) _ rfl⟩

theorem uPromise_inv {U : UProg} {c : UCfg} {i : Nat} (a : Address) (v : Val) (w : Ts) (hc : UInv U c) :
    UInv U (uPromise c i a v w) := by
  unfold uPromise
  cases hth : c.ths[i]? with
  | none => exact hc
  | some th =>
    refine ⟨hc.1, ?_⟩
    dsimp only
    refine uInv_set hc ?_ _ rfl
    exact hc.2 i th hth

theorem extCfg_env (C : Cfg) (i : Nat) (T : TTh) (x : String) (n : ExtName) (e : Expr) (ws rs : List Word) :
    ∀ y ∈ ((extCfg C i T x n e ws rs).ths[i]?.getD T).env, y.1 = x ∨ y ∈ T.env := by
  have key : ∀ (ths : Array TTh) (v : TTh), (∀ y ∈ v.env, y.1 = x ∨ y ∈ T.env) →
      ∀ y ∈ ((ths.set! i v)[i]?.getD T).env, y.1 = x ∨ y ∈ T.env := by
    intro ths v hv y hy
    rw [get_set!_self] at hy
    split at hy
    · exact hv y hy
    · exact Or.inr hy
  have cons : ∀ (v : TTh) (t : Ty) (ws' : List Word), v.env = (x, t, ws') :: T.env →
      ∀ y ∈ v.env, y.1 = x ∨ y ∈ T.env := by
    intro v t ws' hv y hy
    rw [hv] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Or.inl rfl
    · exact Or.inr hy
  unfold extCfg
  split
  · unfold curCfg
    split
    · exact key _ _ (cons _ _ _ rfl)
    · exact key _ _ (cons _ _ _ rfl)
  · exact key _ _ (cons _ _ _ rfl)

theorem uExtCfg_inv {U : UProg} {c : UCfg} {i : Nat} {th : UTTh} {x : String} {o : Op} {n : ExtName}
    {j : Nat} {e : UExpr} (ws rs : List Word) (hc : UInv U c) (hth : c.ths[i]? = some th)
    (hl : layer th.ctr th.term = .letOp x o j e) : UInv U (uExtCfg c i th x n e j ws rs) := by
  have ht := hc.2 i th hth
  obtain ⟨hkj, hx, he⟩ := layer_letOp_hyg ht.1 hl
  refine ⟨hc.1, uInv_set hc (thInv_back ht hkj he ?_) _ rfl⟩
  intro y hy
  rcases extCfg_env _ _ _ _ _ _ _ _ y hy with h1 | h1
  · left; rw [h1]; exact hx
  · exact Or.inr h1

theorem uExtSteps_inv {U : UProg} {c c' : UCfg} {i : Nat} (hc : UInv U c) (h : c' ∈ uExtSteps c i) :
    UInv U c' := by
  unfold uExtSteps at h
  split at h
  · rename_i th hth
    split at h
    · rename_i x n a j e hl
      split at h
      · simp at h
      · split at h
        · obtain ⟨rs, -, rfl⟩ := List.mem_map.mp h
          exact uExtCfg_inv _ _ hc hth hl
        · simp at h
    · simp at h
  · simp at h

theorem uSpawnCfg_inv {U : UProg} {c : UCfg} {i : Nat} {th : UTTh} {x : String} {o : Op} {j : Nat} {e : UExpr}
    (f : String) (ts : List Ty) (T : Ty) (ws : List Word) (hc : UInv U c) (hth : c.ths[i]? = some th)
    (hl : layer th.ctr th.term = .letOp x o j e) : UInv U (uSpawnCfg c i th x e j f ts T ws) := by
  have ht := hc.2 i th hth
  obtain ⟨hkj, hx, he⟩ := layer_letOp_hyg ht.1 hl
  refine ⟨hc.1, ?_⟩
  intro i' t h'
  simp only [uSpawnCfg] at h'
  rcases get_push h' with h1 | h1
  · refine uInv_set hc (thInv_back ht hkj he ?_) _ rfl i' t h1
    intro y hy
    simp only [spawnPar, withS, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Or.inl hx
    · exact Or.inr hy
  · subst h1
    have ha : okName 0 "a" := okName_of_res (by simp [reserved])
    refine ⟨?_, ?_, ?_⟩
    · intro s hs
      simp [fromCore0, uNames, argNames, atNames] at hs
      subst hs; exact ha
    · intro y hy
      simp only [fromCore0, spawnKid, List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy; exact ha
    · intro f' hf'
      simp [fromCore0] at hf'

theorem USolo.inv {U : UProg} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : UCfg}
    (h : USolo U k arch i c c') (hc : UInv U c) : UInv U c' := by
  induction h with
  | refl => exact hc
  | thread h1 _ ih => exact ih (uThreadSteps_inv hc h1)
  | prom a v w _ _ ih => exact ih (uPromise_inv a v w hc)
  | ext h1 _ ih => exact ih (uExtSteps_inv hc h1)

theorem UStep.inv {U : UProg} {k : Promises.Knobs} {arch : Arch} {c c' : UCfg}
    (h : UStep U k arch c c') (hc : UInv U c) : UInv U c' := by
  cases h with
  | thread i h1 _ => exact uThreadSteps_inv hc h1
  | prom i a v w _ _ _ => exact uPromise_inv a v w hc

theorem USpawn.inv {U : UProg} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : UCfg}
    (h : USpawn U k arch cap c c') (hc : UInv U c) : UInv U c' := by
  cases h with
  | mk i x f a T ts j e th rt ws hth hl _ _ _ => exact uSpawnCfg_inv f ts T ws hc hth hl

theorem UExt.inv {U : UProg} {k : Promises.Knobs} {arch : Arch} {c c' : UCfg}
    (h : UExt U k arch c c') (hc : UInv U c) : UInv U c' := by
  cases h with
  | mk i x n a j e th rt ws rs hth hl _ _ _ _ =>
    have h1 : UInv U (uExtCfg c i th x n e j ws rs) := uExtCfg_inv ws rs hc hth hl
    refine ⟨h1.1, fun i' t ht => ?_⟩
    rcases uWake_get (uExtCfg c i th x n e j ws rs) i (relView th.vs) n ws i' with h' | ⟨t0, _, h2, h3⟩
    · rw [h'] at ht; exact h1.2 i' t ht
    · rw [h3] at ht; obtain rfl := Option.some.inj ht; exact h1.2 i' t0 h2

theorem StepsGU.inv {U : UProg} {k : Promises.Knobs} {arch : Arch} {Sp : UCfg → UCfg → Prop}
    (hSp : ∀ {c c'}, Sp c c' → UInv U c → UInv U c') {c c' : UCfg}
    (h : StepsGU U k arch Sp c c') (hc : UInv U c) : UInv U c' := by
  induction h with
  | refl => exact hc
  | step h1 _ ih =>
    rcases h1 with h1 | h1
    · exact ih (h1.inv hc)
    · exact ih (hSp h1 hc)

/-- **`UInv` along runs** of machine, spawn and extern steps. -/
theorem StepsU.inv {U : UProg} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : UCfg}
    (h : StepsU U k arch cap c c') (hc : UInv U c) : UInv U c' :=
  StepsGU.inv (fun h1 hc1 => h1.elim (fun h2 => h2.inv hc1) (fun h2 => h2.inv hc1)) h hc

/-! ## The wrapper start -/

/-- **The U wrapper start**: the core wrapper term (embedded), `a : Unit`, counter 0. -/
def startU (U : UProg) (cap : Nat) : UCfg :=
  { mem := #[], ths := #[{ term := embed (wrapTerm (mainRet (elabProg U))), env := [("a", .unit, [])] }],
    cap := cap }

theorem toCoreCfg_startU (U : UProg) (cap : Nat) : toCoreCfg (startU U cap) = startW (elabProg U) cap := by
  simp [toCoreCfg, startU, startW, wrapTh, toCoreTh, elabT_embed]

theorem noRes_wrap (rt : Option Ty) : noReservedE (embed (wrapTerm rt)) = true := by
  cases rt with
  | none =>
    simp [wrapTerm, exitTail, embed, noReservedE, noResPat, noResHead, noResArgs, noResArg, okAt,
      TermScope.opAts, reserved]
  | some t =>
    simp only [wrapTerm, exitTail]
    split
    · simp [embed, noReservedE, noResPat, noResHead, noResArgs, noResArg, okAt, TermScope.opAts, reserved]
    · split
      · simp [embed, noReservedE, noResPat, noResHead, noResArgs, noResArg, okAt, TermScope.opAts, reserved]
      · simp [embed, noReservedE, noResPat, noResHead, noResArgs, noResArg, okAt, TermScope.opAts, reserved]

theorem uInv_start {U : UProg} (hU : noReserved U = true) (cap : Nat) : UInv U (startU U cap) := by
  refine ⟨hU, ?_⟩
  intro i th h
  simp only [startU] at h
  rcases i with _ | i
  · simp at h
    subst h
    refine ⟨hygE_of_noRes (noRes_wrap _) 0, ?_, fun f hf => by simp at hf⟩
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    exact okName_of_res (by simp [reserved])
  · simp at h

/-- **Every configuration reachable from the U wrapper start satisfies `UInv`** (no reserved user name). -/
theorem uInv_reach {U : UProg} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c : UCfg}
    (hU : noReserved U = true) (h : StepsU U k arch cap (startU U cap) c) : UInv U c :=
  h.inv (uInv_start hU cap)

end UnElab

#print axioms UnElab.hygE_of_noRes
#print axioms UnElab.layer_letOp_hyg
#print axioms UnElab.layer_head_hyg
#print axioms UnElab.ustep_inv
#print axioms UnElab.StepsU.inv
#print axioms UnElab.toCoreCfg_startU
#print axioms UnElab.uInv_start
#print axioms UnElab.uInv_reach
