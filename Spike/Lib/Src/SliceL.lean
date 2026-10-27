import Spike.Lib.Src.HeapBuf

/-!
**Slices in the source environment** (ISA-neutral), from `countsOk2`.
`countsOk2` asks that every pair whose left part is a locative pairs a buffer
of `bufs` with a value known to be its count (`pairOk`). In the source, the
pair's words are then the buffer's locative and that count as a number, and
the buffer's first `count` cells have messages (`SBufs`). `SliceL` records
this fact at every pair of a binding's layout whose left part is a locative,
so that the output extern's operand (`ownSliceTy`, a locative paired with its
count) reads its buffer's cells (`print_arg_slAt`).

- `SlAt P ws`, `SlP L sm`: a locative word paired with a number word, the
  pair satisfying `P` (for `SlP`: a label of `L` with `m` cells);
- `SliceL P V ws`: `SlAt` at every `.node .loc _` of layout `V`; `.mono`,
  `.of_erase`, `.pair`;
- `EnvSl P lits env`: every binding of the walk is `SliceL` at its layout;
  `.cons`, `.mono`, `.evalAt`, `.split`, `.splitLeaf`;
- `SCs env cs`: every known value of `countsB`'s `cs` is bound to its number;
  `.cons`, `.constOf`, `.after`;
- `sliceL_pairOp`: a `pairOk` pair;
- `countsB_let`, `_split`, `_unpack`, `_ifeq`, `countsOk2_decl`: `countsOk2`
  at a block and through its body;
- `envSl_entry`, `envSl_call`, `envSl_ret`: across calls and returns that
  pass `callsOk2`;
- `print_arg_slAt`: the extern's operand;
- `LabelsIn sm L B`: `L`'s labels and every message's below `B`; `.push`,
  `.fresh` (the next label fresh and outside `L`), `.allocBuf` (one
  thread's allocation moves `B` to the next label).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (LitV litAt unbuf constOf bindC pairOk csAfter bufsAfter countsB countsOk2 opLit shapeOf
  params2 isPrintExt hasPrint)

/-! ## Slices -/

/-- **A slice's words**: the first a locative at offset 0 of label `l`, the
second the number `m`, and `P l m`. -/
def SlAt (P : WeakMem.AllocLabel → Nat → Prop) (ws : List TermRun.Word) : Prop :=
  ∃ l m, ws[0]?.map (·.val) = some (.loc ⟨l, 0⟩ 0) ∧ ws[1]?.map (·.val) = some (.num m) ∧ P l m

/-- **A buffer with its count**: a label of `L` whose first `m` cells have
messages in `sm`, the count below `2^28` (a buffer's count bound). -/
def SlP (L : WeakMem.AllocLabel → Prop) (sm : WeakMem.Memory) (l : WeakMem.AllocLabel) (m : Nat) : Prop :=
  L l ∧ (∀ i < m, HasCell sm ⟨l, i⟩) ∧ m < 2 ^ 28

theorem SlP.mono {L L' : WeakMem.AllocLabel → Prop} {sm sm' : WeakMem.Memory} (hL : ∀ l, L l → L' l)
    (hm : ∀ sa, HasCell sm sa → HasCell sm' sa) {l : WeakMem.AllocLabel} {m : Nat} (h : SlP L sm l m) :
    SlP L' sm' l m :=
  ⟨hL _ h.1, fun i hi => hm _ (h.2.1 i hi), h.2.2⟩

/-- **The slices of a layout**: at every pair whose left part is a locative,
the words from there are `SlAt P`. -/
def SliceL (P : WeakMem.AllocLabel → Nat → Prop) : LitV → List TermRun.Word → Prop
  | .node l r, ws => (l = .loc → SlAt P ws) ∧ SliceL P l (ws.take l.words.length) ∧
      SliceL P r (ws.drop l.words.length)
  | _, _ => True

namespace SliceL

variable {P : WeakMem.AllocLabel → Nat → Prop}

theorem nil (ws : List TermRun.Word) : SliceL P .nil ws := trivial
theorem leaf (o : Option Nat) (ws : List TermRun.Word) : SliceL P (.leaf o) ws := trivial
theorem loc (ws : List TermRun.Word) : SliceL P .loc ws := trivial

theorem mono {P' : WeakMem.AllocLabel → Nat → Prop} (hP : ∀ l m, P l m → P' l m) :
    ∀ {V : LitV} {ws : List TermRun.Word}, SliceL P V ws → SliceL P' V ws
  | .nil, _, _ | .leaf _, _, _ | .loc, _, _ => trivial
  | .node _ _, _, ⟨h0, hl, hr⟩ =>
    ⟨fun he => let ⟨l, m, h1, h2, h3⟩ := h0 he; ⟨l, m, h1, h2, hP _ _ h3⟩, mono hP hl, mono hP hr⟩

theorem words_erase : ∀ V : LitV, V.erase.words.length = V.words.length
  | .nil | .leaf _ | .loc => rfl
  | .node l r => by simp [LitV.erase, LitV.words, words_erase l, words_erase r]

theorem eq_loc_of_erase : ∀ {V : LitV}, V.erase = .loc → V = .loc
  | .loc, _ => rfl
  | .nil, h | .leaf _, h | .node _ _, h => by simp [LitV.erase] at h

/-- **Literals do not change the slices** (across a call or a return that
passes `callsOk2`). -/
theorem of_erase : ∀ {V M : LitV} {ws : List TermRun.Word}, SliceL P V ws → V.erase = M → SliceL P M ws
  | .nil, _, _, _, he | .leaf _, _, _, _, he | .loc, _, _, _, he => by subst he; trivial
  | .node l r, _, _, ⟨h0, hl, hr⟩, he => by
    subst he
    refine ⟨fun hx => h0 (eq_loc_of_erase hx), ?_, ?_⟩
    · rw [words_erase]; exact of_erase hl rfl
    · rw [words_erase]; exact of_erase hr rfl

/-- **A pair's slices**: its parts', and its own if its left part is a
locative. -/
theorem pair {la lb : LitV} {wa wb : List TermRun.Word} (ha : SliceL P la wa) (hb : SliceL P lb wb)
    (hl : wa.length = la.words.length) (h0 : la = .loc → SlAt P (wa ++ wb)) :
    SliceL P (.node la lb) (wa ++ wb) := by
  refine ⟨h0, ?_, ?_⟩
  · rw [← hl, List.take_left]; exact ha
  · rw [← hl, List.drop_left]; exact hb

end SliceL

/-! ## Environments -/

/-- **Every binding of the walk has its layout's slices** in the source's
environment. -/
def EnvSl (P : WeakMem.AllocLabel → Nat → Prop) (lits : List (String × LitV)) (env : TermRun.Env) : Prop :=
  ∀ x V, lits.lookup x = some V → ∃ t ws, TermRun.lookupE env x = some (t, ws) ∧ SliceL P V ws

namespace EnvSl

variable {P : WeakMem.AllocLabel → Nat → Prop}

theorem nil (env : TermRun.Env) : EnvSl P [] env := fun _ _ h => by cases h

theorem cons {lits : List (String × LitV)} {env : TermRun.Env} (h : EnvSl P lits env) {x : String} {V : LitV}
    {t : Ty} {ws : List TermRun.Word} (hs : SliceL P V ws) : EnvSl P ((x, V) :: lits) ((x, t, ws) :: env) := by
  intro y M hy
  rw [lookup_cons_name] at hy
  rw [lookupE_cons]
  split at hy
  · cases hy; rename_i hyx; exact ⟨t, ws, by simp [hyx], hs⟩
  · rename_i hyx; simp only [hyx, ite_false]; exact h y M hy

theorem mono {P' : WeakMem.AllocLabel → Nat → Prop} {lits : List (String × LitV)} {env : TermRun.Env}
    (h : EnvSl P lits env) (hP : ∀ l m, P l m → P' l m) : EnvSl P' lits env := fun x V hx =>
  let ⟨t, ws, he, hs⟩ := h x V hx
  ⟨t, ws, he, hs.mono hP⟩

/-- **An atom's words have its layout's slices** (an unbound variable's
layout, a literal's and `()`'s have none). -/
theorem evalAt {lits : List (String × LitV)} {env : TermRun.Env} (h : EnvSl P lits env) {a : At} {t : Ty}
    {ws : List TermRun.Word} (he : TermRun.evalAt env a = some (t, ws)) : SliceL P (litAt lits a) ws := by
  cases a with
  | var x =>
    cases hL : lits.lookup x with
    | none => simp only [litAt, hL, Option.getD_none]; trivial
    | some V =>
      obtain ⟨t0, ws0, he0, hs⟩ := h x V hL
      simp only [TermRun.evalAt, he0, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      simpa only [litAt, hL, Option.getD_some] using hs
  | lit _ => trivial
  | unit => trivial

/-- **`let (x, y) = a`** of a pair layout: the parts' slices. -/
theorem split {lits : List (String × LitV)} {env : TermRun.Env} (h : EnvSl P lits env) {a : At} {t u v : Ty}
    {ws : List TermRun.Word} {l r : LitV} {k : Nat} {x y : String} (he : TermRun.evalAt env a = some (t, ws))
    (hl : litAt lits a = .node l r) (hk : k = l.words.length) :
    EnvSl P ((y, r) :: (x, l) :: lits) ((y, v, ws.drop k) :: (x, u, ws.take k) :: env) := by
  have hs := h.evalAt he
  rw [hl] at hs
  subst hk
  exact (h.cons hs.2.1).cons hs.2.2

/-- **`let (x, y) = a`** of another layout: the walk binds leaves. -/
theorem splitLeaf {lits : List (String × LitV)} {env : TermRun.Env} (h : EnvSl P lits env) {u v : Ty}
    {w1 w2 : List TermRun.Word} {x y : String} :
    EnvSl P ((y, .leaf none) :: (x, .leaf none) :: lits) ((y, v, w2) :: (x, u, w1) :: env) :=
  (h.cons (SliceL.leaf _ _)).cons (SliceL.leaf _ _)

end EnvSl

/-! ## Known values -/

/-- **`countsB`'s known values in the source**: each `y` of `cs` with value
`k` is bound to one word, the number `k`. -/
def SCs (env : TermRun.Env) (cs : List (String × Nat)) : Prop :=
  ∀ y k, cs.lookup y = some k → ∃ t w, TermRun.lookupE env y = some (t, [w]) ∧ w.val = .num k

namespace SCs

theorem nil (env : TermRun.Env) : SCs env [] := fun _ _ h => by cases h

/-- **Another binding keeps the known values** that it does not shadow. -/
theorem cons {env : TermRun.Env} {cs : List (String × Nat)} (h : SCs env cs) (x : String) (t : Ty)
    (ws : List TermRun.Word) : SCs ((x, t, ws) :: env) (unbuf x cs) := by
  intro y k hy
  rw [lookup_unbuf] at hy
  split at hy
  · cases hy
  · rename_i hyx
    obtain ⟨t', w, he, hw⟩ := h y k hy
    exact ⟨t', w, by rw [lookupE_cons]; simp only [hyx, ↓reduceIte]; exact he, hw⟩

/-- **A known atom is one word, its number.** -/
theorem constOf {env : TermRun.Env} {cs : List (String × Nat)} (h : SCs env cs) {a : At} {k : Nat} {t : Ty}
    {ws : List TermRun.Word} (hc : Scc.Lower.constOf cs a = some k) (he : TermRun.evalAt env a = some (t, ws)) :
    ∃ w, ws = [w] ∧ w.val = .num k := by
  cases a with
  | var y =>
    obtain ⟨t', w, hl, hw⟩ := h y k hc
    simp only [TermRun.evalAt, hl, Option.some.injEq, Prod.mk.injEq] at he
    exact ⟨w, he.2.symm, hw⟩
  | lit n =>
    simp only [Scc.Lower.constOf, Option.some.injEq] at hc
    subst hc
    simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at he
    exact ⟨_, he.2.symm, rfl⟩
  | unit => simp [Scc.Lower.constOf] at hc

/-- **The known values after `let x = op`** (`csAfter`): an atom or a
`nameI` binds `x` to its operand's words. -/
theorem after {env : TermRun.Env} {cs : List (String × Nat)} (h : SCs env cs) (x : String) (op : Op) (t : Ty)
    (ws : List TermRun.Word) (hop : ∀ a, (op = .atom a ∨ op = .nameI a) → ∃ t', TermRun.evalAt env a = some (t', ws)) :
    SCs ((x, t, ws) :: env) (csAfter x cs op) := by
  have hb : ∀ a, (∃ t', TermRun.evalAt env a = some (t', ws)) →
      SCs ((x, t, ws) :: env) (bindC x (Scc.Lower.constOf cs a) cs) := by
    intro a ⟨t', he⟩
    cases hk : Scc.Lower.constOf cs a with
    | none => exact h.cons x t ws
    | some k =>
      obtain ⟨w, rfl, hw⟩ := h.constOf hk he
      intro y k' hy
      simp only [bindC, lookup_cons_name] at hy
      split at hy
      · cases hy; rename_i hyx; exact ⟨t, w, by rw [lookupE_cons]; simp [hyx], hw⟩
      · exact h.cons x t [w] y k' hy
  cases op with
  | atom a => exact hb a (hop a (Or.inl rfl))
  | nameI a => exact hb a (hop a (Or.inr rfl))
  | _ => exact h.cons x t ws

end SCs

/-! ## A `pairOk` pair -/

/-- **A pair that passes `pairOk`, its left part a locative**: a buffer of
`bufs` and its known count, so its words are a slice of that buffer. -/
theorem slAt_of_pairOk {cs bufs : List (String × Nat)} {lits : List (String × LitV)} {env : TermRun.Env}
    {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} {a b : At} {ta tb : Ty}
    {wa wb : List TermRun.Word}
    (hp : pairOk cs bufs lits (.pair a b) = true) (hloc : litAt lits a = .loc) (hB : SBufs env bufs L sm lsize)
    (hbn : ∀ y n, a = .var y → bufs.lookup y = some n → n < 2 ^ 28)
    (hC : SCs env cs) (ha : TermRun.evalAt env a = some (ta, wa)) (hb : TermRun.evalAt env b = some (tb, wb)) :
    SlAt (SlP L sm) (wa ++ wb) := by
  cases a with
  | lit _ => simp [litAt] at hloc
  | unit => simp [litAt] at hloc
  | var y =>
    simp only [pairOk] at hp
    rw [hloc] at hp
    simp only at hp
    cases hn : bufs.lookup y with
    | none => rw [hn] at hp; cases hp
    | some n =>
      rw [hn] at hp
      simp only [beq_iff_eq] at hp
      obtain ⟨t, u, lbl, he, -, -, hl, hc, -⟩ := hB y n hn
      simp only [TermRun.evalAt, he, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨-, rfl⟩ := ha
      obtain ⟨w, rfl, hw⟩ := hC.constOf hp hb
      exact ⟨lbl, n, by simp [TermRun.cst, Promises.TVal.mk0], by simp [hw], hl, hc, hbn y n rfl hn⟩

/-- **`let x = pair a b` that passes `pairOk`**: the pair's slices. -/
theorem sliceL_pairOp {cs bufs : List (String × Nat)} {lits : List (String × LitV)} {env : TermRun.Env}
    {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} {a b : At} {ta tb : Ty}
    {wa wb : List TermRun.Word}
    (hp : pairOk cs bufs lits (.pair a b) = true) (hS : EnvSl (SlP L sm) lits env) (hB : SBufs env bufs L sm lsize)
    (hbn : ∀ y n, a = .var y → bufs.lookup y = some n → n < 2 ^ 28)
    (hC : SCs env cs) (ha : TermRun.evalAt env a = some (ta, wa)) (hb : TermRun.evalAt env b = some (tb, wb))
    (hl : wa.length = (litAt lits a).words.length) :
    SliceL (SlP L sm) (.node (litAt lits a) (litAt lits b)) (wa ++ wb) :=
  (hS.evalAt ha).pair (hS.evalAt hb) hl fun hloc => slAt_of_pairOk hp hloc hB hbn hC ha hb

/-! ## `countsOk2` through a body -/

section countsB

variable {p : Prog} {cs bufs : List (String × Nat)} {lits : List (String × LitV)}

theorem countsB_let {x : String} {op : Op} {e : Expr} (h : countsB p cs bufs lits (.let_ x op e) = true) :
    pairOk cs bufs lits op = true ∧
      countsB p (csAfter x cs op) (bufsAfter x cs bufs op) ((x, opLit p lits op) :: lits) e = true := by
  simpa only [countsB, Bool.and_eq_true] using h

/-- `let (x, y) = a` of a pair layout: the walk takes its parts. -/
theorem countsB_split {a : At} {x y : String} {e : Expr} {l r : LitV} (hl : litAt lits a = .node l r)
    (h : countsB p cs bufs lits (.split a x y e) = true) :
    countsB p (unbuf y (unbuf x cs)) (unbuf y (unbuf x bufs)) ((y, r) :: (x, l) :: lits) e = true := by
  simp only [countsB] at h
  rw [hl] at h
  exact h

/-- `let (x, y) = a` of another layout: the walk binds leaves. -/
theorem countsB_splitLeaf {a : At} {x y : String} {e : Expr} (hl : ∀ l r, litAt lits a ≠ .node l r)
    (h : countsB p cs bufs lits (.split a x y e) = true) :
    countsB p (unbuf y (unbuf x cs)) (unbuf y (unbuf x bufs)) ((y, .leaf none) :: (x, .leaf none) :: lits) e =
      true := by
  cases hV : litAt lits a with
  | node l r => exact absurd hV (hl l r)
  | _ => simpa only [countsB, hV] using h

theorem countsB_unpack {a : At} {i x : String} {e : Expr} (h : countsB p cs bufs lits (.unpack a i x e) = true) :
    countsB p (unbuf x (unbuf i cs)) (unbuf x (unbuf i bufs)) ((x, litAt lits a) :: lits) e = true := by
  simpa only [countsB] using h

theorem countsB_ifeq {a b : At} {yes no : Expr} (h : countsB p cs bufs lits (.ifeq a b yes no) = true) :
    countsB p cs bufs lits yes = true ∧ countsB p cs bufs lits no = true := by
  simpa only [countsB, Bool.and_eq_true] using h

end countsB

/-- **A block of `countsOk2`**, neither the extern nor its loop, is `countsB`
from its parameter. -/
theorem countsOk2_decl {p : Prog} (h : countsOk2 p = true) {d : Decl} (hd : d ∈ p) (hx : isPrintExt d = false)
    (hl : ¬(hasPrint p = true ∧ d.name = "printL")) :
    countsB p [] [] ((params2 d).map (·, shapeOf d.argTy)) d.body = true := by
  have := List.all_eq_true.1 h d hd
  simp only [hx, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  exact this.resolve_left hl

/-! ## Calls and returns -/

section calls

variable {P : WeakMem.AllocLabel → Nat → Prop}

/-- **A block's entry**: its parameter at its declared layout. -/
theorem envSl_entry {d : Decl} {ws : List TermRun.Word} (hs : SliceL P (shapeOf d.argTy) ws) {env : TermRun.Env} :
    EnvSl P ((params2 d).map (·, shapeOf d.argTy)) ((d.arg, d.argTy, ws) :: env) := by
  intro y M hy
  unfold params2 at hy
  split at hy
  · cases hy
  · simp only [List.map_cons, List.map_nil, lookup_cons_name, List.lookup_nil] at hy
    split at hy
    · cases hy; rename_i hyx; exact ⟨d.argTy, ws, by rw [lookupE_cons]; simp [hyx], hs⟩
    · cases hy

/-- **A call that passes `callsOk2`**: the callee's entry has its
parameter's slices. -/
theorem envSl_call {lits : List (String × LitV)} {env : TermRun.Env} {a : At} {d : Decl} {t : Ty}
    {ws : List TermRun.Word} (h : EnvSl P lits env) (he : TermRun.evalAt env a = some (t, ws))
    (hcall : (litAt lits a).erase = shapeOf d.argTy) :
    EnvSl P ((params2 d).map (·, shapeOf d.argTy)) [(d.arg, d.argTy, ws)] :=
  envSl_entry ((h.evalAt he).of_erase hcall)

/-- **A return that passes `callsOk2`**: the caller's environment extended
by the result has the result's slices. -/
theorem envSl_ret {lc lf : List (String × LitV)} {env : TermRun.Env} {fr : TermRun.Frame} {a : At} {t : Ty}
    {ws : List TermRun.Word} (h : EnvSl P lc env) (he : TermRun.evalAt env a = some (t, ws))
    (hret : (litAt lc a).erase = shapeOf fr.ty) (hf : EnvSl P lf fr.env) :
    EnvSl P ((fr.x, shapeOf fr.ty) :: lf) ((fr.x, fr.ty, ws) :: fr.env) :=
  hf.cons ((h.evalAt he).of_erase hret)

end calls

/-! ## The extern's operand -/

/-- **The output extern's operand** (`ownSliceTy`'s layout, by `callsOk2`):
its first word a locative of a label and its second a number `m`, `P l m`. -/
theorem print_arg_slAt {P : WeakMem.AllocLabel → Nat → Prop} {lits : List (String × LitV)} {env : TermRun.Env}
    {a : At} {t : Ty} {pw wm wn : TermRun.Word} (h : EnvSl P lits env)
    (he : TermRun.evalAt env a = some (t, [pw, wm, wn]))
    (hs : (litAt lits a).erase = shapeOf Scc.Frontend.ownSliceTy) :
    ∃ l m, pw.val = .loc ⟨l, 0⟩ 0 ∧ wm.val = .num m ∧ P l m := by
  have h1 := (h.evalAt he).of_erase hs
  have h2 : SliceL P (.node (.node .loc (.leaf none)) (.leaf none)) [pw, wm, wn] := by
    simpa only [Scc.Frontend.ownSliceTy, shapeOf] using h1
  obtain ⟨l, m, h3, h4, hP⟩ := h2.2.1.1 rfl
  exact ⟨l, m, by simpa [LitV.words] using h3, by simpa [LitV.words] using h4, hP⟩

/-! ## Labels below the next one -/

/-- **The labels of `L` and every message's label are below `B`** (with one
thread, `B = lbase + nalloc`). -/
def LabelsIn (sm : WeakMem.Memory) (L : WeakMem.AllocLabel → Prop) (B : Nat) : Prop :=
  LabelsBelow sm B ∧ ∀ l, L l → l < B

theorem labelsIn_empty (B : Nat) : LabelsIn #[] (fun _ => False) B :=
  ⟨labelsBelow_empty B, fun _ h => h.elim⟩

theorem LabelsIn.mono {sm : WeakMem.Memory} {L : WeakMem.AllocLabel → Prop} {B B' : Nat} (h : LabelsIn sm L B)
    (hB : B ≤ B') : LabelsIn sm L B' :=
  ⟨h.1.mono hB, fun l hl => Nat.lt_of_lt_of_le (h.2 l hl) hB⟩

/-- **A pushed message at a label of `L`** keeps the bound. -/
theorem LabelsIn.push {sm : WeakMem.Memory} {L : WeakMem.AllocLabel → Prop} {B : Nat} (h : LabelsIn sm L B)
    {m : WeakMem.Msg} (hm : L m.loc.label) : LabelsIn (sm.push m) L B :=
  ⟨h.1.push (h.2 _ hm), h.2⟩

/-- **The next label is fresh and outside `L`.** -/
theorem LabelsIn.fresh {sm : WeakMem.Memory} {L : WeakMem.AllocLabel → Prop} {b k : Nat}
    (h : LabelsIn sm L (b + k)) : FreshIn sm (TermRun.freshLabel b 1 0 k) ∧ ¬L (TermRun.freshLabel b 1 0 k) :=
  ⟨freshIn_one h.1, fun hl => by
    have := h.2 _ hl
    rw [freshLabel_one] at this
    exact Nat.lt_irrefl _ this⟩

/-- **One thread's allocation** at its `k`-th label: the label joins `L` and
the bound moves to `b + (k + 1)`. -/
theorem LabelsIn.allocBuf {s : TermRun.St} {L : WeakMem.AllocLabel → Prop} {b k : Nat}
    (h : LabelsIn s.mem L (b + k)) (n : Nat) (z : Option (List WeakMem.Val)) :
    LabelsIn (TermRun.allocBuf (TermRun.freshLabel b 1 0 k) n z s).1.mem
      (fun l => L l ∨ l = TermRun.freshLabel b 1 0 k) (b + (k + 1)) := by
  have hb := labelsBelow_allocBuf h.1 (Nat.le_of_eq (freshLabel_one b k).symm) n z
  rw [freshLabel_one] at hb ⊢
  refine ⟨hb, fun l hl => ?_⟩
  rcases hl with hl | rfl
  · exact Nat.lt_succ_of_lt (h.2 l hl)
  · exact Nat.lt_succ_self _

/-! ## Tests -/

#guard shapeOf Scc.Frontend.ownSliceTy == .node (.node .loc (.leaf none)) (.leaf none)

end Spike.Lib.LowerNode
