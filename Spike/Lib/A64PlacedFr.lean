/-
**The suspended frames' placement through a call and a return** (AArch64): the
transfers a segment invariant carrying `PlacedSE` needs at a source call and a
source return, and the frames' placement kept by a target state that agrees on
the places it uses (registers or slots).

- `FramesPlacedOn`: `FramesPlaced` with every place in a set `B` of places;
  `.toFramesPlaced`, `.mono`, `.of_eq` (kept by a state agreeing with `s` on
  `B`: a callee keeping the caller's slots and callee-saved registers);
  `framesPlacedOn_of_inI` (the slot placement `FramesPlacedInI`),
  `framesPlacedOn_univ` (every place).
- `wordPlaceRep_of_places`: a word place represented alike in two states that
  agree on its places.
- `framesPlaced_of_eq`: the frames placed in a state agreeing on every place.
- `framesPlaced_push`, `framesPlaced_push_nofv`, `framesPlaced_pushSE`: the
  caller's frame pushed at `let x = op in e` from the caller's placement (the
  immediates the caller's are also the continuation's, `himm`).
- `placedSE_call`: the callee's entry at a source call (`FrameStep.call`'s
  successor) at `PlacedSE`, the callee's body a model term or reading no
  variable.
- `placedS_ret`: the continuation after a return placed from the frames.
- `framesPlaced_of_ret`: the frames before a return placed from the
  continuation's `PlacedSE` (the return's binder unread by the continuation's
  frame clause, the continuation no model term).
- `placedSE_ret`: a `ret` of a term reading no variable at `PlacedSE` from the
  continuation's `PlacedSE`.
-/
import Spike.Lib.A64PlacedSE
import Spike.Lib.A64FramesPlacedI

namespace Spike.Lib.A64PlacedFr

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s s' : State} {c : Ctl} {fs : List TermRun.Frame}

/-! ## Placement on a set of places -/

/-- **The suspended frames placed on the places `B`**: `FramesPlaced` with
every place of every word place in `B`. -/
def FramesPlacedOn (Λ : Scc.Sem.Layout) (lbl : Lbl) (s : State) (fs : List TermRun.Frame)
    (B : Place (machine (kernel 1)).I.RegId → Prop) : Prop :=
  ∃ envm : Nat → String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId),
    (∀ d f, fs[d]? = some f → ∀ x ty ws, TermRun.lookupE f.env x = some (ty, ws) →
      ∀ k wd wp, ws[k]? = some wd → envm d x k = some wp → WordPlaceRep (machine (kernel 1)) lbl s wp wd.val) ∧
    (∀ d f, fs[d]? = some f → ∀ x ∈ (exprFv f.body).filter (· != f.x), ∀ ty ws,
      TermRun.lookupE f.env x = some (ty, ws) → ∀ k < ws.length, ∃ pl, envm d x k = some pl) ∧
    (∀ d f x k n, fs[d]? = some f → envm d x k = some (.imm n) → Λ.imms f.body x k = some n) ∧
    (∀ d x k wp, envm d x k = some wp → ∀ pl ∈ wp.places, B pl)

theorem FramesPlacedOn.toFramesPlaced {B : Place (machine (kernel 1)).I.RegId → Prop}
    (h : FramesPlacedOn Λ lbl s fs B) : FramesPlaced Λ lbl s fs := by
  obtain ⟨envm, hrep, htot, himm, -⟩ := h
  exact ⟨envm, hrep, htot, himm⟩

theorem FramesPlacedOn.mono {B B' : Place (machine (kernel 1)).I.RegId → Prop}
    (h : FramesPlacedOn Λ lbl s fs B) (hB : ∀ pl, B pl → B' pl) : FramesPlacedOn Λ lbl s fs B' := by
  obtain ⟨envm, hrep, htot, himm, hin⟩ := h
  exact ⟨envm, hrep, htot, himm, fun d x k wp hwp pl hpl => hB pl (hin d x k wp hwp pl hpl)⟩

/-- **Every placement is on every place.** -/
theorem framesPlacedOn_univ (h : FramesPlaced Λ lbl s fs) : FramesPlacedOn Λ lbl s fs fun _ => True := by
  obtain ⟨envm, hrep, htot, himm⟩ := h
  exact ⟨envm, hrep, htot, himm, fun _ _ _ _ _ _ _ => trivial⟩

/-- **The slot placement is on its slots.** -/
theorem framesPlacedOn_of_inI {A : Nat → Prop} (h : FramesPlacedInI Λ lbl s fs A) :
    FramesPlacedOn Λ lbl s fs fun pl => ∃ a, pl = .slot a ∧ A a := by
  obtain ⟨envm, hrep, htot, hin, himm⟩ := h
  exact ⟨envm, hrep, htot, himm, fun d x k wp hwp => hin d x k wp hwp⟩

/-- **A word place is represented alike in two states agreeing on its
places.** -/
theorem wordPlaceRep_of_places {wp : WordPlace (machine (kernel 1)).I.RegId}
    (hpv : ∀ pl ∈ wp.places, placeVal (machine (kernel 1)) s' pl = placeVal (machine (kernel 1)) s pl)
    {v : WeakMem.Val} (h : WordPlaceRep (machine (kernel 1)) lbl s wp v) :
    WordPlaceRep (machine (kernel 1)) lbl s' wp v := by
  match wp, hpv, h with
  | .one pl, hpv, ⟨w, hw, hr⟩ => exact ⟨w, by rw [hpv pl (by simp [WordPlace.places]), hw], hr⟩
  | .loc pb (.at po), hpv, ⟨vb, vo, hb, ho, hr⟩ =>
    refine ⟨vb, vo, by rw [hpv pb (by simp [WordPlace.places]), hb], ?_, hr⟩
    show placeVal _ _ po = _
    rw [hpv po (by simp [WordPlace.places])]; exact ho
  | .loc pb (.imm n), hpv, ⟨vb, vo, hb, ho, hr⟩ =>
    exact ⟨vb, vo, by rw [hpv pb (by simp [WordPlace.places]), hb], ho, hr⟩
  | .imm n, _, h => exact h

/-- **The placement on `B` is kept** by a state agreeing with `s` on `B`
(a callee's run keeping the caller's slots and callee-saved registers). -/
theorem FramesPlacedOn.of_eq {B : Place (machine (kernel 1)).I.RegId → Prop}
    (h : FramesPlacedOn Λ lbl s fs B)
    (hB : ∀ pl, B pl → placeVal (machine (kernel 1)) s' pl = placeVal (machine (kernel 1)) s pl) :
    FramesPlacedOn Λ lbl s' fs B := by
  obtain ⟨envm, hrep, htot, himm, hin⟩ := h
  exact ⟨envm, fun d f hf x ty ws hx k wd wp hwd hwp =>
    wordPlaceRep_of_places (fun pl hpl => hB pl (hin d x k wp hwp pl hpl)) (hrep d f hf x ty ws hx k wd wp hwd hwp),
    htot, himm, hin⟩

/-- **The frames stay placed** in a state agreeing on every place. -/
theorem framesPlaced_of_eq (h : FramesPlaced Λ lbl s fs)
    (hB : ∀ pl, placeVal (machine (kernel 1)) s' pl = placeVal (machine (kernel 1)) s pl) :
    FramesPlaced Λ lbl s' fs :=
  ((framesPlacedOn_univ h).of_eq fun pl _ => hB pl).toFramesPlaced

/-! ## Through a call -/

/-- **The caller's frame pushed** at `let x = op in e` from the caller's
`PlacedS`, the caller's immediates also the continuation's. -/
theorem framesPlaced_push (h : PlacedS Λ lbl s c fs) {x : String} {op : Op} {e : Expr}
    (ht : c.term = .let_ x op e) {fr : TermRun.Frame} (hx : fr.x = x) (hb : fr.body = e) (he : fr.env = c.env)
    (himm : ∀ y k n, Λ.imms c.term y k = some n → Λ.imms e y k = some n) :
    FramesPlaced Λ lbl s (fr :: fs) := by
  obtain ⟨envm, hrep, htot, himm'⟩ := h
  refine ⟨envm, ?_, ?_, ?_⟩
  · intro d f hf y ty ws hy k wd wp hwd hwp
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      rw [he] at hy
      exact hrep 0 c.env (by simp [envsOf]) y ty ws hy k wd wp hwd hwp
    · exact hrep (d + 1) f.env (by simp_all [envsOf]) y ty ws hy k wd wp hwd hwp
  · intro d f hf y hy ty ws hl k hk
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      rw [he] at hl
      refine htot 0 c.env (exprFv c.term) (by simp [envsOf]) (by simp [fvOf]) y ?_ ty ws hl k hk
      rw [ht, exprFv]
      rw [hb, hx] at hy
      exact List.mem_append_right _ hy
    · simp only [List.getElem?_cons_succ] at hf
      exact htot (d + 1) f.env _ (by simp [envsOf, hf]) (by simp [fvOf, hf]) y hy ty ws hl k hk
  · intro d f y k n hf hy
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      rw [hb]
      exact himm y k n (himm' 0 c.term y k n (by simp [termsOf]) hy)
    · simp only [List.getElem?_cons_succ] at hf
      exact himm' (d + 1) f.body y k n (by simp [termsOf, hf]) hy

/-- **The caller's frame pushed** at `let x = op in e` reading no variable:
the frame reads none either. -/
theorem framesPlaced_push_nofv (h : FramesPlaced Λ lbl s fs) {x : String} {op : Op} {e : Expr}
    (ht : c.term = .let_ x op e) (hfv : exprFv c.term = []) {fr : TermRun.Frame} (hx : fr.x = x)
    (hb : fr.body = e) : FramesPlaced Λ lbl s (fr :: fs) := by
  obtain ⟨envf, hrep, htot, himm⟩ := h
  have hnil : (exprFv fr.body).filter (· != fr.x) = [] := by
    rw [ht, exprFv] at hfv
    rw [hb, hx]
    exact (List.append_eq_nil_iff.mp hfv).2
  refine ⟨fun d => match d with | 0 => fun _ _ => none | d + 1 => envf d, ?_, ?_, ?_⟩
  · intro d f hf y ty ws hy k wd wp hwd hwp
    rcases d with _ | d
    · cases hwp
    · exact hrep d f (by simpa using hf) y ty ws hy k wd wp hwd hwp
  · intro d f hf y hy ty ws hl k hk
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      rw [hnil] at hy
      cases hy
    · exact htot d f (by simpa using hf) y hy ty ws hl k hk
  · intro d f y k n hf hy
    rcases d with _ | d
    · cases hy
    · exact himm d f y k n (by simpa using hf) hy

/-- **The caller's frame pushed** at `let x = op in e` from the caller's
`PlacedSE`, the caller at no model term. -/
theorem framesPlaced_pushSE (h : PlacedSE Λ lbl s c fs) (hne : c.term ∉ externModelTerms) {x : String} {op : Op}
    {e : Expr} (ht : c.term = .let_ x op e) {fr : TermRun.Frame} (hx : fr.x = x) (hb : fr.body = e)
    (he : fr.env = c.env) (himm : ∀ y k n, Λ.imms c.term y k = some n → Λ.imms e y k = some n) :
    FramesPlaced Λ lbl s (fr :: fs) := by
  rcases h with h | ⟨hm | hfv, hf⟩
  · exact framesPlaced_push h ht hx hb he himm
  · exact absurd hm hne
  · exact framesPlaced_push_nofv hf ht hfv hx hb

/-- **The callee's entry at a source call at `PlacedSE`** (`FrameStep.call`'s
successor, at the same target state): the callee's body a model term of the
output extern or reading no variable, the caller's frame pushed by
`framesPlaced_pushSE`. -/
theorem placedSE_call (h : PlacedSE Λ lbl s c fs) (hne : c.term ∉ externModelTerms) {x f : String}
    {is : List String} {a : At} {e : Expr} (ht : c.term = .let_ x (.call f is a []) e) {d : Decl}
    {ws : List TermRun.Word}
    (himm : ∀ y k n, Λ.imms c.term y k = some n → Λ.imms e y k = some n)
    (hE : d.body ∈ externModelTerms ∨ exprFv d.body = []) :
    PlacedSE Λ lbl s ⟨d.body, [(d.arg, d.argTy, ws)], none⟩ (⟨x, e, c.env, [], d.retTy⟩ :: fs) :=
  PlacedSE.of_ext hE (framesPlaced_pushSE h hne ht rfl rfl rfl himm)

/-! ## Through a return -/

theorem lookupE_cons_ne {x y : String} {t : Ty} {ws : List TermRun.Word} {env : TermRun.Env} (h : x ≠ y) :
    TermRun.lookupE ((x, t, ws) :: env) y = TermRun.lookupE env y := by
  simp [TermRun.lookupE, h]

/-- **The continuation after a return placed**: the frames placed, the
return's binder unread by the continuation. -/
theorem placedS_ret {fr : TermRun.Frame} (h : FramesPlaced Λ lbl s (fr :: fs)) (hx : fr.x ∉ exprFv fr.body)
    {t : Ty} {ws : List TermRun.Word} {hd : Option (Nat × TermRun.Word)} :
    PlacedS Λ lbl s ⟨fr.body, (fr.x, t, ws) :: fr.env, hd⟩ fs := by
  obtain ⟨envf, hrep, htot, himm⟩ := h
  refine ⟨fun d => match d with
    | 0 => fun y k => if y = fr.x then none else envf 0 y k
    | d + 1 => envf (d + 1), ?_, ?_, ?_⟩
  · intro d env hd y ty ws' hy k wd wp hwd hwp
    rcases d with _ | d
    · simp only [envsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      by_cases hyx : y = fr.x
      · simp [hyx] at hwp
      · simp only [hyx, ite_false] at hwp
        rw [lookupE_cons_ne (Ne.symm hyx)] at hy
        exact hrep 0 fr (by simp) y ty ws' hy k wd wp hwd hwp
    · simp only [envsOf, List.getElem?_cons_succ, List.getElem?_map] at hd
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact hrep (d + 1) f (by simpa using hf) y ty ws' hy k wd wp hwd hwp
  · intro d env xs hd hxs y hy ty ws' hl k hk
    rcases d with _ | d
    · simp only [envsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      simp only [fvOf, List.getElem?_cons_zero, Option.some.injEq] at hxs
      subst hd hxs
      have hyx : y ≠ fr.x := fun h => hx (h ▸ hy)
      rw [lookupE_cons_ne (Ne.symm hyx)] at hl
      obtain ⟨pl, hpl⟩ := htot 0 fr (by simp) y (by simp [hy, hyx]) ty ws' hl k hk
      exact ⟨pl, by simp [hyx, hpl]⟩
    · simp only [envsOf, List.getElem?_cons_succ, List.getElem?_map] at hd
      simp only [fvOf, List.getElem?_cons_succ, List.getElem?_map] at hxs
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
      rw [hf] at hxs
      cases hxs
      exact htot (d + 1) f (by simpa using hf) y hy ty ws' hl k hk
  · intro d e y k n hd hy
    rcases d with _ | d
    · simp only [termsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      by_cases hyx : y = fr.x
      · simp [hyx] at hy
      · simp only [hyx, ite_false] at hy
        exact himm 0 fr y k n (by simp) hy
    · simp only [termsOf, List.getElem?_cons_succ, List.getElem?_map] at hd
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact himm (d + 1) f y k n (by simpa using hf) hy

/-- **The frames before a return placed** from the continuation's
`PlacedSE`, the continuation at no model term (the return's binder is
filtered out of the frame's clause). -/
theorem framesPlaced_of_ret {fr : TermRun.Frame} {t : Ty} {ws : List TermRun.Word} {hd : Option (Nat × TermRun.Word)}
    (h : PlacedSE Λ lbl s ⟨fr.body, (fr.x, t, ws) :: fr.env, hd⟩ fs) (hne : fr.body ∉ externModelTerms) :
    FramesPlaced Λ lbl s (fr :: fs) := by
  rcases h with h | ⟨hm | hfv, hf⟩
  · obtain ⟨envm, hrep, htot, himm⟩ := h
    refine ⟨fun d => match d with
      | 0 => fun y k => if y = fr.x then none else envm 0 y k
      | d + 1 => envm (d + 1), ?_, ?_, ?_⟩
    · intro d f hf y ty ws' hy k wd wp hwd hwp
      rcases d with _ | d
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
        subst hf
        by_cases hyx : y = fr.x
        · simp [hyx] at hwp
        · simp only [hyx, ite_false] at hwp
          rw [← lookupE_cons_ne (t := t) (ws := ws) (Ne.symm hyx)] at hy
          exact hrep 0 _ (by simp [envsOf]) y ty ws' hy k wd wp hwd hwp
      · exact hrep (d + 1) f.env (by simp_all [envsOf]) y ty ws' hy k wd wp hwd hwp
    · intro d f hf y hy ty ws' hl k hk
      rcases d with _ | d
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
        subst hf
        have hyx : y ≠ fr.x := by simpa using (List.mem_filter.mp hy).2
        rw [← lookupE_cons_ne (t := t) (ws := ws) (Ne.symm hyx)] at hl
        obtain ⟨pl, hpl⟩ := htot 0 _ _ (by simp [envsOf]) (by simp [fvOf]) y (List.mem_filter.mp hy).1
          ty ws' hl k hk
        exact ⟨pl, by simp [hyx, hpl]⟩
      · simp only [List.getElem?_cons_succ] at hf
        exact htot (d + 1) f.env _ (by simp [envsOf, hf]) (by simp [fvOf, hf]) y hy ty ws' hl k hk
    · intro d f y k n hf hy
      rcases d with _ | d
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
        subst hf
        by_cases hyx : y = fr.x
        · simp [hyx] at hy
        · simp only [hyx, ite_false] at hy
          exact himm 0 fr.body y k n (by simp [termsOf]) hy
      · simp only [List.getElem?_cons_succ] at hf
        exact himm (d + 1) f.body y k n (by simp [termsOf, hf]) hy
  · exact absurd hm hne
  · obtain ⟨envf, hrep, htot, himm⟩ := hf
    refine ⟨fun d => match d with | 0 => fun _ _ => none | d + 1 => envf d, ?_, ?_, ?_⟩
    · intro d f hf y ty ws' hy k wd wp hwd hwp
      rcases d with _ | d
      · cases hwp
      · exact hrep d f (by simpa using hf) y ty ws' hy k wd wp hwd hwp
    · intro d f hf y hy ty ws' hl k hk
      rcases d with _ | d
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
        subst hf
        have := (List.mem_filter.mp hy).1
        simp only at hfv
        rw [hfv] at this
        cases this
      · exact htot d f (by simpa using hf) y hy ty ws' hl k hk
    · intro d f y k n hf hy
      rcases d with _ | d
      · cases hy
      · exact himm d f y k n (by simpa using hf) hy

/-- **A `ret` reading no variable at `PlacedSE`** from the continuation's
`PlacedSE` (`framesPlaced_of_ret`): a callee's return pair a frame-run
predecessor of the caller's continuation pair. -/
theorem placedSE_ret {fr : TermRun.Frame} {t : Ty} {ws : List TermRun.Word} {hd : Option (Nat × TermRun.Word)}
    {c' : Ctl} {a : At} (hr : c'.term = .ret a) (ha : atVars a = [])
    (h : PlacedSE Λ lbl s ⟨fr.body, (fr.x, t, ws) :: fr.env, hd⟩ fs) (hne : fr.body ∉ externModelTerms) :
    PlacedSE Λ lbl s c' (fr :: fs) :=
  PlacedSE.of_ext (.inr (by rw [hr, exprFv]; exact ha)) (framesPlaced_of_ret h hne)

end Spike.Lib.A64PlacedFr

/-- info: 'Spike.Lib.A64PlacedFr.placedSE_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64PlacedFr.placedSE_call

/-- info: 'Spike.Lib.A64PlacedFr.placedSE_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64PlacedFr.placedSE_ret

/-- info: 'Spike.Lib.A64PlacedFr.placedS_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64PlacedFr.placedS_ret

/-- info: 'Spike.Lib.A64PlacedFr.FramesPlacedOn.of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64PlacedFr.FramesPlacedOn.of_eq
