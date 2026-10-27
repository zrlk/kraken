/-
**The suspended frames' placement at depth** (x86-64, H7a calls, the deep
abort path): `PlacedS` (`Spike/Lib/X64ConsumerS.lean`) split into the
current control's `Placed` and the suspended frames' (`FramesPlaced`), the
suspended frames placed in stack slots only (`FramesPlacedIn`: no register,
no whole-word immediate), so that a callee's run, which keeps the caller's
cells, keeps them placed; and `EnvSmallS` through a call.

- `FramesPlaced`, `PlacedS.ofFrames`, `PlacedS.frames`: `PlacedS` is the
  current control's `Placed` and the suspended frames' placement.
- `SlotPlaced`: the caller's `Placed` with every place a stack slot in `A`
  (at the call, the caller's words spilled to its frame's slots).
- `FramesPlacedIn`, `.toFramesPlaced`, `.of_eq` (kept by a state whose
  private memory agrees on `A`), `.push` (the caller's frame pushed at a
  call from its `SlotPlaced` control).
- `EnvSmallS.push`, `EnvSmallS.tail`: `EnvSmallS` through a call and a
  return.
-/
import Spike.Lib.X64ConsumerS

namespace Spike.Lib.X64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.X64Consumer

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s s' : State} {c : Ctl} {fs : List TermRun.Frame}

/-! ## The suspended frames' placement -/

/-- **Every suspended frame's environment is placed** in `s` (`PlacedS`'s
clauses at the frames `fs`, frame `d` the `d`-th suspended one): each placed
word represented, every word of a variable the frame still reads placed, an
immediate only where the layout's table has it at the frame's body. -/
def FramesPlaced (Λ : Scc.Sem.Layout) (lbl : Lbl) (s : State) (fs : List TermRun.Frame) : Prop :=
  ∃ envm : Nat → String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId),
    (∀ d f, fs[d]? = some f → ∀ x ty ws, TermRun.lookupE f.env x = some (ty, ws) →
      ∀ k wd wp, ws[k]? = some wd → envm d x k = some wp → WordPlaceRep (machine (kernel 1)) lbl s wp wd.val) ∧
    (∀ d f, fs[d]? = some f → ∀ x ∈ (exprFv f.body).filter (· != f.x), ∀ ty ws,
      TermRun.lookupE f.env x = some (ty, ws) → ∀ k < ws.length, ∃ pl, envm d x k = some pl) ∧
    (∀ d f x k n, fs[d]? = some f → envm d x k = some (.imm n) → Λ.imms f.body x k = some n)

/-- **The current control placed and the suspended frames placed** is every
frame placed. -/
theorem PlacedS.ofFrames (h : Placed Λ lbl s c) (hf : FramesPlaced Λ lbl s fs) : PlacedS Λ lbl s c fs := by
  obtain ⟨envm, hrep, htot, himm⟩ := h
  obtain ⟨envf, hrepf, htotf, himmf⟩ := hf
  refine ⟨fun d => match d with | 0 => envm | d + 1 => envf d, ?_, ?_, ?_⟩
  · intro d env hd x ty ws hx k wd wp hwd hwp
    rcases d with _ | d
    · simp only [envsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      exact hrep x ty ws hx k wd wp hwd hwp
    · simp only [envsOf, List.getElem?_cons_succ, List.getElem?_map] at hd
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact hrepf d f hf x ty ws hx k wd wp hwd hwp
  · intro d env xs hd hxs x hx ty ws hl k hk
    rcases d with _ | d
    · simp only [envsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      simp only [fvOf, List.getElem?_cons_zero, Option.some.injEq] at hxs
      subst hd hxs
      exact htot x hx ty ws hl k hk
    · simp only [envsOf, List.getElem?_cons_succ, List.getElem?_map] at hd
      simp only [fvOf, List.getElem?_cons_succ, List.getElem?_map] at hxs
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
      rw [hf] at hxs
      cases hxs
      exact htotf d f hf x hx ty ws hl k hk
  · intro d e x k n hd hx
    rcases d with _ | d
    · simp only [termsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      exact himm x k n hx
    · simp only [termsOf, List.getElem?_cons_succ, List.getElem?_map] at hd
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact himmf d f x k n hf hx

/-- **Every frame placed places the suspended ones.** -/
theorem PlacedS.frames (h : PlacedS Λ lbl s c fs) : FramesPlaced Λ lbl s fs := by
  obtain ⟨envm, hrep, htot, himm⟩ := h
  refine ⟨fun d => envm (d + 1), ?_, ?_, ?_⟩
  · intro d f hf x ty ws hx k wd wp hwd hwp
    exact hrep (d + 1) f.env (by simp [envsOf, hf]) x ty ws hx k wd wp hwd hwp
  · intro d f hf x hx ty ws hl k hk
    exact htot (d + 1) f.env _ (by simp [envsOf, hf]) (by simp [fvOf, hf]) x hx ty ws hl k hk
  · intro d f x k n hf hx
    exact himm (d + 1) f.body x k n (by simp [termsOf, hf]) hx

/-! ## Placed in stack slots -/

/-- **A word place in the slots of `A`**: not a whole-word immediate, and
each of its places a slot of `A`. -/
def InSlots (A : Nat → Prop) (wp : WordPlace (machine (kernel 1)).I.RegId) : Prop :=
  (∀ n, wp ≠ .imm n) ∧ ∀ pl ∈ wp.places, ∃ a, pl = .slot a ∧ A a

/-- **A control placed in the slots of `A`** (`Placed` with every place a
slot of `A`): the caller at a call, its words in its frame's slots. -/
def SlotPlaced (lbl : Lbl) (s : State) (c : Ctl) (A : Nat → Prop) : Prop :=
  ∃ envm : String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId),
    (∀ x ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k wd wp, ws[k]? = some wd → envm x k = some wp →
      WordPlaceRep (machine (kernel 1)) lbl s wp wd.val) ∧
    (∀ x ∈ exprFv c.term, ∀ ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k < ws.length,
      ∃ pl, envm x k = some pl) ∧
    (∀ x k wp, envm x k = some wp → InSlots A wp)

/-- **The suspended frames placed in the slots of `A`**. -/
def FramesPlacedIn (lbl : Lbl) (s : State) (fs : List TermRun.Frame) (A : Nat → Prop) :
    Prop :=
  ∃ envm : Nat → String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId),
    (∀ d f, fs[d]? = some f → ∀ x ty ws, TermRun.lookupE f.env x = some (ty, ws) →
      ∀ k wd wp, ws[k]? = some wd → envm d x k = some wp → WordPlaceRep (machine (kernel 1)) lbl s wp wd.val) ∧
    (∀ d f, fs[d]? = some f → ∀ x ∈ (exprFv f.body).filter (· != f.x), ∀ ty ws,
      TermRun.lookupE f.env x = some (ty, ws) → ∀ k < ws.length, ∃ pl, envm d x k = some pl) ∧
    (∀ d x k wp, envm d x k = some wp → InSlots A wp)

/-- No suspended frame is placed anywhere. -/
theorem FramesPlacedIn.nil (A : Nat → Prop) : FramesPlacedIn lbl s [] A :=
  ⟨fun _ _ _ => none, fun _ _ hf => by simp at hf, fun _ _ hf => by simp at hf, fun _ _ _ _ h => by cases h⟩

/-- **Placed in slots is placed.** -/
theorem FramesPlacedIn.toFramesPlaced {A : Nat → Prop} (h : FramesPlacedIn lbl s fs A) :
    FramesPlaced Λ lbl s fs := by
  obtain ⟨envm, hrep, htot, hin⟩ := h
  exact ⟨envm, hrep, htot, fun d _ x k n _ hx => ((hin d x k _ hx).1 n rfl).elim⟩

/-- A word in the slots of `A` is represented alike in two states whose
private memory agrees on `A`. -/
theorem wordPlaceRep_of_eq {A : Nat → Prop}
    (hA : ∀ a, A a → (machine (kernel 1)).privLoad s' (BitVec.ofNat 64 a) =
      (machine (kernel 1)).privLoad s (BitVec.ofNat 64 a))
    {wp : WordPlace (machine (kernel 1)).I.RegId} (hwp : InSlots A wp) {v : WeakMem.Val}
    (h : WordPlaceRep (machine (kernel 1)) lbl s wp v) : WordPlaceRep (machine (kernel 1)) lbl s' wp v := by
  obtain ⟨hni, hpl⟩ := hwp
  have hpv : ∀ pl ∈ wp.places, placeVal (machine (kernel 1)) s' pl = placeVal (machine (kernel 1)) s pl := by
    intro pl hm
    obtain ⟨a, rfl, ha⟩ := hpl pl hm
    simp only [placeVal, hA a ha]
  match wp, hpv, hni, h with
  | .one pl, hpv, _, ⟨w, hw, hr⟩ => exact ⟨w, by rw [hpv pl (by simp [WordPlace.places]), hw], hr⟩
  | .loc pb (.at po), hpv, _, ⟨vb, vo, hb, ho, hr⟩ =>
    refine ⟨vb, vo, by rw [hpv pb (by simp [WordPlace.places]), hb], ?_, hr⟩
    show placeVal _ _ po = _
    rw [hpv po (by simp [WordPlace.places])]; exact ho
  | .loc pb (.imm n), hpv, _, ⟨vb, vo, hb, ho, hr⟩ =>
    exact ⟨vb, vo, by rw [hpv pb (by simp [WordPlace.places]), hb], ho, hr⟩
  | .imm n, _, hni, _ => exact (hni n rfl).elim

/-- **Placed in slots is kept** by a state whose private memory agrees on
`A` (a callee's run keeping the caller's cells). -/
theorem FramesPlacedIn.of_eq {A : Nat → Prop} (h : FramesPlacedIn lbl s fs A)
    (hA : ∀ a, A a → (machine (kernel 1)).privLoad s' (BitVec.ofNat 64 a) =
      (machine (kernel 1)).privLoad s (BitVec.ofNat 64 a)) :
    FramesPlacedIn lbl s' fs A := by
  obtain ⟨envm, hrep, htot, hin⟩ := h
  exact ⟨envm, fun d f hf x ty ws hx k wd wp hwd hwp =>
    wordPlaceRep_of_eq hA (hin d x k wp hwp) (hrep d f hf x ty ws hx k wd wp hwd hwp), htot, hin⟩

/-- **The caller's frame pushed at a call**: a control placed in the slots
of `A` at `let x = op in e` and the suspended frames placed there place the
frames with the caller's continuation `e` (in the caller's environment,
returning into `x`) pushed. -/
theorem FramesPlacedIn.push {A : Nat → Prop} (hc : SlotPlaced lbl s c A) (hf : FramesPlacedIn lbl s fs A)
    {x : String} {op : Op} {e : Expr} (ht : c.term = .let_ x op e) {fr : TermRun.Frame} (hx : fr.x = x)
    (hb : fr.body = e) (he : fr.env = c.env) :
    FramesPlacedIn lbl s (fr :: fs) A := by
  obtain ⟨envc, hrepc, htotc, hinc⟩ := hc
  obtain ⟨envf, hrepf, htotf, hinf⟩ := hf
  refine ⟨fun d => match d with | 0 => envc | d + 1 => envf d, ?_, ?_, ?_⟩
  · intro d f hfd y ty ws hy k wd wp hwd hwp
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hfd
      subst hfd
      rw [he] at hy
      exact hrepc y ty ws hy k wd wp hwd hwp
    · exact hrepf d f (by simpa using hfd) y ty ws hy k wd wp hwd hwp
  · intro d f hfd y hy ty ws hl k hk
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hfd
      subst hfd
      rw [he] at hl
      refine htotc y ?_ ty ws hl k hk
      rw [ht, exprFv]
      rw [hb, hx] at hy
      exact List.mem_append_right _ hy
    · exact htotf d f (by simpa using hfd) y hy ty ws hl k hk
  · intro d y k wp hwp
    rcases d with _ | d
    · exact hinc y k wp hwp
    · exact hinf d y k wp hwp

/-! ## Small environments through calls -/

/-- **`EnvSmallS` through a call**: the callee's environment small and the
caller's frame (in the caller's environment) pushed. -/
theorem EnvSmallS.push {cE : TermRun.Env} {fr : TermRun.Frame} (hE : EnvSmall cE) (hc : EnvSmallS c.env fs)
    (he : fr.env = c.env) : EnvSmallS cE (fr :: fs) := by
  refine ⟨hE, fun f hf => ?_⟩
  rcases List.mem_cons.mp hf with rfl | hf
  · rw [he]; exact hc.1
  · exact hc.2 f hf

/-- **`EnvSmallS` through a return**: the suspended frames below the top one
keep theirs. -/
theorem EnvSmallS.tail {env env' : TermRun.Env} {fr : TermRun.Frame} (h : EnvSmallS env (fr :: fs))
    (hE : EnvSmall env') : EnvSmallS env' fs :=
  ⟨hE, fun f hf => h.2 f (List.mem_cons_of_mem _ hf)⟩

end Spike.Lib.X64ConsumerS
