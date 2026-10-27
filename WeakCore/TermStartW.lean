import WeakCore.TermInit
import WeakCore.TermSpawnEntry

/-! # TermStartW: the wrapper start

`main`'s return produces its exit event through a **start wrapper**, not a machine rule: thread 0 runs
`let r = call main a in …exitEv… in ret ()` on `a : Unit` (no words).  The exit argument follows
Kraken's rule "exit (n mod 256) if the result is one number word, else exit 0":

* `main` returns an integer (`Int`, `Int[i]`, through `refine`): `exitEv r`;
* `main` returns another one-number-word type (`fix sg w`, `lanes sg w`, through `refine`): the word as
  an `Int` of the same 64-bit pattern, `let v = cvt U64 r in let n = toInt v in exitEv n` (`cvt` to
  `fix false w64` keeps the low byte, sign-extending a signed `fix`), so the event is `exit (n mod 256)`
  of the same low byte;
* otherwise (or no `main`): `exitEv 0`.

The existing `Ext`/`exitEv` step appends `exit (exitCode n)`.  No new step, flag or frozen text.

* `startW p cap`: the wrapper thread alone, empty memory, empty trace, capacity `cap`.
* `initShape_startW`: `TermInit.InitShape p (startW p cap)` from the checker accepting the wrapper
  (`check` and `checkW` at `wcx`); hence `InitOK` (`TermMain.initOK_of`).
* `runScope_startW`: `RunScope (startW p cap)`, unconditionally (`TermInit.runDRF_init`).
-/

namespace TermStartW

open CoreLang CoreTerm CoreTyping TermRun TermSound TermCut TermTv TermScope TermInit

/-- A type with its `refine`ments stripped. -/
def unRefine : Ty → Ty
  | .refine t _ => unRefine t
  | t => t

/-- One number word: an integer, a fixed-width integer or a `lanes` word, through `refine`. -/
def numWord (t : Ty) : Bool :=
  (intOf t).isSome || (fixOf (unRefine t)).isSome || (lanesOf (unRefine t)).isSome

/-- `main`'s declared result type, if the program has a `main`. -/
def mainRet (p : Prog) : Option Ty := (p.find? (·.name == "main")).map (·.retTy)

/-- Does the program's `main` return one number word (Kraken's "exit n mod 256" case)? -/
def mainRetNum (p : Prog) : Bool :=
  match mainRet p with
  | some t => numWord t
  | none => false

/-- The wrapper's exit tail after `r := main a`, by `main`'s result type (see the module doc). -/
def exitTail : Option Ty → Expr
  | some t =>
      if (intOf t).isSome then .let_ "u" (.ext .exitEv (.var "r")) (.ret .unit)
      else if numWord t then
        .let_ "v" (.cvt false .w64 (.var "r"))
          (.let_ "n" (.toInt (.var "v")) (.let_ "u" (.ext .exitEv (.var "n")) (.ret .unit)))
      else .let_ "u" (.ext .exitEv (.lit 0)) (.ret .unit)
  | none => .let_ "u" (.ext .exitEv (.lit 0)) (.ret .unit)

/-- **The start wrapper's body**: call `main` on `a`, then make the exit event. -/
def wrapTerm (rt : Option Ty) : Expr := .let_ "r" (.call "main" [] (.var "a")) (exitTail rt)

/-- The wrapper thread of program `p`: `a : Unit`, bound to no words; every other field at its default. -/
def wrapTh (p : Prog) : TTh := { term := wrapTerm (mainRet p), env := [("a", .unit, [])] }

/-- **The wrapper start**: the wrapper thread alone, empty memory, empty trace, thread capacity `cap`. -/
def startW (p : Prog) (cap : Nat) : Cfg := { mem := #[], ths := #[wrapTh p], cap := cap }

/-- The wrapper's checking context: `a : Unit`, returning `Unit`. -/
def wcx : Cx := { vars := [("a", .unit, true)], ret := .unit }

@[simp] theorem startW_cap (p : Prog) (cap : Nat) : (startW p cap).cap = cap := rfl
@[simp] theorem startW_trace (p : Prog) (cap : Nat) : (startW p cap).trace = [] := rfl

theorem startW_get {p : Prog} {cap i : Nat} {th : TTh} (h : (startW p cap).ths[i]? = some th) :
    i = 0 ∧ th = wrapTh p := by
  simp only [startW] at h
  rcases i with _ | i
  · simp at h; exact ⟨rfl, h.symm⟩
  · simp at h

theorem allOK_exitTail (rt : Option Ty) : allOK (exitTail rt) = true := by
  unfold exitTail
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem allOK_wrapTerm (rt : Option Ty) : allOK (wrapTerm rt) = true := by
  simp only [wrapTerm, allOK, allOK_exitTail, Bool.and_true]
  rfl

theorem wcx_tvOK : TvOK wcx := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wcx] <;> decide

/-- **`RunScope` at the wrapper start** (no program condition). -/
theorem runScope_startW (p : Prog) (cap : Nat) : RunScope (startW p cap) :=
  runDRF_init fun i th hth => by
    obtain ⟨-, rfl⟩ := startW_get hth
    have hσ : AllDrf (wrapTh p).σs := fun σ (hσ : σ ∈ ([] : List Ty)) => by cases hσ
    refine ⟨allOK_wrapTerm _, hσ, fun e he => ?_, rfl⟩
    simp only [wrapTh, List.mem_singleton] at he
    subst he
    rfl

/-- **The holdings clause of a one-argument entry frame** `a : t` bound to `ws`, holding nothing: the shared
form of the `HeldOK` block of `TermInit.entryOK_of` and `TermSpawn.entryR_of` (those two still carry their own
copies; switching them is a follow-up). -/
theorem heldOK_entry {η : TEnv} {t r : Ty} {env : Env} {ws : List Word} (henv : env = [("a", t, ws)])
    (hv : VRR (fun _ => 0) η t (shp t) ws .zero) :
    HeldOK (fun _ => 0) η { vars := [("a", t, true)], ret := r } env .zero := by
  have hfind : ∀ x e, ([("a", t, true)] : List (String × Ty × Bool)).find? (·.1 == x) = some e →
      x = "a" ∧ e = ("a", t, true) := by
    intro x e h
    by_cases hx : "a" = x
    · subst hx; simp at h; exact ⟨rfl, h.symm⟩
    · have : ("a" == x) = false := by simpa using hx
      simp [List.find?, this] at h
  refine ⟨by simp, by simp, fun y h => by simp at h, fun _ => .zero, fun x e hx _ => ?_, ?_⟩
  · obtain ⟨rfl, rfl⟩ := hfind x e hx
    exact ⟨t, ws, by rw [henv]; simp [lookupE], hv⟩
  · simp only [TermSound.Holds, List.filter, Bool.true_or, List.map, Res.sum_cons, Res.sum_nil, Res.add_zero]
    exact Res.le_refl _

/-- **The wrapper's entry frame** (`EntryOK`), from the checker accepting the wrapper at `wcx`. -/
theorem entryOK_wrap {p : Prog} {i : Nat} (hc : check p wcx (wrapTerm (mainRet p)) = .ok ())
    (hw : checkW p wcx (wrapTerm (mainRet p)) = .ok ()) : EntryOK p i (wrapTh p) := by
  have hv : VRR (fun _ => 0) (Cut (Eg0 p) i S0) .unit (shp .unit) ([] : List Word) .zero := rfl
  exact ⟨fun _ => 0, wcx, ⟨check_sound p _ _ hc, hw,
      fun v hm => by simp only [wcx, List.mem_singleton] at hm; subst hm; rfl,
      fun k hk _ => absurd hk (Nat.not_lt_zero _)⟩, wcx_tvOK,
    TermSpawn.finv_entry (fun _ _ => trivial) rfl rfl hv (Lay_etok_unit rfl), fun _ _ _ _ _ _ => rfl,
    heldOK_entry rfl hv⟩

/-- **`InitShape` at the wrapper start**, from the checker accepting the wrapper at `wcx`. -/
theorem initShape_startW {p : Prog} {cap : Nat} (hc : check p wcx (wrapTerm (mainRet p)) = .ok ())
    (hw : checkW p wcx (wrapTerm (mainRet p)) = .ok ()) : InitShape p (startW p cap) where
  mem := rfl
  pairs := rfl
  bf := rfl
  thr := fun i th hth => by
    obtain ⟨-, rfl⟩ := startW_get hth
    exact ⟨rfl, rfl, rfl, entryOK_wrap hc hw⟩
  vs0 := fun i th hth => by
    obtain ⟨-, rfl⟩ := startW_get hth
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun e he w hw => ?_⟩
    simp only [wrapTh, List.mem_singleton] at he
    subst he
    cases hw
  envNoLoc := fun i th hth => by
    obtain ⟨-, rfl⟩ := startW_get hth
    intro e he w hw
    simp only [wrapTh, List.mem_singleton] at he
    subst he
    cases hw
  tid0 := fun i th hth => by
    obtain ⟨-, rfl⟩ := startW_get hth
    rfl

end TermStartW

#print axioms TermStartW.startW_get
#print axioms TermStartW.allOK_exitTail
#print axioms TermStartW.allOK_wrapTerm
#print axioms TermStartW.wcx_tvOK
#print axioms TermStartW.runScope_startW
#print axioms TermStartW.heldOK_entry
#print axioms TermStartW.entryOK_wrap
#print axioms TermStartW.initShape_startW
