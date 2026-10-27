import Spike.Lib.Src.NJLC
import Spike.Lib.Hello1Src

/-!
**`EnvLit` from the start before the setup block** (ISA-neutral). The start
`setupStart cap meW` (`Scc/Sem/SrcOut.lean`) binds `me` at `Ptr pub Void` to
`meW` and `u` to the unit and runs `setupTerm`: `let r = call rodata u;
let a = (r, me); tail main a`. `setupInit` lets the start's `meW` be any
word, so the simulation picks a number (`meNum`). Along `setupTerm`, with
`me` and `u` at their walk layouts (`setupLits`):

- `envLit_setupStart`: the start's environment;
- `envLit_setup_call`: the call of `rodata` (unit argument), by `envLit_call`;
- `envLit_setup_pair`: after `rodata` returns its result `r` at its declared
  layout, the pair `a = (r, me)`;
- `envLit_main_entry`: `tail main a` enters `main` with its parameter at its
  declared layout, `main`'s argument type the pair of `rodata`'s result type
  and `Ptr pub Void` (`main2`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (LitV litAt shapeOf params2)

/-- **The walk's bindings at the start**: `me` one word, `u` none. -/
def setupLits : List (String × LitV) := [("me", .leaf none), ("u", .nil)]

/-- **A number for `me`**: the start's word chosen as the target's value. -/
def meNum (v : Nat) : TermRun.Word := TermRun.cst (.num v)

theorem isNum_meNum {v : Nat} (hv : v < 2 ^ 64) : IsNum (meNum v) := ⟨v, rfl, hv⟩

/-- **The start's environment** has `EnvLit` at `setupLits`, `me` a number. -/
theorem envLit_setupStart {meW : TermRun.Word} (hm : IsNum meW) :
    EnvLit setupLits [("me", .ptr .pub .void, [meW]), ("u", .unit, [])] := by
  have h0 : EnvLit [] ([] : TermRun.Env) := fun _ _ h => by cases h
  have hu : EnvLit [("u", .nil)] [("u", .unit, [])] := h0.cons rfl (NumL.of_all (by simp))
  exact hu.cons rfl (NumL.of_all fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact hm)

theorem inLits_setup_u : InLits setupLits (.var "u") := fun x hx => by cases hx; rfl

theorem inLits_setup_me : InLits setupLits (.var "me") := fun x hx => by cases hx; rfl

/-- **The call of `rodata`** on `u`: `rodata`'s entry and the pushed frame. -/
theorem envLit_setup_call {env : TermRun.Env} {e : Expr} {d : Decl} {t : Ty} {ws : List TermRun.Word}
    (h : EnvLit setupLits env) (he : TermRun.evalAt env (.var "u") = some (t, ws)) (hu : d.argTy = .unit)
    (hcr : Compat d.retTy (shapeOf d.retTy) = true) :
    EnvLit ((params2 d).map (·, shapeOf d.argTy)) [(d.arg, d.argTy, ws)] ∧
      FrameLit ⟨"r", e, env, [], d.retTy⟩ setupLits :=
  envLit_call (c := ⟨.let_ "r" (.call "rodata" [] (.var "u")) e, env, none⟩) h inLits_setup_u
    (fun _ h => by cases h) he (by rw [hu]; rfl) (by rw [hu]; rfl) hcr

/-- **The pair `a = (r, me)`** after `rodata` returns `r` at its declared
layout. -/
theorem envLit_setup_pair {env : TermRun.Env} {s t u : Ty} {wr wm : List TermRun.Word}
    (h : EnvLit (("r", shapeOf s) :: setupLits) env)
    (her : TermRun.evalAt env (.var "r") = some (t, wr)) (hem : TermRun.evalAt env (.var "me") = some (u, wm))
    (hlen : wr.length = (shapeOf s).words.length) :
    EnvLit (("a", .node (shapeOf s) (.leaf none)) :: ("r", shapeOf s) :: setupLits)
      (("a", .prod t u, wr ++ wm) :: env) := by
  have hr : InLits (("r", shapeOf s) :: setupLits) (.var "r") := fun x hx => by cases hx; rfl
  have hm : InLits (("r", shapeOf s) :: setupLits) (.var "me") := fun x hx => by cases hx; rfl
  obtain ⟨hcr, hnr⟩ := h.evalAt' hr (fun _ h => by cases h) her
  obtain ⟨hcm, hnm⟩ := h.evalAt' hm (fun _ h => by cases h) hem
  have hlr : litAt (("r", shapeOf s) :: setupLits) (.var "r") = shapeOf s := rfl
  have hlm : litAt (("r", shapeOf s) :: setupLits) (.var "me") = .leaf none := rfl
  rw [hlr] at hcr hnr; rw [hlm] at hcm hnm
  exact h.cons (by simp [Compat, hcr, hcm]) (hnr.pair hnm hlen)

/-- **`tail main a`** enters `main` with its parameter at its declared
layout: `main`'s argument type is the pair of `rodata`'s result type and
`Ptr pub Void` (`main2`). -/
theorem envLit_main_entry {lits : List (String × LitV)} {env : TermRun.Env} {s t : Ty} {ws : List TermRun.Word}
    {d : Decl} (h : EnvLit (("a", .node (shapeOf s) (.leaf none)) :: lits) env)
    (he : TermRun.evalAt env (.var "a") = some (t, ws)) (hd : d.argTy = .prod s (.ptr .pub .void))
    (hc : Compat d.argTy (shapeOf d.argTy) = true) :
    EnvLit ((params2 d).map (·, shapeOf d.argTy)) [(d.arg, d.argTy, ws)] := by
  have ha : InLits (("a", .node (shapeOf s) (.leaf none)) :: lits) (.var "a") := fun x hx => by cases hx; rfl
  have hn := (h.evalAt' ha (fun _ h => by cases h) he).2
  refine EnvLit.entry hc ?_
  rw [hd]
  exact hn

/-- **A type with a runtime layout has its own layout** (`simpleTy`, its
words known): the `Compat` premises of the entries and frames. -/
theorem compat_shapeOf_self {t : Ty} (hs : Scc.Lower.simpleTy t = true) {k : Nat}
    (hk : Scc.Obj.valWords t = some k) : Compat t (shapeOf t) = true :=
  compat_shapeOf t 0 0 hs (slots_of_valWords hk)

/-! ## Tests -/

-- `hello1L.w`'s `main` takes the pair of the slice package and `me`: its layout is the
-- package's three words (locative, count, length) and `me`'s one.
#guard litMask (shapeOf (.prod (.iex Spike.Lib.Hello1Src.sliceTy) (.ptr .pub .void))) == [false, true, true, true]

end Spike.Lib.LowerNode
