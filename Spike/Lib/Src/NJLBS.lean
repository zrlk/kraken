import Spike.Lib.Src.NJLB
import Spike.Lib.Src.NJLS

/-!
**Slices from the start before the setup block** (ISA-neutral): `EnvSl`
along `setupTerm` (`let r = call rodata u; let a = (r, me); tail main a`),
as `NJLS` has `EnvLit`. The start's bindings (`me` one word, `u` none) have
no pair, so no slice; `rodata`'s result comes back with its slices
(`envSl_ret`); the pair `a = (r, me)` has its parts' slices, and none of its
own when `rodata`'s result type is not a bare locative.

- `envSl_setupStart`: the start's environment;
- `envSl_setup_call`: the call of `rodata` (unit argument);
- `envSl_setup_pair`: the pair `a = (r, me)`;
- `envSl_main_entry`: `tail main a` enters `main` (`main2`);
- `envB_setup_call`, `envB_main_entry`: the same as `EnvB` at the blocks'
  entries (`countsOk2_decl`: no known value, no buffer).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (LitV litAt shapeOf params2)

variable {P : WeakMem.AllocLabel → Nat → Prop}

/-- **The start's environment** has the slices of `setupLits` (none). -/
theorem envSl_setupStart (meW : TermRun.Word) :
    EnvSl P setupLits [("me", .ptr .pub .void, [meW]), ("u", .unit, [])] :=
  ((EnvSl.nil []).cons (SliceL.nil _)).cons (SliceL.leaf _ _)

/-- **The call of `rodata`** on `u`: `rodata`'s entry. -/
theorem envSl_setup_call {env : TermRun.Env} {d : Decl} {t : Ty} {ws : List TermRun.Word}
    (h : EnvSl P setupLits env) (he : TermRun.evalAt env (.var "u") = some (t, ws)) (hu : d.argTy = .unit) :
    EnvSl P ((params2 d).map (·, shapeOf d.argTy)) [(d.arg, d.argTy, ws)] :=
  envSl_call h he (by rw [hu]; rfl)

/-- **The pair `a = (r, me)`** after `rodata` returns `r` at its declared
layout, that layout not a bare locative. -/
theorem envSl_setup_pair {env : TermRun.Env} {s t u : Ty} {wr wm : List TermRun.Word}
    (h : EnvSl P (("r", shapeOf s) :: setupLits) env)
    (her : TermRun.evalAt env (.var "r") = some (t, wr)) (hem : TermRun.evalAt env (.var "me") = some (u, wm))
    (hlen : wr.length = (shapeOf s).words.length) (hs : shapeOf s ≠ .loc) :
    EnvSl P (("a", .node (shapeOf s) (.leaf none)) :: ("r", shapeOf s) :: setupLits)
      (("a", .prod t u, wr ++ wm) :: env) :=
  h.cons ((h.evalAt her).pair (h.evalAt hem) hlen fun hl => absurd hl hs)

/-- **`tail main a`** enters `main` with its parameter's slices (`main2`). -/
theorem envSl_main_entry {lits : List (String × LitV)} {env : TermRun.Env} {s t : Ty} {ws : List TermRun.Word}
    {d : Decl} (h : EnvSl P (("a", .node (shapeOf s) (.leaf none)) :: lits) env)
    (he : TermRun.evalAt env (.var "a") = some (t, ws)) (hd : d.argTy = .prod s (.ptr .pub .void)) :
    EnvSl P ((params2 d).map (·, shapeOf d.argTy)) [(d.arg, d.argTy, ws)] := by
  have hs := h.evalAt he
  refine envSl_entry (env := []) ?_
  rw [hd]
  exact hs

/-- **`rodata`'s entry** as `EnvB`. -/
theorem envB_setup_call {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat}
    {env : TermRun.Env} {d : Decl}
    {t : Ty} {ws : List TermRun.Word} (h : EnvSl (SlP L sm) setupLits env)
    (he : TermRun.evalAt env (.var "u") = some (t, ws)) (hu : d.argTy = .unit) :
    EnvB ((params2 d).map (·, shapeOf d.argTy)) [] [] L sm lsize [(d.arg, d.argTy, ws)] :=
  ⟨envSl_setup_call h he hu, sBufs_nil _ _ _ _, SCs.nil _⟩

/-- **`main`'s entry** as `EnvB`. -/
theorem envB_main_entry {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat}
    {lits : List (String × LitV)}
    {env : TermRun.Env} {s t : Ty} {ws : List TermRun.Word} {d : Decl}
    (h : EnvSl (SlP L sm) (("a", .node (shapeOf s) (.leaf none)) :: lits) env)
    (he : TermRun.evalAt env (.var "a") = some (t, ws)) (hd : d.argTy = .prod s (.ptr .pub .void)) :
    EnvB ((params2 d).map (·, shapeOf d.argTy)) [] [] L sm lsize [(d.arg, d.argTy, ws)] :=
  ⟨envSl_main_entry h he hd, sBufs_nil _ _ _ _, SCs.nil _⟩

/-! ## Tests -/

-- `hello1`'s `rodata` returns the slice package: its layout is a pair, not a bare locative.
#guard shapeOf (.iex Spike.Lib.Hello1Src.sliceTy) != .loc

end Spike.Lib.LowerNode
