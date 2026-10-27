import Spike.Lib.SrcCalls

/-!
**The setup call's frame** (ISA-neutral): the start before the setup block
(`SrcSem.setupStart`) calls `rodata` on `u` from `SrcSem.setupTerm`, pushing
a frame that returns into `r` and continues with `SrcCalls.setupCont`. That
continuation reads `me` alone (besides `r`), and the start's environment
binds `me` to the one word `meW`: the facts the targets' frame placement
(`X64SetupPlaced`, `A64SetupPlaced`) reads.

- `setupCont_fv`: `setupCont` reads no variable but `r` and `me`;
- `setupStart_me`: the start's thread binds `me` to `[meW]`;
- `lookup_setupEnv_me`: so does its environment.
-/

namespace Spike.Lib.Src

open CoreLang CoreTerm

/-- **The setup call's continuation reads only `me`** besides its binder `r`. -/
theorem setupCont_fv : ∀ y ∈ (Scc.Sem.exprFv SrcCalls.setupCont).filter (· != "r"), y = "me" := by
  decide

/-- The start's environment binds `me` to its one word. -/
theorem lookup_setupEnv_me (meW : TermRun.Word) (ty : Ty) (ws : List TermRun.Word)
    (h : TermRun.lookupE [("me", .ptr .pub .void, [meW]), ("u", .unit, [])] "me" = some (ty, ws)) :
    ws = [meW] := by
  simp [TermRun.lookupE] at h
  exact h.2.symm

/-- **The start's thread binds `me` to `[meW]`.** -/
theorem setupStart_me (cap : Nat) (meW : TermRun.Word) :
    (Scc.Sem.SrcSem.setupStart cap meW).ths[0]? =
      some { term := Scc.Sem.SrcSem.setupTerm, env := [("me", .ptr .pub .void, [meW]), ("u", .unit, [])] } :=
  rfl

end Spike.Lib.Src
