/-
**The extern step `emit` as a source step** under WeakCore's hook, with no
ISA in its imports: `emit_src` of `Spike/Test/OutToySrc.lean` (whose toy
imports the AArch64 consumer), restated so that ISA-generic source facts
(`Spike/Lib/PrintSrc.lean`) can be imported next to either ISA's modules.

- `emit_src`: thread 0 at `let x = ext emit a in e`, with no promises, takes
  the extern step; its trace is the growth of `srcObs` (the byte, and
  `main`'s exit if `e` is a `ret`).
-/
import Scc.Sem.SrcOutProto
import Spike.Lib.SrcRun

namespace Spike.Lib.SrcEmit

open CoreLang CoreTerm TermRun TermExtStep
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib

/-- **The extern step `emit` of thread 0** under WeakCore's hook, with no
promises: its trace is the growth of `srcObs`. -/
theorem emit_src {P : SrcParams} {p : Prog} (hP : UsesWc P p) {s : Cfg} {th : TTh} {x : String} {a : At}
    {e : Expr} {rt : Ty} {ws : List Word} (hi : s.ths[0]? = some th) (ht : th.term = .let_ x (.ext .emit a) e)
    (hp : th.promises = []) (ha : evalAt th.env a = some (rt, ws)) :
    (source P p).step 0 s
      ((srcObs P.hooks.trace (extCfg s 0 th x .emit e ws [])).drop (srcObs P.hooks.trace s).length)
      (extCfg s 0 th x .emit e ws []) := by
  refine ⟨mainExit_of_not_ret hi (fun b h => by rw [ht] at h; cases h), .inr (.inr ?_), rfl⟩
  rw [hP]
  exact ⟨x, .emit, a, e, th, rt, ws, [], hi, ht, fun _ => hp, ha, rfl,
    ⟨_, .refl _, by rw [extCfg_noPromises hi, hp]; rfl⟩, rfl⟩

end Spike.Lib.SrcEmit
