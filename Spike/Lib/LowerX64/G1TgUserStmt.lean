/-
**The user functions' segments, as a statement** (x86-64): scc's x86-64
code for each user function of an `Accepted2` program (`funcs2`), emitted
in the lowered program (`progOf`), is a user function's segment
(`UserPart`). The branch-target check on the whole output
(`Spike/Lib/LowerX64/G1TgOk.lean`) takes it as a hypothesis.

- `UserPartStmt`: the statement.
-/
import Spike.Lib.LowerX64.G1TgSeg
import Spike.Lib.LowerX64.EmitLabels
import Spike.Lib.LowerX64.LowerProgC2X

namespace Spike.Lib.LowerX64

/-- **Each user function's code is a user function's segment**: at every
configuration and `Accepted2` program, whatever its lowered blocks (`ws`)
and runtime functions (`rt`), each user function's directives in the
lowered program, at every argument area table and passed number, form a
`UserPart`. -/
def UserPartStmt : Prop :=
  ∀ (cfg : Scc.Config) (p : CoreTerm.Prog) (ws : List Spike.Lib.LowerNode.Low2) (rt : List Scc.IR.Func),
    Scc.Lower.Accepted2 p = true →
    Spike.Lib.LowerNode.Pairwise2 (Spike.Lib.LowerNode.LowC2 p cfg.layout.obj) (Spike.Lib.LowerNode.compiled2 p) ws →
    Scc.Lower.Inv.rtFuncs cfg.arch cfg.layout (Spike.Lib.LowerNode.entry2 p) (Spike.Lib.LowerNode.setupWords2 p)
      (Spike.Lib.LowerNode.setupMask2 p) = .ok rt →
    ∀ f ∈ Spike.Lib.LowerNode.funcs2 p ws, ∀ (areas : List (Scc.IR.Sym × Nat)) (n : Nat)
      (r : List Scc.Emit.X64.Item × Nat × List Scc.Emit.X64.Map),
    Scc.Emit.X64.emitFuncAt (Scc.Lower.Inv.progOf cfg.layout rt (Spike.Lib.LowerNode.funcs2 p ws)) areas f n = .ok r →
    UserPart (dOf r.1)

end Spike.Lib.LowerX64
