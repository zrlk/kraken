import Scc.Frontend
import Scc.Lower.Program
import Scc.Lower.Split
import Scc.Lower.Inv1
import Scc.Test.Src

/-!
# Block lengths of the test programs

The heaviest block (`Scc.IR.blockWeight`, the first block of a function with
its parameters) of every user function and thread trampoline, and of every
runtime routine, of `hello.w` and `wake.w`, on both architectures: all within
`maxBlockLen`, so the split (`Scc.Lower.Split`) leaves these programs as they
are.  The runtime routines are not split (see `Scc/Lower/Split.lean`); their
bound is listed here for information.
-/

namespace Scc.Test.Split

open Scc.IR Scc.Lower

/-- The heaviest block of `f`, the first with the parameters. -/
def maxWeight (f : Func) : Nat :=
  match f.blocks with
  | [] => 0
  | b :: bs => bs.foldl (fun m c => max m (blockWeight c)) (f.params.length + blockWeight b)

/-- The heaviest block over the user functions and trampolines, and over the
runtime routines, of a source text's lowering; whether every function is
`blocksOk`. -/
def weights (arch : Arch) (src : String) : Except String (Nat × Nat × Bool) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error _ => throw "frontend"
  let ir ← lowerProgram { arch } c
  let isRt (f : Func) : Bool := f.name.startsWith "scc_rt_" && !f.name.startsWith "scc_rt_thr_"
  let user := ir.funcs.filter (!isRt ·)
  let rt := ir.funcs.filter isRt
  pure (user.foldl (fun m f => max m (maxWeight f)) 0, rt.foldl (fun m f => max m (maxWeight f)) 0,
    ir.funcs.all blocksOk)

def hello : String := w_src% "Scc/Test/hello.w"
def wake : String := w_src% "Scc/Test/wake.w"

-- (user functions and trampolines, runtime routines, all `blocksOk`) for
-- hello x64, hello arm, wake x64, wake arm
/-- info: [Except.ok (34, 18, true), Except.ok (34, 18, true), Except.ok (26, 18, true), Except.ok (26, 18, true)] -/
#guard_msgs in
#eval [weights .x64 hello, weights .arm hello, weights .x64 wake, weights .arm wake]

/-! ## Piece labels are fresh

Piece `k ≥ 1` of block `l` is `l.k` (`pieceLabel`), which contains `.`; the
lowering's labels (`labName hint n`, the shape of every `freshLabel`) and
every label of the lowered test programs, runtime routines included, do not,
so no piece label can be one of them. -/

/-- Every block label of a source text's lowering. -/
def labels (arch : Arch) (src : String) : List Label :=
  match Frontend.run src with
  | .ok c => match lowerProgram { arch } c with
    | .ok ir => ir.funcs.flatMap fun f => f.blocks.map (·.label)
    | .error _ => []
  | .error _ => []

#guard ["L", "then", "else", "deep", "call", "cls", "clsnext", "clsdone", "spin", "locked", "is", "next"].all
  fun h => (List.range 1000).all fun n =>
    !(Inv.labName h n).contains '.' && (List.range 4).all fun k => (pieceLabel (Inv.labName h n) (k + 1)).contains '.'
#guard [labels .x64 hello, labels .arm hello, labels .x64 wake, labels .arm wake].all fun ls =>
  !ls.isEmpty && ls.all fun l => !l.contains '.'

-- Every function of hello and wake is `splittable` (so `blocksOk_splitFunc` applies).
#guard [hello, wake].all fun src => [Arch.x64, .arm].all fun arch =>
  match Frontend.run src with
  | .ok c => match lowerProgram { arch } c with
    | .ok ir => ir.funcs.all splittable
    | .error _ => false
  | .error _ => false

end Scc.Test.Split
