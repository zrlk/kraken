import Scc.Emit.X64

/-!
# Each function's first local label number (x86-64)

Moved out of `Scc/Cert/Code1X64.lean` (unchanged, same namespace) so that the
A9 checker (`Spike.Lib.LowerX64.Checks`), which `Code1X64` imports, can use
`starts` as well. The x86-64 emitter numbers each function's local labels
`.L<f>.xN` from 0 (`emitFuncAt`, as on AArch64): `starts` gives every
function the number 0, `fnLabs` counts the labels a function takes, and
`startsOk` checks the numbering against the emitter (by evaluation, in the
tests).
-/

namespace Scc.Cert.Code1X64

/-! ## The local labels' numbering -/

/-- The local labels (`freshL`) the emitter takes for an instruction, with
safepoints recorded (`maps`) or not (an `addChk`'s: its fall-through's). -/
def instLabs (maps : Bool) : Scc.IR.Inst → Nat
  | .bin .udiv _ _ _ | .bin .urem _ _ _ => 2
  | .bin .sdiv _ _ _ | .bin .srem _ _ _ => 3
  | .clone .. => 1
  | .addChk .. => 1
  | .call .. => if maps then 1 else 0
  | _ => 0

/-- The local labels the emitter takes for a function: its instructions',
its `ret` terminators' (the return site's), and the grow stub's safepoint (a
stack-checked function with growth). -/
def fnLabs (ir : Scc.IR.Program) (f : Scc.IR.Func) : Nat :=
  (f.blocks.map fun b => (b.insts.map (instLabs ir.growth.isSome)).sum).sum +
    (f.blocks.filter (·.term matches .ret _)).length +
    if f.checkStack && ir.growth.isSome then 1 else 0

/-- **Each function with its first local label number**: the emitter numbers
each function's local labels from 0 (`emitFuncAt`), so every function of
`fs` gets `n` (0 from `fnCode1Ok`). Kept, trivial, so that the checkers'
interface (`(f, n) ∈ starts ir 0 ir.funcs`) does not move. -/
def starts (ir : Scc.IR.Program) : Nat → List Scc.IR.Func → List (Scc.IR.Func × Nat)
  | _, [] => []
  | n, f :: fs => (f, n) :: starts ir n fs

/-- `startsOk`'s walk: each function's `emitFuncAt` passes the number `n`
on. -/
def startsOkAux (ir : Scc.IR.Program) (areas : List (Scc.IR.Sym × Nat)) : Nat → List Scc.IR.Func → Bool
  | _, [] => true
  | n, f :: fs =>
    match Scc.Emit.X64.emitFuncAt ir areas f n with
    | .ok (_, n', _) => n' == n && startsOkAux ir areas n' fs
    | .error _ => false

/-- **`starts` is the emitter's numbering** of `ir` (checked by evaluation
in the tests; A12 does not depend on it: a wrong number fails `segIn`). -/
def startsOk (ir : Scc.IR.Program) : Bool :=
  match Scc.Emit.X64.emitPre ir with
  | .ok areas => startsOkAux ir areas 0 ir.funcs
  | .error _ => false

end Scc.Cert.Code1X64
