import Kraken.Promising.AArch64

/-!
# The one-word fragment of AArch64, as a decidable check

The syntactic fragment of `Scc/Cert/Rt/WideA64.lean` (`certExec_w8`: the
certification semantics of a program in it writes words only), on its own
so that the compiler can import it: `scc-arm`'s `--code` refuses a program
outside it (`Scc.Cert.WideCheckA64`), and `Scc.Sem.TargetA64`, which
`WideA64.lean` needs, brings WeakCore's root `main` into scope.
-/

namespace Scc.Cert.WideA64

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- **The one-word fragment, per operation**: `str x`/`stur x`, and
`stlr`/`swp`/`ld<op>`/`cas` of an 8-byte memory width; no other store-like
operation (`stp`, `strb`/`strh`/`sturb`/`sturh`, `str w`/`stur w`, the
exclusives `stxr`/`stxp`, `casp`). Every other operation is in. -/
def _root_.Operation.wideOk : {w : RegWidth} → Operation w → Bool
  | .W64, .STR .. | .W64, .STUR .. => true
  | .W32, .STR .. | .W32, .STUR .. => false
  | _, .STLR sz .. | _, .SWP _ sz .. | _, .CAS _ sz .. | _, .LDOP _ _ sz .. => sz == .W64
  | _, .STP .. | _, .STRB .. | _, .STRH .. | _, .STURB .. | _, .STURH .. => false
  | _, .STXR .. | _, .STXP .. | _, .CASP .. => false
  | _, _ => true

/-- **The one-word fragment, per directive**: an instruction of the fragment
(`Operation.wideOk`); labels and data are in. -/
def _root_.Directive.wideOk : Directive → Bool
  | .instr i => i.operation.wideOk
  | _ => true

/-- **A program of the one-word fragment**: every directive is
`Directive.wideOk`. Decidable; `scc --code` refuses a program for which it is
`false`. -/
def wideIn (prog : Program) : Bool := prog.all Directive.wideOk

end Scc.Cert.WideA64
