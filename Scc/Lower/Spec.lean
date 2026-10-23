import Scc.Lower.Program
import Scc.Cert.Place

/-!
# scc's pipeline as one function, ISA-independent half

The compiler theorem is stated about scc's own pipeline, from a checked
WeakCore program to the instruction list the emitter writes, as one pure
Lean function `lowerAll` per ISA (`Scc/Lower/SpecA64.lean`,
`Scc/Lower/SpecX64.lean`; one module each because no module may import both
emitters). This module holds the half the two share:

* `checkedOf p`: what the lowering reads of a program that passed the
  frontend (`Frontend.run`): the program, its entry point and its externs.
  The frontend's own checks (parse, type check, fragment diagnostics) are not
  repeated: `scc` runs them before (`Scc.Cli.run`), and the theorem's
  hypotheses take their place;
* `lowerIR cfg p`: the lowering to the IR (`lowerWithMarks` with the depth
  limit of `stackBudget`, as `lowerProgram`), with its placement trace and
  the budget, in one record `Lowered`; the command line calls it and then the
  ISA's emission (`Scc.Cli.run`), so that `scc` and `lowerAll` are the same
  code;
* `Listing`: what the command line needs of an ISA's emission besides the
  instruction list (the text, the placement data, the stack need table);
* `Accepted0`: the fragment the first compiler theorem covers.

All of it is total and reducible by the kernel: a certificate decides a
`Bool` about `lowerAll cfg p` by `decide`, which runs this code.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower

/-! ## The checked program -/

/-- What the lowering reads of a program that passed the frontend: the
program, its entry point (`Frontend.entryOf`, whose diagnostic positions
need the source text, here empty) and its externs; no `+` sites (only
`scc --report` reads them). On a program `Frontend.run` accepts, these are
the fields `Frontend.run` computes. -/
def checkedOf (p : Prog) : Except String Frontend.Checked := do
  let entry ← (Frontend.entryOf "" p).mapError (·.msg)
  pure { prog := p, entry, externs := Frontend.externs p, adds := [] }

/-! ## The lowering to the IR -/

/-- **A program lowered to the IR**: the checked program, the stack depth
limit (`stackBudget`), the IR program (`lowerWith` at that limit, as
`lowerProgram`) and the placement traces of its compiled code blocks (as
`lowerMarks`). -/
structure Lowered where
  checked : Frontend.Checked
  budget : StackBudget
  ir : Program
  marks : List (Sym × Array (Node × Point))

instance : Inhabited Lowered :=
  ⟨{ checked := { prog := [], entry := default, externs := [], adds := [] }, budget := default,
     ir := { funcs := [], data := [], start := "", abortFn := "" }, marks := [] }⟩

/-- **The lowering of a checked program to the IR** for configuration `cfg`
(see the module docstring). -/
def lowerIR (cfg : Config) (p : Prog) : Except String Lowered := do
  let c ← checkedOf p
  let budget ← stackBudget cfg c
  let (ir, marks) ← lowerWithMarks cfg c (some budget.frames)
  pure { checked := c, budget, ir, marks }

/-- `lowerIR`'s IR program is `lowerProgram`'s. -/
theorem lowerIR_ir (cfg : Config) (p : Prog) :
    (·.ir) <$> lowerIR cfg p = (checkedOf p >>= lowerProgram cfg) := by
  simp only [lowerIR, bind_pure_comp, Functor.map_map, map_bind]
  rfl

/-! ## What the command line needs of an emission -/

/-- What `scc` writes besides the instruction list, from an ISA's emission:
the assembler text, the placement data of the compiled functions (AArch64
only, `Scc.Cert.Place.FnPlace`) and the stack need table (`stackNeed`;
`none` for a program with non-tail recursion). -/
structure Listing where
  text : String
  places : Option (Except String (List Cert.Place.FnPlace)) := none
  need : Option (List (Sym × Nat × Nat))

/-! ## Reading the emitter's lines

The instruction lists keep the lines of the `.text` sections, which needs a
prefix test on the emitter's directive lines. Core's `String.trimAsciiStart`
and `String.startsWith` do not reduce in the kernel, and taking a computed
string apart into characters (`String.toList`) is slow there, so the test is
on the UTF-8 bytes. -/

/-- An ASCII white space byte: the bytes of the characters
`Char.isWhitespace` accepts (space, tab, carriage return, line feed). -/
def wsByte (b : UInt8) : Bool := b == 32 || b == 9 || b == 13 || b == 10

/-- `lineStarts s p`: the line `s`, leading white space dropped, starts with
`p`, for `p` of ASCII characters other than white space; the same as
`(s.trimAsciiStart.toString.startsWith p)`. (A byte below 128 in UTF-8 is
always a whole character, so dropping white space bytes drops white space
characters and an ASCII prefix of bytes is one of characters.) -/
def lineStarts (s p : String) : Bool :=
  p.toByteArray.data.toList.isPrefixOf (s.toByteArray.data.toList.dropWhile wsByte)

/-! ## The fragment of the first compiler theorem -/

/-- An atom of an `Accepted0` body: a variable bound by an earlier `let`
(`scope`), or an integer literal below `2^63`. -/
def atom0 (scope : List String) : At → Bool
  | .var x => scope.contains x
  | .lit n => decide (n < 2 ^ 63)
  | .unit => false

/-- An `Accepted0` body: straight-line `let`s of an atom or a checked `+` of
two atoms, ending in `ret` of an atom; `scope` the variables bound so far
(the parameter, `Unit`, is not one). -/
def body0 (scope : List String) : Expr → Bool
  | .let_ x (.atom a) e => atom0 scope a && body0 (x :: scope) e
  | .let_ x (.add a b) e => atom0 scope a && atom0 scope b && body0 (x :: scope) e
  | .ret a => atom0 scope a
  | _ => false

/-- The checked `+`s of a body (its `let`s of an addition). -/
def adds0 : Expr → Nat
  | .let_ _ (.add _ _) e => adds0 e + 1
  | .let_ _ _ e => adds0 e
  | _ => 0

/-- The most checked `+`s an `Accepted0` body may have: each gets a frame
slot of 8 bytes, and with the saved `x29`/`x30` pair the AArch64 frame
(`align16 (8 * slots + 16)`) must stay within 4095 bytes, so that the
prologue and the exit move `sp` by one immediate (`ctxOf_func0_frame_le`).
Exact: 508 slots give a frame of 4080 bytes, 509 one of 4096. -/
def maxAdds0 : Nat := 508

/-- **The fragment `Accepted0`**: one code block, `main(u : Unit) : Int`, no
type or index parameters, with an `Accepted0` body (`body0`): no calls, no
allocation, no output, no spawn, no `if`; at most `maxAdds0` checked `+`s. -/
def Accepted0 : Prog → Bool
  | [d] => d.name == "main" && d.tparams.isEmpty && d.idx.isEmpty && d.argTy == .unit &&
      d.retTy == .int && body0 [] d.body && decide (adds0 d.body ≤ maxAdds0)
  | _ => false

/-- The setup words of the main-thread runtime function (`Runtime.mainThreadF`):
`sw` with a setup block, else none. -/
def mainSetup (entry : Frontend.Entry) (sw : Nat) : Nat :=
  if entry.arg == .setupTid then sw else 0

end Scc.Lower
