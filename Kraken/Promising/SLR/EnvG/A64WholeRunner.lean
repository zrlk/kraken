/-
**Generic checks that a `.kl` file's runner runs a
given whole image**.

- `A64Whole.codeIs src img`: the `.kl`'s `code` block parses to exactly
  `img`;
- `A64Whole.runnerIs src ss`: the runner's prepared threads
  (`Kraken.Litmus.AArch64.prepareProgram`) are, in order, the states `ss`:
  executable, pc, end, the whole register file, and an empty private memory.
  (Not compared: the runner's `decls`; the whole-image theorems assume no
  declarations.)

The per-program `codeMatchesW…`/`runnerMatchesW…` of the whole-image
concretes are these at the program's image and threads.
-/
import Kraken.Litmus.AArch64
import Kraken.Promising.SLR.EnvG.RelPureEnvA64

namespace Kraken.Promising.SLR.EnvG.A64Whole

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The `code` block of the `.kl` source `src` parses to `img`. -/
def codeIs (src : String) (img : Program) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == img
    | .error _ => false

/-- A runner's thread runs the state `s`'s executable, pc, end, registers,
with an empty private memory. -/
def sameAsRunner (t : Thread isa) (s : AArch64.State) : Bool :=
  t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
    t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem.isEmpty

/-- The runner's threads for the `.kl` source `src` are `ss`, in order. -/
def runnerIs (src : String) (ss : List AArch64.State) : Bool :=
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr => pr.config.threads.toList.length == ss.length &&
      (pr.config.threads.toList.zip ss).all fun (t, s) => sameAsRunner t s

end Kraken.Promising.SLR.EnvG.A64Whole
