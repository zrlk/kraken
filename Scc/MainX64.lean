import Scc.Cli
import Scc.Lower.SpecX64
import Scc.Cert.X64
import Scc.Cert.Sizes
import Scc.Cert.WideCheckX64

/-!
# scc-x64

The x64 compiler behind the `scc` driver (`Scc.Cli.dispatch`): the command
line of `scc`, with the x64 emitter; a certificate gets the instruction sizes
GNU `as` assembles the text to (`Scc.Cert.Sizes`), and `--code` refuses a
program outside the one-word fragment (`Scc.Cert.WideCheckX64`).
-/

def main (args : List String) : IO UInt32 :=
  Scc.Cli.run .x64 (fun l => do (← Scc.Lower.X64.emitAll l).listing) args (some Scc.Cert.Sizes.sizesOf)
    (some Scc.Cert.WideCheckX64.check)
