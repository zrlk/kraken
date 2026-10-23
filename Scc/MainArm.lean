import Scc.Cli
import Scc.Lower.SpecA64
import Scc.Cert.Arm
import Scc.Cert.WideCheckA64

/-!
# scc-arm

The AArch64 compiler behind the `scc` driver (`Scc.Cli.dispatch`): the
command line of `scc`, with the AArch64 emitter.
-/

def main (args : List String) : IO UInt32 :=
  Scc.Cli.run .arm (fun l => do (← Scc.Lower.A64.emitAll l).listing) args none
    (some Scc.Cert.WideCheckA64.check)
