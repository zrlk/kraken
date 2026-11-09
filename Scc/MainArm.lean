import Scc.Cli
import Scc.Lower.SpecA64
import Scc.Cert.Arm
import Scc.Cert.WideCheckA64
import Scc.Cert.MapsCheckA64

/-!
# scc-arm

The AArch64 compiler behind the `scc` driver (`Scc.Cli.dispatch`): the
command line of `scc`, with the AArch64 emitter.
-/

def main (args : List String) : IO UInt32 :=
  Scc.Cli.run .arm (fun l => do
      let e ← Scc.Lower.A64.emitAll l
      -- refuse unless the tables put together from the constants and the split are the
      -- text's (`Scc.Cert.MapsA64.checkTables`); the CLI's configuration is always the
      -- default layout (`Scc.Cli.parseArgs` sets only the architecture), and a wrong
      -- configuration here could only cause a refusal
      Scc.Cert.MapsA64.checkTables { arch := .arm } e.low.ir e.items e.safepoints
      let lst ← e.listing
      -- the functions the placement check's block table splits the code
      -- into (`Scc.Cert.PlaceOK.A64.Data.splitFns`): one at the first label
      -- and one at each later label of a declared function
      let decl := e.low.ir.funcs.map (·.name) ++
        (if e.low.ir.growth.isSome then [Scc.IR.StackMap.morestackSym] else [])
      let labs := e.prog.filterMap fun | .label l => some l | _ => none
      let parts := match labs with
        | [] => 0
        | _ :: ls => 1 + (ls.filter decl.contains).length
      pure { lst with parts }) args none
    (some Scc.Cert.WideCheckA64.check)
