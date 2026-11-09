import Scc.Cli
import Scc.Lower.SpecX64
import Scc.Cert.X64
import Scc.Cert.Sizes
import Scc.Cert.WideCheckX64
import Scc.Cert.MapsCheckX64

/-!
# scc-x64

The x64 compiler behind the `scc` driver (`Scc.Cli.dispatch`): the command
line of `scc`, with the x64 emitter; a certificate gets the instruction sizes
GNU `as` assembles the text to (`Scc.Cert.Sizes`), and `--code` refuses a
program outside the one-word fragment (`Scc.Cert.WideCheckX64`).
-/

def main (args : List String) : IO UInt32 :=
  Scc.Cli.run .x64 (fun l => do
      let e ← Scc.Lower.X64.emitAll l
      -- refuse unless the tables put together from the constants and the split are the
      -- text's (`Scc.Cert.MapsX64.checkTables`); the CLI's configuration is always the
      -- default layout (`Scc.Cli.parseArgs` sets only the architecture), and a wrong
      -- configuration here could only cause a refusal
      Scc.Cert.MapsX64.checkTables { arch := .x64 } e.low.ir e.items e.safepoints
      let lst ← e.listing
      -- the functions the placement check's block table splits the code
      -- into (`Scc.Cert.PlaceOK.X64.Data.splitFns`): one at the first label
      -- and one at each later label of a declared function
      let decl := "_start" :: e.low.ir.funcs.map (·.name) ++
        (if e.low.ir.growth.isSome then [Scc.IR.StackMap.morestackSym] else [])
      let labs := (e.prog.getD []).filterMap fun | .label l => some l | _ => none
      let parts := match labs with
        | [] => 0
        | _ :: ls => 1 + (ls.filter decl.contains).length
      pure { lst with parts }) args (some Scc.Cert.Sizes.sizesOf)
    (some Scc.Cert.WideCheckX64.check)
