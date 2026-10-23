import Scc.Cli

/-!
# scc: WeakCore to assembler

The `scc` executable: reads a WeakCore program (`.w`) and writes GNU assembler
for x64 or AArch64 Linux.  See `Scc/README.md`.  It is a driver: the compilers
are `scc-x64` (`Scc/MainX64.lean`) and `scc-arm` (`Scc/MainArm.lean`), which it
runs (`Scc.Cli.dispatch`).
-/

def main (args : List String) : IO UInt32 := Scc.Cli.dispatch args
