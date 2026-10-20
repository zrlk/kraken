/-
**The runner-configuration check shared by the x64 `*Runner.lean`
companions**. Each companion's `runnerMatchesD` asks whether the
`.kl` runner's prepared configuration is `Config.init threads initMem` in
everything its theorem reads: per thread the executable, end, pc, registers,
private memory, **declarations** and no promise (`runnerSameD`); the initial
memory; no messages.

- `runnerMatchesDL src ths initMem`: the threads are `ths`, in order;
- `runnerMatchesDN src n s initMem`: `n` copies of `s`.
-/
import Kraken.Litmus.X64
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.X64

/-- A runner thread agrees with the state `s` (executable, end, pc,
registers, private memory, declarations; no promise). -/
def runnerSameD (t : Thread isa) (s : X64.State) : Bool :=
  t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
    t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem == s.st.1.dmem && t.st.decls == s.decls && t.prom.isEmpty

/-- The runner's configuration for `src` is `Config.init ths initMem`. -/
def runnerMatchesDL (src : String) (ths : List X64.State) (initMem : List (Loc × Val)) : Bool :=
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => (pr.config.threads.toList.length == ths.length &&
      (pr.config.threads.toList.zip ths).all fun p => runnerSameD p.1 p.2) &&
      pr.config.mem.init == initMem && pr.config.mem.msgs.isEmpty

/-- The runner's configuration for `src` has `n` threads, each agreeing with
`s`, and the initial memory `initMem`. -/
def runnerMatchesDN (src : String) (n : Nat) (s : X64.State) (initMem : List (Loc × Val)) : Bool :=
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => pr.config.threads.size == n && pr.config.threads.all (runnerSameD · s) &&
      pr.config.mem.init == initMem && pr.config.mem.msgs.isEmpty

end Kraken.Promising.X64.EnvG
