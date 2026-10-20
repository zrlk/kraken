/-
**Item 1: the AArch64 counter theorems already run
the runner's whole image.** Checks only (no new proofs).

Each counter `.kl` (`spinlock_swp{2,3}`, `spinlock_swpl{2,3}`,
`spinlock_cas{2,3}`, `ticketlock{2,3}`) has a single role: its `code` block
is exactly the worker of the theorem, and every thread the runner
(`Kraken.Litmus.AArch64.prepareProgram`) prepares runs that block, laid out
at `0x100000` with each directive its `fakeSize`, from cell `0` to the end
of the text. That is exactly the theorems' start predicates
(`exe = layout worker`, `pc = addrOf 0`, `endPc = addrOf worker.length`,
empty private memory, the base registers) at the runner's layout, so the
public theorems are already whole-image:

| theorem | worker | `.kl` |
|---|---|---|
| `SwpFinal.swp_counter_armv8` / `SwpPublic` | `swpWorker` | `spinlock_swp2.kl`, `spinlock_swp3.kl` |
| `SwplLock.swpl_counter_envG` | `swplWorker` | `spinlock_swpl2.kl`, `spinlock_swpl3.kl` |
| `CasSmoke.cas_counter_envG` | `casTtasWorker` | `spinlock_cas2.kl`, `spinlock_cas3.kl` |
| `TicketLock.ticket_counter_envG` | `tkWorker` | `ticketlock2.kl`, `ticketlock3.kl` |

- `runnerWhole src w regs` checks: the `code` block parses to `w`; every
  prepared thread has executable `Layout.ofSize 0x100000 fakeSize w w`, pc
  `addrOf 0`, end `addrOf w.length`, empty private memory, and the base
  registers `regs` (`X0`, `X1`, `X2`); the thread count is `n`.
- Not compared, as for every AArch64 theorem: the runner's `decls` (the
  theorems assume none; see `SwpConcrete.runnerDecls`).
-/
import Kraken.Promising.SLR.SwpConcrete
import Kraken.Promising.SLR.EnvG.ConcreteSwpl
import Kraken.Promising.SLR.EnvG.ConcreteCas
import Kraken.Promising.SLR.EnvG.TicketLockPublic
import Kraken.Litmus.AArch64

namespace Kraken.Promising.SLR.EnvG.A64WholeCounters

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- **The runner runs `w` whole**: `src`'s `code` block parses to `w`, and
its `n` prepared threads each run `w` laid out at `0x100000` (each directive
its `fakeSize`) from cell `0` to the end of the text, with empty private
memory and `X0, X1, X2 = regs`. -/
def runnerWhole (src : String) (w : Program) (n : Nat) (regs : UInt64 × UInt64 × UInt64) : Bool :=
  let e : Kraken.Executable Directive := (Kraken.Layout.ofSize 0x100000 Directive.fakeSize w) w
  let code := match Kraken.Litmus.parseProgram src with
    | .error _ => false
    | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
      | .ok prog => prog == w
      | .error _ => false
  let threads := match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram with
    | .error _ => false
    | .ok pr =>
      pr.config.threads.size == n &&
      pr.config.threads.all fun t =>
        t.st.exe == e && t.st.st.2 == e.addrOf 0 && t.st.endPc == e.addrOf w.length &&
          t.st.st.1.dmem.isEmpty && t.st.st.1.regs.X0 == regs.1 && t.st.st.1.regs.X1 == regs.2.1 &&
          t.st.st.1.regs.X2 == regs.2.2
  code && threads

/-- The `.kl` sources not yet included elsewhere. -/
def swp3Kl : String := include_str "../../../Examples/LockFree/AArch64/spinlock_swp3.kl"
def cas2Kl : String := include_str "../../../Examples/LockFree/AArch64/spinlock_cas2.kl"
def cas3Kl : String := include_str "../../../Examples/LockFree/AArch64/spinlock_cas3.kl"
def ticket2Kl : String := include_str "../../../Examples/LockFree/AArch64/ticketlock2.kl"
def ticket3Kl : String := include_str "../../../Examples/LockFree/AArch64/ticketlock3.kl"

/-! `swp_counter`, `swpl_counter`, `cas_counter` (`lock = 0x1000`,
`counter = 0x1100`) and `ticket_counter` (`next = 0x1000`,
`owner = 0x1100`, `counter = 0x1200`). -/

/-- info: (true, true) -/
#guard_msgs in
#eval (runnerWhole SwpConcrete.swpKl Kraken.AArch64.Examples.InvEnv.swpWorker 2 (0x1000, 0x1100, 0),
  runnerWhole swp3Kl Kraken.AArch64.Examples.InvEnv.swpWorker 3 (0x1000, 0x1100, 0))

/-- info: (true, true) -/
#guard_msgs in
#eval (runnerWhole ConcreteSwpl.swpl2Kl SwplLock.swplWorker 2 (0x1000, 0x1100, 0),
  runnerWhole ConcreteSwpl.swpl3Kl SwplLock.swplWorker 3 (0x1000, 0x1100, 0))

/-- info: (true, true) -/
#guard_msgs in
#eval (runnerWhole cas2Kl CasSmoke.casTtasWorker 2 (0x1000, 0x1100, 0),
  runnerWhole cas3Kl CasSmoke.casTtasWorker 3 (0x1000, 0x1100, 0))

/-- info: (true, true) -/
#guard_msgs in
#eval (runnerWhole ticket2Kl TicketLock.tkWorker 2 (0x1000, 0x1100, 0x1200),
  runnerWhole ticket3Kl TicketLock.tkWorker 3 (0x1000, 0x1100, 0x1200))

/-- The concrete workers of `ConcreteSwpl`/`ConcreteCas`/`SwpConcrete` are
the runner's threads (executable, pc, end, registers). -/
def sameAs (src : String) (s : AArch64.State) : Bool :=
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr => pr.config.threads.all fun t =>
      t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
        t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem.isEmpty

/-- info: (true, true, true) -/
#guard_msgs in
#eval (sameAs SwpConcrete.swpKl SwpConcrete.worker0, sameAs ConcreteSwpl.swpl2Kl ConcreteSwpl.swplWorker0,
  sameAs cas2Kl ConcreteCas.casWorker0)

end Kraken.Promising.SLR.EnvG.A64WholeCounters
