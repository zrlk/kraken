/-
**Certification witnesses on `ret0.w` (x86-64)**: concrete runs of the
canonical target (one thread slot, the layout `ret0Λ`, `Arch.tso`) that
refute three premises of `correctX64` (`Spike/Lib/X64Correct.lean`) as
stated on the M1 baseline. They are the targets of the lemmas replacing those
premises (the take-site decision; `sys_progress` for `SvcNoProm`). The
AArch64 versions are in the take-limbo tests.

- **(a) A promise outstanding at a system call** (against `SvcNoProm`): at
  the load configuration thread 0 can promise the `.data` word `6291472 := 80`
  (the pinned-region counter) under `Kernel.certExec`. The run then reaches the
  first system call (`rt_sigaction`, pc `4194366`) after 13 steps with the
  promise outstanding, and is still certified there.
- **(b) The take site's `nop` against the phase** (`TakePath.instr` /
  `SFacts.tkInstr` against `TakePath.site`): at the take site (pc `4196177`,
  `Tk` false, not at a system call) the `nop`'s instruction successor and
  `abi.skip` share the pc `4196178`, at which `Tk` holds. `instr` asks
  `Tk` false there and `site` asks it true, so for a pc-only `Tk`
  (`Spike.Lib.X64.Flow.Ret0.Inst.Tk`) the two cannot both hold. Resolved:
  `TakePath.instr` and `SFacts.tkInstr` now ask only off the transfer sites
  (`Kernel.siteAt abi μ s = none`), so the site's `nop` is no longer asked.
- **(c) A promise certifiable at the take site** (against `TakeNoProm`): at
  the site thread 0 can promise the TCB's self word `134217736 := 134217736`;
  after the promise it is at the site with the promise outstanding.

Status: (a) is answered by `Kernel.sys_progress` (`SvcNoProm` is now
`WriteNoProm`, promises excluded only at a `write`); (b) by the guard
`Kernel.siteAt abi μ s = none` of `TakePath.instr`; (c) by
`Kernel.certAfter_take` (`TakeNoProm` removed).

Not refuted here: `PromShared` on x86-64. At the two configurations above
the certified promises are all to shared words (the AArch64 take site also
certifies stores to the stack pool). Other `Pre` states were not
enumerated, so the premise stays open.
-/
import Scc.Sem.Test.RunX64
import Spike.Lib.X64Ret0I

namespace Spike.Test.X64CertWitness

open Kraken.Promising Kraken.Promising.X64 Scc.Sem.X64 Scc.Sem Scc.Sem.Test Scc.Sem.Test.RunX64
open SccCode (ret0Λ ret0Cells ret0Asm)

/-- A configuration of the canonical target. -/
abbrev Cfg := Config isa × Kernel.KState

/-- The transfer and abort sites of `ret0`. -/
def μ : RunMarks := marksIn ret0Cells

/-- The certification semantics (`CertOkC`'s). -/
def cx : isa.State → Option (EvTree isa.State) := Kernel.certExec abi

/-- `Tk` of `Spike.Lib.X64.Flow.Ret0.Inst`, as a Boolean. -/
def tk (s : isa.State) : Bool := Spike.Lib.X64.Flow.Ret0.Inst.ph (pcOf s) / 8 % 2 == 0

/-- The load configuration. -/
def load? : Option Cfg := (canonical 1).load ret0Asm ret0Λ

/-- Thread 0 is at the first system call. -/
def atSvc (c : Cfg) : Bool := c.1.threads[0]?.any fun t => abi.atSys t.st

/-- Thread 0 is at the take site. -/
def atTake (c : Cfg) : Bool := c.1.threads[0]?.any fun t => some (pcOf t.st) == μ.take

/-- The last message's location and value. -/
def lastMsg (m : Memory) : Option (Nat × Nat) := m.msgs.back?.map fun w => (w.loc.addr.toNat, w.val.toNat)

/-- **(a)** Each promise certified at the load configuration, then the run to
the first system call with it outstanding: the steps, the pc, whether thread
0 is at a system call, its promises, and whether it is still certified. -/
def svcWitness : List String :=
  match load? with
  | none => ["load refused"]
  | some c =>
    let (ps, _, _) := certifiedPromisesWith Arch.tso cx {} c.1 0 300
    ps.map fun (x : Config isa × TraceEv) =>
      let r := runUntil abi Arch.tso pcOf μ atSvc 4000 0 { cfg := (x.1, c.2) }
      match r.cfg.1.threads[0]? with
      | none => "no thread"
      | some t =>
        let (cr, _) := certifyWith Arch.tso cx {} t 0 r.cfg.1.mem 300
        s!"promise={lastMsg x.1.mem} steps={r.steps} pc={pcOf t.st} atSys={abi.atSys t.st} " ++
          s!"prom={t.prom} certified={cr.certified}"

/-- info: ["promise=(some (6291472, 80)) steps=13 pc=4194366 atSys=true prom=[1] certified=true"] -/
#guard_msgs in
#eval svcWitness

/-- The run to the take site. -/
def toTake : Option Cfg :=
  load?.map fun c => (runUntil abi Arch.tso pcOf μ atTake 4000 0 { cfg := c }).cfg

/-- **(b)** At the take site: its pc, `Tk`, whether it is a system call; the
`nop`'s instruction successors' pcs and `Tk`; `abi.skip`'s pc and `Tk`. -/
def siteWitness : String :=
  match toTake with
  | none => "no site"
  | some c =>
  match c.1.threads[0]? with
  | none => "no thread"
  | some t =>
    let succ := match stepThread Arch.tso c.1 0 with
      | some os => os.filterMap fun (x : Except String (Outcome isa)) => match x with
        | .ok o => some (pcOf o.thread.st, tk o.thread.st)
        | .error _ => none
      | none => []
    s!"site={pcOf t.st} Tk={tk t.st} atSys={abi.atSys t.st} nopSucc={succ} " ++
      s!"skip={(pcOf (abi.skip t.st), tk (abi.skip t.st))}"

/-- info: "site=4196177 Tk=false atSys=false nopSucc=[(4196178, true)] skip=(4196178, true)" -/
#guard_msgs in
#eval siteWitness

/-- **(c)** The promises certified at the take site, each with thread 0's pc
and promises after it. -/
def takeWitness : List String :=
  match toTake with
  | none => ["no site"]
  | some c =>
    let (ps, cr, _) := certifiedPromisesWith Arch.tso cx {} c.1 0 120
    s!"certified={cr.certified} bound={cr.boundHit}" :: ps.map fun (x : Config isa × TraceEv) =>
      s!"promise={lastMsg x.1.mem} pc={(x.1.threads[0]?.map (pcOf ·.st))} " ++
        s!"prom={(x.1.threads[0]?.map (·.prom))}"

/-- info: ["certified=true bound=false", "promise=(some (134217736, 134217736)) pc=(some 4196177) prom=(some [6])"] -/
#guard_msgs in
#eval takeWitness

end Spike.Test.X64CertWitness
