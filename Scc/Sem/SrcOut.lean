/-
**The source with output and a setup block** (trusted statement text).

This file adds to the source side of the `scc` statement (`Scc/Sem/SrcExt.lean`) the
definitions a statement about a program that prints, or that starts with a setup block,
reads. Everything here is a definition; nothing in it is assumed. `source P p` and
`SrcParams` are unchanged, and the parameters of the existing theorems (`Spike.Lib.srcP1`,
hook `SrcHooks.none`, start `mainInit`) are unaffected.

- `evOf`, `traceOf`: WeakCore's events (`TermRun.Event`, appended to `TermRun.Cfg.trace`
  by its extern step) as the statement's `Ev`: `out b ↦ out (b % 256)`,
  `exit n ↦ exit (n % 256)`, device events dropped.
- `ExtBy p k arch i`: WeakCore's extern step (`TermExtStep.Ext`: `emit`, `exitEv`,
  `current`) taken by thread `i`.
- `wcHooks p k arch`: the source hook made of the two (`ext := ExtBy`,
  `trace := traceOf`).
- `setupStart`, `setupInit`: the start before the setup block: thread 0 calls `rodata` on
  ``, pairs its result with the main thread's `Ptr pub Void` word and enters `main`.
- `tidStart`, `tidInit`: the start of `main(a : Ptr pub Void)`: thread 0 enters `main` on
  the main thread's word.
- `tidStartT`, `setupStartT`: the starts of `main(a : ThreadId)` and
  `main(a : S * ThreadId)`: the main thread holds its own `ThreadId` (`tidLbl` set, the
  box at its first label, `mainTidLbl`), so `unpark` of it names thread 0.
- `progInit p cap`: the start of program `p`, chosen by `main`'s argument type as `scc`'s
  entry check (`Scc.Frontend.entryOf`) classifies it.
- `srcP1o arch p`: the single-thread parameters of `p` with output: memory model `arch`,
  one thread, start `progInit p 1`, hook `wcHooks p .all arch`.
- `srcPo n arch p`: as `srcP1o` with `n` threads (capacity and label stripe `n`).
-/
import Scc.Sem.SrcExt

namespace Scc.Sem.SrcSem

open CoreLang CoreTerm TermRun

/-! ## Events -/

/-- **A WeakCore event as an observable event**: an output byte (`emit` takes a `U8`, so
on well-typed runs `b < 256` and the `% 256` is the identity), the exit with its code
(already `% 256`, `TermRun.exitCode`). -/
def evOf : TermRun.Event → Option Ev
  | .out b => some (.out ⟨b % 256, Nat.mod_lt _ (by decide)⟩)
  | .exit n => some (.exit ⟨n % 256, Nat.mod_lt _ (by decide)⟩)
  | _ => none

/-- **The observable events of a configuration**: its event list, mapped by `evOf` (device
events dropped). -/
def traceOf (c : TermRun.Cfg) : List Ev := c.trace.filterMap evOf

/-! ## The extern step -/

/-- **WeakCore's extern step taken by thread `i`**, in program `p` at knobs `k` and memory
model `arch`: the premises of `TermExtStep.Ext.mk` with the thread exposed. Thread `i` is at
`let x = ext n a in e`; if `n` needs an empty promise set (`exitEv`, `current`) it has
none; `a` evaluates to the words `ws`; the configuration after the step (`extCfg`: bind
the result `rs` that `n` admits, append the events of `n` to the trace) certifies thread
`i`; and `c'` is that configuration after the threads `n` wakes (`wake`). -/
def ExtBy (p : Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (i : Nat) (c c' : TermRun.Cfg) : Prop :=
  ∃ (x : String) (n : ExtName) (a : At) (e : Expr) (th : TTh) (rt : Ty) (ws rs : List Word),
    c.ths[i]? = some th ∧ th.term = .let_ x (.ext n a) e ∧ (ExtNeedsNoProm n th → th.promises = []) ∧
    evalAt th.env a = some (rt, ws) ∧ n.Admits i ws c.trace rs ∧
    Certified p k arch (extCfg c i th x n e ws rs) i ∧ c' = wake (extCfg c i th x n e ws rs) i (relView th.vs) n ws

/-- **The source hook of WeakCore's extern step**, for program `p`, knobs `k` and memory
model `arch` (those of the parameters it is used in): extern steps are `ExtBy`, the event
list is `traceOf`. -/
def wcHooks (p : Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) : SrcHooks :=
  ⟨ExtBy p k arch, traceOf⟩

/-! ## Starts -/

/-- The term thread 0 starts at before a setup block: call `rodata` on `u`, pair its
result with `me`, enter `main` on the pair. -/
def setupTerm : Expr :=
  .let_ "r" (.call "rodata" [] (.var "u")) (.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a")))

/-- **The start before the setup block**: one thread at `setupTerm`, `u` the unit and
`me` the main thread's `Ptr pub Void` word `meW`; empty memory; label stripe width
`cap`. The setup is an ordinary call: its `ret` returns into the wrapper, so `main` has
not returned (`mainExit = []`) until `main` itself returns. -/
def setupStart (cap : Nat) (meW : Word) : TermRun.Cfg where
  mem := #[]
  ths := #[{ term := setupTerm, env := [("me", .ptr .pub .void, [meW]), ("u", .unit, [])] }]
  cap := cap

/-- The starts before the setup block: `setupStart` at any word for `me`. -/
def setupInit (cap : Nat) : TermRun.Cfg → Prop := fun s => ∃ meW, s = setupStart cap meW

/-- **The start of `main(a : Ptr pub Void)`**: one thread entering `main` on the main
thread's word `meW`; empty memory; label stripe width `cap`. -/
def tidStart (cap : Nat) (meW : Word) : TermRun.Cfg where
  mem := #[]
  ths := #[{ term := .tail "main" [] (.var "me"), env := [("me", .ptr .pub .void, [meW])] }]
  cap := cap

/-- The starts of `main(a : Ptr pub Void)`: `tidStart` at any word for `me`. -/
def tidInit (cap : Nat) : TermRun.Cfg → Prop := fun s => ∃ meW, s = tidStart cap meW

/-- **The main thread's own `ThreadId`** in a start of label stripe `cap`: its box label
`freshLabel 0 (max cap 1) 0 0` (thread 0's first allocation, as `current` would allocate
it, `TermRun.curCfg`), and the word `cst (.loc ⟨l, 0⟩ 0)` naming it (`thrOfTid`). -/
def mainTidLbl (cap : Nat) : WeakMem.AllocLabel := freshLabel 0 (max cap 1) 0 0

/-- **The start of `main(a : ThreadId)`**: one thread entering `main` on its own
`ThreadId` (`tidLbl` set, one allocation made: the box); empty memory; stripe `cap`. -/
def tidStartT (cap : Nat) : TermRun.Cfg where
  mem := #[]
  ths := #[{ term := .tail "main" [] (.var "me"), env := [("me", .tid, [cst (.loc ⟨mainTidLbl cap, 0⟩ 0)])],
             tidLbl := some (mainTidLbl cap), nalloc := 1 }]
  cap := cap

/-- **The start before the setup block of `main(a : S * ThreadId)`**: as `setupStart`,
with `me` the main thread's own `ThreadId` (as `tidStartT`). -/
def setupStartT (cap : Nat) : TermRun.Cfg where
  mem := #[]
  ths := #[{ term := setupTerm, env := [("me", .tid, [cst (.loc ⟨mainTidLbl cap, 0⟩ 0)]), ("u", .unit, [])],
             tidLbl := some (mainTidLbl cap), nalloc := 1 }]
  cap := cap

/-- **The start of program `p`**, by `main`'s argument type (the classes of
`Scc.Frontend.entryOf`): `Unit` starts at `main` (`mainInit`), `Ptr pub Void` at `main`
on the thread's word (`tidInit`), `S * Ptr pub Void` before the setup block
(`setupInit`), `ThreadId` at `main` on the thread's own `ThreadId` (`tidStartT`),
`S * ThreadId` before the setup block with it (`setupStartT`). Any other program has no
start. -/
def progInit (p : Prog) (cap : Nat) : TermRun.Cfg → Prop :=
  match p.find? (·.name == "main") with
  | some d =>
    match d.argTy with
    | .unit => mainInit cap
    | .ptr .pub .void => tidInit cap
    | .prod _ (.ptr .pub .void) => setupInit cap
    | .tid => (· = tidStartT cap)
    | .prod _ .tid => (· = setupStartT cap)
    | _ => fun _ => False
  | none => fun _ => False

/-! ## Parameters -/

/-- **The single-thread source parameters of program `p` with output**: the memory model
`arch`, all knobs, one thread, the program's start (`progInit p 1`), WeakCore's extern
step and event list (`wcHooks p .all arch`). -/
def srcP1o (arch : WeakMem.Arch) (p : Prog) : SrcParams where
  arch := arch
  cap := 1
  init := progInit p 1
  hooks := wcHooks p .all arch

/-- **The source parameters of program `p` with output and `n` threads** (`n ≥ 1`; the
statement takes `n` at least the target's thread slots and above `B.threads`): as
`srcP1o`, with capacity and label stripe `n`. -/
def srcPo (n : Nat) (arch : WeakMem.Arch) (p : Prog) : SrcParams where
  arch := arch
  cap := n
  init := progInit p n
  hooks := wcHooks p .all arch

end Scc.Sem.SrcSem
