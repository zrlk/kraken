/-
**The one-thread consumer on the canonical x86-64 target** (`canonical 1`),
the twin of `Spike/Lib/A64Consumer.lean` over `X64.isa` under `Arch.tso`
(`Scc.Sem.X64.abi`, the fragment `Scc.Cert.WideX64.WideSt`,
`Spike/Lib/X64Ext.lean`): `Correct` for a one-thread program from an invariant of `Out` rows
(`Spike/Lib/Seg.lean`) over the one-word fragment (`WideSt`), the one-thread
memory invariant (`Scc.Sem.Inv1`), and explicit node and source obligations.

Contents:

- From `Spike/Lib/Consumer1.lean` (the ISA-free part): `SrcMem` and the
  source steps of the memory rows (`src_store_step`, `src_load_step`,
  `src_swap_step`), `OwnMsgs`, `MemIn`, `MemFits`, `HoldInv`, `Refusal`,
  `TI` and small lemmas.
- `Nodes`, `SrcSafe`: the node obligations on an explicit fragment `I` and
  the source side's safety (`SrcSafe.cell`: dereferenced cells exist;
  `SrcSafe.xchg`: exchanged cells exist).
- `AbortPath`: the abort path, a phase `Ab` of the thread states
  past a refused `write`, entered only by the refusal; a pair at an abort
  site is at the `writeErr` one in the phase, or at the `overflow` one with
  the source thread about to overflow (`OvfReady`, `EnvSmall`).
- `Owned`, `TakePath`: the take path, a phase `Tk` of the thread states past
  the take of the stack range `rS` (in the pool), entered only at the take
  site, `rS` owned in it.
- `KS`, `HeldOk`: the kernel state of the one thread, and the ranges held
  (none before the take, `rS` after it).
- `Pre`, `Post`, `R`: the relation; `pre_load`: it holds at load;
  `init_of_load`: at the target's load of a parsed text.
- `pre_step`, `r_step`: every step from `R` is matched by a source run with
  its observable events, landing in `R` (an instruction by its `Out` row,
  the load and store rows by `SrcMem`'s source steps, an exchange's load
  by a stutter into the hold and its store by `src_swap_step`; a promise by a
  stutter; a `write` byte to `fd ≠ 1` by a stutter, a return by `Out.sys`,
  `exit_group` by `Out.sys`'s `SysOk` off the abort sites, an abort by a stutter
  into `Post`; the take by `TakePath.site`'s local run, certified after it
  by `Kernel.certAfter_take` (the pool's bytes zero); no spawn or release).
- `step_take`, `fresh_of`: the step at the take site is the take, and the
  stack range is fresh there.
- `PreCore`, `pre_core`, `pre_core_promise`, `core_step`, `core_sys`,
  `core_site`, `core_ins`: the core of `Pre` for a thread and memory (its message
  clauses `MsgsExcept` over the outstanding promises), from `Pre` and from
  `Pre` with a certified promise, kept by an instruction step off a system
  call and by a certification step at one or at the take site
  (`stepG_of`'s `hins`, `hsys` and `hsite`, `Spike/Lib/X64PromShared.lean`).
- `stepSim`: the step-wise simulation (`Scc/Sem/ExtSim.lean`).
- `OwnMsgs` (`Consumer1`): every message is thread 0's (kept in `Pre` and `Post`).
- `wit`, `components_one`, `r_components`: the explicit witness of a
  related pair (`Components.ofMemRelP`).
- `MemIn`, `loadMem_in`, `shared_of_wordAddr`: the memory in the layout
  (kept in `Pre` and `Post`).
- `MemFits`: every target value 64-bit (kept in `Pre`; a load's register
  receives the whole value read, `valRep_setWidth_of_fits`).
- `OwnOk` (`ExtRows`): the runtime words the thread owns (`own`,
  `msOf`'s `MemSide.own`) read as their values (kept in `Pre`, so a runtime
  read of one returns its value: `ExtRows.out_local`, `ExtRows.out_mem`):
  at load each at its initial value (`hown0`, `OwnInit`, `ownOk_init`),
  kept by an instruction (`Nodes.ownInstr`,
  `ownOk_step`), a promise (`ownOk_promise`), a `write` byte, a return
  (`Nodes.ownSys`) and the take (`Nodes.ownTake`).
- `MemInv G`: every target value one the runtime memory's value invariant
  `G` allows (kept in `Pre`; the memory side's `G`, so a runtime load reads
  a `G` value, `Out.rtLoad`): a runtime store's value is `G`
  (`Out.rtStore`), a store to a placed word is (`hGpl`, with
  `heapData_of_wordAddr`), and so is a promise (`PromShared`).
- `WriteNoProm`, `pre_progress`, `post_progress`,
  `r_progress`: progress from `R` (no fault; thread 0 steps by its `Out`
  row's outcome, the first step of its certification, the take at the take
  site, or the kernel's return or `exit_group`, at an abort site as the
  abort).
- `TI`, `ti_load`, `ti_step`, `ti_run`, `r_abort`: the abort clause (in the
  phase the trace has a `writeErr`, so the abort is justified).
- `r_memIn`, `inLayout_of_memIn`, `correctK`: `Correct`
  (`correct_of_stepSim`).

## Open hypotheses

- `WriteNoProm`: no outstanding promise at a `write`. At the other calls a
  certified thread with promises has a kernel step after which it is
  certified (`Kernel.sys_progress`, `Kernel.prom_nil_of_exit`); a
  certified thread at a `write` has none (`Kernel.prom_nil_of_write`: the
  certification has no branch there), so this follows from `Pre`'s
  certification (not yet derived here). The consumers'
  programs reach a `write` only on the abort path, after which only private
  stores and `exit_group` follow; the discharge is per program (open: once
  for all accepted programs).
- `PromShared`: a certified promise is to a shared region (for `MemIn`) of a
  value `G` allows (for `MemInv G`); the
  planned discharge is a certification fragment (a superset of the
  fragment closed under every outcome, its stores to shared regions).
- `SrcMem`: the source steps of the load and store rows; discharged
  (`srcMem`, `Spike/Lib/Consumer1.lean`; `correctX64` in
  `Spike/Lib/X64Correct.lean` is `correctK` without it).
- `rd` total (`∀ w, rd w`, in `pre_step`): the memory side's read
  predicate is not yet tied to the source's loads.
- `SysOk` (in `Nodes.out`'s `Out.sys`): a temporary restriction (no
  output) until output events are matched.
- `Nodes.noAlloc`: a temporary restriction (no `newBuf` binding) until the
  allocation row is matched; placing the fresh label needs an allocator
  invariant.
- `hG0`, `hGpl` (in `correctK`): per-program data on the runtime memory's
  value invariant `G` (it holds of the loaded memory; it allows every value
  at a word of the heap or the static image). For `Scc.Sem.FixG` with its
  fixed words pinned: `memInv_fixG_load` and `fixG_of_placed`
  (`Scc/Sem/FixInv.lean`).
- `AbortPath`, `hab0` (in `correctK`): per-program data (the abort path's
  phase, off it at load); with `Ab` false, no pair is at an abort site.
- `TakePath`, `htk0` (in `correctK`): per-program data (the take path's
  phase, off it at load); with `Tk` false, no pair is at the take site.
- `own`, `hown0` (in `correctK`), `Nodes.ownInstr`, `Nodes.ownSys`,
  `Nodes.ownTake`: per-program data on the runtime words owned (at load each
  at its initial value, `OwnInit`); `own := fun _ => []` discharges them
  (`OwnTree.nil`, `OwnInit.nil`).
- `Nodes.svc`, `msOf`'s `mp`: per-program data (the system calls are at
  `syscall` cells; runtime stores are to shared regions).

## Accepted boundary

The parse and the load (`init_of_load`, `correctK`): the text's `.text`
is laid out to the code cells `cells` at the text's sizes and its data
sections parse to `secs` (`cellsOf`,
`dataSections`), the target's load succeeds, the static link's image check
(`imageOk`, `StaticSyms`), the program is in the one-word fragment
(`wideIn` of the cells' directives), and the start pair is in the fragment; each checked per program.

## Differences from the AArch64 consumer

- A system call is at a `syscall` cell (`Nodes.svc`; `out_sys` by
  `exec_syscall`), which clobbers `%rcx` and `%r11` (`abi.ret`); at
  `arch_prctl(ARCH_SET_FS)` the kernel's successor sets the `%fs` base first
  (`certSuccs_archSetFs`), covered by `Out.sys` as every other call.
- The load is cell-based: the parse boundary is `cellsOf asm = some cells`
  (the text laid out at its size table) with `dataSections asm.text`, and
  the loaded thread is `threadAt` of the cells (`load_of_parsed`,
  `loadParsed`).
-/
import Spike.Lib.X64Ext
import Spike.Lib.SrcRun
import Scc.Sem.ExtSim
import Scc.Sem.StartX64
import Scc.Sem.SysX64
import Scc.Sem.LoadX64
import Scc.Sem.Fits
import Spike.Lib.Consumer1
import Spike.Lib.OvfAbort
import Scc.Sem.CertLift
import Scc.Sem.CertSys

namespace Spike.Lib.X64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1

variable {P : SrcSem.SrcParams} {p : Prog} {E : Entry}

/-! ## The node obligations -/

/-- The target: the canonical x86-64 target with one thread slot. -/
abbrev T : Target := canonical 1

/-- **A target on `T`'s machine**: texts `A`, load `ld`, label resolution
`rs`. `T` is one (`TOn T.Asm T.load T.resolve`), and so is the target on
parsed texts (`parsedTarget`, `Scc/Sem/LoadX64.lean`). -/
abbrev TOn (A : Type) (ld : A → Scc.Sem.Layout → Option T.M.Cfg)
    (rs : A → Scc.Sem.Layout → String → Option Nat) : Target := ⟨T.M, A, ld, rs⟩

/-- The labels' placement and sizes (they grow with allocation). -/
abbrev Lbl := WeakMem.AllocLabel → Option Nat

/-- The labels' sizes in words. -/
abbrev Lsize := WeakMem.AllocLabel → Nat

/-- **The register environment of a control is placed** in the target state
`s` (`CompRest`'s `env_rep` and `env_total` for one frame): a map from
variable and word index to a word place, each placed word represented, every
word of a free variable of the term placed, and an immediate only where the
layout's table has that constant for the term (`CompRest.env_imm`). -/
def Placed (Λ : Scc.Sem.Layout) (lbl : Lbl) (s : State) (c : Ctl) : Prop :=
  ∃ envm : String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId),
    (∀ x ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k wd wp, ws[k]? = some wd → envm x k = some wp →
      WordPlaceRep (machine (kernel 1)) lbl s wp wd.val) ∧
    (∀ x ∈ exprFv c.term, ∀ ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k < ws.length,
      ∃ pl, envm x k = some pl) ∧
    (∀ x k n, envm x k = some (.imm n) → Λ.imms c.term x k = some n)

/-- **The kernel state as loaded, without the entry stack**: one slot,
running, the layout's regions mapped (`Kernel.KState.init` but for the
initial stack, which only private accesses reach). The loaded state at an
entry state `E` maps more (`KS`, `mapped_KS`), so an access mapped here is
mapped there at every `E`. -/
def K0 (Λ : Scc.Sem.Layout) : Kernel.KState :=
  { slots := #[.run 0], pool := Λ.stackPool, rw := [Λ.data, Λ.heap, Λ.stackPool, Λ.pinned],
    ro := [Λ.code, Λ.rodata] }

/-- **The fragment** of thread states paired with source controls, under a
placement and sizes of the labels. -/
abbrev Inv := Lbl → Lsize → Frag isa

/-- **The runtime words a thread state owns**, with their values
(`MemSide.own`: a runtime read of one returns its value). -/
abbrev Own := State → List (Loc × Val)

/-- **The memory side of a placement** (read side `rd`, value invariant
`G`, owned words `own`, marks `μ`, layout `Λ`, labels `lbl`, sizes
`lsize`): the labels' memory side (`MemSide.ofLabels`) under the kernel
model, with the runtime words each state owns (`own`); the runtime
accesses to the locations mapped in the loaded kernel state and, for
writing, in a shared region (`mp`); the abort sites at the marks' resolved
abort sites (`abortAt`); the placed pairs under the layout (`pl`); and the
output's byte step `bo` (default: none). -/
def msOf (Λ : Scc.Sem.Layout) (μ : Marks) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop) (own : Own)
    (lbl : Lbl) (lsize : Lsize) (bo : State → Nat → Ctl → (Ctl → Prop) → Prop := fun _ _ _ _ => False) :
    MemSide isa :=
  MemSide.ofLabels rd lbl lsize (some abi) G (own := own)
    (mp := fun L w => Kernel.mapped (K0 Λ) w L = true ∧ (w = true → LocIn Λ.shared L))
    (abortAt := fun s => ∃ k a, μ.abortAt k = some a ∧ pcOf s = a) (pl := Placed Λ lbl) (bo := bo)

/-- **The node obligations** on the fragment `I` (read side `rd`, runtime
memory's value invariant `G`, marks `μ`, layout `Λ`): `out`, every pair
off the resolved take site (where the step is the take, `TakePath.site`)
takes an `Out` row into the fragment under the placement's memory side
(`msOf`: its system calls are supported, `SysOk`, not `clone` or `exit`, no
`write` to `fd = 1` as the source has no output events yet, and an
`exit_group` off every abort site is `main`'s exit; its runtime stores are to
shared regions); `noRet`, no pair is at
`ret` (a local run reaching `main`'s `ret` is `main`'s exit, which only the
`exit_group` node takes off every abort site: there the kernel ends
the process as an abort, `AbortPath`); `cell`, the load and store rows access
single-word cells; `noSite`, no pair is at the resolved release site (the
take site is `TakePath`'s, the abort sites are `AbortPath`'s); `mapped`, no
instruction off a system call
touches an unmapped location; `place`, every pair's environment is placed;
`svc`, a pair at a system call is at a `syscall` cell (so the instruction's own
tree is a fault and only `Out.sys` applies there); `noAlloc`, no pair is at a buffer allocation (`Out.alloc`, whose
fresh label the one-thread relation does not place yet); `ownInstr`,
`ownSys`, `ownTake`, the runtime words owned (`own`, read by `Out.rtLoad`,
`Out.rtRmw` and `Out.ctrRmw`) are kept by every instruction off a system
call, no write of it to an owned word, but for one plain word store from a
state owning nothing to a state owning just that word with the stored value
(`OwnTree`), and by every system call's resumption and the take (with
`own := fun _ => []`, all three hold trivially: `OwnTree.nil`). -/
structure Nodes (Λ : Scc.Sem.Layout) (p : Prog) (μ : Marks) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : Own) (I : Inv) : Prop where
  out : ∀ lbl lsize s c, I lbl lsize s c → (∀ a, μ.site .take = some a → pcOf s ≠ a) →
    Out p lbl (msOf Λ μ rd G own lbl lsize) (I lbl lsize) s c
  noRet : ∀ lbl lsize s c, I lbl lsize s c → ∀ a, c.term ≠ .ret a
  cell : ∀ lbl lsize s c, I lbl lsize s c → ∀ x a e ty w,
    (c.term = .let_ x (.load true a) e ∨ ∃ b, c.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c.env a = some (ty, [w]) → OneCellTy ty
  noSite : ∀ lbl lsize s c, I lbl lsize s c → ∀ a, μ.site .release = some a → pcOf s ≠ a
  mapped : ∀ lbl lsize s c, I lbl lsize s c → abi.atSys s = false → ∀ e, isa.exec s = some e →
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e
  place : ∀ lbl lsize s c, I lbl lsize s c → Placed Λ lbl s c
  svc : ∀ lbl lsize s c, I lbl lsize s c → abi.atSys s = true →
    ∃ sz, Kraken.Promising.Lower.X64.CellAt s (Kraken.Promising.Lower.X64.op64 .syscall) sz
  noAlloc : ∀ lbl lsize s c, I lbl lsize s c → ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e
  ownInstr : ∀ lbl lsize s c, I lbl lsize s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
    OwnTree own (own s) tree
  ownSys : ∀ lbl lsize s c, I lbl lsize s c → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, own s' = own s
  ownTake : ∀ lbl lsize s c, I lbl lsize s c → ∀ a, μ.site .take = some a → pcOf s = a →
    ∀ m, own (abi.skip (abi.setDmem s m)) = own s

/-- **The abort path** (marks `μ`, fragment `I`, phase `Ab`): `Ab` holds of
the thread states past a refused `write`, on the way to the `writeErr` abort
stub (through the runtime's abort routine and its own `write`s). `at_`, a
pair at a resolved abort site is at the `writeErr` site, in the phase, or at
the `overflow` site with its control about to overflow (`OvfReady`) in a
small environment (`EnvSmall`; the overflow kind needs no phase: the source
does not step on the way to the stub), and an `exit_group` there has the
abort status; `instr`, off a system call no
instruction enters the phase; `sys`, a system call enters it only by a
refusal of a `write` (`Refusal`); `take`, the take does not enter it. With
`Ab` false no pair is at an abort site. -/
structure AbortPath (μ : Marks) (I : Inv) (Ab : State → Prop) : Prop where
  at_ : ∀ lbl lsize s c, I lbl lsize s c → ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmall c.env)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus
  instr : ∀ lbl lsize s c, I lbl lsize s c → ¬ Ab s → abi.atSys s = false → ∀ tree,
    isa.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ab s')
  sys : ∀ lbl lsize s c, I lbl lsize s c → ¬ Ab s → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, Ab s' →
      ∃ fd buf n, call = .write fd buf n ∧ ∀ r, abi.ret s r = s' → Refusal n r
  take : ∀ lbl lsize s c, I lbl lsize s c → ¬ Ab s → ∀ a, μ.site .take = some a → pcOf s = a →
    ∀ m, ¬ Ab (abi.skip (abi.setDmem s m))

/-- **The stack range is owned** in the thread state `s`: `rS` is in the
stack pool, and every aligned word of it is in the private memory
(`Components.stack_owned` for the one thread). -/
def Owned (Λ : Scc.Sem.Layout) (rS : Range) (s : State) : Prop :=
  rS.Sub Λ.stackPool ∧
    ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) → (privLoad s (BitVec.ofNat 64 a)).isSome

/-- **The take path** (marks `μ`, fragment `I`, stack range `rS`, phase
`Tk`): `Tk` holds of the thread states past the take of `rS`. `site`, a pair
at the resolved take site is before the take, at a `nop` cell off a system call
naming `rS` (in the pool, nonempty, the `.rodata` image off the pool), and
whatever bytes the pool has there, its state after the take is paired, past
a local run, in the phase; `instr` (off the transfer sites) and `sys`, no
instruction or system call enters or leaves the phase; `owned`, in the phase `rS` is owned. With `Tk`
false no pair is at the take site. -/
structure TakePath (Λ : Scc.Sem.Layout) (p : Prog) (μ : Marks) (I : Inv) (rS : Range) (Tk : State → Prop) :
    Prop where
  site : ∀ lbl lsize s c, I lbl lsize s c → ∀ a, μ.site .take = some a → pcOf s = a →
    ¬ Tk s ∧ (∃ n sz, Kraken.Promising.Lower.X64.CellAt s (Kraken.Promising.Lower.X64.op64 (.nop n)) sz) ∧
      abi.atSys s = false ∧ Kernel.siteRange abi s = rS ∧
      rS.Sub Λ.stackPool ∧ 0 < rS.size ∧ Λ.rodata.Disjoint Λ.stackPool ∧
      ∀ pm, ∃ c', LocalRun p c c' ∧
        I lbl lsize (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) rS))) c' ∧
        Tk (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) rS)))
  instr : ∀ lbl lsize s c, I lbl lsize s c → Kernel.siteAt abi μ s = none → abi.atSys s = false →
    ∀ tree, isa.exec s = some tree →
    tree.AllInv (fun _ _ => True) (fun s' => Tk s' ↔ Tk s)
  sys : ∀ lbl lsize s c, I lbl lsize s c → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, (Tk s' ↔ Tk s)
  owned : ∀ lbl lsize s c, I lbl lsize s c → Tk s → Owned Λ rS s

/-- **The source side's safety**: in every reachable source configuration
whose thread 0 is paired with the fragment (under any hold), the address
word of a load or store row (`cell`) and the address of an exchange
(`xchg`) name a cell with a message (a dereferenced pointer is live and
initialised). -/
structure SrcSafe (P : SrcSem.SrcParams) (p : Prog) (I : Inv) : Prop where
  cell : ∀ tr s th, (SrcSem.source P p).Reach tr s → s.ths[0]? = some th → ∀ lbl lsize st hd,
    I lbl lsize st ⟨th.term, th.env, hd⟩ →
    ∀ x a e ty w sa, (th.term = .let_ x (.load true a) e ∨ ∃ b, th.term = .let_ x (.store true a b none) e) →
      TermRun.evalAt th.env a = some (ty, [w]) → w.val = .loc sa 0 →
      ∃ (k : Nat) (m : WeakMem.Msg), s.mem[k]? = some m ∧ m.loc = sa
  xchg : ∀ tr s th, (SrcSem.source P p).Reach tr s → s.ths[0]? = some th → ∀ lbl lsize st hd,
    I lbl lsize st ⟨th.term, th.env, hd⟩ → ∀ x sa u v e, XchgSite ⟨th.term, th.env, hd⟩ x sa u v e →
      ∃ (k : Nat) (m : WeakMem.Msg), s.mem[k]? = some m ∧ m.loc = sa

/-! ## The relation -/

/-- **The bytes of the current `write`**: none, or the thread is at a
`write` of at least that many bytes. -/
def WrOk (th : Thread isa) (j : Nat) : Prop :=
  j = 0 ∨ (abi.atSys th.st = true ∧ ∃ fd buf n, Kernel.callOf abi th = some (.write fd buf n) ∧ j ≤ n)

/-- **The kernel state of the one thread**: as loaded but for the current
`write`'s bytes `j`, the ranges held `hl` and the pool's bytes `pm`. -/
def KS (E : Entry) (Λ : Scc.Sem.Layout) (j : Nat) (hl : List (Nat × Range)) (pm : _root_.Mem 64) :
    Kernel.KState :=
  { Kernel.KState.init 1 E Λ with slots := #[.run j], held := hl, pmem := pm }

/-- **The ranges held** by the thread in state `s` (stack range `rS`, phase
`Tk`): none before the take, `rS` (owned) after it. -/
def HeldOk (Λ : Scc.Sem.Layout) (rS : Range) (Tk : State → Prop) (s : State) (hl : List (Nat × Range)) : Prop :=
  (hl = [] ∧ ¬ Tk s) ∨ (hl = [(0, rS)] ∧ Tk s ∧ Owned Λ rS s)

/-- `HeldOk` is kept by a step that keeps the phase, the range owned after
it if in the phase. -/
theorem HeldOk.of_iff {Λ : Scc.Sem.Layout} {rS : Range} {Tk : State → Prop} {s s' : State}
    {hl : List (Nat × Range)} (h : HeldOk Λ rS Tk s hl) (hi : Tk s' ↔ Tk s) (ho : Tk s' → Owned Λ rS s') :
    HeldOk Λ rS Tk s' hl := by
  rcases h with ⟨rfl, hn⟩ | ⟨rfl, ht, -⟩
  · exact .inl ⟨rfl, fun h => hn (hi.mp h)⟩
  · exact .inr ⟨rfl, hi.mpr ht, ho (hi.mpr ht)⟩

/-- **Before the exit**: one target thread `th` and one source thread `th0`
(one frame, no promise), paired in the fragment under some placement and
sizes of the labels and a hold `hd` (`HoldInv`); the thread in the one-word fragment, certified, its
values at most `|M|` (`Thread.Bnd`, for the stores' progress), and the
one-thread memory invariant; the kernel state as loaded but for the
current `write`'s bytes, the ranges held (`HeldOk`: the stack range `rS`
after the take, phase `Tk`) and the pool's bytes, every one zero (the
consumers release no range, `Nodes.noSite`; so the take's bytes are zero,
which `Kernel.certAfter_take` needs); every message thread 0's;
the memory in the layout, its values 64-bit and allowed by `G`; the
runtime words the thread owns reading as their values (`OwnOk`, `own`); the
source configuration reachable. -/
def Pre (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : Own) (I : Inv)
    (rS : Range) (Tk : State → Prop) (μ : Marks) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isa) (th0 : TermRun.TTh) (j : Nat) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (hl : List (Nat × Range)) (pm : _root_.Mem 64) (hd : Option (Nat × TermRun.Word)),
    t.1.threads = #[th] ∧ (∃ E : Entry, t.2 = KS E Λ j hl pm) ∧ (∀ a, Kernel.byte pm a = 0) ∧ HeldOk Λ rS Tk th.st hl ∧
    WrOk th j ∧
    CertOkC Arch.tso (Kernel.certSem abi Arch.tso μ t.2 0) 0 th t.1.mem ∧
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.stack = [] ∧ th0.promises = [] ∧
    I lbl lsize th.st ⟨th0.term, th0.env, hd⟩ ∧ HoldInv lbl lsize s.mem hd ∧ WideSt th.st ∧
    th.Bnd t.1.mem.last ∧ Inv1 Λ lbl lsize ts th t.1.mem s.mem ∧
    OwnMsgs t.1.mem ∧ MemIn Λ t.1.mem ∧ MemFits t.1.mem ∧ MemInv G t.1.mem ∧
    ExtRows.OwnOk (own th.st) t.1.mem th.prom ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- **After the exit**: the process has exited; the source thread at
`main`'s `ret`, its environment placed; the ranges held; the memory
invariant; every message thread 0's; the memory in the layout. -/
def Post (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (rS : Range) (Tk : State → Prop)
    (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isa) (th0 : TermRun.TTh) (j : Nat) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (hl : List (Nat × Range)) (pm : _root_.Mem 64) (o : Outcome),
    t.1.threads = #[th] ∧ (∃ E : Entry, t.2 = { KS E Λ j hl pm with exited := some o }) ∧ (∀ a, Kernel.byte pm a = 0) ∧
    HeldOk Λ rS Tk th.st hl ∧
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.stack = [] ∧ th0.promises = [] ∧
    Placed Λ lbl th.st (Ctl.of th0) ∧ Inv1 Λ lbl lsize ts th t.1.mem s.mem ∧ OwnMsgs t.1.mem ∧
    MemIn Λ t.1.mem ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- **The relation.** -/
def R (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : Own) (I : Inv)
    (rS : Range) (Tk : State → Prop) (μ : Marks) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  Pre Λ P p G own I rS Tk μ t s ∨ Post Λ P p rS Tk t s

/-- The source start: `main`'s tail call. -/
def s0 (cap : Nat) : TermRun.Cfg := { SrcSem.mainStart with cap := cap }

/-- The control of the source start's thread. -/
def c0 : Ctl := ⟨.tail "main" [] (.var "a") [], [("a", .unit, [])], none⟩

/-- A fresh thread's values are 0. -/
theorem bnd_init {I : ISA} (st : I.State) (n : Nat) : (Thread.init st).Bnd n := by
  refine ⟨⟨⟨fun l => by simp [Thread.init, Views.getCoh], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun l f hf => by simp [Thread.init, Views.getFwd] at hf,
    Nat.zero_le _⟩, fun l f hf => by simp [Thread.init, Views.getFwd] at hf, fun _ _ _ h => by simp [Thread.init] at h⟩,
    fun v hv => ?_, fun v hv => ?_⟩
  · simp only [Thread.init, Array.mem_replicate] at hv; rw [hv.2]; exact Nat.zero_le _
  · simp only [Thread.init, Array.mem_replicate] at hv; rw [hv.2]; exact Nat.zero_le _

open Scc.Cert.Link in
/-- **The relation at load**: the loaded configuration of a program of the
one-word fragment (`wideIn`) and the source start, the start pair in the
fragment under the static placement, given the static link's image check
and the static labels at their symbols (`Inv1.start_static`), and the loaded
memory satisfying the runtime memory's value invariant `G`. -/
theorem pre_load {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : Prog} {G : Loc → Val → Prop} {own : Own}
    {I : Inv} {μ : Marks} {cells : List (Directive × Nat)}
    {syms : List (String × Nat)} {mem : List (Loc × Val)} {lsize : Lsize} {secs : DataSecs}
    {code : String → Option Nat} {name : WeakMem.AllocLabel → String}
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name) (hw : wideIn (cells.map (·.1)) = true)
    (hinit : P.init (s0 P.cap)) (hst : I Λ.static lsize (threadAt E Λ.code.lo cells syms) c0)
    (hmem : ∀ q ∈ mem, InitIn Λ q.1) (hmf : ∀ q ∈ mem, q.2.toNat < 2 ^ 64) {rS : Range} {Tk : State → Prop}
    (htk0 : ¬ Tk (threadAt E Λ.code.lo cells syms))
    (hown0 : OwnInit (own (threadAt E Λ.code.lo cells syms))
      (loadProg (kernel 1) E Λ cells syms mem).1.mem)
    (hg : MemInv G (loadProg (kernel 1) E Λ cells syms mem).1.mem) :
    Pre Λ P p G own I rS Tk μ (loadProg (kernel 1) E Λ cells syms mem) (s0 P.cap) := by
  refine ⟨Thread.init (threadAt E Λ.code.lo cells syms), _, 0, Λ.static, lsize, fun _ => none, [], ∅, none,
    rfl, ?_, fun _ => by simp [Kernel.byte],
    .inl ⟨rfl, htk0⟩, .inl rfl, certOkC_of_prom_nil rfl, rfl, rfl, rfl, rfl, hst, trivial,
    wideSt_threadAt hw _ _ _,
    bnd_init _ _,
    Inv1.start_static himg hss rfl rfl, ?_, ⟨?_, hmem⟩, ⟨fits_empty rfl, hmf⟩, hg,
    ownOk_init (by simp [loadProg, Config.init]) hown0 _, [], s0 P.cap,
    hinit, .refl _⟩
  · exact ⟨E, rfl⟩
  · intro k m hk; unfold Memory.get? at hk; split at hk
    · cases hk
    · simp [loadProg, Config.init] at hk
  · intro k m hk; unfold Memory.get? at hk; split at hk
    · cases hk
    · simp [loadProg, Config.init] at hk

/-- **The loaded memory is in the layout**: the static image in `.data`
(`Layout.WF`), the `.rodata` words in the `.rodata` image (`rodataFits`). -/
theorem loadMem_in {Λ : Scc.Sem.Layout} {items : List Kraken.DataImage.Item} {code : String → Option Nat}
    (hwf : Λ.WF) (hf : rodataFits Λ items = true) :
    ∀ q ∈ imageMem Λ ++ wordsMem (rodataWords Λ items code), InitIn Λ q.1 := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · simp only [imageMem, wordsMem, List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    obtain ⟨hc, h8, -⟩ := hwf.image r hr
    have hsp := (hwf.inSpace Λ.data (by simp [Scc.Sem.Layout.regions])).2
    have hlt : r.1 < 2 ^ 64 := Nat.lt_of_lt_of_le hc.2 hsp
    refine .inr ⟨rfl, ?_, .inl (.inl ?_)⟩ <;> simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    · exact h8
    · exact hc
  · simp only [wordsMem, List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    simp only [rodataFits, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.isEmpty_iff,
      List.all_eq_true] at hf
    obtain ⟨⟨hlo, hend⟩, hne⟩ := hf
    simp only [rodataWords, Kraken.DataImage.words] at hr
    obtain ⟨⟨j, hj, he⟩, -⟩ := Kraken.DataImage.wordsN_mem _ _ _ r hr
    have hl := Kraken.DataImage.image_length
      (Kraken.DataImage.resolve (fun l => BitVec.ofNat 64 ((code l).getD 0)) Λ.rodata.lo items) Λ.rodata.lo items
    rcases hne with rfl | ⟨⟨-, hsp⟩, -⟩
    · simp [Kraken.DataImage.image] at hj
    · have h8 : r.1 < Λ.rodata.lo + Λ.rodata.size := by omega
      have hlt : r.1 < 2 ^ 64 := Nat.lt_of_lt_of_le h8 hsp
      refine .inr ⟨rfl, ?_, .inr ?_⟩ <;> simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Range.contains]
      · omega
      · omega

open Scc.Cert.Link in
/-- **The relation at the target's load**: a text whose `.text` parses to a
program of the one-word fragment and whose data sections parse, loaded under
`Λ` (`load_of_parsed`), is related to the source start, given `pre_load`'s
image check, static labels and start pair (at the loader's symbols) and the
loaded memory satisfying `G`. -/
theorem init_of_load {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : Own} {I : Inv} {μ : Marks}
    {offs : List (String × Nat)}
    {cells : List (Directive × Nat)}
    {secs : DataSecs}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hwf : Λ.WF)
    (himg : imageOk Λ secs code = true)
    (hss : StaticSyms Λ secs code lsize name) (hw : wideIn (cells.map (·.1)) = true) (hinit : P.init (s0 P.cap))
    (hst : I Λ.static lsize (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)) c0)
    {rS : Range} {Tk : State → Prop} (htk0 : ¬ Tk (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)))
    {t0 : T.M.Cfg} (hown0 : OwnInit (own (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)))
      t0.1.mem)
    (hg : MemInv G t0.1.mem) (h : loadParsed (kernel 1) E Λ cells secs offs = some t0) :
    ∃ s, (SrcSem.source P p).init s ∧ R Λ P p G own I rS Tk μ t0 s := by
  simp only [loadParsed] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    cases h
    refine ⟨s0 P.cap, hinit, .inl (pre_load himg hss hw hinit hst (loadMem_in hwf hc.1.1.1.1.2) ?_ htk0 hown0 hg)⟩
    rw [imageMem, wordsMem, wordsMem, ← List.map_append]
    exact initFits_words fun q hq => (List.mem_append.mp hq).elim (image_fit hwf q) (rodataWords_fit _ _ _ q)
  · cases h

/-- **At load the thread is off the abort path** `Ab`, given that the loaded
thread state is. -/
theorem ti_load {Λ : Scc.Sem.Layout} {offs : List (String × Nat)} {cells : List (Directive × Nat)} {secs : DataSecs} {Ab : State → Prop}
    (hab0 : ¬ Ab (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata))) {t0 : T.M.Cfg}
    (h : loadParsed (kernel 1) E Λ cells secs offs = some t0) : ∀ th, t0.1.threads[0]? = some th → ¬ Ab th.st := by
  simp only [loadParsed] at h
  split at h
  · cases h
    intro th hth
    obtain rfl : Thread.init (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)) = th :=
      Option.some.inj hth
    exact hab0
  · cases h

/-! ## The step -/

/-- The one thread of a configuration replaced. -/
theorem withThread_one {c : Config isa} {th u : Thread isa} {mem : Memory} (h : c.threads = #[th]) :
    (c.withThread 0 u mem).threads = #[u] := by
  simp only [Config.withThread, h]; rfl

/-- The thread of a one-thread configuration. -/
theorem get_one {th : Thread isa} {c : Config isa} (h : c.threads = #[th]) {tid : Nat}
    {t : Thread isa} (ht : c.threads[tid]? = some t) : tid = 0 ∧ th = t := by
  rw [h] at ht
  rcases tid with _ | n
  · exact ⟨rfl, Option.some.inj ht⟩
  · simp at ht

/-- The kernel state with one running slot: its `write` count. -/
theorem wr_one {Λ : Scc.Sem.Layout} {x : Kernel.KState} {j : Nat} {hl : List (Nat × Range)} {pm : _root_.Mem 64}
    (h : x = KS E Λ j hl pm) : x.wr 0 = j := by
  subst h; rfl

/-- **An `Out` row at a `syscall` cell is `Out.sys`**: the instruction's own
tree there is a fault (`exec_syscall`), and no abort is justified there
(`ms.we`, so not `Out.emit`: `Out.we_of_emit`). -/
theorem out_sys {p : Prog} {lbl : Lbl} {ms : MemSide isa} {X : Frag isa} {s : State} {c : Ctl}
    {sz : Nat} (hc : Kraken.Promising.Lower.X64.CellAt s (Kraken.Promising.Lower.X64.op64 .syscall) sz)
    (h : Out p lbl ms X s c) (hwe : ∀ c1, ¬ ms.we s c1) :
    ∃ K call, ms.K = some K ∧ K.atSys s = true ∧ Kernel.decode K.nrs (K.nr s) (K.arg s) = some call ∧
      SysOk p ms s c call ∧ ∀ s' ∈ Kernel.certSuccs K s call, ∃ c', LocalRun p c c' ∧ X s' c' := by
  have hex := Kraken.Promising.Lower.X64.exec_syscall hc
  cases h with
  | silent s' c' he => rw [hex] at he; cases he
  | choice P t he hs => rw [hex] at he; cases he; exact hs.elim
  | load _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
  | store _ _ _ _ _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
  | rtStore _ _ _ _ _ he => rw [hex] at he; cases he
  | rtLoad _ _ _ _ he => rw [hex] at he; cases he
  | rtRmw _ _ _ _ _ he => rw [hex] at he; cases he
  | sys K call hK ha hd hok hx => exact ⟨K, call, hK, ha, hd, hok, hx⟩
  | holdLoad _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
  | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
  | ctrRmw _ _ _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
  | alloc _ _ _ _ _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
  | emit K buf n Pw Qw _ _ _ h0 _ hr hq =>
    exact absurd (Out.we_of_emit K buf n Pw Qw h0 hr hq) fun ⟨c1, h⟩ => hwe c1 h

variable {Λ : Scc.Sem.Layout} {I : Inv} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own}

/-- A pair at a system call is off the take site (`TakePath.site`: the take
site is off a system call). -/
theorem TakePath.off_sys {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk) {lbl : Lbl}
    {lsize : Lsize} {s : State} {c : Ctl} (hI : I lbl lsize s c) (hs : abi.atSys s = true) :
    ∀ a, μ.site .take = some a → pcOf s ≠ a := fun a ha hpc => by
  have h := (hT.site _ _ _ _ hI a ha hpc).2.2.1
  rw [hs] at h; cases h

/-- **A system call of the fragment is supported** (`Out.sys`'s `SysOk` at
the pair's `syscall` cell): not `exit` or `clone`, and no `write` to `fd = 1`. -/
theorem Nodes.sysOk (hN : Nodes Λ p μ rd G own I) {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} (hI : I lbl lsize s c) (hs : abi.atSys s = true) :
    ∃ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧ call ≠ .exit ∧
      (∀ st tl, call ≠ .clone st tl) ∧ ∀ fd buf n, call = .write fd buf n → fd ≠ 1 := by
  obtain ⟨sz, hc⟩ := hN.svc _ _ _ _ hI hs
  obtain ⟨K, call, hK, -, hd, ⟨hnx, hcl, hfd, -⟩, -⟩ := out_sys hc (hN.out _ _ _ _ hI (hT.off_sys hI hs)) (fun _ h => False.elim h)
  cases hK
  exact ⟨call, hd, hnx, hcl, hfd⟩

/-- **`exit_group` off every abort site is `main`'s exit** (`Out.sys`'s
`SysOk` at the pair's `syscall` cell, `MainExit`). -/
theorem Nodes.exit (hN : Nodes Λ p μ rd G own I) {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {v : Nat} (hI : I lbl lsize s c) (hs : abi.atSys s = true)
    (hoff : ∀ k a, μ.abortAt k = some a → pcOf s ≠ a)
    (hcall : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v)) :
    ∃ c', LocalRun p c c' ∧ Placed Λ lbl s c' ∧ ∀ (s0 : TermRun.Cfg) (th : TermRun.TTh), s0.ths[0]? = some th →
      th.term = c'.term → th.env = c'.env → th.stack = [] → mainExit s0 = [.exit (Kernel.exitCode v)] := by
  obtain ⟨sz, hc⟩ := hN.svc _ _ _ _ hI hs
  obtain ⟨K, call, hK, -, hd, ⟨-, -, -, hex⟩, -⟩ := out_sys hc (hN.out _ _ _ _ hI (hT.off_sys hI hs)) (fun _ h => False.elim h)
  cases hK
  obtain rfl : call = .exitGroup v := Option.some.inj (hd.symm.trans hcall)
  exact hex v rfl (fun ⟨k, a, ha, hpc⟩ => hoff k a ha hpc)

/-- **A local run lands in `Pre`**: the target thread replaced by `u` (its
`write` count 0), the source thread by the run's end, the hold the run's
(`holdInv_run`). -/
theorem pre_local (hP : HookOK P p) (hN : Nodes Λ p μ rd G own I) {t' : T.M.Cfg}
    {s : TermRun.Cfg} {u : Thread isa} {th0 : TermRun.TTh} {lbl : Lbl} {lsize : Lsize}
    {ts : Nat → Option Nat} {c c' : Ctl} {rS : Range} {Tk : State → Prop} {hl : List (Nat × Range)}
    {pm : _root_.Mem 64} (hth : t'.1.threads = #[u]) (hk : t'.2 = KS E Λ 0 hl pm) (hz : ∀ a, Kernel.byte pm a = 0)
    (hh : HeldOk Λ rS Tk u.st hl)
    (hc : CertOkC Arch.tso (Kernel.certSem abi Arch.tso μ t'.2 0) 0 u t'.1.mem) (hs0 : s.ths = #[th0])
    (hσ : th0.σs = [])
    (hst : th0.stack = []) (hp : th0.promises = []) (hI : I lbl lsize u.st c') (hw : WideSt u.st)
    (hb : u.Bnd t'.1.mem.last) (hinv : Inv1 Λ lbl lsize ts u t'.1.mem s.mem) (hown : OwnMsgs t'.1.mem)
    (hmi : MemIn Λ t'.1.mem) (hfi : MemFits t'.1.mem) (hgi : MemInv G t'.1.mem)
    (hoo : ExtRows.OwnOk (own u.st) t'.1.mem u.prom)
    (hre : ∃ tr, (SrcSem.source P p).Reach tr s) {hd : Option (Nat × TermRun.Word)}
    (hc0 : c = ⟨th0.term, th0.env, hd⟩) (hhi : HoldInv lbl lsize s.mem hd) (hcr : ∀ a, c.term ≠ .ret a)
    (hr : LocalRun p c c') :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ Pre Λ P p G own I rS Tk μ t' s' := by
  subst hc0
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  have hrun := hr.run_source_nil hP h0 rfl rfl hσ hst hp hcr (hN.noRet _ _ _ _ hI)
  obtain ⟨tr, hre⟩ := hre
  exact ⟨_, hrun, u, { th0 with term := c'.term, env := c'.env }, 0, lbl, lsize, ts, hl, pm, c'.hold, hth, ⟨E, hk⟩,
      hz, hh,
    .inl rfl, hc, set_one hs0, hσ, hst, hp, hI, holdInv_run hr hhi, hw, hb, hinv, hown, hmi, hfi, hgi, hoo, _,
    reach_run hre hrun⟩

/-- **Promises are to shared regions**: in `Pre`, a certified promise of
thread 0 is to a shared region (every byte). An open hypothesis: a promise is fulfilled
by a later store of the certification run, whose states need not stay in
the fragment (`Out.load` lands in it only for represented values); the
planned discharge is a certification fragment (a superset of the fragment
closed under every outcome, its stores to shared regions). -/
def PromShared (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : Own) (I : Inv)
    (rS : Range) (Tk : State → Prop) (μ : Marks) : Prop :=
  ∀ t s th w, Pre Λ P p G own I rS Tk μ t s → t.1.threads = #[th] → w.tid = 0 →
    CertOkC Arch.tso (Kernel.certSem abi Arch.tso μ t.2 0) 0 (Live.Sem.promThread th t.1.mem w)
      (t.1.mem.append w).1 →
    LocIn Λ.shared w.loc ∧ G w.loc w.val

/-- **No exit at an abort site** (`Step.sys`). -/
theorem exit_off {t t' : T.M.Cfg} {tid : Nat} {es : List Ev} {e : Fin 256} (hs : T.M.Step μ tid t es t')
    (he : Ev.exit e ∈ es) : ∀ k a, μ.abortAt k = some a → ¬ T.M.AtAddr a t tid := by
  cases hs with
  | sys _ _ _ _ hx => exact hx e he
  | _ => simp at he

/-- A pair of the fragment off the take site is at no transfer site
(`Nodes.noSite`). -/
theorem no_site (hN : Nodes Λ p μ rd G own I) {t : T.M.Cfg} {th : Thread isa} {lbl : Lbl} {lsize : Lsize} {c : Ctl}
    (ht : t.1.threads[0]? = some th) (hI : I lbl lsize th.st c)
    (hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a) : ∀ k, ¬ T.M.AtSite μ k t 0 := by
  rintro k ⟨a, ha, t2, ht2, hpc⟩
  cases (show some t2 = some th from ht2.symm.trans ht)
  cases k
  · exact hnt a ha hpc
  · exact hN.noSite _ _ _ _ hI a ha hpc

/-- A pair of the fragment off the take site is off the transfer sites of
the certification semantics (`Nodes.noSite` at the release site). -/
theorem siteAt_none (hN : Nodes Λ p μ rd G own I) {s : State} {lbl : Lbl} {lsize : Lsize} {c : Ctl}
    (hI : I lbl lsize s c) (hnt : ∀ a, μ.site .take = some a → pcOf s ≠ a) : Kernel.siteAt abi μ s = none :=
  Kernel.siteAt_eq_none_iff.mpr ⟨fun h => hnt _ h rfl, fun h => hN.noSite _ _ _ _ hI _ h rfl⟩

/-- **The step at the take site is the take** (`Kernel.step_at_take`): the
range `rS` moves into the thread's private memory with the pool's bytes,
and the thread moves past the `nop`. -/
theorem step_take (hN : Nodes Λ p μ rd G own I) {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk)
    {t t' : T.M.Cfg} {th : Thread isa} {lbl : Lbl} {lsize : Lsize} {c : Ctl} {es : List Ev} {a : Nat}
    (ht : t.1.threads[0]? = some th) (hI : I lbl lsize th.st c) (ha : μ.site .take = some a)
    (hpc : pcOf th.st = a) (hs : T.M.Step μ 0 t es t') :
    es = [] ∧ t' = (t.1.withThread 0
        { th with st := abi.skip (abi.setDmem th.st (Kernel.copyRange t.2.pmem (abi.dmem th.st) rS)) } t.1.mem,
      { t.2 with held := (0, rS) :: t.2.held, pmem := Kernel.eraseRange t.2.pmem rS }) := by
  obtain ⟨-, -, hsys, hsr, -⟩ := hT.site _ _ _ _ hI a ha hpc
  have hat : T.M.AtSite μ .take t 0 := ⟨a, ha, th, ht, hpc⟩
  have hnr : ¬ T.M.AtSite μ .release t 0 := fun ⟨a', ha', t2, ht2, hpc'⟩ => by
    cases (show some t2 = some th from ht2.symm.trans ht)
    exact hN.noSite _ _ _ _ hI a' ha' hpc'
  obtain ⟨hes, hx⟩ := Kernel.step_at_take ht hsys hat hnr hs
  refine ⟨hes, ?_⟩
  subst hsr
  unfold Kernel.takeStep at hx
  erw [ht] at hx
  simp only at hx
  split at hx
  · exact (Option.some.inj hx).symm
  · cases hx

/-- **A word in `data` or `pinned` is mapped in `K0`**, for reading and
writing. -/
theorem mapped_K0_of_mem {w : Bool} {a : BitVec 64}
    (h : ∀ i < 8, Λ.data.contains (a.toNat + i) ∨ Λ.pinned.contains (a.toNat + i)) :
    Kernel.mapped (K0 Λ) w ⟨a, 8⟩ = true := by
  unfold Kernel.mapped
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  intro i hi
  rcases h i hi with h | h
  · exact ⟨Λ.data, by simp [Kernel.mappedRegions, K0], h⟩
  · exact ⟨Λ.pinned, by simp [Kernel.mappedRegions, K0], h⟩

/-- The loaded state at any entry state, with any ranges held, maps more: an
access unmapped there is unmapped in `K0`. -/
theorem mapped_KS {j : Nat} {hl : List (Nat × Range)} {pm : _root_.Mem 64} {l : Loc} {w : Bool}
    (h : Kernel.mapped (KS E Λ j hl pm) w l = false) : Kernel.mapped (K0 Λ) w l = false := by
  cases hc : Kernel.mapped (K0 Λ) w l
  · rfl
  · rw [← h]; symm
    unfold Kernel.mapped at hc ⊢
    simp only [List.all_eq_true, List.any_eq_true] at hc ⊢
    intro i hi
    obtain ⟨r, hr, hcr⟩ := hc i hi
    refine ⟨r, ?_, hcr⟩
    simp only [Kernel.mappedRegions, K0, KS, Kernel.KState.init, List.mem_append, List.map_nil,
      List.not_mem_nil, or_false, List.mem_cons] at hr ⊢
    rcases hr with hr | hr
    · exact .inl (.inl (by rcases hr with h | h | h | h <;> simp [h]))
    · exact .inr hr

/-- **The stack range is fresh** before the take (`Kernel.fresh`): nonempty
and in the pool (`TakePath.site`), no range held (`HeldOk`), and every
message and initial word off the pool (`MemIn`: shared regions and the
`.rodata` image, both off the pool). -/
theorem fresh_of (hwf : Λ.WF) {rS : Range} {t : T.M.Cfg} {j : Nat} {pm : _root_.Mem 64}
    (hk : t.2 = KS E Λ j [] pm) (hsub : rS.Sub Λ.stackPool) (hpos : 0 < rS.size)
    (hrod : Λ.rodata.Disjoint Λ.stackPool) (hmi : MemIn Λ t.1.mem) : Kernel.fresh t rS = true := by
  have hsp := (hwf.inSpace Λ.stackPool (by simp [Scc.Sem.Layout.regions])).2
  have hal : Λ.stackPool.lo % 16 = 0 := hwf.aligned Λ.stackPool (by simp [Scc.Sem.Layout.regions])
  have hpool : t.2.pool = Λ.stackPool := by rw [hk]; rfl
  have hheld : t.2.held = [] := by rw [hk]; rfl
  have hloc : ∀ l, LocIn Λ.shared l → Kernel.overlaps rS l.addr.toNat (Kernel.locBytes l) = false := by
    intro l hl
    cases ho : Kernel.overlaps rS l.addr.toNat (Kernel.locBytes l)
    · rfl
    · obtain ⟨i, hi, hc⟩ := overlaps_contains hpos (by unfold Kernel.locBytes; split <;> omega) ho
      exact (shared_not_pool hwf (hl i hi) (sub_contains hsub hc)).elim
  unfold Kernel.fresh
  rw [hpool, hheld]
  have h1 : rS.lo + rS.size ≤ 2 ^ 64 := Nat.le_trans hsub.2 hsp
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.all_nil, and_true]
  refine ⟨⟨⟨⟨⟨hpos, hsub.1⟩, hsub.2⟩, h1⟩, ?_⟩, fun q hq => ?_⟩
  · rw [Array.all_eq_true_iff_forall_mem]
    intro m hm
    simpa using hloc _ (memIn_msgs hmi m (by simpa using hm))
  rcases hmi.2 q hq with hl | ⟨h8, ha8, hx⟩
  · exact hloc _ hl
  · cases ho : Kernel.overlaps rS q.1.addr.toNat (Kernel.locBytes q.1)
    · rfl
    · obtain ⟨i, hi, hc⟩ := overlaps_contains hpos (by unfold Kernel.locBytes; split <;> omega) ho
      rw [show Kernel.locBytes q.1 = 8 by simp [Kernel.locBytes, h8]] at hi
      have hp := sub_contains hsub hc
      exfalso
      rcases hx with (h | h | h) | h
      · exact word_off_pool h hwf.disjoint.2.2.2.2.1 ha8 hal hi hp
      · exact word_off_pool h hwf.disjoint.2.2.2.2.2.1 ha8 hal hi hp
      · exact word_off_pool h (Or.symm hwf.disjoint.2.2.2.2.2.2.2.2.2) ha8 hal hi hp
      · exact word_off_pool h hrod ha8 hal hi hp

/-- A thread ready for a kernel step is at a system call. -/
theorem atSys_of_ready {t : T.M.Cfg} {th : Thread isa} (hr : Kernel.ready abi 0 t th = true) :
    abi.atSys th.st = true := by
  simp only [Kernel.ready, Bool.and_eq_true] at hr; exact hr.1.1

/-- A pair of the fragment does not spawn (`Nodes.sysOk`: no `clone`). -/
theorem no_spawn (hN : Nodes Λ p μ rd G own I) {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk)
    {t t' : T.M.Cfg} {th : Thread isa} {lbl : Lbl} {lsize : Lsize} {c : Ctl} (ht : t.1.threads[0]? = some th)
    (hI : I lbl lsize th.st c) : ¬ (X64.kernel 1).spawn μ 0 t t' := by
  rintro ⟨jj, r, h, -⟩
  unfold Kernel.spawnStep at h
  erw [ht] at h
  simp only at h
  cases hr : Kernel.ready abi 0 t th
  · simp [hr] at h
  · obtain ⟨call, hd, -, hcl, -⟩ := hN.sysOk hT hI (atSys_of_ready hr)
    simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false] at h
    rw [show Kernel.callOf abi th = some call from hd] at h
    cases call with
    | clone st tl => exact hcl st tl rfl
    | _ => cases h

/-- In `Pre`, a `write` has at most its length out (`WrOk`). -/
theorem wr_le {t : T.M.Cfg} {th : Thread isa} {j : Nat} {hl : List (Nat × Range)} {pm : _root_.Mem 64}
    (hk : t.2 = KS E Λ j hl pm)
    (hwr : WrOk th j) : ∀ fd buf n, Kernel.callOf abi th = some (.write fd buf n) → t.2.wr 0 ≤ n := by
  intro fd buf n hc
  rw [wr_one hk]
  rcases hwr with rfl | ⟨-, fd', buf', n', hc', hle⟩
  · exact Nat.zero_le _
  · rw [hc] at hc'; cases hc'; exact hle

/-- **The steps before the exit**: every step from `Pre` is matched by a
source run with its observable events, landing in `R`. -/
theorem pre_step (hP : HookOK P p) (hN : Nodes Λ p μ rd G own I) (hS : SrcMem P p)
    (hsafe : SrcSafe P p I) {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk)
    (hps : PromShared Λ P p G own I rS Tk μ) (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev} (h : Pre Λ P p G own I rS Tk μ t s)
    (hs : T.M.Step μ tid t es t') : ∃ s', (SrcSem.source P p).Run s (obs es) s' ∧ R Λ P p G own I rS Tk μ t' s' := by
  have hpre := h
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, hz, hh, hwr, hcert0, hs0, hσ, hst, hp, hI, hhi, hw,
      hb, hinv,
    hown, hmi, hfi, hgi, hoo, hre⟩ := h
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  obtain ⟨tr, hreach⟩ := hre
  by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
  · -- the take: a local run of the source
    obtain ⟨a, ha, hpc⟩ := htk
    obtain ⟨hntk, ⟨n, sz, hcn⟩, hsys, -, -, -, -, hrun⟩ := hT.site _ _ _ _ hI a ha hpc
    have hat : T.M.AtSite μ .take t 0 := ⟨a, ha, th, ht1, hpc⟩
    have hnr : ¬ T.M.AtSite μ .release t 0 := fun ⟨a', ha', t2, ht2, hpc'⟩ => by
      cases (show some t2 = some th from ht2.symm.trans ht1)
      exact hN.noSite _ _ _ _ hI a' ha' hpc'
    have htake := (Kernel.step_at_take ht1 hsys hat hnr hs).2
    obtain ⟨hes, rfl⟩ := step_take hN hT ht1 hI ha hpc hs
    subst hes
    have hsa : Kernel.siteAt abi μ th.st = some .take := by
      unfold Kernel.siteAt; rw [ite_eq_left_iff.mpr (fun h => absurd (by rw [ha, ← hpc]; rfl) h)]
    have hca := Kernel.certAfter_take ht1 htake hsa
      hsys (X64.deps_of_atNop (atNop_of_cellAt hcn)) (fun a _ => by rw [hk]; exact hz a) hcert0
    obtain ⟨c', hlr, hI', htk'⟩ := hrun t.2.pmem
    have hj : j = 0 := by
      rcases hwr with h | ⟨h, -⟩
      · exact h
      · rw [hsys] at h; cases h
    subst hj
    obtain rfl : hl = [] := by
      rcases hh with ⟨h, -⟩ | ⟨-, h, -⟩
      · exact h
      · exact absurd h hntk
    have hk' : ({ t.2 with held := (0, rS) :: t.2.held, pmem := Kernel.eraseRange t.2.pmem rS } : Kernel.KState) =
        KS E Λ 0 [(0, rS)] (Kernel.eraseRange pm rS) := by rw [hk]; rfl
    obtain ⟨s', hrun', hpre'⟩ := pre_local (u := { th with st := abi.skip (abi.setDmem th.st
        (Kernel.copyRange t.2.pmem (abi.dmem th.st) rS)) })
      (t' := (t.1.withThread 0 _ t.1.mem, _)) hP hN (withThread_one hth) hk'
      (fun a => by rw [Kernel.byte_eraseRange]; split <;> simp [hz])
      (.inr ⟨rfl, htk', hT.owned _ _ _ _ hI' htk'⟩) (hca _ (by erw [withThread_one hth]; rfl)) hs0 hσ
      hst hp hI' hw ⟨hb.1, hb.2⟩ ⟨hinv.1, hinv.2, hinv.3⟩ hown hmi hfi hgi
      (by show ExtRows.OwnOk (own (abi.skip _)) _ _; rw [hN.ownTake _ _ _ _ hI a ha hpc]; exact hoo)
      ⟨tr, hreach⟩ rfl hhi
      (hN.noRet _ _ _ _ hI) hlr
    exact ⟨s', hrun', .inl hpre'⟩
  have hsite := no_site hN ht1 hI (fun a ha hpc => htk ⟨a, ha, hpc⟩)
  have hready := atSys_of_ready (t := t) (th := th)
  have hsp := no_spawn (t' := t') hN hT ht1 hI
  have hwj : t.2.wr 0 = j := wr_one hk
  have hwr' := wr_le hk hwr
  rcases X64Ext.step_cases_site ht1 hw hinv hs hsp hsite with
    ⟨rfl, hns, outs, o, hso, ho, rfl, hw', hc⟩ | ⟨rfl, w, rfl, hinv', hc, hwt⟩ | ⟨pk, hsys, hcert, hi⟩
  · -- an instruction
    have hj : j = 0 := by
      rcases hwr with h | ⟨h, -⟩
      · exact h
      · rw [hns] at h; cases h
    subst hj
    have hth' := withThread_one (u := o.thread) (mem := o.mem) hth
    have hsn := siteAt_none hN hI (fun a ha hpc => htk ⟨a, ha, hpc⟩)
    have hi := (stepOne_allInv Arch.tso hso ho (hT.instr _ _ _ _ hI hsn hns) ⟨fun _ => trivial, fun _ _ => trivial⟩).1
    have hb' := (stepOne_bnd _ hso ho hb).1
    have hfi' : MemFits o.mem := by
      refine ⟨fits_stepOne Arch.tso (fun _ he => certExec_fit hw ((Kernel.certExec_of_not_atSys abi hns).trans he))
        hso ho hfi.1, ?_⟩
      unfold InitFits; rw [(stepOne_dord _ hso ho).2.2.1.1]; exact hfi.2
    have hmg : MemIn Λ o.mem ∧ MemInv G o.mem := by
      rcases ExtRows.out_mem hinv hso ho hns (X64Ext.wide8_exec hw hns) hgi
        hoo (hN.out _ _ _ _ hI (fun a ha hpc => htk ⟨a, ha, hpc⟩)) with hm | ⟨L, V, hm, hL8L⟩
      · rw [hm]; exact ⟨hmi, hgi⟩
      · rw [hm]
        rcases hL8L with ⟨hL8, hL⟩
        have hLw := loc_eq_wordLoc hL8
        have h8 : Kernel.locBytes L = 8 := by simp [Kernel.locBytes, hL8]
        rcases hL with ⟨-, hmp, hGV⟩ | ⟨x, a, b, e, ty, w, sa, ht, hev, hv, hsa⟩ |
          ⟨x, sa, u, v, e, hxs, hA⟩ | ⟨-, -, ⟨xn, an, τn, en, hnb⟩, -⟩
        · exact ⟨memIn_append (hmp.2 rfl) hmi, hgi.append hGV⟩
        · obtain ⟨k, m, hkm, hl⟩ :=
            hsafe.cell tr s th0 hreach h0 lbl lsize th.st hd hI x a e ty w sa (.inr ⟨b, ht⟩) hev hsa
          obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
          rw [hl] at hoff
          rw [hsa] at hv
          have hwa := wordAddr_of_valRep_loc0 hv
          refine ⟨memIn_append (fun i hi => ?_) hmi, hgi.append ?_⟩
          · rw [h8] at hi
            exact shared_of_wordAddr hinv.mem hwa hoff i hi
          · show G L V
            rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
        · obtain ⟨k, m, hkm, hl⟩ := hsafe.xchg tr s th0 hreach h0 lbl lsize th.st hd hI x sa u v e hxs
          obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
          rw [hl] at hoff
          have hwa := wordAddr_of_valRep_loc0 hA
          refine ⟨memIn_append (fun i hi => ?_) hmi, hgi.append ?_⟩
          · rw [h8] at hi
            exact shared_of_wordAddr hinv.mem hwa hoff i hi
          · show G L V
            rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
        · exact absurd hnb (hN.noAlloc _ _ _ _ hI xn an τn en)
    obtain ⟨hmi', hgi'⟩ := hmg
    have hoo' : ExtRows.OwnOk (own o.thread.st) o.mem o.thread.prom := by
      obtain ⟨tree, hex⟩ := Option.isSome_iff_exists.mp (ExtRows.out_exec hns
        (hN.out _ _ _ _ hI (fun a ha hpc => htk ⟨a, ha, hpc⟩)))
      exact ownOk_step hex (hN.ownInstr _ _ _ _ hI hns tree hex) hinv.coh hinv.mem.tq_nodup
        (fun p hp => (hinv.mem.tq_le p hp).2) hso ho hoo
    rcases ExtRows.out_local hinv hso ho hns (X64Ext.wide8_exec hw hns) hgi hoo
        (hN.out _ _ _ _ hI (fun a ha hpc => htk ⟨a, ha, hpc⟩)) with
      ⟨c', hr, hI', hinv'⟩ |
      ⟨kl, A, g, x, a, e, ty, w, sa, hex, ht, hev, hv, hsa, hX⟩ |
      ⟨kr, A, V, s', x, a, b, e, ty, tb, w, wb, sa, hex, ht, hev, hv, hsa, hevb, hvb, hX⟩ |
      ⟨kl, A, g, x, sa, u, v, e, hex, hxs, hA, hh0, hX⟩ |
      ⟨kr, A, V, s', x, sa, u, v, e, tv, wv, wold, hex, hxs, hA, hh0, hev, hvb, hX⟩ |
      ⟨x, a, τ, e, -, -, -, -, ht, -⟩ | ⟨-, -, x, a, τ, e, -, -, -, -, -, -, -, ht, -⟩
    · obtain ⟨s', hrun, hpre⟩ := pre_local (t' := (t.1.withThread 0 o.thread o.mem, t.2)) hP hN hth' hk hz
        (hh.of_iff hi (hT.owned _ _ _ _ hI')) hc hs0 hσ hst hp hI' hw' hb' hinv' (ownMsgs_step hso ho hown) hmi'
        hfi' hgi' hoo' ⟨tr, hreach⟩ rfl hhi
        (hN.noRet _ _ _ _ hI) hr
      exact ⟨s', hrun, .inl hpre⟩
    · -- the load row
      obtain ⟨jl, hjl⟩ :=
        exists_sLatest (hsafe.cell tr s th0 hreach h0 lbl lsize th.st hd hI x a e ty w sa (.inl ht) hev hsa)
      rw [hsa] at hv
      rw [← wordLoc_toNat] at hex
      obtain ⟨-, -, hinv', -⟩ := hinv.load hwf _ hex hso ho (wordAddr_of_valRep_loc0 hv) hjl
      obtain ⟨-, k, v, hgv, htl, hrd'⟩ := stepOne_load_tlatestP _ hex hso ho hinv.coh
      obtain ⟨m, hm, hrep⟩ := hinv.mem.latestP_read hwf hinv.narrow (wordAddr_of_valRep_loc0 hv)
        (SLatestP.nil_iff.mpr hjl) htl hrd'
      have hX' := hX v ⟨m.val, m.view, jl⟩ (hrd _) (valRep_setWidth_of_fits hrep (read?_fits hfi.1 hfi.2 hrd'))
      obtain ⟨th', hstep, hte, hen, hp', hσ', hst'⟩ := src_load_step hP hS h0 hp ht hev hsa
        (hN.cell _ _ _ _ hI x a e ty w (.inl ht) hev) hjl hm (hN.noRet _ _ _ _ hX')
      have hrun := run_one hstep
      refine ⟨_, hrun, .inl ⟨o.thread, th', 0, lbl, lsize, ts, hl, pm, none, hth', ⟨E, hk⟩, hz,
        hh.of_iff hi (hT.owned _ _ _ _ (by rw [hgv]; exact hX')), .inl rfl, hc, set_one hs0, hσ' ▸ hσ,
        hst' ▸ hst, hp', ?_, trivial, hw', hb', hinv', ownMsgs_step hso ho hown, hmi', hfi', hgi', hoo', _,
        reach_run hreach hrun⟩⟩
      show I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩
      rw [hte, hen, hgv]; exact hX'
    · -- the store row
      obtain ⟨k, m, hkm, hml⟩ :=
        hsafe.cell tr s th0 hreach h0 lbl lsize th.st hd hI x a e ty w sa (.inr ⟨b, ht⟩) hev hsa
      obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
      rw [hml] at hoff
      obtain ⟨th', mv, hstep, hte, hen, hp', hσ', hst'⟩ := src_store_step hP hS h0 hp ht hev hsa
        (hN.cell _ _ _ _ hI x a e ty w (.inr ⟨b, ht⟩) hev) hevb (hN.noRet _ _ _ _ hX)
      rw [hsa] at hv
      rw [← wordLoc_toNat] at hex
      obtain ⟨hst'', q, hinv'⟩ := hinv.store (m := ⟨sa, wb.val, mv⟩) _ hex hso ho (wordAddr_of_valRep_loc0 hv) hoff hvb
      have hrun := run_one hstep
      refine ⟨_, hrun, .inl ⟨o.thread, th', 0, lbl, lsize, _, hl, pm, none, hth', ⟨E, hk⟩, hz,
        hh.of_iff hi (hT.owned _ _ _ _ (by rw [hst'']; exact hX)), .inl rfl, hc, set_one hs0, hσ' ▸ hσ,
        hst' ▸ hst, hp', ?_, trivial, hw', hb', hinv', ownMsgs_step hso ho hown, hmi', hfi', hgi', hoo', _,
        reach_run hreach hrun⟩⟩
      show I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩
      rw [hte, hen, hst'']; exact hX
    · -- the load of an exchange: the source stutters, holding the latest word
      obtain ⟨k, m0, hkm, hml⟩ := hsafe.xchg tr s th0 hreach h0 lbl lsize th.st hd hI x sa u v e hxs
      obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
      rw [hml] at hoff
      obtain ⟨jl, hjl⟩ := exists_sLatest ⟨k, m0, hkm, hml⟩
      have hwa := wordAddr_of_valRep_loc0 hA
      rw [← wordLoc_toNat] at hex
      obtain ⟨-, -, hinv', -⟩ := hinv.load hwf _ hex hso ho hwa hjl
      obtain ⟨-, k', r, hgr, htl, hrd'⟩ := stepOne_load_tlatestP _ hex hso ho hinv.coh
      obtain ⟨m, hm, hrep⟩ := hinv.mem.latestP_read hwf hinv.narrow hwa (SLatestP.nil_iff.mpr hjl) htl hrd'
      have hX' := hX r ⟨m.val, m.view, jl⟩ (hrd _) (valRep_setWidth_of_fits hrep (read?_fits hfi.1 hfi.2 hrd'))
      refine ⟨s, .refl _, .inl ⟨o.thread, th0, 0, lbl, lsize, ts, hl, pm, some (A.toNat, ⟨m.val, m.view, jl⟩), hth',
        ⟨E, hk⟩, hz, hh.of_iff hi (hT.owned _ _ _ _ (by rw [hgr]; exact hX')), .inl rfl, hc, hs0, hσ, hst, hp, ?_,
        ⟨sa, jl, m, hwa, hoff, hjl, hm, rfl⟩, hw', hb', hinv', ownMsgs_step hso ho hown, hmi', hfi', hgi', hoo',
        tr, hreach⟩⟩
      rw [hgr]; exact hX'
    · -- the store of an exchange: the source exchange, reading the held word
      obtain ⟨k, m0, hkm, hml⟩ := hsafe.xchg tr s th0 hreach h0 lbl lsize th.st hd hI x sa u v e hxs
      obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
      rw [hml] at hoff
      have hwa := wordAddr_of_valRep_loc0 hA
      have hhd : hd = some (A.toNat, wold) := hh0
      rw [hhd] at hhi
      obtain ⟨sa', jl, m, hwa', hoff', hjl, hm, rfl⟩ := hhi
      have hsa' : sa' = sa := hinv.mem.wordAddr_inj hwa' hwa hoff' hoff
      subst sa'
      obtain ⟨th', mv, hstep, hte, hen, hp', hσ', hst'⟩ := src_swap_step hP h0 hp hxs hev hjl hm
        (hN.noRet _ _ _ _ hI) (hN.noRet _ _ _ _ hX)
      rw [← wordLoc_toNat] at hex
      obtain ⟨hst'', q, hinv'⟩ := hinv.store (m := ⟨sa, wv.val, mv⟩) _ hex hso ho hwa hoff hvb
      have hrun := run_one hstep
      refine ⟨_, hrun, .inl ⟨o.thread, th', 0, lbl, lsize, _, hl, pm, none, hth', ⟨E, hk⟩, hz,
        hh.of_iff hi (hT.owned _ _ _ _ (by rw [hst'']; exact hX)), .inl rfl, hc, set_one hs0, hσ' ▸ hσ,
        hst' ▸ hst, hp', ?_, trivial, hw', hb', hinv', ownMsgs_step hso ho hown, hmi', hfi', hgi', hoo', _,
        reach_run hreach hrun⟩⟩
      show I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩
      rw [hte, hen, hst'']; exact hX
    · exact absurd ht (hN.noAlloc _ _ _ _ hI x a τ e)
    · exact absurd ht (hN.noAlloc _ _ _ _ hI x a τ e)
  · -- a promise: the source stutters
    have hlast : t.1.mem.last ≤ (t.1.mem.append w).1.last := by rw [Memory.last_append]; exact Nat.le_succ _
    exact ⟨s, .refl _, .inl ⟨_, th0, j, lbl, lsize, ts, hl, pm, hd, withThread_one hth, ⟨E, hk⟩, hz, hh, hwr, hc, hs0,
        hσ,
      hst, hp, hI, hhi, hw,
      ⟨hb.views.mono hlast, hb.regs.mono hlast⟩, hinv', ownMsgs_append hwt hown,
      memIn_append (hps t s th w hpre hth hwt hc).1 hmi,
      ⟨fits_promise_cert_on (soloFit64CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc hfi.1, initFits_append hfi.2 w⟩,
      hgi.append (hps t s th w hpre hth hwt hc).2,
      ownOk_promise hinv.coh hinv.mem.tq_nodup (fun p hp => (hinv.mem.tq_le p hp).2) hoo w, tr, hreach⟩⟩
  · -- a kernel step
    obtain ⟨hr, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsys hwr'
    have hsys' := hready hr
    obtain ⟨call', hdc, hnx, -, hfd⟩ := hN.sysOk hT hI hsys'
    obtain rfl : call = call' := Option.some.inj (hcall.symm.trans hdc)
    rcases hcases with ⟨fd, buf, n, rd', b, u, rfl, rfl, hlt, hrb, hust, hes, rfl⟩ |
      ⟨r, rfl, hx, hg, hev, hmem, u, hu, hsu, hpu⟩ | ⟨hex, -⟩ | ⟨v, rfl, hx⟩
    · -- a byte of a `write` to `fd ≠ 1`: no event
      rw [ite_eq_right_iff.mpr (fun h => absurd h (hfd fd buf n rfl))] at hes
      subst hes
      refine ⟨s, .refl _, .inl ⟨u, th0, j + 1, lbl, lsize, ts, hl, pm, hd, withThread_one hth, ⟨E, by rw [hk]; rfl⟩, hz,
        hust ▸ hh, ?_,
        hcert u (by rw [withThread_one hth]; rfl), hs0, hσ, hst, hp, hust ▸ hI, hhi, hust ▸ hw,
        ExtThread.bnd_readByte abi hb hrb, ExtThread.inv1_readByte abi hinv hrb, hown, hmi, hfi, hgi,
        by rw [hust, Kernel.readByte_prom hrb]; exact hoo, tr, hreach⟩⟩
      refine .inr ⟨hust ▸ hsys', fd, buf, n, ?_, hwj ▸ hlt⟩
      show Kernel.decode _ (abi.nr u.st) (abi.arg u.st) = _
      rw [hust]; exact hcall
    · -- a return
      obtain ⟨K, call', hK, -, hd', -, hx'⟩ := out_sys (Classical.choose_spec
        (hN.svc _ _ _ _ hI hsys')) (hN.out _ _ _ _ hI (hT.off_sys hI hsys')) (fun _ h => False.elim h)
      cases hK
      obtain rfl : call = call' := Option.some.inj (hcall.symm.trans hd')
      obtain ⟨c', hlr, hI'⟩ := hx' _ hsu
      have hbu : u.Bnd t'.1.mem.last := by
        rw [hmem]
        rcases ExtThread.bnd_sysStep abi ht1 hb hsys with he | ⟨u', he, hb'⟩
        · rw [he, hth] at hu; cases hu; exact hb
        · rw [he] at hu
          obtain rfl : u' = u := Option.some.inj ((show (t.1.withThread 0 u' t.1.mem).threads[0]? = some u' by
            simp only [Config.withThread, hth]; rfl).symm.trans hu)
          exact hb'
      have hu1 : t'.1.threads = #[u] ∧ Inv1 Λ lbl lsize ts u t'.1.mem s.mem := by
        rcases hi with he | ⟨u', he, hinv'⟩
        · rw [he] at hu ⊢; rw [hth] at hu; cases hu; exact ⟨hth, hinv⟩
        · rw [he] at hu ⊢
          have h1 : (t.1.withThread 0 u' t.1.mem).threads = #[u'] := withThread_one hth
          obtain rfl : u' = u := Option.some.inj ((show (t.1.withThread 0 u' t.1.mem).threads[0]? = some u' by
            simp only [Config.withThread, hth]; rfl).symm.trans hu)
          exact ⟨h1, hinv'⟩
      have hk' : t'.2 = KS E Λ 0 hl pm := by
        rcases ExtThread.sysStep_ret_kstate abi ht1 hsys (fun h => hx (Option.some.inj
          (hcall.symm.trans h))) (fun v h => hg v (Option.some.inj (hcall.symm.trans h))) with he | ⟨he, hw0⟩
        · rw [he, hk]; rfl
        · rw [he, hk]
          rcases hwr with rfl | ⟨-, fd, buf, n, hc', -⟩
          · rfl
          · have := hw0 fd buf n hc'; rw [hwj] at this; subst this; rfl
      have hobs : obs es = [] := by
        rcases hev with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
      rw [hobs]
      have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := hsu
      obtain ⟨s', hrun, hpre⟩ := pre_local hP hN hu1.1 hk' hz
        (hh.of_iff (hT.sys _ _ _ _ hI hsys' _ hcall _ hsu') (hT.owned _ _ _ _ hI')) (hcert u hu) hs0 hσ hst hp hI'
        (ExtThread.sysStep_wideInv abi wideInv ht1 hw hsys hwr' hu) hbu hu1.2 (by rw [hmem]; exact hown)
        (by rw [hmem]; exact hmi) (by rw [hmem]; exact hfi) (by rw [hmem]; exact hgi)
        (by rw [hmem, hpu, hN.ownSys _ _ _ _ hI hsys' _ hcall _ hsu']; exact hoo)
        ⟨tr, hreach⟩ rfl hhi (hN.noRet _ _ _ _ hI) hlr
      exact ⟨s', hrun, .inl hpre⟩
    · exact absurd hex hnx
    · rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨k, rfl, -, rfl, rfl⟩
      · -- `exit_group`: `main`'s exit (off every abort site, `Step.sys`)
        have hoff : ∀ k a, μ.abortAt k = some a → pcOf th.st ≠ a := fun k a ha hpc =>
          exit_off hs (List.mem_singleton_self _) k a ha ⟨th, ht1, hpc⟩
        obtain ⟨c', hlr, hpl, hexit⟩ := hN.exit hT hI hsys' hoff hcall
        have hrun := hlr.run_source hP h0 rfl rfl hσ hst hp (hN.noRet _ _ _ _ hI)
          (hP.noExit hreach)
        have hlt : 0 < s.ths.size := by rw [hs0]; exact Nat.zero_lt_one
        rw [hexit _ { th0 with term := c'.term, env := c'.env } (by simp [hlt]) rfl rfl hst] at hrun
        refine ⟨_, hrun, .inr ⟨th, { th0 with term := c'.term, env := c'.env }, j, lbl, lsize, ts, hl, pm, _, hth,
          ⟨E, by rw [hk]⟩, hz, hh, set_one hs0, hσ, hst, hp, hpl, hinv, hown, hmi, _, reach_run hreach hrun⟩⟩
      · -- an abort: the process ends, the source stutters
        exact ⟨s, .refl _, .inr ⟨th, th0, j, lbl, lsize, ts, hl, pm, _, hth, ⟨E, by rw [hk]⟩, hz, hh, hs0, hσ, hst, hp,
          by have hpl := hN.place _ _ _ _ hI; exact hpl, hinv, hown, hmi, tr, hreach⟩⟩

/-- **Every step from `R` is matched**: from `Pre` by `pre_step`; after the
exit no thread steps. -/
theorem r_step (hP : HookOK P p) (hN : Nodes Λ p μ rd G own I) (hS : SrcMem P p)
    (hsafe : SrcSafe P p I) {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk)
    (hps : PromShared Λ P p G own I rS Tk μ) (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev} (h : R Λ P p G own I rS Tk μ t s)
    (hs : T.M.Step μ tid t es t') : ∃ s', (SrcSem.source P p).Run s (obs es) s' ∧ R Λ P p G own I rS Tk μ t' s' := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  · exact pre_step hP hN hS hsafe hT hps hrd hwf hGpl h hs
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hk]) hs).elim

/-! ## The core invariant along certification runs -/

/-- **The core of `Pre`** for a thread `th` and a memory `mem`, kept along
the thread's certification runs: `Pre` without the kernel state, the ranges
held and the certification, and with the shared-region and `G` clauses on
messages exempting the outstanding promises (`MsgsExcept`; a promised
message is written only when fulfilled). -/
def PreCore (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : Own) (I : Inv)
    (th : Thread isa) (mem : Memory) (s : TermRun.Cfg) : Prop :=
  ∃ (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.stack = [] ∧ th0.promises = [] ∧
    I lbl lsize th.st ⟨th0.term, th0.env, hd⟩ ∧ HoldInv lbl lsize s.mem hd ∧ WideSt th.st ∧
    th.Bnd mem.last ∧ Inv1 Λ lbl lsize ts th mem s.mem ∧ OwnMsgs mem ∧
    MsgsExcept (fun m => LocIn Λ.shared m.loc) th.prom mem ∧ (∀ q ∈ mem.init, InitIn Λ q.1) ∧ MemFits mem ∧
    MsgsExcept (fun m => G m.loc m.val) th.prom mem ∧ (∀ l, G l (mem.initVal l)) ∧
    ExtRows.OwnOk (own th.st) mem th.prom ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- `PreCore`'s message clauses, as `stepG_of` takes them. -/
theorem PreCore.msgs {th : Thread isa} {mem : Memory} {s : TermRun.Cfg} (h : PreCore Λ P p G own I th mem s) :
    MsgsExcept (fun m => LocIn Λ.shared m.loc) th.prom mem ∧ MsgsExcept (fun m => G m.loc m.val) th.prom mem := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsh, -, -, hgm, -⟩ := h
  exact ⟨hsh, hgm⟩

/-- **`Pre` gives `PreCore`** of its one thread and the memory. -/
theorem pre_core {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isa}
    (h : Pre Λ P p G own I rS Tk μ t s) (hth : t.1.threads = #[th]) : PreCore Λ P p G own I th t.1.mem s := by
  obtain ⟨th', th0, -, lbl, lsize, ts, -, -, hd, hth', -, -, -, -, -, hs0, hσ, hst, hp, hI, hhi, hw, hb, hinv, hown,
    hmi, hfi, hgi, hoo, hre⟩ := h
  obtain rfl : th = th' := (get_one hth (show t.1.threads[0]? = some th' by rw [hth']; rfl)).2
  exact ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hst, hp, hI, hhi, hw, hb, hinv, hown, MsgsExcept.of_all hmi.1 _, hmi.2,
    hfi, MemInv.msgsExcept hgi _, hgi.1, hoo, hre⟩

/-- **`Pre` followed by a certified promise gives `PreCore`** of the
promising thread and the memory with the promise: the promised message is
exempt (`msgsExcept_promise`), the rest as for the promise step of
`pre_step` (no `PromShared` needed). -/
theorem pre_core_promise {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isa}
    {w : Msg} (h : Pre Λ P p G own I rS Tk μ t s) (hth : t.1.threads = #[th]) (hwt : w.tid = 0)
    (hc : CertOkC Arch.tso (Kernel.certSem abi Arch.tso μ t.2 0) 0 (Live.Sem.promThread th t.1.mem w)
      (t.1.mem.append w).1) :
    PreCore Λ P p G own I (Live.Sem.promThread th t.1.mem w) (t.1.mem.append w).1 s := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hst, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hre⟩ := pre_core h hth
  have hlast : t.1.mem.last ≤ (t.1.mem.append w).1.last := by rw [Memory.last_append]; exact Nat.le_succ _
  exact ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hst, hp, hI, hhi, hw, ⟨hb.views.mono hlast, hb.regs.mono hlast⟩,
    hinv.promise_cert_on (soloWide8CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc, ownMsgs_append hwt hown,
    msgsExcept_promise hsh w, hini,
    ⟨fits_promise_cert_on (soloFit64CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc hfi.1, initFits_append hfi.2 w⟩,
    msgsExcept_promise hgm w,
    hgi, ownOk_promise hinv.coh hinv.mem.tq_nodup (fun p hp => (hinv.mem.tq_le p hp).2) hoo w, hre⟩

/-- **An instruction step off a system call and off the take site keeps
`PreCore`**, matched by a source run with no event: `pre_step`'s
instruction case without the kernel state, under outstanding promises
(`ExtRows.out_memP`, `ExtRows.out_localP`): a write appends a message to a
shared region of a `G` value or fulfils a promise of one. -/
theorem core_step (hP : HookOK P p) (hN : Nodes Λ p μ rd G own I) (hS : SrcMem P p)
    (hsafe : SrcSafe P p I) (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {th : Thread isa} {mem : Memory} {s : TermRun.Cfg} {outs : List (Except String (Outcome isa))}
    {o : Outcome isa} (h : PreCore Λ P p G own I th mem s) (hns : abi.atSys th.st = false)
    (hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a)
    (hso : stepOne Arch.tso th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCore Λ P p G own I o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hst, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    tr, hreach⟩ := h
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  have hout := hN.out _ _ _ _ hI hnt
  obtain ⟨tree, hex⟩ := Option.isSome_iff_exists.mp (ExtRows.out_exec hns hout)
  have hw' : WideSt o.thread.st :=
    wideInv _ _ _ hw ((Kernel.certExec_of_not_atSys abi hns).trans hex) (ExtThread.stepOne_treeLeaf hex hso ho)
  have hb' := (stepOne_bnd _ hso ho hb).1
  have hinit : o.mem.init = mem.init := (stepOne_dord _ hso ho).2.2.1.1
  have hfi' : MemFits o.mem := by
    refine ⟨fits_stepOne Arch.tso (fun _ he => certExec_fit hw ((Kernel.certExec_of_not_atSys abi hns).trans he))
      hso ho hfi.1, ?_⟩
    unfold InitFits; rw [hinit]; exact hfi.2
  have hini' : ∀ q ∈ o.mem.init, InitIn Λ q.1 := by rw [hinit]; exact hini
  have hgi' : ∀ l, G l (o.mem.initVal l) := by intro l; unfold Memory.initVal; rw [hinit]; exact hgi l
  have hoo' : ExtRows.OwnOk (own o.thread.st) o.mem o.thread.prom :=
    ownOk_step hex (hN.ownInstr _ _ _ _ hI hns tree hex) hinv.coh hinv.mem.tq_nodup
      (fun p hp => (hinv.mem.tq_le p hp).2) hso ho hoo
  have hown' := ownMsgs_step hso ho hown
  have hmg : MsgsExcept (fun m => LocIn Λ.shared m.loc) o.thread.prom o.mem ∧
      MsgsExcept (fun m => G m.loc m.val) o.thread.prom o.mem := by
    rcases ExtRows.out_memP hinv hso ho hns (X64Ext.wide8_exec hw hns) hgm hgi hoo hout with
      ⟨hm, hpr⟩ | ⟨L, V, hL8, hmem, hL⟩
    · exact ⟨msgsExcept_of_eq hsh hm hpr, msgsExcept_of_eq hgm hm hpr⟩
    have hLw := loc_eq_wordLoc hL8
    have h8 : Kernel.locBytes L = 8 := by simp [Kernel.locBytes, hL8]
    have hPm : LocIn Λ.shared L ∧ G L V := by
      rcases hL with ⟨-, hmp, hGV⟩ | ⟨x, a, b, e, ty, w, sa, ht, hev, hv, hsa⟩ |
        ⟨x, sa, u, v, e, hxs, hA⟩ | ⟨-, -, ⟨xn, an, τn, en, hnb⟩, -⟩
      · exact ⟨hmp.2 rfl, hGV⟩
      · obtain ⟨k, m, hkm, hl⟩ :=
          hsafe.cell tr s th0 hreach h0 lbl lsize th.st hd hI x a e ty w sa (.inr ⟨b, ht⟩) hev hsa
        obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
        rw [hl] at hoff
        rw [hsa] at hv
        have hwa := wordAddr_of_valRep_loc0 hv
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [h8] at hi
          exact shared_of_wordAddr hinv.mem hwa hoff i hi
        · rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
      · obtain ⟨k, m, hkm, hl⟩ := hsafe.xchg tr s th0 hreach h0 lbl lsize th.st hd hI x sa u v e hxs
        obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
        rw [hl] at hoff
        have hwa := wordAddr_of_valRep_loc0 hA
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [h8] at hi
          exact shared_of_wordAddr hinv.mem hwa hoff i hi
        · rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
      · exact absurd hnb (hN.noAlloc _ _ _ _ hI xn an τn en)
    rcases hmem with ⟨hm, hpr⟩ | ⟨q, -, hg, hm, hpr⟩
    · rw [hm, hpr]
      exact ⟨msgsExcept_append hsh (w := ⟨L, V, 0⟩) hPm.1, msgsExcept_append hgm (w := ⟨L, V, 0⟩) hPm.2⟩
    · rw [hm, hpr]
      exact ⟨msgsExcept_erase hsh hg hPm.1, msgsExcept_erase hgm hg hPm.2⟩
  rcases ExtRows.out_localP hinv hso ho hns (X64Ext.wide8_exec hw hns) hgm hgi hoo hout with
    ⟨c', hr, hI', hinv'⟩ |
    ⟨kl, A, g, x, a, e, ty, w, sa, hex, ht, hev, hv, hsa, hX⟩ |
    ⟨kr, A, V, s', x, a, b, e, ty, tb, w, wb, sa, hex, ht, hev, hv, hsa, hevb, hvb, hX⟩ |
    ⟨kl, A, g, x, sa, u, v, e, hex, hxs, hA, hh0, hX⟩ |
    ⟨kr, A, V, s', x, sa, u, v, e, tv, wv, wold, hex, hxs, hA, hh0, hev, hvb, hX⟩ |
    ⟨x, a, τ, e, -, -, -, -, ht, -⟩ | ⟨-, -, x, a, τ, e, -, -, -, -, -, -, -, ht, -⟩
  · -- a local run
    have hrun := hr.run_source_nil hP h0 rfl rfl hσ hst hp (hN.noRet _ _ _ _ hI) (hN.noRet _ _ _ _ hI')
    exact ⟨_, hrun, { th0 with term := c'.term, env := c'.env }, lbl, lsize, ts, c'.hold, set_one hs0, hσ, hst, hp,
      hI', holdInv_run hr hhi, hw', hb', hinv', hown', hmg.1, hini', hfi', hmg.2, hgi', hoo', _,
      reach_run hreach hrun⟩
  · -- the load row
    obtain ⟨jl, hjl⟩ :=
      exists_sLatest (hsafe.cell tr s th0 hreach h0 lbl lsize th.st hd hI x a e ty w sa (.inl ht) hev hsa)
    rw [hsa] at hv
    rw [← wordLoc_toNat] at hex
    obtain ⟨-, -, hinv', -⟩ := hinv.load hwf _ hex hso ho (wordAddr_of_valRep_loc0 hv) hjl
    obtain ⟨-, k, v, hgv, htl, hrd'⟩ := stepOne_load_tlatestP _ hex hso ho hinv.coh
    obtain ⟨m, hm, hrep⟩ := hinv.mem.latestP_read hwf hinv.narrow (wordAddr_of_valRep_loc0 hv)
      (SLatestP.nil_iff.mpr hjl) htl hrd'
    have hX' := hX v ⟨m.val, m.view, jl⟩ (hrd _) (valRep_setWidth_of_fits hrep (read?_fits hfi.1 hfi.2 hrd'))
    obtain ⟨th', hstep, hte, hen, hp', hσ', hst'⟩ := src_load_step hP hS h0 hp ht hev hsa
      (hN.cell _ _ _ _ hI x a e ty w (.inl ht) hev) hjl hm (hN.noRet _ _ _ _ hX')
    have hrun := run_one hstep
    refine ⟨_, hrun, th', lbl, lsize, ts, none, set_one hs0, hσ' ▸ hσ, hst' ▸ hst, hp', ?_, trivial, hw', hb', hinv',
      hown', hmg.1, hini', hfi', hmg.2, hgi', hoo', _, reach_run hreach hrun⟩
    show I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩
    rw [hte, hen, hgv]; exact hX'
  · -- the store row
    obtain ⟨k, m, hkm, hml⟩ :=
      hsafe.cell tr s th0 hreach h0 lbl lsize th.st hd hI x a e ty w sa (.inr ⟨b, ht⟩) hev hsa
    obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
    rw [hml] at hoff
    obtain ⟨th', mv, hstep, hte, hen, hp', hσ', hst'⟩ := src_store_step hP hS h0 hp ht hev hsa
      (hN.cell _ _ _ _ hI x a e ty w (.inr ⟨b, ht⟩) hev) hevb (hN.noRet _ _ _ _ hX)
    rw [hsa] at hv
    rw [← wordLoc_toNat] at hex
    obtain ⟨hst'', q, hinv'⟩ := hinv.store (m := ⟨sa, wb.val, mv⟩) _ hex hso ho (wordAddr_of_valRep_loc0 hv) hoff hvb
    have hrun := run_one hstep
    refine ⟨_, hrun, th', lbl, lsize, _, none, set_one hs0, hσ' ▸ hσ, hst' ▸ hst, hp', ?_, trivial, hw', hb', hinv',
      hown', hmg.1, hini', hfi', hmg.2, hgi', hoo', _, reach_run hreach hrun⟩
    show I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩
    rw [hte, hen, hst'']; exact hX
  · -- the load of an exchange: the source stutters, holding the latest word
    obtain ⟨k, m0, hkm, hml⟩ := hsafe.xchg tr s th0 hreach h0 lbl lsize th.st hd hI x sa u v e hxs
    obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
    rw [hml] at hoff
    obtain ⟨jl, hjl⟩ := exists_sLatest ⟨k, m0, hkm, hml⟩
    have hwa := wordAddr_of_valRep_loc0 hA
    rw [← wordLoc_toNat] at hex
    obtain ⟨-, -, hinv', -⟩ := hinv.load hwf _ hex hso ho hwa hjl
    obtain ⟨-, k', r, hgr, htl, hrd'⟩ := stepOne_load_tlatestP _ hex hso ho hinv.coh
    obtain ⟨m, hm, hrep⟩ := hinv.mem.latestP_read hwf hinv.narrow hwa (SLatestP.nil_iff.mpr hjl) htl hrd'
    have hX' := hX r ⟨m.val, m.view, jl⟩ (hrd _) (valRep_setWidth_of_fits hrep (read?_fits hfi.1 hfi.2 hrd'))
    refine ⟨s, .refl _, th0, lbl, lsize, ts, some (A.toNat, ⟨m.val, m.view, jl⟩), hs0, hσ, hst, hp, ?_,
      ⟨sa, jl, m, hwa, hoff, hjl, hm, rfl⟩, hw', hb', hinv', hown', hmg.1, hini', hfi', hmg.2, hgi', hoo',
      tr, hreach⟩
    rw [hgr]; exact hX'
  · -- the store of an exchange: the source exchange, reading the held word
    obtain ⟨k, m0, hkm, hml⟩ := hsafe.xchg tr s th0 hreach h0 lbl lsize th.st hd hI x sa u v e hxs
    obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
    rw [hml] at hoff
    have hwa := wordAddr_of_valRep_loc0 hA
    have hhd : hd = some (A.toNat, wold) := hh0
    rw [hhd] at hhi
    obtain ⟨sa', jl, m, hwa', hoff', hjl, hm, rfl⟩ := hhi
    have hsa' : sa' = sa := hinv.mem.wordAddr_inj hwa' hwa hoff' hoff
    subst sa'
    obtain ⟨th', mv, hstep, hte, hen, hp', hσ', hst'⟩ := src_swap_step hP h0 hp hxs hev hjl hm
      (hN.noRet _ _ _ _ hI) (hN.noRet _ _ _ _ hX)
    rw [← wordLoc_toNat] at hex
    obtain ⟨hst'', q, hinv'⟩ := hinv.store (m := ⟨sa, wv.val, mv⟩) _ hex hso ho hwa hoff hvb
    have hrun := run_one hstep
    refine ⟨_, hrun, th', lbl, lsize, _, none, set_one hs0, hσ' ▸ hσ, hst' ▸ hst, hp', ?_, trivial, hw', hb', hinv',
      hown', hmg.1, hini', hfi', hmg.2, hgi', hoo', _, reach_run hreach hrun⟩
    show I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩
    rw [hte, hen, hst'']; exact hX
  · exact absurd ht (hN.noAlloc _ _ _ _ hI x a τ e)
  · exact absurd ht (hN.noAlloc _ _ _ _ hI x a τ e)

/-- **A certification step at a system call keeps `PreCore`**, matched by a
source run with no event: the thread resumes in a state `certSuccs` lists
(`Inv1.certSys`), memory and promises unchanged, paired past `Out.sys`'s
local run. -/
theorem core_sys (hP : HookOK P p) (hN : Nodes Λ p μ rd G own I) {rS : Range}
    {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk) {th : Thread isa} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isa))} {o : Outcome isa} {x : Kernel.KState}
    (h : PreCore Λ P p G own I th mem s) (hsi : Kernel.siteAt abi μ th.st = none) (hs : abi.atSys th.st = true)
    (hso : (Kernel.certSem abi Arch.tso μ x 0).step Arch.tso th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCore Λ P p G own I o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hst, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    tr, hreach⟩ := h
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  obtain ⟨sz, hc⟩ := hN.svc _ _ _ _ hI hs
  obtain ⟨K, call, hK, -, hdc, ⟨-, hcl, -, -⟩, hx⟩ := out_sys hc (hN.out _ _ _ _ hI (hT.off_sys hI hs)) (fun _ h => False.elim h)
  cases hK
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', hlr, hI'⟩ := hx _ hsu
  have hrun := hlr.run_source_nil hP h0 rfl rfl hσ hst hp (hN.noRet _ _ _ _ hI) (hN.noRet _ _ _ _ hI')
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  refine ⟨_, hrun, { th0 with term := c'.term, env := c'.env }, lbl, lsize, ts, c'.hold, set_one hs0, hσ, hst, hp,
    hI', holdInv_run hlr hhi, hw', (stepOneWith_bnd _ hso ho hb).1, hinv', ?_, ?_, ?_, ?_, ?_, ?_, ?_, _,
    reach_run hreach hrun⟩
  · rw [hm]; exact hown
  · rw [hm, hpr]; exact hsh
  · rw [hm]; exact hini
  · rw [hm]; exact hfi
  · rw [hm, hpr]; exact hgm
  · rw [hm]; exact hgi
  · rw [hm, hpr, hN.ownSys _ _ _ _ hI hs _ hdc _ hsu]; exact hoo

/-- **The certification step at a transfer site keeps `PreCore`**, matched by
a source run with no event: the site is the take's (`Nodes.noSite` at the
release site), where the step is the solo take (`Kernel.certSem_step_take_out`)
to the state past the `nop` with the solo configuration's pool bytes on the
range, which `TakePath.site`'s local run pairs for any pool bytes; memory
and promises unchanged, the words owned by `Nodes.ownTake`. -/
theorem core_site (hP : HookOK P p) (hN : Nodes Λ p μ rd G own I) {rS : Range}
    {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk) {th : Thread isa} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isa))} {o : Outcome isa} {x : Kernel.KState}
    (h : PreCore Λ P p G own I th mem s) (hsi : Kernel.siteAt abi μ th.st ≠ none)
    (hso : (Kernel.certSem abi Arch.tso μ x 0).step Arch.tso th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCore Λ P p G own I o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hst, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    tr, hreach⟩ := h
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  have ha : μ.site .take = some (pcOf th.st) := Classical.byContradiction fun hne =>
    hsi (Kernel.siteAt_eq_none_iff.mpr ⟨fun h => hne h, fun h => hN.noSite _ _ _ _ hI _ h rfl⟩)
  have hsa : Kernel.siteAt abi μ th.st = some .take := by
    unfold Kernel.siteAt; exact ite_eq_left ha
  obtain ⟨-, ⟨n, sz, hcn⟩, hsys, hsr, -, -, -, hrun⟩ := hT.site _ _ _ _ hI _ ha rfl
  obtain ⟨hot, hom⟩ := Kernel.certSem_step_take_out hsa hsys (X64.deps_of_atNop (atNop_of_cellAt hcn)) hso ho
  rw [hsr] at hot
  rw [hot, hom]
  obtain ⟨c', hlr, hI', -⟩ := hrun x.pmem
  have hrun' := hlr.run_source_nil hP h0 rfl rfl hσ hst hp (hN.noRet _ _ _ _ hI) (hN.noRet _ _ _ _ hI')
  exact ⟨_, hrun', { th0 with term := c'.term, env := c'.env }, lbl, lsize, ts, c'.hold, set_one hs0, hσ, hst, hp,
    hI', holdInv_run hlr hhi, hw, ⟨hb.1, hb.2⟩, ⟨hinv.1, hinv.2, hinv.3⟩, hown, hsh, hini, hfi, hgm, hgi,
    by show ExtRows.OwnOk (own (abi.skip _)) _ _; rw [hN.ownTake _ _ _ _ hI _ ha rfl]; exact hoo, _,
    reach_run hreach hrun'⟩

/-- **Every instruction step off a system call and off the transfer sites
keeps `PreCore`** (the form of `stepG_of`'s `hins`), by `core_step`. -/
theorem core_ins (hP : HookOK P p) (hN : Nodes Λ p μ rd G own I) (hS : SrcMem P p)
    (hsafe : SrcSafe P p I) (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) :
    ∀ th mem s outs o, PreCore Λ P p G own I th mem s → Kernel.siteAt abi μ th.st = none →
      abi.atSys th.st = false → stepOne Arch.tso th 0 mem = some outs → .ok o ∈ outs →
      ∃ s', PreCore Λ P p G own I o.thread o.mem s' := by
  intro th mem s outs o h hsi hns hso ho
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc =>
    (Kernel.siteAt_eq_none_iff.mp hsi).1 (by rw [ha, ← hpc]; rfl)
  obtain ⟨s', -, h'⟩ := core_step hP hN hS hsafe hrd hwf hGpl h hns hnt hso ho
  exact ⟨s', h'⟩

/-! ## The step-wise simulation -/

open Scc.Cert.Link in
/-- **The step-wise simulation** of a text loaded under `Λ` (`init_of_load`,
`r_step`, the node obligations under the loaded program's marks; `hG0`, the
loaded memory satisfies `G`; `hGpl`, `G` allows every value at a word of the
heap or the static image), on any target on `T`'s machine (`TOn`) whose
load of `asm` is `loadParsed` of the parse (`hl`). -/
theorem stepSim {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {offs : List (String × Nat)} {cells : List (Directive × Nat)} {secs : DataSecs} {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ cells secs offs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (cells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)) c0)
    (hP : HookOK P p) (hinit : P.init (s0 P.cap)) (hN : Nodes Λ p ((TOn A ld rs).marks asm Λ) rd G own I)
    (hS : SrcMem P p) (hsafe : SrcSafe P p I) {rS : Range} {Tk : State → Prop}
    (hT : TakePath Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata))) t0.1.mem)
    (hps : PromShared Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ))
    (hrd : ∀ w, rd w)
    (hwf : Λ.WF) (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) :
    StepSim (TOn A ld rs) (SrcSem.source P p) Λ asm (R Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ)) where
  init _ h := init_of_load hwf himg hss hw hinit hst htk0 (hown0 _ h) (hG0 _ h) (hl.symm.trans h)
  step _ _ _ _ _ h hs := r_step hP hN hS hsafe hT hps hrd hwf hGpl h hs

/-! ## The explicit witness -/

/-- **The witness of a one-thread pair**: thread 0 to thread 0, the labels'
placement, sizes and timestamp map of `Inv1`, the environment map of
`Placed` for frame 0, no marked place, no epochs, target epochs from the
last timestamp. -/
def wit (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (envm : String → Nat → Option (WordPlace T.M.I.RegId)) (last : Nat) : Witness T.M where
  thr i := if i = 0 then some 0 else none
  lbl := lbl
  lsize := lsize
  ts := ts
  env i d x k := if i = 0 ∧ d = 0 then envm x k else none
  marked _ _ := False
  since _ := 0
  tsFrom _ := last

/-- **`Components` for a one-thread pair**: the memory relation of `Inv1`
(`Components.ofMemRelP`; the unmirrored promises are thread 0's, and below
the last timestamp), the environment of `Placed`, and the stack range, if
any, the one range held (`HeldOk`): in the pool, owned by the one thread,
and off the shared messages (`MemIn`). -/
theorem components_one (hwf : Λ.WF) {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isa} {th0 : TermRun.TTh}
    {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat} {rS : Range} {Tk : State → Prop}
    {hl : List (Nat × Range)} (hth : t.1.threads = #[th]) (hheld : t.2.held = hl) (hh : HeldOk Λ rS Tk th.st hl)
    (hmi : MemIn Λ t.1.mem) (hs0 : s.ths = #[th0]) (hst : th0.stack = []) (hpl : Placed Λ lbl th.st (Ctl.of th0))
    (hinv : Inv1 Λ lbl lsize ts th t.1.mem s.mem) (hown : OwnMsgs t.1.mem) :
    ∃ w : Witness T.M, Components T.M Λ w t s ∧ w.thr 0 = some 0 := by
  obtain ⟨envm, hrep, htot, himm⟩ := hpl
  have hsr : ∀ j rg, T.M.stackRange t j = some rg → j = 0 ∧ rg = rS ∧ Owned Λ rS th.st := by
    intro j rg h
    change Kernel.stackRangeOf abi t j = some rg at h
    unfold Kernel.stackRangeOf at h
    split at h
    · cases h
    · rename_i tt htt
      obtain ⟨rfl, rfl⟩ := get_one hth htt
      rw [hheld] at h
      rcases hh with ⟨rfl, -⟩ | ⟨rfl, -, ho⟩
      · simp at h
      · refine ⟨rfl, ?_, ho⟩
        simp only [List.find?_cons, List.find?_nil] at h
        split at h
        · exact (Option.some.inj h).symm
        · cases h
  have hfe : frameEnvs th0 = [th0.env] := by simp [frameEnvs, hst]
  have hff : frameFv th0 = [exprFv th0.term] := by simp [frameFv, hst]
  have hs1 : ∀ {i} {th'}, s.ths[i]? = some th' → i = 0 ∧ th' = th0 := by
    intro i th' h
    rw [hs0] at h
    rcases i with _ | i
    · exact ⟨rfl, (Option.some.inj h).symm⟩
    · simp at h
  refine ⟨wit lbl lsize ts envm t.1.mem.last, Components.ofMemRelP (tp := []) (sp := []) hinv.mem
    { thr_total := ?_, thr_inj := ?_, thr_onto := ?_, env_rep := ?_, env_total := ?_,
      stack_pool := (fun j rg h => by obtain ⟨-, rfl, ho⟩ := hsr j rg h; exact ho.1),
      stack_disj := (fun j j' rg rg' hne h h' => absurd ((hsr j rg h).1.trans (hsr j' rg' h').1.symm) hne),
      stack_owned := (fun j rg h j' tt' htt a h8 h1 h2 => by
        obtain ⟨rfl, rfl, ho⟩ := hsr j rg h
        obtain ⟨rfl, rfl⟩ := get_one hth htt
        exact ⟨fun _ => rfl, fun _ => ho.2 a h8 h1 h2⟩),
      stack_private := (fun j rg h m hm hc => by
        obtain ⟨-, rfl, ho⟩ := hsr j rg h
        exact shared_not_pool hwf (memIn_msgs hmi m hm).addr (sub_contains ho.1 hc)),
      stack_marked := fun _ _ h => h.elim,
      stack_unmarked := fun _ _ _ _ _ _ _ _ _ _ h => h, env_imm := ?_ }
    (fun _ => rfl) (fun _ q hq => (hinv.mem.tq_le q hq).2) ?_, rfl⟩
  · intro i hi
    rw [hs0] at hi
    obtain rfl : i = 0 := by simpa using hi
    exact ⟨0, rfl, by rw [hth]; exact Nat.zero_lt_one⟩
  · intro i i' j h h'
    simp only [wit] at h h'
    by_cases hi : i = 0 <;> by_cases hi' : i' = 0
    · rw [hi, hi']
    · simp [hi'] at h'
    · simp [hi] at h
    · simp [hi] at h
  · intro j tt _ hj
    obtain ⟨rfl, -⟩ := get_one hth hj
    exact ⟨0, by rw [hs0]; exact Nat.zero_lt_one, rfl⟩
  · intro i th' j tt hi hj htt d e hd x ty ws hx k wd wp hwd hwp _hxf
    obtain ⟨rfl, rfl⟩ := hs1 hi
    simp only [wit, ite_true, Option.some.injEq] at hj
    subst hj
    obtain ⟨-, rfl⟩ := get_one hth htt
    simp only [wit, true_and] at hwp
    by_cases hd0 : d = 0
    · subst hd0
      simp only at hwp
      rw [hfe] at hd
      cases (show th'.env = e from Option.some.inj hd)
      exact hrep x ty ws hx k wd wp hwd hwp
    · simp [hd0] at hwp
  · intro i th' hi d e xs hd hxs _hxf x hx ty ws hl k hk
    obtain ⟨rfl, rfl⟩ := hs1 hi
    rw [hfe] at hd
    rw [hff] at hxs
    rcases d with _ | d
    · cases (show th'.env = e from Option.some.inj hd)
      cases (show exprFv th'.term = xs from Option.some.inj hxs)
      obtain ⟨pl, hpl⟩ := htot x hx ty ws hl k hk
      exact ⟨pl, by simp only [wit, true_and]; exact hpl⟩
    · simp at hd
  · intro i th' d e x k n hi hd hx
    obtain ⟨rfl, rfl⟩ := hs1 hi
    rcases d with _ | d
    · cases (show th'.term = e by simpa [frameTerms] using hd)
      simp only [wit, true_and] at hx
      exact himm x k n hx
    · simp [wit] at hx
  · intro q hq m' hg
    rw [hown q m' hg]
    exact ⟨th, by rw [hth]; rfl, hq⟩

/-- **`R` is explicit**: every related pair has a witness (`components_one`;
before the exit the environment is placed by `Nodes.place`). -/
theorem r_components (hN : Nodes Λ p μ rd G own I) (hwf : Λ.WF) {rS : Range} {Tk : State → Prop} {t : T.M.Cfg}
    {s : TermRun.Cfg} (h : R Λ P p G own I rS Tk μ t s) :
    ∃ w : Witness T.M, Components T.M Λ w t ((SrcSem.source P p).core s) := by
  rcases h with ⟨th, th0, j, lbl, lsize, ts, hl, pm, _, hth, ⟨E, hk⟩, -, hh, -, -, hs0, -, hst, -, hI, -, -, -, hinv,
      hown,
      hmi, -, -, -, -⟩ |
    ⟨th, th0, j, lbl, lsize, ts, hl, pm, o, hth, ⟨E, hk⟩, -, hh, hs0, -, hst, -, hpl, hinv, hown, hmi, -⟩
  · exact (components_one hwf hth (by rw [hk]; rfl) hh hmi hs0 hst
      (by have hpl := hN.place _ _ _ _ hI; exact hpl) hinv hown).imp
      fun _ h => h.1
  · exact (components_one hwf hth (by rw [hk]; rfl) hh hmi hs0 hst hpl hinv hown).imp fun _ h => h.1

/-! ## Progress -/

/-- **No promise at a `write`** in `Pre`: an open hypothesis. At every other
supported call a certified thread with promises has a kernel step after
which it is certified (`Kernel.sys_progress`; none is certified at `exit` or
`exit_group`, `Kernel.prom_nil_of_exit`). At a `write` the certification
has no branch, so a certified thread there has no promise
(`Kernel.prom_nil_of_write`); deriving this hypothesis from that is not yet
done here. The consumers' programs reach a
`write` only on the abort path, after which only private stores and
`exit_group` follow, so no promise is outstanding there; the discharge is
per program (once for all accepted programs: an open item). A fragment with
no state at a `write` discharges it (`NoWrite`, `writeNoProm_of_noWrite` in
`Spike/Lib/{isa}SegInst.lean`). -/
def WriteNoProm (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : Own) (I : Inv)
    (rS : Range) (Tk : State → Prop) (μ : Marks) : Prop :=
  ∀ t s th, Pre Λ P p G own I rS Tk μ t s → t.1.threads = #[th] → abi.atSys th.st = true →
    (∃ fd buf n, Kernel.callOf abi th = some (.write fd buf n)) → th.prom = []

/-- **Before the exit there is progress**: no fault (an `Out` row off a
system call has an instruction and no error outcome, every system call is
supported and touches nothing unmapped) and thread 0 steps: off a system
call by its `Out` row's outcome with no promise left, or, with promises, by
the first step of its certification; at a system call by the kernel's
return (with promises, `Kernel.sys_progress`; none at a `write`,
`WriteNoProm`, or at `exit_group`, `Kernel.prom_nil_of_exit`), or
`exit_group` (at an abort site as the abort, `AbortPath.at_`). -/
theorem pre_progress (hN : Nodes Λ p μ rd G own I) {Ab : State → Prop} (hA : AbortPath μ I Ab) {rS : Range}
    {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk) (hwf : Λ.WF) (hsvc : WriteNoProm Λ P p G own I rS Tk μ)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : Pre Λ P p G own I rS Tk μ t s) : T.M.Progress μ t := by
  have hwnp := hsvc t s
  have hpre := h
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, hh, hwr, hcert, hs0, hσ, hst, hp, hI, -, hw, hb,
      hinv,
    hown, hmi, -, -, -, hre⟩ := h
  have ht : t.1.threads[0]? = some th := by rw [hth]; rfl
  have hrk : t.2.runs 0 = true := by rw [hk]; rfl
  have hxk : t.2.exited = none := by rw [hk]; rfl
  have hruns : T.M.runs t 0 := ⟨⟨th, ht⟩, hxk, by show ¬ (t.2.runs 0 = false); rw [hrk]; simp⟩
  have hnh : th.halted = false := by
    by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
    · obtain ⟨a, ha, hpc⟩ := htk
      obtain ⟨n, sz, hcn⟩ := (hT.site _ _ _ _ hI a ha hpc).2.1
      simp [Thread.halted, Kraken.Promising.Lower.X64.exec_nop hcn]
    cases hs : abi.atSys th.st
    · have := ExtRows.out_exec hs (hN.out _ _ _ _ hI (fun a ha hpc => htk ⟨a, ha, hpc⟩))
      simp only [Thread.halted]
      cases he : isa.exec th.st
      · rw [he] at this; cases this
      · simp
    · obtain ⟨sz, hc⟩ := hN.svc _ _ _ _ hI hs
      simp [Thread.halted, Kraken.Promising.Lower.X64.exec_syscall hc]
  refine ⟨?_, .inr ⟨⟨0, hxk, hruns.2.2, th, ht, fun h => by rw [hnh] at h; cases h.1⟩, fun tid hl => ?_⟩⟩
  · rintro (⟨tid, m, ⟨⟨t1, ht1⟩, -, -⟩, hns, outs, hs, hm⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, ht1, -, -, hns, hex, htouch⟩))
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      have hs' : stepOne Arch.tso th 0 t.1.mem = some outs := by simp only [stepThread, ht1] at hs; exact hs
      cases hsy : abi.atSys th.st
      · by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
        · obtain ⟨a, ha, hpc⟩ := htk
          obtain ⟨n, sz, hcn⟩ := (hT.site _ _ _ _ hI a ha hpc).2.1
          exact Kraken.Promising.Lower.stepOne_silent_no_error Arch.tso 0 (Kraken.Promising.Lower.X64.exec_nop hcn)
            (Kraken.Promising.Lower.silentTree_done _) hs' m hm
        · exact ExtRows.out_no_error hsy (hN.out _ _ _ _ hI (fun a ha hpc => htk ⟨a, ha, hpc⟩)) hs' m hm
      · exact hns ⟨th, ht1, hsy⟩
    · unfold Kernel.faultAt at hf
      split at hf
      · rename_i t1 ht1
        obtain ⟨rfl, rfl⟩ := get_one hth ht1
        rw [hnh, Bool.or_false] at hf
        cases hsy : abi.atSys th.st
        · simp [hsy] at hf
        · obtain ⟨call, hd, -, hcl, -⟩ := hN.sysOk hT hI hsy
          rw [show Kernel.callOf abi th = some call from hd] at hf
          cases call with
          | clone st tl => exact hcl st tl rfl
          | _ => simp at hf
      · cases hf
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      rw [hk] at htouch
      exact hN.mapped _ _ _ _ hI hns e hex (touches_mono (fun _ _ h => mapped_KS h) htouch)
  · obtain ⟨-, -, t1, ht1, -⟩ := hl
    obtain ⟨rfl, rfl⟩ := get_one hth ht1
    by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
    · -- at the take site: the take
      obtain ⟨a, ha, hpc⟩ := htk
      obtain ⟨hntk, ⟨n, sz, hcn⟩, -, hsr, hsub, hpos, hrod, -⟩ := hT.site _ _ _ _ hI a ha hpc
      obtain rfl : hl = [] := by
        rcases hh with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact h
        · exact absurd h hntk
      have hf : Kernel.fresh t (Kernel.siteRange abi th.st) = true := by
        rw [hsr]; exact fresh_of hwf hk hsub hpos hrod hmi
      exact ⟨[], _, .xfer .take hruns ⟨a, ha, th, ht, hpc⟩
        (Kernel.xfer_take (K := abi) Arch.tso 1 ht hrk hxk (atNop_of_cellAt hcn) hf)⟩
    have hsite := no_site hN ht hI (fun a ha hpc => htk ⟨a, ha, hpc⟩)
    cases hs : abi.atSys th.st
    · have hnsys : ¬ T.M.atSys t 0 := fun ⟨t2, ht2, h2⟩ => by
        cases (show some t2 = some th from ht2.symm.trans ht)
        have h3 : abi.atSys th.st = true := h2
        rw [hs] at h3; cases h3
      by_cases hpn : th.prom = []
      · obtain ⟨outs, o, hso, ho, hpo⟩ :=
          ExtRows.out_progress (A := Arch.tso) (tid := 0) (mem := t.1.mem) hpn hb hs
            (hN.out _ _ _ _ hI (fun a ha hpc => htk ⟨a, ha, hpc⟩))
        exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, certOkC_of_prom_nil hpo, rfl⟩)⟩
      · obtain ⟨t', mem', hr, hp'⟩ := hcert
        cases hr with
        | refl => exact absurd hp' hpn
        | step hs1 hrest =>
          obtain ⟨outs, o, hso, ho, rfl⟩ := hs1
          replace hso : stepOne Arch.tso th 0 t.1.mem = some outs :=
            (Kernel.certSem_step_of_not_site (x := t.2) (siteAt_none hN hI fun a ha hpc => htk ⟨a, ha, hpc⟩)
              hs).symm.trans hso
          exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, ⟨t', mem', hrest, hp'⟩, rfl⟩)⟩
    · have hr := Kernel.ready_of abi (t := th) (c := t) hs hrk hxk
      obtain ⟨call, hd, hnx, hcl, -⟩ := hN.sysOk hT hI hs
      have hc : Kernel.callOf abi th = some call := hd
      have hsys : ∀ c', (kernel 1).sys μ 0 t [] c' → ∃ es c', T.M.Step μ 0 t es c' :=
        fun c' h => ⟨[], c', .sys hruns h (by simp) (by simp) (by simp)⟩
      by_cases hpn : th.prom = []
      rotate_left
      · -- with promises: no `write` (`WriteNoProm`), none at `exit_group`; elsewhere `Kernel.sys_progress`
        have hsn := siteAt_none hN hI (fun a ha hpc => htk ⟨a, ha, hpc⟩)
        cases call with
        | write fd buf n => exact absurd (hwnp th hpre hth hs ⟨fd, buf, n, hc⟩) hpn
        | exitGroup v => exact absurd (Kernel.prom_nil_of_exit hsn hs hd (.inr ⟨v, rfl⟩) hcert) hpn
        | exit => exact absurd rfl hnx
        | clone st tl => exact absurd rfl (hcl st tl)
        | _ =>
          obtain ⟨r, es, c', h, hca⟩ := Kernel.sys_progress ht hr hsn hc (fun _ _ _ h => by cases h)
            (fun _ _ h => by cases h) hpn hcert
          obtain rfl := Kernel.sysStep_ret_nil ht hc (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
            (fun h => by cases h) (fun _ h => by cases h) h
          exact hsys c' ⟨.ret r, h, hca⟩
      cases call with
      | write fd buf n =>
        by_cases hj : t.2.wr 0 = 0
        · exact hsys _ (Kernel.sys_writeIntr (K := abi) Arch.tso 1 ht hr hpn hc hj)
        · exact hsys _ (Kernel.sys_writeRet (K := abi) Arch.tso 1 ht hr hpn hc (Nat.pos_of_ne_zero hj))
      | futexWait => exact hsys _ (Kernel.sys_futexWait (K := abi) Arch.tso 1 ht hr hpn hc)
      | futexWake k => exact hsys _ (Kernel.sys_futexWake (K := abi) Arch.tso 1 ht hr hpn hc)
      | rtSigaction => exact hsys _ (Kernel.sys_rtSigaction (K := abi) Arch.tso 1 ht hr hpn hc)
      | archSetFs a => exact hsys _ (Kernel.sys_archSetFs (K := abi) Arch.tso 1 ht hr hpn hc)
      | exitGroup v =>
        by_cases hab : ∃ k a, μ.abortAt k = some a ∧ pcOf th.st = a
        · -- at an abort site: the abort
          obtain ⟨k, a, ha, hpc⟩ := hab
          obtain ⟨-, hv⟩ := hA.at_ _ _ _ _ hI k a ha hpc
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroupAbort (K := abi) Arch.tso 1 k ht hr hpn hc (hv v hd))
            (by simp) (fun k' hk => by obtain rfl : k' = k := by simpa using hk
                                       exact ⟨a, ha, th, ht, hpc⟩) (fun e he => by simp at he)⟩
        · have hnoab : ∀ k a, μ.abortAt k = some a → ¬ T.M.AtAddr a t 0 := fun k a ha ⟨t2, ht2, hpc⟩ => by
            cases (show some t2 = some th from ht2.symm.trans ht); exact hab ⟨k, a, ha, hpc⟩
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroup (K := abi) Arch.tso 1 ht hr hpn hc) (by simp)
            (fun k hk => by simp at hk) (fun _ _ => hnoab)⟩
      | exit => exact absurd rfl hnx
      | clone st tl => exact absurd rfl (hcl st tl)

/-- **After the exit there is progress** (`Kernel.exited_progress`). -/
theorem post_progress {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : Post Λ P p rS Tk t s) : T.M.Progress μ t := by
  obtain ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩ := h
  exact Kernel.exited_progress abi (o := o) (by rw [hk])

/-- **There is progress from `R`.** -/
theorem r_progress (hN : Nodes Λ p μ rd G own I) {Ab : State → Prop} (hA : AbortPath μ I Ab) {rS : Range}
    {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk) (hwf : Λ.WF) (hsvc : WriteNoProm Λ P p G own I rS Tk μ)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : R Λ P p G own I rS Tk μ t s) : T.M.Progress μ t :=
  h.elim (pre_progress hN hA hT hwf hsvc) post_progress

/-! ## Correctness -/

/-- The memory of a related target configuration is in the layout. -/
theorem r_memIn {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg} (h : R Λ P p G own I rS Tk μ t s) :
    MemIn Λ t.1.mem := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _⟩ <;> exact hmi

/-! ## The abort clause -/

/-- **`TI` is kept by every step from `R`**: off the phase an instruction
stays off it (`AbortPath.instr`), a promise and a byte of a `write` keep the
thread's state, a return enters the phase only at a refused `write`
(`AbortPath.sys`), which emits `writeErr`; an exit keeps the threads. -/
theorem ti_step (hN : Nodes Λ p μ rd G own I) {Ab : State → Prop} (hA : AbortPath μ I Ab) {rS : Range}
    {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk) {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es pre : List Ev} (h : R Λ P p G own I rS Tk μ t s) (hs : T.M.Step μ tid t es t')
    (hti : TI Ab pre t) : TI Ab (pre ++ es) t' := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  rotate_left
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hk]) hs).elim
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, -, hwr, -, hs0, hσ, hst, hp, hI, -, hw, hb, hinv,
      hown,
    hmi, -, -, -, hre⟩ := h
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  intro u hu hab
  by_cases hab0 : Ab th.st
  · exact List.mem_append_left _ (hti th ht1 hab0)
  refine List.mem_append_right _ ?_
  have hget : ∀ {v : Thread isa} {mem : Memory}, (t.1.withThread 0 v mem).threads[0]? = some u → u = v :=
    fun h => by
      simp only [Config.withThread, hth] at h
      exact (Option.some.inj h).symm
  by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
  · -- the take does not enter the phase (`AbortPath.take`)
    obtain ⟨a, ha, hpc⟩ := htk
    obtain ⟨-, rfl⟩ := step_take hN hT ht1 hI ha hpc hs
    obtain rfl := hget hu
    exact absurd hab (hA.take _ _ _ _ hI hab0 a ha hpc _)
  rcases X64Ext.step_cases_site ht1 hw hinv hs (no_spawn hN hT ht1 hI)
    (no_site hN ht1 hI (fun a ha hpc => htk ⟨a, ha, hpc⟩)) with
    ⟨rfl, hns, outs, o, hso, ho, rfl, -, -⟩ | ⟨rfl, w, rfl, -, -, -⟩ | ⟨pk, hsys, -, -⟩
  · obtain rfl := hget hu
    exact absurd hab (stepOne_allInv Arch.tso hso ho (hA.instr _ _ _ _ hI hab0 hns)
      ⟨fun _ => trivial, fun _ _ => trivial⟩).1
  · obtain rfl := hget hu
    exact absurd hab hab0
  · obtain ⟨hr, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsys (wr_le hk hwr)
    rcases hcases with ⟨fd, buf, n, rd', b, u', rfl, rfl, -, -, hust, -, rfl⟩ |
      ⟨r, rfl, -, -, -, -, u', hu', hsu, -⟩ | ⟨-, -, -, rfl⟩ | ⟨v, rfl, ⟨-, -, rfl⟩ | ⟨k, -, -, -, rfl⟩⟩
    · obtain rfl := hget hu
      exact absurd (hust ▸ hab) hab0
    · have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := Option.some.inj (hu'.symm.trans hu) ▸ hsu
      obtain ⟨fd, buf, n, rfl, hrf⟩ := hA.sys _ _ _ _ hI hab0 (atSys_of_ready hr) _ hcall _ hsu' hab
      obtain ⟨hc', hes⟩ := sysStep_write_ret ht1 hcall (wr_le hk hwr _ _ _ hcall) hsys
      have hu2 : u = Kernel.retThread abi th r := by rw [hc'] at hu; exact hget hu
      rw [hes (hrf r (by rw [hu2, Kernel.retThread_st]))]
      exact List.mem_singleton_self _
    all_goals
      obtain rfl : th = u := Option.some.inj (ht1.symm.trans hu)
      exact absurd hab hab0

/-- **`TI` along every run from `R`.** -/
theorem ti_run (hN : Nodes Λ p μ rd G own I) {Ab : State → Prop} (hA : AbortPath μ I Ab) {rS : Range}
    {Tk : State → Prop} (hT : TakePath Λ p μ I rS Tk)
    (hstep : ∀ {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev}, R Λ P p G own I rS Tk μ t s →
      T.M.Step μ tid t es t' → ∃ s', R Λ P p G own I rS Tk μ t' s')
    {t t' : T.M.Cfg} {tr : List Ev} (hr : T.M.Run μ t tr t') :
    ∀ {s pre}, R Λ P p G own I rS Tk μ t s → TI Ab pre t → TI Ab (pre ++ tr) t' := by
  induction hr with
  | refl => intro s pre _ h; rwa [List.append_nil]
  | step hs _ ih =>
    intro s pre hR h
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨s', hR'⟩ := hstep hR hs
    rw [← List.append_assoc]
    exact ih hR' (ti_step hN hA hT hR hs h)

/-- **An abort from `R` is justified**: it is taken at an abort site
(`Step.abort_at`), the `writeErr` one in the phase (`AbortPath.at_`), and the
trace has the refusal (`TI`); the `overflow` one with the source thread about
to overflow in a small environment, its next step crossing the budget
(`abortJustified_overflow_source`). -/
theorem r_abort (hN : Nodes Λ p μ rd G own I) (hwf : Λ.WF) {Ab : State → Prop} (hA : AbortPath μ I Ab) {B : Budget}
    {rS : Range} {Tk : State → Prop} {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es tr : List Ev} {k : AbortKind} (h : R Λ P p G own I rS Tk μ t s) (hti : TI Ab tr t)
    (hs : T.M.Step μ tid t es t') (hk : Ev.abort k ∈ es) :
    ∃ w i, Components T.M Λ w t ((SrcSem.source P p).core s) ∧ w.thr i = some tid ∧
      AbortJustified B (SrcSem.source P p) tr s i k := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hx⟩, _⟩
  rotate_left
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hx]) hs).elim
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, _, hth, ⟨E, hk'⟩, -, hh, -, -, hs0, hσ, hst, hp, hI, -, -, -, hinv, hown,
    hmi, -, -, -, -⟩ := h
  obtain ⟨a, ha, t2, ht2, hpc⟩ := hs.abort_at hk
  obtain ⟨rfl, rfl⟩ := get_one hth ht2
  obtain ⟨w, hw, hw0⟩ := components_one hwf hth (by rw [hk']; rfl) hh hmi hs0 hst
    (by have hpl := hN.place _ _ _ _ hI; exact hpl) hinv hown
  refine ⟨w, 0, hw, hw0, ?_⟩
  obtain ⟨⟨rfl, hab⟩ | ⟨rfl, hc, he⟩, -⟩ := hA.at_ _ _ _ _ hI k a ha hpc
  · exact hti th ht2 hab
  · exact abortJustified_overflow_source (by rw [hs0]; rfl) hc hσ hst hp he

open Scc.Cert.Link in
/-- **`Correct` for a one-thread program on a target on the canonical x86-64
machine** (`TOn`) whose load of `asm` is `loadParsed` of the parse (`hl`)
(`correct_of_stepSim` with `stepSim`, `r_progress`, `r_memIn`,
`r_abort` with `ti_run` from `ti_load`, `r_components`; `InLayout` from
`MemIn`, `inLayout_of_memIn`). -/
theorem correctKOn {B : Budget} {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {offs : List (String × Nat)} {cells : List (Directive × Nat)} {secs : DataSecs} {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ cells secs offs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (cells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, (TOn A ld rs).load asm Λ = some t0) (hP : HookOK P p) (hinit : P.init (s0 P.cap))
    (hN : Nodes Λ p ((TOn A ld rs).marks asm Λ) rd G own I) (hS : SrcMem P p) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata))) t0.1.mem)
    (hps : PromShared Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ))
    (hsvc : WriteNoProm Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath ((TOn A ld rs).marks asm Λ) I Ab)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata))) :
    Correct (TOn A ld rs) (SrcSem.source P p) Λ B asm := by
  have hsim := stepSim hl himg hss hw hst hP hinit hN hS hsafe hT htk0 hown0 hps hrd hwf hG0 hGpl
  refine correct_of_stepSim hsim hwf hload (fun t0 tr t h0 hr => ?_)
    (fun t0 tr t tid es t' k s h0 hr _ hR hs hk => ?_)
    (fun t s hR => r_components hN hwf hR)
  · obtain ⟨s, -, hR⟩ := hsim.reach h0 hr
    exact ⟨r_progress hN hA hT hwf hsvc hR, inLayout_of_memIn (r_memIn hR)⟩
  · obtain ⟨s0', -, hR0⟩ := hsim.init t0 h0
    have hti := ti_run hN hA hT
      (fun hR hs => let ⟨s', _, h'⟩ := r_step hP hN hS hsafe hT hps hrd hwf hGpl hR hs; ⟨s', h'⟩)
      hr hR0 (pre := []) (fun th h hab => absurd hab (ti_load hab0 (hl.symm.trans h0) th h))
    rw [List.nil_append] at hti
    exact r_abort hN hwf hA hR hti hs hk

open Scc.Cert.Link in
/-- **`Correct` for a one-thread program on the canonical x86-64 target**:
`correctKOn` at `T`, the load by `load_of_parsed`. -/
theorem correctK {B : Budget} {asm : Asm} {cells : List (Directive × Nat)} {secs : DataSecs} {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hpa : cellsOf asm = some cells)
    (hd : dataSections asm.text = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (cells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, T.load asm Λ = some t0) (hP : HookOK P p) (hinit : P.init (s0 P.cap))
    (hN : Nodes Λ p (T.marks asm Λ) rd G own I) (hS : SrcMem P p) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p (T.marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, T.load asm Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata))) t0.1.mem)
    (hps : PromShared Λ P p G own I rS Tk (T.marks asm Λ)) (hsvc : WriteNoProm Λ P p G own I rS Tk (T.marks asm Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath (T.marks asm Λ) I Ab)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata))) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctKOn (A := Asm) (ld := T.load) (rs := T.resolve) (load_of_parsed (kernel 1) Entry.linux Λ hpa hd)
    himg hss hw hst hload hP hinit hN hS hsafe hT htk0 hown0 hps hsvc hrd hwf hG0 hGpl hA hab0

end Spike.Lib.X64Consumer
