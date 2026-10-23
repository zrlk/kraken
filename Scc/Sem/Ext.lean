/-
The extended target machine, as an abstract interface.

Kraken's Promising machine (`Kraken.Promising.Config`, stepped by the
fuel-free `Live.Inf.StepSemInf`) has no thread creation, no system calls, no
observable trace, no thread pointer and no way to move memory between a
thread's private memory (`dmem`) and the shared stack pool. The `scc`
correctness statement needs all of them. This file does not change Kraken: it
states what the statement needs from an extended machine as a structure
(`ExtMachine`), and gives the existing machine as the instance with empty
extensions (`ExtMachine.ofBase`). The concrete extension is implemented in
Kraken later, as another instance; `Scc/DESIGN.md` §2 describes it.

**The instruction step is not a field.** Every instance steps an instruction
of a running thread by exactly the existing `Live.Inf.StepSemInf A tid` on
`Config I` (`ExtMachine.Step.instr`), leaving the extension state alone,
except that promises are certified with the instance's certification
semantics `cexec` (`StepSemC`; Kraken's own `exec` by default, where
`StepSemC` is `StepSemInf`, `stepSemC_exec`), which may depend on the code
marks, the extension state and the thread. The
extension can only *gate* it (`runs`: dormant thread slots and an exited
process take no step at all; `atSys`: a thread at a system-call instruction
takes no instruction step; a thread at a range-transfer site takes no
instruction step either) and *add* steps beside it (`spawn`, `sys`, `xfer`,
each also gated by `runs`; `xfer` only at the transfer sites, where it
replaces the instruction step, and `abort k` only at the abort site of kind
`k`: the code marks `Marks` of the loaded program, given with the step
relation). This is how every existing theorem about the machine stays
meaningful: an instance with empty extensions is the existing machine
(`ofBase_run_iff`).

Fields:

- `X`: the extension state (kernel-side state: dormant/active thread slots,
  futex wait queues, the process exit status, per-thread stack ranges).
  The thread pointer (`%fs` base, `TPIDR_EL0`) is a register of the thread's
  ISA state, not part of `X`.
- `runs c tid`: thread `tid` may take steps (an active slot of a process
  that has not exited).
- `atSys c tid`: thread `tid` is at a system-call instruction.
- `spawn μ tid`, `sys μ tid`, `xfer k tid`: the thread-creation step, the
  other system-call steps (with the events they emit), and the
  range-transfer step of kind `k` of thread `tid` (the first two under the
  code marks `μ`, which certification after the step may need).
- `cexec μ x tid`: the certification semantics (`CertSem`) of thread `tid`.
- `pc`: the program counter of a thread state (to locate the transfer and
  abort sites).
- Observations: `live`, `exited`, `fault`, `regVal`, `privLoad`,
  `stackRange` (documented at each field). A refused `write` is not an
  observation but an event (`Ev.writeErr`) of the `sys` step.
-/
import Scc.Sem.Basic
import Kraken.Promising.LiveSemInf

namespace Scc.Sem

open Kraken.Promising

/-! ## Certification with a certification semantics

Kraken certifies a promise by running the thread alone with the ISA's own
`exec`, under which a system call faults (`MachineData.pendingSyscall`): no
certification passes a system call. An extended machine certifies with its
own semantics instead (`ExtMachine.cexec`, a `CertSem`: an event tree and
register dependencies per state): the canonical targets' is the ISA's on
every instruction but a transfer site or a system call, where it is the
kernel's step of the thread run alone (`Kernel.certSem`). The steps below
are Kraken's `InstrSemInf`, `PromSemInf` and `StepSemInf` with `CertOk`
replaced by `CertOkC A cs`; the thread's own steps still use `I.exec`
(`stepOne`). With `cs = CertSem.ofExec I.exec` they are Kraken's
(`stepSemC_exec`). -/

variable {I : ISA}

/-! ## Certification semantics with their own dependencies

A certification semantics gives, per state, the instruction's event tree
and its register dependencies (`InstrDeps`). Kraken's `stepOneWith` takes
the tree from `cexec` but the dependencies from the ISA (`I.deps`). The
canonical targets need their own at a system call: there the kernel writes
the result registers with no register input (`Kernel.retThread`), whereas
the ISA's dependencies of `svc`/`syscall` are empty. -/

/-- **A certification semantics**: the event tree of the instruction at a
state, and its register dependencies. -/
structure CertSem (I : ISA) where
  exec : I.State → Option (EvTree I.State)
  deps : I.State → Kraken.InstrDeps I.RegId

/-- The semantics with the tree `cexec` and the ISA's dependencies. -/
def CertSem.ofExec (cexec : I.State → Option (EvTree I.State)) : CertSem I := ⟨cexec, I.deps⟩

/-- Kraken's `stepOneWith` with the dependencies `cdeps` in place of
`I.deps` (otherwise verbatim). -/
def stepOneWithD (A : Arch) (cexec : I.State → Option (EvTree I.State)) (cdeps : I.State → Kraken.InstrDeps I.RegId)
    (t : Thread I) (tid : Nat) (mem : Memory) : Option (List (Except String (Kraken.Promising.Outcome I))) := do
  let tree ← cexec t.st
  let d := cdeps t.st
  let iv := instrViews t d
  let ctx : Ctx := { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }
  return (runTree A tid iv ctx tree).flatMap fun
    | .error m => [.error m]
    | .ok (st, c') => (finishInstr t d iv st c').map fun th =>
        .ok { thread := th, mem := c'.mem, promisedNow := c'.promisedNow, log := c'.log }

/-- One instruction under the certification semantics `cs`. -/
def CertSem.step (A : Arch) (cs : CertSem I) (t : Thread I) (tid : Nat) (mem : Memory) :
    Option (List (Except String (Kraken.Promising.Outcome I))) :=
  stepOneWithD A cs.exec cs.deps t tid mem

/-- A function `cexec` is the certification semantics with the tree `cexec`
and the ISA's dependencies (`CertSem.ofExec`). -/
instance : Coe (I.State → Option (EvTree I.State)) (CertSem I) := ⟨CertSem.ofExec⟩

/-- Under `CertSem.ofExec cexec` a step is Kraken's `stepOneWith cexec`. -/
@[simp] theorem CertSem.step_ofExec (A : Arch) (cexec : I.State → Option (EvTree I.State)) (t : Thread I)
    (tid : Nat) (mem : Memory) : (CertSem.ofExec cexec).step A t tid mem = stepOneWith A cexec t tid mem := rfl

/-- With the ISA's dependencies, `stepOneWithD` is Kraken's `stepOneWith`. -/
theorem stepOneWithD_deps (A : Arch) (cexec : I.State → Option (EvTree I.State)) (t : Thread I) (tid : Nat)
    (mem : Memory) : stepOneWithD A cexec I.deps t tid mem = stepOneWith A cexec t tid mem := rfl

/-- **Where the dependencies agree with the ISA's**, `stepOneWithD` is
Kraken's `stepOneWith`. -/
theorem stepOneWithD_eq {A : Arch} {cexec : I.State → Option (EvTree I.State)}
    {cdeps : I.State → Kraken.InstrDeps I.RegId} {t : Thread I} {tid : Nat} {mem : Memory}
    (h : cdeps t.st = I.deps t.st) : stepOneWithD A cexec cdeps t tid mem = stepOneWith A cexec t tid mem := by
  unfold stepOneWithD; rw [h]; rfl

/-- One instruction of thread `tid`, run alone under the certification
semantics `cs` (`CertSem.step`: Kraken's `stepOneWith`, the step of
`certifyWith`, with `cs`'s dependencies). -/
def ThreadStepC (A : Arch) (cs : CertSem I) (tid : Nat)
    (p q : Thread I × Memory) : Prop :=
  ∃ outs o, cs.step A p.1 tid p.2 = some outs ∧ .ok o ∈ outs ∧ q = (o.thread, o.mem)

/-- Promise-free solo runs under `cs`. -/
inductive ThreadNPC (A : Arch) (cs : CertSem I) (tid : Nat) :
    Thread I × Memory → Thread I × Memory → Prop
  | refl (p : Thread I × Memory) : ThreadNPC A cs tid p p
  | step {p q r : Thread I × Memory} : ThreadStepC A cs tid p q → ThreadNPC A cs tid q r →
      ThreadNPC A cs tid p r

/-- **Certification under `cs`**: some promise-free solo run under `cs`
empties the thread's promise set (Kraken's `CertOk`, with `cs` for
`I.exec` and `I.deps`). -/
def CertOkC (A : Arch) (cs : CertSem I) (tid : Nat) (t : Thread I)
    (mem : Memory) : Prop :=
  ∃ t' mem', ThreadNPC A cs tid (t, mem) (t', mem') ∧ t'.prom = []

/-- An instruction step of `tid` certified under `cs` (`InstrSemInf`
with `CertOkC`). -/
def InstrSemC (A : Arch) (cs : CertSem I) (tid : Nat) (c c' : Config I) : Prop :=
  ∃ t outs o, c.threads[tid]? = some t ∧ stepOne A t tid c.mem = some outs ∧ .ok o ∈ outs ∧
    CertOkC A cs tid o.thread o.mem ∧ c' = c.withThread tid o.thread o.mem

/-- A promise step of `tid` certified under `cs` (`PromSemInf` with
`CertOkC`). -/
def PromSemC (A : Arch) (cs : CertSem I) (tid : Nat) (c c' : Config I) : Prop :=
  ∃ (t : Thread I) (w : Msg), c.threads[tid]? = some t ∧ w.tid = tid ∧
    CertOkC A cs tid (Live.Sem.promThread t c.mem w) (c.mem.append w).1 ∧
    c' = c.withThread tid (Live.Sem.promThread t c.mem w) (c.mem.append w).1

/-- **A step of thread `tid` certified under `cs`.** -/
def StepSemC (A : Arch) (cs : CertSem I) (tid : Nat) (c c' : Config I) : Prop :=
  InstrSemC A cs tid c c' ∨ PromSemC A cs tid c c'

/-- Under the ISA's own semantics a certification step is Kraken's. -/
theorem threadStepC_exec {A : Arch} {tid : Nat} {p q : Thread I × Memory} :
    ThreadStepC A I.exec tid p q ↔ ThreadStep A tid p q := Iff.rfl

/-- Under the ISA's own semantics certification is Kraken's `CertOk`. -/
theorem certOkC_exec {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory} :
    CertOkC A I.exec tid t mem ↔ CertOk A tid t mem := by
  have h1 : ∀ {p q : Thread I × Memory}, ThreadNPC A I.exec tid p q → ThreadNP A tid p q := by
    intro p q h
    induction h with
    | refl => exact .refl _
    | step hs _ ih => exact .step (threadStepC_exec.mp hs) ih
  have h2 : ∀ {p q : Thread I × Memory}, ThreadNP A tid p q → ThreadNPC A I.exec tid p q := by
    intro p q h
    induction h with
    | refl => exact .refl _
    | step hs _ ih => exact .step (threadStepC_exec.mpr hs) ih
  exact ⟨fun ⟨t', m', h, hp⟩ => ⟨t', m', h1 h, hp⟩, fun ⟨t', m', h, hp⟩ => ⟨t', m', h2 h, hp⟩⟩

/-- **Under the ISA's own semantics a certified step is Kraken's
`StepSemInf`.** -/
theorem stepSemC_exec {A : Arch} {tid : Nat} {c c' : Config I} :
    StepSemC A I.exec tid c c' ↔ Live.Inf.StepSemInf A tid c c' := by
  unfold StepSemC InstrSemC PromSemC Live.Inf.StepSemInf Live.Inf.InstrSemInf Live.Inf.PromSemInf
  simp only [certOkC_exec]

/-- A thread with no outstanding promise is certified, under any semantics. -/
theorem certOkC_of_prom_nil {A : Arch} {cs : CertSem I} {tid : Nat}
    {t : Thread I} {mem : Memory} (h : t.prom = []) : CertOkC A cs tid t mem :=
  ⟨t, mem, .refl _, h⟩

/-- The thread of a certified step exists. -/
theorem StepSemC.thread {A : Arch} {cs : CertSem I} {tid : Nat}
    {c c' : Config I} (h : StepSemC A cs tid c c') : ∃ t, c.threads[tid]? = some t := by
  rcases h with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩

/-- **The code marks of a loaded program**, in the model's code addresses
(the target resolves them from labels, `Target.resolve` in
`Scc/Sem/Correct.lean`): the address of the range-transfer site of each
kind (`XferKind.label`), where a thread takes the transfer and no
instruction step, and the address of the abort site (the `exit_group` of
the abort stub) of each kind, if resolved. -/
structure Marks where
  site : XferKind → Option Nat
  abortAt : AbortKind → Option Nat

/-- **The extended machine interface.** See the module docstring.

Every field is a parameter, so an arbitrary instance can make the statement
of `Scc/Sem/Correct.lean` trivial (for instance `fault := fun _ => False`
hides faults). The statement
means something only for the canonical instances, one per ISA, which are
part of the trusted base; a certificate states `Correct` for the canonical
target of its architecture, never for an instance supplied by `scc`. -/
structure ExtMachine where
  /-- The ISA (AArch64 `isaLSE2` or x64 `isa`, with the extensions of
  `Scc/DESIGN.md` §2). -/
  I : ISA
  /-- The architecture profile (`Arch.armv8` or `Arch.tso`). -/
  A : Arch
  /-- The extension state. -/
  X : Type
  /-- The semantics a promise of thread `tid` is certified with
  (`CertOkC`), under the code marks `μ` and with extension state `x` at the
  step: the ISA's own by default; the canonical targets' is the solo
  projection of the kernel step (`Kernel.certSem`). The thread's own
  instruction steps always use `I.exec`. -/
  cexec : Marks → X → Nat → CertSem I := fun _ _ _ => CertSem.ofExec I.exec
  /-- Thread `tid` may take steps (an active slot of a process that has not
  exited); every step of a thread that does not run is excluded. -/
  runs : Config I × X → Nat → Prop
  /-- Thread `tid` is at a system-call instruction (`svc #0` / `syscall`):
  it takes no instruction step there, only `spawn` or `sys`. -/
  atSys : Config I × X → Nat → Prop
  /-- Thread `tid` creates a thread (`clone`): activates a dormant slot with
  the child's initial state and thread pointer. -/
  spawn : Marks → Nat → Config I × X → Config I × X → Prop
  /-- Thread `tid` performs a system call other than `clone` (`write`,
  `exit`, `exit_group`, `futex`, `rt_sigaction`, `arch_prctl`), or one step
  of one, emitting the listed events: at most one per step (`Step.sys`), so
  a `write` of `k` bytes is `k` steps, one `out` byte each, between which
  other threads may step (no atomicity of a `write` call); `writeErr` for a
  refused `write`; `exit` or `abort k` for `exit_group`. -/
  sys : Marks → Nat → Config I × X → List Ev → Config I × X → Prop
  /-- Thread `tid`, at the transfer site of kind `k`, moves the stack-pool
  range its argument registers give into (`take`) or out of (`release`) its
  private memory, and moves past the site. -/
  xfer : XferKind → Nat → Config I × X → Config I × X → Prop
  /-- Thread `tid` exists and has not finished: progress must be possible for
  it. -/
  live : Config I × X → Nat → Prop
  /-- The configuration has terminated, and how. -/
  exited : Config I × X → Option Outcome
  /-- Some thread has a faulting step, or is stuck in a way the statement
  forbids (in the extension: a thread halted off its exit path, a misaligned
  stack pointer, an unsupported system call). -/
  fault : Config I × X → Prop
  /-- The 64-bit value of a register of a thread state. -/
  regVal : I.State → I.RegId → BitVec 64
  /-- An 8-byte load from the thread's private memory, if all 8 bytes are
  mapped there. -/
  privLoad : I.State → BitVec 64 → Option (BitVec 64)
  /-- The current stack range of thread `tid` (from its control block). -/
  stackRange : Config I × X → Nat → Option Range
  /-- The program counter of a thread state. -/
  pc : I.State → Nat

namespace ExtMachine

variable (M : ExtMachine)

/-- Configurations of the extended machine. -/
abbrev Cfg : Type := Config M.I × M.X

/-- Thread `tid` exists and its program counter is in the range `g`. -/
def AtPc (g : Range) (c : M.Cfg) (tid : Nat) : Prop :=
  ∃ t, c.1.threads[tid]? = some t ∧ g.contains (M.pc t.st)

/-- Thread `tid` exists and its program counter is `a`. -/
def AtAddr (a : Nat) (c : M.Cfg) (tid : Nat) : Prop :=
  ∃ t, c.1.threads[tid]? = some t ∧ M.pc t.st = a

/-- Thread `tid` is at the transfer site of kind `k`. -/
def AtSite (μ : Marks) (k : XferKind) (c : M.Cfg) (tid : Nat) : Prop :=
  ∃ a, μ.site k = some a ∧ M.AtAddr a c tid

/-- **One step of thread `tid`**, with the events it emits, under the code
marks `μ` of the loaded program: an instruction step of the existing
machine, or one of the extension's steps; all only if the thread runs; an
instruction step only off a system-call instruction and off the transfer
sites; a range transfer of kind `k` only at the site of kind `k`
(`μ.site k`), where it is the only step: the transfer is forced, and its
range is the one the thread's registers give, not a choice of the run
(`Scc/DESIGN.md` §2.6); a system call emits at most one
event, `abort k` only at the abort site of kind `k` (`μ.abortAt k`), and an
exit never at an abort site. -/
inductive Step (μ : Marks) : Nat → M.Cfg → List Ev → M.Cfg → Prop
  | instr {tid : Nat} {c : M.Cfg} {c' : Config M.I} :
      M.runs c tid → ¬ M.atSys c tid → (∀ k, ¬ M.AtSite μ k c tid) → StepSemC M.A (M.cexec μ c.2 tid) tid c.1 c' →
      Step μ tid c [] (c', c.2)
  | spawn {tid : Nat} {c c' : M.Cfg} : M.runs c tid → M.spawn μ tid c c' → Step μ tid c [] c'
  | sys {tid : Nat} {c c' : M.Cfg} {es : List Ev} :
      M.runs c tid → M.sys μ tid c es c' → es.length ≤ 1 →
      (∀ k, Ev.abort k ∈ es → ∃ a, μ.abortAt k = some a ∧ M.AtAddr a c tid) →
      (∀ e, Ev.exit e ∈ es → ∀ k a, μ.abortAt k = some a → ¬ M.AtAddr a c tid) → Step μ tid c es c'
  | xfer {tid : Nat} {c c' : M.Cfg} (k : XferKind) : M.runs c tid → M.AtSite μ k c tid → M.xfer k tid c c' →
      Step μ tid c [] c'

/-- Runs of the extended machine, with their traces. -/
def Run (μ : Marks) : M.Cfg → List Ev → M.Cfg → Prop := LRun fun c es c' => ∃ tid, M.Step μ tid c es c'

/-- **Progress at `c`**: no fault, and either the process has terminated or
some thread is live and every live thread can step. A configuration with no
live thread that has not terminated (every thread gone without an exit
outcome) is not progress. A thread blocked in the kernel is not a separate
case: with the futex model of `Scc/DESIGN.md` (§3, K7: spurious returns) a
wait can always step. -/
def Progress (μ : Marks) (c : M.Cfg) : Prop :=
  ¬ M.fault c ∧
    ((M.exited c).isSome ∨ ((∃ tid, M.live c tid) ∧ ∀ tid, M.live c tid → ∃ es c', M.Step μ tid c es c'))

variable {M} in
/-- **Every step is gated by `runs`**: a thread that does not run takes no
step (no instruction, spawn, system call or range transfer). -/
theorem Step.runs {μ : Marks} {tid : Nat} {c c' : M.Cfg} {es : List Ev} (h : M.Step μ tid c es c') :
    M.runs c tid := by
  cases h <;> assumption

variable {M} in
/-- **At most one event per step**: a `write` of several bytes is several
steps, which other threads' steps may interleave. -/
theorem Step.events_le_one {μ : Marks} {tid : Nat} {c c' : M.Cfg} {es : List Ev} (h : M.Step μ tid c es c') :
    es.length ≤ 1 := by
  cases h with
  | sys _ _ h _ _ => exact h
  | _ => simp

variable {M} in
/-- **Aborts are classified by site**: a step that emits `abort k` is taken
by a thread at the resolved abort site of kind `k`. -/
theorem Step.abort_at {μ : Marks} {tid : Nat} {c c' : M.Cfg} {es : List Ev} {k : AbortKind}
    (h : M.Step μ tid c es c') (hk : Ev.abort k ∈ es) : ∃ a, μ.abortAt k = some a ∧ M.AtAddr a c tid := by
  cases h with
  | sys _ _ _ ha _ => exact ha k hk
  | _ => simp at hk

variable {M} in
/-- **A range transfer happens only at a transfer site**: an extension step
that is neither a spawn nor a system call, with no events, from a thread at
no transfer site, is an instruction step. -/
theorem Step.xfer_atSite {μ : Marks} {tid : Nat} {c c' : M.Cfg} (h : M.Step μ tid c [] c')
    (hn : ∀ k, ¬ M.AtSite μ k c tid) (hsp : ¬ M.spawn μ tid c c') (hsy : ¬ M.sys μ tid c [] c') :
    ¬ M.atSys c tid ∧ StepSemC M.A (M.cexec μ c.2 tid) tid c.1 c'.1 ∧ c'.2 = c.2 := by
  cases h with
  | instr _ ha _ hs => exact ⟨ha, hs, rfl⟩
  | spawn _ h => exact absurd h hsp
  | sys _ h _ _ _ => exact absurd h hsy
  | xfer k _ hp _ => exact absurd hp (hn k)

variable {M} in
/-- **The transfer is forced**: at a transfer site a thread takes no
instruction step; every step it takes there is a spawn, a system call, or a
transfer of the kind of a site it is at. -/
theorem Step.at_site {μ : Marks} {tid : Nat} {c c' : M.Cfg} {es : List Ev} {k : XferKind}
    (h : M.Step μ tid c es c') (hs : M.AtSite μ k c tid) :
    M.spawn μ tid c c' ∨ M.sys μ tid c es c' ∨ (es = [] ∧ ∃ k', M.AtSite μ k' c tid ∧ M.xfer k' tid c c') := by
  cases h with
  | instr _ _ hn _ => exact absurd hs (hn k)
  | spawn _ h => exact .inl h
  | sys _ h _ _ _ => exact .inr (.inl h)
  | xfer k' _ hs' hx => exact .inr (.inr ⟨rfl, k', hs', hx⟩)

/-! ## The existing machine as an instance -/

/-- **The existing machine with empty extensions.** No extra state, no extra
steps, every thread runs; a thread is live until it has halted with no
outstanding promise, the configuration has terminated when it is
`Config.final`, and a fault is a faulting instruction step
(`Config.FaultStep`). The register and private-memory observations are the
ISA's, supplied by the caller. -/
def ofBase (I : ISA) (A : Arch) (regVal : I.State → I.RegId → BitVec 64)
    (privLoad : I.State → BitVec 64 → Option (BitVec 64)) : ExtMachine where
  I := I
  A := A
  X := Unit
  runs _ _ := True
  atSys _ _ := False
  spawn _ _ _ _ := False
  sys _ _ _ _ _ := False
  xfer _ _ _ _ := False
  live c tid := ∃ t, c.1.threads[tid]? = some t ∧ ¬ (t.halted = true ∧ t.prom = [])
  exited c := if c.1.final then some .halted else none
  fault c := ∃ tid m, c.1.FaultStep A tid m
  regVal := regVal
  privLoad := privLoad
  stackRange _ _ := none
  pc _ := 0

section ofBase

variable {I : ISA} {A : Arch} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)}

@[simp] theorem ofBase_runs {c : (ofBase I A rv pl).Cfg} {tid : Nat} : (ofBase I A rv pl).runs c tid :=
  trivial

@[simp] theorem ofBase_exited {c : (ofBase I A rv pl).Cfg} :
    (ofBase I A rv pl).exited c = if c.1.final then some .halted else none := rfl

@[simp] theorem ofBase_stackRange {c : (ofBase I A rv pl).Cfg} {tid : Nat} :
    (ofBase I A rv pl).stackRange c tid = none := rfl

@[simp] theorem ofBase_fault {c : (ofBase I A rv pl).Cfg} :
    (ofBase I A rv pl).fault c ↔ ∃ tid m, c.1.FaultStep A tid m := Iff.rfl

/-- A step of the base instance is a step of the existing machine, with no
event, under any marks (the converse, `ofBase_step_iff`, needs marks with
no transfer site). -/
theorem ofBase_step_inv {μ : Marks} {tid : Nat} {c c' : (ofBase I A rv pl).Cfg} {es : List Ev}
    (h : (ofBase I A rv pl).Step μ tid c es c') : es = [] ∧ Live.Inf.StepSemInf A tid c.1 c'.1 := by
  cases h with
  | instr _ _ _ hs => exact ⟨rfl, stepSemC_exec.mp hs⟩
  | spawn _ h => exact h.elim
  | sys _ h _ _ _ => exact h.elim
  | xfer _ _ _ h => exact h.elim

/-- A run of the base instance is a run of the existing machine, with an
empty trace, under any marks (the converse is in `ofBase_run_iff`). -/
theorem ofBase_run_inv {μ : Marks} {c c' : (ofBase I A rv pl).Cfg} {tr : List Ev}
    (h : (ofBase I A rv pl).Run μ c tr c') : tr = [] ∧ Live.Inf.ReachableSemInf A c.1 c'.1 := by
  induction h with
  | refl => exact ⟨rfl, .refl _⟩
  | step hs _ ih =>
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨hes, hs'⟩ := ofBase_step_inv hs
    obtain ⟨htr, hr⟩ := ih
    subst hes htr
    exact ⟨rfl, .step tid hs' hr⟩

/-- A step of the base instance is a step of the existing machine (under
marks with no transfer site). -/
theorem ofBase_step_iff {μ : Marks} (hμ : ∀ k, μ.site k = none) {tid : Nat} {c c' : (ofBase I A rv pl).Cfg}
    {es : List Ev} : (ofBase I A rv pl).Step μ tid c es c' ↔ es = [] ∧ Live.Inf.StepSemInf A tid c.1 c'.1 := by
  constructor
  · intro h
    cases h with
    | instr _ _ _ hs => exact ⟨rfl, stepSemC_exec.mp hs⟩
    | spawn _ h => exact h.elim
    | sys _ h _ _ _ => exact h.elim
    | xfer _ _ _ h => exact h.elim
  · rintro ⟨rfl, hs⟩
    obtain ⟨c1, ⟨⟩⟩ := c'
    exact .instr trivial id (fun k ⟨a, ha, _⟩ => by simp [hμ k] at ha) (stepSemC_exec.mpr hs)

/-- **Conservativity of the interface**: the runs of the base instance are
exactly the runs of the existing fuel-free machine, with empty traces
(under marks with no transfer site). -/
theorem ofBase_run_iff {μ : Marks} (hμ : ∀ k, μ.site k = none) {c c' : (ofBase I A rv pl).Cfg} {tr : List Ev} :
    (ofBase I A rv pl).Run μ c tr c' ↔ tr = [] ∧ Live.Inf.ReachableSemInf A c.1 c'.1 := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨rfl, .refl _⟩
    | step hs _ ih =>
      obtain ⟨tid, hs⟩ := hs
      obtain ⟨hes, hs'⟩ := (ofBase_step_iff hμ).mp hs
      obtain ⟨htr, hr⟩ := ih
      subst hes htr
      exact ⟨rfl, .step tid hs' hr⟩
  · rintro ⟨rfl, h⟩
    obtain ⟨c1, ⟨⟩⟩ := c
    obtain ⟨c2, ⟨⟩⟩ := c'
    simp only at h
    induction h with
    | refl => exact .refl _
    | step tid hs _ ih =>
      exact LRun.step (es := []) (tr := []) ⟨tid, (ofBase_step_iff hμ).mpr ⟨rfl, hs⟩⟩ ih

end ofBase

end ExtMachine

end Scc.Sem
