/-
The per-construct simulation judgement.

`Seg p lbl ms P Q`: **a code segment simulates a source term**. `P` and `Q`
are fragments of the relation for one thread (`Frag`): predicates on a
Kraken thread state paired with the source thread's control (`Ctl`: its term
and environment, one frame). From every pair in `P`, each Kraken
instruction is matched by a stuttering source run, and the pairs stay
inside the segment until they reach `Q`. Exits to an abort label are part
of `Q` (a disjunct), so a construct with an abort edge has two exits.

What one instruction does (`Out`):

* `silent`: its event tree is `.done s'` (a register operation, a branch, a
  load or store of thread-private memory: the stack slots), and the source
  takes zero or more **local** steps (`LocalRun`: steps that change only the
  term and the environment, such as `+`, a test, a tail call), possibly
  none (stuttering);
* `choice`: its event tree is a finite choice of `.done` leaves
  (`SilentTree`, `Kraken/Promising/Lower/Silent.lean`: x64 instructions
  with an undefined flag, `and`/`or`/`xor`/`test`/`imul`/shifts), and from
  every leaf the source takes a local run, as for `silent`;
* `load`: one load of an 8-byte location, matched by the source thread's
  acquire load `let x = load acq a in e` of the word at the same address
  (`ValRep`), for every value read and every word `ms.rd` admits as the
  source's reading of it (`ms.rd` is the read side of the memory relation: a
  memory of numbers admits numbers, a memory with uninitialised cells also
  `undef`);
* `holdLoad`, `xchgStore`: the two plain accesses of an exchange of a
  one-word cell the thread holds exclusively (`xchg`, `xchgAt`, a plain
  load then a plain store, `XchgSite`): at the load the source stutters and
  the control records, as proof-only ghost state (`Ctl.hold`), the address
  and the word the source would read there; at the store the source takes
  its whole exchange step, binding that word;
* `ctrRmw`: the allocator's atomic add of the buffer's source units
  (`MemSide.units`) to the heap counter (`MemSide.ctr`) at a buffer
  allocation `let x = newBuf a τ in e`: the source stutters, and the control
  holds the counter's address and the old count (`Ctl.hold`);
* `alloc`: the last instruction of a buffer allocation `let x = newBuf a τ
  in e` (its event tree `.done s'`), the counter's old count held, at which
  the source takes its allocation step: the base `A` is the arena
  (`MemSide.heap`) plus 16 bytes per old count plus the base's offset in
  the object (`MemSide.off`), and for every label the source may allocate
  (one not yet placed), the pair lands in the allocation fragment
  (`MemSide.xa`) of that label placed at `A` with the buffer's size in
  bytes, with `x` bound to the buffer's locative;
* `store`: one store of an 8-byte location, matched by the source thread's
  release store `let x = store rel a b in e` of a word represented by the
  stored value;
* `rtStore`: one store to an address the runtime owns (`MemSide.rt`:
  outside every placed label), with no source counterpart: the source takes
  a local run, typically none (`MemRel.runtime_write`);
* `rtLoad`: one load from an address the runtime owns (the thread
  pointer's block: the stack limit, the thread's control block), with no
  source counterpart: the source takes a local run, and every value read
  lands in the fragment (nothing depends on which value is read);
* `rtRmw`: one read-modify-write at an address the runtime owns (a lock's
  word), with no source counterpart: the source takes a local run, and
  every old value read lands in the fragment;
* `sys`: a supported system call under the kernel model `ms.K`
  (`Kernel.certSuccs`, `Scc/Sem/Kernel.lean`): from every state the thread
  may resume in, the source takes a local run. The call is not `exit`,
  `clone` or a `write` to the output (they need a different source
  obligation: the kernel step's output and the error flags of `write` and
  `clone` are not part of this one), and an `exit_group` off an abort site
  (`MemSide.abortAt`) is `main` returning (`MainExit`): the source runs
  locally to a placed control (`MemSide.pl`) whose return is the exit event
  with the call's code (`SrcSem.mainExit`); `SysOk` bundles these.

The runtime accesses (`rtLoad`, `rtStore`, `rtRmw`, `ctrRmw`) are at
locations mapped for them (`MemSide.mp`), and what they read agrees with the
runtime words the thread owns (`MemSide.own`).

The read side and the runtime's addresses come from the memory relation
through `MemSide`. Neither `Out` nor `Seg` mentions promises: whether a
target store appends a message or fulfils an outstanding promise is the
memory relation's business, decided once per access kind by the consumer
(`Spike/Lib/Mem.lean` has the append form).

The memory side of a load or store (which message is read, which promise is
fulfilled, the views) is not part of the judgement: it belongs to the
global memory relation, and a whole-program proof discharges it once per
access kind (`Spike/Lib/Thread.lean` does it for the flag of the bridge
spike). Load and store kinds are left free: the memory relation decides
which kinds match release/acquire (`.rel`/`.acq` on AArch64, plain on
x64).

The judgement composes:

* `Seg.step`: one instruction;
* `Seg.seq`: sequencing, the exit of the first segment being the entry of
  the second;
* `Seg.loop`: a tail-call loop, a body whose exit includes its own entry;
* `Seg.seq_left`: sequencing on the normal exit of a segment with a second
  (abort) exit, which is kept;
* `Seg.or_pre`, `Seg.mono_pre`, `Seg.mono_post`: case splits and
  weakening;
* `Seg.cfg`: a control-flow graph of segments, each exiting to a node or
  to the graph's exit (loops and joins included);
* `Seg.exists_pre`: ghost parameters of a specification.

The source half lifts to whole configurations: `LocalStep.mem_threadSteps`
(a local step of a thread is one of its thread steps) and `LocalRun.run`
(a local run of a thread without promises is a source run with the empty
trace).
-/
import Spike.Bridge.Common
import Kraken.Promising.Lower.Silent
import Scc.Sem.SysLink

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising
open Kraken.Promising.Lower (SilentTree)
open Scc.Sem (SrcSem ValRep)

/-! ## Fragments -/

/-- **The control of a source thread** with one frame: its term and
environment, and `hold`, proof-only ghost state: between the two target
accesses of an exchange (`Out.holdLoad`, `Out.xchgStore`), the target word
address loaded and the source word the exchange will read there; between a
buffer allocation's counter add and its last instruction (`Out.ctrRmw`,
`Out.alloc`), the counter's address and the old count. The ghost
changes no source or target behaviour (no step reads it) and is not part of
the source state (`Ctl.of`); a whole-program relation keeps it as its own
per-thread ghost, with the invariant that the source's latest message at
that address has that word. -/
structure Ctl where
  term : Expr
  env : TermRun.Env
  hold : Option (Nat × TermRun.Word) := none

/-- The control of a source thread (no hold). -/
def Ctl.of (th : TermRun.TTh) : Ctl := ⟨th.term, th.env, none⟩

/-- **A fragment of the relation for one thread**: a Kraken thread state
paired with the related source thread's control. -/
abbrev Frag (I : ISA) := I.State → Ctl → Prop

/-! ## Local source steps -/

/-- **A local source step** in program `p`: for a thread with control `c`,
one frame (`stack = []`) and no type variables (`σs = []`), `TermRun.tstep`
has exactly one successor, which keeps memory, the pair list and every
other field of the thread and has control `c'`. The step leaves no hold
(`Ctl.hold`): the source has moved past any exchange. -/
def LocalStep (p : Prog) (c c' : Ctl) : Prop :=
  c'.hold = none ∧
  ∀ (g : TermRun.G) (mem : WeakMem.Memory) (pairs : List Nat) (th : TermRun.TTh), g.p = p →
    th.term = c.term → th.env = c.env → th.σs = [] → th.stack = [] →
    TermRun.tstep g mem pairs th = [(mem, pairs, { th with term := c'.term, env := c'.env })]

/-- Zero or more local source steps. -/
inductive LocalRun (p : Prog) : Ctl → Ctl → Prop
  | refl (c : Ctl) : LocalRun p c c
  | step {c c₁ c' : Ctl} : LocalStep p c c₁ → LocalRun p c₁ c' → LocalRun p c c'

theorem LocalRun.single {p : Prog} {c c' : Ctl} (h : LocalStep p c c') : LocalRun p c c' :=
  .step h (.refl _)

theorem LocalRun.trans {p : Prog} {c c₁ c' : Ctl} (h₁ : LocalRun p c c₁) (h₂ : LocalRun p c₁ c') :
    LocalRun p c c' := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- A local run from a control without a hold lands in one without. -/
theorem LocalRun.hold {p : Prog} {c c' : Ctl} (h : LocalRun p c c') (hc : c.hold = none) : c'.hold = none := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih hs.1

/-- **The control of a thread with a control's term and environment** is
that control, when it holds nothing. -/
theorem Ctl.of_with (th : TermRun.TTh) {c : Ctl} (hc : c.hold = none) :
    Ctl.of { th with term := c.term, env := c.env } = c := by
  cases c; cases hc; rfl

/-- A control without a hold is `Ctl.of` of any thread with its term and
environment. -/
theorem Ctl.of_eq {th : TermRun.TTh} {c : Ctl} (ht : th.term = c.term) (he : th.env = c.env) (hc : c.hold = none) :
    Ctl.of th = c := by
  cases c; cases hc; simp only [Ctl.of] at *; rw [ht, he]

/-! ## One instruction -/

/-- The type the source binds the result of a load through a reference of
type `ty` to (`TermRun.tstep`, `.load`): `Int` for a word cell, the cell's
type otherwise. -/
def loadTy (ty : Ty) : Ty :=
  match cellOf ty with
  | some (_, u) => if (wordOf ty).isSome then .int else u
  | none => .unit

/-- **An exchange site**: the term binds `x` to the exchange of the one-word
cell at the source address `sa` (an untagged locative) with `v`, then
continues with `e`; the cell's type is `u`. Either `xchg a v` on a
reference, or `xchgAt b i v` on element `i` of a buffer (`sa` is the
element's address). Both run as a plain load then a plain store
(`TermRun.tstep`), on a cell the thread holds exclusively. -/
def XchgSite (c : Ctl) (x : String) (sa : WeakMem.Address) (u : Ty) (v : At) (e : Expr) : Prop :=
  TermRun.accs u = some [.one] ∧
  ((∃ a t pw μ, c.term = .let_ x (.xchg a v) e ∧ TermRun.evalAt c.env a = some (t, [pw]) ∧
      pw.val = .loc sa 0 ∧ cellOf t = some (μ, u)) ∨
   (∃ b i t pw ti iws μ sb k, c.term = .let_ x (.xchgAt b i v) e ∧ TermRun.evalAt c.env b = some (t, [pw]) ∧
      pw.val = .loc sb 0 ∧ TermRun.bufElem t = some (μ, u) ∧ TermRun.evalAt c.env i = some (ti, iws) ∧
      TermRun.numOf iws = some k ∧ sa = TermRun.offs sb k))

/-- **The memory side the judgement is stated against**: what a whole-program
proof's memory relation provides to the per-instruction rows.

- `rd`: the words the source may read (a memory of numbers admits numbers,
  a memory with uninitialised cells also `undef`);
- `rt`: the addresses the runtime owns: a store there has no source
  counterpart (allocator cursors, object headers, the stack pool's
  metadata, control blocks). With `MemRel`, the addresses outside every
  placed label (`MemSide.ofLabels`, `Spike/Lib/Mem.lean`);
- `K`: the kernel model of the system calls, if the proof matches any
  (`none`: no system call is matched, `Out.sys` is unusable);
- `G`: the values runtime memory may hold at each location (Kraken's
  `MemInv`): every runtime load reads a `G` value (`Out.rtLoad`), every
  runtime store writes one (`Out.rtStore`). `MemSide.ofLabels` defaults it
  to everything;
- `heap`, `ctr`: the allocator's arena base and the address of its heap
  counter, which counts source units and is the arena's cursor in 16-byte
  cells (`Out.ctrRmw`, `Out.alloc`);
- `units`, `off`: for a buffer of `k` elements of type `τ`, the source units
  the allocation adds to the counter and the byte offset of the buffer's
  base in its object (past the header and the trace words);
- `cells`: the arena's size in 16-byte cells. With no allocation pending
  the counter is within it (the heap use the source has; Scc's
  `HeapCtr1`), which a whole-program proof provides at the counter's add
  (`Out.ctrRmw`);
- `own`: the runtime words the thread owns at a state, with their values (a
  counter it holds, its control block): a runtime read of an owned location
  reads its value (`Out.rtLoad`, `Out.ctrRmw`, `Out.rtRmw`);
- `mp L w`: the location `L` is mapped for a runtime access (`w`: for
  writing);
- `abortAt`: the states at an abort site (`Out.sys`: an `exit_group` there is
  the abort, not `main` returning);
- `pl`: the pairs placed in the program (`Out.sys`: `main` returns from one);
- `xa l b n`: the fragment a buffer allocation lands in (`Out.alloc`), the
  label `l` placed at `b` with `n` bytes.

The defaults of the last five fields are the strong direction for a row: no
owned words (no read facts), nothing mapped, no abort site, nothing placed,
no allocation fragment; a row stated against them obliges its producer to
establish each, and a whole-program proof fixes them all. -/
structure MemSide (I : ISA) where
  rd : TermRun.Word → Prop
  rt : Nat → Prop
  K : Option (Scc.Sem.Kernel.Abi I)
  G : Loc → Val → Prop
  heap : Nat
  ctr : Nat
  units : Nat → Ty → Nat
  off : Nat → Ty → Nat
  cells : Nat
  own : I.State → List (Loc × Val) := fun _ => []
  mp : Loc → Bool → Prop := fun _ _ => False
  abortAt : I.State → Prop := fun _ => False
  pl : I.State → Ctl → Prop := fun _ _ => False
  xa : WeakMem.AllocLabel → Nat → Nat → Frag I := fun _ _ _ _ _ => False

/-- **`main` returns with code `v`** from the pair `(s, c)`: the source runs
locally to a placed control (`ms.pl`) whose return, in thread 0 with an
empty stack, is the exit event with code `v` (`SrcSem.mainExit`). -/
def MainExit {I : ISA} (p : Prog) (ms : MemSide I) (s : I.State) (c : Ctl) (v : Nat) : Prop :=
  ∃ c', LocalRun p c c' ∧ ms.pl s c' ∧
    ∀ (s0 : TermRun.Cfg) (th : TermRun.TTh), s0.ths[0]? = some th → th.term = c'.term → th.env = c'.env →
      th.stack = [] → SrcSem.mainExit s0 = [.exit (Scc.Sem.Kernel.exitCode v)]

/-- **A system call the judgement matches** from the pair `(s, c)`: not
`exit`, `clone` or a `write` to the output, and an `exit_group` off an abort
site (`ms.abortAt`) is `main` returning with the call's code. -/
def SysOk {I : ISA} (p : Prog) (ms : MemSide I) (s : I.State) (c : Ctl) (call : Scc.Sem.Kernel.Call) : Prop :=
  call ≠ .exit ∧ (∀ st tl, call ≠ .clone st tl) ∧ (∀ fd buf n, call = .write fd buf n → fd ≠ 1) ∧
    ∀ v, call = .exitGroup v → ¬ ms.abortAt s → MainExit p ms s c v

/-- `exit_group` at an abort site is matched. -/
theorem SysOk.exitGroup_abort {I : ISA} {p : Prog} {ms : MemSide I} {s : I.State} {c : Ctl} {v : Nat}
    (h : ms.abortAt s) : SysOk p ms s c (.exitGroup v) :=
  ⟨nofun, nofun, nofun, fun _ _ hn => absurd h hn⟩

/-- `exit_group` off an abort site returning from `main` is matched. -/
theorem SysOk.exitGroup_main {I : ISA} {p : Prog} {ms : MemSide I} {s : I.State} {c : Ctl} {v : Nat}
    (h : ¬ ms.abortAt s → MainExit p ms s c v) : SysOk p ms s c (.exitGroup v) :=
  ⟨nofun, nofun, nofun, fun _ he hn => by cases he; exact h hn⟩

/-- **What one instruction does** from the pair `(s, c)`, landing in the
fragment `X`: see the module docstring. -/
inductive Out {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I) (X : Frag I)
    (s : I.State) (c : Ctl) : Prop where
  /-- No event; the source takes a local run. -/
  | silent (s' : I.State) (c' : Ctl) :
      I.exec s = some (.done s') → LocalRun p c c' → X s' c' → Out p lbl ms X s c
  /-- No event, a finite choice of leaves (an undefined flag); from every
  leaf the source takes a local run. -/
  | choice (P : I.State → Prop) (t : EvTree I.State) :
      I.exec s = some t → SilentTree P t → (∀ s', P s' → ∃ c', LocalRun p c c' ∧ X s' c') → Out p lbl ms X s c
  /-- One load of `⟨A, 8⟩`, matched by the source's acquire load of the word
  at `A`; every value read lands in `X` with the source variable bound (at
  the type `loadTy` gives) to any word the memory relation lets the source
  read (`ms.rd`) that represents the value's low 64 bits. (An
  8-byte location holds a 64-bit value in every related memory, but the
  phase must be total: certification runs from memories the relation does
  not constrain.) The address word is an untagged locative, so `A` is its
  word address (`wordAddr`), the location the source reads. -/
  | load (kl : Kraken.LoadKind) (A : BitVec 64) (g : Val → I.State) (x : String) (a : At) (e : Expr)
      (ty : Ty) (w : TermRun.Word) :
      I.exec s = some (.load kl false ⟨A, 8⟩ fun v => .done (g v)) →
      c.term = .let_ x (.load true a) e → TermRun.evalAt c.env a = some (ty, [w]) → ValRep lbl w.val A.toNat →
      (∀ (v : Val) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val (v.setWidth 64).toNat →
        X (g v) ⟨e, (x, loadTy ty, [w']) :: c.env, none⟩) →
      (∃ sa, w.val = .loc sa 0) → Out p lbl ms X s c
  /-- One store of `V` to `⟨A, 8⟩`, matched by the source's release store
  of a word that `V` represents to the word at `A` (an untagged locative,
  as for `load`). -/
  | store (kr : Kraken.StoreKind) (A : BitVec 64) (V : Val) (s' : I.State) (x : String) (a b : At) (e : Expr)
      (ty tb : Ty) (w wb : TermRun.Word) :
      I.exec s = some (.store kr false ⟨A, 8⟩ V fun _ => .done s') →
      c.term = .let_ x (.store true a b none) e → TermRun.evalAt c.env a = some (ty, [w]) →
      ValRep lbl w.val A.toNat → TermRun.evalAt c.env b = some (tb, [wb]) → ValRep lbl wb.val V.toNat →
      X s' ⟨e, (x, .unit, []) :: c.env, none⟩ → (∃ sa, w.val = .loc sa 0) → Out p lbl ms X s c
  /-- One store of `V` to `L`, at an address the runtime owns (`ms.rt`)
  mapped for writing (`ms.mp`), of any size, `V` a value runtime memory may
  hold there (`ms.G`); the source takes a local run, possibly none
  (stuttering). -/
  | rtStore (kr : Kraken.StoreKind) (L : Loc) (V : Val) (s' : I.State) (c' : Ctl) :
      I.exec s = some (.store kr false L V fun _ => .done s') → ms.rt L.addr.toNat → ms.mp L true → ms.G L V →
      LocalRun p c c' → X s' c' → Out p lbl ms X s c
  /-- One load from `L`, at an address the runtime owns (`ms.rt`) mapped for
  reading (`ms.mp`), of any size; the source takes a local run, possibly
  none (stuttering), and every value read that runtime memory may hold there
  (`ms.G`), the owned value if the thread owns `L` (`ms.own`), lands in
  `X`. -/
  | rtLoad (kl : Kraken.LoadKind) (L : Loc) (g : Val → I.State) (c' : Ctl) :
      I.exec s = some (.load kl false L fun v => .done (g v)) → ms.rt L.addr.toNat → ms.mp L false →
      LocalRun p c c' → (∀ v, ms.G L v → (∀ w, (L, w) ∈ ms.own s → v = w) → X (g v) c') →
      Out p lbl ms X s c
  /-- One read-modify-write at `L`, at an address the runtime owns
  (`ms.rt`) mapped for writing (`ms.mp`), of any size; the source takes a
  local run, possibly none (stuttering), and for every old value runtime
  memory may hold there (`ms.G`), the owned value if the thread owns `L`
  (`ms.own`), every new value is one runtime memory may hold there and the
  pair lands in `X`. -/
  | rtRmw (k : Kraken.RmwKind) (L : Loc) (op : Val → Option Val) (g : Val → I.State) (c' : Ctl) :
      I.exec s = some (.rmw k false L op fun v => .done (g v)) → ms.rt L.addr.toNat → ms.mp L true →
      LocalRun p c c' →
      (∀ old, ms.G L old → (∀ w, (L, w) ∈ ms.own s → old = w) →
        (∀ new, op old = some new → ms.G L new) ∧ X (g old) c') → Out p lbl ms X s c
  /-- A supported system call `call` under the kernel model `ms.K`, one
  the judgement matches (`SysOk`: not `exit`, `clone` or a `write` to the
  output; an `exit_group` off an abort site is `main` returning): from every
  state the thread may resume in (`Kernel.certSuccs`), the source takes a
  local run (see the module docstring). -/
  | sys (K : Scc.Sem.Kernel.Abi I) (call : Scc.Sem.Kernel.Call) :
      ms.K = some K → K.atSys s = true → Scc.Sem.Kernel.decode K.nrs (K.nr s) (K.arg s) = some call →
      SysOk p ms s c call →
      (∀ s' ∈ Scc.Sem.Kernel.certSuccs K s call, ∃ c', LocalRun p c c' ∧ X s' c') → Out p lbl ms X s c
  /-- The plain load of an exchange (`XchgSite`) of the word at `A`, no hold
  pending: the source stutters, and every value read lands in `X` with the
  control holding `A` and any word the memory relation lets the source read
  that represents the value (the whole-program proof supplies the word of
  the source's latest message at `sa`). -/
  | holdLoad (kl : Kraken.LoadKind) (A : BitVec 64) (g : Val → I.State) (x : String) (sa : WeakMem.Address)
      (u : Ty) (v : At) (e : Expr) :
      I.exec s = some (.load kl false ⟨A, 8⟩ fun r => .done (g r)) →
      XchgSite c x sa u v e → ValRep lbl (.loc sa 0) A.toNat → c.hold = none →
      (∀ (r : Val) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
        X (g r) { c with hold := some (A.toNat, w') }) → Out p lbl ms X s c
  /-- The plain store of an exchange of the word at `A`, of a value `V`
  represents `v`'s word, with the hold `(A, wold)` pending: the source takes
  its exchange step, binding `x` to the held word `wold`, and the hold ends. -/
  | xchgStore (kr : Kraken.StoreKind) (A : BitVec 64) (V : Val) (s' : I.State) (x : String)
      (sa : WeakMem.Address) (u : Ty) (v : At) (e : Expr) (tv : Ty) (wv wold : TermRun.Word) :
      I.exec s = some (.store kr false ⟨A, 8⟩ V fun _ => .done s') →
      XchgSite c x sa u v e → ValRep lbl (.loc sa 0) A.toNat → c.hold = some (A.toNat, wold) →
      TermRun.evalAt c.env v = some (tv, [wv]) → ValRep lbl wv.val V.toNat →
      X s' ⟨e, (x, u, [wold]) :: c.env, none⟩ → Out p lbl ms X s c
  /-- The heap counter's atomic add at a buffer allocation `let x = newBuf
  a τ in e`, `a` a number `n`, no hold pending: an RMW of the counter word
  (`ms.ctr`, owned by the runtime, mapped for writing) adding the buffer's
  units `ms.units n τ`, its old value returned (not `noRet`).
  The source stutters; for every old value that runtime memory may hold
  there (`ms.G`), the owned value if the thread owns the counter
  (`ms.own`), within the arena's cells (`ms.cells`: no allocation is
  pending), the new value may be held there too, and the control, holding
  the counter's address and the old count, lands in `X`. -/
  | ctrRmw (k : Kraken.RmwKind) (op : Val → Option Val) (g : Val → I.State) (x : String) (a : At)
      (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word) (n : Nat) :
      I.exec s = some (.rmw k false ⟨BitVec.ofNat 64 ms.ctr, 8⟩ op fun v => .done (g v)) →
      ms.rt (BitVec.ofNat 64 ms.ctr).toNat → ms.mp ⟨BitVec.ofNat 64 ms.ctr, 8⟩ true →
      c.term = .let_ x (.newBuf a τ) e → TermRun.evalAt c.env a = some (ta, ws) → TermRun.numOf ws = some n →
      c.hold = none →
      (∀ old, op old = some ((old.setWidth 64 + BitVec.ofNat 64 (ms.units n τ)).setWidth 128)) →
      (∀ old, ms.G ⟨BitVec.ofNat 64 ms.ctr, 8⟩ old → (∀ w, (⟨BitVec.ofNat 64 ms.ctr, 8⟩, w) ∈ ms.own s → old = w) →
        (old.setWidth 64).toNat ≤ ms.cells →
        ms.G ⟨BitVec.ofNat 64 ms.ctr, 8⟩ ((old.setWidth 64 + BitVec.ofNat 64 (ms.units n τ)).setWidth 128) ∧
        X (g old) { c with hold := some (ms.ctr, TermRun.cst (.num (old.setWidth 64).toNat)) }) →
      Out p lbl ms X s c
  /-- The last instruction of a buffer allocation `let x = newBuf a τ in e`,
  `a` a number `k`, the heap counter's old count `old` held (`Out.ctrRmw`),
  at the base `A = ms.heap + 16·old + ms.off k τ`, the element type's
  accesses `us`: the source takes its allocation step; for every label `l`
  not yet placed, the pair lands in the allocation fragment `ms.xa` of `l`
  placed at `A` with `k` elements of `nWords us` bytes, with `x` bound to
  `l`'s locative at the buffer's type (`ini` elements initialised). It does
  not land in `X`. -/
  | alloc (s' : I.State) (A : BitVec 64) (x : String) (a : At) (τ : Ty) (e : Expr) (ta : Ty)
      (ws : List TermRun.Word) (k : Nat) (wold : TermRun.Word) (old : Nat) (us : List TermRun.Acc) :
      I.exec s = some (.done s') → c.term = .let_ x (.newBuf a τ) e → TermRun.evalAt c.env a = some (ta, ws) →
      TermRun.numOf ws = some k → c.hold = some (ms.ctr, wold) → TermRun.numOf [wold] = some old →
      A.toNat = ms.heap + 16 * old + ms.off k τ → TermRun.accs (TermRun.close [] τ) = some us →
      (∀ (l : WeakMem.AllocLabel) (ini : Nat), lbl l = none →
        ms.xa l A.toNat (k * TermRun.nWords us) s'
          ⟨e, (x, .refine (.loc .own (.array (.lit k) (TermRun.close [] τ))) (.ini (.lit ini)),
            [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩) → Out p lbl ms X s c

theorem Out.mono {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {X Y : Frag I} {s : I.State} {c : Ctl}
    (h : Out p lbl ms X s c) (hXY : ∀ s c, X s c → Y s c) : Out p lbl ms Y s c := by
  cases h with
  | silent s' c' he hr hx => exact .silent s' c' he hr (hXY _ _ hx)
  | choice P t he hs hx =>
    exact .choice P t he hs fun s' hp => let ⟨c', hr, h⟩ := hx s' hp; ⟨c', hr, hXY _ _ h⟩
  | load kl A g x a e ty w he ht hev hv hx htag =>
    exact .load kl A g x a e ty w he ht hev hv (fun v w' hr h => hXY _ _ (hx v w' hr h)) htag
  | store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag =>
    exact .store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb (hXY _ _ hx) htag
  | rtStore kr L V s' c' he hrt hm hG hr hx => exact .rtStore kr L V s' c' he hrt hm hG hr (hXY _ _ hx)
  | rtLoad kl L g c' he hrt hm hr hx =>
    exact .rtLoad kl L g c' he hrt hm hr fun v hG ho => hXY _ _ (hx v hG ho)
  | rtRmw k L op g c' he hrt hm hr hx =>
    exact .rtRmw k L op g c' he hrt hm hr fun old hG ho => ⟨(hx old hG ho).1, hXY _ _ (hx old hG ho).2⟩
  | sys K call hK ha hd hok hx =>
    exact .sys K call hK ha hd hok fun s' hs => let ⟨c', hr, h⟩ := hx s' hs; ⟨c', hr, hXY _ _ h⟩
  | holdLoad kl A g x sa u v e he hx hA hh hX =>
    exact .holdLoad kl A g x sa u v e he hx hA hh fun r w' hr h => hXY _ _ (hX r w' hr h)
  | xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX =>
    exact .xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv (hXY _ _ hX)
  | ctrRmw k op g x a τ e ta ws n he hrt hm ht hev hn hh hop hX =>
    exact .ctrRmw k op g x a τ e ta ws n he hrt hm ht hev hn hh hop fun old hG ho hc =>
      ⟨(hX old hG ho hc).1, hXY _ _ (hX old hG ho hc).2⟩
  | alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hu hX =>
    exact .alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hu hX

/-! ## Segments -/

/-- **Segment simulation**: every pair of `P` lies in an invariant whose
pairs each step (`Out`) into the invariant or into the exit `Q`. -/
def Seg {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I) (P Q : Frag I) : Prop :=
  ∃ inv : Frag I, (∀ s c, P s c → inv s c) ∧
    ∀ s c, inv s c → Out p lbl ms (fun s c => inv s c ∨ Q s c) s c

namespace Seg

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
  {P P' Q Q' R : Frag I}

/-- **One instruction** from every pair of `P` into `Q`. -/
theorem step (h : ∀ s c, P s c → Out p lbl ms Q s c) : Seg p lbl ms P Q :=
  ⟨P, fun _ _ h => h, fun s c hp => (h s c hp).mono fun _ _ h => .inr h⟩

/-- **Sequencing**: the exit of the first segment is the entry of the
second. -/
theorem seq (h₁ : Seg p lbl ms P Q) (h₂ : Seg p lbl ms Q R) : Seg p lbl ms P R := by
  obtain ⟨i₁, hs₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), ?_⟩
  rintro s c (h | h)
  · exact (ho₁ s c h).mono fun s c h => h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c h))
  · exact (ho₂ s c h).mono fun s c h => h.elim (fun h => .inl (.inr h)) .inr

/-- **A tail-call loop**: a body from `H` whose exit is `H` again (the back
edge, the source's tail call) or `X`. -/
theorem loop {H X : Frag I} (h : Seg p lbl ms H (fun s c => H s c ∨ X s c)) : Seg p lbl ms H X := by
  obtain ⟨i, hs, ho⟩ := h
  refine ⟨i, hs, fun s c hi => (ho s c hi).mono fun s c h => ?_⟩
  rcases h with h | h | h
  · exact .inl h
  · exact .inl (hs s c h)
  · exact .inr h

theorem mono_pre (h : Seg p lbl ms P Q) (hP : ∀ s c, P' s c → P s c) : Seg p lbl ms P' Q :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, fun s c h => hs s c (hP s c h), ho⟩

theorem mono_post (h : Seg p lbl ms P Q) (hQ : ∀ s c, Q s c → Q' s c) : Seg p lbl ms P Q' :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, hs, fun s c h => (ho s c h).mono fun s c h => h.imp_right (hQ s c)⟩

/-- A case split on the entry. -/
theorem or_pre (h : Seg p lbl ms P Q) (h' : Seg p lbl ms P' Q) :
    Seg p lbl ms (fun s c => P s c ∨ P' s c) Q := by
  obtain ⟨i, hs, ho⟩ := h
  obtain ⟨i', hs', ho'⟩ := h'
  refine ⟨fun s c => i s c ∨ i' s c, fun s c h => h.imp (hs s c) (hs' s c), ?_⟩
  rintro s c (h | h)
  · exact (ho s c h).mono fun s c h => h.imp_left .inl
  · exact (ho' s c h).mono fun s c h => h.imp_left .inr

/-- Continue the normal exit `Q` with a segment to `R`, keeping a second exit
`E` (an abort edge) as it is. -/
theorem seq_left {E : Frag I} (h₁ : Seg p lbl ms P (fun s c => Q s c ∨ E s c)) (h₂ : Seg p lbl ms Q R) :
    Seg p lbl ms P (fun s c => R s c ∨ E s c) := by
  obtain ⟨i₁, hs₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), ?_⟩
  rintro s c (h | h)
  · exact (ho₁ s c h).mono fun s c h => by
      rcases h with h | h | h
      · exact .inl (.inl h)
      · exact .inl (.inr (hs₂ s c h))
      · exact .inr (.inr h)
  · exact (ho₂ s c h).mono fun s c h => h.elim (fun h => .inl (.inr h)) fun h => .inr (.inl h)

/-- **A control-flow graph**: nodes `N i`, each a segment whose exit is some
node or the graph's exit `X`, make one segment from any node to `X`. The
nodes may form any graph (loops, joins, several exits); a node is a block,
or an instruction or routine whose segment is given. -/
theorem cfg {ι : Sort _} (N : ι → Frag I) {X : Frag I}
    (h : ∀ i, Seg p lbl ms (N i) (fun s c => (∃ j, N j s c) ∨ X s c)) :
    Seg p lbl ms (fun s c => ∃ i, N i s c) X := by
  refine ⟨fun s c => ∃ i, ∃ J : Frag I, (∀ s c, N i s c → J s c) ∧
      (∀ s c, J s c → Out p lbl ms (fun s c => J s c ∨ ((∃ j, N j s c) ∨ X s c)) s c) ∧ J s c, ?_, ?_⟩
  · rintro s c ⟨i, hi⟩
    obtain ⟨J, hs, ho⟩ := h i
    exact ⟨i, J, hs, ho, hs s c hi⟩
  · rintro s c ⟨i, J, hs, ho, hJ⟩
    refine (ho s c hJ).mono fun s c h => ?_
    rcases h with h | ⟨j, hj⟩ | h
    · exact .inl ⟨i, J, hs, ho, h⟩
    · obtain ⟨J', hs', ho'⟩ := h j
      exact .inl ⟨j, J', hs', ho', hs' s c hj⟩
    · exact .inr h

/-- **Ghost parameters**: a segment for every value of `g` is a segment
from the union (a routine's specification quantified over its caller's
state). -/
theorem exists_pre {γ : Sort _} {P : γ → Frag I} {X : Frag I} (h : ∀ g, Seg p lbl ms (P g) X) :
    Seg p lbl ms (fun s c => ∃ g, P g s c) X :=
  cfg P fun g => (h g).mono_post fun _ _ h => .inr h

end Seg

/-! ## Guarded segments -/

/-- **Guarded segment simulation**: as `Seg`, but each pair of the invariant
need only step when the source control satisfies the guard `J`. The guard is
a fact about the source alone that the global proof supplies at every step,
such as the source thread being well typed (it is reachable). `Seg` is the
case of the trivial guard (`Seg.toJ`). -/
def SegJ {I : ISA} (J : Ctl → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I)
    (P Q : Frag I) : Prop :=
  ∃ inv : Frag I, (∀ s c, P s c → inv s c) ∧
    ∀ s c, inv s c → J c → Out p lbl ms (fun s c => inv s c ∨ Q s c) s c

/-- An unguarded segment is a guarded one, for any guard. -/
theorem Seg.toJ {I : ISA} {J : Ctl → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {P Q : Frag I} (h : Seg p lbl ms P Q) : SegJ J p lbl ms P Q :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, hs, fun s c hi _ => ho s c hi⟩

/-- The trivial guard gives back `Seg`. -/
theorem SegJ.toSeg {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {P Q : Frag I} (h : SegJ (fun _ => True) p lbl ms P Q) : Seg p lbl ms P Q :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, hs, fun s c hi => ho s c hi trivial⟩

namespace SegJ

variable {I : ISA} {J : Ctl → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
  {P P' Q Q' R : Frag I}

/-- **One instruction** from every pair of `P` whose source satisfies the
guard into `Q`. -/
theorem step (h : ∀ s c, P s c → J c → Out p lbl ms Q s c) : SegJ J p lbl ms P Q :=
  ⟨P, fun _ _ h => h, fun s c hp hj => (h s c hp hj).mono fun _ _ h => .inr h⟩

/-- **Sequencing**. -/
theorem seq (h₁ : SegJ J p lbl ms P Q) (h₂ : SegJ J p lbl ms Q R) : SegJ J p lbl ms P R := by
  obtain ⟨i₁, hs₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), ?_⟩
  rintro s c (h | h) hj
  · exact (ho₁ s c h hj).mono fun s c h => h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c h))
  · exact (ho₂ s c h hj).mono fun s c h => h.elim (fun h => .inl (.inr h)) .inr

/-- **A tail-call loop**. -/
theorem loop {H X : Frag I} (h : SegJ J p lbl ms H (fun s c => H s c ∨ X s c)) : SegJ J p lbl ms H X := by
  obtain ⟨i, hs, ho⟩ := h
  refine ⟨i, hs, fun s c hi hj => (ho s c hi hj).mono fun s c h => ?_⟩
  rcases h with h | h | h
  · exact .inl h
  · exact .inl (hs s c h)
  · exact .inr h

theorem mono_pre (h : SegJ J p lbl ms P Q) (hP : ∀ s c, P' s c → P s c) : SegJ J p lbl ms P' Q :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, fun s c h => hs s c (hP s c h), ho⟩

theorem mono_post (h : SegJ J p lbl ms P Q) (hQ : ∀ s c, Q s c → Q' s c) : SegJ J p lbl ms P Q' :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, hs, fun s c h hj => (ho s c h hj).mono fun s c h => h.imp_right (hQ s c)⟩

/-- A stronger guard: a segment under `J` is one under any `J'` implying it. -/
theorem mono_guard {J' : Ctl → Prop} (h : SegJ J p lbl ms P Q) (hJ : ∀ c, J' c → J c) :
    SegJ J' p lbl ms P Q :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, hs, fun s c h hj => ho s c h (hJ c hj)⟩

/-- A case split on the entry. -/
theorem or_pre (h : SegJ J p lbl ms P Q) (h' : SegJ J p lbl ms P' Q) :
    SegJ J p lbl ms (fun s c => P s c ∨ P' s c) Q := by
  obtain ⟨i, hs, ho⟩ := h
  obtain ⟨i', hs', ho'⟩ := h'
  refine ⟨fun s c => i s c ∨ i' s c, fun s c h => h.imp (hs s c) (hs' s c), ?_⟩
  rintro s c (h | h) hj
  · exact (ho s c h hj).mono fun s c h => h.imp_left .inl
  · exact (ho' s c h hj).mono fun s c h => h.imp_left .inr

/-- Continue the normal exit `Q`, keeping a second exit `E` as it is. -/
theorem seq_left {E : Frag I} (h₁ : SegJ J p lbl ms P (fun s c => Q s c ∨ E s c)) (h₂ : SegJ J p lbl ms Q R) :
    SegJ J p lbl ms P (fun s c => R s c ∨ E s c) := by
  obtain ⟨i₁, hs₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), ?_⟩
  rintro s c (h | h) hj
  · exact (ho₁ s c h hj).mono fun s c h => by
      rcases h with h | h | h
      · exact .inl (.inl h)
      · exact .inl (.inr (hs₂ s c h))
      · exact .inr (.inr h)
  · exact (ho₂ s c h hj).mono fun s c h => h.elim (fun h => .inl (.inr h)) fun h => .inr (.inl h)

/-- **A control-flow graph** of guarded nodes. -/
theorem cfg {ι : Sort _} (N : ι → Frag I) {X : Frag I}
    (h : ∀ i, SegJ J p lbl ms (N i) (fun s c => (∃ j, N j s c) ∨ X s c)) :
    SegJ J p lbl ms (fun s c => ∃ i, N i s c) X := by
  refine ⟨fun s c => ∃ i, ∃ K : Frag I, (∀ s c, N i s c → K s c) ∧
      (∀ s c, K s c → J c → Out p lbl ms (fun s c => K s c ∨ ((∃ j, N j s c) ∨ X s c)) s c) ∧ K s c, ?_, ?_⟩
  · rintro s c ⟨i, hi⟩
    obtain ⟨K, hs, ho⟩ := h i
    exact ⟨i, K, hs, ho, hs s c hi⟩
  · rintro s c ⟨i, K, hs, ho, hK⟩ hj
    refine (ho s c hK hj).mono fun s c h => ?_
    rcases h with h | ⟨j, hj⟩ | h
    · exact .inl ⟨i, K, hs, ho, h⟩
    · obtain ⟨K', hs', ho'⟩ := h j
      exact .inl ⟨j, K', hs', ho', hs' s c hj⟩
    · exact .inr h

/-- **Ghost parameters**. -/
theorem exists_pre {γ : Sort _} {P : γ → Frag I} {X : Frag I} (h : ∀ g, SegJ J p lbl ms (P g) X) :
    SegJ J p lbl ms (fun s c => ∃ g, P g s c) X :=
  cfg P fun g => (h g).mono_post fun _ _ h => .inr h

end SegJ

end Spike.Lib
