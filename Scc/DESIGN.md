# `scc`: the correctness statement and the machine extensions

This note accompanies `Scc/Sem/`. It states what "`scc` is correct" means
(§1), what the Kraken machine needs before that statement can be proved for a
real program (§2), the kernel model (§3), the trusted base (§4), and the plan
for the first proof that relates the two promise machines (§5). §6 lists the
choices made here.

| File | Contents |
|---|---|
| `Scc/Sem/Basic.lean` | events `Ev`, outcomes, address ranges, labelled runs `LRun` |
| `Scc/Sem/Ext.lean` | `ExtMachine`, the extended target machine as an interface; `ExtMachine.ofBase`, the existing machine as an instance; `ofBase_run_iff` |
| `Scc/Sem/SrcExt.lean` | `SrcSem`, the source machine as an interface; `ofStepsG` (`TermRun.Step` beside an extra configuration step, labelled by the growth of an observable trace), `ofStep`, `ofSpawn`; `srcObs` (events cut at the exit point); `source P p`, the source instance (extern step a hook, `SrcHooks`); `source_run_trace` |
| `Scc/Sem/Correct.lean` | layout `Layout`, budget `Budget`, value representation `ValRep`, `Witness`, `Components`, `RouteS`, `Sim`, `Correct`; `Sim.transfer`, `Sim.transfer_stepsX`; sanity lemmas |
| `Scc/Sem/Live.lean` | live labels across a promise step (`live_promise`, `dead_promise`): the obligation on the promised value |
| `Scc/Sem/MemRel.lean` | the memory relation for one thread (§8): `MemRel`, `ComponentsAll.iff_memRel`, `Components.ofMemRel`; its preservation by a store, an allocation and a runtime write; the read side (`MemRel.latest`) |
| `Scc/Sem/Coh.lean` | the target side of §8: the thread invariant `CohCovers` (no promise, coherence views cover memory), its preservation (`stepOne_coh`, `instrSemC_coh`, `readByte_coh`), and the latest-write reads it gives (`stepOne_load_tlatest`, `readByte_tlatest`); `stepOne_store_append` |
| `Scc/Sem/Typing.lean` | typing invariants (§10): small words and `NoBigNumT` preservation (`MemRel.small`, `NoBigNumT.push`); `ThreadTyped`/`SrcTyped` (WeakCore's `Typed` + `FInv`) and the defined-operand facts it gives (`ThreadTyped.add_num`, `ifeq_num`, `parity_num`, `ifnull_def`) |
| `Scc/Sem/TypingRows.lean` | the typing facts in the rows' form (§10): `TypedAt` (typing of a control), `valRep_addW`/`valRep_subW` (checked `+` fall-through, saturating `-`), `TypedAt.carry_nums` (checked `+` abort edge), `valRep_num`, `TypedAt.ifnull_iff` (tests), `transfer_typedAt` (the rows' guard at each reachable target configuration) |
| `Scc/Sem/Scope.lean` | `exprFv` and `opVars` against WeakCore's `TermScope.freeB`/`opAts` (`mem_exprFv`, `mem_opVars`) |
| `Scc/Sem/Target.lean` | `Hooks`, `ExtMachine.ofHooks` (Kraken's machine with extension hooks), loader pieces, `Entry`, `CertCfg`, `CertCfg.WF` |
| `Scc/Sem/CorrectE.lean`, `Scc/Sem/CorrectEA64.lean`, `Scc/Sem/CorrectEX64.lean` | the release statement's entry quantifier: `Entry.Ok` (an admissible initial stack for a layout), `Entry.ok_witness`, and per ISA `CorrectE` (`Correct` at `target (kernel n) E` for every admissible `E`) |
| `Scc/Sem/Kernel.lean` | the kernel model (§3): every trusted kernel assumption as a named definition; `Kernel.hooks`, the canonical targets' hooks |
| `Scc/Sem/TargetA64.lean`, `Scc/Sem/TargetX64.lean` | the canonical targets (`A64.canonical`, `X64.canonical`), the registers the kernel reads and writes (`A64.abi`, `X64.abi`), `Scc.Correct` |
| `Scc/Sem/StartLoad.lean`, `Scc/Sem/StartA64.lean`, `Scc/Sem/StartX64.lean` | `Components` at load (one thread): the ISA-free half (`not_live_start`, `Witness.start`, `Kernel.KState.init_runs`, the initial words over `wordsList`) and, per ISA, `components_load`, `init_stackRange`, `wordAt_load`, `loadProg_init` |
| `Scc/Sem/LoadA64.lean`, `Scc/Sem/LoadX64.lean` | each canonical loader split at the parser (`loadParsed`, `load_of_parsed`, `resolve_of_parsed`): the parse equations are a certificate's trust boundary |

`Scc.Sem.Correct` is the first module that imports both Kraken
(`Kraken.Promising.LiveSemInf`) and WeakCore (`WeakCore.TermSpawnStep`, which
imports `WeakCore.TermRun`). Its build takes about 2 s and 1.7 GB resident.
The two Kraken ISAs cannot be imported together (their syntax modules both
define root-level names), so anything ISA-specific lives in one file per ISA
(`Scc/Sem/TargetA64.lean`, `Scc/Sem/TargetX64.lean`, each about 1.7 GB).

## 1. The statement

```lean
def Correct (T : Target) (S : SrcSem) (Λ : Layout) (B : Budget) (asm : T.Asm) : Prop :=
  Nonempty (Sim T S Λ B asm)
```

`T` is the target: an extended machine `T.M`, an assembly type and a loader
`T.load : Asm → Layout → Option T.M.Cfg`. `S` is the source machine with its
start configurations (a WeakCore program and its setup block). For WeakCore
with its extern step (designed upstream, not yet in the tree) `S` is
`SrcSem.ofStepsG p k arch (Spawn ∨ Ext) (srcObs trace)`: runs are WeakCore's
`StepsG p k arch (Spawn ∨ Ext)` runs, and each step is labelled with the
growth of the observable trace, i.e. the configuration's append-only event
list (`out b`, `exit n ↦ exit (n % 256)`) followed by `main`'s exit once
thread 0 has returned with an empty stack, cut at the first exit
(`srcObs`, `mainExit`, `cutAtExit`; `ofStepsG_run_trace`: a run's trace is
the growth). `Λ` is the
layout and `B` the budget. A `Sim` is a relation `R` between target and source
configurations, exposed as a field, together with the proofs of the clauses
below. `Scc.Correct cfg asm p` is this statement at the canonical target of
the ISA and `S := SrcSem.source (cfg.src arch) p`, with `Λ`, `B`, the
source's thread capacity and start in `cfg : CertCfg`; the canonical target
is the one with `cfg.slots` thread slots (`canonical cfg.slots`). It is
defined once per ISA file (`Scc/Sem/TargetA64.lean`,
`Scc/Sem/TargetX64.lean`, which are never imported together), memory model
`arm` / `tso`, conjoined with `cfg.WF` (`CertCfg.WF`: the thread slots are
`B.threads + 1`, `slotsEq`, so the slot count is fixed by the published
budget; the source's thread capacity is at least the target's thread slots,
`Target.threadSlots`, the size of the loaded thread array, and above
`B.threads`, without which no `threads` abort is justified,
`threads_abort_unjustified`). The source
instance `SrcSem.source P p` is `ofStepsG p k arch (Spawn ∨ ext) (srcObs
trace)` (`SrcSem.sourceG`) with every step gated on `main` not having
returned (`mainExit c = []`), and the extern step and its event list a hook
(`SrcHooks`, empty in `SrcHooks.none` until WeakCore's lands); for every
hook whose event list only grows, the observable trace only grows
(`source_run_trace`) and has nothing after an exit
(`cutAtExit_exit_last`, rejected example `not_correct_event_after_exit`).

**Only canonical targets.** `Target` and `ExtMachine` are records of free
fields (`runs`, `atSys`, `live`, `exited`, `fault`, `stackRange`,
`regVal`, `privLoad`, `pc`, the extension steps, the loader). An arbitrary
instance trivialises the statement: `fault := fun _ => False` hides faults, a loader returning `none`
discharges everything but start. `Correct` is meaningful only for the
canonical `Target` of each ISA, defined once and part of the trusted base
(§4): `A64.canonical` (`Scc/Sem/TargetA64.lean`) and `X64.canonical`
(`Scc/Sem/TargetX64.lean`), built from Kraken's machine and the kernel
model (`Scc/Sem/Kernel.lean`, §3), each a function of the number of thread
slots (`CertCfg.slots`, fixed by `CertCfg.WF`). A certificate must
state `Correct (targetOf arch) …` with that canonical target; it must never
state `Correct` for a `Target` supplied by `scc`. There is no `waiting`
field (it would discharge progress for any thread): with the futex model of
§3 (K7, spurious returns) a thread in a futex wait can always step.

**The budget is published.** `B` appears in the statement and is chosen by
whoever produces the certificate; a tiny `B` makes almost every abort
justified. The statement is honest only with `B` published next to it:
`scc` prints `B` for each program, and the guarantee reads "the target is
correct for every run whose source stays within `B`; beyond `B` it may
abort, with the abort kind of the part of `B` the source crosses".

### 1.1 Layout, budget, value representation

- **Layout `Λ`** (`Layout`): ranges for the text, the writable static image
  (`.data`), the heap arena, the shared stack pool and the pinned region
  (`pinned`, the `.bss` range `scc_rt_pinned` of the thread control blocks,
  apart from the arena); the placement of the
  labels the setup block allocates (`static`); the static image as words;
  and `abortLbl k`, the assembler label of the `exit_group` of the abort
  stub of each kind `k` (a label, resolved by the target in the loaded text,
  `Target.resolve`, so that classification does not depend on model
  instruction sizes, §7.2) (`AbortKind`: `overflow`, `heap`, `stack`, `threads`,
  `writeErr`); and
  `symbols`, the address of each data symbol (assembler
  name) the text refers to, as the linker placed it: the `.data` and `.bss`
  labels, including the heap arena, the stack pool and the runtime's words;
  and `rodata`, the range of the read-only image the loader builds from the
  text's `.rodata` (outside `regions`, §7.2).
  `static` places source labels, `symbols` assembler names; the loader
  resolves the text's references through `symbols` (§7.1, item 9).
  `Layout.WF`: the five regions in the address space, never containing
  address 0 (`null`; `pos`, so a placed base is positive, `WF.lo_pos`), 16-aligned, pairwise disjoint; the stubs at distinct
  labels; every data symbol in a data region (`Layout.dataRegion`: data,
  heap, pool or pinned; `symIn`), below or above the code (`symAbove`,
  hence never in `code`, `WF.sym_not_code`), with distinct names
  (`symNodup`). Rejected
  examples `Holes.not_correct_sym_in_code` (a symbol on the text image),
  `not_correct_sym_dup`; accepted `symbols_wf`. `symAbove` is what the
  loaders need (they lay the label cells of the symbols below the code out
  before it and of the others after it, and refuse one inside it,
  `symsAbove`); with it
  and model code that fits in `Λ.code` the loaders' check refuses no
  well-formed layout. Thread control blocks are in `pinned`, which is
  shared (`Layout.shared`: data, heap or pinned; other threads read and
  write a block's futex permit and `exited`) and mapped read-write by the
  kernel model (`KState.init`). The futex and `clone` models read no
  memory (a futex wait may return spuriously, `clone`'s thread pointer is a
  number), so they need nothing of the region. The two stack-range
  transfer sites are not part of `Λ`: their labels are fixed
  (`XferKind.label`: `scc_rt_take_site`, `scc_rt_release_site`, §2.6) and
  resolved by the target like the abort labels.
  Two fields describe a collector, both off with none: `colourMask`, the
  reserved metadata bits of a reference word a collector may rewrite in a
  live slot with no source step (`ColourOnly`), `0` by default; and
  `relocates`, whether the runtime moves live objects, `false` by default
  (`Components.epoch_fixed`; without relocation `Components.pre_alloc`
  bounds the target writes to a label's range before its placement).
- **Budget `B`** (`Budget`, `Budget.Part`, `Budget.Within`), in source
  terms, one part per abort kind: heap use (`heapUse`: the words allocated,
  `cellCount`, plus one header word per allocation, `allocCount`, the sum of
  the threads' `nalloc`) within `B.cells`; threads created (`ths.size`)
  within `B.threads`; each thread's frames (`stack.length`) within
  `B.frames`; and "every number in thread `i`'s register environments is
  below `2^64`" (`NoBigNumT i`). `cellCount`, the distinct addresses in
  source memory, counts allocated words, not written ones: every
  allocation (`TermRun.alloc`, `allocBuf` for `newBuf`, with or without a
  zero) pushes one first message per word, `undef` or zero. *Heap form
  (chosen: target-sized, mode-dependent).* The intended heap part
  is `Σ_{l ∈ L} size(ty l) ≤ B.heap`, `size` the bipartite layout's object
  bytes (`8 · (1 + len · (n + m))`, plus alignment filler once 16-byte units
  land), `L` all labels under `gc none` and the live labels (§1.2, 5) under
  a collector; thread boxes (WeakCore's boxed `ThreadId`) count under
  `threads`, their control blocks being in `Λ.pinned`. Until WeakCore
  exports a per-label closed type, `heapUse` stands in under `gc none`,
  with an explicit margin: `objBytes t f = 8 · (1 + t) + f`, and
  `arena_margin` / `arena_covers` bound the arena bytes of allocations
  accounting for `cellCount` and `allocCount` (at most three target words
  per two source words, filler at most 8) by `16 · heapUse`, so an arena of
  `16 · B.cells` bytes is not exhausted within the heap part. *Runtime
  commitment for a future collector:* on arena exhaustion mid-cycle the
  allocator waits for the cycle to complete instead of aborting, and aborts
  with `heap` only if the arena is full right after a completed cycle; the
  arena is at least `2 · B.heap` plus the largest object. Then a live
  footprint within `B.heap` implies no heap abort; a waiting thread takes no
  steps, and progress (clause 2) holds because the collector thread is
  live. `Within` is
  every part for every thread. The source's own thread cap
  (`Spawn` needs `ths.size < cap`) is set to `B.threads + 1`: a spawn beyond
  the budget is then a source step that leaves it, which is what justifies
  the target's `threads` abort at that spawn (with `cap = B.threads` the
  source would block there and the abort would be unjustified). The target
  has `B.threads + 1` thread slots (`CertCfg.slots`, `CertCfg.WF`); a
  `clone` with every slot used is a fault (§3.1), so the runtime must abort
  before it. Plain
  `Int` `+` beyond `2^64` therefore counts as leaving the budget (checked
  `+`, aborting on overflow). Each part of the budget is the justification of
  one abort kind (`AbortJustified`, §1.2, 4). The target's
  thread slots are part of the statement (above); its other
  own limits (arena size, per-thread stack cap of at least
  `B.frames` times the largest frame plus slack) are facts about `Λ` that the
  proof of `Correct` uses; they are not part of the statement.
- **Value representation** (`ValRep lbl x v`): source value `x`, target word
  `v`, under a label placement `lbl`. `undef`: any `v`. `num n`: `v = n`, and
  `n < 2^64` (a larger number has no representation). `loc a tag`:
  `v = lbl a.label + 8 · a.offset + tag` with `tag < 8` (source offsets count
  words; a tagged pointer keeps its tag in the low bits). `null`: `v = 0`.

### 1.2 The clauses

1. **Start** (`Sim.start`). The loader yields a start configuration `t0`
   and `R t0 s0` for some source start `s0`, unconditionally: this is the
   heap-bytes fallback, which ships first (the image is empty). Route S
   (`RouteS Λ S`: some start configuration of the source has exactly the
   static image as the latest values of its static cells, `ImageMatches`)
   is defined but not part of `Correct` yet; when Route S exists it becomes
   a conjunct of `Correct` (checked per program by evaluation in the
   certificate), not a hypothesis of `start`: as a hypothesis, a false
   `RouteS` made `start` vacuous, and with a refusing loader every clause
   (`not_correct_load_none`).
2. **Progress** (`Sim.progress`). Every reachable target configuration has
   no fault and has either terminated or has a live thread and lets each live
   thread step (`ExtMachine.Progress`); a configuration
   where every thread is gone but no exit outcome was recorded is not
   progress (`not_correct_silent_exit`: otherwise `_start: exit` with no
   event, or a thread that just stops, would compile every program), and every shared location it has
   written lies in `.data` or the heap (`InLayout`). *Why:* the simulation
   clause alone is satisfied by a target that gets stuck; fault freedom is a
   property users want and the source cannot give. Exhaustion is not a stuck
   state: the target branches to its abort routine and exits with `abort`.
   What counts as a fault is the instance's `fault` (§2.3: a faulting
   instruction, a thread halted off its exit path, an unsupported system
   call).
3. **Simulation** (`Sim.sim`). For every run `t0 →tr→ t` there are a source
   run reaching `s` with trace `tr'` and `R t s`, and `obs tr` (the trace
   without its `writeErr`, `cloneErr` and `abort` events, which have no source
   counterpart) is a prefix of `tr'`. *Why prefixes:* a `write`
   may be partial, and the target emits one event per byte, so the target is
   behind the source between the source's `print` and the end of the write
   loop. The prefix relation also makes the first exit event, with its code
   modulo 256, part of the observable behaviour.
4. **Justified abort** (`Sim.abort`). For every run `t0 →tr→ t` and every
   step of target thread `tid` from `t` that emits `abort k`, there are a
   source configuration `s` reachable with trace exactly `obs tr` and
   `R t s`, a witness `w` with
   `Components M Λ w t s`, and a source thread `i` with `w.thr i = some tid`
   such that `AbortJustified B S tr s i k`:
   - `overflow`, `heap`, `stack`, `threads`: some step of thread `i` from
     `s` **crosses** the budget part of kind `k` (`B.Part k i`): the part
     holds at `s` and fails after the step. The parts are thread `i`'s own
     numbers (`NoBigNumT i`), heap use within `B.cells`, thread `i`'s call
     depth within `B.frames`, and the thread count within `B.threads`.
   - `writeErr`: `Ev.writeErr ∈ tr` (the kernel refused an earlier `write`).
   - `threads`, as an alternative to a crossing: `Ev.cloneErr ∈ tr` (the
     kernel refused an earlier `clone`, §3 K6c; `AbortJustified.of_cloneErr`).
     `EnvJustified tr k` names this environment justification; `crossing`,
     `part_before` and `not_of_not_part` assume its absence.

   Crossing, not merely ending outside: once a part is exceeded at `s` (a big
   number in a dead variable, say), "some step ends outside" would hold for
   every step of every thread and justify any abort.
   `AbortJustified.part_before` / `not_of_not_part`: a budget abort is never
   justified at a configuration already outside that part for that thread.

   The trace of `s` is exactly the target's observable trace: the target
   has produced every byte the source produced before the step that crosses
   the part. Without it a source that prints and then exhausts a budget
   admits a target that aborts at once (`not_correct_early_abort`).

   *Why:* without it, the program that aborts at once is a correct lowering
   of everything (`not_correct_spurious_abort` checks that the clause
   excludes it, for every kind). Tying the kind to the event and the
   justifying step to the aborting thread (through `thr`, hence the
   thread-indexed source step `SrcSem.step i`) rules out a compiler that
   aborts thread `tid` for a reason only another thread has, or that reports
   one exhaustion as another. Every overflow check stays in the emitted code
   (no check is elided), so the proof of `Correct` needs no lemma relating a
   target index to a source value beyond `R`; eliding a check later needs a
   WeakCore lemma that, in reachable states, an `Int[i]` variable holds the
   value of `i` and the checker's index facts hold.

   *Known looseness.* `R` has no program-point component, so "some step of
   thread `i` crosses the part" is not tied to the instruction that aborts:
   the justifying source step need not be the one the abort check guards.
   This is sound as stated because the source steps that cross a part (an
   `Int` `+`, an allocation, a call, a spawn) are determined by thread `i`'s
   current term and frame, so a thread whose next step crosses has exactly
   that step to take; but nothing in the statement forces the target to
   abort at that point rather than earlier in the same source step's
   lowering. The bridge spike should tighten it if it can (e.g. by a
   program-point map in `Witness`).
5. **`R` is explicit** (`Sim.explicit`). Whenever `R t s`, some `Witness w`
   satisfies `Components M Λ w t s`:
   - *thread map* `thr` (`thr_total`, `thr_inj`, `thr_onto`): each source
     thread is a distinct target thread; every running target thread is one
     (the runtime has no threads of its own);
   - *live labels* (`Live s l`): the memory clauses below cover only the
     labels reachable from the roots; a dead label's cells are runtime-owned
     (the collector may reuse them). `Live s := Reach s (RootLabel s)`.
     `RootLabel s l`: some thread `i` (`s.ths[i]? = some th`), frame depth
     `d` with environment `e` (`frameEnvs th`) and read set `xs`
     (`frameFv th`), a variable `x ∈ xs` with `lookupE e x = some (ty, ws)`,
     and a word `wd ∈ ws` with `wd.val = .loc a g` and `a.label = l`: the
     roots are exactly the words `env_total` places (a source thread holds
     no word outside its frames, so these are also the values in flight).
     `Reach s R` closes `R` under "a message (any message, not only the
     latest: a thread may read an older one) to a reachable label holds
     `.loc a g`", cells and boxes alike. A thread's control block is no root
     (a `ThreadId` is not yet a reference, §7, 1). With no threads nothing is
     live (`live_no_threads`). `Live` is a `Prop`, not a computed set;
   - *layout injection* `lbl`, `lsize` (`lbl_static`, `lbl_range`,
     `lbl_disj`, `lbl_mem`): each source label is an aligned word range in the
     heap or the static image, static labels where `Λ` puts them, distinct
     live labels disjoint (a dead label's range may be reused), every cell of
     a live label placed;
   - *placement epochs* `since`, `tsFrom` (`epoch_fixed`): a moving
     collector gives a label a new placement; `since l` is the source
     timestamp from which the current placement represents `l`'s messages
     (plus, per address, the latest earlier message, the value the move
     copied: `Witness.InEpoch`), `tsFrom l` the target timestamp after which
     target writes in its range are `l`'s. Unless `Λ.relocates`, `since` is
     0 for every label, so every source message is in the epoch; `tsFrom`
     is then free, and marks where the label's placement begins in target
     time: a target message to its range at or before `tsFrom` is either a
     source image or an outstanding promise of some thread (`pre_alloc`).
     That is the exemption for a promise made to recycled or arena memory
     before the allocation that covers it (§9.0, "Fresh allocation"); a
     fulfilled or non-promise write there is still rejected
     (`not_components_live_write`);
   - *value representation on memory* through a timestamp map `ts`
     (`mem_rep`, `ts_first`, `ts_mono`, `mem_onto`), on the messages to live
     labels in their epoch: each source message is a
     target message at the mapped word with a representing value (or the
     target's initial write: a fresh cell's `undef` message and a buffer's
     zero messages are the zeroed arena), in the same order. The word is
     read by `wordAt`: an 8-byte message at the address, or the low or high
     half of a 16-byte one, so the two source messages of a store pair
     (`pairs`) may share one target message. `ts_mono` is per location:
     on the positive images of messages to one live source location in its
     epoch, `ts` is strictly increasing. Across locations it says nothing:
     a target promise to an address the promising thread allocates later
     is placed at promise time but mirrored at fulfil time, so its source
     index is above messages to other locations whose target timestamps
     are higher; cross-location order is the view relation's concern
     (`ComponentsAll`, and `MemRel`, keep the global form, with equal
     images allowed exactly for a recorded pair; it implies the
     per-location one). `wordAt_of_read` reduces the 8-byte case to
     `Memory.read?`, so the 8-byte proofs are unchanged. Only the first
     message to a source address may be the initial write (`ts_first`), so
     on the messages to one address `ts` is strictly monotone, 0 included
     (`Components.ts_mono_loc`, for a live label in its epoch; the initial
     write only in the first epoch, `since = 0`); and every target write
     inside a live label's current range after `tsFrom` comes from a source
     message or is colour-only (`ColourOnly Λ`: it rewrites the previous
     message at its location in colour bits only; none with
     `colourMask = 0`, `not_colourOnly_zero`). Across addresses the initial write
     is not ordered: a cell allocated after a store elsewhere maps its first
     message to 0 although the store's image is positive, which a strictly
     monotone `ts` over all messages would forbid. Target writes outside
     every live label (allocator cursor, control blocks, headers, collector
     metadata, from-space copies, dead objects) are unconstrained, at
     every timestamp, at or below a label's `tsFrom` included. This is
     harmless: every read the source must match is of a live label's word
     (the read side uses only messages at that word); when an address
     enters a live range, every message already there is constrained at
     that related pair (`mem_onto` above `tsFrom`, `pre_alloc` at or below
     it), so reuse cannot bring stale contents into the image; and the
     trace comes only from kernel reads of live buffers. One consequence:
     a non-moving collector that reuses dead slots fails `pre_alloc` (the
     old non-promise messages in the slot have no preimage), so it needs
     `relocates = true`; the earlier `epoch_fixed` (forcing `tsFrom = 0`)
     was stricter still.
     `ComponentsAll` is the unscoped form (every label, no epochs);
     `ComponentsAll.scoped` turns it into `Components` when `since` and
     `tsFrom` are 0 (`pre_alloc` then follows from `mem_onto`), the
     migration path for proofs written against it.
     *Dead stays dead.* The statement's soundness does not need it (the
     components are checked at every related pair), but a collector's proof
     does. `dead_stays_dead`/`Reach.step`: a label neither live nor fresh
     (no message) stays dead across a step whose new messages and new roots
     refer only to live or fresh labels. Not proved for the source steps:
     `TermRun.Step.prom` appends an arbitrary value, which may refer to a
     dead label (`dead_promise`, `Scc/Sem/Live.lean`: the promised value is
     the only way, so this is the obligation certification must provide,
     WeakCore's no-forging invariant on solo runs); thread steps
     (`tstep`/`evalOp`) are unproved (no operation turning a number into a
     reference was found, and `offs` stays within its label, but this is
     not proved);
   - *register-environment map* `env` (`env_rep`, `env_total`): source
     thread, frame depth (0 is the current frame), variable and word index ↦
     register or stack slot; each placed word is represented by the value at
     its place, and every word of every variable the frame still reads is
     placed (`frameFv`: the free variables of the current term, or of a
     suspended frame's continuation less its result variable; `exprFv`
     removes a name exactly where the runtime binds it, so it is WeakCore's
     `TermScope.freeB` (`mem_exprFv`, `Scc/Sem/Scope.lean`): `unpack`'s
     index, the region of `region`/`openPub` and `parity`'s `k` bind
     nothing, and `cas`/`casp` bind `t` in the `ok` branch only). Only dead variables
     may be dropped. *Provisional:* how heap references in registers and
     slots are related (and whether `env` must also expose them as tracing
     roots) waits on WeakCore's GC tracing design; a placed word holding a
     reference represents it by the current label placement `lbl` (one
     placement per related pair: after a move, `R` relates the target only
     once every live root is rewritten). The roots of `Live` are exactly the
     words this clause places;
   - *stack map* `marked` (`stack_pool`, `stack_disj`, `stack_owned`,
     `stack_private`, `stack_marked`, `stack_unmarked`): each thread's current
     stack range is in the pool, ranges are disjoint, a range is mapped in its
     thread's private memory and in no other's, no shared write lands in one,
     every marked place points into its own thread's range, and no place that
     holds a source word is marked. With the layout injection (labels avoid
     the pool) this says that the marked places are exactly the words that a
     stack copy has to rewrite: stack pointers never escape, and nothing that
     represents a source value is one. The source has no stack addresses
     (every `Ptr`/`Loc` is an allocation label), so the clause concerns only
     stack pointers the lowering introduces (saved frame pointers, addresses
     of spilled slots).

   `R` may say more (view and promise-set correspondence, pc ↔ term
   position, runtime invariants); those are internal to a proof. *Why:* so
   that WeakCore's results about reachable source configurations reach the
   binary: `Sim.transfer` gives, for each reachable target configuration, a
   related source configuration with the invariant and the components;
   `Sim.transfer_stepsX` does the same for a property proved along
   `TermSpawnStep.StepsX`, the form of `SpawnArmZ.reachable_typed_spawn` and
   the token-soundness theorems.

**Not covered:** liveness (a target that hangs, or loses a wake-up, satisfies
the statement), performance, the kernel and hardware beyond the models of §3
and §4.

### 1.3 Sanity lemmas (proved)

- `ExtMachine.ofBase_run_iff`: with no transfer site resolved, the base
  instance's runs are exactly `Live.Inf.ReachableSemInf` runs, with empty
  traces.
- `components_empty`, `correct_trivial`: the components are satisfiable, and
  the empty assembly is a correct lowering of the empty program on the
  existing machine, for every budget, with every clause discharged.
- `not_correct_spurious_output`, `not_correct_spurious_abort`: a target that
  prints a byte, or aborts (any kind), is not a correct lowering of the empty
  program.
- `AbortJustified.crossing`, `part_before`, `not_of_not_part`: a budget
  abort with no environment justification (`EnvJustified`: a refused
  `clone` for `threads`) is justified only by a step that crosses its part.
- `Sim.transfer`, `Sim.transfer_stepsG`, `Sim.transfer_stepsX`,
  `Sim.transfer_source` (above); `SrcSem.ofStepsG_run_stepsG`,
  `SrcSem.ofStepsG_run_trace`, `SrcSem.source_run_stepsG`.

All use only `propext`, `Classical.choice`, `Quot.sound`.

**Holes and their regression lemmas** (`Scc/Sem/Holes.lean`, toy
instances: a scripted source whose configurations are program points, toy
targets with at most one Kraken thread, which never takes an instruction
step). Rejected:

- `not_correct_early_abort`: a target that aborts (kind `heap`) at once,
  printing nothing, for a source that prints a byte and then exceeds the
  heap budget (clause 4 ties the justifying source trace to the target's).
- `not_correct_silent_exit`: a target whose only thread exits with no event
  (no live thread, `exited = none`), for a source that prints and exits.
- `not_components_skipped_store`: no witness gives `Components` for a target
  that kept only the first of the source's stores `x := 1; x := 0` to a cell
  a variable the thread still reads points to (`components_both_stores`,
  `components_live_stores`: the faithful target passes). Accepted by
  design, `components_skipped_store_dead`: with no reference left, the cell
  is dead and the skipped store admitted.
- `not_components_live_write`: a target write into a live label's range with
  no source message (stores `0; 1`, target writes `1; 3` to the word) is
  rejected, for every choice of `tsFrom`: after it by `mem_onto`, with no
  colour bits; at or before it by `pre_alloc`, the write being no
  outstanding promise.
- `not_correct_load_none`: a target whose loader refuses every text.
- `not_components_empty_env`: no witness gives `Components` when the source
  variable about to be read holds 5 and every target register holds 7 (the
  empty `env` no longer passes; `components_env_placed`: placed in a register
  holding 5, it passes).
- `not_correct_wrong_exit`, `not_correct_wrong_store` (P10): a target that
  exits with 4 for a source that exits with 3, or that stores 2 and prints
  it for a source that stores 1 and prints it.

Accepted (sanity): `correct_justified_abort`, a target that prints and then
aborts at the resolved heap abort site, for a source that prints and then
crosses the heap budget.

Each was first proved as an accepted hole against the earlier statement;
dropping the corresponding clause turns it back into one.

## 2. Kraken machine extensions

The extended machine is a new instance of `ExtMachine`, built in Kraken. Its
instruction step is, by construction of `ExtMachine.Step`, the existing
`Live.Inf.StepSemInf A tid` on `Config I`; the extension only gates it
(`runs`, `atSys`) and adds steps beside it (`spawn`, `sys`, `xfer`). Every
step of a thread is gated by `runs` (`Step.runs`: a thread of a dormant slot,
one that has called `exit`, or any thread after `exit_group` takes no step
at all); `xfer k` is further gated by the thread's pc (`ExtMachine.pc`) being
at the site of kind `k` (`ExtMachine.AtSite`), so that a range transfer
cannot serve as the step that makes progress hold elsewhere, and at a site
the instruction step is disabled (`Step.instr` asks `¬ AtSite`), so that
the transfer is forced (§2.6). A
`sys` step emitting `Ev.abort k` must be at the address of `Λ.abortLbl k`
(`ExtMachine.AtAddr`), and one emitting `Ev.exit` at none of the abort
sites. `Step`, `Run` and `Progress` take these code addresses as a
parameter (`Marks`: the address of each transfer site and the abort site
of each kind); `Correct` uses `Target.marks`, the target's resolution
(`Target.resolve`) of `XferKind.label k` and `Λ.abortLbl` in the loaded
text, so `Λ` holds no numeric
code address. Nothing in the
existing `Config`, `Thread`, `stepOne`, `certify` or `StepSemInf` changes.

### 2.1 Spawn: dormant slots (recommended) or a growing thread array

| | Dormant slots | Dynamic array |
|---|---|---|
| Shape | `Config.threads` has `CertCfg.slots` entries from the start (`B.threads + 1`, `CertCfg.WF`); unused slots hold a halted state (pc at the end address) with no promises; `clone` overwrites one | `clone` pushes a thread |
| Existing proofs | Unaffected: thread indices are stable, `Config.withThread` is `set!`, the array size is constant along runs, a dormant thread is halted, so `stepOne` is `none` for it, `Config.final` treats it as finished, and certification of other threads ignores it | Every lemma that uses a constant `threads.size` (`Config.Bnd`, the K-world chain, kits) needs a case for growth |
| Source | WeakCore's `Cfg.cap` (labels striped by `max cap ths.size`) already fixes a capacity | WeakCore pushes children (`spawnT`), so the thread map is a renaming either way |

**Recommendation: dormant slots.** `thr` maps source thread `i` to whichever
slot the `clone` for it activated, and the thread map absorbs the
difference with WeakCore's push.

The activation (`spawn tid c c'`, the `clone` of §3, K6): the parent's
outstanding promises stay its own (certification after the step checks
them, §2.2); the child slot gets the parent's executable, the parent's register values
except the return register (0) and `sp` (the `stack` argument), the thread
pointer (`tls`), pc after the system call, the parent's `Views`, register
views 0, no promises, and as private memory the range the parent holds
that ends at the `stack` argument, with its bytes, or none (§2.6: the
runtime takes the child's stack at the take site in the parent before the
`clone` and only writes the control block, in the heap). The parent's return
register gets a positive kernel thread id that the runtime ignores. The
emitter puts a full fence (`dmb ish`, `mfence`) immediately before the
`clone` system call, so the parent's views at the call are post-barrier
views; the model's step adds no fence of its own. This matches WeakCore's
`Spawn` (`spawnCfg`): the parent takes a full barrier and the child starts
at the parent's post-barrier views, with no outstanding promises and memory
unchanged.

### 2.2 System-call instructions and certification through them

Forms: AArch64 `svc #0` (number in `x8`, arguments `x0`–`x5`, result in `x0`,
every other register preserved); x64 `syscall` (number in `rax`, arguments
`rdi`, `rsi`, `rdx`, `r10`, `r8`, `r9`, result in `rax`, `rcx := next pc`,
`r11 := rflags`). Each needs syntax, parser, printer, `Directive.deps`
(defines the result register; uses the number and argument registers) and a
sequential semantics.

**Finding: certification must be able to pass a system call.** A promise is
certified by a promise-free solo run of the thread (`CertOk`, built on
`stepOne`). If the solo run cannot get past a system call, then no write after
a system call can ever be promised before it, i.e. the model orders every
earlier write of the thread before every later write across a system call.
AArch64 gives no such guarantee (exception entry and return are context
synchronising, not barriers), so that model would forbid hardware
behaviours, which is unsound for this direction of simulation.

**Recommendation:** give each system-call instruction an *over-approximating*
sequential semantics, used only by certification: the result register is
`undefined` (any 64-bit value; on x64 also `rcx`/`r11` as the hardware sets
them), pc advances, no memory event. In `Config` this is the instruction's
`EvTree`, so `CertOk` passes through it. The real step at a system call is
the extension's `sys` (or `spawn`) step: the instance's `runs c tid` is false
while thread `tid` is at a system call, so the havoc tree is never taken as
an instruction step. Every behaviour of the real kernel is among the havoc
tree's (it changes nothing but those registers, §3, K2), so certification
can only get more permissive, never less. With this, a system call is not a
fence anywhere in the model (§3, K2), except `clone` (K6).

Implemented (§3.1, *Promises at a system call*) without changing Kraken's
instruction semantics: certification runs `Hooks.cexec`, which the canonical
targets set to `Kernel.certExec`, choosing among the results the kernel
model may return rather than havocking the result register.

**Superseded.** The havoc recommendation and `certExec` are no longer what
the canonical targets certify with. Certification is the faithful solo
projection of the kernel step (`Kernel.soloExec`, `Kernel.certSem`): at a
system call the states `sysStep` returns the thread to from the solo
configuration, at a transfer site the state `xferStep` leaves it in, at
`clone` no branch (§6, 44). The residual differences from the kernel step
are the table of §3.1.

### 2.3 The extern step and the trace

`sys tid c es c'` covers `write`, `exit`, `exit_group`, `futex`,
`rt_sigaction` and `arch_prctl` as specified in §3; `es` is the list of events
(one `Ev.out b` per step for each byte written to fd 1, `Ev.writeErr` for a
refused `write`, `Ev.cloneErr` for a refused `clone`;
`Ev.exit (v % 256)` or `Ev.abort k` for `exit_group`; nothing otherwise).
After `exit_group`, `exited` is `some` and no thread runs; `exited` is
`abort k` iff the `exit_group` was at the label `Λ.abortLbl k` (its address
in the loaded program, `Target.resolve`; `Step.sys` checks it against the
thread's pc, `Step.abort_at`).

The instance's other observations: `live` (an active slot that has not
called `exit`), `fault` (a faulting instruction step, a thread halted anywhere but its
`exit`, an unsupported system call or argument, an `unaligned_sp` effect,
an access outside the mapped regions, K11),
`regVal`/`privLoad` (the ISA's register file and an 8-byte
`Mem.loadInt` of `dmem`), `stackRange` (the thread's current stack range,
§2.6).

### 2.4 Thread pointer

- **x64:** a new `MachineData` field `fsBase : BitVec 64 := 0`, and an
  optional `fs:` segment on memory operands that adds `fsBase` to the
  effective address. Set by `arch_prctl(ARCH_SET_FS)` and by `clone` with
  `CLONE_SETTLS`. The emitter uses `fs:` only on 8-byte `mov` loads of
  control-block fields. `fsBase` carries no dependency view (it is not a
  register of `RegId`): an access through `fs:` has no address dependency on
  it, which only allows more reorderings.
  Lower-risk alternative, if the `MachineData` change proves costly:
  `rdfsbase` (register-only, needs the kernel to enable FSGSBASE) and plain
  addressing; `fs:` was decided, so it stays the design.
- **AArch64:** a new `MachineData` field for `TPIDR_EL0` (default 0) and the
  instructions `mrs xN, tpidr_el0` / `msr tpidr_el0, xN`, register-only, no
  view on the system register (as above). Set by `clone` with
  `CLONE_SETTLS` and by `msr` once in `_start`.

### 2.5 Abort outcome

No new machinery: there is one abort stub per kind `k`; each writes its
message to fd 2 (no events) and calls `exit_group(101)` at the label
`Λ.abortLbl k`,
which the `sys` step reports as `Ev.abort k` and `Outcome.abort k`. The host
sees exit status 101 for every kind. The statement's abort clause (§1.2, 4) is
what limits when it may be reached.

### 2.6 Range transfer (stack pool)

The pool region `Λ.stackPool` holds stack ranges only. The pool's shared
metadata (free list, cursor, any lock) lives in `Λ.heap` or `Λ.data`, so its
writes are shared writes inside `Layout.shared` (`InLayout`) and the pool
region is only ever accessed as private stack memory (`stack_private`,
`stack_owned`). This is a constraint on the runtime's pool.

Implemented (`Kernel.takeStep`, `Kernel.releaseStep`, `Kernel.spawnStep`,
`Kernel.fresh`). A range moves between the pool and a thread's private
memory (`dmem`) only at two **forced, deterministic transfer sites**, each a
`nop` at a fixed label (`XferKind.label`, resolved by the target in the
loaded text, `Target.marks`):

- **take**, `scc_rt_take_site`: the single exit of `scc_rt_stack_take`,
  while the range's base and size are in the first two argument registers
  (`x0`/`x1`, `%rdi`/`%rsi`; `Kernel.siteRange`). The range must be
  **fresh**: nonempty, inside `Λ.stackPool` and the address space,
  disjoint from every range a thread holds (`KState.held`) and from every
  shared write, initial or not. It enters `dmem` with the pool's bytes
  (`KState.pmem`: zero for a range never held, else its bytes at its last
  release) and is recorded as held by the thread.
- **release**, `scc_rt_release_site`: the entry of `scc_rt_stack_release`,
  same registers. The thread must hold the range and must not be on it
  (`Kernel.onStack r sp`: `r.lo < sp ≤ r.lo + r.size`; an empty descending
  stack has `sp` at the top). The range leaves `dmem`, its bytes go to
  `pmem`, and it is no longer held.

At a site the instruction step is disabled (`Step.instr` asks
`¬ AtSite`); the only step a thread there can take is the transfer of the
range its registers name (`Kernel.step_at_take`, per ISA `A64.take_forced`,
`X64.take_forced`; `Kernel.xfer_det`), which moves it past the `nop`. If
the instruction at the label is not a `nop`, or the side conditions fail,
the thread is **stuck**, which progress excludes; so a correct target does
take and release exactly the ranges its runtime takes and releases. A
transfer that were optional, or whose range were chosen freely, could not
be used by a proof of `Correct`, which speaks of every run: a run that
skips the transfer, or moves another range, puts the thread's stack
accesses into shared memory outside `Layout.shared` and breaks `InLayout`.

`clone` moves the range the parent holds that ends at the child's `stack`
argument (taken by `scc_rt_thread_init` in the parent before the `clone`)
to the child, with its bytes; with none the child has no private memory.
`stackRange` (`Kernel.stackRangeOf`) is the held range the thread's `sp` is
on. The main thread's first range goes through the take site like every
other (the runtime's start-up must take it through `scc_rt_stack_take`),
so no start-up special case is needed. Growth takes the new range at the take site, copies the
live words, rewrites the marked places, switches, and releases the old
range at the release site once it is off it.

**Reuse** through the pool is modelled: a released range is fresh again
and the next take restores its bytes (`Kernel.release_take_handoff`;
`take_bytes`, `release_bytes`). What the proof of `Correct` needs from the
runtime's lock protocol (per-class free arrays under a spin lock, lock an
acquire RMW, unlock a release store), stated here and not proved: the
release site comes before the push of the range under the lock, and the
take site after its pop. Then the releaser's unlock (release) and the
taker's lock (acquire) put every access of the releaser to the range
before every access of the taker, so the bytes the model hands over in
`pmem` are the hardware contents of the range, and the taker's private
accesses agree with what it would read from shared memory. The proof must
also show that the runtime's choice is a fresh range (`stack_pool`,
`stack_disj`, `stack_owned`, `stack_private`), not assume it.

**Runtime and emitter obligations.** `scc_rt_stack_take` has a single exit
whose instruction is a `nop` labelled `scc_rt_take_site`, reached with the
range's base in `x0`/`%rdi` and its size in `x1`/`%rsi`;
`scc_rt_stack_release` begins with a `nop` labelled `scc_rt_release_site`,
with the same registers; neither label occurs elsewhere and the emitter
and assembler keep both `nop`s. No stack word is read before it is
written in the current range (a fresh range never held reads zero; a
reused one its old bytes, which the runtime must not rely on).

### 2.7 Conservativity checklist

- Instruction step = `StepSemInf`, by the interface; the base instance is the
  existing machine (`ofBase_run_iff`).
- New instruction constructors (`svc`, `syscall`, `mrs`/`msr`, the `fs:`
  operand): new cases in every exhaustive match, with the semantics above and
  nothing for existing forms; parser and printer tests; `.S` tests for the
  single-threaded register effects where `asm_tests.py` can observe them.
- New `MachineData` fields with defaults: audit positional constructions and
  `deriving` users (`BEq`, `Hashable`, `DecidableEq`); the hash gate must show
  every existing theorem unchanged; litmus suites unchanged (no new forms
  occur in them).
- Kits generalised to one shared text: a spawned thread runs the parent's
  executable (copied at activation).

## 3. The kernel model

Implemented in `Scc/Sem/Kernel.lean` (§3.1), each assumption a named
definition there. Linux, one process, threads created only by the runtime.

- **K0 (no other actors).** Nothing but the program's threads writes its
  memory: no `CLONE_CHILD_SETTID`/`CLONE_CHILD_CLEARTID`, no shared mappings,
  no signal handlers. Asynchronous external signals are out of scope.
- **K1 (calling convention).** As in §2.2. Unknown system-call numbers and
  unsupported arguments are faults.
- **K2 (no ordering).** A system call is not a fence. Its memory accesses are
  performed by the calling thread, in program order, as the accesses listed
  below; its other effect is on the listed registers only. (This is the
  weakest model; the runtime never relies on a system call for ordering.)
- **K3 (`write(fd, buf, n)`, `fd ∈ {1, 2}`).** The kernel reads
  `buf[0..k)` as plain 1-byte loads (each value readable by the thread under
  the memory model) and returns `k ∈ [1, n]`; for fd 1 the call is `k + 1`
  steps of the thread, one per byte emitting that byte's `Ev.out`, then the
  return, and other threads' steps (and their `write` bytes) may come between
  them; for fd 2 the bytes emit nothing. Or it returns `-EINTR` or
  `-EAGAIN` with no output, or `0` or another error, in which case the step
  emits `Ev.writeErr` (and the runtime branches to the `writeErr` stub).
  No atomicity per call is assumed: Linux gives it only for pipes up to
  `PIPE_BUF` bytes, and the source's `out` is per byte anyway. The statement
  enforces the granularity: a step emits at most one event
  (`ExtMachine.Step.sys`, `Step.events_le_one`).
- **K4 (`exit(code)`).** The calling thread ends (its slot is no longer
  live); no memory effect. Certification makes its promise set empty first.
- **K5 (`exit_group(v)`).** The process ends: `Ev.exit (v % 256)`, or
  `Ev.abort k` at the label `Λ.abortLbl k`. Other threads stop where they are; their
  outstanding promises are never fulfilled, which nothing can observe.
  `main`'s own thread has none where its return is the exit: on the
  source, a finished thread 0 is certified only with no promises, so every
  reachable source configuration at which `mainExit` fires has thread 0
  promise-free (`SrcSem.source_mainExit_noProm`, given that an extern step
  does not finish thread 0 with promises); `mainExit` needs no promise
  condition.
- **K6 (`clone`)**, flags exactly `CLONE_VM | CLONE_FS | CLONE_FILES |
  CLONE_SIGHAND | CLONE_THREAD | CLONE_SYSVSEM | CLONE_SETTLS`, `ptid` and
  `ctid` null, always issued right after an emitted full fence (`dmb ish` /
  `mfence`). **K6a (child's view):** the child starts with the parent's views
  at the call, i.e. it observes everything the parent had observed or
  written before the fence (the kernel's hand-off of the new task to a CPU
  includes the barriers that make this so; it is the one point where the
  model relies on the kernel for ordering). This is WeakCore's `spawnCfg`
  (parent `fenceS … .sy`, child at the parent's post-barrier views,
  `mine := []`, argument words bumped to the parent's `vRelSt`).
  **K6b (registers):** as in §2.1. The process has `CertCfg.slots`
  thread slots; a `clone` with no dormant slot is a fault (§3.1, *Thread
  slots*): the runtime must abort with `threads` before it (the source's
  next spawn leaves `B`, §1.1). **K6c (refusal):** any `clone` may instead
  return `-EAGAIN` or `-ENOMEM` with no other effect; the step emits
  `Ev.cloneErr` (not observable), which justifies a later `threads` abort
  (§1.2, 4), as `writeErr` does for `write`.
- **K7 (`futex`, private).** `FUTEX_WAIT(addr, val)` may return `0`,
  `-EAGAIN` or `-EINTR` at any time and performs at most a plain 4-byte load
  of `addr`; `FUTEX_WAKE(addr, n)` returns some count in `[0, n]` with no
  memory effect. `addr` must be a 4-aligned heap address. Spurious returns
  make blocking unobservable to safety (the runtime rechecks the permit word
  with its own release/acquire accesses), so the model needs no wait queue.
- **K8 (`rt_sigaction(SIGPIPE, SIG_IGN)`).** Returns 0; reads the action
  structure with plain loads; afterwards a write to a closed pipe returns
  `-EPIPE` (K3) instead of killing the process.
- **K9 (`arch_prctl(ARCH_SET_FS, a)`, x64).** Sets the calling thread's
  `fsBase` to `a`, returns 0.
- **K10 (initial state).** One active thread (slot 0) at `_start`, the others
  dormant; memory is the ELF image (text, `.data` image, everything else in
  `.bss` zero); thread pointer 0. The kernel's initial stack is not used
  after `_start` switches to a pool range.
- **K11 (mappings).** `.data`, the heap arena, the stack pool and the
  initial stack are mapped read-write for the whole run, the code
  read-only; there is no `mmap`. Any other access, and a write to the
  code, is `SIGSEGV`, i.e. a fault, which progress excludes.

**Memory ordering across a system call:** none (K2), except K6a. **The
child's initial view:** the parent's views at the call, which the emitted
fence makes post-barrier views (K6a).

**Emitter obligations from the source machine.** `TermRun` forbids some
outcomes that herd7 (and hence Kraken) allows; a target behaviour there would
have no source counterpart, so the emitter must not produce these forms:

| Pattern (herd7 allows, `TermRun` forbids) | Obligation |
|---|---|
| `SB+cas{,a,l}-rfi-ldr-addrs`, `SB+cas{,a}-rfi-ldar-addrs`: an RMW's write read back by the same thread and used as an address | such an RMW must be an acquire-release (`-AL`) RMW, or the write a release store re-read by `LDAR`; never `LDAPR` |
| `LB+casp` (`TermRun` makes single-word promises only) | lower `casPair` as `CASPAL`, or `CASP` preceded by `DMB ISH` |
| `MP+str-stp+dmb.sy` (pair store) | a pair store `STP` preceded by `DMB ISH` |

These are also the first instruction forms the spike (§5) checks.

### 3.1 The implementation (`Scc/Sem/Kernel.lean`)

The canonical targets' hooks are `Kernel.hooks abi A n` (`A64.kernel n`,
`X64.kernel n`) with `n = CertCfg.slots`. The trusted kernel assumptions, each a named
definition of `Scc/Sem/Kernel.lean` (the per-ISA `abi` only reads and writes
registers):

| Name | Assumption |
|---|---|
| `Nrs.a64`, `Nrs.x64` | the Linux system-call numbers `scc`'s runtime uses (`write`, `exit`, `exit_group`, `futex`, `rt_sigaction`, `clone`; x64 `arch_prctl`), and `clone`'s argument order |
| `eintr`, `eagain`, `maxErrno`, `futexWaitPrivate`, `futexWakePrivate`, `sigpipe`, `sigsetSize`, `archSetFs`, `cloneFlags`, `pidMax` | Linux constants |
| `Abi`, `A64.abi`, `X64.abi` | K1: `svc` (any immediate) / `syscall`; number `x8` / `%rax`; arguments `x0`–`x5` / `%rdi`, `%rsi`, `%rdx`, `%r10`, `%r8`, `%r9`; result `x0` / `%rax`, x64 also `%rcx :=` next pc and `%r11 := RFLAGS`; every other register preserved; the pc past the instruction; thread pointer `TPIDR_EL0` / `fsBase` |
| `decode` | K1: the supported calls and arguments; any other is a fault (`faultAt`) |
| `readByte` | K2, K3: a `write` byte is read from private memory if mapped there, else by a plain load of the calling thread (Kraken's `readSuccs`, no register dependency) of the 8-byte word containing it |
| `sysStep` | K3 (`write`, per byte, `-EINTR`/`-EAGAIN`, refusals `writeRefused` with `writeErr`), K6c (`clone` refused with `-EAGAIN`/`-ENOMEM` (`enomem`) and `cloneErr`), K4 (`exit`), K5 (`exit_group`, `exitCode`, `abort k` when the status is `abortStatus`), K7 (`futexWaitRet`, wake count up to `n`), K8 (`rt_sigaction` returns 0), K9 (`arch_prctl`) |
| `spawnStep`, `childThread` | K6, K6a: `clone` activates a dormant slot; the child starts at the parent's views, register views 0, no promises, and as private memory the parent's held range ending at its stack pointer, with its bytes, or none |
| `KState.init`, `CertCfg.slots` | K6b, K10: `n` thread slots (the certificate's, `B.threads + 1`), slot 0 running at load; the stack pool from the layout, no range held, pool bytes zero |
| `fresh`, `takeStep`, `siteRange` | §2.6: at the take site the range in the first two argument registers, in the pool and the address space, disjoint from every held range and every shared write, moves into private memory with its pool bytes |
| `releaseStep`, `onStack` | §2.6: at the release site a held range the thread is not on moves back to the pool with its bytes |
| `stackRangeOf` | §2.6: a thread's stack range is the held range its `sp` is on |
| `retThread` | a returned result has register view 0 |
| `ready` | a system-call step needs no exited process and a running slot (outstanding promises are allowed) |
| `results`, `certSuccs`, `certExec` | certification (§2.2): a supported system call returns to the calling thread one of the values `sysStep`/`spawnStep` may return (`sysStep_ret_mem`, `spawnStep_ret_mem`), as a choice of `Abi.ret` states with no event; `exit`/`exit_group` are dead ends, and under the solo projection `soloExec`/`certSem` so is `clone` (§6, 44); the ISA's `exec` elsewhere |
| `CertAfter`, `Hooks.cexec` | a kernel step (`sys`, `spawn`) leaves the calling thread certified under `certExec`, and every instruction step certifies under it (`StepSemC`) |
| `faultAt` | K1 faults; `clone` with no dormant slot (K6b); a running thread that has halted (run off its code) |
| `KState.rw`, `KState.ro`, `mappedRegions`, `mapped`, `Touches`, `unmappedAt` | K11: read-write `Λ.data`, `Λ.heap`, `Λ.stackPool`, the initial stack `E.stack` (and the held ranges, inside the pool); read-only `Λ.code`; a running thread whose instruction may reach a shared access with a byte outside the regions mapped for it is a fault |

Where the implementation is more specific than the list above:

- **Promises at a system call and at the transfer sites** (`certSem`,
  `CertAfter`). Certification passes system calls: Kraken's instruction
  step halts at `svc`/`syscall` (`MachineData.pendingSyscall`), so the
  extended machine certifies with Kraken's `stepOneWith` over `Hooks.cexec`,
  which the canonical targets set to `Kernel.certSem` (marks `μ`, the
  kernel state of the step): the solo projection of the kernel step
  (`soloExec`). At a supported call other than `clone` it chooses among the
  states `sysStep` returns the thread to from the solo configuration (only
  that thread, no shared write, no byte of a `write` out), with the
  kernel's register dependencies (`svcDeps`, the result registers from no
  input, so the result views are `retThread`'s); at `write` also the
  byte loads (`writeTree`); at a transfer site the state `xferStep` leaves
  the thread in; at `exit`, `exit_group` and `clone` nothing. A thread may
  reach a system call with outstanding promises, and a write after a system
  call can be promised before it (the target files check `futex` wake,
  `rt_sigaction` and `exit_group`). The design invariant is: the first step
  exact, later steps never under-approximating, except where the table
  says. It is enforced by this table, not a theorem.

  | Residual | Direction | Status |
  | --- | --- | --- |
  | `fresh`'s message part not checked in the solo configuration (no shared write there); the release's range match loose | over-approximates | sound |
  | `write`: certification does not raise the thread's views by the kernel's byte reads (`readByte`) | over-approximates | sound |
  | the pool bytes are the kernel state's at the step, fixed for the run: a range released and re-taken in one certification run reads stale bytes | under-approximates | obligation `NoRetakeAfterRelease` (no certification run takes a range it released earlier in the same run); unreachable for the programs certified so far (no release site reached) |
  | the thread's own held ranges at `clone` | under-approximates | obligation `NoTouchAfterHandoff`; moot while `clone` is a dead end |
  | `clone` a dead end (no promise across it) | under-approximates | argued hardware claim (§4, *No promise across `clone`*; §6, 44) |

  What the proofs give on top (`Scc/Sem/CertLift.lean`,
  `Scc/Sem/CertSys.lean`): after a take whose range's pool bytes are zero,
  a certified thread is certified (`certAfter_take`), although the `xfer`
  hook itself asks no `CertAfter`; at a supported call other than `write`
  and `clone` a certified thread with promises has a kernel return after
  which it is certified (`sys_progress`), and none is certified at `exit`
  or `exit_group` (`prom_nil_of_exit`). At `write` that converse is open
  (§9, *Open for hello1*). Still differing:
  - **`futex`** has no memory effect in either (K7).
  - `sysStep_ret_mem` assumes the `write` progress record is at most the
    requested count (an invariant of `sysStep`'s `write` steps, not proved
    here).
- **`write` reads** (K3). Kraken has no mixed-size accesses and the model's
  memory holds 8-byte words (`wordLoc`), so the kernel reads the 8-byte word
  containing each byte and takes the byte; on hardware it reads the byte.
- **`futex`** (K7). The model performs no load of the futex word (its value
  does not affect the result, which is spurious anyway); a missing load only
  allows more reorderings.
- **`rt_sigaction`** (K8). The action structure is not read; the call returns
  0. A refused `write` is always possible (`writeRefused`), which covers
  `-EPIPE`.
- **`clone`** (K6). The child's thread id is any value in `(0, pidMax)`, the
  slot any dormant one. The child's private memory is a fresh range ending
  at its stack pointer, or empty (§2.6). The parent's forwarding and
  exclusive records are not inherited.
- **Thread slots** (K6b). The process has `CertCfg.slots = B.threads + 1`
  slots, and a `clone` with none dormant is a **fault**. Linux would return
  `-EAGAIN` (or succeed, if its limits allow more threads), and the
  runtime would abort with `threads`. The fault is sound without trusting
  the runtime (a proof of `Correct` must show the runtime never gets there)
  and provable once the runtime caps its threads below the slot count. The
  runtime has **no thread cap** today: its control blocks come from the
  heap arena (`scc_rt_alloc_tcb`), so its only limits are arena exhaustion
  and a failed `clone`; it needs a count check before `clone`. Assumed of
  Linux: a `clone` below the slot count succeeds; the refusals Linux may
  give there (`-EAGAIN` under `RLIMIT_NPROC`, `-ENOMEM`) are behaviours the
  model now has (K6c, `Kernel.sys_cloneErr`); a `clone` that Linux lets
  succeed beyond the slot count is excluded by the fault, which a proof
  must rule out through the runtime's cap.
- **Stack ranges** (§2.6). Ranges move only at the take and release sites
  (and to a child at `clone`); the move is forced and deterministic, a
  wrong site instruction or a range failing the side conditions leaves the
  thread stuck. Reused ranges keep their bytes through `pmem`; that these
  are the hardware contents rests on the lock protocol of §2.6.
- **Mappings** (K11). The fault is on the instruction, before its
  access: `unmappedAt` holds when some path of the instruction's event
  tree (`Touches`, over every choice and every value an earlier access of
  the same instruction may return) reaches a shared load, store or RMW
  with a byte outside the regions mapped for it. Over the returned values
  this over-approximates, which only makes the fault, and so `Correct`,
  stronger. Private accesses (`dmem`) are not checked: a thread's private
  memory is its initial stack and the ranges it holds, all mapped. Writes
  were already confined by `InLayout` (shared writes only in `.data` and
  the heap); K11 adds reads and makes an unmapped access a fault where it
  happens. Not checked: the instruction fetch (a pc outside the code makes
  Kraken's thread halt, which `faultAt` reports), and a promised write,
  which `InLayout` covers once it is in memory. The kernel's own reads of
  a `write` buffer are not checked: Linux returns `-EFAULT` there, which
  the always-possible refusal (`writeRefused`) covers.

## 4. Trusted base

- Kraken's ISA semantics (AArch64 `isaLSE2`, x64 `isa`) and memory models
  (`Arch.armv8`, `Arch.tso`), and their fidelity to hardware; litmus-checked
  against herd7, not proved.
- The canonical extended machine instance and `Target` of each ISA (§2, one
  per ISA, defined once) as the meaning of "a target behaviour"; `Correct`
  says nothing for other instances (§1, *Only canonical targets*);
  and the kernel model (§3) with K0–K11, implemented by the named
  definitions of `Scc/Sem/Kernel.lean` (§3.1, with the limits listed
  there); runs of the binaries on hardware are their empirical check.
- **No promise across `clone`** (§6, 44), an argued hardware-fidelity
  claim, not proved: a store program-order after a `clone` never needs to
  be visible before the call. Two facts carry it. (1) No store after an
  `svc`/`syscall` is visible before kernel entry (§9.0, *Certification
  across system calls*, case (a): AArch64 exception entry is context
  synchronising under Linux's `SCTLR_EL1.EIS`, and writes do not
  propagate speculatively; x86-64 `SYSCALL` executes no later instruction
  before the earlier ones complete). (2) A full fence precedes every
  `clone` in `scc`'s output (`Lower.spawn` emits `.fence .full` just
  before `.clone`), which on hardware orders every earlier access before
  every later one, and so excludes the load-buffering and message-passing
  shapes across the call that the dead end removes from the model.
- The loader `T.load`: that the Linux loader maps the executable as its
  program headers say, and that the layout `Λ` read from the executable
  (`Scc.Cert.Elf`) is where it puts the text, the image, the regions (K10,
  K11) and the data symbols (those below the code where `placeBelow` puts
  them), and that it starts the thread at `e_entry`, the start of `.text`;
  that the `.text` sections (`textSection`) are the code and the data
  sections' contents are `Λ.image`; that Kraken's assembly parser, used by
  certificates to re-read the emitted text, agrees with the assembler (GNU
  `as` on x86-64, `clang`'s integrated assembler on AArch64) on the forms
  the emitter uses; and the process entry state
  `Entry.linux` (`Scc/Sem/Target.lean`): the stack pointer at the top of a
  64 KiB zero-filled initial stack in the main thread's private memory, every
  other register zero, nothing else mapped privately. Linux gives at least
  this (the stack holds `argc`/`argv`/`envp`/auxv, which `scc` never reads;
  Linux zeroes the general registers at entry of a static executable,
  beyond what the ELF ABIs require). Not modelled, so outside what `Correct` covers: the
  argument and environment words, the vDSO, a stack larger than 64 KiB.
  The initial stack is disjoint from `Λ`'s regions and in the address
  space: the loaders refuse any other layout (`Entry.clear`,
  `A64.load_clear`, `X64.load_clear`), so a certificate checks it by
  evaluation. It is a loader check, not part of `Layout.WF`, because the
  entry state is the target's, not the layout's.
  The release statement quantifies over every `E` with `Entry.Ok`
  (`Scc/Sem/CorrectE.lean`): a stack inside `2 ^ 64`, disjoint from the code,
  `.rodata` and the data regions, `sp` 16-aligned and below `2 ^ 63`, at
  least 64 KiB; for a layout ending below it, `Entry.linux` is one.
- The ELF layout reader `Scc.Cert.Elf` (evaluated by the elaborator): the
  checks it makes are listed in its module doc; it accepts the linker's
  build-id note, checked as in `Scc.Cert.Elf.buildIdNote`, which is no part
  of the layout, and (`refuseBelowCode := false`) data symbols below the
  code, which `wfB` and the placement check's A2 (`symsAround`, `noClash`)
  then constrain.
- For results transferred through `R` (not for `Correct` itself): WeakCore's
  `CertWinCN`/`CertWinPN` and `storeDepRts = true`, the hypotheses of its
  token-soundness theorems.
- Lean, and `lake env lean` for certificates.

Not trusted: the emitter, the printer, the IR, and the acceptance check beyond
what theorem hypotheses need.

## 5. The bridge spike: plan

**Goal.** For a two-thread, one-access-per-thread program, a proved `R` with
the simulation clause, *including promise certification*, on both targets.
The spike needs no extension: it uses `Target.ofBase` (the base instance)
with the ISA's register and private-memory observations, one file per ISA
(`Scc/Spike/MpA64.lean`, `Scc/Spike/MpX64.lean`).

**Source** (WeakCore, `TermRun.Step` via `SrcSem.ofStep`): label 0 is the
flag, initially `num 0` (memory `#[⟨⟨0, 0⟩, .num 0, 0⟩]`, `lbase := 1`).
Thread 0: `let u = store rel f (lit 1) in ret ()`; thread 1:
`let r = load acq f in ret r`, both with `f = loc ⟨0, 0⟩ 0` in the
environment.

**Targets.** AArch64 (`isaLSE2`, `Arch.armv8`): thread 0 `stlr x1, [x0]`
with `x0 = &flag`, `x1 = 1`; thread 1 `ldar x2, [x0]`. x64 (`isa`,
`Arch.tso`): thread 0 `movq %rsi, (%rdi)`; thread 1 `movq (%rdi), %rax`.
Flag declared as one 8-byte location.

**`R`.** The components of §1.2 with: `thr = id`; `lbl 0 = &flag`,
`lsize 0 = 1`; `ts 0 = 0` and then each new source message to the message the
lockstep step appends; `env`: thread 0 `f ↦ x0`/`rdi`, thread 1 `f ↦ x0`/`rdi`
and, after the load, `r ↦ x2`/`rax`; no stack ranges, nothing marked. Plus
three internal parts: pc ↔ term position (before/after the access); the
promise sets correspond under `ts`; and **views**: every source view of a
thread (`coh`, `vRd`, `vWr`, `vPreBase`, `vRelSt`, `vCtrl`) is at most the
`ts`-preimage of the matching Kraken view (`coh`, `vrOld`/`vrNew`,
`vwOld`/`vwNew`, `vRel`, `vCAP`). The source may be lower: it drops
dependencies (`cst`) and reads a release's message view rather than its
timestamp.

**Steps.** A Kraken instruction step of a memory instruction is one source
step (the `Lower/Events*.lean` lemmas give the Kraken side in closed form:
`instrSemInf_store_iff`, `instrSemInf_load_iff`); a register-only step is a
source stutter (`instrSemInf_done_stutter`).

**How a certified Kraken promise maps to a certified `TermRun` promise.**
Kraken: `PromSemInf A j c c'` appends message `w` (location `ℓ`, value `v`)
and requires `CertOk`: a promise-free solo run `ThreadNP` of thread `j` that
empties its promise set. WeakCore: `Step.prom i a v' wv` appends `⟨a, v', wv⟩`
(`wv < mem.size`) and requires `Certified`: a `Solo` run (promises allowed)
reaching `noPromises`. If `ℓ` is outside every label, the source stutters
(the target promised a runtime word). Otherwise:

1. Take the Kraken certification run `ρ` from the post-promise state.
2. Simulate `ρ` step by step in the source from the *pre-promise* source
   state, with the promised write executed as an ordinary append when `ρ`
   fulfils it. This determines the source write that matches the
   fulfilment: its value `v'` (with `ValRep v' v`) and its message view
   `mview` (`Promises.storeMview`).
3. Make the source promise `⟨a, v', mview⟩`; `mview < mem.size` holds
   because `mview` joins only timestamps of messages that exist at the
   promise point (a later own write would make the Kraken fulfilment fail
   too).
4. Replay the simulation of `ρ` after the promise, now fulfilling at the
   promise's timestamp: `Solo.prom` then `Solo.thread` steps, ending with no
   promises, i.e. `Certified`.

Lockstep `Solo` runs exist because the per-thread part of `R` (thread state,
views, environment) is preserved by solo steps of the related threads
against any memory related by `ts`, with the other threads frozen; this is
the thread-local half of the simulation, proved once.

**The hardest lemma** is step 4's *promise insertion*: inserting the source
promise message at the end of memory does not change the simulation of `ρ`.
Two things must be shown. (a) The promised message hides no message that `ρ`
reads (`WeakMem.hiddenFrom` with the reader's bound): reads in `ρ` are bounded
by views that the view relation keeps below the promise's timestamp until the
fulfilment. (b) The fulfilment's side conditions match: Kraken fulfils at
timestamp `t'` when `t'` exceeds the thread's `coh ℓ`, `vwNew` and `vCAP`
(and, for a release, its read and write views); WeakCore fulfils when
`mview ≤ m.view` and `storeOb < t`. (b) follows from the view relation of
`R` and the monotonicity of `ts`, and it is where any difference between the
two machines' ordering rules for the instruction form shows up.

**Expected breakers** (to be confirmed by the spike and folded into
`WCLowerable`): the emitter obligations of §3 (an RMW's write re-read and
dereferenced: `-AL` RMW or release store + `LDAR`, never `LDAPR`;
`casPair`: `CASPAL` or `DMB ISH; CASP`; pair store: `DMB ISH; STP`), plus
`ldapr` for a source acquire in general (Kraken's RCpc acquire is weaker than
the `ldar` the source acquire corresponds to; emit `ldar`) and 64-bit
`LDP`/`STP` (a pair store cannot fulfil a promise in `TermRun`). At each, the
spike's fulfilment lemma (b) is expected to fail, which is the evidence for
the obligation. The forwarding fixes in the current WeakCore update are the
ones the view relation needs (a read of one's own write); the spike
re-checks them.

## 6. Choices made here

**Provisional decisions (to revisit).** Four decisions are taken for now
and are to be reopened at the trigger given:

- *Never-mirror* (§9.0): no target promise is mirrored by a source
  promise in the one-thread relation. Revisit at the start of M2.
- *Abort budgets by exact runtime counters*, option (c) (§7.3, item 5).
  Revisit once the runtime counters land, before M3.
- *A system call with outstanding promises*: kept as the open hypothesis
  `SvcNoProm` of the AArch64 one-thread theorem. Planned fix: certification
  does not pass an `svc`/`syscall` (`Scc/Sem/Kernel.lean`, `certExec`),
  after a faithfulness check against the Arm exception rules and the x64
  `syscall` (done: §9.0, *Certification across system calls*; faithful on
  x64, on AArch64 only together with a barrier before each `svc` or for
  one thread). Revisit before M3. *Superseded*: certification is now the
  faithful solo projection of the kernel step (§3.1), `SvcNoProm` is gone
  (`Kernel.sys_progress`), and only a `write` keeps a premise,
  `WriteNoProm` (§9, *Open for hello1*).
- *Per-program instance glue*: the first per-node instances of
  `correctA64` (the milestone program `Spike/Gen/ret0.w`, then hello1) take
  the fragment as the hidden invariant of one composed segment (`Seg` with
  `inv ⊆ W`, from the function segments over the block and row data
  `scc --code` and `Spike/Gen` generate), and the ghost own-word map
  (`MemSide.own`) is written by hand in the terms of the segments'
  entry and exit specifications. `scc --cert` for arbitrary programs (M3)
  cannot rely on hand-written glue: the composition and the own map must be
  generated from the call graph and the segment specifications, by a
  symbolic run of the path, not by program order (program order is unsound
  at branches: in `scc_rt_stack_take` the pop path's unlocking store
  precedes the bump path in the text, which would pin the lock to `0` on
  the bump path while it is held). The milestone instance is kept regular
  enough to be the template. Revisit before M3.

1. The statement is over abstract `Target` and `SrcSem` records; `Scc.Config`
   enters through a later `targetOf`.
2. The instruction step is fixed to `StepSemInf` (not a free field), so the
   base instance is the existing machine by construction.
3. Step labels are event lists; `obs` drops `writeErr`, `cloneErr` and `abort`; target
   trace ⊑ source trace by prefix.
4. `Ev.exit` carries the code modulo 256 on both sides; bytes on fd 2 are not
   events.
5. `Outcome.halted` exists for the base machine's termination; the extended
   machine makes it a fault for `scc` programs.
6. Progress: every live thread steps or waits; plus `InLayout` (shared writes
   only in `.data` or the heap).
7. Abort clause (§1.2, 4): per kind (`AbortJustified`); the justifying
   source step is a step of the source thread mapped to the aborting target
   thread; `writeErr` is justified by an earlier `Ev.writeErr` event (a
   refused write is an event, not an observation); source thread cap
   `B.threads + 1`.
8. Budget in source units (cells, threads, frames, 64-bit numbers); the
   target's limits are layout facts derived from it.
9. `ValRep` with pointer tags (`+ tag`, `tag < 8`) and word offsets.
10. Memory relation by a total, order-preserving timestamp map; allocation
    `undef` and buffer zero messages map to the target's initial write
    (needs the zeroed arena and no reuse under `gc none`).
11. Environment map partial, per frame depth, first binding per frame.
12. Stack-map clause as six conditions (§1.2, 5).
13. No runtime-only threads (`thr_onto`).
14. Route S formalised as `ImageMatches` with `Layout.static`.
15. `Sim` carries `Λ.WF`; `Sim.sim` relates to any reachable source state.
16. Dormant thread slots; child register views 0.
17. System calls are not fences; certification passes them through an
    over-approximating havoc semantics (§2.2).
18. Futex with spurious returns, no wait queue.
19. Stack pool without reuse at first (amended by 42: reuse through the
    pool is modelled).
20. Thread pointer without a dependency view.
21. `Layout.abortLbl k`, one abort stub per kind, classifies the abort exit
    by label (resolved by the target, `Target.resolve`), not by numeric pc; stubs at distinct
    labels.
22. No atomicity of a `write` call: one `out` per step, interleaving with
    other threads (K3); a step emits at most one event.
23. `main`'s return as the exit event: the returned number modulo 256, 0 for
    any other result (`mainExit`); a source step's events are the growth of
    the observable trace (`ofStepsG`).
24. Source steps are thread-indexed (`SrcSem.step i`; `StepBy`, `SpawnBy`
    expose the thread of a `TermRun.Step` / `Spawn`); runs quantify over
    the thread.
25. `AbortKind` is carried by the `abort` event and outcome.
26. No overflow check is elided (see §1.2, 4).
27. Budget parts are crossed, not merely exceeded (`AbortJustified`); the
    overflow part is per thread (`NoBigNumT i`).
28. Heap use counts allocated words (`cellCount`, valid because every
    allocation pushes one message per word) plus one header word per
    allocation (`allocCount`); a single `B.cells` bounds both.
29. `B` is the producer's choice and is published with each program (§1).
30. `Correct` is meaningful only for the canonical `Target` per ISA (§1).
31. Stack-pool metadata lives in `Λ.heap`/`Λ.data`, not in the pool (§2.6).
32. No `waiting` field: with spurious futex returns (K7) a wait can always
    step, and a free `waiting` would discharge progress.
33. Known looseness: the justifying source step is not tied to the aborting
    instruction (§1.2, 4).
34. Canonical targets as `ExtMachine.ofHooks` with a `Hooks` record of
    everything Kraken lacks (§7.1); `canonical` uses `Hooks.none`
    (amended by 40: the kernel model's hooks). Asm is
    assembly text through Kraken's parser; one thread at `Λ.code.lo`, entry
    at the first instruction, zero registers, empty private memory, the
    image as initial memory. (Amended by 37: the entry state is `Entry`.)
35. `regVal` of flags in architectural positions (`NZCV` bits 31–28;
    `RFLAGS` CF/PF/AF/ZF/SF/OF); x64 vector registers by their low 64 bits.
36. `Layout.symbols`: data symbol addresses by assembler name, a new field of
    the statement's `Layout` (`static` is keyed by source labels and cannot
    place runtime symbols such as the heap arena or the stack pool). The
    loader puts a label cell for each symbol below the code before it
    (`placeBelow`, the executable starting at the lowest, `exeStart`) and
    for each other one after the code (`placeSyms`), and refuses a text
    with a symbol inside its code `[lo, fin)` (`symsAbove`). `Layout.WF`
    constrains them (§1.1: in a data region, below or above the code,
    distinct names); a lemma `symsAbove_of_wf` (WF and the
    model code within `Λ.code` give the check) belongs next to `symsAbove`
    in `Target.lean`, not added here while the sized loader changes it.
37. The entry state is a parameter of the loader (`Entry`), fixed for the
    canonical targets to `Entry.linux`: the stack pointer at the top of a
    64 KiB zero-filled private stack, every other register zero (§4).
38. The loader reads only the `.text` sections of the text (`textSection`);
    the data sections' bytes are `Λ.image`, which a certificate must check
    against the text's `.byte`/`.zero` directives.
39. x64 code addresses: the model keeps Kraken's one byte per instruction;
    abort classification and the `xfer` gate are by label (`Λ.abortLbl`,
    `XferKind.label`, resolved in the model layout), so no clause depends on real
    code addresses (§7.2).
40. The canonical targets' hooks are the kernel model `Kernel.hooks`
    (`Scc/Sem/Kernel.lean`, §3.1) with `CertCfg.slots` dormant-slot
    thread slots; the choices of §3.1 (`write` read granularity, no futex
    load, view 0 for kernel results, promise-free system calls, any `svc`
    immediate, `rt_sigaction` and `arch_prctl` supported because the
    runtime's start-up issues them) are made there.
41. The thread slots are a field of the certificate's configuration
    (`CertCfg.slots`), tied to the budget by `CertCfg.WF.slotsEq`
    (`B.threads + 1`); the canonical target is a function of it. A `clone`
    with no dormant slot is a fault, not `-EAGAIN` (§3.1, *Thread slots*).
    (Amended by 42 for stack ranges.)
42. Stack ranges move only at two forced, deterministic transfer sites with
    fixed labels (`XferKind.label`: `scc_rt_take_site`,
    `scc_rt_release_site`; `Layout.growLbl` is gone), where the instruction
    step is disabled and the range is the one in the first two argument
    registers; a bad site leaves the thread stuck. Released ranges return
    to the pool with their bytes (`KState.pmem`) and may be taken again;
    `clone` moves the parent's range ending at the child's stack. A refused
    `clone` is `Ev.cloneErr` (K6c), which justifies a `threads` abort like
    `writeErr` justifies a `writeErr` abort (§1.2, 4).
43. K11 is part of the kernel model: an instruction that may access a
    shared location outside the mapped regions (`.data`, heap, pool,
    initial stack read-write; code read-only) is a fault (`unmappedAt`), so
    progress excludes `SIGSEGV`. The initial stack's disjointness from the
    layout is a loader check (`Entry.clear`), not a `Layout.WF` field.
44. `clone` is a certification dead end (`Kernel.soloExec`: no branch at
    `clone`, neither the child ids nor the refusals), not a disabled step:
    the kernel step and `Progress` are unchanged, and a thread with an
    outstanding promise at a `clone` cannot certify, so no promise is
    outstanding across one. This is an **explicit exception to the design
    invariant "exact first step, never under-approximate later"** (the
    certification semantics is the faithful solo projection of the kernel
    step, Decision 11/12): at `clone` the projection under-approximates on
    purpose. Justification: the hardware-fidelity claim of §4 (*No promise
    across `clone`*), that is, no post-call store is visible before kernel
    entry, and a full fence precedes every `clone` in `scc`'s output. What
    it buys: `soloExec` no longer reads the thread's own held ranges
    (`soloHeld none` was read only at `clone`), which is the congruence the
    certification lift after a take needs, and the spawn handover starts
    with no outstanding promise. The fallback, should the claim fail, is
    to relax WeakCore's `Spawn` instead. Checked: a store after `clone` is
    promisable with nothing, after `futex` wake with every count
    (`Spike/Test/{A64,X64}CloneCert.lean`); the take-mark promise sets of
    `ret0`/`hello1` (AArch64 six writes, x64 one), the `OwnDom` runs and
    the litmus corpora (`aarch64` 52/52, `x86_64` 28/28) are unchanged.

## 7. Open points for WeakCore

1. **`ThreadId`.** `TermSpawnStep.spawnCfg` binds the child's id as
   `num ths.size`, an index. The runtime's `ThreadId` is a control-block
   address, so `ValRep (num i) v` would be false for it. `R` cannot cover
   thread-id values until `ThreadId` is a reference value (as WeakCore
   decided); until then they must stay out of the environment map.
2. The extern step and trace as designed upstream (`Ext` beside `Spawn`,
   append-only `Cfg.trace`, behaviours cut at the first `exit` or at `main`'s
   return) are what `ofStepsG`/`srcObs` abstract, through the hook
   `SrcHooks` of `SrcSem.source`. To confirm: the exit code of
   `main`'s return (here: the returned number modulo 256, else 0), and that
   `out b` always has `b < 256` (here reduced modulo 256). Needed for P9
   with the extern step (`srcObs_mono`): no event after `main` has returned
   (the process exits then); otherwise another thread's `out` would land
   after `main`'s exit in `srcObs` and the trace would not only grow.
   Applied: no source step once thread 0 has finished (below, 2a).

2a. **Applied: every source step is gated on `main` not having returned.**
   `SrcSem.source P p` is `sourceG P p` (the former `ofStepsG` instance)
   with step `mainExit c = [] ∧ (sourceG P p).step i c es c'`. The gate is
   on configurations and excludes no program, so `scc` checks nothing for
   it. Consequences:
   - `source_run_sourceG`, `source_run_stepsG`: a gated step is an ungated
     one, so runs are still WeakCore's `StepsG` runs (`Sim.transfer_source`).
   - P9 for every hook whose event list only grows along steps:
     `source_obs_mono` and `source_run_trace` take `hgrow` in place of
     `P.hooks = SrcHooks.none` (`grow_none` discharges it for
     `SrcHooks.none`). From a configuration with `mainExit c = []`,
     `srcObs c = cutAtExit (tr c)` is a prefix of
     `cutAtExit (tr c' ++ mainExit c')` by `cutAtExit_append`.
   - `source_mainDoneNoProm`, `source_mainExit_noProm`: not for every hook.
     The gate only stops steps from a configuration where `main` has
     returned; an extern step from one where it has not could finish
     thread 0 with outstanding promises, since `SrcHooks.ext` is an
     arbitrary relation. They take `hext` (an extern step from a
     configuration where `main` has not returned keeps `MainDoneNoProm`;
     `ext_none` for `SrcHooks.none`). WeakCore's extern step, a certified
     thread step, should satisfy it.
   - `threads_abort_unjustified`: unchanged with `SrcHooks.none` (the gate
     is one more conjunct). For a general hook it needs extern steps to keep
     the thread count.
   - `AbortJustified` asks for a source step of thread `i`. After `main`
     has returned there is none, so no abort is justified after the exit,
     which is right: the target has exited as well.
   - Rejected example `Holes.not_correct_event_after_exit`: a target with an
     event after its exit is not `Correct` for any program and any growing
     hook; without the gate, a hook emitting after `main`'s return gives the
     source that trace (`[exit 0, exit 0]`).
3. Stability of `Certified`/`Solo` and `Promises.stepStore`'s fulfilment
   conditions, on which §5 depends.
4. Source frames do not record their function, so the stack budget counts
   frames, not bytes.
4a. **Live labels.** The memory clauses cover `Live s`
   (`Reach s (RootLabel s)`, §1.2, 5): roots are the words of the variables
   `frameFv` keeps, closed under references in any message to a reachable
   label. WeakCore's planned ghost reachability should match this shape, or
   be shown equivalent. Needed from WeakCore: dead stays dead along solo
   runs (certification excludes a promise of a reference to a dead label,
   `dead_promise`), and the thread-step case of `Reach.step`. Once a
   `ThreadId` is a reference, control blocks become roots.
5. The `pairs` field of `TermRun.Cfg` (16-byte accesses) is related by `R`
   only through `ts_mono` and `wordAt` (a pair may map to one 16-byte target
   message). No proved hole exercises a store pair yet.

### 7.1 Kraken hooks the canonical targets need

`Scc/Sem/TargetA64.lean` and `Scc/Sem/TargetX64.lean` define the canonical
targets from Kraken's thread states, instruction semantics (`isaLSE2` under
`Arch.armv8`, `X64.isa` under `Arch.tso`) and parsers
(`Kraken.AArch64.Parser.parse`, `Kraken.X64.Parser.parse`), with the hooks
of `Hooks` (`Scc/Sem/Target.lean`) set by the kernel model
(`Kernel.hooks`, `Scc/Sem/Kernel.lean`, §3.1). Kraken now has `svc`,
`mrs`/`msr` of `TPIDR_EL0`, `syscall`, `%fs:` moves with `Reg64s.fsBase`,
and `ud2` (`Kraken/SYSCALL.md`); a system call halts Kraken's step with a
fault (`MachineData.pendingSyscall`), and the hooks take the thread's step
there. Status of each hook:

1. **System-call instruction** (`Hooks.atSys`, `Hooks.sys`): implemented.
   `atSys` is `A64.atSvc` / `X64.atSyscall` (the directive at the pc);
   `sys` is `Kernel.sysStep` (§3 K1–K5, K7–K9) through
   `Config.withThread`, with `Ev.out`/`Ev.writeErr`/`Ev.exit`/`Ev.abort k`
   events; that the pc is at the address of `Λ.abortLbl k` for `Ev.abort k`
   (and at none of them for `Ev.exit`) is required by `Step.sys`.
   `ExtMachine.ofHooks` counts a faulting Kraken step as a fault only for a
   running thread not at a system call (`ofHooks_none_fault_iff`: no change
   without hooks). Certification passes system calls through
   `Hooks.cexec` (`Kernel.certExec`, §3.1, *Promises at a system call*).
   Open (in Kraken): `Directive.deps` of `svc`/`syscall`.
2. **Thread creation** (`Hooks.spawn`): implemented with dormant slots
   (§2.1). The loader lays out `Hooks.slots` slots (`dormantAt`: halted, no
   private memory); `Kernel.KState.slots` records dormant, running and
   exited slots, read by `runs`/`live` through `Hooks.threadDone`; `clone`
   is `Kernel.spawnStep`, activating a slot at the parent's views (K6a),
   optionally with the parent's held range ending at the child's stack
   (§2.6), or refused with `Ev.cloneErr` (K6c). The slot count
   is the certificate's (`CertCfg.slots`); a `clone` with none dormant is a
   fault (`Kernel.fault_clone_full`).
3. **Thread pointer** (`Hooks.threadPtr`): implemented, `Abi.tp`
   (`TPIDR_EL0` / `fsBase`); set by `clone` (`CLONE_SETTLS`), by `msr`
   (Kraken's step) and on x64 by `arch_prctl(ARCH_SET_FS)` (K9).
4. **Range transfer** (`Hooks.xfer k`): implemented, `Kernel.xferStep`:
   `takeStep` / `releaseStep` at the site of kind `k`
   (`ExtMachine.AtSite` on the address `Target.marks` resolves from
   `XferKind.label k`, with the canonical `pc`: `A64.pcOf`, `X64.pcOf`),
   moving the range of `Kernel.siteRange` between `KState.pmem` and `dmem`
   (`copyRange`, `eraseRange`, through `Abi.setDmem`) and past the `nop`
   (`Abi.atNop`, `Abi.skip`); no Kraken change (§2.6). Open: a lemma that
   `privLoad` sees exactly the held ranges.
5. **Exit records** (`Hooks.exited`, `Hooks.threadDone`): implemented,
   written by the `exit`/`exit_group` cases of `sysStep` into
   `Kernel.KState`.
6. **Futex blocking**: none needed; with the spurious-return futex model
   (K7) a wait can always step, so there is no `waiting` hook.
7. **Extension faults** (`Hooks.fault`): implemented, `Kernel.faultAt`:
   unsupported system calls or arguments (K1), `clone` with no dormant slot
   (K6b), and a running thread that has halted (run off its code); and
   `Kernel.unmappedAt` (K11): an instruction that may access a shared
   location outside the mapped regions (`Hooks.init` takes the entry state
   for the initial stack).
8. **Stack ranges** (`Hooks.stackRange`): implemented,
   `Kernel.stackRangeOf`, the held range (`KState.held`) the thread's `sp`
   is on (§2.6).
9. **Loader** (`threadAt`, `loadProg`, `target`). Not hooks. Resolved:
   data symbols are placed as label cells at their `Λ.symbols` addresses,
   before the code for those below it (`placeBelow`) and after it for the
   others (`placeSyms`; x64 as `X64.mkState`'s `syms`), so
   x64 `leaq sym(%rip)` and AArch64 `adrp` + `add :lo12:` give the symbol's
   address and a load from it reads the image word (`#guard_msgs` tests
   `dataRef` in both target files); the entry state is `Entry` (§4; tests
   `entryStack`). Remaining gaps: the image is 8-byte words (`Loc ⟨a, 8⟩`),
   so a narrower or unaligned load of a non-zero `.data` byte reads 0 in
   the model (Kraken's memory has no mixed-size accesses; `.bss` and zero
   bytes are exact, since unwritten memory reads 0); `argv`/`envp`/auxv are
   not modelled; x64 code addresses (§7.2).

Sanity (proved, `Scc/Sem/Target.lean`): with no hooks and no transfer site
resolved, a step of the target is exactly a step of Kraken's existing
machine (`ofHooks_none_step_iff`), and a fault exactly a faulting step
(`ofHooks_none_fault_iff`);
at a no-event instruction away from the transfer sites Kraken's
single-thread step is a step of the target (`ofHooks_step_of_done`,
`A64.step_of_done`, `X64.step_of_done`) and every instruction step agrees
with it (`ofHooks_instr_done`); a straight-line run of Kraken's
single-thread step from a loaded program that never reaches a site is a
run of the target (`A64.run_of_seqRun`, `X64.run_of_seqRun`). A concrete
two-instruction program per ISA is checked by `#guard_msgs` (the target's
steps and Kraken's single-thread step give the same registers and pcs); a
kernel `decide` on it does not reduce (`Executable.withAddresses` is defined
by well-founded recursion). Kernel model (`Scc/Sem/Kernel.lean`): an unsupported call is a
fault (`Kernel.fault_of_unsupported`; per ISA `A64.unsupported_fault`,
`X64.unsupported_fault` for an unknown number), `exit_group` ends the
process (`Kernel.sys_exitGroup`), a `write` transfers one byte per step
and returns the count (`Kernel.sys_writeByte`, `Kernel.sys_writeRet`),
`clone` activates a dormant slot (`Kernel.spawn_clone`), optionally with
the child's stack range (`Kernel.spawn_clone_stack`), and faults with every
slot used (`Kernel.fault_clone_full`), may be refused with `cloneErr`
(`Kernel.sys_cloneErr`); a transfer is deterministic (`Kernel.xfer_det`),
a take moves the register-given fresh range (`Kernel.xfer_take`), and at a
take site the only step is that take, with no instruction step and no
event (`Kernel.step_at_take`, `A64.take_forced`, `X64.take_forced`: the
regression lemma for forced sites); the bytes of a range survive a release
and a later take (`Kernel.take_bytes`, `release_bytes`,
`release_take_handoff`). Per ISA a
`#guard_msgs` check runs `write(1, buf, 1); exit_group(0)` from the loaded
program to the trace `[out 42, exit 0]`, shows the `-EINTR` and refusal
answers, an unknown number faulting, a refused `clone`, `clone` with and
without a child range (the child getting the range taken in the parent at
the take site, the fault with every slot used), growth with reuse (take,
take, release, re-take of the first range, its stored word read back
privately with no shared message), a release while on the range and a
second take of a held range both stuck. An access outside the mapped
regions is a fault (`Kernel.fault_of_unmapped`, `Kernel.unmappedAt_of_root`;
per ISA `unmapped_fault`), checked per ISA on loads and stores to each
region, past the heap and far outside; a loaded layout is clear of the
initial stack (`load_clear`), and a layout that meets it is refused.

### 7.2 x64 code addresses in the model

The x64 loader lays the code out at the sizes GNU `as` gives each
instruction (*The sized loader*, below), so a model code address is the
assembled one (relative to `Λ.code.lo`). Before it, Kraken's unit layout
(`X64.mkState`) gave every instruction one byte, and model addresses were
`Λ.code.lo` plus the number of instructions before. The items below list
every place `scc`'s x64 output (the emitter and runtime of the compiler,
read from their sources) depends on code addresses or sizes, and why each
was harmless under the unit layout, except item 5:

1. **Branch targets** (`jmp L`, `jcc L`, `call f`). The parser resolves `L`
   to the model address of its label cell; the branch goes to the same
   instruction as in the binary. Harmless.
2. **Return addresses.** `call` pushes the address after itself (model:
   `pc + 1`), `ret` pops it and jumps there: the same instruction. Return
   addresses live only in the calling thread's frames (on the initial stack
   or its pool stack); they are not stored elsewhere or written to shared
   memory. A thread's pool stack is private to it (moved into its private
   memory, §2.6), so the different numbers are invisible to other threads
   and to events; the bytes stored there differ from the binary's, but no
   clause of `Correct` constrains the contents of stacks (they are not
   source memory). Harmless, except that stack growth compares them with
   the stack map (item 5).
3. **`_start` and thread entry.** `_start` is `xorl %ebp, %ebp; andq $-16,
   %rsp; call <start>; ud2`; a child created by `clone` runs `call
   <entry>`; a thread switch is `call f`. All direct calls, as 1 and 2.
4. **Rip-relative references** (`leaq sym(%rip)`, the `la` of the emitter).
   All are to data symbols (heap and stack-pool cursors, the arena, the pool,
   the abort messages); the parser sets the displacement to `sym − next pc`
   and the effective address is `sym` exactly, whatever the instruction
   sizes. No rip-relative reference to code. Harmless.
5. **Jump tables, indirect calls and jumps, code pointers in data.** No
   jump table or indirect call: the only indirect control transfer is
   `ret`; the thread control block (`%fs`) holds no code address. But the
   stack map `scc_stackmap` (in `.rodata`) is a table of return addresses
   (`.quad` of code labels), which stack growth (`scc_rt_grow`, reached from
   `scc_rt_morestack`) compares with the return addresses in the frames it
   walks. On the model these agree only if the image holds the *model*
   addresses of those labels, which differ from the linked binary's on x64:
   `Λ.image` is then not the binary's `.rodata`. Resolved by the sized
   loader below: the table's words are the assembled addresses, and
   `raCheck` (`Scc/Sem/Test/RunX64.lean`) reads a frame's return address and
   the table's entry for its call site from model memory and finds them
   equal.
6. **Code size.** Under the sized loader the model code is exactly as long
   as the binary's `.text`; `symsAbove` holds whenever the linker put the
   data after the text. Neither loader checks that the code fits in
   `Λ.code` (the kernel tests use a short `Λ.code`); `Layout.WF` and the
   entry checks (`Entry.clear`) are what the statement relies on.
7. **Abort classification and the transfer sites.** Both are by label:
   `Λ.abortLbl k` and `XferKind.label k`, resolved by the target in the loaded
   program (`Target.resolve`; the canonical targets give a label the model
   address of the instruction after it, `labelAddr`, checked against the
   model pc by a `#guard` per ISA), and gathered by `Target.marks` into the
   `Marks` that `Step` takes. So no clause depends on instruction sizes, and
   `Λ` holds no numeric code address. (With the earlier numeric `abortPc k`
   and growth range, the binary's addresses, the model pc of the same
   instruction was smaller on x64: the abort exit would have been reported
   as `exit 101` and no range transfer could have been taken.) The site
   `nop`s have one model address each, whatever their size.

**The sized loader** (`Scc/Sem/TargetX64.lean`). No Kraken change was
needed: Kraken's executable is a list of `(directive, size)` cells, and
`Kraken.Promising.X64Sized` lays a program out at a size table
(`sizedCells`) and checks one (`SizeCheck`).

- `Target.Asm := Scc.Sem.X64.Asm`: the text, the byte size of each
  instruction of its `.text` sections in text order (`sizes`; an alignment
  directive is a `nopalign` cell whose size is its padding), and the
  offsets of its labels in `.text` (`labelOffs`).
- `load` lays the parsed program out with `sizedCells` (`cellsOf`) and
  refuses unless `SizeCheck (Λ.code.lo) cells labelOffs` holds (positive
  sizes, empty labels, aligned `nopalign`s, no wrap, every listed label at
  its listed offset); `threadAt`, `codeEnd` and `resolve` (`codeLabel`) use
  the same cells.
- `scc --cert` (x64) assembles the text with GNU `as`, reads the sizes and
  label offsets off the object file (`Scc/Cert/Sizes.lean`: `objdump -d`,
  `-h`, `-t`), and writes them into the certificate with `sizes_ok :
  Scc.Cert.X64.sizesOk 0 prog sizes labelOffs = true`. The kernel checks
  the linear `sizesOkFast` (`decide +kernel`, about 10 s for `hello.w`),
  which implies `sizesOk` (`sizesOk_of_fast`); `SizeCheck` itself is
  quadratic in the kernel (over 20 minutes). The check is at base 0: the
  emitter puts no alignment directive in the x64 text, so the table checks
  at any base, and the loader re-checks it at `Λ.code.lo`.
- §4 trusts the sizes to be `as`'s: the check shows them consistent with
  the parsed program and the label offsets, not that they are the
  binary's. Model and binary addresses then agree, return addresses
  included.

AArch64 needs none of this: every instruction is 4 bytes in Kraken and in
the binary (the text's alignment directives, `.p2align 4` at the start of
`.text` and `.p2align 2` before each function, pad nothing; the
`.p2align 4` makes `.text` 16-aligned in the object file, so `ld.lld`
starts the code on the 16-byte boundary `wfB` requires whatever `.rodata`
below it ends on); its loader keeps Kraken's 4-byte layout.

**`.rodata`** (both ISAs). The loader reads the text's data sections
(`Scc.Sem.dataSections`) and builds the `.rodata` image itself
(`rodataWords`: `Kraken.DataImage` laid out from `Λ.rodata.lo`, `.quad`s of
code labels resolved to their model addresses), refusing unless the image
fits in `Λ.rodata` (`rodataFits`), every `.rodata` symbol that `Λ.symbols`
lists is at the image's address for it (`symsAgree`), and every code label
resolves (`quadsResolve`). `Λ.rodata` is a `Layout` field (default empty),
outside `Layout.regions`, so `Layout.WF` and every proof about it are
unchanged; the kernel model's read-only ranges are `Λ.code` and
`Λ.rodata` (`KState.init`). The image is shared memory (initial words of
the promising memory, like `Λ.image`), not thread-private `dmem`: a thread
`clone` creates starts with an empty `dmem`, so a private image would be
invisible to spawned threads, and `dmem` is writable; read-only-ness comes
from the kernel's `ro` ranges (a store to them faults, K11).

### 7.3 Statement and runtime: points to settle

The compiler's runtime and emitter (read from their sources) and `Correct`
are compared here; neither is changed here. Items 1 and 2 are resolved in
the runtime, 4 in the emitter, 5 is decided; 3 remains, with the thread cap (§3.1,
*Thread slots*). The transfer sites (§2.6, *Runtime and emitter
obligations*) are labelled in the runtime (§7.4, item 1).

1. **One abort exit** (resolved). The runtime's abort stub of each kind
   writes the kind's message to fd 2 and issues its own `exit_group(101)`,
   so each kind has one `exit_group` site, as `Λ.abortLbl k` asks, labelled
   `scc_rt_abort_<kind>_exit` (§7.4, item 2).
2. **No `threads` kind** (resolved). The runtime's kinds are `overflow`,
   `heap`, `stack`, `write` and `threads`; `threads` reports a failed
   control-block allocation and a failed `clone`. The runtime's `write` is
   the statement's `writeErr`. The `heap` message still reads "out of heap
   or threads". Control blocks now have their own region (`Λ.pinned`,
   `scc_rt_pinned`, sized for the thread cap) and cursor, so a spawn no
   longer consumes the arena: pinned-region exhaustion is a `threads`
   abort, arena exhaustion a `heap` abort.
3. **Regions in `.bss`.** The arena (`heap`), the pinned region
   (`pinned`) and the stack pool (`stacks`) are `.bss` symbols, so
   `Λ.heap`, `Λ.pinned` and `Λ.stackPool` are those symbols'
   ranges carved out of the `.bss`, and `Λ.data` the rest of `.data`/`.bss`
   (`Layout.WF` asks 16-alignment, which their `.balign 16` gives, and
   disjointness). The cursors (`heapNext`, `stackNext`) are in the data, as
   choice 31 says.
4. **System-call forms in the text** (resolved in the emitter). Both
   emitters now print no raw lines: AArch64 `svc`, `mrs`/`msr` of
   `TPIDR_EL0` and the x64 `syscall`, `ud2` and `%fs:` moves are Kraken
   directives, and the x64 `cmpq %fs:…` (which Kraken rejects: only `mov`
   takes a `%fs:` operand) became a `mov` and a `cmp`.

5. **Abort budgets: exact crossings** (decided: (c); to be implemented,
   it may be revisited). `AbortJustified` asks a budget abort to be an
   exact crossing: the part (`Budget.Part`) holds at the source
   configuration and fails after thread `i`'s step (`part_before`). The
   runtime's thresholds do not line up with the parts:
   - *Heap*: `scc_rt_alloc` bumps the arena cursor by the object's bytes
     and aborts when it passes the arena's end (or on a huge length);
     `arena_covers` bounds the target bytes by `16 · heapUse` only, so the
     source can cross `B.cells` while the target runs on (a later abort is
     unjustified), and an abort before the crossing is unjustified too.
   - *Stack*: the pool is shared by all threads, while `Part .stack` is
     per thread (frames); a thread can run out because of the others, and
     its limit check counts bytes, not frames.
   - *Threads*: the pinned area's capacity must be exactly `B.threads`
     control blocks; otherwise only `cloneErr` justifies the abort.

   The options:
   - **(a) Target-sized parts.** The heap part counts runtime bytes per
     allocation (the per-label target size), the stack part frame bytes
     per thread with the pool at least `(B.threads + 1)` caps, the
     threads part the pinned capacity. Changes `Budget` and needs each
     allocation's target size in the source (the blocker at `allocCount`).
     *Fallback* if the runtime cannot count in source units.
   - **(b) Weaker `AbortJustified` for global parts**: the part fails at
     `s` or after the step. Smallest change, but it drops the
     not-inherited property (`part_before` and its Holes example would be
     restated). *Fallback* only if the statement may be weakened.
   - **(c) Exact runtime counters in source units (chosen).** The runtime
     counts `heapUse` words globally and frames per thread, and aborts
     exactly when a count passes `B.cells` / `B.frames`; the pinned area
     holds exactly `B.threads` control blocks. `Correct` is unchanged.
     Chosen because it keeps the statement as strong as it is; the cost is
     a counter update per allocation and per call at run time.

   The plan for (c):
   - *Heap.* A global counter `scc_rt_heap_use`; `scc_rt_alloc` takes the
     allocation's source units `u` (its words plus one header) and adds
     them atomically, `old ← rmw add u`. It aborts exactly when
     `old ≤ B.cells < old + u`, the crossing. `B.cells` is derived from
     the layout, `heapBytes / 16`, so the arena check is unreachable while
     the part holds (`arena_covers`).
   - *Heap, settled shape.* The counter **is** the arena cursor, with a
     stride of 16 bytes per unit: an allocation whose `rmw add` returns
     `old` owns the bytes from `s = heap + 16 · old`, and there is no
     separate byte cursor (the former `scc_rt_heap_next` is dropped). The
     allocation is linearised at that `rmw` (x64 `lock xadd`, AArch64
     `ldadd`); its label is placed at `base = s + 8 · k · m + 8`, the
     header word at `base − 8` (`alloc_placed`). `heapBytes = 16 · B.cells`
     exactly: the lowering refuses `heapBytes % 16 ≠ 0` and checks
     statically, per allocated type, that an object's target words fit its
     slot (`n + m ≤ 2 · words`). The runtime's shape: the length check
     (`k ≥ 2^lenBits` aborts), then `old ← rmw add u`; if
     `old + u ≤ B.cells`, store the header and return `base`; otherwise, if
     `old > B.cells`, spin (another thread crossed), else the `heap` abort
     (this thread crossed). The invariant the proof keeps: the counter is
     `Σ u` over the linearised allocations, the source `heapUse`.
     *Cost*, to weigh in the abort-budget revisit: a scalar-only object
     takes a 16-byte slot per unit, twice its words.
     *Overflow*: the counter stays below `B.cells + (threads + 1) · umax`
     (each thread adds at most one `u` past the crossing, then spins or
     aborts), which must be below `2^64`. The lowering checks it for the
     program's largest `u` and the thread cap; the runtime proof takes it
     as an assumption, not a `Layout.WF` field.
     *Counter invariant* (`Scc/Sem/HeapCtr.lean`, `HeapCtr1`): with one
     thread, the counter is `heapUse` plus the units of the pending
     allocation, if any. An allocation is pending from its `rmw` with
     `old + u > cells` to `full`'s exit, the abort step that simulates its
     source step. A pending allocation's `old` is the heap use, so `slow`
     goes to `full` and `spin` is unreachable. *Several threads* (M2): the
     pending allocations form a list; the oldest one's `old` is `heapUse`,
     and each newer one's `old` is at least the previous one's `old + u`.
     So only the oldest (the crossing thread) has `old ≤ cells` and
     aborts, the others spin, and the counter stays below
     `cells + (threads + 1) · umax`.
   - *Stack.* A per-thread depth in the control block, changed only
     around source non-tail calls (`let x = f(a)`, `callc`; not tail calls,
     not runtime calls): `depth + 1 > B.frames` aborts, else the call runs
     between `depth += 1` and `depth −= 1`. `B.frames` is derived from the
     stack cap and the largest frame, so the pool and cap checks are
     unreachable within the part.
     *Settled shape*: the word `Tcb.depth` (offset 64), read and written
     only by its thread, zero in the fresh control block (no store); the
     caller brackets a call of a user block (not an extern or runtime
     call; `callc` is refused by the frontend): load `d`, `d + 1 > F`
     aborts, store `d + 1`, call, store `d` back (`d` kept in a frame
     slot). `F` is an immediate, the program's `{p}Frames` in the code
     file, and the certificate's `B.frames`.
     *Counter invariant* (`Scc/Sem/StackCtr.lean`, `StackCtr1`): with one
     thread, the counter is the number of user-block frames on the source
     stack, within `F`, but one ahead between the store of `d + 1` and the
     `call` (the source push) and between the callee's `ret` (the source
     pop) and the restore. The branch is the source budget (`branch`:
     `d + 1 > F` exactly when the depth is `F`), so the abort is justified
     by the call's push (`abort_justified`, `stack_of_push`). Inside an
     extern call's window the source stack has one frame more than the
     depth (the extern's model body), which justifies nothing the target
     does there. *Own word* (`Scc/Sem/OwnWord.lean`, `Inv1.rtLoad_own`):
     a load of a word only the thread writes returns its last write, or
     the initial value; Kraken's read rule never offers the thread's own
     unfulfilled promise, so under the cover a promise to the word (which
     certification allows) needs no exclusion. The word's value is kept
     by every instruction not writing it (`stepOne_own`) and set by a
     store (`stepOne_store_own`) or kept by a promise (`own_promise`).
     Open on the consumer side: threading `OwnVal` of the depth word
     through the rows, and a per-frame ghost keeping the caller's saved
     `d` across the call.
   - *Threads.* `B.threads = maxThreads + 1` (the main thread counts); the
     abort is at the reservation `i = maxThreads + 1`, after earlier
     reservations' `clone`s complete (a counter of successful spawns), so
     the source count is the target's. M2: no M1 program spawns.
   - *Spin after crossing.* A thread whose counter update finds the part
     already crossed by another thread (`old > B.cells`; a reservation
     past `maxThreads + 1`) does not abort, since that abort would be
     inherited, not justified (`part_before`); it waits. The crossing
     thread's `exit_group` ends the process, so the wait is bounded by it.
   - *Zero-word buffers* (fragment limit, M2). A `newBuf` of a zero-word
     element type allocates one header for any length, and the runtime's
     length check (`k ≥ 2^lenBits`) is then no crossing of the heap part.
     `scc --code` refuses such a `newBuf` (as it refuses 32-bit accesses);
     lifting the limit is an M2 item.

### 7.4 Emitted programs on the canonical targets

`Scc/Sem/Test/RunA64.lean` and `Scc/Sem/Test/RunX64.lean` (test only;
the driver is `Scc/Sem/Test/Run.lean`) load the text `scc -S` prints for
`Scc/Test/hello.w` and `Scc/Test/handoff.w`, embedded with the command and
the sha256 of its output, on `target (kernel 2) Entry.linux` and run it.

- **Layout.** A model of a static link: code at `0x400000`, the data
  sections laid out from `0x600000` (`.balign`, `.p2align`, labels,
  `.zero`, `.byte`, `.quad` of numbers or code labels), the arena
  (`scc_rt_heap`) at `0x1000000`, the pinned region (`scc_rt_pinned`) at
  `0x8000000` and the pool (`scc_rt_stacks`) at `0x10000000` with their
  `.zero` sizes; the data symbols as `Λ.symbols`, the non-zero bytes as
  `Λ.image`, `scc_rt_abort_<kind>_exit` as `Λ.abortLbl`. `.rodata` is at
  `0x500000` (`Λ.rodata`): its symbols are listed in `Λ.symbols`, and the
  loader builds its image (§7.2, *`.rodata`*). Code labels in data (the
  stack map) get their model addresses. On x64 the code is laid out at the
  sizes `as` gives (embedded next to the text, `helloSizes`).
- **Scheduler.** Deterministic: running threads take turns, one step each;
  an instruction takes Kraken's last successor (for a load, the newest
  write it may read, so spin loops progress); a system call takes the
  kernel model's first useful answer (`write` transfers every byte, reading
  the newest write, and returns the full count; `futex`, `rt_sigaction`,
  `arch_prctl` return 0; `clone` takes the first dormant slot); a thread at
  a resolved transfer site takes the transfer; `exit_group(101)` is
  `abort k` only at the resolved site of `Λ.abortLbl k`.
- **Results** (both ISAs). `hello.w` prints `Hello, world\n` (13 `out`
  events, from the bytes the worker thread stored in the arena) and exits
  with 0; `handoff.w` exits with 42. The runs use the futex wait and wake,
  `clone`, the thread pointer and release/acquire handoff between two
  threads.

Mismatches between the emitted code and the statement, found by the runs:

1. **Transfer sites** (resolved). The runtime now labels its transfer
   sites (`scc_rt_take_site`, `scc_rt_release_site`), the sites resolve
   (`marksIn`), each thread's pool stack is taken into private memory, and
   no shared write lands in `Λ.stackPool` (`poolMsgs=0` in every run;
   formerly about 140 per run of `hello.w`).
2. **Abort labels at the system call** (resolved). The runtime labels
   each abort routine's `exit_group(101)` `scc_rt_abort_<kind>_exit`, and
   `Λ.abortLbl k` is that label. With every `write` to fd 1 refused,
   `hello.w` takes the write abort: the run ends with `writeErr` and the
   outcome `abort writeErr` on both ISAs (formerly it stopped at the
   unlabelled `exit_group`).
3. **Return addresses in data** (§7.2, item 5; resolved). The stack map
   holds code addresses that stack growth compares with return addresses.
   `raCheck` (both ISAs) runs `hello.w` until the callee of the stack map's
   first call site has built its frame, and reads the frame's return
   address (`[%rbp + 8]`, `[x29 + 8]`) and the table's entry from model
   memory: they are equal.

Byte-granular reads of the image (a byte load from a `.data` word) and the
kernel's `write` reading a byte of a word are as §3.1 states: the image is
8-byte words and `readByte` takes a byte of the word containing it. The
runs read the arena's bytes this way; the abort message (`.balign 1` in
`.rodata`, read by `write(2, …)`) is read the same way.

### 7.5 Derived data symbols (prepared, not switched)

Today `Λ.symbols` lists every data symbol's address and is trusted, checked
only by `Layout.WF` (§1.1). The alternative keeps only the section bases
trusted and computes each symbol's address from the text:

- **Layout.** `Λ.symbols` gives way to one base per data section
  (`dataBase`, `bssBase`; the heap arena, the stack pool and the pinned
  region are `.bss` symbols, so their ranges become derived too, or stay as
  `Λ` ranges checked against the derived symbol addresses). A symbol's
  address is `Kraken.DataImage.dataLabel base items name`, `items` the
  section's `DataImage.Item` list (labels, bytes, `.zero`, `.quad`,
  `.quadLabel`, alignment); `dataLabel_addrAt` gives the address of an item,
  `labelsFrom` the full table. `Λ.image` becomes `DataImage.image` of the
  same items (`.quad L` through `DataImage.resolve` with the code's label
  addresses), so the image and the symbols cannot disagree.
- **Where the items come from.** Either `textSection` keeps the data
  sections and the loader parses them into items (a parser for the
  directives `scc` prints: `.balign`, `.p2align`, labels, `.zero`, `.byte`,
  `.quad` of a number or a label; the walk of `Scc/Sem/Test/Run.lean`,
  `layoutOf`, is a prototype), or the emitter supplies the item list beside
  the text (trusted to match the text, checked by re-rendering). The first
  keeps the trusted base smaller.
- **x64 code.** A `.quad L` of a code label (the stack map) must hold the
  label's binary address, so x64 code must be laid out at the assembled
  sizes: `X64.sizedCells prog table` with the size table checked by
  `SizeCheck base cells labelOffs` (`Kraken/Promising/X64Sized.lean`,
  `label_of_sizeCheck`), the sized loader of §7.2. AArch64 needs nothing
  (4-byte instructions).
- **What changes in `Target{A64,X64}.lean`.** `load`: parse the data
  sections, compute `labelsFrom` per section, place their label cells
  (`placeSyms` on the derived table), load `DataImage.image` as initial
  memory in place of `imageMem Λ`; `symsAbove` against the derived table;
  x64 `threadAt` on `sizedCells` (shared with §7.2). `Layout.WF.symIn` /
  `symAbove` / `symNodup` become checks on the derived table (by
  evaluation: `labelsFrom` is computable), `symNodup` replaced by "first
  occurrence" (`dataLabel` is `lookup`).
- **Estimate.** Data-section parser into `Item`s: 120–180 lines (both
  ISAs share the directive syntax `scc` prints); loader changes: 40–60 lines
  per ISA; `Layout` / `WF` / `imageMem` replacement and the `#guard` tests
  redone on the derived layout: 80–120 lines; x64 sized cells beyond §7.2:
  none if that lands first. About 300–450 lines in all, plus re-running
  `Scc/Sem/Test`.

## 8. The memory relation, one thread (M1): design

A reusable library, `Scc/Sem/MemRel.lean`, showing that the memory clauses of
`Components` are preserved by each shared access of one target thread paired
with the matching source step, stated over the witness's maps so that the
per-construct `Seg` lemmas (`Spike/Lib/Seg.lean`, cases `Out.load`,
`Out.store`) and the runtime routines (allocator, cursors, headers) can call
it. The spike did this for one location (`Spike.Bridge.MemRel`: identity
timestamps, every message a flag write); this generalises it to every
placed label.

**Scope of M1.** One source thread and one target thread doing all shared
writes; no promises on either side; 8-byte shared accesses at word
addresses (no store pairs: `pairs` is untouched, and target messages inside
label ranges are 8-byte at word addresses); `gc none` (`Λ.relocates =
false`, `Λ.colourMask = 0`, `since = tsFrom = 0`); no reuse of label ranges.

**Scope of M1: scalar-only labels, and where words live.** `wordAddr`
places word `i` of a label at `base + 8i`, the linear reading of
`Scc/LAYOUT.md` §2 for objects without trace words; the base
(`Witness.lbl`) is the object's scalar word 0, the address `scc_rt_alloc`
returns, and the header at `base − 8` is outside the label's range, so the
allocator's header store is a runtime write. Objects with trace words need
the general slot map (`Obj.slots`) and are M2's. In registers and frames a
locative is two target words (`Scc/LAYOUT.md` §4), so `Witness.env` maps a
source word to a `WordPlace`: one place (`ValRep`), or a base place and an
offset word (`LocRep`: base = the label's base, offset word = `8 · offset`,
no tag). The offset word may be an immediate folded into the access
displacements (`OffPlace.imm`, `newBuf`'s `(p, 0)`). The lowering also
keeps live scalar constants as immediates only (hello1's `m ↦ imm 2`
across the `newBuf` call). **Decision (A′):** a word may be at an immediate
(`WordPlace.imm n`, represented when `ValRep lbl x n`) only where a fixed
per-program table says so: `Layout.imms : Expr → String → Nat → Option
Nat`, keyed by a frame's remaining term (its control point, `frameTerms`),
the variable and the word index, emitted by `scc` from the lowering's
placement data. `Components.env_imm` asks every immediate the witness uses
to be the table's. Keyed by the source term, not the target pc, so that it
holds in runtime code (the frame stays at `let p = newBuf …; e` across the
call) and for suspended frames. Two control points with the same remaining
term and different constants are refused by `scc --code` (the table is a
function). Holes: P4 still rejects (empty table); `not_components_imm_wrong`
(another constant), `not_components_imm_wrong_var` (another variable);
`components_env_imm` accepts.

**The relation.** `MemRel Λ lbl lsize ts tm sm` on the target memory `tm`,
the source memory `sm` and the witness's `lbl`, `lsize`, `ts`: the memory
clauses of `ComponentsAll` (`lbl_static`, `lbl_range`, `lbl_disj`,
`lbl_mem`, `mem_rep`, `ts_first`, `ts_mono`, `mem_onto`), for **every**
label. Under `gc none` nothing is reused, so the unscoped form is an
invariant, and it avoids liveness reasoning altogether: `Components` follows
by `ComponentsAll.scoped` (since and tsFrom are 0). Liveness matters only
once a collector reuses ranges (M2 or later). Two derived facts carry most
proofs:

- *injectivity of placement* (`wordAddr_inj`): two source addresses with
  in-bounds offsets that map to one target word are equal (from `lbl_disj`
  and `lbl_mem`; zero-word labels have no in-bounds offset);
- *timestamp bound* (`ts_le_last`): every `ts k` is at most `tm.last`
  (`mem_rep`'s `wordAt` needs the message to exist).

**Operations** (each a theorem `MemRel … → MemRel …'`, plus what the
construct proof needs):

1. `MemRel.store`: the target appends `⟨wordLoc a, v, tid⟩` (timestamp
   `tm.last + 1`), the source pushes a message to `sa` with `wordAddr lbl sa
   = some a`, `sa.offset < lsize sa.label` and `ValRep lbl m.val v.toNat`;
   the new `ts` maps `sm.size ↦ tm.last + 1`. `mem_rep` of old messages:
   `read?` at old timestamps is unchanged by `append`; `ts_mono`: the new
   image is above every old one (`ts_le_last`); `mem_onto` of the new
   message: its preimage is the new source message.
2. `MemRel.latest` (the read side, `rd` of FINDING.md): if `j` is the latest
   source message to `sa` and `k'` the latest target message to `a` (or 0
   with none), then `ts j = k'`, so the value the target reads at `k'`
   is represented by `sm[j].val`. Proof: `ts j ≤ k'` since `ts j`'s message
   is at `a`; a target message at `a` after `ts j` has a preimage
   (`mem_onto`) at `sa` (`mem_rep`, `wordAddr_inj`), hence before `j`, and
   `ts_mono_loc` orders them the other way. `MemRel.load` packages it for
   `Out.load`: the source word `⟨sm[j].val, sm[j].view, j⟩` represents the
   value read.
3. *Views* (thread invariants the caller keeps, with preservation lemmas
   here): the source thread's read bound at `sa` is at least the latest
   message to `sa`, so `WeakMem.readable` holds for that message only
   (`readable_iff_latest`); the target thread's coherence view of `a` is at
   least the latest target message to `a`, so Kraken's load reads it only.
   A store raises both to the new message; a load keeps them. With one
   thread these are the whole view relation.
4. `MemRel.rmw`: a read of the latest message and an adjacent append
   (`cas`, exchange, fetch-add), as 2 then 1.
5. `MemRel.alloc`: the source allocates a fresh label `l` of `n` words (one
   first message per word, `undef` or zero, `TermRun.alloc`, `allocBuf`);
   the target bumps its cursor and writes no cell (the arena is zeroed).
   New `lbl l = b`, `lsize l = n`, the range in `Λ.heap`, disjoint from
   every placed label, no target message in it; the new messages map to
   timestamp 0 (`ts_first`: they are first at their addresses), `ValRep`
   of `undef` or zero against the initial `0`.
6. `MemRel.runtime_write`: a target write outside every label range
   (cursors, headers, the stack pool's metadata, control blocks in
   `Λ.pinned`) with no source step keeps `MemRel` (`mem_onto` does not
   apply; old reads unchanged).
7. `Components.ofMemRel`: `MemRel` plus the non-memory clauses (threads,
   environments, stacks) and `since = tsFrom = 0` give `Components`.

**Not in M1.** Promises and certification (a promised target write is
appended before the source's; the timestamp map then needs the promise
correspondence of `Spike/Bridge/Sim.lean`), other threads' writes (the
views become a relation between the threads' views and `ts`), store pairs
and 16-byte messages, relocation and colour bits. M2 extends `MemRel` with
these; the M1 lemmas stay as the promise-free cases.

**Estimate.** `MemRel` and the derived facts 200–300 lines; store, load
(latest) and the view lemmas 300–450; alloc and runtime writes 200–300;
`Components.ofMemRel` and tests (toy memories in the style of
`Scc/Sem/Holes.lean`) 150–250. About 0.9–1.3k lines.

**Status: implemented** (`Scc/Sem/MemRel.lean`, about 720 lines), with
these differences from the plan above:

- `MemRel` also takes the source's pair list (`ts_mono` mentions it); the
  operations leave it unchanged. `MemRel.empty` is the base case (no static
  labels, nothing placed, no source message).
- Items 1, 5, 6, 7 are `MemRel.store`, `MemRel.alloc`,
  `MemRel.runtime_write`, `Components.ofMemRel`, as planned. `alloc` takes
  the new source memory abstractly (its size, its old prefix, and one
  message per new word whose value the zero word represents).
- Item 2 assumes every target message is an 8-byte access (`Narrow`; M1 has
  no store pairs and no narrower shared accesses). `MemRel.latest` takes the
  latest source message as `SLatest sm sa j` and the latest target write as
  `TLatest tm a k'`. `MemRel.latest_read` is the planned `load`: the value
  an 8-byte target read at `k'` returns is represented by `sm[j].val`.
  `MemRel.latest_byte` gives the byte the kernel's `write` reads
  (`Kernel.readByte` reads the containing word).
- Item 3 is simpler than planned. `readable_latest`: the source can always
  read the latest message to `sa`, whatever its read bound, because no later
  message can hide it. So M1 needs no lower bound on the source's views.
  `readable_iff_latest`: with a bound at or above it, it is the only message
  the source can read. The target side is a hypothesis of `latest`: the
  target thread must read at the latest write of the word (`TLatest`).
  `Scc/Sem/Coh.lean` discharges it. The thread invariant is
  `t.prom = [] ∧ CohCovers t.views tm`: every message's timestamp is at
  most the thread's coherence view of its location.
  - It holds of the loaded memory (`CohCovers.empty`).
  - Every instruction of the thread keeps it (`stepOne_coh`,
    `instrSemC_coh`), runtime writes included. With no promise, a store is
    a "promise now" at `last + 1` that raises the coherence view there
    (`stepOne_store_append` gives the appended message).
  - The kernel's byte read and its return keep it (`readByte_coh`,
    `retThread_views`).
  - Under it, a load reads the latest write of its word
    (`stepOne_load_tlatest`), and so does the kernel's `write` byte read
    (`readByte_tlatest`). Kraken's read rule hides every write to the
    location between the timestamp read and the coherence view.
  - Promise steps break the invariant: an outstanding promise is a message
    above the coherence view, and the thread may read below it. They belong
    to M2, as do other threads' writes and `clone`.
- Item 4 is a composition, not a lemma. The read-modify-writes of the
  fragment (`xchg` on own buffers) lower to a plain load then a plain store.
  The target load appends nothing, so it is the read side followed by
  `store`.
- Sub-word stores are outside the fragment and are not covered.
- `MemRel.toy` composes `empty`, `alloc` and `store` on `trivLayout`.

## 9. The memory relation with promises and several threads (M2)

### 9.0 Promises in the one-thread case: the choice

The M1 lemmas (§8) assume the target thread has no outstanding promise.
Kraken's machine lets even a lone thread promise (`PromSemInf`) any write a
promise-free solo run of it can perform, so a related target configuration
may hold promised messages. The statement fixes one constraint: `Sim.sim`
needs `R t s` at **every** reachable target configuration, and `explicit`
needs `Components` there. `Components.mem_onto` then asks every target
message in a live label's range to be the image of a source message,
promised ones included. So with an outstanding target promise to a live
cell, the source memory must already hold the corresponding message: the
source must promise too. The options:

**(a) Promise elimination for one thread.** Prove that every run of the
one-thread target machine is matched by a promise-free run with the same
observable trace.
- This does not meet the constraint above by itself. `R` must still hold
  at the configurations that have outstanding promises, and their memory
  holds messages the source has not written. So (a) is useful only
  together with a statement that quantifies over promise-free runs, as in
  (b). (a) would then justify (b): it shows that, for one thread, (b)
  loses no observable behaviour.
- Reuse: Kraken's per-promise Lemma 1 in both directions (`PromProjection`,
  `PromReplay`, with `PromProjectionSim`, `PromReplaySim`), Lemma J
  (`prom_le_of_certOkN_promThread`, `not_certOkN_of_dead`), and
  `Config.Equiv` from `PFComplete`. A whole-run elimination needs a
  scheduling argument across promises, which `PFComplete` rates as the hard
  step of `pf_complete_ordered`. It is simpler for one thread, since every
  promise is the thread's own and is fulfilled by it. Estimate:
  2–3k lines.
- M2: does not carry over. Hello has two threads, and `PFCompleteDRF`
  records that promise-free completeness fails for racy programs and needs
  a data-race-freedom hypothesis in general.

**(b) State M1 for promise-free runs only.** Add an explicit hypothesis to
the theorem, for example by quantifying `Sim` over runs with no promise
step.
- Size: no new proof in `Scc/Sem/MemRel.lean` or `Scc/Sem/Coh.lean`. The
  statement edit plus the Holes evidence for it (D5(b)) are about 100–200
  lines.
- Cost: the certificate then says nothing about executions that need a
  promise. Those are the executions the promising model admits beyond
  promise-free interleaving, so the claim is narrowed. Without (a), it is
  not known that nothing observable is lost even for one thread.
- M2: a dead end. Two threads with a release/acquire handoff have
  behaviours that need promises, so the hypothesis would have to be
  removed again.

**(c) Mirror promises (recommended).** A target promise of a message to a
placed word is matched by a source promise (`TermRun.Step.prom`) of the
corresponding message, at the paired timestamp (`sm.size ↦ tm.last + 1`,
the shape `MemRel.store` already takes: a source promise is a push). The
source promise is certified by lockstep: the target's `CertOk` run is
replayed by a source `Solo` run, as the spike's `certified_of_certOk`
does for the writer. A promise to an address outside every label range is
`MemRel.runtime_write`, with no source step. The work:
- The target invariant generalises from `CohCovers` to every
  non-promised message being at most the coherence view of its location.
  Every outstanding promise is then above it, because a certifiable thread
  has no dead promise (`not_certOkN_of_dead`, `Thread.hasDeadPromise`).
  Promises are also above the write floor (`Config.LiveK.wfloor_lt`,
  AcqFloor). Done for one thread: `CohCoversP` in `Scc/Sem/Coh.lean`,
  kept by every instruction and promise step with no hypothesis on the
  promises (`stepOne_cohP`, `stepSemC_cohP`); a read sees the latest
  write not promised (`TLatestP`, `stepOne_load_tlatestP`).
- `TLatest` and `SLatest` become "latest fulfilled write", with promised
  messages paired by `ts`.
- A view relation for the one thread: source views at most target views
  through `ts`. It fixes the source promise view (`w = sm.size - 1` is
  safe, FINDING.md) and the side conditions of the source fulfilment.
- The lockstep lemma generalised from one source step per target step to
  the `Seg`/`Out` cases (`Solo` segments).
- Estimate: 1.5–2.5k lines for one thread.
- M2: carries over directly. It is the promise half of M2, and M2 adds
  other threads' messages and the view relation across threads (§9.1 on).
  The M1 lemmas stay as the promise-free cases.

  Open risk: a promise to a cell the thread allocates later in its
  certification run. This risk is analysed under "Fresh allocation"
  below. The analysis corrects the first reading: the source cannot
  usefully promise to a label it has not allocated yet. The target can
  promise to the future address, and that asymmetry is the actual risk.

**Recommendation.** (c), with no statement change. The M1 library remains
valid as the promise-free cases, and the promise mirroring is the first
part of M2. (b) is acceptable only as an explicitly labelled intermediate
milestone ("M1 for promise-free runs"), never in the final certificate.

**Decision: (c).** Chosen: promises are mirrored, the
statement is unchanged, and there is no interim promise-free theorem. The
fresh-allocation risk above is analysed before the promise mirroring is
built.

**Fresh allocation (analysis; Decision 2: (a) with (e) and (f′)).**

The mechanics on each side:

- Target. `writeSuccs` either fulfils an own promise `t` with the same
  location and value, provided `t` is above `max νpre (coh l)` (for RMW
  also above the read timestamp), or appends and then fulfils. Every
  store can fulfil, including the plain header store in `Runtime.allocF`,
  the init stores emitted for `new`, and the cursor RMW. The arena is
  zero-filled `.bss` and is never reused, so the address the next `allocF`
  returns is a deterministic function of the cursor. A thread can promise
  `⟨X, v⟩` for a future arena address `X` and certify that promise solo by
  running to its next allocation and storing `v` there.
- Source. `alloc`/`allocBuf` push fresh messages for `base … base+n-1`
  and raise `coh` past them. A source promise is pushed at `mem.size`, so
  a promise made before the alloc has an index below the post-alloc
  `coh`. `stepStore` needs `coh a < t`, so that promise can never be
  fulfilled. Since `freshLabel` is thread-local and the label does not
  exist before the alloc, a certified source thread never promises into a
  label it has not allocated yet.

The mismatch: a target promise to an address that, at promise time, lies
in no placed label but is later covered by an allocation of the promising
thread (M1), or of another thread (M2). Lockstep mirroring at promise time
has no source label to push to. If it pushed anyway (to some placeholder),
the mirrored promise would be dead after the alloc, so source certification
would fail where target certification succeeds.

Options:

- (a) Deferred mirroring (recommended). A target promise to an address
  outside every placed label pushes no source message. It is a runtime
  write, and `Components.mem_onto`, `mem_rep` and `ts_first` already
  scope to `Live` labels, so nothing is owed for it. When the promise is
  fulfilled after the alloc, the source makes an ordinary append store
  (the append case of the store step), not a stutter.
  - Changes: a `MemRel.alloc` variant whose `hnone` is weakened from "no
    target message in the range" to "no target message in the range other
    than outstanding promises of the allocating thread" (M2: of any
    thread). Also a timestamp-map extension at fulfil time.
  - Certification: the source certifies by the same lockstep, because the
    deferred promise contributes no source obligation until it is
    fulfilled.
  - No statement change.
- (b) Make pre-allocation promises unfulfillable on the target, for
  example by a fence or a release store before every allocation. This does
  not work: `ok t` only bounds the promise from below, so a promise placed
  high enough remains fulfillable whatever the runtime does. Rejected.
- (c) Poison stores: store to every cell of the new block at allocation,
  so the init stores are not the first writes. This costs one store per
  cell, and it is still unsound because the poison store can itself
  fulfil the promise. Rejected.
- (d) Statement scope. Exclude target runs that fulfil a promise made to
  an unplaced address. This weakens the statement, and the analysis shows
  it is unnecessary. Rejected unless (a) fails.

Open point for M2: another thread `T'` may read the promised message at
`X` before `X` is Live for `T'`. Under (a) the read is of a runtime-written
location. The intended argument is that `T'` has no pointer into the
block, because the only way to obtain one is through a published pointer
whose release orders it after the alloc. That needs the provenance part
of the typing invariant (`SrcTyped`) to be stated for target addresses as
well as source labels.

Deferred mirroring conflicts with two `Components` clauses as first
stated. A promise to `X` placed at target time `p` but mirrored at fulfil
time gets a source index above messages to other locations with target
timestamps above `p`, so a global strictly monotone `ts` fails; and while
it is outstanding after the alloc it is a target message in a live range
with no source image, so `mem_onto` fails. Two statement changes resolve
this:

- (e) `Components.ts_mono` is per location: strictly increasing on the
  positive images of messages to one live location in its epoch. Order
  across locations is left to the view relation (the per-location cut
  `k ≤ Vs ↔ ts k ≤ Vt` and the latest-write relation), which is where a
  reordering of writes to distinct locations becomes observable.
- (f′) `Components.pre_alloc`: without relocation, a target message to a
  live label's range at or before `Witness.tsFrom l` is a source image or
  an outstanding promise of its writer. `mem_onto` still covers everything
  after `tsFrom`. `epoch_fixed` no longer forces `tsFrom = 0`.

On x64 (TSO) the same promise machinery exists (`Arch.tso` uses the same
`writeSuccs`); M1 alone would keep the global order, M2 breaks it.

Decision 2: adopt (a) with (e) and (f′), and accept the M2
provenance obligation as part of the cross-thread view relation.

**Open item: M2 provenance obligation.** Under (f′) another thread's
outstanding promise to a block may sit in a live range with no source
image. A thread that reads it must be shown not to hold a pointer into
the block before the allocating thread publishes one (with a release that
orders the read after the allocation). This needs `SrcTyped`'s provenance
stated for target addresses, and is to be discharged with the
cross-thread view relation. Not needed in the one-thread case, where only
the allocating thread can promise into its own future block.

**Open problem for M2: promises into a not-yet-allocated block.** The
provenance obligation above is false as stated. `Scc/Test/M2Hole.lean`
proves a two-thread run reachable in Kraken's fuel-free semantics, on
ARMv8 and on TSO. `T1` runs `cur` bump (acqRel RMW), then `[X] := 5`
through the base, then the publish `[S] := base`. `T2` loads `S`, then `X`
through it. Before `T1` executes anything, it promises all three writes
(on TSO, `S` above `X`), and `T2` reads `S` and `X`. No related source
configuration exists. The source `T1` has not run, so the label is not
allocated. A source promise into it is uncertifiable, because `alloc`
raises `coh` above every earlier index. `freshLabel` is thread-local, so
`T2` cannot name the label either. WeakCore's runtime obligation R11
(`TermRun.alloc`) orders an allocation after the thread's *earlier*
writes only. Here the pointer store is program-order *later*. The state is
also architecturally allowed: nothing orders later stores after
`ldaddal`'s write. Candidate resolutions, none chosen:
- R1, statement scope: exclude runs in which a thread reads a promise to
  a not-yet-allocated address.
- R2, WeakCore: allow promises into the thread's next `freshLabel`, and
  keep them alive across `alloc`.
- R5′, target restriction plus a proof that it loses no observable
  behaviour.
No runtime fix is known: every store can itself be promised low, so no
code sequence forces an access above the promise. `hello.w` is unaffected.
Its pointers cross threads only through `spawn`'s argument, a system call
at which the spawning thread has no outstanding promise (`clone` is a
certification dead end, §6, 44), and
no thread allocates after the spawn. The general case is open for M3.

**Runtime invariant: the cursor bump is acquire-release.** The cursor RMW
of `Runtime.allocF` (`emit (.rmw .add old ⟨cur,0⟩ sz)`, `Scc/Lower/Runtime.lean`)
is emitted as `ldaddal` on A64 (`ldopAL`, `Scc/Emit/A64.lean`) and
`lock xadd` on x64 (`Scc/Emit/X64.lean`; `Arch.tso` has
`plainRmw := .acqRel`). Kraken's `rmwPost` raises `vwNew` to the RMW's
write timestamp `q` for an acqRel RMW, and `writeOk t` needs
`vwNew < t`, so every promise at or below `q` is dead after the bump.
`Scc/Sem/DeadProm.lean` proves this: `not_certOkC_of_dead` (a thread with
an outstanding promise `p ≤ vwNew` is not certifiable) and
`certOkC_prom_gt_vwNew`.

Consequence for deferred mirroring. When the bump appends, `q` is above
every message, so a certified thread holds no promise across the
allocation and the deferred case of (a) does not arise there.

This does not cover a bump that *fulfils* an earlier promise `q` of the
same thread to the cursor; promises above `q` stay alive. Scenario (one
thread, deterministic cursor): promise `cursor := cur+sz` at `q`; promise
`X := v` at `p > q` for an `X` in `[cur, cur+sz)`; the bump reads the old
cursor (below `q`) and fulfils `q`, leaving `vwNew = q < p`; the init store
of the new block fulfils `p`. The target certifies, and at promise time of
`p` there is no source label to mirror to. So the deferred case of (a) can
still fire, but only for promises made after a still-outstanding promise
to the cursor. "Neither variant" (mirror at promise time, `prom = []` at
every allocation) is therefore not sound as stated; a decision on
mirror-at-alloc versus append-at-fulfil is still needed for this case.
(e) and (f′) stay as stated.

The AL is load-bearing. With a relaxed cursor RMW there is a
counterexample to mirror-at-promise: promise Y at target ts 12; allocate
(relaxed); plain load of a zero cell of the new block (the source read
view becomes at least the cell's index, which is above the mirrored Y,
while the target reads ts 0); `dmb ld`; fulfil Y. The target certifies,
and the source's Y is dead. The guard tests
`Scc/Test/AllocOrderA64.lean` and `Scc/Test/AllocOrderX64.lean` pin the
emitted bump (`ldaddal`, `lock xadd`) so that a change to the emitter
breaks the build.

**Never-mirror for M1 (accepted for M1; reverses the
mirroring of Decision (c) for one thread; mirroring is revisited in M2).**
The witness of `explicit` is
chosen per pair of states (`∀ t s, R t s → ∃ w, Components …`), so a proof
may take `Witness.tsFrom l` as the target's last timestamp for every label.
`Components` then admits outstanding promises with no source image anywhere
(`pre_alloc` exempts outstanding promises of their writer), and still
rejects a write that is no promise (`Holes.not_components_live_write_tsFrom_last`).
For one thread this gives a simpler M1:
- a target promise is a source stutter (`MemRelP.promise_unmirrored`);
- a target fulfil is a source append (`MemRelP.fulfil_unmirrored`), which
  `Promises.stepStore` takes with no side condition; (e) holds because the
  fulfilled timestamp is above `coh l`;
- no source promise, so no source certification;
- a source load reads the latest message (`readable_latest`), and the
  target reads the latest message not its own promise (`TLatestP`), which
  `MemRelP.latestP` relates with the promise list `tq`.
M1 then needs no view relation. The fresh-allocation case, the narrow case
above (a bump fulfilling a cursor promise) and the AL dependency only
matter once promises are mirrored, so they move to M2. The earlier text of
this section, which treats the narrow case as an M1 obligation, is kept
as the analysis under mirroring: it is the M2 plan.

**M2 note: a view relation draft, and RMW forwarding.** The draft maps
source views to target views as: `coh` to the coherence view of the word
location, `vRd` to `vrOld`, `vWr` to `vwOld`, `vPreBase` to `vrNew` and
`vwNew`, `vRelSt` to `vwNew`, `vCtrl` to `vwNew` (TermRun never raises
`vCtrl`). One mismatch is known. WeakCore records no `fwd` entry for an
RMW's own write, so a plain re-read of the RMW's location raises the source
`vRd` to the RMW's message index, while Kraken reads through the RMW's
forwarding view, which can lie below a mirrored promise. So `vRd ↦ vrOld`
breaks after `rmw X; ldr X; dmb ld` when a mirrored promise lies below
`X`'s write. M2 must either add the `fwd` entry in WeakCore or weaken the
`vRd` clause.

**Decision: the M2 mirroring policy is by phase, and the M2 relation
assumes (D).** This replaces an earlier policy (lockstep for placed words,
deferred mirroring at fulfilment for unplaced ones).
- *Before the first spawn* (one thread): never-mirror, the M1 machinery as
  it is, with no view relation.
- *After the first spawn*: lockstep, with no deferral. A target promise to
  a placed word is matched at once by a source promise at the paired index
  (`sm.size ↦ tm.last + 1`, `MemRelP.store` with `b = true`) with message
  view `w = sm.size − 1`.
- *(D) No deferred message after the first spawn*: no target promise into
  a label not placed yet is fulfilled while another thread exists. (D) is
  the hypothesis of the M2 relation. Deferral after the spawn breaks the
  relation (the late-index problem below).
- (D) for hello.w is discharged on the target side: every store row
  reachable after the spawn (`worker`, `waitLoop`, the runtime) names `b`
  or `o`, both placed before the spawn, or a runtime word. It is not taken
  from the source text, which would be circular.
- *The handover at the spawn.* The `clone` dead end (§6, 44) makes the
  switch clean: no promise is outstanding at the `clone`. The relation's view part is set
  up there by three lemmas, to be proved explicitly: with no outstanding
  promise, `vwOld` is at least the timestamp of every message the thread
  wrote; every source message's image at the spawn frontier `N` is a write
  of `main` or an initial value; and the register pairing's cut is taken
  against `max reg.view Full`, since fences do not raise the register
  views.

Two arguments fix lockstep after the spawn:
- *Never-mirror fails for two threads.* `Sim.sim` is run-based: every
  reachable target configuration, including those with outstanding
  promises, must be related. In hello.w, `worker` (after its last system
  call) promises its release store of `c`, and `main`'s `ldar c` reads the
  promised message before `worker` executes the store. Under never-mirror
  the source has no message to read, so no reachable source configuration
  is related. Nothing in the statement excludes this; it is ordinary
  behaviour of the model on both architectures.
- *Lazy mirroring (mirror a promise only once another thread observes it)
  is unsound.* Views are scalar on both sides, so a message's place in the
  global order is observable. On TSO: `T1` promises `y := 1` at `p`
  (unmirrored); `T2` promises `z := 1` at `p2 > p`, mirrored at `n2`; `T2`
  reads `T1`'s promise, which is mirrored now at `n > n2`. The target `T2`
  has `vRd = p < p2` and can fulfil `p2`; the source `T2` has `vRd = n >
  n2`, its store bound includes `vRd`, and the fulfilment's `ob < t`
  fails. ARM has the same shape through `vPreBase` after an acquire read or
  `dmb ld`. So the source promise must be made when the target's is.

**The late-index problem: why no deferral after the spawn.** A deferred
target promise at timestamp `t0` (to an address in no placed label when it
is made) gets its source message only at its fulfilment, at index
`k0 = sm.size`, after every source message pushed in between. Messages
`j < k0` with `ts j > t0` are inversions: a source view raised by index to
cover `k0` covers them too (`rdV`, `acqV`, `pairTop`, the fulfilment's
`commit` raising `vWr` to `t`), where the target view covers only `t0`.

*Example 1, one thread, TSO (paper, not checked in Lean).*
- Program: `T1` does `alloc B; X := 5` (into `B`) `; S := 1` (`S` a placed
  global).
- Run: `T1` promises the cursor bump (`q`), then `X` at `t0` (deferred, as
  `B` is not placed). It executes the bump, which fulfils `q`, so the `X`
  promise survives. It then promises `S` at `tS > t0`, mirrored at `kS`,
  executes `X` (fulfilling `t0`, a source append at `k0 > kS`) and then
  `S`.
- Source: `storeOb` on TSO includes `vWr`, and after the `X` append
  `vWr ≥ k0 > kS`, so the source cannot fulfil `kS`. Target: `vwOld = t0 <
  tS`, so the target can fulfil `S`. The source thread has a dead promise
  where the target has none (`not_certOkN_of_dead`).

*Example 2, three threads, TSO (paper, not checked in Lean).* As Example 1,
and `T3` writes `y := 1` at `t1 > tS` (source index `j1`, `kS < j1 < k0`).
- `T2` reads `S` after its fulfilment, then `X` after its fulfilment, then
  `y`; no promise is outstanding at any of these reads.
- Target: `T2`'s bound is at least `tS` and below `t1`, so it may read
  `y`'s initial value. Source: `T2`'s `vRd ≥ k0 > j1`, and on TSO
  `readBoundOf` includes `vRd`, so `y`'s initial value is hidden
  (`hiddenFrom`). The source cannot make the target's read.

Both examples need the narrow case: a deferred promise to a heap block not
placed yet must survive its allocation's bump, so the thread must have
promised the bump itself (an appending bump kills every earlier promise of
the thread). Static labels are placed at the start and never need
deferral. Repairing deferral by mirroring at placement instead of at
fulfilment only shrinks the window: a lockstep promise of the same thread
in between recreates Example 1. For general programs, (D) is the scope of
the open problem above, and R1, R2 and R5′ are to be judged against it;
R5′ in the form "no promise of the cursor RMW while another thread exists"
would establish (D) directly.

**Open point for M3: allocation after the first spawn.** (D) alone is not
enough. A source allocation after the spawn pushes the fresh cells'
messages at high source indices whose images are old target timestamps,
which breaks the monotonicity of `ts` above the spawn frontier even with
no promise at all. The relation then needs "no placement after the first
spawn", which is stronger than (D). R1, R2 and R5′ remove deferred
promises but not this. hello.w and handoff.w allocate nothing after the
spawn.

Consequence for M1 code: definitions (`Pre`, `R`, `CertProm`, the `Out`
rows, generated instance parts) stay generic over the split and carry
`tp`. `tp = []` is specialised only in the final instantiation; where a
one-thread proof genuinely needs it, it is a named hypothesis of the
lemma, not part of a definition.

**Certified promises in M1.** Never-mirror still needs every outstanding
target promise to lie in the layout's shared region (and, for the fixed
runtime words, to carry their fixed value), so that the memory part of the
relation survives a promise step. A promise is certified by a solo run
that fulfils it, and a fulfilment writes exactly the promised location and
value, so it suffices that every fulfilling write of the certification run
is such a write.
- A per-tree argument (`WriteCodeOn`, `Scc/Sem/Wide.lean`) proves this for
  properties of the written value. It quantifies over every value a load
  may return, so it fails for a property of the address: scc code stores
  through locatives it has loaded.
- The route taken is at the configuration level (`Scc/Sem/CertProm.lean`).
  An invariant `Q` of thread and memory that every step of a certifying
  run keeps, and whose fulfilments satisfy `G` (`StepG`), gives `G` of
  every outstanding promise (`certOkC_prom_good_cfg`). In M1 the
  simulation relation itself is such a `Q`, once its memory clause
  exempts the thread's outstanding promises (`MsgsExcept`): a load of the
  certification run reads the latest message the thread has not promised
  (`stepOne_load_tlatestP`), which the relation pins, so the loaded
  locatives are the related ones.
- The closure `StepG` needs covers every successor of a certification
  step, `stepOneWith (Kernel.certExec K)`, not only the machine's
  (`Scc/Sem/CertStep.lean`). Off a supported system call that step is a
  `stepOne`, so the machine's instruction rows apply unchanged. At a
  supported call it is silent: memory and promises unchanged, the thread
  in a state `certSuccs` lists, one per return in `Kernel.results`; at
  `exit` and `exit_group` the run stops. So the system-call rows must hold
  for every such return, including those the kernel step itself would not
  take at that configuration. Certification runs are promise-free
  (`ThreadNPC`), so `Q` must hold along runs that make no promise.
- M2: other threads' messages above the coherence view become readable in
  a certification run, and they are not pinned by the run's own relation.
  The address argument must then come from a typing invariant of all
  messages (every message to a shared word holds a well-typed value),
  not from the one-thread simulation.

#### Certification across system calls (faithfulness)

*Status.* Neither fix below was taken. Certification became the faithful
solo projection of the kernel step (§3.1), and alternative (ii)'s progress
argument is proved for every supported call but `write`
(`Kernel.sys_progress`); `SvcNoProm` is replaced by `WriteNoProm` (§9,
*Open for hello1*). The analysis is kept as the record of the hardware
questions.

The open hypothesis `SvcNoProm` (no outstanding promise at a system call)
had a planned fix: make `Kernel.certExec` a dead end at every
`svc`/`syscall`, so that no certification run passes a system call. In
Kraken's promising machine an outstanding promise at a system call is the
only way to make a store that is program-order after the call visible
before an access that is program-order before it. So the fix forbids
exactly the reorderings across a system call. This subsection checks
whether hardware (with Linux) can show them. It is a paper analysis; no
model change is made here.

Sources consulted:
- [S1] B. Simner, A. Armstrong, T. Bauereiss, B. Campbell, O. Kammar,
  J. Pichon-Pharabod, P. Sewell, *Relaxed exception semantics for Arm-A
  (extended version)*, arXiv:2412.15140v1 (2024). Used: §3.2.1, §3.2.2,
  §3.5, §4.1, §5 (Fig. 9, the axiomatic model), App. B.1.1 and Fig. 14
  (architectural intent per test and hardware results on Cortex-A53,
  A72, A76 and A73).
- [S2] Intel 64 and IA-32 Architectures Software Developer's Manual,
  Vol. 2, instruction reference for SYSCALL, paragraph "Instruction
  ordering" (read through a public mirror of the SDM text).
- [S3] Linux, `arch/arm64/include/asm/sysreg.h` (`INIT_SCTLR_EL1_MMU_ON`)
  and `arch/arm64/kernel/entry.S` (`kernel_exit`), current mainline.
- The Arm ARM (DDI 0487) itself was **not** consulted directly. Its
  exception-entry text is cited here only as [S1] reports it.

**AArch64.**
- (a) *A store after the `svc` visible before the `svc` is taken: no.*
  A context-synchronising exception entry is not taken speculatively, and
  writes do not propagate speculatively ([S1] §3.2.2, §4.1). In the model
  of [S1] Fig. 9, `ctxob` contains `[CSE]; po` and the exception entry
  (`TE`) is a CSE unless FEAT_ExS is implemented with SCTLR_ELx.EIS = 0.
  Linux sets EIS and EOS in `INIT_SCTLR_EL1_MMU_ON` [S3], so under Linux
  entry and return are context synchronising.
- (b) *A store after the `svc` visible before an earlier load is
  satisfied (load buffering): architecturally allowed.* Exception
  boundaries are not memory barriers: loads and stores may be reordered
  across entry, return, or both ([S1] §3.2.1). The ordering
  `speculative; [CSE]` covers only `ctrl`, `addr; po` and the SEA
  variants, not a plain earlier load. `LB+svc-erets` (both threads:
  `ldr; svc` with an `eret`-only handler, then `str`) is Allowed in the
  base intent, but was not observed on the four cores tested. `LB+svcs`
  (the store in the handler) was observed on Cortex-A73 (388 in 18M)
  ([S1] Fig. 14). It is forbidden only on implementations whose loads may
  raise synchronous external aborts ([S1] §4.1, variant SEA_R).
- *Write-write across an `svc`: allowed and observed.* `MP+svceret+addr`
  ([S1] App. B.1.1):
  `T0: str 1,[x]; svc #0; str 1,[y] || T1: ldr r0,[y]; ldr r1,[x + (r0 eor r0)]`.
  The outcome `r0 = 1 ∧ r1 = 0` is Allowed in the base intent. It was
  observed on Cortex-A53 (52 in 1M), A76 (2 in 11M) and A73 (13K in 17M).
  In Kraken this outcome needs T0 to promise `y` before it writes `x`,
  that is, a promise outstanding at the `svc`. The fix forbids it.
- *A full barrier before the `svc` removes both shapes in hardware*:
  `LB+svc-dmb-erets`, `MP+svc-dmb+addr` and `MP+svc-dmb-eret+addr` are
  all Forbidden ([S1] Fig. 14; there the `dmb` is in the handler, which
  orders the same accesses as a `dmb` placed just before the `svc`).
- *Linux entry path.* `kernel_exit` [S3] has a `dsb nsh` only under the
  workaround for speculative unprivileged loads, and a `dmb sy` only for
  returns to EL1 under an erratum. The `sb` after `eret` is a speculation
  barrier and is never executed architecturally. So the entry path
  guarantees no memory barrier between user code before and after a
  call. A particular call may still order these accesses through the
  locks or barriers it uses internally (a release followed by an acquire
  orders everything before the release before everything after the
  acquire). That depends on the call and the kernel version. It was not
  audited for `write`, `futex` or `rt_sigaction`, and is not relied on.

**x86-64.** SYSCALL is not serialising. The instructions after it do not
execute, even speculatively, until all earlier instructions have
completed, but earlier stores may not yet be globally visible [S2]. So
(a) cannot happen. TSO already orders load→store and store→store, so
load buffering and message passing across a `syscall` do not happen
either. Kraken's x64 target runs the same promising machine under
`Arch.tso` (`writeSuccs` keeps its promise branch and `PromSemInf`
applies), so promises exist in the model. Every TSO store is a release,
so a promise can be fulfilled only above the thread's earlier read and
write views. Promises then add no TSO outcome, and the fix removes no
hardware behaviour on x64. This last point is expected: Kraken's x64
results are stated over promise-free `Arch.tso` runs, and no general
"TSO runs need no promise" theorem was found to cite.

**What the fix removes.**
- From the current model, on both ISAs: early visibility of a
  post-call store relative to the call itself, for example relative to
  the bytes a `write` emits. Case (a) shows hardware forbids this, so
  removing it is faithful. The current model over-approximates here,
  which is the safe direction.
- On AArch64 it also removes `MP+svceret+addr` (observed) and the load
  buffering shape `LB+svc-erets` (allowed). These are hardware
  behaviours. With the fix alone, the AArch64 target machine would be
  **stricter than the hardware** for programs with more than one thread,
  so a certificate about it would not cover real executions.
- In M1 (one thread, and the kernel model reads only the thread's own
  non-promised messages) there is no observer of either shape. The
  removed executions are then observably redundant if one-thread promise
  elimination holds (§9.0 (a)). That is expected but not proved.

**Verdict.**
- x64: the fix is faithful.
- AArch64: the fix alone is not faithful from M2 on. Faithful
  alternatives:
  - (i) The emitter places a full barrier (`dmb ish`) immediately before
    every `svc`, and `certExec` becomes a dead end at the `svc`. Hardware
    then forbids the shapes above. One proof obligation remains: on
    `Arch.armv8`, a promise of a write that is program-order after a
    `fence .sy` is never needed to reach an outcome. The fence raises
    `vrNew`/`vwNew` to the thread's earlier read and write timestamps,
    and a later fulfilment must lie above them (`writeSuccs`, `ok`). That
    kills the early promises the hardware also forbids, for example in
    `ldr x; dmb; svc; str y` against the LB partner. The cost is one
    barrier per system call, negligible beside the call itself.
  - (ii) Keep certification across system calls, and discharge
    `SvcNoProm` instead by making the kernel return the branch the
    certification run chose (`Kernel.certSuccs` over-approximates the
    returns, and the hook already requires `CertAfter`). This changes no
    semantics, but `Progress` must show the chosen return is enabled.
- In M1, the fix alone loses no observable behaviour (modulo §9.0 (a)).
  It is acceptable there only as an explicitly provisional choice, to be
  replaced by (i) or (ii) before any multi-threaded target.

**Scope of alternative (ii) (revisit material; no model change made).**
As the model stands, (ii) cannot discharge `SvcNoProm`, for two reasons.
- *Stuck after a byte.* A thread at `write` has a promise that only its
  `-EINTR` path fulfils, and its certification picks that branch:
  `certExec` offers every result whatever the kernel's progress. The kernel
  transfers one byte, and `CertAfter` passes because `certExec` ignores
  `wr`. With `wr = 1`, `sysStep` allows only the counts from 1 up, and none
  of them certifies. This configuration is reachable and has no step, so
  `Progress` fails.
- *Kernel reads raise views.* `readByte` installs a plain load's views
  (`vrOld`, `coh` of the word). Take the run: promise `y` at `p`;
  `str x` at `q > p`; `svc write(buf = x)`; `dmb ld`; `str y`. It
  certifies before the read. After the read `vrOld ≥ q`, the `dmb ld`
  raises `vwNew` to `q`, and the fulfilment at `p` fails. So certification
  is not monotone under kernel reads, even for one thread.

Model changes (A), all in `Kernel.lean`, the trusted model:
- A1. Certification knows the write's progress. At `wr = j > 0` the write
  branches of `certExec` are only the counts `j … n`, and `CertAfter`
  takes `wr`. This prunes only executions whose certification is already
  dead, so no hardware behaviour is lost. About 80–120 lines, plus the
  users of `CertAfter`.
- A2(a), recommended. `readByte` keeps the thread's views. This is a safe
  over-approximation: the kernel's read no longer orders later user
  accesses, nor raises `coh`. In M1 nothing observable changes, because
  user loads read the latest message they have not promised. About 20
  lines.
- A2(b), the alternative. `certExec` mirrors the byte loads as `.load`
  events, so that after each kernel read certification continues with
  the rest of the tree. About 300–500 lines, mostly the load-to-register
  view bookkeeping of `finishInstr`.

Lemmas (B), in `Scc/Sem`, assuming A1 and A2(a):
- B1. `certOkC_of_le`: certification survives pointwise lower thread and
  register views. `retThread` zeroes the result registers' views, while
  the certification branch sets them through `finishInstr`. It reuses
  `Sim.runTree_sim_noForeign`, `finishInstr_sim` and `stepOne_sim` with
  `TMap.idUpTo`; what is new is the `stepOneWith`/`ThreadNPC` lift.
  About 150–300 lines. The opposite direction, higher views, is false
  (the second counterexample).
- B2. `certOkC_svc_cases`: certification at a supported call with
  `wr = j` gives no promise, or an allowed `r` with `retThread t r`
  certified, or (write, `k > j`) the unchanged thread certified at
  `wr = j + 1`. About 150–250 lines.
- B3. At `exit`/`exit_group`, certification implies no promise (no
  branch). About 30 lines.
- B4. The byte step is enabled: the latest message the thread has not
  promised is readable (from `CohCoversP` and the TLatestP lemmas).
  About 60–120 lines.
- B5. The `sys_*`/`spawn_*` lemmas take the certificate instead of
  `prom = []`. About 60–100 lines.
- Consumer side: `pre_progress` without `SvcNoProm` (the kernel follows
  B2's branch), and the system-call rows with promises exempted
  (`MsgsExcept`). About 400–700 lines.

Total: about 1–1.7k lines, 600–1000 of them in `Scc/Sem`.

#### Open for hello1 (promises at kernel steps)

The one-thread consumers (`Spike/Lib/{A64,X64}Consumer.lean`) assume of
promises only `PromShared` and `WriteNoProm`. Their scope and the gaps
beyond it:
- *Pool bytes zero at the take.* `Pre` carries the pool's bytes as zero,
  which the certification lift after a take needs (`certAfter_take`). It
  holds because the consumers never reach a release site (`Nodes.noSite`):
  the loaded pool is zero and only a release writes it. A program that
  releases (the stack-grow trampoline) needs the stale-snapshot item of the
  §3.1 table (`NoRetakeAfterRelease`) and a `Pre` with released bytes.
- *`write` with promises outstanding.* `WriteNoProm`: no promise at a
  `write`. The generic converse of `sysStep_solo` fails there in two
  cases: at `wr = 0` a certification run may take a `writeTree` branch
  (the buffer loaded in one step where the kernel moves one byte per step,
  with views raised by `readByte`); at `wr > 0` (mid-write) the solo
  configuration, with no byte out, is not the real one. `ret0` writes
  only on the abort path, which its main-path fragment excludes (empty
  `AbortPath`): no state of the fragment is at a `write` (`NoWrite`, an
  `SFacts` field, from the `svc`/`syscall` nodes' call numbers), and
  `writeNoProm_of_noWrite` discharges the premise
  (`Spike/Lib/{A64,X64}SegInst.lean`). hello1's `print` writes on the main
  path, so `NoWrite` does not hold there. Open: hello1, and once for every
  accepted program, or the two cases.
- *Clone.* The handover relies on the `clone` dead end (§6, 44); hello1
  waits for it in the consumer (`Nodes.sysOk` excludes `clone` today).

M2 open items from the certification projection, beside (D):
`NoRetakeAfterRelease` (above); `Reserved tid rS`; no store to a released
range before exit.

## 10. Typing invariants

`ValRep` of `undef` holds of every word, so neither the memory relation
nor the register relation says that a source operand is defined. Several
per-construct proofs need exactly that: the target branches on a word
where the source, on `undef`, has no successor. `Scc/Sem/Typing.lean`
collects these facts, separately from §8.

- **Defined operands.** `ThreadTyped p th` is WeakCore's typing of one
  thread: some context `cx` types `th.term` (`CoreTyping.Typed`) and the
  environment realises `cx` (`TermSound.FInv`). From it:
  `ThreadTyped.add_num` (both operands of `let x = a + b` are numbers, so
  the target carry is the source sum crossing `2^64`), `ifeq_num` and
  `parity_num` (tests read numbers), `ifnull_def` (an `ifnull` test reads
  `null` or a location). Integer types are realised by one number
  (`vr_intOf`).
- **No big number.** `NoBigNumT` (the overflow part of the budget) is
  kept by a step that binds only small words (`NoBigNumT.of_frames`,
  `NoBigNumT.push`). Words loaded from memory are small under the memory
  relation (`MemRel.small`); checked results are small on their
  fall-through edge; a literal is small when below `2^64`.

**Where `SrcTyped` comes from.** WeakCore's token soundness theorem
(`TermMain.machine_tokens_mainF`, `SpawnArmZ.machine_tokens_main_spawn`)
gives `Typed` and `FInvR` at every reachable configuration, hence
`SrcTyped`. Its hypotheses include `ObligationsFX`, which contains the
certification obligations `CertWinCNX`/`CertWinPNX`. WeakCore assumes
these and does not prove them. Using the theorem therefore puts these
obligations into the correctness proof chain. This is a design decision.
The alternative is for each segment to carry the typing facts it needs
for its construct, as a compiler-side check.

**Decision: (a), WeakCore's theorem for publish-free programs.** The
choice is to take `SrcTyped` from WeakCore's token soundness theorem.
The obligations `CertWinCNX`/`CertWinPNX` are discharged, for programs
with no `publish`, by `certWinCNX_of_noPublish`/`certWinPNX_of_noPublish`
(`Scc/Sem/PubFree.lean`, in progress). Their argument: `NoHoldPubN` only
constrains a thread whose term is `let x = publish a; e`. A run invariant
in the style of `TermScope.RunScope` (every thread term and every frame
body is `publish`-free, kept by steps, promises and spawns of a program
whose declaration bodies are `publish`-free) excludes that form. Programs
that use `publish` stay outside this route until the obligations are
proved in general. Until the `SrcTyped` corollary lands, `ThreadTyped`
and its consequences are used through hypotheses (the earlier interim
choice). Nothing in `Scc/Sem/Typing.lean` imports WeakCore's token
soundness theorem yet.

**Not covered.**
- Literals: scc must reject `.lit n` with `n ≥ 2^64`. This is a
  program-side condition; otherwise `NoBigNumT` fails at the binding.
  **Front-end task** (open): the scc front end rejects such literals.
- Representable locations (the label is placed and the offset is in
  bounds) need WeakCore's per-state cell-type map, which WeakCore plans to
  provide. They are deferred.
- Facts for `case` and sum tests are not stated yet.
- Extern steps (`SrcHooks`) are outside WeakCore's theorem. With
  `SrcHooks.none` there are none.

**The rows' form** (`Scc/Sem/TypingRows.lean`). A per-construct row is
stated for every pair of a segment invariant, with no reachability, so the
typing reaches it as a guard on the source control at each instruction:
`TypedAt p [] c.term c.env`. The global proof discharges the guard from
`transfer_typedAt`: the source related to a reachable target configuration
has every thread with no type arguments typed at its control. The checked
`+` falls through with the target's sum representing `addW`
(`valRep_addW`, the result small, so `NoBigNumT.push` keeps the overflow
part) and aborts only on operands that are numbers whose sum carries
(`TypedAt.carry_nums`); the saturating `-` is exact without typing
(`valRep_subW`). `ifeq` and `parity` decide alike on both sides because a
number's representative is the number (`valRep_num`); `ifnull` does when
every placed base is positive (`TypedAt.ifnull_iff`, a hypothesis the
layout must supply). `NoBigNumT` is a clause of `R`, not a source
invariant: a source `+` may bind a big number, and only the target's abort
keeps a related source from doing so.
