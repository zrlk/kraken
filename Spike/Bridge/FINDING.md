# Bridge spike: Kraken runs related to WeakCore runs

This spike relates the fuel-free Kraken machine (`StepSemInf`, with
`CertOk` certification) to the WeakCore machine (`TermRun.Step`, with
`Certified`/`Solo` certification). The program is the smallest one with a
release/acquire pair:

- thread 0 runs `let u = store rel f 1 in ret ()`;
- thread 1 runs `let r = load acq f in ret r`.

It is lowered on both ISAs, and the programs come from Kraken's parsers:

| ISA | memory model | writer | reader | registers |
|---|---|---|---|---|
| AArch64 (`isaLSE2`) | `Arch.armv8` | `stlr x1, [x0]` | `ldar x2, [x0]` | `x0 = 0x1000`, `x1 = 1` |
| x64 (`isa`) | `Arch.tso` | `movq %rsi, (%rdi)` | `movq (%rdi), %rax` | `rdi = 0x1000`, `rsi = 1` |

On x64 the store and load kinds are `plain`, matching what the emitter
produces for acquire and release.

Files:

- `Common.lean`: the source program, the source steps in closed form, the
  memory relation, and the lockstep lemma.
- `Sim.lean`: the ISA-independent relation, the simulation step,
  reachability, and every `Sim` clause except progress.
- `Progress.lean`: the target invariant (`TInvG`, generic in the reader
  through `RSpec`), absence of faults, and progress, so that `Correct` holds
  without hypotheses.
- `LoopSrc.lean`, `Loop.lean`, `LoopCorrect.lean`: the spinning-reader
  variant (source program, stutter-form simulation step, view relation;
  components, progress, `Correct`).
- `A64.lean`, `X64.lean`: the instances; `A64Loop.lean`, `X64Loop.lean`:
  the instances of the spinning-reader variant. AArch64 and x64 modules
  cannot be imported together; the library globs build all of them.
- `Spike/Lib/*`: a per-construct judgement, its instances for scc's
  lowering, and a consumer (see "A per-construct judgement" below); one
  theorem for every straight-line block, applied to a whole listing (see
  "Straight-line blocks" below).

## What is proved

Everything below is free of `sorry` and new axioms. It depends only on
`propext`, `Classical.choice` and `Quot.sound`.

### The lockstep lemma (`Common.lean`)

```lean
theorem certified_of_certOk (TR : Thread I × Memory → TermRun.Cfg → Prop)
    (hstep : ∀ q q' s, TR q s → ThreadStep A tid q q' →
      ∃ s', s' ∈ TermRun.threadSteps p k arch s i ∧ TR q' s')
    (hdone : ∀ q s, TR q s → q.1.prom = [] → TermRun.noPromises s i = true)
    (h : TR (t, mem) s) (hc : CertOk A tid t mem) : TermRun.Certified p k arch s i
```

Suppose a per-thread relation is preserved by every promise-free solo step
of Kraken, each matched by one source thread step, and an empty Kraken
promise set gives an empty source promise set. Then a Kraken certification
run is replayed as a source `Solo` run. The lemma knows nothing about the
ISA or the program.

### The relation and simulation (`Sim.lean`)

The relation is `Rel F v1 st0 sW st1 fR c s`:

- **Thread map:** Kraken thread `i` is source thread `i`, with
  `c.threads = #[t0, t1]` and `s.ths = #[th0, th1]`.
- **Memory (`MemRel`):**
  - The timestamp map is the identity. Kraken timestamp 0 (the initial
    write) is the source's first message.
  - Every Kraken message is a write of `v1` (with `v1.toNat = 1`) to
    `⟨F, 8⟩`.
  - Its source counterpart writes `num 1` to label 0, offset 0.
- **Writer phase (`WPhase`):**
  - before the store: Kraken is at `st0`, the source is `writerAt P`, and
    `P` is the same promise set on both sides;
  - after the store: Kraken is at `sW`, the source is `writerDone vs P`;
  - throughout, every promise is a timestamp of memory (`PromOK`).
- **Reader phase (`RPhase`):**
  - there are no promises;
  - before the load: Kraken is at `st1`, the source is `reader0`;
  - after the load: Kraken is at `fR v`, the source is `readerDone vs w u`,
    with `w.val = num v.toNat` and `v ∈ {0, v1}`.
- **Views:** the relation constrains no views beyond these. The writer's
  views are initial on both sides before its store, so the side conditions
  of the source store are trivial (`writer_mview`, `writer_ob`: both 0).

Every ISA fact the development uses is in one structure, `Shape I F v1 st0
sW st1 fR`. It describes the two event trees: a non-exclusive store of `v1`
to `⟨F, 8⟩` followed by nothing, and a non-exclusive load of `⟨F, 8⟩`
followed by nothing.

**Theorems (all in `Spike.Bridge`):**

```lean
-- One Kraken step (instruction or promise) is one source step of the same
-- thread, certified by lockstep.
theorem sim_step (hS : Shape I F v1 st0 sW st1 fR) (hR : Rel F v1 st0 sW st1 fR c s)
    (h : StepSemInf A tid c c') :
    ∃ s', SrcSem.StepBy prog k arch tid s s' ∧ Rel F v1 st0 sW st1 fR c' s'

theorem reach (hS) (h : ReachableSemInf A c c') :
    ∀ s, Rel … c s → ∃ s', (SrcSem.ofStep prog k arch init).Run s [] s' ∧ Rel … c' s'

-- The Sim.sim clause, with trace equality (the stricter form).
theorem sim_clause_eq (hS) (rv pl Λ) :
    ∀ t0 tr t, (Target.ofBase I A rv pl).load (asmOf st0 st1 F) Λ = some t0 →
      (Target.ofBase I A rv pl).M.Run t0 tr t →
      ∃ tr' s, (SrcSem.ofStep prog k arch (· = srcInit)).Reach tr' s ∧ Rel … t.1 s ∧ obs tr = tr'

theorem sim_clause …    -- the same, with `obs tr <+: tr'` (the statement's form)

theorem components (hS) (hRg : Regs rv F st0 sW st1 fR rF rR) (hΛ : FlagIn Λ F)
    (hR : Rel … t.1 s) : Components (ExtMachine.ofBase I A rv pl) Λ (witness A rv pl F rF rR) t s

theorem correct_of_progress (hS) (hRg) (hΛ : FlagIn Λ F) (hwf : Λ.WF) (B : Budget)
    (hprog : ProgressOf A rv pl st0 st1 F) :
    Correct (Target.ofBase I A rv pl) (SrcSem.ofStep prog k arch (· = srcInit)) Λ B (asmOf st0 st1 F)
```

The Kraken-side certification analysis has three lemmas:

- **`certW_pre_shape`:** a certifiable writer before its store has either no
  promise, or exactly one, which is of its own store's message
  `⟨⟨F, 8⟩, v1, tid⟩`.
- **`certR_pre`:** a reader before its load is certifiable only with no
  promises.
- **`cert_halted`:** a certifiable thread with no next instruction has no
  promises.

So the only certifiable Kraken promise from a related configuration is the
writer's first one, of its own store. Its source counterpart is
`promise s 0 flagA (num 1) 0`:

- it has the same timestamp: the source's `mem.size` equals Kraken's
  `last + 1`;
- its message view is 0;
- it is certified by lockstep from the `CertOk` that `PromSemInf` carries.

A Kraken promise-now inside the store is the source's append. Its promise
set `(P ++ [last+1]).erase (last+1) = P` uses `PromOK`.

`components` uses this witness:

| component | value |
|---|---|
| thread map | `i ↦ i` (for `i < 2`) |
| layout injection | label `0 ↦ F`, one word |
| timestamp map | identity |
| environment | `f ↦ rF` in both threads; `r ↦ rR` in the reader (current frame, word 0) |
| marked places | none |

Every field of `Components` is proved, including `mem_rep`, `ts_mono` and
`env_rep`.

### The instances

| | AArch64 (`Spike.Bridge.A64`) | x64 (`Spike.Bridge.X64`) |
|---|---|---|
| `shape` | `Shape isaLSE2 0x1000 1 st0 sW st1 fR`, from `exec_stlr_agrees`, `exec_ldar_agrees` | `Shape isa 0x1000 1 st0 sW st1 fR`, from `exec_store_agrees`, `exec_load_agrees` |
| simulation step | `sim_step_a64` | `sim_step_x64` |
| `Sim.sim` clause (trace equality) | `sim_a64` | `sim_x64` |
| `Components` | `components_a64` (`regVal`: `x0` holds the flag reference, `x2` the value read) | `components_x64` (`rdi`, `rax`) |
| `Correct` under `layoutΛ`, any budget, given progress | `correct_a64_of_progress` | `correct_x64_of_progress` |
| progress | `progress_a64` | `progress_x64` |
| `Correct` under `layoutΛ`, any budget, unconditional | `correct_a64` | `correct_x64` |

On both ISAs, any knobs `k` and any WeakCore memory model `arch` are
allowed on the source side.

### Progress (`Progress.lean`)

`ProgressOf A rv pl st0 st1 F` (every reachable configuration has no
faulting step, and every live thread can step) is proved for any `Shape`:

```lean
theorem progressOf (hS : Shape I F v1 st0 sW st1 fR) (rv pl) : ProgressOf A rv pl st0 st1 F
theorem correct (hS) (hRg : Regs rv F st0 sW st1 fR rF rR) (hΛ : FlagIn Λ F) (hwf : Λ.WF) (B : Budget) :
    Correct (Target.ofBase I A rv pl) (SrcSem.ofStep prog k arch (· = srcInit)) Λ B (asmOf st0 st1 F)
```

The proof has three parts:

1. **A target invariant `TInv`** (`TInvG` for the reader's states `RSt`),
   preserved by every `StepSemInf` step (`tinvG_step`, `tinvG_reach`,
   `tinv_reach`):
   - writer (`WInv`): the start thread of `st0` (initial views and
     register views) with no promise or one promise of its own store's
     message; or at `sW` with no promise;
   - reader: no promise, at `st1` or at some `fR v`;
   - memory (`MsgsOK`): every message is the writer's write of `v1` to
     `⟨F, 8⟩`.
2. **No fault** (`noFaultG`): `runTree` produces an error only from a
   `.fault` leaf, and neither tree has one (`stepOne_no_error`).
3. **Every live thread can step**: the writer at `st0` either fulfils a
   promise or writes at `last + 1` with `writeOk` from its initial views
   (`writer_can_step`); the reader at `st1` reads the last message
   (`load_can_step`). Both are certified with no promise left
   (`certOk_nil`). A thread at `sW` or `fR v` with no promise is not live.

The reader enters only through `RSpec` (its steps keep its memory,
promises and states; it certifies only with no promise; no error outcome;
not halted means it can step); `rspec` is the straight-line instance,
`rspecL` the spinning one.

**Why `TInv` is separate from `WPhase`.** "No promise after the store" is
not preserved by the lockstep relation: `writer_sim` is also used for the
uncertified steps of a certification run, where the writer may finish with
promises left. The fact holds only for steps of the machine, where
`CertOk` gives it (`cert_halted`), so it lives in the target-only invariant.

`BaseProgress` states progress on the base machine as: no fault, the
configuration is final or some thread is live, and every live thread can
step. That is the form `ExtMachine.Progress` takes on the revised statement
(see "Porting to the revised statement" below), so the port touches only the
glue lemma `progress_of_base`.

## The spinning-reader variant (`LoopSrc.lean`, `Loop.lean`, `*Loop.lean`)

The reader loops on its acquire load until it reads a non-zero value:

| ISA | reader |
|---|---|
| AArch64 | `l: ldar x2, [x0]; cbz x2, l` |
| x64 | `l: movq (%rdi), %rax; cmpq $0, %rax; jz l` |

On the source the loop is a code block `spin` (`progL`). Its body loads the
flag, tests the value, and tail-calls itself on `0` (`spinBody`).

**The stutter form** (`reach_stutter`, `sim_clause_stutter`): each Kraken
step from a related pair is matched by a source run with the empty trace of
zero or more steps. Lifting this to the `Sim.sim` clause is the same as for
the lockstep form. The matching:

| Kraken step | source steps |
|---|---|
| the reader's load | one load (`head_read`) |
| a register-only instruction that stays at the test (x64 `cmp`) | none |
| the branch back to the head | two: the test, the tail call (`mid_test`, `tail_enter`) |
| the branch to the exit | one: the test |
| the writer's steps and promises | one each, as in the straight-line program (`writer_sim`, `writer_prom`) |

**What the loop adds to the relation** (`RelL`, `RPhaseL`). The second and
later loads are made with non-initial views on both sides. The source may
read only a message its read bound does not hide (`hiddenFrom`). So the
relation bounds the source reader's read-bound views by the Kraken reader's
coherence view of the flag (`VBound`): `coh flagA`, `vPreBase` and `vRd`
are all at most `getCoh ⟨F, 8⟩`. To keep that bound across a read it also
needs:

- source message views `0` (`MV0`);
- no pair accesses (`s.pairs = []`);
- no own writes of the reader (`vs.mine = []`);
- no Kraken forwarding entry for the reader (`fwdb = []`).

A Kraken read at `ts` has no flag write in `(ts, getCoh]`, so the source has
none in `(ts, bound]` (`hidden_false`). This is the first piece of the
general view relation sketched below ("source views ≤ Kraken views"),
restricted to one location.

**The ISA side** is one structure, `LoopShape I F Head Mid Exit`:

- at a loop head, one non-exclusive load of `⟨F, 8⟩`;
- at the test, `.done` trees that stay at the test, return to a head (only
  if the low 64 bits of the value are `0`) or reach the exit (otherwise);
- at the exit, no instruction.

The test is on the low 64 bits because the loaded `Val` is 128 bits wide
and the register gets `v.setWidth 64`. The relation knows `v ∈ {0, v1}`
with `v1.toNat = 1`, which is enough. On x64 the test is `cmp $0`, not
`test`: Kraken's `test` leaves AF unspecified, an `EvTree.choose 2`, which
`LoopShape` does not allow. `test` would need `md` to accept a `choose` of
`.done` leaves.

**Proved:**

| | AArch64 (`Spike.Bridge.A64Loop`) | x64 (`Spike.Bridge.X64Loop`) |
|---|---|---|
| `LoopShape` | `loopShape`, from `exec_ldar_agrees`, `exec_cbz` | `loopShape`, from `exec_load_agrees`, `exec_of_cellAt` (the `cmp`), `exec_jcc` |
| simulation step (stutter form) | `sim_step_loop_a64` | `sim_step_loop_x64` |
| `Sim.sim` clause (trace equality) | `sim_loop_a64` | `sim_loop_x64` |
| where the words live | `regsL` (`x0`, `x2`) | `regsL` (`rdi`, `rax`) |
| `Correct` under `layoutΛ`, any budget, unconditional | `correct_loop_a64` | `correct_loop_x64` |

The generic theorems are `sim_step_loop` and `sim_clause_loop`, from
`WShape` (the writer's half of `Shape`) and `LoopShape`, and in
`LoopCorrect.lean`:

- `componentsL`: the straight-line `witness` serves unchanged. The spinning
  reader's frames are the straight-line reader's (`f` bound; at the test
  and the exit also `r`), so `components_of` (the straight-line proof,
  abstracted over the reader's frame `RFrame`) applies. `RegsL` says where
  the registers hold `f` and `r` in each phase.
- `rspecL`: the spinning reader meets `RSpec`, so the generic invariant and
  progress of `Progress.lean` (`TInvG`, `tinvG_reach`, `baseProgressG`)
  apply. A reader at a loop head can always step: a load of the latest
  write is allowed whatever its views (`load_can_step`). At the test it
  takes its register-only step (`done_can_step`).
- `progressOfL`, `correctL`: progress and the assembled `Correct`.

To keep `r`'s value in `rR` at the exit, the instances' `Exit` predicates
record the registers (not just "at the end of the text").

## Which forms and promise patterns break the lockstep argument

The argument has three parts:

- **Per-thread `TR`.** The relation splits into per-thread relations,
  preserved by Kraken's promise-free solo steps.
- **Solo matching.** Each solo step is matched by a source `Solo` segment.
  The proved lemma uses exactly one thread step; generalising to a `Solo`
  run, with stutters and source promises, is mechanical, because `Solo` is
  closed under composition.
- **Promises.** At a Kraken promise, the source promises the corresponding
  message, with a view below the current memory size (`StepBy` requires
  `w < c.mem.size`).

The table below says which part each form stresses. The statuses mean:

- **Proved:** in this spike.
- **Analysed:** reasoned about from the rules, not proved.

| Form | Status | Breaks lockstep? | What it needs | Proposed `WCLowerable` clause |
|---|---|---|---|---|
| `stlr`/`ldar`, x64 plain `mov` | proved | no | — | — |
| `ldapr` (`acqPc`) | analysed | no | Read bound: Kraken's `readPre` for `acq` adds `vRel` (store-release → load-acquire order), `acqPc` does not; WeakCore's acquire `readBoundOf` adds no release view either, so the `ldapr` read bound is no stronger than WeakCore's acquire bound. Risk: the post-view on a read forwarded from the thread's own store (Kraken `readView … fwd` vs WeakCore `acqV`/`extTs`). If WeakCore's acquire bump exceeds Kraken's `acqPc` post-view, later Kraken reads are not source reads. | `load acq ↦ ldar` always; `↦ ldapr` only with a lemma that WeakCore's acquire bump on a forwarded read is ≤ Kraken's `acqPc` post-view. |
| Exclusives (`ldxr`/`stxr`, `ldaxr`/`stlxr`) as the lowering of a source RMW | analysed | the one-to-one shape breaks; the lemma survives with stutters | `ldxr` is a source stutter; the source RMW step is taken at a successful `stxr`, reading `ldxr`'s timestamp `tr`. `TR` must carry the pending `(tr, value)` (Kraken `xclb`). A failed `stxr` is a stutter. Source readability of `tr` at `stxr` time requires that no source view grows between the two. A promise of the `stxr` message is fulfilled in Kraken under `Memory.atomic`; the source RMW fulfils under `rmwAdjacent` (`stepRmwAt`'s `fulfilled` branch), which must be implied. | "An RMW lowers to `ldxr; <register-only>; stxr; cbnz → ldxr`, with no memory access or fence between the exclusives; the value returned is the `ldxr` value of the successful iteration." Proof obligation: `Memory.atomic l tid tr t → rmwAdjacent` under the timestamp map. |
| RMW re-reads (plain load, then CAS loop) | analysed | no | The plain load is a source stutter. It may grow Kraken views (`coh`, `vrOld`) beyond the source's, which is harmless under a "source ≤ Kraken" view relation. The CAS's read is the RMW's read. A failed CAS is a source failed-CAS load. It breaks only if the returned value is the first load's rather than the CAS's. | "A lowered RMW returns the value read by its last (successful) atomic; earlier plain reads are discarded." |
| x64 locked RMW (`lock xadd`/`cmpxchg`, `xchg`) | analysed | no | One Kraken `rmw` with `Arch.rmwFence` (a full fence on both sides) is one source `stepRmw` with `lockFence` on both sides. A promise of its write is fulfilled under `atomic` (Kraken) and `rmwAdjacent` (source), the same obligation as for exclusives. | Same atomicity lemma as for exclusives; no lowering restriction. |
| STP/LDP to two 8-byte words | analysed | no | One Kraken instruction makes two writes (two events) and is matched by two source stores, a `Solo` segment of length 2. Two Kraken promises are two source promises, each certified by the same lockstep. | none |
| STP/LDP to a declared 16-byte location (`isaLSE2` single access) | analysed | no for lockstep; **yes for the statement** | One Kraken message corresponds to two source messages (two words). The timestamp map is then not injective, and `Components.ts_mono` (strict) fails. Also `mem_rep` reads `t.1.mem.read? (wordLoc a) k'` at the 8-byte location `⟨a, 8⟩`, which a 16-byte message `⟨a, 16⟩` does not match. | "16-byte single-copy-atomic accesses only to source pair cells (`newBuf`/pair layout), and only through the source pair rules (`stepLoadPair`, pair stores)." Plus the statement edit below. |
| `casp` | analysed | lockstep needs source promise steps inside `Solo`; **statement as above** | One Kraken 16-byte RMW message with one promise corresponds to a source pair RMW, which writes two messages and "fulfils two promises at once, or none" (`stepRmwPair`). So one Kraken promise step is matched by **two** source promise steps. The first is certified by a `Solo` run that starts with the second promise and then replays the Kraken run. `Solo` allows this (`Solo.prom`), so the lemma generalises. | "`casp` only on source pair cells; the source pair RMW's write timestamps are adjacent and both map to the Kraken timestamp." Same statement edit. |

**Promise patterns that are fine.** A Kraken promise-now inside an
instruction is a source append. The source can always follow a promise-free
Kraken solo run with plain steps.

**Promise patterns that need more `R`.**

- **Promises to locations outside the image.** A Kraken thread may promise
  a write to an address that is not yet a placed source label: a cell the
  thread allocates later in its certification run. The source must then
  promise to the label it will allocate. That requires the label number
  (WeakCore's `lbase`/`nalloc`) and its placement to be determined at
  promise time. In this spike `certW_pre_shape` rules this out: only the
  flag is certifiable.
  - **Proposed clause:** "a lowered thread's stores in any solo run from a
    related configuration are to placed labels or to labels the thread
    allocates in that run, with placement a function of the thread's
    allocation counter (thread-local arena or reserved block)."
- **The source promise view.** Choosing `w = mem.size - 1` is safe in
  general, under a view relation where source views ≤ Kraken views and the
  timestamp map is order-preserving:
  - Kraken can fulfil promise `t` only above `writePre ⊔ coh`, which for a
    release write includes `vrOld`/`vwOld`. So everything ordered before
    the fulfilling store has Kraken view `< t`.
  - It therefore has source view `≤ t - 1`, which is the source's
    `mem.size - 1` at promise time.
  - So the source `storeMview ≤ w` and `storeOb < t` hold at the fulfil.
  - A reader of the promised message gets Kraken post-view `≥ t > w`, so
    it stays at least as constrained as the source reader.

  The spike needs only `w = 0`, because the writer's views are initial.
  Longer threads need the view relation stated as part of `R`:
  - `coh ≤ getCoh`, `vRd ≤ vrOld`, `vWr ≤ vwOld`;
  - `vPreBase ≤ vrNew ⊓ vwNew`, `vCtrl ≤ vCAP`;
  - register views ≤ register views;

  all through the timestamp map.

## Does the `Sim` shape need to change?

**For lockstep, no.** Certification is internal to the two machines' step
relations: `InstrSemInf`/`PromSemInf` carry `CertOk`, and
`TermRun.Step` and `SrcSem.StepBy` require `Certified`. `Sim` only needs
reachability, so the lockstep argument lives entirely inside the proof of
`Sim.sim`. Two remarks:

- `TermRun.Step.thread` requires `Certified` after **every** thread step,
  not only after promises. Lockstep is used there too: `certW`/`certR` in
  `sim_step`.
- Source certification runs (`Solo`) are not related by `R`, so none of the
  `Components` obligations apply to them.

**For 16-byte accesses (`casp`, single-access LDP/STP), yes.** These are the
exact edits to `Scc.Sem.Components`.

1. `ts_mono`: let the two halves of one source pair write share a target
   timestamp.

   ```lean
   ts_mono : ∀ k1 k2 k1' k2', w.ts k1 = some k1' → w.ts k2 = some k2' → 0 < k1' → 0 < k2' →
     k1 < k2 → k1' < k2' ∨ (k1' = k2' ∧ k2 = k1 + 1 ∧ k1 ∈ s.pairs)
   ```

2. `mem_rep`: read the word at `a` out of whichever target message covers
   it, rather than requiring an 8-byte message at exactly `⟨a, 8⟩`.

   ```lean
   /-- The 8 bytes at word address `a` of target message `k'` (or of the
   initial write when `k' = 0`), if that message's location covers them. -/
   def wordAt (mem : Kraken.Promising.Memory) (a : Nat) (k' : Nat) : Option Nat := …

   mem_rep : ∀ k m, s.mem[k]? = some m → ∃ k' a v, w.ts k = some k' ∧ wordAddr w.lbl m.loc = some a ∧
     wordAt t.1.mem a k' = some v ∧ ValRep w.lbl m.val v
   ```

   `wordAt mem a k' = (mem.read? (wordLoc a) k').map (·.toNat)` whenever
   the covering location is `⟨a, 8⟩`. So every 8-byte-only proof, this
   spike's included, is unchanged.

## Porting to the revised statement

The spike was first proved against an earlier `Scc.Sem` statement. It
is now proved against the revised statement; the port was as estimated
below, and nothing in the revised statement was hard. The revised statement
changes these names the spike uses:

| change | effect on the spike |
|---|---|
| `Step`, `Run`, `Progress` take the code marks `μ` (`Target.marks asm Λ`) | add `μ` to `sim_clause*`, `reach_stutter`, `correct_of_progress`, `ProgressOf`; `ofBase_step_iff`/`ofBase_run_iff` keep their shape with `μ` |
| `Progress`: `exited ∨ ((∃ live) ∧ ∀ live, can step)`; no `waiting` | `progress_of_base` uses the `∃ live` conjunct `BaseProgress` already carries (`baseProgressG`: the writer before its store or the reader before its load is live; otherwise the configuration is final) |
| `ofBase.atSys := False` | `Step.instr` needs `¬ atSys`: `id` |
| `Sim.start` without the `RouteS` hypothesis | drop `fun _ =>` in `correct_of_progress` |
| `Sim.abort`: exact trace `obs tr` | vacuous on `ofBase` (no system-call steps), unchanged |
| `Components.mem_rep` reads through `wordAt` with `ValRep … v` | `wordAt_of_read` from the existing `read?` fact |
| `Components.ts_mono` gains a pair disjunct | `.inl` of the existing proof |
| new `Components.ts_first` | only message `0` maps to timestamp `0` (identity map), so no `k2 < 0` |
| new `Components.env_total` | every variable bound to a word in any phase is `f` or the reader's `r`, both placed (`lookup_word`); `frameFv` is not needed |
| `Layout`: `abortLbl`, `growLbl`, `symbols` replace `abortPc`; `WF.aligned` at 16 | the instances' `layoutΛ` name the abort stubs `scc_abort_<idx>` (as `trivLayout`); `abortInj` by cases |

The lockstep lemma, the simulation steps (both forms), the certification
analysis and the target invariant are unchanged. The work was in
`progress_of_base` (a few lines), the `μ` arguments (mechanical), the two
new `Components` fields (`ts_first` three lines, `env_total` one lookup
lemma), and the instances' layouts.

## Statement names this spike depends on

**`Scc.Sem`:**

- `Sim` and its fields `R`, `layout`, `start`, `progress`, `sim`, `abort`,
  `explicit`; `Correct`.
- `Target`, `Target.ofBase`, `Target.load`; `ExtMachine.ofBase`,
  `ExtMachine.Run`, `ExtMachine.Progress`, `ofBase_run_iff`,
  `ofBase_step_iff`.
- `SrcSem`, `SrcSem.ofStep`, `SrcSem.StepBy`, `SrcSem.Run`, `SrcSem.Reach`;
  `LRun.step`; `obs`.
- `Witness` and its fields `thr`, `lbl`, `lsize`, `ts`, `env`, `marked`.
- `Components` and every one of its fields: `thr_total`, `thr_inj`,
  `thr_onto`, `lbl_static`, `lbl_range`, `lbl_disj`, `lbl_mem`, `mem_rep`,
  `ts_mono`, `mem_onto`, `env_rep`, `stack_pool`, `stack_disj`,
  `stack_owned`, `stack_private`, `stack_marked`, `stack_unmarked`.
- `Place`, `placeVal`, `ValRep`, `wordAddr`, `wordLoc`, `labelRange`,
  `frameEnvs`.
- `Layout` and its fields `code`, `data`, `heap`, `stackPool`, `static`,
  `image`, `abortPc`; `Layout.WF`, `Layout.regions`, `Layout.shared`.
- `Range` and `Range.Sub`, `contains`, `Disjoint`, `InSpace`, `Aligned`.
- `AbortKind.idx`, `idx_lt`, `idx_inj`; `InLayout`; `Budget`.

**WeakCore:**

- `TermRun`: `Cfg`, `TTh`, `threadSteps`, `tstep`, `promise`, `Step`,
  `Solo`, `Certified`, `noPromises`, `lookupE`.
- `Promises`: `stepStore`, `stepLoad`, `storeMview`, `storeOb`,
  `readBoundOf`.

**Kraken:**

- Machine: `ThreadStep`, `ThreadNP`, `CertOk`, `Live.Inf.InstrSemInf`,
  `PromSemInf`, `StepSemInf`, `ReachableSemInf`, `Live.Sem.promThread`,
  `stepOne`, `Config.init`, `Config.withThread`.
- Memory: `Memory.append`, `get?`, `read?`, `last`, `initVal`.
- Event lemmas (`Lower`): `stepOne_ok_iff`, `run_store_iff`,
  `run_load_iff`, `mem_writeSuccs_iff`, `mem_readSuccs`, `readSuccs_prom`,
  `finishInstr_st`, `finishInstr_relKey`.
- Row lemmas:
  - `Lower.A64`: `CellAt`, `after`, `jumpTo`, `branchTarget`,
    `exec_stlr_agrees`, `exec_ldar_agrees`, `exec_cbz`;
  - `Lower.X64`: `CellAt`, `after`, `jumpTo`, `op64`, `labelAddr`,
    `exec_of_cellAt`, `exec_store_agrees`, `exec_load_agrees`, `exec_jcc`.

## Does the stricter `R` make lockstep harder?

**1. `ts k = 0` only for the first message at its location; `ts` strictly
monotone.**

- Here the identity map satisfies both: the flag's initial message is the
  only one mapped to 0, and `ts_mono` is proved.
- Lockstep is unaffected. The per-thread `TR` used in certification need
  not contain the timestamp map. When it does (longer programs), appends on
  both sides extend it with a fresh, larger pair, which keeps it strictly
  monotone.
- The rule bites elsewhere: one Kraken message per two source messages
  (`casp`, 16-byte STP), as described above.

**2. `env` places every free variable of every frame.**

- Satisfied: `f ↦ x0`/`rdi` in both threads throughout, and `r ↦ x2`/`rax`
  after the load. `u : unit` has no words.
- It does not touch lockstep, because certification runs are not
  `R`-related.

**3. Trace equality (not just prefix).**

- Proved here (`sim_clause_eq`); both traces are empty.
- It does not interact with lockstep. Kraken's `ThreadStep` contains no
  system call and WeakCore's `Solo` contains no extern step, so a
  certification run on either side stops before any observable event.

## A per-construct judgement (`Spike/Lib`)

The proofs above relate whole programs written by hand. This section
covers a lemma library at the granularity of scc's lowering. It has a
judgement for one construct, three instances on each ISA for the code scc
emits, and a consumer that turns the judgement into `Correct`.
`correct_loop_a64` is re-derived through the library.

Files:

- `Spike/Lib/Seg.lean`: the judgement and its combinators.
- `Spike/Lib/Src.lean`: its source half (local steps, lifting, the
  overflow abort).
- `Spike/Lib/A64.lean`, `Spike/Lib/X64.lean`: the instances.
- `Spike/Lib/Thread.lean`: the consumer.
- `Spike/Lib/A64Loop.lean`: the re-derivation.

The library has about 2300 lines.

### The judgement

`Seg p lbl rd P Q` says that a code segment simulates a source term.

- `P` and `Q` are fragments of the relation for one thread (`Frag I`).
  A fragment is a predicate on a Kraken thread state and the related source
  thread's control (`Ctl`: its term and environment, one frame).
- The definition is `∃ inv ⊇ P, ∀ (s, c) ∈ inv, Out p lbl rd (inv ∨ Q) s c`.
  Every instruction from an invariant pair lands in the invariant or in the
  exit.
- An abort edge is a disjunct of `Q`, so a construct with an abort edge has
  two exits.

`Out` has one case per kind of instruction:

| case | Kraken side | source side |
|---|---|---|
| `silent` | the event tree is `.done s'` (registers, branches, private memory: the frame slots) | a `LocalRun`, zero or more local steps |
| `load` | `.load kl false ⟨A, 8⟩ (done ∘ g)` | `let x = load acq a in e`, with `a`'s word representing `A`. For every value `v` read and every word `w'` with `rd w'` that represents `v`'s low 64 bits, `(g v, ⟨e, (x, loadTy ty, [w']) :: env⟩)` is in the target fragment. |
| `store` | `.store kr false ⟨A, 8⟩ V (done s')` | `let x = store rel a b in e`, with words representing `A` and `V` |

A local step changes only the term and the environment and has exactly
one successor (`+`, a test, a tail call).

**Stuttering.** A `silent` instruction with `LocalRun.refl` is a stutter.
Slot loads and stores, `adds`/`add` and `b.cs`/`jc` without carry are all
stutters. The source steps once per construct: at the shared access, or at
the conditional branch for `+`.

**Composition.**

- `Seg.step` and `Seg.seq` compose instructions and sequences.
- `Seg.loop` builds a tail-call loop from a body whose exit includes its
  own entry.
- `Seg.seq_left` continues the normal exit and keeps an abort exit.
- `Seg.or_pre`, `Seg.mono_pre` and `Seg.mono_post` split cases and weaken.

**How it plugs into `Sim.sim` and progress** (`Thread.lean`).
`Reader p lbl F Inv Fin` is a `Seg` body with its invariant exposed
(`Reader.seg`), plus side conditions: no store, every load is of the flag,
and `Fin` is halted. The consumer reads each `Out` case once:

- **Simulation step.** `silent` is the lifted local run (`LocalRun.run`).
  `load` is one source load of the message related to the one Kraken read
  (`load_read`, `head_read` for any thread, term and environment).
- **Progress.**
  - `silent` steps by `done_can_step` and `load` by `load_can_step`.
  - `RSpec.ok` follows from `runTree_done_ok`/`runTree_load_ok`.
  - Certification (the reader never promises) holds because every step
    keeps the phase.
- **Components.** They come from where the fragments place the source
  words (`Place`).

`correctS` is `Correct` with every clause discharged, for any ISA, any
program and any reader given this way, with the writer and memory relation
of the flag program.

Writing the consumer forced three changes to the judgement. None of the
instances needed more than a renaming.

1. **The type a load binds.** It is `loadTy ty`, the type `TermRun.tstep`
   gives (`Int` for a word cell), not an arbitrary type. With an arbitrary
   type the placement of the source words (`RFrame`) cannot be read off
   the fragment.
2. **Every value read.** `Out.load` covers every value read, not only
   64-bit ones, through its low 64 bits. Certification runs from memories
   the relation does not constrain: the reader can read its own promise of
   any value. The phase must therefore be total. With "for `v < 2^64`
   only", the reader's certification argument has no next step for the
   other values.
3. **`rd`, the read side of the memory relation.** `ValRep` of `undef` is
   `True`, so if a load could bind any representing word, the source could
   read `undef`. A test of `undef` has no successor (`ifeq` on a non-number
   is `[]`), so the reader's test would be stuck. The words a load may
   bind are a parameter. The flag consumer uses `NumRd`: the flag's memory
   holds numbers.

### The instances

Each instance is a `Seg` from the sequence's entry to its exit, for
64-bit accesses at displacement 0 with register operands. The sequences
are copied as data; the library does not import the emitter.

| construct | AArch64 (`Scc/Emit/A64.lean`) | x64 (`Scc/Emit/X64.lean`) | theorem |
|---|---|---|---|
| frame slots | `[sp, #8i]`, `getReg`/`setReg` 373–378 over `ldrOff`/`strOff` 183–194 | `-8(k+1)(%rbp)`, `Frame.slotOff`/`Frame.slot` 112–119, `ld`/`st` 188–196 | `Slots` |
| `store rel` | `ldr x9,[sp,#ov]; ldr x10,[sp,#op]; stlr x9,[x10]` (540–551, `getAddr` 386–388, `storeRel` 235–236) | `mov op(%rbp),%rcx; mov ov(%rbp),%rax; mov %rax,0(%rcx)` (325–333) | `seg_store` |
| `load acq` | `ldr x10,[sp,#op]; ldar x9,[x10]; str x9,[sp,#od]` (531–539) | `mov op(%rbp),%rcx; mov 0(%rcx),%rax; mov %rax,od(%rbp)` (312–324) | `seg_load` |
| checked `+` | `ldr x9; ldr x10; adds x9,x9,x10; b.cs <abort_overflow>; str x9` (522–524, `addChecked` 148–149; stub `abortStub` 684–686, placed at 708) | `mov oa(%rbp),%rax; mov ob(%rbp),%rcx; add %rcx,%rax; jc .L<fn>.ovf; mov %rax,od(%rbp)` (299–303; stub 433–437) | `seg_add` |

The slot fragment `Slots lbl F slot st env` is the `env_rep` component for
`Place.slot`. It links to `Scc.Sem.A64.privLoad`/`Scc.Sem.X64.privLoad`
(`Slots.privLoad`) and requires:

- the frame is mapped in private memory;
- each placed variable's slot holds a word representing it;
- slots are distinct and inside the frame;
- every address a source location represents is unmapped, declared as an
  8-byte location, and outside the frame.

The checked `+` has two exits:

- **Fall-through.** The source adds once, at the conditional branch
  (`localStep_add`). `x` is bound to `addW wa wb` and placed at `od`.
- **Abort label.** The source thread is unchanged and `OvfReady`: two
  numbers whose sum is at least `2^64`. The carry of `adds` and of x64
  `add` is exactly that condition.

`abortJustified_overflow` (`Src.lean`) turns `OvfReady` into
`AbortJustified … .overflow`. Its conditions are no promises, one frame,
no type variables, and `NoBigNumT`.

### `correct_loop_a64` from the library

`Spike.Lib.A64Loop.correct_loop_a64'` has the statement of
`Spike.Bridge.A64Loop.correct_loop_a64`. It is proved as follows:

- three fragments, `HeadF`, `MidF` and `ExitF`;
- `out_head`: the `ldar` is `Out.load`;
- `out_mid`: the `cbz` is `Out.silent`, with the test plus the tail call
  (two `LocalStep`s, `ls_test` and `ls_tail`) or the test alone;
- `seg_reader`: `Seg.loop (Seg.seq …)` of the two;
- `reader` and `place`, the consumer's inputs;
- `correctS`.

No Kraken-only shape (`LoopShape`) and no hand-written source step
(`head_read`, `mid_test`, `tail_enter`) is used.

`Spike.Lib.X64Loop.correct_loop_x64'` does the same for x64, with the
statement of `Spike.Bridge.X64Loop.correct_loop_x64`: four fragments
(`HeadF`, `CmpF`, `JzF`, `ExitF`), the `movq` as `Out.load`, the `cmp` as
`Out.silent` with the source stuttering, the `jz` as the test plus the tail
call or the test alone, and `seg_reader` as `Seg.loop (Seg.seq …)` of the
three. It reuses the bridge's instruction rows; the loop has no slot code,
so the block lemma below plays no part in it.

### What the library needs from the statement

- **`undef` operands of `+`.** WeakCore's `addW` of an `undef` operand is
  `undef`, and nothing crosses a budget, but the target's carry can fire on
  any word. An abort at an `undef` operand is therefore unjustified.
  `seg_add` requires number operands. The statement or the typing must
  exclude `undef` `Int` operands at a checked `+`, or count them as
  justifying.
- **`undef` at tests.** This is the same issue as `rd` above. A source
  that reads `undef` and branches on it is stuck while the target
  proceeds. The memory relation must state what the source may read, or
  WeakCore's tests must branch on `undef`.
- **The abort under `Target.ofBase`.** `ofBase` has no system steps, so
  `Sim.abort` is vacuous there. Using the abort exit needs the canonical
  target (`ExtMachine.ofHooks` with the kernel). It also needs a segment
  from the abort label through the stub (`movImm x0, code; bl abortFn`) to
  the `exit_group` at `μ.abortAt` that keeps the source thread `OvfReady`.
- **Promises at the abort.** `AbortJustified` takes a `StepBy`, which
  needs `Certified`. The lemma takes `promises = []`. Discharging that
  needs the `Reader.cert` argument (the aborting thread's steps keep its
  promise set) for any thread, not only a read-only one.
- **`NoBigNumT`** must be an invariant of `R`. It is part of the overflow
  kind's budget, and nothing here maintains it.
- **Promise-free source threads.** `LocalRun.run` certifies each local step
  by the empty solo run, which needs `promises = []`. A source thread with
  outstanding promises needs a stutter form of lockstep certification.

### What the library needs from Kraken

- **Code segments: now from Kraken.** `CodeAt` (each directive of a
  sequence is the cell at `pc + 4j` on AArch64, `pc + j` on x64) is derived
  from Kraken's `codeAt`. `CodeAt.of_codeAt` (in `Spike/Lib/A64.lean` and
  `Spike/Lib/X64.lean`) goes through `Lower.A64.cellAt_segment4` and
  `Lower.X64.cellAt_segment`. The bridges build each `CellAt` with
  `cellAt_of_codeAt`. The abort label's address is still a hypothesis.
- **Rows: now from Kraken.** The `sp`-relative AArch64 rows with the
  alignment check (`exec_ldr_sp`, `exec_str_sp`), `exec_adds_s`, and the
  x64 carry (`exec_add_flags`, `addFlags_cf`) used to be added here. They
  are in Kraken now and the Spike copies are gone. Effective addresses go
  through `eaddr_reg_disp`/`eaddr_reg`. The `loadInt_storeInt8` copies
  stay, because Kraken's are in a namespace (`Flat.Take`) that the library
  does not open.
- **Layout facts.** These are the `stack_private` and layout facts in
  `Slots`:
  - the frame is mapped in `dmem` and 16-aligned on AArch64;
  - heap and static addresses are unmapped in `dmem`, satisfy
    `decls.AgreesAt`, and lie outside every frame.

  Kraken's loader and the statement's layout must provide them as
  invariants.


## Straight-line blocks (`Spike/Lib/A64Block.lean`)

scc's code is mostly runs of `ldr Xt, [sp, #o]`, register operations and
`str Xt, [sp, #o]` with no shared-memory event. `seg_block` proves the
`Seg` judgement for any such run, so these instructions need no
per-instruction instance. This first lemma covers straight-line code in a
fixed frame. The next two sections extend it to branches and `sp` updates
(AArch64) and to x64.

### The lemma

- **Classification** (`classify`). A directive is a slot load, a slot
  store (64-bit, scaled immediate), or a register operation (`RegOnly`:
  `add`, `sub`, `adds`, `subs`, `madd`, `msub`, `and`, `orr`, `eor`, `ubfm`,
  `sbfm`, `lslv`, `lsrv`, `asrv`, `csel`, `csinc`, `mrs`, `movz`/`movk` with
  an integer immediate, `add`/`sub`/`subs` with an integer immediate and
  not writing `sp`). Anything else is not covered.
- **All register operations in one theorem** (`interp_regOnly`). Kraken's
  own `Operation.interp` of a register operation continues with
  `regRes op m`, the machine data that `Operation.interp` itself computes
  with no labels and a dummy pc range. The proof is one case split on
  `RegOnly`. No instruction's meaning is restated; the abstract step of a
  register operation is Kraken's step.
- **The abstract state** (`AS`). It holds the registers and flags as
  Kraken has them, and the frame's slots as `Int64 → BitVec 64`.
  - `Abs` relates `AS` to the private memory.
  - `DFrame`: memory outside the frame is unchanged.
  - `arun` runs a block structurally, so `simp` evaluates it on a symbolic
    state.
- **Kraken's `exec` is never reduced.** Each cell goes through
  `execLSE2_of_cellAt_free` to `Directive.interp`, which is structural.
  The well-founded `withAddresses`/`codeAt` stays behind `CodeAt`. No
  structurally recursive copy of `withAddresses` and no custom `Decidable`
  was needed.
- **`seg_block`.** Take any pair of `P` (at the block's address, the block
  there, the frame related to some `σ`, `okBlk n blk`). Then:
  - the source stutters until the last instruction;
  - the last instruction carries a given local run of the source;
  - the exit sees machine data related to `arun blk σ`, with the memory
    outside the frame unchanged.
- **Connection to `Slots`.** `Slots.abs`, `Slots.of_abs`,
  `Slots.keep_abs` (the block writes no placed slot) and
  `Slots.bind_abs` (the block writes one free slot, for the new variable)
  do the slot bookkeeping once.
- **`seg_add'`.** It re-derives the checked `+` with its two straight-line
  parts as `seg_block` instances. The offsets are symbolic there, so
  `okBlk` comes from the frame's facts. It has the statement of `seg_add`
  (`seg_add'_type`).

### Measured on `hello.w` (first listing)

An earlier version of `A64Hello.lean` took scc's AArch64 listing of
`Scc/Test/hello.w` (`scc --arch arm -S Scc/Test/hello.w` at an
earlier revision, copied as data). It cut the listing into maximal runs of covered
instructions, each parsed by Kraken's `parseAArch64`. For each block,
`block_spec` proved two things:

- `okBlk` by `decide`;
- the closed form of `arun` on a symbolic state, by `simp` (a generated
  theorem `…_run`).

For example, emit8's `z0 = fcmp eq cnt0 nil` block yields slot 48 `= if
σ.slot 8 = 0 then 1 else 0`, with the flags of the `subs`.

| | instructions | covered | not covered: control flow / `sp` update / shared or non-frame memory / label address / system |
|---|---|---|---|
| compiled functions (`wc_*`) | 720 | 579 (80.4%) | 76 / 38 / 21 / 2 / 4 |
| runtime (`scc_rt_*`, `_start`) | 1087 | 801 (73.7%) | 134 / 43 / 48 / 44 / 17 |
| total | 1807 | 1380 (76.4%) | |

There were 275 blocks (90 in compiled functions) of 1 to 27 instructions.

- **Time.** Checking the module took 16.9 s wall time (`lake env lean`),
  of which 1.2 s was importing. That is about 57 ms per block, or 11 ms per
  covered instruction. The slowest `simp` (a 27-instruction block) took
  0.23 s.
- **Memory.** Peak RSS was 1.83 GB, against 1.74 GB for the imports alone.
- **The generic part.** `A64Block.lean` is 635 lines, including
  `seg_add'` and the generator, and checks in about 4 s.

`A64Block.lean` is kept unchanged for `seg_add'` and the `Slots` bridges.
`A64Hello.lean` now goes through `A64Flow` (below).


## Control flow and `sp` updates (`Spike/Lib/A64Flow.lean`, `Spike/Lib/X64Block.lean`)

Both ISAs now have a block lemma over a **stack region** instead of a
fixed frame, with **static offsets**:

- **`Region`** (`Spike/Lib/Region.lean`, shared by both ISAs) is a base
  address and a range `[lo, hi)` of offsets, mapped and private in `dmem`.
  An offset list (`SO`) records, for `sp`/`rsp` and some registers, their
  value as `base + offset`. `SORel` relates it to the registers.
- **`sp` updates.** `sub`/`add` of an immediate to `sp` (AArch64), and
  `push`/`pop`, `sub`/`add` of an immediate and `mov` between `%rsp` and
  `%rbp` (x64), move the static offset. A prologue and epilogue are
  ordinary block instructions. On AArch64,
  `add`/`sub` of an immediate from `sp` into another register (`sub x9, sp,
  #n` before the stack check, `add x29, sp, #n`) records that register's
  offset. Every access is decided to lie inside the region, and on AArch64
  `sp` is decided to be 16-aligned at each `sp`-based access (the region's
  base is 16-aligned by hypothesis, `Region.addr_align16`).
- **Branches as terminators.** A block may end with one branch: `b`,
  `b.cond`, `cbz`/`cbnz`, `bl`, `ret` on AArch64; `jmp`, `jcc`, `call`,
  `ret` on x64. `arun` gives the exit pc: the address after the block, a
  label, either edge of a conditional branch (as an `if` on the abstract
  flags or register), or the address `ret` reads (from `x30`, or popped
  from the region on x64). `bl`/`call` write the return address and keep
  the offsets.
- **`seg_block`.** Its exit is the `Seg` exit predicate at the abstract
  run's pc, offsets and state, with memory outside the region unchanged.
  A block that ends in a branch is therefore one `Seg`, which `Seg.seq`
  and `Seg.loop` compose like any other. No multi-block composition over
  scc's listing is proved here.
- **Generic in the layout.** The lemma, `okBlk` and `block_spec` know
  nothing about scc. The per-program part is data: a generator reads the
  listing, runs a static-offset pass per function (offsets flow along
  fall-through and branch edges; an uncovered instruction forgets the
  register it writes; a call keeps `sp` and forgets the link register),
  and writes one `block_spec name lo hi o blk` line per block. After a
  change to scc's layout only that data is regenerated.

On x64 the register operations are Kraken's `Operation.interp` again,
except those whose undefined flags are an event-tree choice (`and`, `or`,
`xor`, `test`, `imul`, shifts): the block lemma does not cover them. They
are single-instruction function nodes instead (`Out.choice`, below).

### Measured on `hello.w` (second listing)

These are the first measurements; the data has since been regenerated
(in "Whole functions" below). Then, `A64Hello.lean` and
`X64Hello.lean` held scc's listings of
`Scc/Test/hello.w` at that revision (`scc --arch arm -S` and `scc --arch
x64 -S`). Each block's `block_spec` proves `okBlk` by `decide` and the
closed form `…_run` by `simp`.

| | AArch64 instructions | covered | x64 instructions | covered |
|---|---|---|---|---|
| compiled functions (`wc_*`) | 711 | 687 (96.6%) | 634 | 576 (90.9%) |
| runtime (`scc_rt_*`, `_start`) | 1118 | 992 (88.7%) | 1030 | 844 (81.9%) |
| total | 1829 | 1679 (91.8%) | 1664 | 1420 (85.3%) |

On the same AArch64 listing, the straight-line `A64Block` covers 572
(80.4%), 820 (73.3%) and 1392 (76.1%).

What remains uncovered:

- **AArch64.**
  - In compiled functions: non-frame memory (`ldr`/`str` through a
    register base, 18), system (4), shared memory (2).
  - In the runtime: label addresses (`adrp` plus `:lo12:`, 46), non-frame
    memory (36), system (17), shared memory (13), an `sp` of unknown offset
    after the thread start's stack switch (10), the switches themselves
    (2), `nop` (2).
- **x64.**
  - In compiled functions: undefined flags (33), non-frame memory (13),
    system (4), other (8).
  - In the runtime: undefined flags (19), non-frame memory (83), system
    (33), and thread-pointer accesses, shared memory, label addresses, an
    unknown stack offset and stack switches (51).

| | blocks (compiled functions) | instructions per block | ending with a branch | check time (wall) | peak memory |
|---|---|---|---|---|---|
| AArch64 | 361 (114) | 1–14 | 213 | 35 s | 2.0 GB |
| x64 | 387 (140) | 1–19 | 193 | 26 s | 1.9 GB |

The generic parts are `A64Flow.lean` (767 lines, about 10 s),
`X64Block.lean` (885 lines) and `Region.lean` (139 lines). All theorems
use only `propext`, `Classical.choice` and `Quot.sound`.

### Two kernel limits on AArch64

The kernel checks each `…_run` proof term. Two shapes were too costly, and
the generator cuts blocks to avoid them. Both cuts only split blocks; the
coverage is the same.

- **Time.** A 28-instruction run of constant arithmetic ending in `b.eq`
  took about 45 s per block to check, and one chunk of such blocks took
  174 s. With blocks of at most 14 instructions the same code checks in
  16 s.
- **Deep recursion.** A conditional branch in the same block as a
  preceding `movk` makes the kernel report deep recursion. The smallest
  case is `movz x10, #65525; movk x10, #65535, lsl #16; subs …; b.eq`, or
  `movz` with three `movk` and `b.eq` and no `subs`. Removing the simp
  lemmas for `CondCode.interp` and `StatusFlags.subs`, or the simprocs,
  does not help. The cause is not known. The generator puts such a branch
  in a block of its own. The same happens with an unconditional `b` or a
  `cbz` after `movz; movk` (`movz; movk; b L`). `movz` alone or `movk`
  alone before the branch checks. Since the cut costs no coverage, this
  was not investigated further.

**Resolved.** Both limits came from how `block_spec` built the proof. The
kernel limit came from unfolding `AI.step`/`AI.tgt` by `rfl`. That left a
definitional gap, and closing it re-evaluated constant arithmetic under the
free `σ`, where the kernel's GMP `Nat` arithmetic is off. Non-`rfl`
equations (`noRfl`) and a pass that re-synthesizes each `ite`'s instance
remove it. Once that was fixed, `simp` itself blew up: unfolding the
`@[simp]` `StatusFlags.subs` on a known 32-bit constant cost more than
4 GB, so `block_spec` now keeps it folded. The kernel check of the
declaration also runs under the raised `maxRecDepth`. With all three,
the generator needs no cut. The 354 maximal AArch64 blocks (up to 32
instructions) check in 31 s with 2.0 GB.

### What it changes in the estimate

- **The instruction-level work.** For straight-line code, prologues,
  epilogues and the branch at the end of a block, it is now a generated
  `okBlk` and closed form per block. Per construct, what remains is:
  - the source's `LocalStep` for the operation;
  - the arithmetic from the closed form to `ValRep`;
  - relating each branch's abstract condition to the source's test;
  - the rows of the uncovered instructions (shared accesses, non-frame
    memory, label addresses, system calls, x64's undefined-flag
    operations).
- **What the re-derivation shows.** `seg_add'` (77 lines) is barely
  shorter than `seg_add` (82 lines). The instruction-level part is gone,
  but in a five-instruction construct it was never most of the proof. The
  conditional branch, the carry arithmetic and the source step are.
- **Where the saving lies.** It comes from the bookkeeping moving into
  `Slots.keep_abs`/`bind_abs` (written once) and from long blocks: up to
  14 (AArch64) or 19 (x64) instructions cost one `block_spec` line.
- **What would cut it further.** A per-IR-form `Seg` lemma (block + source
  step + value relation, generic in the operation) would make most
  constructs a few lines.
- **x64.** It has its own block lemma now, at about the same cost and
  coverage. Its undefined-flag operations needed a choice row in `Out`
  (now `Out.choice`, below).

## Whole functions (`Spike/Lib/A64Cfg.lean`, `Spike/Lib/X64Cfg.lean`)

Blocks compose into whole functions through one new rule in `Seg.lean`:

- **`Seg.cfg`**: a family of nodes `N i`, each a segment whose exit is
  some node or the graph's exit `X`, is one segment from any node to `X`.
  The graph may have loops, joins and several exits. **`Seg.exists_pre`**
  (ghost parameters) is a corollary.
- **Nodes** (`ND`, per ISA): a pc, the static offsets there and an
  invariant `J` on the abstract state and the source control. A node's
  fragment holds when the region is related to some `σ` at the node's
  offsets with `J σ c`, and memory satisfies a frame condition `F` that no
  write inside the region breaks (**`FStable`**). For a function without
  calls this is "memory outside the region as at entry". With calls it is
  any condition the callees keep too.
- **Block nodes** (`seg_nd`): the obligation is about the block's
  generated closed form only. The run must **hit** a node or an exit: same
  pc, offsets no stronger than the run's (`SO.le`, decided), and the
  node's invariant. **Given nodes** are instructions or routines whose
  segment is a hypothesis: system calls, calls, accesses the block lemma
  does not cover.

Four functions of `hello.w`'s listing (the second listing) are proved as one
`Seg` each. They cover loops, a system call, a call, a tail call, the
stack-grow path and abort exits:

| file | function | lines (blocks generated / graph / proof) | check time | peak memory |
|---|---|---|---|---|
| `A64Print.lean` | `scc_rt_print` | 277 (78 / 84 / 70) | 6.1 s | 1.9 GB |
| `X64Print.lean` | `scc_rt_print` | 238 (68 / 77 / 69) | 6.7 s | 1.9 GB |
| `A64PrintL.lean` | `wc_printL` | 304 (104 / 86 / 75) | 7.2 s | 1.9 GB |
| `X64PrintL.lean` | `wc_printL` | 315 (97 / 90 / 83) | 9.3 s | 1.9 GB |

- **Graph.** The graph section is one `ND` per node plus the invariants,
  and is mechanical given the generator's offsets.
- **Proof.** Most of the proof is one line per edge: `Hit` by `simp` on
  the closed form, plus the case split of each conditional branch. The
  rest is the given nodes. Since the generic parts are `A64Cfg.lean` and
  `X64Cfg.lean` (142 lines each), the per-function cost is about 60–80
  lines of proof on top of generated data.
- **Generator changes.** Proving the functions led to three fixes in the
  generator's offset pass:
  - offsets must be the meet over incoming edges at a join (to a
    fixpoint), not the first edge's;
  - a call keeps only the callee-saved registers;
  - a system call (and an atomic) forgets every register.

### Undefined flags (`Out.choice`, `Spike/Lib/X64Flags.lean`)

On x64, `and`/`or`/`xor`/`test`/`imul` and the shifts leave some flags
undefined. Kraken's event tree for them is a `.choose` over the flag
values: a **silent** tree (`Kraken.Promising.Lower.Silent`: no memory
events, every leaf a `.done`). The existing `Out.silent` needed a single
`.done`, so a new case was added:

- **`Out.choice`**: the instruction's tree is a `SilentTree P` and every
  state in `P` continues to the exit. The lockstep side (`sim_step_seg`,
  `rspecS`, `Reader.step`) uses `stepOne_silent_ok/_exists` and
  `stepOne_silent_no_error`. `choice_can_step` gives progress.
- **`flag_nd`**: a flag instruction is a node of its own, whose hit
  obligation is quantified over all flag values. The leaves differ only in
  flags, so the obligation is the same as a block's.
- **Coverage.** `FI` covers the register forms and the shifts by `%cl`
  (count zero included), 61 instructions of the listing. Not covered:
  32-bit `xorl` (5) and `andq $-16, %rsp` (1).
- **Use.** `X64PrintL.lean` uses `flag_nd` for its `imulq`, which was a
  hypothesis before.

### Regenerated listing

The block data (`A64Hello.lean`, `X64Hello.lean`) is regenerated from the
listing at a later revision. Since then the generator counts `ldur`/`stur`
as non-frame memory. The x64 "covered" column includes the `flag_nd`
nodes. The generators now start a function only at a label that the listing
declares a function (`.type NAME, %function`), so x64 runtime labels such as
`scc_rt_release_site` no longer start a function with offsets reset to the
entry offsets. This gained 56 x64 runtime instructions (from 965) whose
offsets were unknown before. AArch64 coverage is unchanged, but its
site blocks now carry their function's offsets.

Single-instruction nodes (counted by the generators as `nodes`, at known
offsets) now also cover label addresses and the system instructions without
an event: `si_nd` in `Spike/Lib/A64Nodes.lean` (`adrp`, `add …, :lo12:L`,
`nop`, `msr tpidr_el0`) and `Spike/Lib/X64Nodes.lean` (`leaq L(%rip)`), and
`flag_nd` now also covers the zeroing `xorl %r32, %r32`. The "covered"
columns count blocks and nodes:

| | AArch64 instructions | covered | x64 instructions | covered |
|---|---|---|---|---|
| compiled functions | 748 | 722 (96.5%) | 642 | 615 (95.8%) |
| runtime | 1236 | 1156 (93.5%) | 1143 | 1045 (91.4%) |
| total | 1984 | 1878 (94.7%) | 1785 | 1660 (93.0%) |

| | blocks (compiled functions) | check time (wall) | peak memory |
|---|---|---|---|
| AArch64 | 354 (108) | 31 s | 2.0 GB |
| x64 | 407 (139) | 25 s | 1.9 GB |

System calls are nodes as well, through a new `Out` row (`Out.sys`,
`Spike/Lib/Seg.lean`). The memory side now carries the kernel model
(`MemSide.K`). At a call it decodes, every state the kernel may resume the
thread in (`Kernel.certSuccs`) must land in the target fragment after a
local source run. The row covers only the thread's control: the kernel
step's events (output, the error flags of `write` and `clone`) and the exit
code are left out. The node lemmas are `svc_nd` (`Spike/Lib/A64Nodes.lean`)
and `syscall_nd` (`Spike/Lib/X64Nodes.lean`, `arch_prctl` excluded). The
generators split the 17 sites on each ISA by the number the code before them
sets:

| | no kernel event | number set before a label (abort exits) | `write`/`clone`, control only |
|---|---|---|---|
| AArch64 | 5 | 5 | 7 (1 in compiled functions) |
| x64 | 5 | 5 | 7 (1 in compiled functions) |

Stack switches are nodes too (`sw_nd`, `Spike/Lib/A64Switch.lean`;
`sw_nd`, `swand_nd`, `Spike/Lib/X64Switch.lean`). After a switch the
generators restart the static offsets at 0, in a region based at the new
stack pointer: the offsets carry an epoch, and edges of different epochs
meet to unknown. This removes the unknown-offset code after the thread
start's switch (10 AArch64, 7 x64 runtime instructions) and adds 4 blocks
on each ISA (358 and 411). Counting the switches and all 17 system calls:

| | AArch64 covered | x64 covered |
|---|---|---|
| compiled functions | 723 (96.7%) | 616 (96.0%) |
| runtime | 1184 (95.8%) | 1072 (93.8%) |
| total | 1907 (96.1%) | 1688 (94.6%) |

x64's thread-pointer loads (`movq %fs:k, %r`, 7 in compiled functions and 4
in the runtime) read an address the runtime owns outside the thread's
private memory. They are nodes through a further `Out` row, `Out.rtLoad`:
the source takes a local run and the thread continues for every value read,
so the memory relation only needs the load to be possible. The node lemma is
`fsld_nd` (`Spike/Lib/X64Nodes.lean`). With them x64 covers 623 (97.0%),
1076 (94.1%) and 1699 (95.2%).

x64's `ud2` (3 in compiled functions, 16 in the runtime) follows a call that
does not return or `exit_group`. It is a node whose invariant no run
satisfies (`dead_nd`, `Spike/Lib/X64Dead.lean`); the obligation moves to the
edge into it, which must not land there. Counting them, x64 covers 626
(97.5%), 1092 (95.5%) and 1718 (96.2%).

The 7 `write`/`clone` sites per ISA still need a source obligation for the
kernel step's events.

What remains uncovered:

- **In compiled functions:** non-frame memory (heap loads and stores,
  object headers), the thread-pointer load of the stack limit, a few
  system and shared accesses.
- **In the runtime:** additionally label addresses, the thread start's
  stack switch, and code after it.

All of these are given nodes in a function's graph. Each is one
hypothesis, discharged by an `Out` row for the access.

## Distance to a whole scc program

The library covers single-thread slot code in a stack region on both
ISAs, with `sp` updates and branch terminators. Whole functions compose
from generated blocks over their control-flow graph. x64's undefined
flags are covered, and there is one shared access per construct. The
consumer covers one read-only thread against one flag.

The table below is the estimate before whole functions. The revision
follows it.

| item | what it adds | size |
|---|---|---|
| Per-instruction instances | scc's IR has a few dozen instruction forms per ISA. Without automation each instance is 50–150 lines, mostly slot bookkeeping. With the block lemmas (blocks generated on both ISAs, bookkeeping in `Slots.keep_abs`/`bind_abs`), each form costs its source `LocalStep`, the closed-form-to-`ValRep` arithmetic, the link from each branch's abstract condition to the source test, and the rows of its shared accesses, about 20–40 lines. | Was about 10k lines for both ISAs; now about 2.5–3.5k (≈40 forms × 2 ISAs × 20–40 lines). A per-form `Seg` lemma generic in the operation would roughly halve that again. |
| Calls, frames, prologue/epilogue | At the block level, `sp` updates and `bl`/`call`/`ret` as terminators are covered on both ISAs. What remains: a stack of `Slots` (one region per frame, the callee restoring `sp`, which the generator assumes), and source frames: `LocalStep` and `LocalRun.run` assume `stack = []`, so they need a frame-aware form and an `Out` case for call and return. | about 1k lines |
| Runtime and abort stubs | Segments for the stubs and the runtime entry points under the canonical target and its kernel model. The `abort` clause of `Sim` via `OvfReady` and `abortJustified_overflow`. The runtime's label addresses, non-frame memory and stack switch are its uncovered instructions. | about 1k lines |
| The memory relation | A relation over all shared locations: timestamp map and views, as `VBound` here for one location. Writer-side stores and promises in the consumer (the `Out.store` case, certification by lockstep for writing threads). Messages of any value. | the largest single item, several thousand lines |
| Typing invariants | `NoBigNumT`, number operands at checked arithmetic, defined values at tests, representable locations (`Slots.heap`), all as invariants of `R` | about 0.5k lines |
| Code layout | `CodeAt` now comes from Kraken's `codeAt` through one lemma (`CodeAt.of_codeAt`). What remains are label addresses from the emitted program. | about 0.1k lines |
| N threads | Spawn and join, a consumer over any number of threads, each given by fragments | about 1k lines |

The total was on the order of 15–20k lines without automation. With the
block lemmas the per-instruction item drops from about 10k to about
2.5–3.5k, and calls/frames and code layout shrink. The total is on the
order of 8–12k lines. Most of it is now the memory relation, then the
runtime/abort stubs, N threads and frames, none of which the block lemmas
touch. The judgement's composition rules did not need to change for the
three constructs, the loops on both ISAs, or the block lemmas. The open
design points are the memory relation (`rd` and the store side) and
frames.

### Revised with whole functions

The machine side of a function is now mostly generated. Blocks and their
closed forms come from the listing; the graph is one node per label, with
offsets from the generator. The hand-written part is one line per edge
plus the given nodes, about 60–80 lines per function. The function-level
glue (`Seg.cfg`, the `Cfg` modules) is written once, and the composition
rules needed one new rule (`Seg.cfg`) and one new `Out` case
(`Out.choice`). What changes per item:

| item | before | now | why |
|---|---|---|---|
| Per-instruction instances | 2.5–3.5k | about 2–3k | Unchanged in kind: the source relation per IR form (`LocalStep`, `ValRep`, branch conditions) is still the cost. Flags no longer need special handling on x64. A per-form `Seg` lemma would roughly halve it. |
| Whole functions (new) | in the above | about 60–80 lines per function of proof on generated data | A generator for the graph and edge lines, as for the blocks, would make most of it generated as well. |
| Calls, frames | about 1k | about 1k | Unchanged. Calls are given nodes with an `FStable` frame condition, but the stack of `Slots` and the source's frames (frame-aware `LocalStep`, `Out` call/return cases) are not done. |
| Runtime and abort stubs | about 1k | about 1k, less with generated functions | `scc_rt_print` is done on both ISAs. The rest of the runtime's machine side is the same work per function. Its uncovered instructions (label addresses, non-frame memory, stack switch) remain. |
| The memory relation | several thousand | smaller, still the largest item | A relation over all locations now exists outside Spike: `MemRel` (`Scc/Sem/MemRel.lean`: `ComponentsAll.iff_memRel`, `MemRel.store/alloc/runtime_write/latest`) and per-thread coherence (`Scc/Sem/Coh.lean`: `CohCovers`, `stepOne_coh`, `stepOne_load_tlatest`, `stepOne_store_append`). Remaining: `Out` rows for heap and shared accesses in terms of them, including a runtime store outside every label with the source stuttering (`MemRel.runtime_write`), and certification for writing threads. |
| Typing invariants, code layout, N threads | about 1.6k | about 1.6k | Untouched. |

The total moves from 8–12k to about 7–10k lines. The machine side of
whole functions is now cheap; what remains is mostly the source side and
memory:

1. the per-IR-form source relation;
2. frames on both sides;
3. the `Out` rows connecting heap and shared accesses to `MemRel`/`Coh`;
4. N threads.

The first certified whole program (`hello.w`) needs all four for the
functions it calls, but for only those functions.
