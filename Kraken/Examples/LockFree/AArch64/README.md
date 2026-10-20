# Lock-free algorithms on AArch64, bounded (Stage 1)

The classical examples of the Promising-ARM paper (PLDI 2019, §7, Table 1)
as `.kl` programs (format: `Kraken/Litmus/Program.lean`), run exhaustively
on Kraken's Promising machine with `krakenlitmus_aarch64`. Each file states
the algorithm, the shape of the code, the property and the expected
verdict in its header; `# flags:` and `# expect:` lines drive
[`../run.sh`](../run.sh).

    lake build krakenlitmus_aarch64
    Kraken/Examples/LockFree/run.sh            # the fast ones (< ~1 min each)
    Kraken/Examples/LockFree/run.sh -slow      # everything

All runs below use `-v -fuel 300` plus the file's flags; `-sym` only where
every thread runs the same code with the same role and the condition is
symmetric. Times are wall-clock on a 64-core workstation (single-threaded
explorer); `Configs` is the number of configurations explored.

Every Lean theorem about each file (whole-image and runner-exact
safety, no-fault, reachability, liveness, open gaps) is indexed in
[`../THEOREMS.md`](../THEOREMS.md); each file's header has the same
`Proved…`/`Counterexample…`/`Open…` lines.
`THEOREMS.md` is generated: edit `../tools/inv.py`, then run `python3 Kraken/Examples/LockFree/tools/gen_md.py` from the repository root (its "Regenerating" section lists the `#check` step).

## Results

| Example | Threads / ops | Sync | Verdict | Configs | Time | Flags |
|---|---|---|---|---|---|---|
| `spinlock2.kl` | 2 × (lock, counter++, unlock) | `LDAXR/STXR`, `STLR` | Always (ok) | 6 028 | 0.4 s | `-sym` |
| `spinlock3.kl` | 3 × same | same | Always (ok) | 494 433 | 26 s | `-sym` |
| `spinlock_relaxed2.kl` | 2 × same, release = `STR` | `LDAXR/STXR`, `STR` | **Sometimes** (expected violation, `[counter]=1`) | 26 346 | 1.9 s | `-sym` |
| `spinlock_relaxed_acq2.kl` | 2 × same, acquire = `LDXR` | `LDXR/STXR`, `STLR` | **Sometimes** (expected violation, `[counter]=1`) | 9 484 | 0.7 s | `-sym` |
| `spinlock_swp2.kl` | 2 × same, TTAS | `SWPA`, `LDR` spin, `STLR` | Always (ok) | 2 166 | 0.3 s | `-sym` |
| `spinlock_swp3.kl` | 3 × same | same | Always (ok) | 606 252 | 39 s | `-sym` |
| `ticketlock2.kl` | 2 × same | `LDADDA`, `LDAR` spin, `STLR` | Always (ok) | 2 810 | 0.2 s | `-sym` |
| `ticketlock3.kl` | 3 × same | same | Always (ok) | 162 883 | 9 s | `-sym` |
| `ticketlock_al2.kl` | 2 × same, ticket by `LDADDAL` | `LDADDAL`, `LDAR` spin, `STLR` | Always (ok) | 1 154 | 1.0 s | `-sym` |
| `ticketlock_al3.kl` | 3 × same | same | Always (ok) | 54 630 | 3.7 s | `-sym` |
| `ticketlock_relaxed2.kl` | 2 × same, spin = `LDR` | `LDADDA`, `LDR` spin, `STLR` | **Sometimes** (expected violation, `[counter]=1`) | 3 948 | 0.3 s | `-sym` |
| `treiber_pp.kl` | 1 push ∥ 1 pop (retry) | `LDAR`, `CASAL` | Always (ok) | 323 | 0.05 s | |
| `treiber_pp_relaxed.kl` | same, `LDR`/`CAS` | none | **Sometimes** (expected: pops n1 with data 0) | 2 075 | 0.1 s | |
| `treiber2_nodes.kl` | 2 × (push own node, pop), no data word | `LDAR`, `CASAL` | Always (ok) | 51 736 | 3 s | |
| `treiber2.kl` | 2 × (write data, push, pop, read data) | `LDAR`, `CASAL` | Always (ok) | 1 062 593 | 66 s, 1.4 GB | |
| `treiber2_arm.kl` | same, Arm-minimal annotations | push `LDR`+`CASL`, pop `LDAR`+`CAS` | Always (ok) | 1 062 593 | 73 s | |
| `treiber2_relaxed.kl` | same, no ordering | `LDR`, `CAS` | did not finish (25 min, 28 GB); with `-promises 1` (incomplete, diagnostic only): **Sometimes**, lost node (`0:X10=0`) and stale data, 2 745 951 configs, 155 s | — | — | `# slow` |
| `spsc_queue.kl` | producer 3 items ∥ consumer 3, 2 slots | `LDAR`/`STLR` on head/tail | Always (ok) | 36 241 | 3.7 s | |
| `spsc_queue_relaxed2.kl` | 2 items, tail published with `STR` | `LDAR`, `STR` tail | **Sometimes** (expected violation, stale 0) | 72 198 | 5 s | |
| `spsc_queue_relaxed3.kl` | 3 items, same | same | **Sometimes** (expected violation, all three slots can be stale) | 4 185 329 | 274 s, 5 GB | `# slow` |
| `msqueue1.kl` | 1 enqueue ∥ 1 dequeue (retry) | `LDAR`, `CASAL` | Always (ok) | 1 914 | 0.2 s | |
| `msqueue_relaxed1.kl` | same, plain `CAS` | `LDAR`, `CAS` | **Sometimes** (expected violation, dequeues data 0) | 12 364 | 1 s | |
| `msqueue2.kl` | 1 enqueuer × 2 ∥ 1 dequeuer × 2 (FIFO) | `LDAR`, `CASAL` | Always (ok) | 79 779 | 8 s | |
| `msqueue3.kl` | 1 enqueuer × 2 ∥ 2 dequeuers × 1 | `LDAR`, `CASAL` | Always (ok) | 10 954 030 | ~15 min, 12 GB | `# slow` |
| `msqueue_relaxed2.kl` | 1 enqueuer × 2 ∥ 1 dequeuer × 2, plain `CAS` | `LDAR`, `CAS` | did not finish (25 min, 12 GB); with `-promises 1` (incomplete, diagnostic only): **Sometimes**, stale data in either dequeue, 315 042 configs, 68 s | — | — | `# slow` |
| `mp_relay3.kl` | writer ∥ relay ∥ reader: data, flag f1, relay writes d, flag f2 | `STLR` f1, `LDAR` spin + `STLR` f2, `LDAR` spin | Always (ok); proved for all layouts (`mp_relay3_envG`, `SLR/EnvG/RelayPublic.lean`) | 367 | 0.1 s | |
| `mp_relay3_swpl.kl` | same, relay releases f2 with `SWPL` | `STLR`, `LDAR` spin + `SWPL`, `LDAR` spin | Always (ok); proved for all layouts on `EnvGC` (`mp_relay3_swpl_envG`, `SLR/EnvG/RelaySwplPublic.lean`; release-RMW limit lifted) | 367 | 0.1 s | |
| `spinlock_swpl2.kl` | 2 × (lock, counter++, unlock), TTAS, release by `SWPL` | `SWPA`, `LDR` spin, `SWPL` | Always (ok); proved for all layouts on `EnvGC` (`swpl_counter_envG`, `SLR/EnvG/SwplLockPublic.lean`; first lock with an RMW release) | 2 166 | 0.2 s | `-sym` |
| `spinlock_swpl3.kl` | 3 × same | same | Always (ok); same theorem | 606 252 | 41 s | `-sym` |
| `chaselev2.kl` | owner: push 1, push 2, take ∥ thief: steal × 2 (Chase–Lev, Lê et al. PPoPP'13; fixed buffer) | push `STLR`; take `STR`, `DMB ISH`, `LDR`, `CASAL`; steal `LDAR`, `DMB ISH`, `LDAR`, `CASAL` | Always (ok): no value obtained twice, none lost (in `[top, bottom)` otherwise) | 145 941 | 12 s | |
| `chaselev2_nofence.kl` | same, no `DMB ISH` in take | same minus the owner's fence | **Sometimes** (expected: store buffering, take and steal 2 both obtain 2: `0:X10=2; 1:X10=1; 1:X11=2`) | 155 016 | 12 s | |
| `flatmap2.kl` | flat hash map, N = 4, linear probing: P0 inserts 1 then 3, P1 inserts 2 (1 and 2 collide), P2 lookup(3) then lookup(1) | `CASAL` key, `STLR` value; `LDAR` key and value | Always (ok): no key lost or duplicated, a found key has its own value or 0, lookup(3) = 33 implies lookup(1) finds 11 | 267 090 | 18 s | |
| `flatmap2_relaxed.kl` | same, reader loads `LDR` | `CASAL`, `STLR`; `LDR` | **Sometimes** (expected: causality only, e.g. `2:X11=33; 2:X12=0`: reads val[2] = 33, then key[0] = 0 @0) | 343 394 | 23 s | |
| `flatmap_pair2.kl` | pair map, N = 2, `{key, value}` per slot in `uint64_t tab[4]`: 2 inserters (same home slot), 1 scanner | `CASPAL` insert, `LDP` scan | **Sometimes**, Kraken weaker than hardware: torn `{k,0}`/`{0,v}` (two-event `CASP`; `LDP` on two 8-byte cells is two loads even with `-lse2`); never on FEAT_LSE2 hardware | 246 399 | 15 s | `-lse2` |
| `flatmap_pair2_casp.kl` | same, scanner reads with a failing `CASPAL` | `CASPAL` only | **Sometimes**, Kraken weaker than hardware: torn reads come from the two-event `CASP` alone (Arm ARM §B2.2.1: `CASP` is 128-bit single-copy atomic) | 451 053 | 30 s | `-lse2` |

Properties, in short: the locks protect a counter and the property is
`counter = #threads` (a lost update is the visible symptom of a broken
critical section). The stack and queue examples record what each thread
popped/dequeued in registers and the condition says the multiset of
results is the expected one (distinct non-null nodes, the data written
before the push/enqueue, FIFO order where there is a single dequeuer).

## Expected violations: witness excerpts

`-witness` prints one trace per final state violating a `forall`. The
traces below are from the runs above, condensed to the memory accesses
(timestamps `@n` are positions in the promising machine's memory;
"promises" are writes committed early; addresses the tool prints as
numbers are shown by name). The exploration is breadth first, so each
trace is a shortest run to its final state.

### `spinlock_relaxed2.kl` — plain `STR` release

P0's unlock (`lock := 0 @2`) is promised *before* its counter write
(`counter := 1 @3`); P1 acquires the lock reading `@2`, and its counter
read, bounded only by view 2, still sees the initial value.

    P0: LDAXR W2,[X0]          read lock = 0 @0
    P0: STXR W4,W3,[X0]        write lock := 1 @1
    P0 promises lock := 0 @2
    P0: LDR W5,[X1]            read counter = 0 @0
    P0: STR W5,[X1]            write counter := 1 @3
    P0: STR WZR,[X0]           write lock := 0 @2  (fulfils promise)
    P1: LDAXR W2,[X0]          read lock = 0 @2  (post-view 2)
    P1: STXR W4,W3,[X0]        write lock := 1 @4
    P1: LDR W5,[X1]            read counter = 0 @0  (post-view 2)
    P1: STR W5,[X1]            write counter := 1 @5

### `spinlock_relaxed_acq2.kl` — `LDXR` instead of `LDAXR`

The release is intact (`counter @2` before `lock := 0 @3`), but P1's
non-acquire lock read does not raise its read view, so the counter read
is satisfied from `@0`:

    P0: STR W5,[X1]            write counter := 1 @2
    P0: STLR WZR,[X0]          write lock := 0 @3
    P1: LDXR W2,[X0]           read lock = 0 @3  (post-view 3)
    P1: STXR W4,W3,[X0]        write lock := 1 @4
    P1: LDR W5,[X1]            read counter = 0 @0  (post-view 0)

### `ticketlock_relaxed2.kl` — plain `LDR` spin on `owner`

Same shape: the ticket is taken with `LDADDA` (post-view 1), the spin read
sees `owner = 1 @3` but, being a plain load followed only by a branch, it
does not order the critical section's load:

    P0: STR W5,[X2]            write counter := 1 @2
    P0: STLR W4,[X1]           write owner := 1 @3
    P1: LDADDA W6,W3,[X0]      read next = 1 @1 / write next := 2 @4
    P1: LDR W4,[X1]            read owner = 1 @3  (post-view 3)
    P1: LDR W5,[X2]            read counter = 0 @0  (post-view 1)

### `spsc_queue_relaxed2.kl` — tail published with `STR`

The producer promises `tail := 1 @1` ahead of the data store `@2`; the
consumer reads `tail = 1`, then slot 0 before the data landed (final state
`1:X10=0; 1:X11=2`):

    P0 promises tail := 1 @1
    P0: STR W3,[X7]            write buf := 1 @2
    P0: STR X4,[X2]            write tail := 1 @1  (fulfils promise)
    ...
    P1: LDAR X5,[X2]           read tail = 1 @1  (post-view 1)
    P1: LDR W10,[X7]           read buf = 0 @0  (post-view 1)

### `msqueue_relaxed1.kl` — plain `CAS` on `tail.next`

The paper's bug, at the smallest size: the enqueuer's swing of `tail` and
its link `d.next := n1` are promised (`@1`, `@2`) before its data store
`n1 := 1 @3`; the dequeuer reads `tail` and the link, and reads the
node's data as 0:

    P0 promises tail := n1 @1
    P0 promises [d.next] := n1 @2
    P0: STR W9,[X2]            write n1 := 1 @3
    P0: CAS X5,X2,[X8]         write [d.next] := n1 @2  (fulfils promise)
    P0: CAS X5,X2,[X1]         write tail := n1 @1  (fulfils promise)
    P1: LDAR X4,[X1]           read tail = n1 @1  (post-view 1)
    P1: LDAR X5,[X8]           read [d.next] = n1 @2  (post-view 2)
    P1: LDR W7,[X5]            read n1 = 0 @0  (post-view 2)
    P1: CAS X6,X5,[X0]         write head := n1 @4

### `treiber_pp_relaxed.kl`, `treiber2_relaxed.kl`

Same mechanism through `top`: with a plain `CAS` in push the data (and
`next`) stores are not ordered before the publication of the node; the
popper pops `n1` and reads data 0 (and, with two threads, can read a
stale `next` and lose a node).

## Which annotations the Treiber stack needs on Arm

`treiber2_arm.kl` is the Arm-minimal version: push reads `top` with a
plain `LDR` (a stale value only makes the `CAS` fail and retry) and links
with `CASL` (release: it publishes the node's data and `next`); pop reads
`top` with `LDAR` (acquire: the following `next`/data reads are ordered
after the push's release) and swings it with a plain `CAS` (nothing to
publish — in this instance; a pop that frees or reuses the node would need
release). It explores exactly the same number of configurations as the
`CASAL`-everywhere version and the verdict is the same. Removing the
release on push or the acquire on pop (`treiber_pp_relaxed.kl`,
`treiber2_relaxed.kl`) breaks it. Proved: `treiber2_arm_envG`
and its whole-image and runner-exact forms
(`Promising/SLR/EnvG/Treiber2Arm*.lean`, `A64Treiber2Arm*.lean`). The plain
pop `CAS` writes `top` non-release, so `top`'s release predicate must be pure
and carries nothing; the history comes from each thread's own write set of
`top` instead (`Litmus/KNOWN_GAPS.md`, "Uncovered").

## Notes on the explorer and `.kl` format

1. **Certification succeeds when all outstanding promises are fulfilled** (`certify` in
   `Kraken/Promising/Machine.lean`), matching the paper's certification rule:
   a promise-free run does not need to reach a halt to certify its promises.
   This matters when a thread cannot finish alone (e.g. the SPSC producer
   with 3 items and 2 slots, which must wait for the consumer); writes after
   the promise set becomes empty are still collected as promise candidates.
2. **A thread does not read its own outstanding promise** (`readSuccs` in
   `Thread.lean`). Doing so would raise `coh` past the promise's timestamp,
   after which `fulfil` is impossible, so that state is dead and is not
   offered (otherwise the Michael–Scott enqueuer's certification runs would
   read their own pending link, take the helping path, link the node to
   itself and spin writing `tail`).
3. **Dead promises end certification branches** (`Thread.hasDeadPromise`):
   a promise whose timestamp is ≤ `coh`, `vwNew` or `vCAP` can never be
   fulfilled, so certification prunes the branch immediately rather than
   running to the fuel limit (e.g. when a dequeuer helps `tail` forward on
   the strength of the enqueuer's pending link and the enqueuer observes the
   new `tail` before performing the link).
4. A pure `SWPA` spin loop (`while (swap(1)) {}`) has an **infinite state
   space** in the promising machine: every failed swap appends a new
   message, so there is no repeated configuration. The SWP spinlock is
   therefore written test-and-test-and-set (`SWPA`, then spin on `LDR`
   while the lock is held), which is what Linux/Rust spinlocks do anyway.
   The same would hold for any spin that writes.
5. **Early-promisable plain stores dominate the state space.** `treiber2`
   with the per-node data word explores 1.06 M configurations; without it
   (`treiber2_nodes.kl`) 52 k. The data store can be promised at any
   point of the run and each placement is a different memory. A
   promise-order reduction (promise a write no earlier than the first
   step that can observe it) would help every example here.
6. `.kl` format: the parser drops lines starting with `#` (`# flags:`,
   `# expect:` and `# slow` are read by `run.sh`). `normalizeColons` applies
   to the init block only so that code labels ending in a digit (`enq1:`) stay
   on their own line, and trace texts are computed per directive.
7. Parser coverage was sufficient: `LDAR/STLR/LDAXR/STXR/SWPA/LDADDA/
   CAS/CASL/CASAL/CBZ/CBNZ/B.cond/CMP/EOR imm/ADD/SUB/MOV` all parsed.
   Atomics take `[Xn]` only, so `tail.next` is addressed through an
   `ADD X8,X3,#8` (plain `LDR/STR` take `[Xn,#8]`). Node fields are at
   offsets inside a symbolic location's 256-byte slot: undeclared
   addresses read 0 initially but cannot be named in the condition, so
   data-structure results are checked through registers.
8. Witness traces print the trace for every *violating* final state only
   (`-witness`), which is what one wants for `forall`; `-traces` prints
   all. The `showPc` text past the end of a thread's code prints as
   `pc=…` (harmless).
9. `msqueue3.kl` (10.9 M configs) needs ~12 GB and ~15 minutes;
   `msqueue_relaxed2.kl` and `treiber2_relaxed.kl` (relaxed variants have
   many more promise opportunities) did not finish within 25 minutes
   (12 GB and 28 GB resident when killed). The smallest instances
   (`msqueue_relaxed1.kl`, `treiber_pp_relaxed.kl`) show the same
   violations in about a second, and `-promises 1` finds them in the
   larger instances too (reported in the table as diagnostics only: a
   promise cap is an under-approximation, so it can show a violation but
   never prove its absence).
   Memory is the limit before time: the visited set holds every
   configuration (each with its own copy of memory and views). The search
   order does not change that: `msqueue3` peaks at 12.1 GB breadth first
   (the default) and 12.3 GB depth first (peak RSS, `/usr/bin/time -v`).

Generated files: `msqueue*.kl` are produced by `gen_msqueue.py` (unrolled
enqueue/dequeue bodies); edit the generator, not the output.

**Reachability theorems.** Every `Sometimes` file has
a Lean theorem: the violating final state is `Reachable` from the runner's
initial configuration (`Promising/ReachA64*.lean`, named in each file's
`# Proved reachable:` line). `spinlock_relaxed_acq2` and
`ticketlock_relaxed2` need no promise and hold for every fuel. The other
seven (`*_relaxed*`) need a promise step, so the kernel replays promise
certification (`Promising/ReachCertCore.lean`); they are stated for the
runner's fuel 300 (`Litmus/KNOWN_GAPS.md`, "Reachability theorems for the
`Sometimes` LockFree examples").

**Typed headers and runner-exact theorems.** The headers of
`treiber_pp`, `treiber2`, `treiber2_arm`, `treiber2_nodes`, `msqueue{1,2,3}`,
`mp_relay3(_swpl)`, `spsc_queue`, `spinlock2`, `spinlock_{swp,swpl,cas}{2,3}`
and `ticketlock(_al){2,3}` declare their shared symbols with a C type
(`uint64_t` for the pointer words `top`/`head`/`tail` and the spsc indices,
`uint32_t` for data words, locks, counters and flags), so the runner's
declarations are strict sized (`Decls.StrictSized`). A mixed-size access to a
declared symbol is then a fault, not an independent location. The cells
the code reaches only by offset (a node's `next` at `n+8`, spsc slot 1 at
`buf+8`) stay undeclared; each header says so in a note. Explorer verdicts
and configuration counts are unchanged for every typed file. The
eighteen files with a `Proved from the runner's exact configuration` line
have a theorem whose initial configuration has the runner's declarations
and initial memory, checked against the runner by a `runnerIsD`
`#guard_msgs #eval`:
- seven files: `treiber_pp`, `treiber2`, `msqueue{1,2,3}`,
  `mp_relay3(_swpl)` (`Promising/SLR/EnvG/A64Whole*Runner.lean`);
- ten files, six families: `treiber2_nodes`
  (`A64WholeTreiber2NodesRunner.lean`), `spinlock_cas{2,3}`
  (`A64CasRunner.lean`), `spsc_queue` (`A64SpscWholeRunner.lean`),
  `spinlock_swpl{2,3}` (`A64SwplRunner.lean`), `ticketlock{2,3}` and
  `ticketlock_al{2,3}` (`A64TicketRunner.lean`), all in
  `Promising/SLR/EnvG/`;
- one file: `treiber2_arm` (`A64Treiber2ArmRunner.lean`);
- one family: `spinlock_swp{2,3}` (`A64SwpRunner.lean`). This needed a new
  EnvG proof, `SwpEnvG.swp_counter_envG` (`SwpEnvG*.lean`), with the
  statement of the cell-route `swp_counter_public`. Its no-fault and
  program-level fault freedom at the runner's declarations are in
  `A64SwpNoFault.lean`.

`spinlock2` is typed but has no runner-exact theorem. Note: `msqueue*.kl`
carry typed declaration lines and `Proved` header lines on top of the
`gen_msqueue.py` skeleton.

**No fault at the runner's declarations.** For the
fixed-layout files, `spinlock_{cas,swpl}{2,3}`, `ticketlock(_al){2,3}`,
`mp_relay3(_swpl)` and `spsc_queue`, each thread's rule at `decls = ds` also
has its no-fault (`*_runner_noFault`, with a `_concrete` instance at the
runner's declarations; `Promising/SLR/EnvG/A64NoFaultD{Locks,Relay,Spsc}.lean`).
The rule carries an extra address run (`AddrSafeA`: the thread's text in an
environment that accepts only the program's shared words), so every access
is one of those words, and the declarations agree with `decls = {}` on each
(`Decls.AgreesOnA`, closed by `decls_agrees_on_a`; spsc slot 1 at `buf+8` is
undeclared and agrees too). Not covered: the pointer programs (`treiber*`,
`msqueue*`), whose accessed addresses depend on values.

**Program-level fault freedom at the runner's declarations.**
For the same fixed-layout files and for the pointer programs `treiber_pp`,
`treiber2`, `treiber2_nodes` and `msqueue{1,2,3}`, no configuration reachable
from the runner's exact start (declarations and initial memory included),
under any architecture and with promises, has a faulting step
(`Config.FaultFree`; `*_runner_faultFree` with a `_concrete` instance,
`Promising/SLR/EnvG/A64FaultFreeFixed.lean` and
`Promising/SLR/EnvG/MemValsA64*.lean`). The pointer programs use a value
invariant: every shared pointer word (`top`, `head`, `tail`, the nodes'
links) holds `0` or a node, so every dereference is inside the program's
words. For `msqueue*` that includes the null node's link `0 + 8`, an
undeclared word (see `Litmus/KNOWN_GAPS.md`).
The same holds for `treiber2_arm` (`treiber2_arm_envG_runner_faultFree`,
`Promising/SLR/EnvG/MemValsA64Treiber2Arm.lean`, with treiber2's value
invariant). For every file with both a runner-exact safety theorem and a
`*_runner_faultFree`, `*_runner_safe_faultFree` (with `_concrete` or
`_concreteN`, `Promising/SLR/EnvG/RunnerSafeFFA64.lean`) states both
conclusions at once, at the union of the two theorems' hypotheses.
