# Lock-free algorithms on x86-TSO: Stage 1 bounded checks

The classical locking and lock-free algorithms of the Promising-ARM paper
(PLDI 2019, §7, Table 1) written as `.kl` programs (format:
`Kraken/Litmus/Program.lean`) in AT&T syntax and run exhaustively on
Kraken's Promising machine under the TSO profile with `krakenlitmus_x64`.

    lake build krakenlitmus_x64
    Kraken/Examples/LockFree/run_x64.sh            # all of X64/*.kl but the `# slow` ones
    Kraken/Examples/LockFree/run_x64.sh -slow      # all of X64/*.kl
    Kraken/Examples/LockFree/run_x64.sh X64/treiber2.kl
    Kraken/Examples/LockFree/run.sh -isa x64       # skips the `# slow` ones

Each file carries, in its header comment, `# flags:` (extra runner flags)
and `# expect: Always|Sometimes|Never` (the expected `Observation` word);
`run_x64.sh` runs each file with `-v` plus its flags, prints a table, and
exits non-zero on a mismatch; it skips files with a `# slow` line
(`spinlock3`, `msqueue3`) unless given `-slow`. `run.sh -isa x64` does the
same with `-fuel 300` added. To see traces, add `-witness` (violations
of a `forall`/`~exists`, witnesses of an `exists`) or `-traces` (every
final state).

Every Lean theorem about each file (whole-image and runner-exact
safety, no-fault, fault freedom, reachability, open gaps) is indexed in
[`../THEOREMS.md`](../THEOREMS.md); each file's header has the same
`Proved…`/`Open…` lines.

## Results

Single core, times wall-clock; `Configs` is the number of configurations
explored. `-sym` (symmetry reduction) is used only where all threads run
the same code with the same registers and the property is symmetric.

| Example | Threads / ops | Property | Verdict | Configs | Time | Flags |
|---|---|---|---|---|---|---|
| `spinlock2.kl` | 2 × 1 increment | counter = 2 | Always | 6,735 | 0.4 s | `-sym -fuel 300` |
| `spinlock3.kl` | 3 × 1 increment | counter = 3 | Always | 3,106,483 | 182 s | `-sym -fuel 300`, `# slow` |
| `spinlock_cmpxchg2.kl` | 2 × 1 | counter = 2 | Always | 867 | 0.1 s | `-sym -fuel 300` |
| `spinlock_cmpxchg3.kl` | 3 × 1 | counter = 3 | Always | 36,088 | 2.3 s | `-sym -fuel 300` |
| `ticketlock2.kl` | 2 × 1 | counter = 2 (proved: `ticket2_counter_envG_verbatim`, `_runner`) | Always | 1,059 | 0.1 s | `-sym -fuel 300` |
| `ticketlock3.kl` | 3 × 1 | counter = 3 (proved: `ticket3_counter_envG_verbatim`, `_runner`) | Always | 54,630 | 3.2 s | `-sym -fuel 300` |
| `dekker_broken.kl` | 2 × 1 | not (both entered ∧ counter = 1) | **Sometimes** (expected) | 29,069 | 1.5 s | `-fuel 300 -witness` |
| `dekker_mfence.kl` | 2 × 1 | same | Never | 7,005 | 0.3 s | `-fuel 300` |
| `treiber2.kl` | 2 × (push, pop) | pops = {n1, n2} (proved: `x64_treiber2_envG_verbatim`) | Always | 57,050 | 3.7 s | `-fuel 300` |
| `spsc_queue.kl` | 1 producer × 3, 1 consumer × 3, ring of 2 | consumed 1,2,3 in order (proved: `x64_spsc_envG`) | Always | 17,421 | 1.5 s | `-fuel 300` |
| `spsc_queue_early.kl` | same, consumer reads slot before index | same | **Sometimes** (expected) | 88,197 | 7.5 s | `-fuel 300 -witness` |
| `msqueue2.kl` | 1 enqueuer × 2, 1 dequeuer × 2 | dequeued n1 then n2 (proved: `x64_msqueue2_envG_verbatim`) | Always | 75,551 | 7.0 s | `-fuel 300` |
| `msqueue3.kl` | 1 enqueuer × 2, 2 dequeuers × 1 (try-once) | no duplicate, no loss, FIFO (proved: `x64_msqueue3_envG_verbatim`) | Always | 6,562,872 | 8 m 38 s, 4.8 GB | `-fuel 300`, `# slow` |
| `publish_movdqa.kl` | 1 writer × 2 16-byte `movdqa` stores, 1 reader × 1 `movdqa` load | record torn | **Never** | 38 | 0.0 s | `-fuel 300` |
| `publish_movups.kl` | same with `movups` (two 8-byte pieces) on both sides | record torn | **Sometimes** (expected) | 108 | 0.0 s | `-fuel 300` |
| `treiber_aba_tagged.kl` | tagged `{ptr, tag}` head, `movdqa` + `lock cmpxchg16b`; P0 pop, P1 pop, pop, push | ABA corruption | **Never** | 41,556 | 3.4 s | `-fuel 300` |
| `treiber_aba_untagged.kl` | same with an untagged head and `lock cmpxchgq` | ABA corruption | **Sometimes** (expected) | 15,646 | 1.1 s | `-fuel 300` |
| `mp_relay3_xchg.kl` | writer, `xchg` relay, reader (3-thread ownership relay) | reader ebx = 43 ∧ [d] = 43 (proved: `mp_relay3_xchg_envG`) | Always | 565 | 0.1 s | `-fuel 300` |
| `mp_incl.kl` | writer (`movl $42`; unlocked `incl` of the flag), reader (spin, load data) | reader ebx = 42 ∧ [d] = 42 ∧ [f] = 1 (proved: `x64_mp_incl_envGV_verbatim`; without `[f] = 1`: `x64_mp_incl_envG`) | Always | 52 | 0.1 s | `-fuel 300` |
| `mp_incl_early.kl` | same with the `incl` before the data store | reader ebx = 0 reachable | **Sometimes** (expected) | 71 | 0.0 s | `-fuel 300` |
| `treiber_pp.kl` | pusher (data store, push by `lock cmpxchgq`), popper (pop by `lock cmpxchgq`, load data) | popper r10 = n1 ∧ r11 = 1 (proved: `x64_treiber_pp_envG`) | Always | 291 | 0.1 s | `-fuel 300` |
| `treiber_pp_late.kl` | same with the data store after the push | popper reads data 0 | **Sometimes** (expected) | 579 | 0.1 s | `-fuel 300` |
| `chaselev2.kl` | owner: push 1, push 2, take ∥ thief: steal × 2 (Chase–Lev, Lê et al. PPoPP'13; fixed buffer; `mfence` in take and steal, `lock cmpxchgq` on top) | no value obtained twice, none lost (in `[top, bottom)` otherwise) | Always | 131,944 | 12.5 s | `-fuel 300` |
| `chaselev2_nofence.kl` | same without the owner's `mfence` | take and steal 2 both obtain 2 (store buffering) | **Sometimes** (expected) | 142,267 | 13.3 s | `-fuel 300` |
| `flatmap2.kl` | flat hash map, N = 4, linear probing: P0 inserts 1 then 3, P1 inserts 2 (same home slot), P2 lookup(3) then lookup(1); `lock cmpxchgq` key, plain `movq` value and loads | no key lost or duplicated, a found key has its own value or 0, lookup(3) = 33 implies lookup(1) finds 11 (no `_relaxed` twin: TSO has no weaker lowering) | Always | 372,557 | 30 s | `-fuel 300` |
| `flatmap_pair2.kl` | pair map, N = 2, `__int128` `{key, value}` slots: 2 inserters by `lock cmpxchg16b` (same home slot), 1 scanner by `movdqa` | no torn pair in the scan or in a failed CAS's old value; table {1:11, 2:22} | Always | 3,009 | 0.2 s | `-fuel 300` |

All verdicts match expectations. The `Sometimes` rows are the intended
negative examples. The vector rows have their verdicts argued in each
file's header, since herd's x86 catalogue has no vector tests and herd7 does not parse `movdqa`/`cmpxchg16b`.

### What each example checks

- **Spinlocks** (`spinlock{2,3}`, `spinlock_cmpxchg{2,3}`): mutual
  exclusion observed through a non-atomic `counter` increment in the
  critical section; `counter = n` in every final state. Acquire is a
  test-and-test-and-set with `xchgl` (implicitly locked) or a bare
  `lock cmpxchgl` loop; release is a plain `movl $0,(lock)`, which is
  correct on TSO since a store is never reordered before the earlier loads
  and stores of the critical section.
- **Ticket locks** (`ticketlock{2,3}`): `lock xaddl` on `next`, plain-load
  spin on `owner`, release with an unlocked `incl (owner)` (2) or a plain
  store of `owner+1` (3). Same property.
- **Dekker-style lock** (`dekker_broken`, `dekker_mfence`): raise own flag,
  read the other's, enter if it is down (back off otherwise, so the program
  is finite). Each thread records in `edx` whether it entered; the critical
  section increments `counter` non-atomically. Property:
  `~exists (0:edx=1 /\ 1:edx=1 /\ [counter]=1)` — both entered *and* an
  increment was lost, which is only possible if both were inside at once
  (both entering with `counter = 2` is legitimate: the second entered after
  the first lowered its flag). Without the fence this is store buffering
  and TSO allows it; with `mfence` between the store and the load it does
  not.
- **Treiber stack** (`treiber2`): nodes are static; a node is its address
  and consists of one `next` field at offset 0 (no payload needed: the
  popped node's identity is the value). Each thread pushes its node, then
  pops; the property is that the two pops return the two distinct nodes,
  i.e. no node lost and none popped twice. No reuse, so no ABA.
  Proved for every layout of the runner's image, the `.kl` code verbatim,
  by `x64_treiber2_envG_verbatim` (`Promising/SLR/EnvG/X64Treiber2Public.lean`,
  on the adjacency environment `EnvGCAdjX`; concrete runner instance in
  `X64Treiber2Concrete.lean`).
- **Michael–Scott queue** (`msqueue2`): proved for every layout of the
  runner's image, the `.kl` code verbatim, by
  `x64_msqueue2_envG_verbatim` (`Promising/SLR/EnvG/X64MsQueue2Public.lean`,
  on `EnvGCAdjX`; concrete runner instance in `X64MsQueue2Concrete.lean`).
- **Michael–Scott queue, two try-once dequeuers** (`msqueue3`): the five
  outcomes proved for every layout of the runner's image, the `.kl` code
  verbatim, by `x64_msqueue3_envG_verbatim`
  (`Promising/SLR/EnvG/X64MsQueue3Public.lean`, on `EnvGCAdjX`; concrete
  runner instance in `X64MsQueue3Concrete.lean`).
- **SPSC ring** (`spsc_queue`): two slots, plain `mov`s only. Producer
  spins on `head` while full, writes the slot, then the index; consumer
  spins on `tail` while empty, reads the index, then the slot. Property:
  the consumer's three values are 1, 2, 3 in order. Correct on TSO
  (store–store and load–load order are preserved).
  `spsc_queue_early` moves the consumer's slot read before its index check.
  This is observably wrong, but it is a program-order bug, not a TSO one:
  it fails under SC too (data read, then producer writes slot and index,
  then the index check passes). The weak-memory-relevant relaxation — plain
  loads for index and data with no acquire — is what `spsc_queue.kl`
  already is, and TSO is strong enough for it.
- **Michael–Scott queue** (`msqueue2`, `msqueue3`): sentinel `s`, nodes
  `n1`, `n2`, each one `next` field; CASes are `lock cmpxchgq` on
  `tail.next`, `tail`, `head`, everything else plain. `msqueue2` is one
  enqueuer (n1 then n2) and one dequeuer dequeuing twice (spinning while
  empty): FIFO. `msqueue3` adds a second dequeuer; each dequeues once and
  returns 0 if it observes the queue empty (`head == tail`,
  `head.next == 0`), retrying only on contention. Property: the pair of
  results is one of (n1,n2), (n2,n1), (n1,0), (0,n1), (0,0) — no node twice,
  n2 never without n1 (nothing lost), FIFO.

- **Vector publication** (`publish_movdqa`, `publish_movups`): a two-word
  record published twice and read once. `movdqa` (aligned 16 bytes) is
  single-copy atomic on processors with AVX, so the record is a 16-byte
  location (`__int128 rec`) and is never seen torn. `movups` is modelled
  as two 8-byte accesses, low word first, so the record is two 8-byte
  words (`uint64_t rec[2]`) and five of the eight reachable reads are
  torn. The `movups` reader also uses `movups`: a `movdqa` load of two
  8-byte locations is mixed-size, which the model reports instead of
  answering.
- **Tagged Treiber stack** (`treiber_aba_tagged`): the head is a 16-byte
  `{ptr, tag}` pair read with `movdqa` (split into `rax`/`rdx` through the
  private stack) and swung with `lock cmpxchg16b`, bumping the tag. P1 pops
  A, pops B and pushes A back while P0 pops; the ABA outcome (P0 installs
  B, which P1 holds) is unreachable. `treiber_aba_untagged` is the same
  with an 8-byte head and `lock cmpxchgq`: there the outcome is reachable,
  which shows the test detects ABA.
- **Message passing with an unlocked `incl` release** (`mp_incl`,
  `mp_incl_early`): P0 stores 42 to `d`, then increments the flag `f` with
  `incl` without `lock` (a load, then a store, which is a release under
  TSO); P1 spins on `f` and loads `d`. P0 is the only writer of `f`, so the
  unlocked increment loses nothing. Property: P1's `ebx` is 42, `[d] = 42`
  and `[f] = 1`. The first two are proved for all layouts by
  `x64_mp_incl_envG` (`Promising/SLR/EnvG/X64MpIncPublic.lean`), the
  writer on the load-then-release environment `EnvGLRX`; all three by
  `MpIncV.x64_mp_incl_envGV` (`LRValMpIncPublic.lean`, on `EnvGLRV`) and,
  for the code verbatim, `MpInclAbs.x64_mp_incl_envGV_verbatim`
  (`X64MpInclAbsPublic.lean`) with its `_runner` form. `mp_incl_early`
  increments before the data store; there the reader can load 0 (even
  under SC).
- **Ownership relay through `xchg`** (`mp_relay3_xchg`): the x64
  counterpart of `../AArch64/mp_relay3_swpl.kl`. P0 stores 42 to `d` and
  sets `f1` with a plain `movl`; P1 spins on `f1`, overwrites `d` with 43
  and sets `f2` with `xchgl` (an RMW release giving `d` away); P2 spins on
  `f2` and loads `d`. Property: P2's `ebx` is 43 and `[d] = 43`. Proved for
  all layouts by `mp_relay3_xchg_envG`
  (`Promising/SLR/EnvG/X64RelayXchgPublic.lean`).
- **Treiber push/pop** (`treiber_pp`, `treiber_pp_late`): the x64 port of
  `../AArch64/treiber_pp.kl`. P0 writes 1 to the node `n1`'s data word,
  links `n1.next` to the read `top` and pushes `n1` with `lock cmpxchgq`
  (retrying on failure); P1 reads `top` until non-empty, reads the node's
  `next`, pops with `lock cmpxchgq` (retrying on failure), and loads the
  popped node's data word. Property: P1 gets `n1` (`r10`) with data 1
  (`r11d`). Proved for all layouts by `x64_treiber_pp_envG`
  (`Promising/SLR/EnvG/X64TreiberPublic.lean`; concrete instance in
  `X64TreiberConcrete.lean`, which also checks that the `.kl`'s code block
  parses to the proof's two threads). The proof needs the popper's private
  memory to be empty: its loads at `%rax` are at a loaded address, so its
  layout covers every 4- and 8-byte word (`EnvG/X64_KNOWN_GAPS.md`).
  `treiber_pp_late` stores the data after the push; there the popper can
  read 0.

- **Typed headers and runner-exact theorems** (DECLS): the eleven
  `.kl` files with verbatim theorems (`spinlock2/3`, `spinlock_cmpxchg2/3`,
  `dekker_mfence`, `treiber_pp`, `treiber2`, `mp_incl`, `spsc_queue`,
  `mp_relay3_xchg`, `msqueue2/3`) declare their shared symbols with C types
  (`uint32_t` for `movl` words, `uint64_t` for `movq` words), so the runner
  declares them as sized locations at the width of the code's accesses (it
  was in legacy mode: every symbol unsized). The code blocks and verdicts
  are unchanged (configuration counts identical). Each verbatim theorem now
  has a `*_runner` companion stated for threads with the runner's
  declarations and a concrete instance from the runner's exact threads and
  initial memory (`runnerMatchesD`: declarations and initial memory
  included): `Promising/SLR/EnvG/*Runner.lean`, on the generic
  `X64DeclsLink.lean`. Since then `ticketlock3`
  (`ticket3_counter_envG_verbatim`, `_runner`), `publish_movdqa` and
  `treiber_aba_tagged` (stated with declarations) have verbatim
  theorems too, and `ticketlock2` (`ticket2_counter_envG_verbatim`,
  `_runner`, an access-timestamp invariant for its unlocked `incl (owner)`
  release). All of them: [`../THEOREMS.md`](../THEOREMS.md).

## Witness excerpts

`dekker_broken.kl` (`-witness`; the exploration is breadth first, so this
is a shortest run): P0 runs its whole critical section, then P1 reads
P0's flag and the counter as 0 and writes 1 again:

    Witness for 0:edx=1; 1:edx=1; [counter]=1;  (of interest):
    P0: movl $1,(%rsi)
        write flag0 := 1 @1
    P0: movl (%rdi),%eax
        read flag1 = 0 @0  (post-view 0)
    ...
    P0: movl (counter),%ecx
        read counter = 0 @0  (post-view 0)
    P0: movl %ecx,(counter)
        write counter := 1 @2
    P0: movl $0,(%rsi)
        write flag0 := 0 @3
    ...
    P1: movl $1,(%rsi)
        write flag1 := 1 @4
    P1: movl (%rdi),%eax
        read flag0 = 0 @0  (post-view 0)
    ...
    P1: movl (counter),%ecx
        read counter = 0 @0  (post-view 0)
    P1: movl %ecx,(counter)
        write counter := 1 @5

(P1's loads read the initial values with view 0 although P0's stores are
already in memory; no promise is needed, because a store does not raise the
thread's read view. In TSO terms all four loads executed before any store
drained, and P0's stores drained before P1's.) With `mfence`, the final state
`0:edx=1; 1:edx=1; [counter]=1` is unreachable; `0:edx=1; 1:edx=1;
[counter]=2` (sequential entry) remains.

`spsc_queue_early.kl` (`-witness`, state `1:r12=0; 1:r13=2; 1:r14=3`): the
consumer's slot read precedes the producer's write, the index check then
succeeds against the newer `tail`:

    P0: movl %r8d,(%rbx,%rdx,1)
        write buf0 := 1 @1
    P0: movl %ecx,(tail)
        write tail := 1 @2
    ...
    P1: movl (%rbx,%rdx,1),%r12d
        read buf0 = 0 @0  (post-view 0)
    P1: movl (tail),%ecx
        read tail = 1 @2  (post-view 2)
    P1: cmpl %eax,%ecx
    P1: je cempty0

## Notes, gaps and oddities

- **Bare `xchg` spin loops do not terminate in the explorer.** Every
  `xchg`, failed or not, is an RMW that appends a message, so a thread
  spinning on `xchg` while another holds the lock never repeats a state and
  the exploration is unbounded (the first `spinlock2` attempt ran for
  minutes without finishing). The spinlocks therefore read-spin first
  (test-and-test-and-set), which bounds the number of `xchg`s. A failed
  `lock cmpxchg` writes nothing, so a bare `cmpxchg` loop is fine.
- **Symbol layout.** Data symbols are laid out 0x100 bytes apart in the
  order of their first mention in the init block (`Litmus/X64.lean`,
  `symAddr`). `spsc_queue*.kl` rely on this to index the ring
  (`buf0 + (i << 8)`), since `(sym)` operands cannot take an index and
  `sym(,%reg,s)` is not recognised as a symbol mention (declare the symbol
  in the init block if you use it that way). Linked structures avoid the
  issue by making a node a single `next` cell and using the node's address
  as its value; a payload field would need the same 0x100 offset trick.
- **Symbolic immediates** `movq $n1,%rsi` resolve through the executable's
  label table as `(n1)` does.
- **`cmpq %reg,(sym)`** (memory destination compare) and `incl (sym)`
  (unlocked memory RMW, modelled as a load and a store) parse and run.
- **Certification pruning on `msqueue{2,3}`.** Having *promised* a `tail`
  write and certified alone, an enqueuer that read its own promise as `tail`
  would link the node to itself and swing `tail` forever. Two rules of the
  machine prevent this (notes 2 and 3 of
  [`../AArch64/README.md`](../AArch64/README.md)): a thread never reads its
  own outstanding promise, and a certification branch with a promise that
  can no longer be fulfilled is dropped. Together with note 1 there
  (certification succeeds when the promise set empties, not only at a
  halt), results are the same for `-fuel 64` and `-fuel 300`.
- **`-witness` for `~exists`:** prints states violating a `forall` condition,
  and states satisfying the existential core otherwise (`Litmus/X64.lean` and
  `Litmus/AArch64.lean`).
- **Labels ending in a digit** (`cempty0:`): `normalizeColons` is applied to
  the init block only (`Litmus/Program.lean`), keeping per-pc trace text
  aligned.
- **Sizes.** `msqueue3` with two *spinning* dequeuers (each loops until it
  gets a node) did not finish in 15 minutes; the try-once version above is
  the largest MS-queue instance that completes (≈9 min, 6.6 M
  configurations, 4.8 GB). `spinlock3` with `-sym` takes 3 minutes and
  3.1 M configurations, versus 2–3 s for the `cmpxchg` and ticket
  versions: the extra plain-load spin and the `xchg` messages blow up the
  state space.
- **Private stack top.** `stack N` maps `[rsp - N, rsp)`: `(%rsp)` itself
  is outside it, so a spill there is a shared access. Spill below `rsp`
  (`-16(%rsp)`).
- Comments in `.kl` files are `(* ... *)` and whole lines starting with
  `#`, which `Litmus/Program.lean` drops anywhere in the file (`# flags:`,
  `# expect:` and `# slow` lines live in the header comment).

**Reachability theorems.** Every `# expect: Sometimes` file
here has a Lean theorem: its violating (or, for `exists`, satisfying) final
state is `Reachable` from the runner's initial configuration. The file's
`# Proved reachable:` header line names the theorem
(`Promising/ReachX64*.lean`; method and status in `Litmus/KNOWN_GAPS.md`,
"Reachability theorems for the `Sometimes` LockFree examples").
