# The interactive stepper: a tutorial

`krakenlitmus_aarch64 -i test.litmus` (or `krakenlitmus_x64 -i`, or a `.kl`
program) drops you into a stepper over the Promising machine. This is the
way to *understand* an outcome rather than just learn whether it is
reachable: you drive the threads yourself, see what each instruction may do
and why, and watch views and memory change. It follows the informal
presentation of the model in §4 of the Promising-ARM/RISC-V paper, and the
examples below are the paper's.

The commands, which the prompt reminds you of:

| command | effect |
|---|---|
| `s` | show the configuration: memory, each thread's next instruction, views, promises |
| `t N` | list the transitions thread `N` may take now |
| `t N k` | take transition `k` of thread `N` |
| `p N` | list the promises thread `N` may make now |
| `p N k` | take promise `k` of thread `N` |
| `a` | list every transition of every thread |
| `u` | undo the last transition |
| `q` | quit |

## 1. Memory is a list of timestamped writes

Start with message passing (`Kraken/Litmus/corpus/aarch64/MP.litmus`):
thread P0 writes `x := 1` then `y := 1`; thread P1 reads `y` then `x`. Is
`y = 1, x = 0` possible?

    $ .lake/build/bin/krakenlitmus_aarch64 -i Kraken/Litmus/corpus/aarch64/MP.litmus
    memory:
      @0: initial
    P0: MOV W0,#1
        vrNew=0 vwNew=0 vrOld=0 vwOld=0 vCAP=0 vRel=0
        coh[] prom=[]
    P1: LDR W0,[X1]
        vrNew=0 vwNew=0 vrOld=0 vwOld=0 vCAP=0 vRel=0
        coh[] prom=[]

Memory starts with the initial write of every location at timestamp `@0`.
Each thread shows its next instruction and its *views*: timestamps that
record what it has already seen. Everything is 0.

Run P0 to the end (`t 0 0` takes the only transition each time):

    > t 0 0
      took: P0: MOV W0,#1
    > t 0 0
      took: P0: STR W0,[X1] | write x := 1 @1
    > t 0 0
      took: P0: MOV W2,#1
    > t 0 0
      took: P0: STR W2,[X3] | write y := 1 @2
    > s
    memory:
      @0: initial
      @1: x=1 (P0)
      @2: y=1 (P0)
    P0: halted
        vrNew=0 vwNew=0 vrOld=0 vwOld=2 vCAP=0 vRel=0
        coh[x:1 y:2] prom=[]
    P1: LDR W0,[X1]
        ...

A store *appends a message* to memory at a fresh timestamp. Nothing is ever
overwritten: `x=1` sits at `@1`, `y=1` at `@2`, and the initial values are
still there at `@0`. P0's `coh` view says the newest write it knows of for
`x` is `@1` and for `y` is `@2`.

Now P1. A load does not simply return "the current value"; it may read any
write to the location that is not already superseded from this thread's
point of view. Ask what P1 may do:

    > t 1
      0: P1: LDR W0,[X1] | read y = 0 @0  (post-view 0)
      1: P1: LDR W0,[X1] | read y = 1 @2  (post-view 2)

P1 has seen nothing yet, so it may read the initial `y` (`@0`) or P0's
write (`@2`). Take the latter — this is the interesting half of the
outcome:

    > t 1 1
      took: P1: LDR W0,[X1] | read y = 1 @2  (post-view 2)
    > t 1
      0: P1: LDR W2,[X3] | read x = 0 @0  (post-view 0)
      1: P1: LDR W2,[X3] | read x = 1 @1  (post-view 1)

Having read `y = 1`, P1 may *still* read the old `x = 0`. That is the
weak behaviour of MP on Arm: two independent loads are not ordered. Take
transition 0 and the configuration is final with `1:X0=1; 1:X2=0`.

Why was the stale read allowed? Look at P1's views after `s`: reading `y`
at `@2` gave the load a *post-view* of 2, which went into `vrOld` (the
oldest-read bookkeeping) and `coh[y]`, but **not** into `vrNew`, the view
that constrains *later* loads. A plain load constrains nothing after it.

## 2. What a barrier or an acquire does to the views

Undo back to before P1's second load (`u`), or restart with a variant. In
`MP+rel+acq` P0's second store is `STLR` (release) and P1's first load is
`LDAR` (acquire). Run P0 to the end and let P1 read `y = 1` as before, then
look at P1:

    > t 1 1
      took: P1: LDAR W2,[X3] | read y = 1 @2  (post-view 2)
    > s
    ...
    P1: LDR W0,[X1]
        vrNew=2 vwNew=2 vrOld=2 vwOld=2 vCAP=0 vRel=0
        coh[y:2] prom=[]
    > t 1
      0: P1: LDR W0,[X1] | read x = 1 @1  (post-view 2)

The acquire pushed its post-view 2 into `vrNew` and `vwNew`: every later
access of P1 must now read at or after timestamp 2 in the sense that no
write to its location with timestamp ≤ 2 may be skipped. The only write
to `x` is `@1 ≤ 2`, so the initial `x = 0` is no longer readable — the
list of transitions has a single entry. That is the model's rendering of
"an acquire load orders everything after it".

A `DMB SY` on P0 plus an *address dependency* on P1 gives the same
single-entry list for a different reason. Run `-i` on
`Kraken/Litmus/generated/aarch64/MP+dmb.sy+addr.litmus`, step P0 through
(`DMB SY` shows as `fence sy`), let P1 read `y = 1`, then:

    > t 1 0
      took: P1: EOR W2,W0,W0
    > t 1
      0: P1: LDR W4,[X1,W2,SXTW] | read x = 1 @1  (post-view 2)

`W0` was written by the load of `y` and carries that load's view, 2; the
`EOR` copies it to `W2`; the final load uses `W2` in its address, so its
pre-view is at least 2 and, as above, `x = 0` is unreadable. Dependencies
are tracked as views on registers, syntactically: `EOR W2,W0,W0` is zero
but still depends on `W0`, exactly as the architecture says.

## 3. Promises: how load buffering happens

Load buffering (`LB.litmus`): P0 reads `x` then writes `y := 1`; P1 reads
`y` then writes `x := 1`. Can both reads see 1? On Arm, yes — each
thread's store may become visible before its load. The machine explains
this with *promises*: a thread may append a write it has not executed yet,
provided it can certify that, running alone, it would indeed perform it.

    $ .lake/build/bin/krakenlitmus_aarch64 -i Kraken/Litmus/corpus/aarch64/LB.litmus
    > p 0
      0: P0 promises y := 1 @1
    > p 0 0
      took: P0 promises y := 1 @1
    > s
    memory:
      @0: initial
      @1: y=1 (P0)
    P0: LDR W0,[X1]
        vrNew=0 vwNew=0 vrOld=0 vwOld=0 vCAP=0 vRel=0
        coh[] prom=[1]

P0 has not moved — its next instruction is still the load — yet `y=1` is
in memory at `@1`, and P0 has an outstanding promise `prom=[1]` that it
must fulfil later. Now P1 can read it and run to the end:

    > t 1 1
      took: P1: LDR W0,[X1] | read y = 1 @1  (post-view 1)
    > t 1 0
      took: P1: MOV W2,#1
    > t 1 0
      took: P1: STR W2,[X3] | write x := 1 @2

And P0 reads P1's write:

    > t 0
      0: P0: LDR W0,[X1] | read x = 0 @0  (post-view 0)
      1: P0: LDR W0,[X1] | read x = 1 @2  (post-view 2)
    > t 0 1
      took: P0: LDR W0,[X1] | read x = 1 @2  (post-view 2)
    > t 0 0
      took: P0: MOV W2,#1
    > t 0
      0: P0: STR W2,[X3] | write y := 1 @1  (fulfils promise)
      1: P0: STR W2,[X3] | write y := 1 @3

The store has two options: *fulfil* the promise at `@1`, or write a fresh
message at `@3` and leave the promise dangling. Only the first leads to a
final configuration (a thread with an unfulfilled promise is never final,
and the explorer prunes such branches by certification); take it:

    > t 0 0
      took: P0: STR W2,[X3] | write y := 1 @1  (fulfils promise)
      (final configuration)

Both threads read 1. Notice the order of events in memory: `y=1 @1`
*before* `x=1 @2`, although P0 "executed" its store last. Timestamps are
the coherence order, not execution order.

Why can P0 fulfil at `@1` after reading `x` at `@2`? The fulfil rule asks
that the store's *pre-view* — the join of the views of its address and data
registers and of `vwNew`, `vCAP` — be below the promised timestamp. `W2`
comes from `MOV W2,#1`, view 0; the load's view 2 went into `W0`, which the
store does not use. Try the dependent variant (`LB+datas` in the generated
corpus, where the store writes the loaded register): after the same
promise and reads, `t 0` offers only the fresh write — the promise can no
longer be fulfilled, and the behaviour is forbidden. That is how a data
dependency forbids load buffering in this model.

## 4. Store forwarding and exclusives

Two more things you will meet:

- A thread reading its own earlier store sees it with the store's
  *pre-view* rather than its timestamp — the `fwdb` ("forward bank")
  entry. That is why `SB+rfi-pos` under TSO lets a thread read its own
  write and still read an old value from another location.
- A store exclusive (`STXR`) lists a success and a failure transition. The
  success is offered only if the thread's last `LDXR` was to the same
  location and no other thread wrote it in between (`atomic`); the failure
  is always offered, because the architecture allows spurious failure. In
  a `.kl` spinlock you can watch the `xclb` field appear after `LDAXR` and
  disappear after the `STXR`.

## 5. Programs

`-i` works on `.kl` programs too (`Kraken/Examples/LockFree/*/*.kl`). With
more than a handful of instructions the useful pattern is: run the
exhaustive explorer with `-witness` to get a trace of the outcome you care
about, then replay its first steps in `-i` and look at the views at the
point where the "impossible" read becomes available. `s` at that point
usually shows which view is *not* as large as you assumed — a plain store
where a release was intended, or a dependency that the hardware does not
recognise.
