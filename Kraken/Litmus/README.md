# Running litmus tests on Kraken's weak-memory model

`krakenlitmus_aarch64` and `krakenlitmus_x64` take herd7 `.litmus` files,
run every interleaving of the threads on the Promising machine
(`Kraken/Promising/`), and print herd7's report so the two can be diffed.
`litmus_tests.py` does that diff over a whole corpus.

## Build

    lake build krakenlitmus_aarch64 krakenlitmus_x64

The binaries land in `.lake/build/bin/`.

## Run one test

    $ cd Kraken/Litmus/corpus/aarch64
    $ ../../../../.lake/build/bin/krakenlitmus_aarch64 -kinds kinds.txt -v MP+dmb.sy+po.litmus
    Test MP+dmb.sy+po Allowed
    States 4
    1:X0=0; 1:X2=0;
    1:X0=0; 1:X2=1;
    1:X0=1; 1:X2=0;
    1:X0=1; 1:X2=1;
    Ok
    Witnesses
    Positive: 1 Negative: 3
    Condition exists (1:X0=1 /\ 1:X2=0)
    Observation MP+dmb.sy+po Sometimes 1 3
    Configs 68

Reading it, line by line (this is herd7's format):

- `Test NAME KIND`: `KIND` comes from the `-kinds` file if given
  (`Allowed`/`Forbidden`/`Required`), else from the quantifier (`exists` →
  Allowed, `~exists` → Forbidden, `forall` → Required).
- `States n` and one line per reachable final state, restricted to the
  registers and locations the condition and `locations` mention. Memory
  locations print as `[x]=1;`.
- `Ok`/`No`: whether the test's expectation holds (`exists` is Ok when some
  state satisfies it, `~exists` when none does, `forall` when all do).
- `Positive`/`Negative`: states for and against the whole condition.
- `Observation NAME Always|Sometimes|Never p n`: states for and against the
  existential core, i.e. `Never` means the condition's witness is unreachable.
- `Configs` (with `-v`): configurations explored; `(certification budget
  hit)` is appended if some thread ran past `-fuel` instructions (default
  64) while being certified, which can happen with loops.
- `Fault NAME: msg` lines report an execution that reached something the
  model does not handle (an undefined register value, an unmapped private
  access); `Unsupported NAME: msg` means the test could not be set up at all
  (unknown instruction, array initialiser, …).

The same for x86 (AT&T syntax, TSO):

    $ cd Kraken/Litmus/corpus/x86_64
    $ ../../../../.lake/build/bin/krakenlitmus_x64 -v SB+mfences.litmus
    Test SB+mfences Allowed
    States 3
    0:rax=0; 1:rax=1;
    0:rax=1; 1:rax=0;
    0:rax=1; 1:rax=1;
    No
    Witnesses
    Positive: 0 Negative: 3
    Condition exists (0:rax=0 /\ 1:rax=0)
    Observation SB+mfences Never 0 3
    Configs 49

herd's 32-bit `X86` dialect (`MOV [x],$1`, `MOV EAX,[y]`, `XCHG [x],EAX`,
`MFENCE`) is accepted too; it is rewritten to AT&T on the way in.

## Exploring: witnesses and the interactive stepper

    krakenlitmus_aarch64 -witness LB.litmus     # a trace for each final state of interest
    krakenlitmus_aarch64 -traces LB.litmus      # a trace for every final state
    krakenlitmus_aarch64 -i MP.litmus           # interactive stepper

"Of interest" is a witness of an `exists`, or a violation of a `forall` /
`~exists`. A trace lists thread steps with the timestamps read and written,
promises and their later fulfilment, barriers, failed store exclusives. The
exploration is breadth first, so each trace is a shortest run. A promise
costs a step, so for loop-free threads a trace contains a promise only if no
promise-free run reaches the state:

    Witness for 0:X0=1; 1:X0=1;  (of interest):
    P0 promises y := 1 @1
    P1: LDR W0,[X1]
        read y = 1 @1  (post-view 1)
    P1: MOV W2,#1
    P1: STR W2,[X3]
        write x := 1 @2
    P0: LDR W0,[X1]
        read x = 1 @2  (post-view 2)
    P0: MOV W2,#1
    P0: STR W2,[X3]
        write y := 1 @1  (fulfils promise)

The stepper shows memory (timestamped messages), each thread's next
instruction, views and promises; `t N` lists thread N's transitions, `t N k`
takes one, `p N [k]` the same for certified promises, `a` everything, `u`
undoes, `s` shows, `q` quits. [INTERACTIVE.md](INTERACTIVE.md) is a
tutorial that walks through MP, acquire/dependency ordering and load
buffering with promises in the stepper.

Other flags: `-fuel N` (certification budget per thread, default 64),
`-sym` (symmetry reduction: sound only when the threads are interchangeable
and the property symmetric), `-promises N` (cap outstanding promises per
thread: faster, but an under-approximation), `-kinds kinds.txt`, `-v`,
`-lse2` (FEAT_LSE2: an aligned 16-byte `LDP`/`STP` of a declared 16-byte
location is one single-copy-atomic access; a Kraken-only model of that
hardware, which herd does not have, off by default).

## Programs larger than a litmus test: `.kl`

For algorithms (locks, lock-free structures) the `.kl` format keeps one
assembly listing with labels and lets threads share it:

    AArch64 Spinlock2
    { lock=0; counter=0; 0:X0=lock; 0:X1=counter; 1:X0=lock; 1:X1=counter; }
    threads { P0: worker done; P1: worker done; }
    stack 64
    code {
    worker:
      LDAXR W2,[X0]
      CBNZ W2,worker
      ...
      B done
    done:
    }
    forall [counter]=2

Each thread starts at its entry label and has halted when its pc reaches
its exit label; `stack N` gives each thread `N` bytes of private memory with
`SP`/`rsp` at the top. Both binaries accept `.kl` files; examples are under
`Kraken/Examples/LockFree/`. See `Kraken/Litmus/Program.lean` for the full
format.

## From Lean, without the front-end

`Kraken/AArch64/Examples/WeakMemory.lean` (MP with plain, release/acquire,
and barrier-plus-address-dependency variants; LB plain and with data
dependencies) and `Kraken/X64/Examples/WeakMemory.lean` (SB and
SB+mfences) build the configurations directly from programs parsed by
Kraken's parsers (`Promising.AArch64.mkState`, `Promising.X64.mkState`),
run `explore`, and state each verdict as a theorem decided by evaluation
(`native_decide`); `#guard_msgs` pins the reachable final states and a
shortest run to each weak outcome. They are the smallest starting point for
using the model from Lean. `Kraken/Examples/LockFree/Theorems{AArch64,X64}.lean`
do the same for `.kl` files through the front-end.

## Write your own test

The format is herd7's: architecture and name, an init block, the threads
as columns, a condition.

    AArch64 MyMP
    {
    0:X1=x; 0:X3=y;
    1:X1=x; 1:X3=y;
    }
     P0           | P1           ;
     MOV W0,#1    | LDAR W0,[X3] ;
     STR W0,[X1]  | LDR W2,[X1]  ;
     MOV W2,#1    |              ;
     STLR W2,[X3] |              ;
    exists (1:X0=1 /\ 1:X2=0)

- `x`, `y` are symbolic shared locations; `0:X1=x` puts the address of `x`
  in `X1` of thread 0; `x=1;` sets an initial value (default 0); a type may
  prefix either (`uint64_t 0:X0;`, `int x=1;`) and controls how the value is
  printed.
- Widths: a typed location (`int8_t` … `int64_t`, `uint*`, `int128_t` /
  `__int128` / `uint128_t`) is declared at its type's width, and an access
  at another width is reported unsupported (mixed-size, as in herd). A test
  that types no location keeps herd's width-agnostic default. Values and
  literals may be up to 128 bits, decimal or hex.
- Arrays: `int64_t a[2];` or `int a[2]={1,2};` declares one location per
  element; `a[1]` names an element (in conditions, `locations`, and as an
  address, `0:X0=a[1]`), `a={3,4}` compares the whole array.
- x86: `xmm` registers may be initialised and observed (`0:xmm0=0x...`),
  printed as one unsigned 128-bit number.
- Columns are separated by `|`, rows end with `;`; labels (`L0:`) are
  allowed inside a column. The single-thread form `P0;` followed by one
  instruction per line is accepted as well.
- Conditions: `obs=value` atoms (`1:X0=1`, `[x]=2`, `0:X1=y`) combined with
  `/\`, `\/`, `~`/`not`, parentheses; `exists`, `~exists`, `forall`;
  `locations [1:X6; x;]` adds observables to the printed states.

Running it:

    $ .lake/build/bin/krakenlitmus_aarch64 mine.litmus
    Test MyMP Allowed
    States 3
    1:X0=0; 1:X2=0;
    1:X0=0; 1:X2=1;
    1:X0=1; 1:X2=1;
    No
    ...
    Observation MyMP Never 0 3

The release/acquire pair forbids the message-passing anomaly; `Allowed` in
the first line only restates the quantifier, the verdict is `No`/`Never`.

To check against herd7 (built from `herdtools7`, see `corpus/ORACLE.txt`):

    $ herd7 mine.litmus          # same report, plus Time/Hash lines

For x86, use `X86_64 MyTest` as the header, AT&T instructions
(`movl $1,(x)`, `movl (y),%eax`, `mfence`, `lock xaddl %eax,(x)`,
`xchgl %eax,(x)`, `lock cmpxchgl %ebx,(x)`), and `0:rax` registers.

## Compare a corpus with herd7

    python3 Kraken/Litmus/litmus_tests.py Kraken/Litmus/corpus/aarch64
    python3 Kraken/Litmus/litmus_tests.py --isa x64 Kraken/Litmus/corpus/x86_64
    python3 Kraken/Litmus/litmus_tests.py --isa x64 Kraken/Litmus/corpus/x86
    python3 Kraken/Litmus/litmus_tests.py Kraken/Litmus/generated/aarch64 -v
    python3 Kraken/Litmus/litmus_tests.py --isa x64 Kraken/Litmus/corpus/x86_64-vector
    python3 Kraken/Litmus/litmus_tests.py Kraken/Litmus/corpus/aarch64-pairs
    python3 Kraken/Litmus/litmus_tests.py --lse2 Kraken/Litmus/corpus/aarch64-pairs/lse2

Each test is compared with the cached oracle `<test>.litmus.herd` (or a
hand-argued `<test>.litmus.hand` where herd cannot run the test) as a set
of states plus the `Observation` word; the summary line counts `match`,
`mismatch` and `unsupported`, and a mismatch prints the states only one side
has. `--herd PATH` produces a missing oracle file on the fly; `--fuel N`
passes the certification budget through; `--lse2` runs with `-lse2` and
compares with hand-argued `<test>.litmus.lse2` oracles instead. The exit status is non-zero on a
mismatch, so the script works as a regression test.

What is known not to match, and why, is in [KNOWN_GAPS.md](KNOWN_GAPS.md).

## Instruction coverage

AArch64: the existing Kraken instruction set plus `LDAR/LDAPR/STLR` (+B/H),
`LDXR/LDAXR/STXR/STLXR` (+B/H), `CAS*`, `SWP*`, `LDADD/LDCLR/LDEOR/LDSET/
LDSMAX/LDSMIN/LDUMAX/LDUMIN` (+A/L/AL, +B/H), `STADD/STCLR/STEOR/STSET`,
`DMB`/`DSB` (SY/LD/ST and the ISH/OSH/NSH variants), `ISB`.
x64: the existing set plus `mfence/lfence/sfence`, `lock` on
`add/sub/and/or/xor/inc/dec/neg/not/xadd/cmpxchg`, `xchg`, `xadd`, `cmpxchg`.
x64 vector accesses to shared memory: aligned 16-byte `movaps/movapd/movdqa`
(and VEX.128) as one atomic access, `lock cmpxchg16b` as a 16-byte RMW,
other vector accesses as 8-byte pieces (`corpus/x86_64-vector`, hand-argued
since herd has no vector instructions).
Not covered: `LDXP/STXP/CASP`, `btc/bts/btr`, mixed-size accesses, EVEX
(see KNOWN_GAPS.md).
