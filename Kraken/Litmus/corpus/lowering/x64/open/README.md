# x64 lowering tests outside the regression run

    python3 Kraken/Litmus/litmus_tests.py --isa x64 Kraken/Litmus/corpus/lowering/x64/open

Each test here is one where Kraken is **stricter than herd** and herd is
unsound: hardware forbids the extra herd state. `../../gen.sh` generates
them and moves them here; their `.litmus.herd` is herd's real output.

The herd model is the X86_64 default of herd 7.58, `x86tso-mixed.cat`
(`herd/model.ml`: `` `X86_64 -> File "x86tso-mixed.cat" ``;
`herd7 -model x86tso.cat` refuses an X86_64 test with "Architecture mismatch").

## `R+po+poana`

diycross7 cycle `PodWW CoeNaA PodWRANa Fre`, family R:

    P0: movl $1,(x) ; movl $1,(y)
    P1: movl $2,%eax ; xchgl (y),%eax ; movl (x),%ebx
    exists ([y]=2 /\ 1:rax=1 /\ 1:rbx=0)

| | verdict | states |
|---|---|---|
| herd 7.58 | Never | `rax=0; rbx=0; [y]=1` · `rax=0; rbx=1; [y]=1` · **`rax=1; rbx=1; [y]=1`** · `rax=1; rbx=1; [y]=2` |
| Kraken | Never | the same without `rax=1; rbx=1; [y]=1` |

**herd's extra state breaks atomicity.** With `rax=1` the `xchg` read `y = 1`
from P0's store W1. With `[y]=1` that store W1 is the last write to `y`. So
the `xchg`'s own write W2 (`y = 2`) is coherence-before the write it read
from: R(xchg) rf← W1, W2 co→ W1, R and W2 the read and write of one locked
instruction. x86tso-mixed checks atomicity only as `empty rmw & (fre;coe)`.
That forbids a write between the read's source and the RMW's write, not an
RMW write placed *before* its source. Its SC-per-location axiom
(`acyclic po-loc | ca | rf`) would catch the cycle W2 co W1 rf R → W2. But
R → W2 is the RMW's intra-instruction `rmw` edge, which is not in `po`, so
`po-loc` misses it.

**Hardware forbids it.** Intel SDM Vol. 3A (253668-090US) §11.1.2.1
("Automatic Locking": the processor follows the LOCK semantics when
executing an `XCHG` that references memory) and §11.1.2.2 ("Software
Controlled Bus Locking": `XCHG`, `CMPXCHG`, `CMPXCHG16B`… locked): a locked
read-modify-write is atomic, so no other write to `y` can come between its
read and its write. §11.2.3.8 adds that "Locked instructions have a total
order". The extra state needs W2 before W1 and R after W1, which no atomic
execution gives.

**Kraken.** A locked RMW under `Arch.tso` reads the message immediately
before its own write in `y`'s timestamp order (`runTree` `.rmw`,
`Kraken/Promising/Thread.lean`), so its write is coherence-after its
source. That is SDM behaviour.

Already recorded: `../../../../KNOWN_GAPS.md` the failed-`cmpxchg` study entry ("x86
failed `lock cmpxchg` without write-back"), side notes: "herd's
`x86tso-mixed` allows a locked RMW whose write is co-before the write it read
from (CoRR+casf with `lock addl $0`), which Kraken forbids (hardware also
forbids it)." This test shows the same hole with `xchg`, and with
diycross's own R shape.
