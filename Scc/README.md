# scc: WeakCore to assembler

`scc` reads a WeakCore program (`.w`, WeakCore's concrete syntax) and writes
GNU assembler for a freestanding static Linux binary: `_start`, raw system
calls, no libc.

> **Status: the emitter is not verified.**  An emitted program is trusted
> only through a certificate (`Scc/Test/certify.sh`).  A compiler theorem
> covers the single-declaration fragment `Accepted0` at any layout that passes
> the placement check, and one program, `Scc/Test/ret0.w`, is certified end to
> end at its linked AArch64 and x86-64 executables (`Scc/RELEASE.md`).  Any
> other output should be treated as untrusted.

## Usage

```
lake build scc scc_x64 scc_arm
.lake/build/bin/scc [--arch x64|arm] [--host linux|raw] [--gc none] [-o out.s | -o - | -S] [--report] [--cert c.lean] [--blocks b.lean] [--code c.lean] prog.w
.lake/build/bin/scc --check c.lean
```

`lake build scc scc_x64 scc_arm` builds three executables in `.lake/build/bin`: the
compilers `scc-x64` and `scc-arm` (one per architecture: Kraken's x64 and
AArch64 syntaxes share names, so no Lean module can import both emitters) and
the driver `scc`, which runs the one `--arch` selects with the same arguments,
standard streams and exit status.  Keep the three together (name all three
targets: `lake build scc` alone does not rebuild stale `scc-x64`/`scc-arm`);
`scc-x64` and `scc-arm` take the same options (and refuse an `--arch` other
than their own).

**Memory and time.**  One module, `WeakCore/TermStep.lean`, needs about
6.5 GB of memory to build, even with `LEAN_NUM_THREADS=1` (about 3 minutes);
under a 4 GB per-process cap it is killed, so a build from a fresh checkout
needs more than 4 GB.  Every other module builds in less (the next largest,
`WeakCore/TermPlant.lean`, needs about 4.2 GB).  Measured on a fresh clone
with lake's default parallelism on 64 cores: `lake build scc scc_x64
scc_arm` takes about 40 s (144 jobs) and `lake build
Spike.Test.Ret0LinkedX64` about 18 minutes (743 jobs).  A parallel build
runs several Lean processes at once; to bound the total, build serially
(`LEAN_NUM_THREADS=1` with lake restricted to one CPU, since lake runs one
job per available CPU, e.g. `LEAN_NUM_THREADS=1 taskset -c 0 lake build Scc
Spike`; about 33 minutes for the last 242 of 1151 modules, on one core).

| option | meaning |
|---|---|
| `--arch x64` (default) | x86-64 with BMI1 (`tzcnt`), AT&T syntax |
| `--arch arm` | AArch64 with FEAT_LSE2 (`isaLSE2`): acquire `ldar`, release `stlr`, atomics `swpal`/`ldaddal`, no 64-bit `ldp`/`stp`, no sub-word store |
| `--host linux` (default) | a static Linux binary; `--host raw` is not implemented |
| `--gc none` (default) | a bump allocator that never frees; no other collector exists yet |
| `-o out.s` | output file (default: `prog.s` next to `prog.w`) |
| `-o -`, `-S` | write the assembly listing to standard output; diagnostics and `--report` then go to standard error only, so `scc -S prog.w \| as -o prog.o` works |
| `--report` | list every `Int` `+` site (all keep their overflow check), marking those that index facts bound |
| `--cert c.lean` | also write a certificate for the compilation to `c.lean` (see below; not a correctness proof) |
| `--blocks b.lean` | also write the block data of the assembly to `b.lean`: one `block_spec` command per straight-line block, with its function's stack region, its static offsets and its address (label + byte offset; on x64 also its instructions' sizes) (`Scc/Cert/Blocks.lean`), and the coverage statistics to `b.lean.json`; on AArch64 also the placement data of the compiled functions to `b.place.lean`: their nodes, IR registers' frame slots, and the source variables and term at each node (`Scc/Cert/Place.lean`) |
| `--code c.lean` | (x64 and AArch64) also write a self-contained Lean file that embeds the assembly (on x64 with GNU `as`'s instruction sizes and label offsets), parses it as the canonical loader does (the parse checked by `#guard`), and checks in the kernel that every block of the block data is code at its label and offset (`Scc.Cert.Rt.A64.blocksIn`, `Scc.Cert.Rt.X64.blocksIn`, one `kernel_rfl` check) and that the layout of its static link (`Scc.Cert.Link`) is well formed, has its abort labels in the program and passes the loader's checks (`decide +kernel`; `Scc/Cert/Blocks.lean`, `code`, `codeX64`; `Scc/Cert/LinkA64.lean`, `Scc/Cert/LinkX64.lean`) |
| `--check c.lean` | check a certificate: `lake env lean c.lean` in the Kraken package, with `lake` from `$LAKE` (default `lake`); exit status 0 when it checks, 1 when it does not |
| `--help` | usage |

Exit status: 0 success; 1 an error in the program, reported as
`file:line:col: error: message`; 2 a usage error or an option that is not
implemented.

Building and running a program, from the repository root, with the output
in a temporary directory: AArch64 (`qemu-aarch64` on an x86-64 host),

```
T=$(mktemp -d)
.lake/build/bin/scc --arch arm -o $T/hello.s Scc/Test/hello.w
clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld -o $T/hello $T/hello.s
qemu-aarch64 -cpu max $T/hello
```

and x64:

```
.lake/build/bin/scc -o $T/hello.s Scc/Test/hello.w
as -o $T/hello.o $T/hello.s && ld -static -o $T/hello $T/hello.o && $T/hello
```

## Certificates

> **The output is still uncertified.**  No certificate states, let alone
> proves, that the assembler program behaves as the WeakCore program does
> (its `correct` theorem is a commented-out placeholder).  A program that
> gets no certificate, or a file marked not certifiable, has nothing checked
> about it beyond `scc`'s own static checks.

`scc --cert c.lean prog.w` writes, besides `prog.s`, a Lean file
(`Scc/Cert/Gen.lean`).  Its module docstring lists what it establishes and
what it does not; in short, it

* embeds `prog.w` and `prog.s` verbatim as string literals, with their SHA-256
  digests in comments;
* re-runs `scc`'s frontend, lowering and emitter on the embedded source at
  elaboration time and checks that the result is exactly the embedded
  assembler text: a `#guard`, i.e. a reproducibility check by evaluation, not
  a proof;
* re-parses the embedded text with Kraken's parser at elaboration time
  (`Scc/Cert/X64.lean`, `Scc/Cert/Arm.lean`) and proves the architecture's
  lowerability predicate of the parsed program by `decide +kernel`: on x64
  `Scc.Emit.X64.ProgramWCLowerable` (`Scc/Emit/X64Lowerable.lean`: every
  memory RMW is locked, no `movnti`), on arm Kraken's `Program.WCLowerable`;
  on x64 it also checks GNU `as`'s instruction sizes and label offsets
  against the parsed program (`sizes_ok`);
* reads the source as a term (`prog_src`, checked against the frontend by a
  `#guard`) and proves by `decide +kernel` that it is in the fragment the
  first compiler theorem covers (`prog_accepted`, `Scc.Lower.Accepted0`) or
  that it is not (`prog_not_accepted`);
* proves the placement check `placeOK` of `scc`'s output for `prog_src`
  (`prog_placeOK`, `Scc/Cert/PlaceOK*.lean`): the kernel runs the lowering
  and the emitter and checks the result equal to a literal (`out_eq`, in
  three steps: `lowered_eq`, `emitted_eq` and the rest,
  `Scc/Cert/OutStage{A64,X64}.lean`; `emitted_eq` itself from the emitter's
  checks, each function and the rest, `emitItemsMaps_of_stages`),
  and decides `placeOK`'s parts on that
  literal; the loader's parse of the embedded text is checked against the
  same output by evaluation (`parsesTo`, a `#guard`).  For an accepted
  program `prog_cert_ready` states acceptance and placement together.

A program with non-tail recursion has no stack need table, so it cannot
satisfy `placeOK`: its file embeds the source only, states nothing, and is
marked `-- outside the certified fragment` (`renderOutside`).

`scc --check c.lean` (or `lake env lean c.lean` in the Kraken package, after
`lake build Scc`) checks a certificate; the test programs' certificates
check in 40 to 70 s, with a Lean process of 2 to 3.5 GB.

**What a check trusts.**  The Lean kernel, for every `theorem`; the Lean
compiler and interpreter, for the `#guard`s (reproducibility, the source
term, `parsesTo`) and for the elaboration-time parse of the embedded text
(`scc_x64_reparse%`, `scc_arm_reparse%`), none of which the kernel replays;
and the definitions the statements name: Kraken's parser and its
lowerability predicates, `Scc.Lower.Accepted0`, `placeOK` and `Out.ofEmitted`
(`Scc/Cert/PlaceOK*.lean`), `parsesTo` (`Scc/Cert/Link*.lean`), and the
lowering and emitter they run (the frontend only through the `#guard`s).  The lemmas of the imported modules
(`Scc/Cert/OutStage*.lean`'s `ofEmitted_of_stages`, the `PlaceOK` modules')
are kernel-checked proofs, so their statements are all that is trusted.  The
literals (`scc_lit%`, with the `ToExpr` instances of `Scc/Cert/OutLit*.lean`
and `PlaceData*.lean`) and GNU `as`'s sizes are untrusted: each is checked
by an equation or a decision.

A future certificate adds the correctness theorem: a simulation of the
emitted program under Kraken's semantics by the WeakCore program, with the
per-construct lemmas and the obligations above discharged.

## Pipeline

| module | role |
|---|---|
| `Scc/Cli.lean`, `Scc.lean`, `Scc/MainX64.lean`, `Scc/MainArm.lean` | options, exit statuses, messages; the `scc` driver and the `scc-x64`/`scc-arm` compilers |
| `Scc/Config.lean` | `(arch, host, gc)`, runtime layout sizes, the Kraken target table |
| `Scc/Frontend.lean` | `Syntax.parseProg`, WeakCore's `checkProg`, the accepted fragment (`accepted`), the entry point, the `Int` `+` analysis |
| `Scc/IR/Core.lean` | the IR: functions of basic blocks over named 64-bit registers; the contract between lowering and emitters |
| `Scc/IR/StackMap.lean` | growable stacks: frame records, safepoints, the stack-map table format, the no-escape check |
| `Scc/Lower/` | the object layout (`Obj.lean`), WeakCore terms to IR (`Term.lean`), the runtime in IR (`Runtime.lean`), whole programs (`Program.lean`) |
| `Scc/Emit/X64.lean`, `Scc/Emit/X64Print.lean` | IR to Kraken x64 `Directive`s (every instruction; no raw lines), and their AT&T printer |
| `Scc/Emit/X64Lowerable.lean` | the x64 forms a WeakCore lowering may emit (`ProgramWCLowerable`), and the obligation `SubWordOwned` |
| `Scc/Cert/` | certificates: the generator (`Gen.lean`), SHA-256, per-architecture support (`X64.lean`, `Arm.lean`), the placement check (`PlaceOK*.lean`), the staged output check (`OutStage*.lean`), the layout of a linked executable read from its ELF file (`Elf.lean`) |
| `Scc/Emit/X64Test.lean` | printer round trip of every emitted item through Kraken's parser, no raw lines, the form table |
| `Scc/Emit/A64.lean`, `Scc/Emit/A64Print.lean` | IR to Kraken AArch64 `Directive`s (only forms `Program.WCLowerable` allows), and their GNU `as` printer |
| `Scc/Emit/A64Test.lean`, `Scc/Emit/a64_check.sh` | printer round trip through Kraken's parser, `WCLowerable` of emitted programs by `decide`, IR-level run tests |
| `Scc/Test/` | test programs, expected outputs, `run.sh`, Lean-level tests |

## The accepted fragment

Everything below is checked by `Scc.Frontend`; anything else is rejected with
the construct named.

* **Terms:** `let`, `let (x, y) =`, `let <i, x> = unpack` (index and type
  existentials, erased), `if a = b`, `ret`, `tail`.
* **Operations:** atoms, pairs, `Int` `+` and `-`, `new`, `publish`, `newBuf`,
  `bufInit`, `b[i]`, `fld`, plain and acquire `load` (also `load b[i]`), plain and
  release `store` without a token, `fence`, `pack`, calls, `xchg` (also
  `xchg b[i]`), `nameI`, `zero`, `cvt`, `toInt`, `asLanes`, `fop`, `fcmp`,
  `fop1`, `lane`, `setLane`, `bits` (not `msb16`), `bit1`, `spawn`.
* **Types:** `Unit`, `Void`, `Int`, `Int[i]`, fixed-width and lanes words,
  products, `Ptr`/`Loc` with mode `own` or `pub`, arrays of one-word
  elements, refinements, index and type existentials of these.  No type
  parameters on blocks.
* **Literals** must be below `2^64`.
* **Entry point:** `main(a : Unit)`, `main(a : Ptr pub Void)` (its own
  `ThreadId`), or `main(a : S * Ptr pub Void)` with a setup block
  `rodata(u : Unit) : S` that runs as code before `main` (static data by the
  heap-bytes route).  `main` returns `Int` (the exit status, modulo 256) or
  `Unit` (status 0).

### Provisional forms (until WeakCore has them)

* `let t = spawn{f}(a)` is the spawn of block `f` on `a` (at `f`'s argument
  type; `spawn[τ…]{f}(a)` passes type arguments).  WeakCore's parser reads it
  as a call of a block named `spawn`, which a program may therefore not
  define.  The result is the child's `ThreadId`, its TCB's address (the
  thread index is kept in the TCB; main is 0).
* A block `print{m}(a : ({Loc pub Array[m] LanesU8 | ini >= m} * Int[m]) * Int) : Unit`
  is the output extern: a call writes the first `n` bytes of the slice
  (at most its length) to standard output.  Its body is not compiled.
* Blocks `park(u : Unit) : Unit` and `unpark(t : Ptr pub Void) : Unit` are
  the runtime's `park`/`unpark`; `ThreadId` is stubbed as `Ptr pub Void`.

### Static checks

* **`Int` addition.**  Plain `Int` is unbounded in WeakCore.  Every `+`
  lowers to an addition whose overflow past `2^64 - 1` takes the abort
  outcome; no check is elided.  `--report` lists every site and marks it
  *boundable* (both operands are literals or index singletons whose sum is
  provably at most the length of an array in scope, as for array indices:
  the check could be elided once WeakCore proves that index-typed variables
  hold their index values) or *unbounded*.  `-` is a saturating subtraction,
  exactly WeakCore's truncated subtraction.
* **Stack pointers never escape.**  The source has no stack addresses (every
  pointer is a heap label and offset, and spawn arguments are copyable), so
  the term lowering produces none.  The IR can hold them (`Inst.slotAddr`,
  registers listed in `Func.stackRegs`) under rules that keep them inside
  the thread: never stored to memory, passed to a system call or `clone`,
  returned or passed in a tail call, and only moved into stack registers
  (including a callee's matching parameters).  Both emitters check these
  rules (`StackMap.check`) on every program.
* **Mixed units do not race** (provisional `regionHomog`).  A
  locative is two words in different regions of an object, so it may live in
  a frame, an argument or an own cell, but not inline in a shared (`pub`)
  cell or as an element of a shared buffer; such a type is rejected wherever
  it occurs (signatures and every binding).
* WeakCore's `ProgScopeOKW` is not run by `scc`: its module closure is most of
  WeakCore's proof development, too heavy for the executable; the
  certificates of stage 4 will check it.

## Runtime ABI (`--host linux --gc none`)

* **Values.**  A WeakCore value is its runtime words as WeakCore's `TermRun`
  lays it out (products concatenated, packages and singletons erased), except
  that a locative is two words, base and offset; every word is 64 bits: a
  number is its pattern (fixed-width words zero-extended), a `Ptr` or
  `ThreadId` an object's base address, `null` 0.  Heap objects use the
  bipartite layout (see "Object layout" below).
* **Calls.**  Arguments and results are flattened to words, at most 32
  arguments and six results.  x64: arguments in `%rdi %rsi %rdx %rcx %r8
  %r9`, results in `%rax %rdx %rcx %rsi %rdi %r8`; AArch64: arguments in
  `x0`–`x7`, results in `x0`–`x5`; further arguments in the caller's
  outgoing area, `[sp + 8j]` at the call, which the callee copies to its
  frame in the prologue (the callee's prologue-check map lists live trace
  words there).  Every IR register lives in a frame slot.  Tail calls reuse
  the frame and write stack arguments over the function's own incoming
  area; functions joined by tail calls share one area, sized for the widest
  of them, which every call of a member reserves, so every tail call is a
  jump (see `LAYOUT.md` §5).  A spawned block takes at most six words (they travel in the TCB).
* **Heap.**  A 64 MiB `.bss` arena with an atomic bump cursor, never freed;
  every object has one header word; exhaustion is the abort outcome.
* **Threads.**  A `ThreadId` is the address of the thread's TCB (`spawn`'s
  result and `main`'s argument alike), an object in the separate pinned
  region, so it never moves: `self` at 0, `stackLimit` at 8, `permit` at 16,
  `exited` at 24, `stackBase` at 32, `stackTop` at 40, `badMask` at 48
  (reserved for a loaded-value barrier, 0), the thread index at 56.
  The thread pointer holds it (x64 `%fs` base, set by `arch_prctl(ARCH_SET_FS)`
  for the main thread and `CLONE_SETTLS` for others; AArch64 `TPIDR_EL0`).
  `spawn` first counts the thread (`scc_rt_thread_reserve`: an atomic add on
  `scc_rt_nthreads`, whose new value is the child's thread index; the count
  is never decremented) and takes the `threads` abort outcome past the cap
  `Layout.maxThreads` (default 1023, the main thread not counted), so a
  program runs at most `maxThreads + 1` threads and its certificates set
  `CertCfg.slots = maxThreads + 1`.  It then allocates the TCB with the
  thread index and the argument words in it, takes a stack, issues a full fence, and calls `clone(CLONE_VM | CLONE_FS | CLONE_FILES |
  CLONE_SIGHAND | CLONE_THREAD | CLONE_SYSVSEM | CLONE_SETTLS)` with no
  `CLONE_*TID` flag; the child runs a trampoline that calls the block,
  release-stores `exited`, and calls `exit`.
* **Stacks.**  Growable copied stacks.  Each thread starts with a 16 KiB
  range of a shared 512 MiB `.bss` pool.  Each function's prologue compares
  the new stack pointer with the TCB's `stackLimit` (`stackBase` + 4 KiB,
  kept for the code that runs unchecked: the abort and grow routines); a
  frame that does not fit calls the grow routine, which takes a range at
  least twice as large, copies the live stack to its top, rewrites every
  stack address, updates `stackBase`/`stackTop`/`stackLimit`, moves onto the
  new range and releases the old one.  Past the per-thread cap (64 MiB), or
  with the pool exhausted, the abort outcome.  Ranges of finished threads
  are not reused (the kernel does not report a thread's exit without a
  `CLONE_*TID` flag).
* **Stack pool.**  Ranges are `16 KiB · 2^k` (size class `k`).  A range comes
  from its class's free array, else from the pool's bump cursor (atomic
  add); the free arrays are guarded by a spin lock (`xchg` / AArch64 `swpal`
  to take it, a release store / `stlr` to give it back).  The pool region
  holds stack contents only: the cursor, the lock, the free counts and the
  free arrays are separate data items, and a range is touched only by the
  thread that owns it (the grow routine releases the old range only after
  the thread has left it).
* **Sites.**  Two global labels on `nop`s (IR `Inst.site`), each placed
  once, mark the moments a range changes hands.  `scc_rt_take_site` is the
  single exit of `scc_rt_stack_take`, after the range is popped or bumped,
  and every take passes it (the main thread's first range at start-up, a
  child's range in the parent before `clone`, the grow routine's new
  range).  `scc_rt_release_site` is the first instruction of
  `scc_rt_stack_release`, before the range is pushed back under the lock.
  At both, the range's base is in the first argument register (`%rdi`,
  `x0`) and its size in the second (`%rsi`, `x1`).
* **Frame records and stack maps.**  The frame pointer (`%rbp`, `x29`) chains
  frame records (saved frame pointer, return address); the chain ends with a
  saved frame pointer of 0 at each thread's entry.  Every call and every
  prologue check is a safepoint, labelled by its return address.  The
  read-only table `scc_stackmap` has one entry per safepoint, sorted by
  return address: `ret, nStack, nHeap, first`, indexing a shared array of
  signed byte offsets from the frame record of the slots that hold stack
  addresses (rewritten when the stack moves) and trace words (references,
  locative bases, `ThreadId`s; recorded for a future moving collector,
  unused).  A prologue check's entry points at
  the save area where its stub keeps the argument registers.  Saved frame
  pointers are always rewritten; return addresses never.  The format and
  the protocol are in `Scc/IR/StackMap.lean`.
* **`park`/`unpark`.**  A futex on the TCB's permit word
  (`FUTEX_WAIT_PRIVATE`/`FUTEX_WAKE_PRIVATE`); `park` may return spuriously.
* **Output.**  `print` is a `write(1, …)` loop: positive results advance,
  `-EINTR`/`-EAGAIN` retry, zero or another error aborts.  `SIGPIPE` is
  ignored at start, so a closed pipe is an error return.
* **Exit.**  `main`'s result goes to `exit_group`.  The abort outcome has
  five kinds: `overflow` (`Int` addition), `heap` (arena exhausted), `stack`
  (cap reached or stack pool exhausted), `write` (output failure) and
  `threads` (the thread cap reached, no room for a new thread's TCB in the
  pinned region, allocated by `scc_rt_alloc_tcb`, or a failed `clone`).  `scc_rt_abort(k)` dispatches to
  the routine `scc_rt_abort_<kind>`, which writes the kind's message to
  standard error and has the kind's own `exit_group(101)`.  The trap
  instruction of that `exit_group` (the AArch64 `svc #0`, the x64 `syscall`)
  carries the label `scc_rt_abort_<kind>_exit` (`Names.abortExit`): the
  abort outcome of kind `<kind>` is reaching that instruction, so a
  correctness statement's abort label for a kind names it, not the routine
  entry (which keeps its own label).  The labels are `scc_rt_abort_overflow_exit`,
  `scc_rt_abort_heap_exit`, `scc_rt_abort_stack_exit`, `scc_rt_abort_write_exit`
  and `scc_rt_abort_threads_exit`.  `Inst.syscall`'s optional `lbl` argument
  places them; the emitters put the label after the number move, directly
  before the trap.

  | kind | `AbortKind.code` | routine | exit label | message on fd 2 |
  |---|---|---|---|---|
  | `overflow` | 1 | `scc_rt_abort_overflow` | `scc_rt_abort_overflow_exit` | `scc: abort: Int addition overflow` |
  | `heap` | 2 | `scc_rt_abort_heap` | `scc_rt_abort_heap_exit` | `scc: abort: out of heap or threads` |
  | `stack` | 3 | `scc_rt_abort_stack` | `scc_rt_abort_stack_exit` | `scc: abort: out of stack` |
  | `write` | 4 | `scc_rt_abort_write` | `scc_rt_abort_write_exit` | `scc: abort: write to standard output failed` |
  | `threads` | 5 | `scc_rt_abort_threads` | `scc_rt_abort_threads_exit` | `scc: abort: cannot create a thread` |

  Every kind exits with the same status, 101 (`IR.abortExitCode`,
  `Kernel.abortStatus`); the messages (`AbortKind.message`) are the only
  per-kind difference a run shows.
* **Exit status 101 is ambiguous.**  The status alone does not tell an abort
  from a normal exit: `main` returning `v` with `v mod 256 = 101` (101, 357,
  …) also exits with 101, through `scc_rt_main`'s `exit_group`.  The cases
  differ as follows.
  - *Observably*, by standard error: an abort writes its kind's message
    before its `exit_group`, and `main`'s exit writes nothing.  Two runs are
    still indistinguishable: an abort whose message `write` fails (fd 2
    closed or refusing; the routine ignores the result and exits anyway)
    and a `main` returning 101 having written nothing to fd 2 itself.  The
    tests read the status together with standard error (`run.sh`: `T.code`
    with the whole of `T.stderr`; `diff.sh`: the first line of standard
    error, and a 101 the reference does not predict is a mismatch).
  - *In the kernel model*, by the trap's address: `exit_group(v)` with
    `v mod 256 = 101` may end the process with `exit 101` or with `abort k`
    (`Kernel.sysStep`), and `Step.sys` admits `abort k` only at the trap
    labelled `scc_rt_abort_<k>_exit` (`Layout.abortLbl k`) and `exit` only
    off every such trap.  So a trace says which case it was, and of which
    kind, even though the status does not.

## Object layout

scc lays objects out as WeakCore's GC design decides (no collector is
built: `--gc none` stays a bump allocator).  Every type has `reg = (n, m)`,
`n` scalar and `m` trace (reference) words; an object has its trace words
below its base and its scalars from it, and one header word carrying
`(n, m)` (arrays: the element's, plus the length); a locative is two words,
base and an offset word packing the pointee's start in both regions.  A
locative (the fragment's only mixed unit) may not sit inline in a shared
cell (`regionHomog`, provisional).  The full description, the stack-map
consequences and the open items are in [`LAYOUT.md`](LAYOUT.md);
`Scc/Lower/Obj.lean` implements it.

Where an allocation lands (`scc_rt_alloc(h, k, u)`, `Runtime.allocF`):

* **16-byte heap cells.**  The arena `scc_rt_heap` (16-aligned) is
  divided into 16-byte cells, and its cursor is the heap counter
  `scc_rt_heap_use`, counting cells, not bytes (`heapCells = heapBytes /
  16`).  An allocation of `u` source units (`new` of a type of `w` source
  words: `u = w + 1`; `newBuf` of `k` elements of `w` words: `u = k·w + 1`)
  adds `u` to the counter atomically; the old value `old` places it at
  `s = scc_rt_heap + 16·old`, and it owns the `u` cells from there.  The
  object's `1 + k·(n + m)` words fit those `2u` words because the lowering
  refuses a type whose runtime words exceed twice its source words
  (`n + m ≤ 2w`, `Lower.Term`'s `new`/`newBuf`).
* **The header word.**  The allocator writes `h | k << 36` (`Obj.lenShift`)
  at `s + 8·k·m` (the default, after the trace region) or at `s`
  (`headerBeforeTrace`).
* **The returned base is 8 above the header (default).**  The result is
  `s + 8·k·m + 8`: the scalar words start there, the header is at
  `base − 8` and the trace words lie below it.  So a base is 8-aligned and
  16-aligned exactly when `k·m` is odd; nothing in the accepted fragment
  needs more (`allocGap`, for 16-byte pairs, is not used yet).
* **The pinned region.**  `scc_rt_alloc_tcb(h, k)` is the same allocator
  over `scc_rt_pinned` with a byte cursor (bumped by `8·(1 + k·(n + m))`,
  no source units) and the same header and `+ 8` base.

## Trusted base (intended, for every certified program)

Kraken's ISA and memory models; the kernel model of `write`, `exit_group`,
`clone`, `futex`, `rt_sigaction`, `arch_prctl`; the assembler, linker and
loader; WeakCore's assumptions inherited through the simulation; Lean.  The
emitter, the IR and the lowering are meant to be checked, not trusted.

## Tests

`Scc/Test/run.sh [--arch x64|arm]` builds `scc` (with `$LAKE`, default
`lake`), compiles every `Scc/Test/*.w`, assembles, links and runs the
binaries, and compares the results; multi-threaded tests run 50 times.  Per
test `T.w`: `T.code` expected exit status (default 0), `T.out` expected
standard output (exact; default empty), `T.stderr` expected standard error,
`T.report` expected `scc --report` output, `T.runs` repetitions.  A
`reject_*.w` must be rejected with exit status 1 and standard error exactly
`reject_*.err`.  Every accepted test also gets a certificate (`--cert`), which
must check (`--check`; time and peak memory are printed) and carry the
`sha256sum` digests of both texts, and a tampered certificate (one instruction
of the embedded text made unlowerable) must fail both its reproducibility
check and its lowerability proof.  `Scc/Test/CertTest.lean` checks the
generator's string literals.  `Scc/Test/FrontendTest.lean` checks the frontend and the
lowering at elaboration time (`lake build Scc`).

`Scc/Emit/X64Test.lean` (built by `lake build Scc`) checks that every item the
x64 emitter produces reads back as itself through Kraken's x64 parser, that
no program has a raw instruction line, and proves
`ProgramWCLowerable` by `decide +kernel` of the re-parsed programs.

`Scc/Test/ElfTest.lean` (built by `lake build Scc`) reads the layout of
`ret0` linked statically for each architecture (`Scc/Test/elf/`) with
`scc_elf_layout%` (`Scc/Cert/Elf.lean`), checks it field by field and with
`wfB`, including `ld.lld`'s default placement of `.rodata` below the code
(`a_def`, accepted) and its build-id note (`a_bid`, accepted), and checks
the reader's refusals on byte-patched files: truncated, wrong machine, the
entry point off `.text`'s start, the code not executable, overlapping or
empty or missing regions, a region outside `.bss`'s zero-filled tail, a
data symbol inside the code or past the start of the heap arena, a `.data`
symbol below the code (outside every data region: `wfB`), and a build-id
note that is executable, writable, not a note, in an executable or no
`PT_LOAD`, off its file bytes, overlapping `.rodata`, or with a symbol in
it.  `Scc/Test/elf.sh [--relink]` compares the reader with `readelf` on
the same files, after relinking them with `--relink`.
`Scc/Test/textalign.sh` links every program `scc --arch arm` accepts as
`run.sh` does and checks that `.text` and the entry point are 16-aligned
(the emitter's opening `.p2align 4`; `wfB` refuses anything else).

`Scc/Test/certify.sh [--arch x64|arm] [--instantiate] [--elf EXE] [-v|--verbose] PROG.w`
certifies after the link.  It compiles `PROG.w` with `--cert` (checking the
certificate's `sha256sum` digests) and links it with `run.sh`'s commands
(`as` and `ld -static` on x64; clang with lld on arm).
`--elf EXE` uses `EXE` as the executable instead.  It then runs the ELF
reader on the executable and writes `T.post.lean` under
`.lake/certify/ARCH/T/`.  That file holds the certificate without its
static-link decisions, then the executable's layout as a
`scc_elf_layout%` literal (its SHA-256 checked by `#guard`), then
`placeOKAt` decided at that layout, component by component.  With
`--instantiate` it also instantiates the compiler theorem at that layout and
prints its axioms.  The file is checked with `lake env lean`, and its time
and peak memory are printed.  On failure, the first failing component is
printed by evaluation.  The last line, `certify: T (ARCH): VERDICT`, and the
exit status are:
- 0, `certified` (only with `--instantiate`);
- 10, `placement decided`;
- 3, `not certifiable` (outside the fragment, e.g. non-tail recursion, or a
  placement component fails);
- 1, `failed` (scc, the link, or the reader refuses, e.g. a truncated
  executable or a zero-size heap symbol).

`T.post.lean` combines the components with `placeOKAt_of`, and with
`--instantiate` applies the compiler theorem at the executable's layout:
`Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt` on x64,
`Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt` on arm.  On x64,
`ret0` gives `certified` with `--instantiate` in about 50 s and 1.3 GB.  On
arm, `ret0` (`ld.lld`'s default link, `.rodata` below the code) gives
`certified` with `--instantiate` in about 53 s and 1.4 GB.  Without
`--instantiate` both give `placement decided`.

Before compiling, `certify.sh` builds what it needs with `lake build`: scc
and the certificate modules, and with `--instantiate` the compiler theorem's
module.  For each build it prints one line naming the targets, how long a
first run on a fresh checkout takes, and the build log,
`.lake/certify/ARCH/T/build.log`, which collects the build output.  When a
build fails, it prints the log's last 20 lines, then the `failed` verdict
with the log's path.  Measured on a fresh clone with nothing built, with
lake's default parallelism on 64 cores: for x64 `ret0` with `--instantiate`,
about 15 minutes for scc and the certificate modules, 3 minutes for the
theorem, then the 50 s check; arm afterwards, about 4 + 3 minutes of builds
(the shared modules are built by then).  The scc and certificate build
includes `WeakCore/TermStep.lean`, whose memory is noted above.  Build
`Spike.Test.Ret0LinkedX64` (and `Spike.Test.Ret0LinkedA64`) first to see the
build's progress directly.

`-v` (`--verbose`) prints each command to standard error before it runs, as
`+ cd DIR && CMD` with absolute paths, and `# wrote PATH (purpose)` for each
Lean file the script generates (`T.elf.lean`, `T.post.lean`,
`T.diag.lean`).  Running the printed commands by hand, in order, repeats the
run; the last, `lake env lean .../T.post.lean`, is the kernel check.  Apart
from that the output, verdict and exit status are the same.
`Scc/Test/certify_test.sh` checks each of these verdicts: x64 `ret0` (with
and without `--instantiate`), two damaged copies of it, `deeprec.w`, and
arm `ret0` (with and without `--instantiate`), and `-v` on x64 `ret0` (the
trace names scc and `lake env lean`; the verdict and status match the run
without `-v`).

`Scc/Test/StackTest.lean` (built by `lake build Scc`) holds an IR-level
program with the real runtime whose frames hold stack addresses
(`Inst.slotAddr`) across calls and prologue checks while the stack grows
several times; `run.sh` writes, assembles and runs it on the selected
architecture (`reloc`).  It also checks the computed maps and the
no-escape check's verdicts.

`Scc/Emit/A64Test.lean` (built by `lake build Scc`) checks that Kraken's
AArch64 parser reads the printed text of every emitted form back to the same
`Directive`s, and proves `Program.WCLowerable` by `decide` of the re-parsed
text of `hello.w` and of IR-level test programs.  `Scc/Emit/a64_check.sh`
assembles, links and runs those IR-level programs under `qemu-aarch64`, then
calls `run.sh --arch arm`.

**Differential tests.**  `Scc/Test/diff.sh [--arch x64|arm] [-n N] [--seed S]`
compares scc against WeakCore's own semantics.  `Scc/Test/Gen.lean` generates
programs `0 … N-1` of stream `S`: well-typed, single-threaded programs in the
accepted fragment with helpers, `if`, tail and non-tail recursion, `U64` and
`Int`-index loops, checked `Int` `+` on values near `2^64`, provably
nonnegative `Int` `-`, `bits`/`bit1`, fixed-width words (`div`/`rem` by zero
included), lanes, heap cells and arrays.  `Scc/Test/RefEval.lean` runs each
program's `main` on WeakCore's executable machine (`TermRun.threadSteps`, one
thread, promises off) with one addition, scc's overflow abort when an `Int`
`+` reaches `2^64`.  The script compiles, links and runs every program (arm
under `qemu-aarch64 -cpu max`) and requires its exit status to equal the
reference's (`main`'s result mod 256, or 101 with the overflow message for a
reference overflow).  A frontend rejection counts as a generator bug.  The
generator's `Int` `-` is always provably nonnegative (the checker demands
it), so scc's saturating subtraction never saturates in these programs.

**System calls and the thread pointer.**  Both emitters write `svc #0`,
`mrs`/`msr` of `TPIDR_EL0`, `syscall`, `ud2` and the `%fs:` moves as Kraken
instructions (`Kraken/SYSCALL.md`), and the lowerability results cover them.
Kraken's `%fs:` operand is `mov` only: the x64 stack check loads the limit
with `movq %fs:8, %r11` and compares registers.  `divq`, `cqto`, `idivq` and
`popcntq` are Kraken instructions too, so neither emitter writes a raw
instruction line: the re-parsed program of either architecture has every
instruction of the binary.
