# scc release note: `wake.w` and `hello.w` certified on AArch64 and x86-64 at their executables; `hello1.w` and `ret0.w` on AArch64 and x86-64; `--granule` certificates for `Accepted0`/`Accepted1` programs

This note states what this release of `scc` proves, what it trusts, and what
it does not cover. Statements are quoted from the source tree.

## New in this release: the granule pass (`--granule`), its certificates and byte check, WeakCore release 7, faster certificates, and an EFI preview

The statements of the final theorems in §1 are those of the previous
release, word for word, and so are their axioms (`#print axioms` of
48 names from §1, in 32 modules: `propext`, `Classical.choice` and
`Quot.sound`, as in the previous release; `ret0_codeEnd` on each ISA depends
on no axiom).
Every statement the previous release quoted in §1 was compared with its text
in this tree: none changed. The new statements are quoted in §1 with
their differences from the theorems they mirror: the three `_final`
theorems of the granule pass (*The compiler theorems on the post-pass
text*), the `Accepted2` statements at the header bound (*The `Accepted2`
statements, proved at the header bound*), and the theorems at the linked
post-pass executables (*The granule instances at the linked post-pass
executables*).
WeakCore moves to release 7 (next section).
The executables checked in by the previous release are unchanged, and so
are their SHA-256 pins and the layouts quoted in §1 and §2.

- **The granule pass, behind `--granule` (default off).** `scc --granule`
  passes the emitter's items through the granule pass before the GC tables
  are appended: `.text` is laid out in 64 KiB granules, with a descriptor
  word (`.quad scc_gc_desc - .`) in the last 8 bytes of every granule
  (`Scc/README.md`). Without the flag scc's output is unchanged. `--host
  raw`, `--blocks` and `--code` refuse the flag.
- **What it certifies.** With `--granule`, `--cert` writes a certificate
  about the output after the pass, and `Scc/Test/certify.sh --granule
  --instantiate` instantiates the `_final` twin of the theorem it would
  instantiate without the flag (`Spike.Lib.Lower{X64,A64}.CorrectFinal`):
  `a64_scc_correctE_text_closedAt1_final` on AArch64,
  `x64_scc_correctE_text_closedAt1_final` on x86-64, or
  `x64_scc_correctE_text_closedAt_final` for an `Accepted0` program whose
  `main` frame exceeds 4096 bytes (or with `CERTIFY_X64_FRAGMENT=0`). These
  are the `closedAt1` finals for the simple fragments: the programs
  `certify.sh` certifies without the flag. `Scc/Test/certify_test.sh`
  certifies `ret0` on both ISAs, `ifsub1` on x86-64, `ret0` on x86-64 over
  `Accepted0`, and `ret0`'s post-pass listing linked by x86-64 `ld.lld`.
- **What answers exit 3.** A registry program (`hello1`, `wake`, `hello`)
  with `--granule` is not certifiable: "no proved theorem for the post-pass
  text (--granule; the registry's theorems are about the text without the
  granule pass)". `certify_test.sh` checks this for `hello1.w` on both ISAs.
- **The byte check (P6).** `T.post.lean` of a `--granule` certificate runs
  `Scc.Cert.ElfBytes.{X64,A64}.check` on the executable (an `#eval` that
  throws on a mismatch). It compares the executable's whole `.rodata` with
  the image the loader lays out from the text, and checks that a `.text` of a
  granule or more is whole granules on a granule boundary, ends at the
  text's `scc_text_end`, and has in the last 8 bytes of every granule the
  word `scc_gc_desc - .` (modulo `2 ^ 64`), with the executable's own
  `scc_gc_desc` symbol at the loader's address. The loader's cell of a
  descriptor word is empty, so these bytes are checked here and nowhere
  else (§3, item 18).
- **Granule executables.** Eight post-pass executables are checked in and
  pinned: `ret0` (x86-64 with GNU `ld`, x86-64 with `ld.lld`, AArch64),
  `call1` (x86-64, AArch64), `frame0` (x86-64) and `hello1` (x86-64,
  AArch64), under `Scc/Test/elf/*g/`. `Scc/Test/elf.sh --relink-check`
  reproduces them byte for byte.
- **Theorems at the post-pass executables.** At the layout of each
  checked-in post-pass executable, given the loader's parse of its text:
  `hello1` is correct on AArch64 (`hello1_finalCAG`) and x86-64
  (`hello1_finalCF`), and `ret0` on AArch64 and x86-64 with GNU `ld`
  (`ret0_linked_correctG`) and with `ld.lld` (`lld_linked_correctG`). For
  `call1` (both ISAs) and `frame0` (x86-64) only the placement check is
  proved there (`call1G_placeOKAt`, `frame0G_placeOKAt`), as for their
  pre-pass executables. `certify.sh --granule` still answers exit 3 for
  `hello1.w` (above): these are checked-in theorems about the checked-in
  texts, not a `certify.sh` path.
- **The `Accepted2` statements are proved** at every configuration with
  the header bound (`Scc.Obj.nShift cfg.layout.obj < 22`):
  `closed2StmtAH_final : Closed2StmtAH` on AArch64 and
  `closed2Stmt_x64_final : Closed2StmtH` on x86-64. The previous release
  stated `Closed2StmtA`/`Closed2Stmt` and proved them only from open
  segment obligations. `certify.sh` does not use them.
- **`hello` on x86-64: a closed run at the current layout.**
  `ctxU_OX_closed` and `landRdUg_OX_closed`
  (`Spike/Test/HelloRootL0XClosed.lean`) show, from the loader's parse
  alone, that a run of the checked-in `hello` text from the load at `Λe`
  reaches, after 283 instructions of thread 0, a state in the root's
  level-0 context, and that the counter add there lands in the antecedent
  of the root's landing obligation. These are non-vacuity results about
  the root's premises; they add no correctness statement.
- **Faster certificate checks (the generator's arithmetic rounds).**
  `Scc/Cert/MapsFast.lean` gives structural forms of the GC table
  computation (leaders, successors, maps, tables, stubs, liveness, least
  fixpoint) and proves each equal to the original for all inputs. Generated
  certificates still state their theorems about the originals and prove them
  through these equalities, so the kernel evaluates only the structural form;
  the originals stay the specification. Round 1 covers the per-function
  maps, successors and tables; round 2 the remaining table checks. The 12
  checked-in certificates are regenerated. Timings and memory: §4.
- **Refused programs.** scc refuses a `device` declaration and an
  index-parameter spawn (`spawnI`) as outside the accepted fragment, and
  WeakCore's checker refuses a device extern called outside a device
  function (`Scc/Test/reject_{device,spawni,devext}.w`).
- `runtime/efi/`: an unverified preview of the raw runtime as a UEFI application. On x86-64 it
  boots, starts the other CPUs and runs the raw-host `hello1` on one thread (`Hello, world`); on
  AArch64 it prints a banner and halts. It is outside every statement in this note.
## WeakCore release 7 (47e9c32c)

The vendored WeakCore (`WeakCore/`) is upstream release 7, commit 47e9c32c
(parent 621ec97a, the previous release's). It changes only `WeakCore/` and
`WeakCore.lean`; the lakefile and toolchain are unchanged. scc and its
proofs are adapted to it.

What changes for users (`WeakCore/README.md` has what is proved, open and
assumed):

- **Region code in the scope check.** `TermScope.ProgScopeOK` (with the
  checks of `TermScope.ProgScopeOKW`) admits region types in signatures and
  annotations, live region binders over a reference, `intoRgn` of an owned
  reference to a coupled payload, and access to region payloads, as the type
  checker permits, with the exceptions listed in `WeakCore/README.md`. Two
  new refusals: the payload of a region binder must be coupled, even when
  the binder's pointer is unused; `endBorrow` is refused while a variable it
  would sweep away still holds a linear token.
- **`spawnI`.** A new operation starts a thread at the parent's index
  parameters on a copy of its argument: affine values move to the child, and
  the second-class capabilities in the argument's type end in the parent
  (`CoreTerm.handOff`, `CoreTerm.handOffR`). New definitions
  `CoreTerm.keyFreeTE` and `CoreTerm.keyFreeT` (a type carries no key).
  `spawnI` and `isTy` are new keywords. scc's frontend refuses `spawnI`
  (above), and `Scc/Sem/Correct.lean`'s `opAts` gives its argument atom, as
  for `spawn`; this matters only outside the fragment.
- **The device cell rule is dropped.** The checker no longer restricts the
  cells a `device def` function's argument points to; `CoreTerm.devCellOK`
  remains as an unused definition. The other device rules stay. scc refuses
  device declarations (above).
- **Obligations.** `ObligationsF` and `ObligationsFX` take `typed`
  (`CoreTyping.ProgT`) and `dyClean` (`TermSound.DyClean`) in place of
  `checked`; `TermSound.typed_dy_of_checked` derives both from acceptance.
  On the scc side `Scc/Sem/PubFree.lean` builds them so. Its `pubFree` now
  also refuses a region binder and `intoRgn`, so `ProgPubFree p` means no
  `publish`, no region binder and no `intoRgn` in any code block, as its
  docstring and that of `SrcChecks` (`Scc/Sem/SrcStart.lean`) say. This is
  forced: release 7's `PubWinTN` also constrains a thread at a region binder
  and at `intoRgn`. It strengthens a premise, and scc's frontend refuses
  both constructs (`region` is not in the accepted fragment; `intoRgn` is
  refused as an operation), so every program scc accepts gets the same
  verdict, and no scc statement changes. `Decl.swapIdx` is a new field that
  no check reads yet, so the semantics ignore it; scc's `declIs` compares
  it, so it is still equality of declarations, and the `print` extern's
  model has `swapIdx = []`. With `Op.spawnI`, it is the only new
  source-language construct of release 7.
- **Memory model.** No change (`WeakCore/README.md`).

**The premise guard.** WeakCore's guard,
`WeakCore/extras/tools/premises/guard.sh`, freezes the meaning of the
statements of WeakCore's final theorems: the transitive closure of the
definitions each statement mentions, and the full text of a list of language
definitions (`CheckPremises.langRoots`, `forceBody`). Release 7 ships 143
frozen texts (59 for the final theorems, 84 language definitions) and the
set `sets/pr-release-15067-vendored`. Run with this repository's toolchain
on a cold build of `WeakCore`, including the 14 modules the guard's
`CheckPremises` imports (`TermSpawnMain`,
`SpawnFinalX`, `SpawnArmZ`, `SpawnNoSpawn`, `ExtArmZ`, `TermProgress`, `TermLiveL3`,
`TermLiveCertRun`, `TermLiveCertScen`, `TermLiveC`, `TermLiveG3`, `SceProof`,
`TermStartD`, `DmaRing`):

```
cd WeakCore/extras
WM_BUILD=<repository>/.lake/build/lib/lean WM_LEAN=<lean> tools/premises/guard.sh
```

Its last lines:

```
premise set: sets/pr-release-15067-vendored (b4f242a84cfb41595d1985a33c1200b0; lean: Lean (version 4.35.0-pre, x86_64-unknown-linux-gnu, commit d0d716161618bd9fbd0bf2d9b8bbb9b48cccd7dd, Release); layout: vendored)
premises: meaning unchanged (143 finals/premises; set sets/pr-release-15067-vendored b4f242a84cfb41595d1985a33c1200b0)
```

**What the guard does not cover.** The closure stops at WeakCore's machine
and language layer (`CheckPremises.stopModules`, which includes `CoreTerm`,
`CoreTyping` and `TermRun`). Definitions there are listed by signature only,
unless they are language roots or forced; their bodies are otherwise not
frozen. The release depends on these bodies, none of which is a language
root or forced:
- `TermRun.tstep`, one step of one thread (its `new` step records the
  allocation's type, and whether it is a type-test target, in the thread's
  `tys`); `TermRun.threadSteps` is frozen, and shows `tstep` by signature
  only;
- `CoreTerm.scan`, `CoreTerm.annNew`, `CoreTerm.progTgts` and
  `CoreTerm.scopeAllocOK`: the walk of the opened-scope check, the
  allocation annotation, and the program's type-test targets;
- `TermRun.tysOf`, the type recorded for an allocation label in a
  configuration;
- new in release 7: `CoreTerm.keyFreeTE`/`CoreTerm.keyFreeT` and
  `CoreTerm.handOff`/`CoreTerm.handOffR`, the key-free test and the
  capability hand-off of `spawnI` and of a call that may reach it. The
  hand-off at a call applies only to a callee that may reach `spawnI`; scc
  refuses `spawnI` in every code block, so no program scc accepts has such
  a callee, and neither form applies to one (without `spawnI` the set of
  such callees is empty: `CoreTerm.spawnSet_nil_of_noSpawnI`).

The guard would not report a change to these bodies. They are part of the
specification (§3, item 15).

**Reproducing the WeakCore build.** `LEAN_NUM_THREADS=1 lake build WeakCore`
(the modules of §4's WeakCore table alone first), then the guard as above.
A cold build of `WeakCore` with the guard's modules took 52
minutes on 64 cores.
## 0. The claim

### `wake.w`

`Scc/Test/wake.w` is a **two-thread** program: `main` allocates a flag cell
`c`, publishes it, and spawns `worker` on `c` and its own `ThreadId`; it
then waits (`waitLoop`: an acquire load of the flag, parking while it is 0).
`worker` stores 1 to the flag with release ordering, unparks `main` and
returns; `main` sees the flag and returns 0.

**AArch64.** Compiled by `scc --arch arm` to the assembler text `asm`, its
text is `CorrectE 2` with respect to the program's two-thread WeakCore
semantics `wakeS arch`, on the kernel-model target with two thread slots, at
**every** admissible entry state, for every memory model `arch` and every
budget `B` whose heap-cell count is the allocator's, at **one layout**:
`Λe`, read from the executable checked in under `Scc/Test/elf/wakea64/wake`
(pinned by SHA-256) (`Spike.Test.WakeLinkedA64.wake_linkedU`).

**x86-64.** Compiled by `scc --arch x64` to the assembler text
`⟨asm, sizes, labelOffs⟩`, its text is `CorrectE 2` with respect to the
program's two-thread WeakCore semantics `wakeSX arch`, on the kernel-model
target with two thread slots, at **every** admissible entry state, for every
memory model `arch` and every budget `B` whose heap-cell count is the
allocator's, at **one layout**: `Λe`, read from the executable checked in
under `Scc/Test/elf/wakex64/wake` (pinned by SHA-256), with the proof's
immediate table (`Spike.Test.WakeLinkedX64Root.wake_linkedX`).

> [!IMPORTANT]
> Each theorem is about **one program text at one layout**: the checked-in
> certificate's `asm` for `wake.w` (`Scc/Test/elf/wakea64/wake.s`,
> `Scc/Test/elf/wakex64/wake.s`), linked into `Scc/Test/elf/wakea64/wake`
> and `Scc/Test/elf/wakex64/wake`. Unlike `hello1`, there is no
> layout-generic form. `Scc/Test/certify.sh --arch arm|x64 --instantiate
> Scc/Test/wake.w` certifies a build only if the program, the text and the
> executable are those files byte for byte (§4).

Each theorem's only premises are `hP`, the certificate's compiled parse
(`#guard`), and `hB`, which fixes the budget's heap-cell count (§1). Every
placement fact at `Λe` and every correctness step are kernel-checked.

### `hello.w` (AArch64)

`Scc/Test/hello.w` is a **two-thread** program: a setup block `rodata`
writes the 13 bytes `Hello, world\n` into a fresh heap buffer and publishes
the slice; `main` allocates a flag cell, publishes it, and spawns `worker`
on the slice, the flag and its own `ThreadId`, then waits (`waitLoop`: an
acquire load of the flag, parking while it is 0). `worker` passes the slice
to the output extern `print`, stores 1 to the flag with release ordering,
unparks `main` and returns; `main` sees the flag and returns 0.

The listing `scc --arch arm` writes for it, `SccCode.helloAsm`, is
`CorrectE 2` with respect to the program's two-thread WeakCore semantics
with output `helloS arch`, on the kernel-model target with two thread slots,
at **every** admissible entry state, for every memory model `arch` and every
budget `B` whose heap-cell count is the allocator's, at **one layout**:
`Λe`, read from the executable checked in under `Scc/Test/elf/helloa64/hello`
(pinned by SHA-256), with the proof's immediate table
(`Spike.Test.HelloLinkedA64.hello_linkedA`).

> [!IMPORTANT]
> This theorem is about **one program text at one layout**: `helloAsm`
> (`Scc/Test/elf/helloa64/hello.s`), linked into
> `Scc/Test/elf/helloa64/hello` with `.text` and `.rodata` placed by the
> link command (§2). There is no layout-generic closed form; `certify.sh`
> certifies a build of `hello.w` only when its text and executable are these
> files byte for byte (§4).

The theorem's only premises are `hparse`, the listing's compiled parse
(`#guard`), and `hB`, which fixes the budget's heap-cell count (§1). Every
layout fact at `Λe` and every correctness step are kernel-checked.

### `hello.w` (x86-64)

The program is the one described for AArch64 above. The listing
`scc --arch x64` writes for it, `SccCode.helloAsm`, is `CorrectE 2` with
respect to the program's two-thread WeakCore semantics with output
`helloSX arch`, on the kernel-model target with two thread slots, at
**every** admissible entry state, for every memory model `arch` and every
budget `B` whose heap-cell count is the allocator's, at **one layout**:
`Λe`, read from the executable checked in under
`Scc/Test/elf/hellox64/hello` (pinned by SHA-256), with the proof's
immediate table (`Spike.Test.HelloLinkedX64.hello_linkedX`).

> [!IMPORTANT]
> This theorem is about **one program text at one layout**: `helloAsm`
> (`Scc/Test/elf/hellox64/hello.s`), assembled by GNU `as` and linked by
> GNU `ld -static` with its default script into
> `Scc/Test/elf/hellox64/hello` (§2). There is no layout-generic closed
> form; `certify.sh` certifies a build of `hello.w` only when its text and
> executable are these files byte for byte (§4).

The theorem's only premises are `hparse`, the listing's compiled parse
(`#guard`), and `hB`, which fixes the budget's heap-cell count (§1). Every
layout fact at `Λe` and every correctness step are kernel-checked.

### `hello1.w`

`Scc/Test/hello1.w` is one thread: a setup block `rodata` writes the 13 bytes
`Hello, world\n` into a fresh heap buffer, and `main` passes the slice to the
output extern `print` and returns 0. Compiled by `scc` to the assembler text
`asm` (AArch64) or `⟨asm, sizes, labelOffs⟩` (x86-64), its text is
`CorrectE` with respect to the program's WeakCore semantics with output, on
the kernel-model target with one thread slot, at **every** admissible entry
state, for every memory model `arch` and every budget `B` whose heap-cell
count is the allocator's, at **every layout at which the compiler's output
passes the placement check** (`Spike.Lib.LowerA64.hello1_finalCA_gen`,
`Spike.Lib.LowerX64.hello1_finalC_gen`), and in particular at the layouts of
the checked-in executables (`hello1_finalCA`, `hello1_finalC`).

> [!IMPORTANT]
> The theorems are about **one program text**: the checked-in certificate's
> `asm` for `hello1.w` (`Scc/Test/elf/hello1{a64,x64}/hello1.s`). The layout
> is free: `hello1_finalCA_gen` / `hello1_finalC_gen` hold at any layout `Λ`
> with `placeOKAt … Λ … = true`. `Scc/Test/certify.sh --instantiate
> Scc/Test/hello1.w` certifies a fresh build at its own link: it checks that
> scc's text is that `asm` byte for byte, reads the executable's layout, and
> instantiates the `_gen` theorem there (§4). Another program outside
> `Accepted1`, or `hello1.w` compiled to another text, is not certifiable.

The closed forms `hello1_finalCA` / `hello1_finalC` are the `_gen` theorems
at `Λe`, the layout read from the executables checked in under
`Scc/Test/elf/hello1a64/hello1` and `Scc/Test/elf/hello1x64/hello1` (pinned
by SHA-256); their only premises are `hpa`, the certificate's compiled parse
`#guard`, and `hB`, which fixes the budget's heap-cell count (§1). The `_gen`
forms add the placement premise `hΛ`. The placement check and every
correctness step are kernel-checked.

### `ret0.w`

`ret0.w` stays certified as in the previous release. For `Scc/Test/ret0.w`
(`main` returns `40 + 2`):

- **At any layout `Λ` at which the output passes the placement check**, the
  text is `CorrectE` on the kernel-model target (`Scc.Sem.A64.target
  (kernel 1) E`, `Arch.armv8` hooks; `Scc.Sem.X64.target (kernel 1) E`; one
  thread slot), at every admissible entry state `E`
  (`Spike.Test.Ret0ReleaseA64.ret0_correct`,
  `Spike.Test.Ret0ReleaseX64.ret0_correct`).
- **At the layout read off the executable** linked from that text, the
  placement check is kernel-decided, so the theorem applies there, with the
  only premise `hpa`. Three links: AArch64 `clang` + `ld.lld`
  (`Spike.Test.Ret0LinkedA64.ret0_linked_correct`); x86-64 GNU `as` + `ld
  -static` (`Spike.Test.Ret0LinkedX64.ret0_linked_correct`); x86-64 GNU `as`
  + `ld.lld -static` (`Spike.Test.Ret0LldX64.lld_linked_correct`).
- `certify.sh --instantiate` certifies a fresh build of `ret0.w` (and of any
  program it accepts, §4) at its `run.sh` link.

### What `Correct` promises

`Scc/Sem/Correct.lean`, module doc, and no more:

- *Refinement of observations* (`Sim.sim`): the observable trace of every
  reachable target configuration (its trace less the `writeErr`, `cloneErr`
  and `abort` events) is a **prefix** of the trace of a related source run.
  For `hello1` and `hello`, the observable events are the bytes written to
  fd 1 and the exit; `wake.w` writes nothing, so its only observable event is
  the exit.
- *Aborts only where justified* (`Sim.abort`): the target may abort (exit
  101) only where `AbortJustified` holds: the related source thread's next
  step would leave the budget `B`, or (for `writeErr`, `threads`) the kernel
  refused an earlier `write` or `clone`.
- *The budget*: `B` bounds heap cells, threads ever created and per-thread
  call depth (`Scc.Sem.Budget`). The `ret0` theorems hold for every `B`. The
  `hello1` theorems hold for every `B` with `B.cells = allocCells`
  (4194304 16-byte cells, the allocator's arena, `Scc/Cert/PlaceOK.lean`); the
  thread and frame bounds are free. The `wake` and `hello` theorems have the
  same `hB`.
- *No termination promise*: a target that diverges or blocks satisfies the
  statement. If the program exits, it exits as the source does, or aborts
  with exit 101 where `Correct` justifies it.

## 1. Statements (verbatim)

### `wake`, AArch64

`Spike/Test/WakeLinkedA64Root.lean`, with `asm`/`outLit` the certificate's
(`Spike.Test.Cert.A64WakeCert`), `wakeS` = `Spike.Lib.WakeA64.wakeS` and
`Le` = `Spike.Test.WakeLinkedA64.Le`, the placed runtime layout at `Λe`
(`Le.Λ` is `Λe` with the proof's immediate table `WakeFinalCAW.iW Λe` as
`imms`):

```lean
theorem wake_linkedU {arch : WeakMem.Arch} {B : Budget} (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame)
    /- the loader's check (the trust boundary; `#guard`-checked in `WakeLinkedA64`) -/
    (hP : Scc.Cert.Link.A64.parsesTo asm outLit.prog outLit.secs = true)
    /- the budget: the caller's choice -/
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    CorrectE 2 (wakeS arch) Le.Λ B asm
```

- `hP` is the loader's parse of `asm` into the certificate's program and
  data sections, as `hpa` for `hello1`; it is `#guard`-checked by
  evaluation (`WakeLinkedA64`, and again in `certify.sh`'s generated file).
- `hB` fixes `B.cells` to the allocator's arena; threads and frames are free.
- `ls0` and `frM` are proof parameters (per-entry label sizes and a frame of
  the invariant); they do not occur in the conclusion, so any values do
  (`certify.sh` passes constants).

`wakeS arch` is `SrcSem.source (srcPo 2 arch wakeSrc) wakeSrc`: the
WeakCore semantics of `wakeSrc`, the frontend's reading of `Scc/Test/wake.w`
(`Spike.Lib.WakeSrc.wakeSrcOk`, `#guard`), with two thread slots and `main`
started on its own `ThreadId` (`Spike/Lib/WakeA64.lean`, §3 item 14).

Root statement (`Spike/Lib/WakeFinalCAW.lean`):

```lean
theorem wake_finalCA_genWP (hp : PlaceW pcfg Λ0 SccCertificate.outLit)
    {arch : WeakMem.Arch} {B : Budget} {r0 r1 : ιR hp i → Range}
    /- the loader's check of the certificate (the trust boundary) -/
    (hP : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (Ly).Λ SccCertificate.outLit.prog SccCertificate.outLit.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (Ly).exe)
    (hsub1 : (WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.A64.Rt.CtrZ SccCertificate.outLit)
    (hnz : WakeOInit.NtZ Λ0 SccCertificate.outLit = true) (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- OPEN: the pre-spawn premises at `DW` -/
    (hO : ∀ E : Entry, E.Ok (Ly).Λ → OpenW hp i cT ls0 Ctx frM inv0 inv1 arch
      (WakeAssemblyR.MR hp i (WakeSpawnRP.parsed_outLit hP).1) r0 r1 E)
    /- the root's choices -/
    (hcT : ∀ E, cT E = WakeHG.cTW hp i) (hr0 : ∀ w, r0 w = WakeOSide.r0W hp i)
    (hr1 : ∀ w, r1 w = WakeOSide.r1W hp i) :
    CorrectE 2 (wakeS arch) (Ly).Λ B SccCertificate.asm
```

### `wake`, x86-64

`Spike/Test/WakeLinkedX64Root.lean` proves
`wake_linkedX : WakeLinkedXGoal ie`. The statement is the `Prop`
`WakeLinkedXGoal` of `Spike/Test/WakeLinkedX64.lean`, with
`asm`/`sizes`/`labelOffs`/`outLit` the certificate's
(`Spike.Test.Cert.X64WakeCert`) and `Λe` = `Spike.Test.WakeLinkedX64.Λe`:

```lean
abbrev wakeSX (arch : WeakMem.Arch) : SrcSem := SrcSem.source (SrcSem.srcPo 2 arch prog_src) prog_src
```

```lean
def WakeLinkedXGoal (ie : CoreTerm.Expr → String → Nat → Option Nat) : Prop :=
  ∀ {arch : WeakMem.Arch} {B : Budget},
    Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ outLit.prog outLit.secs = true →
    B.cells = Scc.Cert.PlaceOK.allocCells →
    Scc.Sem.X64.CorrectE 2 (wakeSX arch) { Λe with imms := ie } B ⟨asm, sizes, labelOffs⟩
```

```lean
theorem wake_linkedX : WakeLinkedXGoal ie
```

- `ie` is `Spike.Lib.X64.WakeImms.iW Λe` (`Spike/Test/WakeLinkedX64Le.lean`;
  `WakeLinkedX64Br.ie_eq`, `rfl`): the conclusion's layout is `Λe` with the
  proof's immediate table as `imms`, as `Le.Λ` on AArch64.
- The first premise (`hP`) is the loader's parse of the text
  `⟨asm, sizes, labelOffs⟩` into the certificate's program and data
  sections; it is `#guard`-checked by evaluation (`WakeLinkedX64`, and again
  in `certify.sh`'s generated file).
- The second (`hB`) fixes `B.cells` to the allocator's arena; threads and
  frames are free.
- Unlike `wake_linkedU`, `wake_linkedX` has no proof parameters: it fixes
  the per-entry label sizes and the invariant's frame to the constants that
  `certify.sh`'s AArch64 file passes. The general form
  `WakeLinkedX64RootL.wake_linkedXL` keeps them as parameters.

`wakeSX arch` is the WeakCore semantics of the certificate's `prog_src`, the
frontend's reading of `Scc/Test/wake.w`
(`#guard Scc.Cert.SrcTerm.reads (w_src% "Scc/Test/wake.w") prog_src`), with
two thread slots and `main` started on its own `ThreadId`. Unlike AArch64,
it uses `Scc.Sem.SrcSem.srcPo` itself, not a local copy; the proof's own
source semantics is identified with it by `WakeLinkedX64Br.wakeSrc_eq` and
`wakeS_eq`.

Root statement (`Spike/Lib/X64WakeLandU.lean`):

```lean
theorem wake_finalX_land {arch : WeakMem.Arch} {B : Budget}
    (hP : Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ outLit.prog outLit.secs).initVal
      ⟨Spike.Lib.X64WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hsub1 : (Spike.Lib.X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ outLit)
    (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 outLit = true)
    (hpl0 : ∀ s, PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0W [])
    (hlft : Spike.Lib.X64.WakePh.StartH0C.HabLft (Ly)) {F0 : MachineData → Prop}
    (hB1 : ∀ E : Entry, E.Ok (Ly).Λ → HB1) (hF0 : HF0)
    (hst : ∀ E : Entry, E.Ok (Ly).Λ →
      inv0G hp i (cTR) ls0 (CtxRU hp i c0W ls0) frM E
        (threadAt E (Ly).Λ.code.lo outLit.prog (loadSyms (Ly).Λ outLit.secs.rodata))
        ⟨Spike.Lib.X64WakePreAsm.wakeTh0.term, Spike.Lib.X64WakePreAsm.wakeTh0.env, none⟩
        Spike.Lib.X64WakePreAsm.wakeTh0.stack) :
    CorrectE 2 (wakeS arch) (Ly).Λ B certAsm
```

At this level some premises are still open: `wake_finalCA_genWP`'s `hO`,
and `wake_finalX_land`'s `hpl0`, `hlft`, `hB1`, `hF0` and `hst`.
`wake_linkedU` and `wake_linkedX` discharge them at `Λe`.

### `hello`, AArch64

`Spike/Test/HelloLinkedA64Root.lean`, with `SccCode.helloAsm`,
`helloProg`, `helloSecs` the listing and its loader parse
(`Spike/Lib/A64HelloCode.lean`), `helloS` = `Spike.Lib.HelloSrc.helloS` and
`Le` = `Spike.Test.HelloLinkedA64.Le`, the placed runtime layout at `Λe`
(`Le.Λ` is `Λe` with the proof's immediate table `ImmsMe.iRdM Λe` as
`imms`):

```lean
theorem hello_linkedA {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    (hparse : Scc.Cert.Link.A64.parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.A64.CorrectE 2 (Spike.Lib.HelloSrc.helloS arch) Le.Λ B SccCode.helloAsm
```

It is `RootFinal.hello_correct` at the layout facts `layoutE_e : LayoutE Λe`.
The general statement (`Spike/Lib/A64HelloRootFinal.lean`) holds at every
layout `Λ0` with those facts:

```lean
theorem hello_correct {Λ0 : Scc.Sem.Layout} (F : LayoutE Λ0) {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    (hparse : parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.A64.CorrectE 2 (helloS arch) (RuntimeLayout.ofPlaceW F.hp (iRdM Λ0)).Λ B SccCode.helloAsm
```

and, per admissible entry, the root's obligations:

```lean
theorem hello_root_final {Λ0 : Scc.Sem.Layout} (F : LayoutE Λ0) {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    {E : Scc.Sem.Entry} {ls : Spike.Lib.A64Consumer.Lsize}
    (hparse : parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) (hE : E.Ok (RuntimeLayout.ofPlaceW F.hp (iRdM Λ0)).Λ) :
    WakeObligationsR arch (RuntimeLayout.ofPlaceW F.hp (iRdM Λ0)).Λ B SccCode.helloAsm
      (RootLit.QRoot (arch := arch) (E := E) (ls := ls) F.hp (i0M Λ0) hparse F.hlo (ImmsMe.immsKid_root F.hp)) E
      (fun t tr => TiPre (AbH F.hp (iRdM Λ0)) (AcH F.hp (iRdM Λ0)) t tr ∧
        TwH (RuntimeLayout.ofPlaceW F.hp (iRdM Λ0)).Λ E (AbH F.hp (iRdM Λ0)) t tr)
      helloSrc
```

`LayoutE Λ0` (`Spike/Lib/A64HelloRootBaseInh.lean`) is the linked layout's
facts: `PlaceW` (A1, A2, A4, A6, A8), `.text` at hello's phase base
`WakePh.lo` (`0x210550`), no static words, `scc_rt_nthreads` starting at 0,
A13's data part at the placed layout, and the second TCB's limit word
starting at 0.

- `hparse` is the loader's parse of `helloAsm` into `helloProg` and
  `helloSecs`, the trust boundary as `hP` is for `wake`; it is
  `#guard`-checked by evaluation (`HelloLinkedA64Root`).
- `hB` fixes `B.cells` to the allocator's arena; threads and frames are free.
- `hello_root_final`'s `ls` (level 0's label sizes) does not occur in
  `hello_correct`'s conclusion.

`helloS arch` is `Spike.Lib.WakeA64.srcS helloSrc arch` (`Spike/Lib/HelloSrc.lean`):
the WeakCore semantics of `helloSrc`, the frontend's reading of
`Scc/Test/hello.w` (`helloSrcOk`, `#guard`), with two thread slots and
`main` started on its own `ThreadId` (wake's source machine, §3 item 14).

### `hello`, x86-64

`Spike/Test/HelloLinkedX64Root.lean`, with `SccCode.helloAsm`,
`helloCells`, `helloSecs` the listing, its code cells and its loader parse
(`Spike/Lib/X64HelloCode.lean`), `iH := iRdM Λe` the proof's immediate
table, and `helloSX` the source semantics fixed in
`Spike/Test/HelloLinkedX64.lean` (`helloS_eq` identifies it with the proof's
`Spike.Lib.X64HelloSrc.helloS`):

```lean
theorem hello_linkedX : HelloLinkedXGoal Λe iH
```

`HelloLinkedXGoal` is stated before the proof (`Spike/Test/HelloLinkedX64.lean`;
every proof module is downstream of it):

```lean
def HelloGoalAt (Λ : Scc.Sem.Layout) : Prop :=
  ∀ {arch : WeakMem.Arch} {B : Scc.Sem.Budget},
    Scc.Cert.Link.X64.parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true →
    B.cells = Scc.Cert.PlaceOK.allocCells →
    Scc.Sem.X64.CorrectE 2 (helloSX arch) Λ B SccCode.helloAsm

def HelloLinkedXGoal (Λ0 : Scc.Sem.Layout) (iH : CoreTerm.Expr → String → Nat → Option Nat) : Prop :=
  HelloGoalAt { Λ0 with imms := iH }
```

At the Linux entry, which is admissible at `Le.Λ` (`linux_ok_e`):

```lean
theorem hello_linkedX_linux {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    (hparse : Scc.Cert.Link.X64.parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.Correct (Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) .linux)
      (Spike.Lib.X64HelloSrc.helloS arch) Le.Λ B SccCode.helloAsm
```

`hello_linkedX` is `RootFinal.hello_correct` at the layout facts
`layoutEX_e : LayoutEX Λe`. The general statement
(`Spike/Lib/X64HelloRootFinal.lean`) holds at every layout `Λ0` with those
facts:

```lean
theorem hello_correct {Λ0 : Scc.Sem.Layout} (F : LayoutEX Λ0) {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    (hparse : parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.X64.CorrectE 2 (helloS arch) (RuntimeLayout.ofPlaceWX F.hp (iRdM Λ0)).Λ B SccCode.helloAsm
```

and, per admissible entry, the root's obligations:

```lean
theorem hello_root_final {Λ0 : Scc.Sem.Layout} (F : LayoutEX Λ0) {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    {E : Scc.Sem.Entry} {ls : Spike.Lib.X64Consumer.Lsize}
    (hparse : parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) (hE : E.Ok (RuntimeLayout.ofPlaceWX F.hp (iRdM Λ0)).Λ) :
    WakeObligationsR arch (RuntimeLayout.ofPlaceWX F.hp (iRdM Λ0)).Λ B SccCode.helloAsm
      (RootLit.QRoot (arch := arch) (E := E) (ls := ls) F.hp (i0M Λ0) hparse F.hlo
        ⟨Spike.Lib.X64.HelloImms.kid_root F.hp, Spike.Lib.X64.HelloImms.wcall_root F.hp⟩) E
      (fun t tr => TiPre (AbH F.hp (iRdM Λ0)) (AcH F.hp (iRdM Λ0)) t tr ∧
        TwH (RuntimeLayout.ofPlaceWX F.hp (iRdM Λ0)).Λ E (AbH F.hp (iRdM Λ0)) t tr)
      helloSrc
```

`LayoutEX Λ0` (`Spike/Lib/X64HelloLayoutE.lean`) is the linked layout's
facts: `PlaceWX` (every component of `placeOK2At`), `.text` at hello's phase
base `X64.HelloPh.lo` (`0x401000`, GNU `ld`'s default), no static words,
`scc_rt_nthreads` starting at 0, A13's data part at the placed layout, the
200 bytes from the first TCB's address `pinA` inside the pinned region
(`hpin2`), the second TCB's limit word starting at 0, and the child's stack
range inside the stack pool.

- `hparse` is the loader's parse of `helloAsm` into `helloCells` and
  `helloSecs`, the trust boundary as for AArch64; it is `#guard`-checked by
  evaluation (`HelloLinkedX64Root`).
- `hB` fixes `B.cells` to the allocator's arena; threads and frames are free.
- `hello_root_final`'s `ls` (level 0's label sizes) does not occur in
  `hello_correct`'s conclusion.

`helloS arch` is `Spike.Lib.X64WakeA64.srcS helloSrc arch`
(`Spike/Lib/X64HelloSrc.lean`), at the same `helloSrc` as on AArch64.

**Where the x86-64 proof differs from the AArch64 one.** None of these
changes the statement's form.

- **Thread pointers live in memory.** x86-64 threads reach their TCB through
  the `%fs` base, so each thread's self word is read from memory (AArch64:
  `TPIDR_EL0`). Main's memory side owns its TCB's self word and the worker's
  side its own; main owns both up to the clone. The root's map of owned words
  is the canonical one plus both self words (`ownGHXW`), and the worker's
  rows and levels 1 and 2 are stated at any map of owned words (through
  `Own1H`, `Spike/Lib/X64HelloOwn1.lean`). `wake`'s x86-64 map with the self
  words is `wakeOwnXW` (`Spike/Lib/X64WakeOwnXW.lean`).
- **Publication is a source stutter.** The publishing store lands between
  two source steps rather than inside a row (AArch64's `stlr`), so segments
  may start their rows after the publication (`Spike/Lib/X64SegWPub.lean`).
- **The clone's arguments.** `clone(flags, k, 0, 0, t)` takes its fourth
  argument in `%r10` (AArch64: `x3`); the clone's decode reads `%rax = 56`,
  `%rdi = cloneFlags` and `%rdx = %r10 = 0`
  (`X64HelloWcInv.clone_decode_of_postH`). The child's `%rbp` is live at the
  clone.
- **Sized instructions.** A block's pcs are byte offsets (AArch64: `4k`);
  system calls are `syscall`, decoded from `%rax` (AArch64: `svc`, `x8`); a
  `ret`'s target is the slot at `%rsp` (AArch64: `x30`); release writes are
  stated per state under `Arch.tso`.
- **Layout facts.** They are one structure over all of `placeOK2At`
  (`LayoutEX`), inhabited at `Λe` and at `Λ1`
  (`Spike/Test/HelloLinkedX64L1.lean`), the listing's static link at GNU
  `ld`'s section bases, which needs no executable.

Every `Spike/Lib/X64Hello*.lean` module doc records its differences from
the AArch64 twin.

### `hello1`, AArch64

`Spike/Test/A64Hello1FinalCA.lean`, with its local notations
`P1A` = `Spike.Test.Hello1MainSrc.hello1o` and
`LeA` = `Spike.Test.Hello1LinkedA64.Λe`:

```lean
theorem hello1_finalCA
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
      SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 LeA P1A) B
      SccCertificate.asm
```

### `hello1`, x86-64

`Spike/Test/X64Hello1FinalC.lean`, with `P1` = `Spike.Test.Hello1MainSrc.hello1o`
and `Le` = `Spike.Test.Hello1LinkedX64.Λe`:

```lean
theorem hello1_finalC
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Le P1) B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
```

In both, `B` and `arch` are implicit and universally quantified; the two
explicit premises are:

- **`hpa`**: the certificate's assembly text parses (Kraken's parser and the
  data-section reader) to the compiler's output `outLit`. It is the one step
  checked by compiled evaluation rather than by the kernel: a `#guard` on
  exactly these constants in `Spike/Test/{A64,X64}Hello1Final.lean`, and the
  certificate's own `#guard … parsesTo asm out.prog out.secs` (`outLit` is
  `out` by the kernel-checked `out_eq`). The parser is `partial`, so the
  kernel cannot evaluate it; the theorem keeps it as a premise.
- **`hB`**: the budget's heap-cell count is the allocator's arena size,
  `allocCells`, the constant the runtime's allocator compares its counter
  with (tied to the code by `allocCells_eq_lit`, checked by A7). Source runs
  that would need more heap than that are the ones the target may abort.

The pieces of the conclusion:

- `hello1o` is `hello1.w`'s program with `print` linked: its WeakCore model
  `printL`/`print` (`Spike/Lib/PrintSrc.lean`), a loop that loads each word
  of the slice and `emit`s its bytes, in place of the extern's empty body.
  `Spike/Test/Hello1MainSrc.lean` checks by `#guard` that the rest is the
  frontend's reading of `hello1.w`, and `hello1_out_eq`/`hello1_out_eqA`
  (`Spike/Test/{X64,A64}Hello1Closed2.lean`, kernel-checked) that its
  compiled output is the certificate's `out`: `print` adds no code.
- `srcP1o arch p` (`Scc/Sem/SrcOut.lean`): the single-thread source
  parameters with WeakCore's extern step and event list.
- `lay2 Λ p` (`Spike/Lib/Lower{A64,X64}/Closed2Of(A).lean`) is
  `{ Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p }`:
  no static label, and the lowering's immediates with the first TCB as `me`
  at the setup start.
- `CorrectE 1` is `Correct` over the kernel-model target with one thread
  slot, at every entry state that `Entry.Ok` admits.

`hello1_finalCA` and `hello1_finalC` are `hello1_finalCA_of hello1_openAPtA`
and `hello1_finalC_of hello1_allocPt`: the `_of` forms (same files) state the
same conclusion from the allocator's per-allocation premises, and
`hello1_openAPtA` (`Spike/Test/A64Hello1HA.lean`) and `hello1_allocPt`
(`Spike/Test/X64Hello1AllocPt.lean`) prove them.

The placement check at `Λe` is `hello1_placeOKAt : A64.placeOKAt placeCfg
Λe out = true` / `hello1_placeOKAt : X64.placeOKAt placeCfg Λe out = true`
(`Spike/Test/Hello1Linked{A64,X64}.lean`, §2).

### `hello1` at every layout passing the placement check

The closed statements above are the following at `Λe` (same files; `OA` /
`OX` is the certificate's compiled output):

```lean
theorem hello1_finalCA_gen (Λ : Scc.Sem.Layout)
    (hΛ : placeOKAt SccCertificate.placeCfg Λ OA = true)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
      SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 Λ P1A) B
      SccCertificate.asm
```

```lean
theorem hello1_finalC_gen (Λ : Scc.Sem.Layout)
    (hΛ : placeOKAt SccCertificate.placeCfg Λ OX = true)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Λ P1) B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
```

Their entry quantifier is not vacuous: `hello1_ok_witness_of_placeOKAtA` /
`hello1_ok_witness_of_placeOKAt` give, at any layout passing the check, an
admissible entry state (a 64 KiB stack at `2 ^ 32`). `certify.sh` uses both
(§2, §4).

### The fragment-generic statements

`Spike/Lib/LowerA64/Closed2StmtA.lean` and
`Spike/Lib/LowerX64/Closed2Stmt.lean` state the compiler theorem for every
`Accepted2` program (setup block, `newBuf`, lane stores, `print`) whose
`main` ends on every path in a call returning its result or a literal
(`mainRetOk`). They are stated as `Prop`s; this release proves them at the
header bound (*The `Accepted2` statements, proved at the header bound*,
below):

```lean
def Closed2StmtA : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : CoreTerm.Prog) (Λ : Scc.Sem.Layout),
    Scc.Lower.Accepted2 p = true → Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true →
    CfgNeedOkA pcfg = true →
    ∀ {asm : String}, Scc.Cert.Link.A64.parsesTo asm
      (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
      (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs = true →
    ∀ {B : Scc.Sem.Budget}, B.cells = Scc.Cert.PlaceOK.allocCells → ∀ {arch : WeakMem.Arch},
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B asm
```

```lean
def Closed2Stmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : CoreTerm.Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout), Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    CfgNeedOk pcfg = true →
    ∀ {text : String}, Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs = true →
    ∀ {B : Scc.Sem.Budget}, B.cells = Scc.Cert.PlaceOK.allocCells → ∀ {arch : WeakMem.Arch},
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B ⟨text, sizes, labelOffs⟩
```

Without the header bound, what the tree proves about them is conditional:

- `a64_scc_correctE_text_closedAt2 (H : Closed2InA) : Closed2StmtA`
  (`Spike/Lib/LowerA64/Closed2AtA.lean`) and
  `x64_scc_correctE_text_closedAt2 (H : Closed2In) : Closed2Stmt`
  (`Spike/Lib/LowerX64/Closed2At.lean`): each from the segment obligations
  `Closed2In(A)` (`In2A`/`In2X` at every instance and admissible entry state),
  which are not proved for the fragment as a whole. No theorem in the tree
  proves `Closed2Stmt` or `Closed2StmtA` outright; `Closed2StmtH` and
  `Closed2StmtAH`, which add the header bound, are proved.
- `hello1` discharges these obligations for its own instance only, which is
  what `hello1_finalC(A)` packages.
- `hello1_of_closed2A (H : Closed2StmtA)` / `hello1_of_closed2 (H :
  Closed2Stmt)` (`Spike/Test/{A64,X64}Hello1Closed2.lean`) check that the
  generic statement, once proved, instantiates at `hello1`.

### `ret0`, AArch64

`Spike/Test/Ret0ReleaseA64.lean`:

```lean
theorem ret0_correct (Λ : Scc.Sem.Layout) (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (h : Scc.Cert.PlaceOK.A64.placeOKAt placeCfg Λ out = true)
    (hpa : Scc.Cert.Link.A64.parsesTo asm out.prog out.secs = true) :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) prog_src)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf main } B asm

theorem ok_witness_of_placeOKAt {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt placeCfg Λ out = true) :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf main }
```

(`ret0_correct_tables` is `ret0_correct` at the certificate's own static
link, where the certificate proves `h`.)

`Spike/Test/Ret0LinkedA64.lean`, where
`def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/ret0a64/ret0"`
and `abbrev Λe : Scc.Sem.Layout := elf.1`:

```lean
theorem ret0_codeEnd : Scc.Sem.A64.codeEnd Λe.code.lo outLit.prog = Λe.code.lo + Λe.code.size
theorem ret0_placeOKAt : A64.placeOKAt placeCfg Λe out = true
theorem ret0_linked_correct (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.A64.parsesTo asm out.prog out.secs = true) :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseA64.main } B
      asm
theorem ret0_linked_witness :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseA64.main }
```

### `ret0`, x86-64

`Spike/Test/Ret0ReleaseX64.lean`:

```lean
theorem ret0_correct (Λ : Scc.Sem.Layout) (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (h : Scc.Cert.PlaceOK.X64.placeOKAt placeCfg Λ out = true)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs = true) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) prog_src)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf main } B ⟨asm, sizes, labelOffs⟩
```

(`ret0_correct_tables` and `ok_witness_of_placeOKAt` as on AArch64, with
`Scc.Cert.PlaceOK.X64.placeOKAt`.)

`Spike/Test/Ret0LinkedX64.lean` (GNU `ld`, fixture `Scc/Test/elf/ret0x64/ret0`)
and `Spike/Test/Ret0LldX64.lean` (`ld.lld`, fixture
`Scc/Test/elf/ret0x64lld/ret0`), each with `Λe := elf.1` read from its
fixture:

```lean
theorem ret0_codeEnd : Scc.Sem.X64.codeEnd Λe.code.lo outLit.prog = Λe.code.lo + Λe.code.size
theorem ret0_placeOKAt : X64.placeOKAt placeCfg Λe out = true
theorem ret0_linked_correct (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs = true) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main } B
      ⟨asm, sizes, labelOffs⟩
theorem ret0_linked_witness :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main }
```

`Ret0LldX64` states the same four theorems as `lld_codeEnd`,
`lld_placeOKAt`, `lld_linked_correct` and `lld_linked_witness`.

### The generic compiler theorems behind `certify.sh`

`a64_scc_correctE_text_closedAt` and `x64_scc_correctE_text_closedAt`
(`Spike/Lib/Lower{A64,X64}/Correct.lean`) are the `Accepted0` theorems of the
previous release, unchanged: hypothesis `hd : Scc.Lower.Accepted0 [d] =
true`, immediates `immsOf d`, otherwise as below. For the `Accepted1`
fragment (`Scc/Lower/Spec1.lean`: non-recursive calls to earlier code
blocks, integer `if` and `-`), `Spike/Lib/Lower{A64,X64}/Correct1.lean`:

```lean
theorem a64_scc_correctE_text_closedAt1 (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (O).prog (O).secs = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B asm

theorem x64_scc_correctE_text_closedAt1 (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) (hfr : MainFrame1Ok cfg d = true) {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B ⟨text, sizes, labelOffs⟩
```

On AArch64 the text is the bare `asm` string: instructions are 4 bytes, so
there is no `sizes`/`labelOffs` table.

### The compiler theorems on the post-pass text (`--granule`)

New in this release. `Spike/Lib/Lower{A64,X64}/CorrectFinal.lean` state the
twins of the theorems above for the output after the granule pass, `F`
(local notation: `Scc.Cert.Granule.{X64,A64}.ofFinal … final`, the
lowering's stage with the pass's items `final`). In place of `placeOKAt` and
the parse of scc's output `O`, they take the stages of the lowering and the
emitter (`h1`, `h2`, `h3`), the pass check (`hc`: the post-pass items
`Expand` the emitter's), on x86-64 that the post-pass program fits the sizes
(`hz`), the post-pass block table (`hb`), and `placeOKAt` and the loader's
parse (`hpa`) on `F` itself. Nothing about the pre-pass layout is
transferred. The conclusion is the same as the twin's.

`a64_scc_correctE_text_closedAt1_final` (`Spike/Lib/LowerA64/CorrectFinal.lean`):

```lean
theorem a64_scc_correctE_text_closedAt1_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    {ir : Scc.IR.Program} {setup : Bool} {items final tits : List Scc.Emit.A64.Item}
    {sps : List Scc.Emit.A64.Safepoint} {blks : List Scc.Cert.Rt.A64.OGrp} {tbl : List Kraken.DataImage.Item}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.A64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.A64.check final items = true)
    (hb : Scc.Cert.Granule.A64.blocksOfFinal ir final = some blks)
    (h : placeOKAt pcfg Λ (F) = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (F).prog (F).secs = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B asm
```

Against `a64_scc_correctE_text_closedAt1` (as quoted in the previous release's note):

```diff
--- previous a64_scc_correctE_text_closedAt1
+++ this release a64_scc_correctE_text_closedAt1_final
@@ -1,4 +1,10 @@
-theorem a64_scc_correctE_text_closedAt1 (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
-    (h : placeOKAt pcfg Λ (O) = true) {asm : String}
-    (hpa : Scc.Cert.Link.A64.parsesTo asm (O).prog (O).secs = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
+theorem a64_scc_correctE_text_closedAt1_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
+    {ir : Scc.IR.Program} {setup : Bool} {items final tits : List Scc.Emit.A64.Item}
+    {sps : List Scc.Emit.A64.Safepoint} {blks : List Scc.Cert.Rt.A64.OGrp} {tbl : List Kraken.DataImage.Item}
+    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps))
+    (h3 : Scc.Lower.A64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
+    (hc : Scc.Cert.Granule.A64.check final items = true)
+    (hb : Scc.Cert.Granule.A64.blocksOfFinal ir final = some blks)
+    (h : placeOKAt pcfg Λ (F) = true) {asm : String}
+    (hpa : Scc.Cert.Link.A64.parsesTo asm (F).prog (F).secs = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
     Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
```

`x64_scc_correctE_text_closedAt1_final` (`Spike/Lib/LowerX64/CorrectFinal.lean`):

```lean
theorem x64_scc_correctE_text_closedAt1_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (hfr : MainFrame1Ok cfg d = true) {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks)
    (h : placeOKAt pcfg Λ (F) = true) {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (F).prog (F).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B ⟨text, sizes, labelOffs⟩
```

Against `x64_scc_correctE_text_closedAt1` (as quoted in the previous release's note):

```diff
--- previous x64_scc_correctE_text_closedAt1
+++ this release x64_scc_correctE_text_closedAt1_final
@@ -1,4 +1,13 @@
-theorem x64_scc_correctE_text_closedAt1 (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
-    (h : placeOKAt pcfg Λ (O) = true) (hfr : MainFrame1Ok cfg d = true) {text : String}
-    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
+theorem x64_scc_correctE_text_closedAt1_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
+    (hfr : MainFrame1Ok cfg d = true) {ir : Scc.IR.Program} {setup : Bool}
+    {items final tits : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
+    {tbl : List Kraken.DataImage.Item}
+    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
+    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
+    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
+    (hc : Scc.Cert.Granule.X64.check final items = true)
+    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
+    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks)
+    (h : placeOKAt pcfg Λ (F) = true) {text : String}
+    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (F).prog (F).secs = true)
     {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
```

`x64_scc_correctE_text_closedAt_final` (`Spike/Lib/LowerX64/CorrectFinal.lean`):

```lean
theorem x64_scc_correctE_text_closedAt_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks)
    (h : placeOKAt pcfg Λ (F) = true) {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (F).prog (F).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := immsOf d } B ⟨text, sizes, labelOffs⟩
```

Against `x64_scc_correctE_text_closedAt` (at the previous release, `Spike/Lib/LowerX64/Correct.lean`):

```diff
--- previous x64_scc_correctE_text_closedAt
+++ this release x64_scc_correctE_text_closedAt_final
@@ -1,4 +1,13 @@
-theorem x64_scc_correctE_text_closedAt (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
-    (h : placeOKAt pcfg Λ (O) = true) {text : String}
-    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
+theorem x64_scc_correctE_text_closedAt_final (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
+    {ir : Scc.IR.Program} {setup : Bool}
+    {items final tits : List Scc.Emit.X64.Item} {sps : List (String × List Int × List Int)}
+    {tbl : List Kraken.DataImage.Item}
+    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
+    (h1 : lowered1 cfg [d] = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
+    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
+    (hc : Scc.Cert.Granule.X64.check final items = true)
+    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
+    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks)
+    (h : placeOKAt pcfg Λ (F) = true) {text : String}
+    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (F).prog (F).secs = true)
     {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
```

### The `Accepted2` statements, proved at the header bound

New in this release. `Closed2StmtA` and `Closed2Stmt` (above) are proved at
every configuration whose object layout's header scalar count starts below
bit 22 (`Scc.Obj.nShift cfg.layout.obj < 22`), the configuration premise of
the theorems. The statements are `Closed2StmtA`/`Closed2Stmt` with that
premise added:

`Closed2StmtAH` (`Spike/Lib/LowerA64/Closed2StmtAH.lean`):

```lean
def Closed2StmtAH : Prop :=
  ∀ (cfg : Scc.Config), Scc.Obj.nShift cfg.layout.obj < 22 →
  ∀ (pcfg : Scc.Cert.PlaceOK.Config) (p : CoreTerm.Prog) (Λ : Scc.Sem.Layout),
    Scc.Lower.Accepted2 p = true → Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true →
    CfgNeedOkA pcfg = true →
    ∀ {asm : String}, Scc.Cert.Link.A64.parsesTo asm
      (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
      (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs = true →
    ∀ {B : Scc.Sem.Budget}, B.cells = Scc.Cert.PlaceOK.allocCells → ∀ {arch : WeakMem.Arch},
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B asm
```

`Closed2StmtH` (`Spike/Lib/LowerX64/G1Closed2Final.lean`):

```lean
def Closed2StmtH : Prop :=
  ∀ (cfg : Scc.Config), Scc.Obj.nShift cfg.layout.obj < 22 →
  ∀ (pcfg : Scc.Cert.PlaceOK.Config) (p : CoreTerm.Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout), Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    CfgNeedOk pcfg = true →
    ∀ {text : String}, Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs = true →
    ∀ {B : Scc.Sem.Budget}, B.cells = Scc.Cert.PlaceOK.allocCells → ∀ {arch : WeakMem.Arch},
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B ⟨text, sizes, labelOffs⟩
```

`closed2StmtAH_final : Closed2StmtAH` (`Spike/Lib/LowerA64/Closed2StmtAH.lean`)
and `closed2Stmt_x64_final : Closed2StmtH`
(`Spike/Lib/LowerX64/G1Closed2X64.lean`) prove them with no premises.
`certify.sh` does not instantiate them: it still certifies `Accepted0`/
`Accepted1` programs and the registry (§5).

### The granule instances at the linked post-pass executables

New in this release. The granule pass leaves the compiler's cells with the
end label `scc_text_end` replaced by a tail (a `.zero` filler, `.Lgw0:`, the
descriptor word and `scc_text_end`) and the data sections unchanged. The
theorems below are about the post-pass text at the layout of the checked-in
`Scc/Test/elf/*g/` executable, each given the loader's parse of that text
(`hpa`/`hpaF`, checked by a compiled `#guard`, the trust boundary as for the
other instances).

The generic theorems they use, for a text whose cells are the compiler's
with the end label replaced by an instruction-free tail: on AArch64, the
twins of `a64_scc_correctE_text_closedAt1` and its `Accepted0` corollary,
from the placement check of the output with the tail and the lowering's
success (`hlow`); on x86-64, for an `Accepted2` program, from the stages a
certificate decides and both placement checks (the compiler's output, `hE`,
and the post-pass output, `hF`):

`a64_scc_correctE_text_closedAt1_tail` (`Spike/Lib/LowerA64/Correct1Tail.lean`):

```lean
theorem a64_scc_correctE_text_closedAt1_tail (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
    (hlow : ∃ em, Scc.Lower.A64.lowerAll? cfg [d] = .ok em) {T : Program}
    (h : placeOKAt pcfg Λ (withTail (O) T) = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (withTail (O) T).prog (withTail (O) T).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B asm := by
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (withTail (O) T) = true
```

Against `a64_scc_correctE_text_closedAt1` (`Spike/Lib/LowerA64/Correct1.lean`, the previous release):

```diff
--- previous a64_scc_correctE_text_closedAt1
+++ this release a64_scc_correctE_text_closedAt1_tail
@@ -1,5 +1,8 @@
-theorem a64_scc_correctE_text_closedAt1 (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
-    (h : placeOKAt pcfg Λ (O) = true) {asm : String}
-    (hpa : Scc.Cert.Link.A64.parsesTo asm (O).prog (O).secs = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
+theorem a64_scc_correctE_text_closedAt1_tail (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted1 [d] = true)
+    (hlow : ∃ em, Scc.Lower.A64.lowerAll? cfg [d] = .ok em) {T : Program}
+    (h : placeOKAt pcfg Λ (withTail (O) T) = true) {asm : String}
+    (hpa : Scc.Cert.Link.A64.parsesTo asm (withTail (O) T).prog (withTail (O) T).secs = true)
+    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
     Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
-      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B asm
+      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of [d] } B asm := by
+  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (withTail (O) T) = true
```

`a64_scc_correctE_text_closedAt_tail` (`Spike/Lib/LowerA64/Correct1Tail.lean`):

```lean
theorem a64_scc_correctE_text_closedAt_tail (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    (hlow : ∃ em, Scc.Lower.A64.lowerAll? cfg [d] = .ok em) {T : Program}
    (h : placeOKAt pcfg Λ (withTail (O) T) = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (withTail (O) T).prog (withTail (O) T).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf d } B asm
```

`x64_scc_correctE_text_closedAt2_final` (`Spike/Lib/LowerX64/Closed2TailFinal.lean`):

```lean
theorem x64_scc_correctE_text_closedAt2_final (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22)
    {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizesE : List Nat} {labelOffsE : List (String × Nat)}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (hp : Scc.Lower.Accepted2 p = true) (hR : Scc.Lower.mainRetOk p = true)
    (hE : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizesE labelOffsE) = true)
    (hcfg : CfgNeedOk pcfg = true)
    {ir : Scc.IR.Program} {setup : Bool} {items final tits : List Scc.Emit.X64.Item}
    {sps : List (String × List Int × List Int)} {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks)
    (hF : placeOKAt pcfg Λ (Scc.Cert.Granule.X64.ofFinal sizes labelOffs
      (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final) = true)
    {P T : List (Directive × Nat)} {te : String} {B : List String}
    (hPE : (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizesE labelOffsE).prog = P ++ [(.label te, 0)])
    (hPF : cs = P ++ T)
    (hte : te ∈ B) (hT : ∀ dz ∈ T, ∀ l, dz.1 = .label l → l ∈ B) (hTi : ∀ dz ∈ T, ∀ i, dz.1 ≠ .instr i)
    (hfree : ∀ i z, (Directive.instr i, z) ∈ P → Directive.Free B (.instr i))
    (hs : ∀ k : XferKind, k.label ∉ B) (ha : ∀ k, Λ.abortLbl k ∉ B) (hn : ∀ x ∈ rtNames, x ∉ B)
    (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B)
    {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩
      (Scc.Cert.Granule.X64.ofFinal sizes labelOffs
        (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final).prog
      (Scc.Cert.Granule.X64.ofFinal sizes labelOffs
        (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final).secs = true)
    {Bu : Budget} (hB : Bu.cells = allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (SrcSem.source (SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } Bu ⟨text, sizes, labelOffs⟩ := by
  obtain ⟨hf, -, -, -, -, -, hfp, -, -⟩
```

The instances (each `#print axioms`: `propext`, `Classical.choice`,
`Quot.sound`, checked by `#guard_msgs` in its file or as listed in §1
*Axioms*; the axiom run printed these three for `hello1_finalCAG`,
`hello1_finalCAG_of`, `hello1_finalCF`, both `ret0_linked_correctG`,
`lld_linked_correctG`, `ret0_correctG` and
`x64_scc_correctE_text_closedAt2_final`, and the files of the placement-only
instances built without error):

- **`hello1`, AArch64** (`Scc/Test/elf/hello1a64g/hello1`): `hello1_finalCAG`,
  `hello1_finalCAG_of` (`Spike/Test/A64Hello1FinalCAG.lean`) at the
  executable's layout `ΛG`, where the placement check holds for both the
  certificate's output and the output with the tail.
- **`hello1`, x86-64** (`Scc/Test/elf/hello1x64g/hello1`): `hello1_finalCF`,
  `x64_scc_correctE_text_closedAt2_final` at the post-pass output computed
  from the certificate's literals (`Spike/Test/X64Hello1GOut.lean`), with
  the pre-pass output's placement check at the post-pass layout
  (`Hello1LinkedX64G.pre_placeOKAt`) and the post-pass output's
  (`Hello1LinkedX64GPost.post_placeOKAt`).
- **`ret0`**: AArch64 (`Scc/Test/elf/ret0a64g/ret0`), `ret0_linked_correctG`
  (`Spike/Test/Ret0LinkedA64G.lean`, from `a64_scc_correctE_text_closedAt_tail`);
  x86-64 with GNU `ld` (`Scc/Test/elf/ret0x64g/ret0`), `ret0_linked_correctG`
  (`Spike/Test/Ret0LinkedX64G.lean`), and with `ld.lld`
  (`Scc/Test/elf/ret0x64lldg/ret0`), `lld_linked_correctG`
  (`Spike/Test/Ret0LldX64G.lean`), both from `ret0_correctG`
  (`Spike/Test/X64Ret0GOut.lean`: `x64_scc_correctE_text_closedAt_final` at
  any layout where the post-pass output passes the placement check).
- **`call1`** (AArch64 and x86-64) **and `frame0`** (x86-64): placement only.
  `call1G_placeOKAt` (`Spike/Test/Call1LinkedA64G.lean`,
  `Spike/Test/Call1LinkedX64G.lean`) and `frame0G_placeOKAt`
  (`Spike/Test/Frame0LinkedX64G.lean`) prove the placement check of the
  post-pass output at the executable's layout; no correctness theorem is
  stated, as for their pre-pass executables. With one instruction of
  `pick` replaced, A12 fails and so does the placement check, while A9
  passes (`perturbedG_not_placeOKAt`/`perturbed_not_placeOKAt`,
  `perturbedG_a9`/`perturbed_a9`).

`hello1_finalCAG` (`Spike/Test/Hello1LinkedA64G.lean`):

```lean
theorem hello1_finalCAG (hpa : Scc.Cert.Link.A64.parsesTo asmG outF.prog outF.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1
      (SrcSem.source (SrcSem.srcP1o arch Spike.Test.Hello1MainSrc.hello1o) Spike.Test.Hello1MainSrc.hello1o)
      (Spike.Lib.LowerA64.lay2 ΛG Spike.Test.Hello1MainSrc.hello1o) B asmG := by
  have h0 : A64.placeOKAt placeCfg ΛG (Scc.Cert.PlaceOK.A64.Out.ofEmitted
      (Scc.Lower.A64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)) = true
```

Against `hello1_finalCA` (`Spike/Test/A64Hello1FinalCA.lean`, the previous release):

```diff
--- previous hello1_finalCA
+++ this release hello1_finalCAG
@@ -1,6 +1,7 @@
-theorem hello1_finalCA
-    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
-      SccCertificate.outLit.secs = true)
+theorem hello1_finalCAG (hpa : Scc.Cert.Link.A64.parsesTo asmG outF.prog outF.secs = true)
     {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
-    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 LeA P1A) B
-      SccCertificate.asm
+    Scc.Sem.A64.CorrectE 1
+      (SrcSem.source (SrcSem.srcP1o arch Spike.Test.Hello1MainSrc.hello1o) Spike.Test.Hello1MainSrc.hello1o)
+      (Spike.Lib.LowerA64.lay2 ΛG Spike.Test.Hello1MainSrc.hello1o) B asmG := by
+  have h0 : A64.placeOKAt placeCfg ΛG (Scc.Cert.PlaceOK.A64.Out.ofEmitted
+      (Scc.Lower.A64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)) = true
```

`hello1_finalCF` (`Spike/Test/X64Hello1FinalCF.lean`):

```lean
theorem hello1_finalCF
    (hpaF : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oF.prog oF.secs = true)
    {Bu : Scc.Sem.Budget} (hB : Bu.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 ΛF P1) Bu
      ⟨textF, sizesFLit, offsFLit⟩
```

Against `hello1_finalC` (`Spike/Test/X64Hello1FinalC.lean`, the previous release):

```diff
--- previous hello1_finalC
+++ this release hello1_finalCF
@@ -1,6 +1,5 @@
-theorem hello1_finalC
-    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
-      SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
-    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
-    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Le P1) B
-      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
+theorem hello1_finalCF
+    (hpaF : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oF.prog oF.secs = true)
+    {Bu : Scc.Sem.Budget} (hB : Bu.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
+    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 ΛF P1) Bu
+      ⟨textF, sizesFLit, offsFLit⟩
```

`ret0_linked_correctG` (`Spike/Test/Ret0LinkedA64G.lean`):

```lean
theorem ret0_linked_correctG (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.A64.parsesTo asmG (withTail out tailG).prog (withTail out tailG).secs = true) :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
      { ΛG with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseA64.main } B
      asmG
```

Against `ret0_linked_correct` (`Spike/Test/Ret0LinkedA64.lean`, the previous release):

```diff
--- previous ret0_linked_correct
+++ this release ret0_linked_correctG
@@ -1,5 +1,5 @@
-theorem ret0_linked_correct (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
-    (hpa : Scc.Cert.Link.A64.parsesTo asm out.prog out.secs = true) :
+theorem ret0_linked_correctG (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
+    (hpa : Scc.Cert.Link.A64.parsesTo asmG (withTail out tailG).prog (withTail out tailG).secs = true) :
     Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
-      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseA64.main } B
-      asm
+      { ΛG with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseA64.main } B
+      asmG
```

`ret0_linked_correctG` (`Spike/Test/Ret0LinkedX64G.lean`):

```lean
theorem ret0_linked_correctG (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oFLit.prog oFLit.secs = true) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) prog_src)
      { ΛF with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main }
      B ⟨textF, sizesFLit, offsFLit⟩
```

Against `ret0_linked_correct` (`Spike/Test/Ret0LinkedX64.lean`, the previous release):

```diff
--- previous ret0_linked_correct
+++ this release ret0_linked_correctG
@@ -1,5 +1,5 @@
-theorem ret0_linked_correct (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
-    (hpa : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs = true) :
-    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
-      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main } B
-      ⟨asm, sizes, labelOffs⟩
+theorem ret0_linked_correctG (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
+    (hpa : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oFLit.prog oFLit.secs = true) :
+    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) prog_src)
+      { ΛF with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main }
+      B ⟨textF, sizesFLit, offsFLit⟩
```

`lld_linked_correctG` (`Spike/Test/Ret0LldX64G.lean`):

```lean
theorem lld_linked_correctG (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oFLit.prog oFLit.secs = true) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) prog_src)
      { ΛF with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main }
      B ⟨textF, sizesFLit, offsFLit⟩
```

Against `lld_linked_correct` (`Spike/Test/Ret0LldX64.lean`, the previous release):

```diff
--- previous lld_linked_correct
+++ this release lld_linked_correctG
@@ -1,5 +1,5 @@
-theorem lld_linked_correct (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
-    (hpa : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs = true) :
-    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
-      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main } B
-      ⟨asm, sizes, labelOffs⟩
+theorem lld_linked_correctG (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
+    (hpa : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oFLit.prog oFLit.secs = true) :
+    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) prog_src)
+      { ΛF with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main }
+      B ⟨textF, sizesFLit, offsFLit⟩
```

`ret0_correctG` (`Spike/Test/X64Ret0GOut.lean`):

```lean
theorem ret0_correctG (Λ : Scc.Sem.Layout) (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (h : placeOKAt SccCertificate.placeCfg Λ oFLit = true)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oFLit.prog oFLit.secs = true) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main }
      B ⟨textF, sizesFLit, offsFLit⟩ := by
  have hF : placeOKAt SccCertificate.placeCfg Λ oF = true := oF_eq ▸ h
  have hpF : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oF.prog oF.secs = true := oF_eq ▸ hpa
  exact Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt_final (cfg := SccCertificate.configW)
    (d := Spike.Test.Ret0ReleaseX64.main) (sizes := sizesFLit) (labelOffs := offsFLit)
    (pcfg := SccCertificate.placeCfg) Λ SccCertificate.prog_accepted SccCertificate.lowered_eq
    SccCertificate.emitted_eq SccCertificate.tables_eq hcF hzF hbF hF hpF

end Spike.Test.X64Ret0GOut

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.X64Ret0GOut.oF_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.X64Ret0GOut.oF_eq

/-- info: 'Spike.Test.X64Ret0GOut.hcF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.X64Ret0GOut.hcF

/-- info: 'Spike.Test.X64Ret0GOut.ret0_correctG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.X64Ret0GOut.ret0_correctG
```

### Axioms

`#print axioms`, each checked by a `#guard_msgs`, gives `[propext,
Classical.choice, Quot.sound]` for:

- `wake_linkedU` (`WakeLinkedA64Root.lean`), `wake_linked`
  (`WakeLinkedA64.lean`), `wake_finalCA_genW`/`wake_finalCA_genWP`
  (`Spike/Lib/WakeFinalCAW.lean`), and `certify.sh`'s generated
  `prog_correct_linked` for `wake.w`;
- `wake_linkedX` (`WakeLinkedX64Root.lean`), `wake_linkedXL`
  (`WakeLinkedX64RootL.lean`), `wake_placeOK2At`
  (`WakeLinkedX64.lean`), `wakeS_eq` (`WakeLinkedX64Br.lean`; `wakeSrc_eq`
  depends on no axioms), and `certify.sh`'s generated `prog_correct_linked`
  for `wake.w` on x86-64;
- `hello_linkedA` and `layoutE_e` (`HelloLinkedA64Root.lean`), and the layout
  facts `placeW_e`, `hpin2`, `hinit2`, `linux_ok_e` and `hA13_e`
  (`HelloLinkedA64.lean`), where `hnz` depends on `propext` only and `hlo` on
  no axiom;
- `hello_linkedX` and `hello_linkedX_linux` (`HelloLinkedX64Root.lean`),
  `layoutEX_e` and `linux_ok_e` (`HelloLinkedX64Le.lean`),
  `RootFinal.hello_correct` and `hello_root_final`
  (`Spike/Lib/X64HelloRootFinal.lean`), `RootLit.hello_root_lit`,
  `hello_root_litM` and `hc_H` (`Spike/Lib/X64HelloRootLit.lean`, where
  `hz_H` depends on `propext` only) and `RootInv.hello_root_inv`
  (`Spike/Lib/X64HelloRootInv.lean`), and `certify.sh`'s generated
  instantiation of `hello_linkedA`/`hello_linkedX` for `hello.w`;
- `hello1_finalCA` and `hello1_finalCA_of` (`A64Hello1FinalCA.lean`);
  `hello1_finalC` and `hello1_finalC_of` (`X64Hello1FinalC.lean`);
  `hello1_e2eOk` (`Hello1LinkedX64.lean`); `hello1_of_closed2A`,
  `hello1_of_closed2`; `a64_scc_correctE_text_closedAt2`,
  `x64_scc_correctE_text_closedAt2`;
- `ret0_correct`, `ret0_correct_tables`, `ok_witness_of_placeOKAt` (both
  ISAs); `ret0_linked_correct` (both ISAs); `ret0_linked_witness` (AArch64);
  `lld_linked_correct`;
- the generic `a64_scc_correctE_closedAt`/`_text_closedAt`,
  `x64_scc_correctE_closedAt`/`_text_closedAt`, and their `…closedAt1`
  forms (`Spike/Test/Lower{A64,X64}Correct{,1}.lean`).

The placement and `codeEnd` theorems at each `Λe` are on the final theorems'
chains, so those guards cover them.

**Why the conclusion's layout overrides `static` and `imms`.** The placement
check reads neither field (`placeOKAt_static`); `imms` is the proof's table of
constants folded into instructions, not an input of the loader nor of
anything `Correct` fixes outside the witness.
`Spike/Test/A64StaticImmsOverride.lean` and
`Spike/Test/X64StaticImmsOverride.lean` check, for arbitrary values of the
two fields (so for `ret0`'s `immsOf` and `hello1`'s `lay2` alike), that the
loader, label resolution, the marks, `InLayout`, `Entry.Ok`, well-formedness
and the placement check agree at `Λ` and at the overridden layout.

**Non-vacuity.** For `ret0`, the entry quantifier is inhabited at every
layout passing the check (`ok_witness_of_placeOKAt`, `ret0_linked_witness`,
`lld_linked_witness`), and the source reaches `[exit 42]`
(`src_reach_exit42`, `Spike/Test/A64ClosedChecks.lean`). For `hello1`, the
source emits `Hello, world\n` and then `exit 0` from the setup block's
return (`hello1_main_src`, `Spike/Test/Hello1MainSrc.lean`). No theorem in
the tree instantiates the entry quantifier at `lay2 Λe hello1o`; the generic
`Entry.ok_witness` (`Scc/Sem/CorrectE.lean`) gives a witness for any layout
whose regions end at or below `2 ^ 32`. Perturbed layouts fail closed: for
`hello1` on x86-64, the code region one byte short or the code base one byte
off fails `placeOKAt`, and one byte long fails the end-to-end guard
(`Hello1LinkedX64`); the `ret0` files test similar perturbations.

## 2. What ties the theorem to the linked binary

The theorem is not applied at an assumed static link: the placement check is
decided at the layout of the binary actually linked.

1. `hello1.s` next to each `hello1` fixture is `SccCertificate.asm` verbatim
   (`#eval` guard in `Hello1LinkedA64`, `Hello1LinkedX64`); the
   certificate's reproducibility guard (`#guard Scc.Cert.Arm.reproduces` /
   `Scc.Cert.X64.reproduces config source asm`) ties `asm` to scc's output
   on `hello1.w`, and `Spike/Gen/drift.sh` ties the certificate to the
   current scc. Likewise `ret0.s` for the three `ret0` fixtures.
2. The links (no linker script in any), as recorded in `Scc/Test/elf.sh`:
   - `hello1`, AArch64 (`run.sh`'s command; `ld.lld`'s default script puts
     `.rodata` (the stack map `scc_stackmap` and the GC tables) below
     `.text` and adds a build-id note):

     ```
     clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld \
       -o hello1a64/hello1 hello1a64/hello1.s
     ```
   - `hello1`, x86-64 (`run.sh`'s command):

     ```
     as -o hello1.o hello1x64/hello1.s && ld -static -o hello1x64/hello1 hello1.o
     ```
   - `ret0`: AArch64 as `hello1`; x86-64 GNU `as` + `ld -static`, and GNU
     `as` + `ld.lld -static`.

   `elf.sh --relink-check` reproduces the checked-in fixtures byte for byte
   with GNU Binutils 2.47 (`as`, `ld`) and Debian clang/LLD 21.1.8.
   `Scc/Test/elf.sh --relink` rebuilds the fixtures with these commands;
   `elf.sh --relink-check` relinks every fixture and compares byte for byte.
   The `hello1` executables print `Hello, world` and exit 0 (x86-64
   natively, AArch64 under `qemu-aarch64`).
3. The ELF reader reads `Λe` off the file (`scc_elf_layout%`, fail closed)
   and accepts it (`#eval` verdict guard); a `#guard elf.2 == …` pins the
   file's SHA-256: `hello1` AArch64 `fba4fbc8…`, `hello1` x86-64
   `98182ede…`; `ret0` AArch64 `d0cb524c…`, x86-64 GNU `ld` `79c52e1a…`,
   x86-64 `ld.lld` `482d4f0f…`. Guarded about the `hello1` layouts:
   - x86-64: `Λe.code.lo == 0x401000`, `.rodata` at or above the code's end,
     and every `.rodata` symbol at or above the code's start;
   - AArch64: `.rodata` ends at or below the code's start, the code's start
     is 16-aligned, and the symbols below the code are exactly `.rodata`'s
     labels, the stack map `scc_stackmap` at `.rodata`'s start and then the
     GC tables `scc_gc_maps`, `scc_gc_succs`, `scc_gc_rseq` and
     `scc_gc_desc` at their offsets. (The module doc gives `.text` at
     `0x213080`; that address is not guarded.) The same module checks, at
     the static link with `.rodata` moved below the code (`Λlo`, `.rodata`
     of `0x3000` bytes), that A2 accepts the output.
4. The kernel decides `placeOKAt placeCfg Λe out` component by component
   (`decide +kernel` per component, A1–A9, A11 and A12, combined by
   `placeOKAt_of`), including A1's `codeFits` and A2's loader check
   (`Link.A64.loadOk`, `Link.X64.loadOk`: the abort labels, data symbols
   around the code, `noClash`, the code's end below `2 ^ 64`), and the
   code fills `.text` exactly (`hello1_codeFills`, `hello1_codeEnd`).
5. `hello1_finalCA` / `hello1_finalC` at `Λe` (their chains use
   `hello1_placeOKAt`); `ret0_correct` at each `ret0` `Λe`.

For `ret0` (and any `Accepted0`/`Accepted1` program), `Scc/Test/certify.sh
[--arch arm] --instantiate PROG.w` performs steps 1–5 on a fresh build and
`run.sh` link and prints **certified** (§4). For `hello1.w` it does the
same with `hello1_finalCA_gen` / `hello1_finalC_gen` in place of the
fragment theorem, after checking that the fresh text is the checked-in
certificate's `asm` byte for byte (by evaluation, on every run); the
certificate and program it imports are the checked-in ones, never the run's.

What this chain still trusts is in §3.

### `wake` at its executables

**AArch64.**

1. `Scc/Test/elf/wakea64/wake.s` is the `wake` certificate's
   `SccCertificate.asm` verbatim (`#eval` guard in
   `Spike/Test/WakeLinkedA64Elf.lean`); the certificate's
   reproducibility guard ties `asm` to scc's output on `wake.w`.
2. The link, as recorded in `Scc/Test/elf.sh` (`run.sh`'s AArch64 command,
   `ld.lld`'s default script):

   ```
   clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld \
     -o wakea64/wake wakea64/wake.s
   ```

   `elf.sh --relink-check` reproduces it byte for byte with the toolchain
   above. The executable runs under `qemu-aarch64`, prints nothing and
   exits 0.
3. The ELF reader reads `Λe` off the file (`scc_elf_layout%`, fail closed);
   a guard pins its SHA-256, `7843e1f7…` (`WakeLinkedA64Elf`).
4. The kernel decides the placement facts the proof uses at `Λe`, one
   `decide +kernel` per component (`PlaceW`: A1, A2, A4, A6, A8 in
   `WakeLinkedA64A1` … `A8`; the thread counter, the pinned region and the
   second stack in `WakeLinkedA64`, `WakeLinkedA64Ctr`).
5. Checked on every `certify.sh` run: the program, `T.s` (`== asm`) and the
   executable byte for byte against the checked-in files (by the script),
   and, by evaluation, `Scc.Cert.SrcTerm.reads` of the run's `wake.w` as
   `wakeSrc` and `hpa`. The layout read from the executable is `Λe` by
   kernel `rfl` (`prog_layout : elf.1 = Spike.Test.WakeLinkedA64.Λe`).

**x86-64.**

1. `Scc/Test/elf/wakex64/wake.s` is the x86-64 `wake` certificate's
   `SccCertificate.asm` verbatim (`#eval` guard in
   `Spike/Test/WakeLinkedX64Elf.lean`); the certificate's reproducibility
   guard ties `asm` to scc's output on `wake.w`.
2. The link, as recorded in `Scc/Test/elf.sh` (`run.sh`'s x86-64 command,
   GNU `ld`'s default script):

   ```
   as -o wake.o wakex64/wake.s && ld -static -o wakex64/wake wake.o
   ```

   `elf.sh --relink-check` reproduces it byte for byte with the toolchain
   above. The executable runs, prints nothing and exits 0.
3. The ELF reader reads `Λe` off the file (`scc_elf_layout%`, fail closed);
   a guard pins its SHA-256, `672d383f…` (`WakeLinkedX64Elf`). `.text` is at
   `0x401000` (`#guard`).
4. The kernel decides the placement facts at `Λe`, one `decide +kernel` per
   component: **all** of `placeOK2`'s components, A1–A9, A11′, A12′ (code
   and phases) and A13 (`WakeLinkedX64A1` … `WakeLinkedX64A13`), combined
   into `placeOK2At` (`WakeLinkedX64.wake_placeOK2At`); that the code fills
   `.text` exactly (`WakeLinkedX64Fill`); and the thread counter, the pinned
   region, the second TCB's limit word and the child's stack
   (`WakeLinkedX64Le`). Unlike AArch64, every component is decided.
5. Checked on every `certify.sh` run: the program, `T.s` (`== asm`) and the
   executable byte for byte against the checked-in files (by the script),
   and, by evaluation, `Scc.Cert.SrcTerm.reads` of the run's `wake.w` as
   `prog_src` and `hpa`. The layout read from the executable is `Λe` by
   kernel `rfl` (`prog_layout : elf.1 = Spike.Test.WakeLinkedX64.Λe`).

### `hello` at its executable (AArch64)

1. `Scc/Test/elf/helloa64/hello.s` is the listing `SccCode.helloAsm`
   verbatim (`#eval` guard in `Spike/Test/HelloLinkedA64Elf.lean`).
   `Spike/Gen/regen_a64.sh hello A64Hello --check` (run by
   `Spike/Gen/drift.sh`) ties the listing to scc's output on
   `Spike/Gen/hello.w`, a checked copy of `Scc/Test/hello.w`.
2. The link, as recorded in `Scc/Test/elf.sh`: `run.sh`'s AArch64 command
   with the build-id note, `.rodata` and `.text` placed by
   `Scc/Test/a64link.sh` (`.text` at hello's phase base `0x210550`, the note
   and `.rodata` at `ld.lld`'s default addresses, below `.text`):

   ```
   clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld \
     -Wl,--section-start=.note.gnu.build-id=0x200190,--section-start=.rodata=0x2001b8,--section-start=.text=0x210550 \
     -o helloa64/hello helloa64/hello.s
   ```

   `elf.sh --relink-check` reproduces it byte for byte with the toolchain
   above. Under `qemu-aarch64` the executable prints `Hello, world` and
   exits 0.
3. The ELF reader reads `Λe` off the file (`scc_elf_layout%`, fail closed);
   a guard pins its SHA-256, `c9f1ff20…` (`HelloLinkedA64Elf`). Guarded:
   `.text` at `0x210550`, `.rodata` ending at or below it.
4. The kernel decides the layout facts at `Λe` (`HelloLinkedA64`): `PlaceW`
   from A1, A2, A4, A6, A8 (`HelloLinkedA64A1` … `A8`, one `decide +kernel`
   per component), `hlo`, `hstat`, `hnz`, and, at the placed layout `Le`,
   `hpin2`, `hinit2` and `hA13_e`. `layoutE_e : LayoutE Λe` collects
   `placeW_e`, `hlo`, `hstat`, `hnz`, `hA13_e` and `hinit2`. That the Linux
   entry is admissible at `Le.Λ` is decided too (`linux_ok_e`), so the entry
   quantifier is not vacuous there.
5. `certify.sh --arch arm --instantiate Scc/Test/hello.w` performs steps
   1–4 for a fresh build at `run.sh`'s pinned link only when its text is
   `helloa64/hello.s` and its executable `helloa64/hello`, byte for byte,
   and then instantiates `hello_linkedA` (§4); a build at `ld.lld`'s default
   layout, or of a changed `hello.w`, is not certifiable (verdict 3).

### `hello` at its executable (x86-64)

1. `Scc/Test/elf/hellox64/hello.s` is the listing `SccCode.helloText`
   verbatim (`#eval` guard in `Spike/Test/HelloLinkedX64Elf.lean`). That
   scc's lowering of `helloSrc` produces the listing's cells and sections is
   checked by evaluation (`#guard` in `Spike/Lib/X64HelloOut.lean`,
   documentation only: no proof reads it). `Spike/Gen/drift.sh` does not
   cover the x86-64 `hello` listing.
2. The link, as recorded in `Scc/Test/elf.sh`: `run.sh`'s x86-64 command
   with GNU `ld`'s default script. No section is placed: `ld`'s default
   `.text` is `0x401000`, which is hello's phase base:

   ```
   as -o hello.o hellox64/hello.s && ld -static -o hellox64/hello hello.o
   ```

   `elf.sh --relink-check` reproduces it byte for byte with the toolchain
   above. The executable prints `Hello, world` and exits 0.
3. The ELF reader reads `Λe` off the file (`scc_elf_layout%`, fail closed);
   a guard pins its SHA-256, `8fb245f0…` (`HelloLinkedX64Elf`). Guarded:
   `.text` at `0x401000`, 16-aligned, `.rodata` above the code.
4. The kernel decides the layout facts at `Λe` (`HelloLinkedX64Le`):
   `placeOK2At` from its components (`HelloLinkedX64A1` … `A13`, one
   `decide +kernel` per module; A12's code part is layout-independent),
   `hlo`, `hstat`, `hnz`, and, at the placed layout `Le`, `hA13_e`,
   `hpin2_e`, `hinit2_e` and `hsub1_e`. `layoutEX_e : LayoutEX Λe` collects
   them. That the Linux entry is admissible at `Le.Λ` is decided too
   (`linux_ok_e`), so the entry quantifier is not vacuous there.
5. `certify.sh --arch x64 --instantiate Scc/Test/hello.w` performs steps 1–4
   for a fresh build only when its text is `hellox64/hello.s` and its
   executable `hellox64/hello`, byte for byte, and then instantiates
   `hello_linkedX` (§4); any other build is not certifiable (verdict 3).

### Other programs at linked layouts

- **`frame0.w`** (`Spike/Gen/frame0.w`, `ret 42` with a zero-byte frame),
  x86-64, GNU `ld` (`Spike/Test/Frame0LinkedX64.lean`): the code fills
  `.text` and `placeOKAt` holds at the executable's layout, each component by
  `decide +kernel`. The file states no correctness theorem; `certify.sh
  --instantiate` certifies it at its `run.sh` link on both ISAs (§4).

## 3. Trusted base

The Lean kernel and its standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); Kraken's ISA semantics and memory models; the kernel model of
the system calls; `Correct` and the WeakCore source semantics as the
specification. In addition:

1. **The ELF layout reader** (`Scc/Cert/Elf.lean`). Its refusal names the
   failing conjunct of `wfB` (`Link.wfBWhy`, diagnostics only; `wfB` and
   `wfB_sound` are unchanged by this). Evaluated by the
   elaborator (`scc_elf_layout%`), not replayed by the kernel: a `#guard`'s
   trust. It reads the System V gABI header, program, section and symbol
   tables of an ELF64 LE `ET_EXEC` file (`EM_AARCH64` or `EM_X86_64`) and
   fails closed. It checks itself: `.text` in an `R+X` (not `W`) `PT_LOAD`
   and mapped from its file bytes; `.rodata` in an `R`-only `PT_LOAD`, mapped
   from its file bytes, 8-aligned, and disjoint from the code, `.data`, the
   heap, the pinned region and the pool; one `R+W` (not `X`) writable
   `PT_LOAD` whose file part is exactly `.data` (giving `Λ.image`), with
   `.bss` and the regions in its zero tail; each region non-empty; the
   regions pairwise disjoint (explicit check, and `Link.wfB`, which also
   checks their 16-alignment, the code's included, and that every data
   symbol lies in a data region); no unknown mapped section (but the
   build-id note, item 2), dynamic or relocation section, executable stack
   or overlapping `PT_LOAD`; no data symbol in the code; **`e_entry` is the
   start of `.text`**. It does not check that `.text` is non-empty.
   Trusted: that Linux maps exactly the `PT_LOAD`s with their `p_flags`,
   zero-filling `[p_filesz, p_memsz)`, and starts the thread at `e_entry`;
   the emitter's region symbols `scc_rt_heap`/`scc_rt_pinned`/`scc_rt_stacks`
   (`OBJECT`, sized, last in `.bss`) mark the regions. Not checked by the
   reader: that `.text`'s bytes are the certified program (items 6 and 7).
2. **The linker's build-id note** (`ld.lld`'s default on AArch64) is
   accepted only as a read-only `SHT_NOTE` section in an `R`-only `PT_LOAD`,
   disjoint from the code, the data and the regions, with no symbol in or at
   it (`buildIdNote`; negative tests in `Scc/Test/ElfTest.lean`). Trusted:
   that Linux maps it as its `PT_LOAD` says and nothing reads it.
3. **Linux stack facts** (the entry quantifier, `Entry.Ok`). `Entry.Ok E Λ`
   requires `E.clear Λ` (`Scc/Sem/Target.lean`): the stack lies inside
   `2 ^ 64` and is disjoint from `Λ.rodata` and every range of `Λ.regions =
   [code, data, heap, stackPool, pinned]`; plus `sp` 16-aligned, `sp < 2 ^
   63` and at least 64 KiB of stack. The trusted Linux fact only needs to
   imply it: Linux starts a static executable with `sp` 16-aligned and below
   `2 ^ 63`, with at least 64 KiB of mapped zero bytes below `sp` in the main
   thread's private memory, disjoint from the code, `.rodata` and the data
   regions, and every other register zero (`threadAt`; `Scc/DESIGN.md` §4).
   The model does not include argc/argv/envp/auxv (scc never reads them).
4. **Data symbols below the code.** The reader does not refuse a data symbol
   below the code (`refuseBelowCode := false`); one inside the code is
   refused, and a `.data`/`.bss` symbol below the code is refused by `wfB`.
   Trusted: that Linux's loader puts those symbols where the target's
   `placeBelow` does. Proved, not trusted: A2's `symsAround` and `noClash`.
   **Exercised** by `.rodata`'s labels (`scc_stackmap` and the GC tables'
   labels) below the code in the AArch64 fixtures (`ret0`, `call1`,
   `hello1`) and in the x86-64 `ld.lld` fixture.
5. **Evaluated, not kernel-checked, on the chain to each fixture** (each a
   `#guard`/`#eval` or elaboration-time evaluation; their trust is that of
   Lean's compiled evaluator):
   - `hpa` (the parsers are `partial`); the theorems keep it as an explicit
     premise;
   - `#guard Scc.Cert.Arm.reproduces config source asm` /
     `Scc.Cert.X64.reproduces config source asm` and `#guard
     Scc.Cert.SrcTerm.reads source prog_src`, in the certificate;
   - for `hello1`, the `#guard`s that `hello1o`'s `rodata` and `main` are the
     frontend's reading of `hello1.w` (`Hello1MainSrc`, `Hello1Src`) and that
     `printLD`/`printD` are the parsed `print` model (`PrintSrc`);
   - `scc_elf_layout%` (item 1);
   - `#guard elf.2 == …`, the pinned SHA-256 of the fixture;
   - the `#eval` guard `hello1.s == asm` (resp. `ret0.s`).
6. **The artefact and its encoding.**
   - The binary that runs is the fixture file whose SHA-256 is pinned; no
     check ties a deployed binary to it beyond `elf.sh --relink`/
     `--relink-check` and that digest.
   - The assembler encodes each instruction of `asm` as the instruction
     Kraken's parser and ISA semantics read: on AArch64 `clang`'s integrated
     assembler, 4 bytes each; on x86-64 GNU `as`, at the size listed in
     `sizes`. `sizes` and `labelOffs` are checked only for consistency
     (`sizes_ok`). `.text`'s bytes are never decoded or compared with
     `out.prog`; the reader checks only `.text`'s extent.
   - Alignment directives in AArch64 `.text` are dropped by Kraken's parser
     (`stripDirectives`); the trust includes that they pad nothing inside
     `.text` (true for 4-byte instructions with `.p2align ≤ 2`, and for the
     `.p2align 4` at offset 0, item 7).
7. **AArch64 `.text` alignment** (scc-side, untrusted). `wfB` requires every
   region, the code included, to be 16-aligned. The emitter opens `.text`
   with `.p2align 4`, so `ld.lld` aligns the code whatever precedes it.
   Regression test `Scc/Test/textalign.sh`, with `hello1` and `tailwide`
   pinned as programs whose `.rodata` ends 8 mod 16.
8. **The target model's entry**: `target (kernel 1) E` for each admissible
   `E`, not only `Entry.linux`.
9. **The output path (`hello1`).** The kernel model's `write`
   (`Scc/Sem/Kernel.lean`, `sysStep`): while fewer than `n` bytes are out,
   each step transfers the next byte, emitting `out b` for fd 1; after at
   least one byte the call may return the count; before any, it may return
   `-EINTR` or `-EAGAIN`, or a refusal with `writeErr`. The trust is that
   Linux's `write` on fd 1 behaves within this model. On the source side,
   `print`'s meaning is its WeakCore model `printL`/`print`
   (`Spike/Lib/PrintSrc.lean`), part of the specification: `hello1.w`
   declares `print` with an empty body, and the theorem is about `hello1o`,
   the program with that model linked in. `hello.w` writes `printL`/`print`
   in its own text as the extern's WeakCore model on a published slice
   (`printExtPubD`/`printLoopPubD`, `Scc/PrintModel.lean`), so `helloS`'s
   `print` is the frontend's reading of that text; scc does not compile
   those bodies, and the call runs the runtime's `scc_rt_print`. The same
   kernel `write` model applies to `hello`'s worker thread.
10. **The allocator and the budget (`hello1`).** The allocator is runtime
    code in `hello1`'s text, checked by the placement check (A7 checks its
    arena constant) and covered by the proof, not trusted. What the
    statement fixes is the budget: `hB` ties `B.cells` to `allocCells`
    (4194304 cells of 16 bytes), so the guarantee is for runs whose source
    heap stays within that arena.

11. **`placeOK2` (`wake.w`).** A program that takes its thread id or spawns
    is checked by `placeOK2` (`Scc/Cert/SpawnA64.lean`,
    `Scc/Cert/SpawnX64.lean`) instead of `placeOK`: **A11′** (`scc_rt_main`
    passing the TCB to `main`), **A12′** (the stack need admitting the spawn
    path's runtime routines, and phase changes at reentrant runtime calls
    that keep the stack lock's bit) and **A13** (the thread counter, the
    second stack in the pool, the second TCB's words, and the code and
    phase facts of `scc_rt_thread_reserve`, `scc_rt_park` and
    `scc_rt_unpark`), the other checks as for `hello1`. They are part of the
    certificate's statement; for `wake` the AArch64 proof uses the
    components it needs, the x86-64 proof all of them, each decided at `Λe`
    (§2). `hello`'s AArch64 proof uses `PlaceW` (A1, A2, A4, A6, A8), A13's
    data part and the second TCB's limit word, its x86-64 proof all of the
    components, each decided at `Λe` (§2).
12. **`certify.sh`'s registry entries for `wake` and `hello`.** The script
    recognises `wake.w` and `hello.w` by comparing the program, `T.s` and the
    executable with the checked-in files (`Scc/Test/elf/wakea64/`,
    `Scc/Test/elf/helloa64/` on AArch64, `Scc/Test/elf/wakex64/`,
    `Scc/Test/elf/hellox64/` on x86-64) byte for byte, and only then
    instantiates `wake_linkedU`, `hello_linkedA` (AArch64) or `wake_linkedX`,
    `hello_linkedX` (x86-64); any other spawning program is not certifiable
    (verdict 3 with `--instantiate`).
13. **The thread and synchronisation calls (`wake`).** The kernel model's
    `clone` (one flag set, a fresh stack and TLS, the child's start state),
    `futex` wait/wake (`FUTEX_WAIT_PRIVATE`/`FUTEX_WAKE_PRIVATE`, used by
    `park`/`unpark`), `exit` and `exit_group` (`Scc/Sem/Kernel.lean`), as
    used by wake's and hello's runtime; on x86-64 also `arch_prctl(ARCH_SET_FS)`, which
    sets the `%fs` base the runtime reads its TCB through (system-call
    numbers 56, 202, 60, 231 and 158). The trust is that Linux's calls
    behave within this model.
14. **`wake`'s source semantics.** `wakeS` (AArch64) uses the source
    parameters `srcPo`/`progInitT` of `Spike/Lib/WakeA64.lean`:
    `Scc/Sem/SrcOut.lean`'s start with `main` entered on its own `ThreadId`
    and two thread slots. `wakeSX` (x86-64) uses `Scc.Sem.SrcSem.srcPo`
    itself, at the certificate's `prog_src`. `helloS` uses the same
    AArch64 source machine, `WakeA64.srcS`, at `helloSrc`, and `helloSX`
    (x86-64) the x86-64 one, `X64WakeA64.srcS`, at the same `helloSrc`. They
    are part of the specification.
15. **WeakCore's machine and language layer.** The bodies of `TermRun.tstep`
    (with `new`), `CoreTerm.scan`, `CoreTerm.annNew`, `CoreTerm.progTgts`,
    `CoreTerm.scopeAllocOK`, `TermRun.tysOf`, and, new in release 7,
    `CoreTerm.keyFreeTE`, `CoreTerm.keyFreeT`, `CoreTerm.handOff` and
    `CoreTerm.handOffR` are part of the source semantics and are not covered
    by WeakCore's premise guard (see "WeakCore release 7 (47e9c32c)"). This
    is the definition text of WeakCore 47e9c32c as vendored.
16. **The AArch64 link of `wake` and `hello`** (`Scc/Test/a64link.sh`,
    sourced by `run.sh`, `certify.sh` and `elf.sh`). Their proofs are stated
    with `.text` at `0x210550`, so their executables are linked with the
    build-id note, `.rodata` and `.text` placed at fixed addresses (the
    note's and `.rodata`'s are `ld.lld`'s defaults); with the three
    placements `ld.lld` writes its default script's segments. A `.rodata` larger than
    about 66 KiB makes the placed link fail. Other programs are linked at
    `ld.lld`'s default. x86-64 needs no placement: GNU `ld` puts `.text` at
    `0x401000` whatever the size of `.rodata`.
17. **x86-64 executables are linked with GNU `ld`.** The x86-64 emitter does
    not 16-align `.text`; with `ld.lld`'s default layout the code base comes
    out unaligned and the reader refuses it (`wfB`).

The trusted files' documentation states the above: `Scc/Sem/CorrectE.lean`
(the trusted Linux stack fact, separate from the proved witness),
`Scc/Sem/Correct.lean` (`Layout.WF`), `Scc/Sem/Kernel.lean` (the system
calls) and `Scc/DESIGN.md` §4 (the loader, the ELF reader, the `Entry.Ok`
quantifier) and its notes on AArch64 alignment.

18. **The byte check of a `--granule` executable** (`Scc/Cert/ElfBytes.lean`,
    `Scc/Cert/ElfBytes{X64,A64}.lean`). The descriptor words in the last 8
    bytes of every granule, and the whole `.rodata`, are compared with the
    text by an `#eval` in `T.post.lean` that throws on a mismatch: evaluated
    by the compiled code, not kernel-checked. The loader's cell of a
    descriptor word is empty, so the theorem says nothing about those bytes;
    this check is the only link between them and the text.
19. **The granule pass check and its tables** (`Scc/Cert/Granule*.lean`,
    `Scc/Cert/MapsFast.lean`). `Scc.Cert.Granule.{X64,A64}.check`,
    `blocksOfFinal`, `textCells` and `ofFinal` appear in the `_final`
    statements' premises, and the MapsFast equalities are proved for all
    inputs; the trusted files that changed are listed by
    `tools/trusted_check.sh` (against the previous release, 5e8882c5: 20
    added, 0 removed, 57 changed).

## 4. Reproducing

**Building.** `lake build Kraken KrakenAArch64 WeakCore Scc Spike scc`
(6227 jobs), then `lake build scc_x64 scc_arm` and the test modules.

**Memory.** Build with `LEAN_NUM_THREADS=1`: Lake may run several `lean`
processes at once, each single-threaded, and the figures below are per
process. `tools/memory_caps.tsv` lists the measured peak anonymous memory and
cap of every module above 2.5 GiB; `tools/quick_gate.sh` builds its `solo`
and `cert` rows alone before the main build. Build each module below alone
once its imports are built, e.g. `LEAN_NUM_THREADS=1 lake build
WeakCore.TermStep`, with about 20 GB of memory free and nothing else
heavy running. No module outside the tables below needs more than
3.5 GiB of anonymous memory.

WeakCore release 7 (peak anonymous memory / peak resident size):

| Module | Anonymous | Resident |
|---|---|---|
| `WeakCore.TermStep` | 6.3 GiB | 7.9 GiB |
| `WeakCore.GenLayer` | 4.9 GiB | 6.7 GiB |
| `WeakCore.TermScopeFHM` | 4.1 GiB | 6.2 GiB |
| `WeakCore.TermPlant` | 3.0 GiB | 4.7 GiB |

Certificate modules (each built alone with `LEAN_NUM_THREADS=1` once its
imports are built), the 12 regenerated certificates and the granule
certificates and packages:

| Certificate module | Peak anonymous memory | Time |
|---|---|---|
| `Spike.Test.Cert.A64Chain5Cert` | 5.4 GiB (5519 MB) | 627 s |
| `Spike.Test.Cert.A64HelloCert` | 4.6 GiB (4720 MB) | 509 s |
| `Spike.Test.Cert.A64WakeCert` | 4.0 GiB (4115 MB) | 499 s |
| `Spike.Test.Cert.X64HelloCert` | 3.9 GiB (4040 MB) | 407 s |
| `Spike.Test.Cert.X64WakeCert` | 3.5 GiB (3547 MB) | 356 s |
| `Spike.Test.Cert.A64Hello1Cert` | 2.9 GiB (2951 MB) | 383 s |
| `Spike.Test.Cert.A64Call1Cert` | 2.6 GiB (2656 MB) | 376 s |
| `Spike.Test.Cert.X64Hello1Cert` | 2.5 GiB (2549 MB) | 367 s |
| `Spike.Test.Cert.A64Ret0Cert` | 2.3 GiB (2363 MB) | 350 s |
| `Spike.Test.Cert.X64Call1Cert` | 2.2 GiB (2301 MB) | 291 s |
| `Spike.Test.Cert.X64Ret0Cert` | 2.1 GiB (2101 MB) | 267 s |
| `Spike.Test.Cert.X64Frame0Cert` | 2.0 GiB (2083 MB) | 269 s |
| `Spike.Test.Call1LinkedA64G` | 2.2 GiB (2270 MB) | 44 s |
| `Spike.Test.Hello1LinkedA64G` | 1.7 GiB (1766 MB) | 94 s |
| `Spike.Test.Ret0LinkedA64GC` | 1.7 GiB (1701 MB) | 44 s |
| `Spike.Test.Hello1LinkedX64GPost` | 1.6 GiB (1602 MB) | 39 s |
| `Spike.Test.Hello1LinkedX64G` | 1.6 GiB (1596 MB) | 37 s |
| `Spike.Test.Ret0LinkedX64G` | 1.6 GiB (1595 MB) | 47 s |
| `Spike.Test.Frame0LinkedX64G` | 1.5 GiB (1587 MB) | 45 s |
| `Spike.Test.Call1LinkedX64G` | 1.5 GiB (1584 MB) | 49 s |
| `Spike.Test.Ret0LldX64G` | 1.5 GiB (1580 MB) | 48 s |
| `Spike.Test.X64Hello1GOut` | 1.2 GiB (1207 MB) | 19 s |
| `Spike.Test.X64Call1GOut` | 1.2 GiB (1189 MB) | 19 s |
| `Spike.Test.X64Ret0GOut` | 1.1 GiB (1144 MB) | 18 s |
| `Spike.Test.X64Frame0GOut` | 1.1 GiB (1135 MB) | 18 s |

These other modules need more than 3.5 GiB each (peak anonymous
memory per process in the release build):

| Module | Peak anonymous memory |
|---|---|
| `Spike.Test.X64Hello1PlaceOK` | 5.2 GiB (5292 MB) |
| `Spike.Test.A64HelloRootLitSmoke` | 4.0 GiB (4134 MB) |
| `Spike.Test.A64HelloRootBaseInhSmoke` | 4.0 GiB (4132 MB) |
| `Spike.Test.Call1LinkedX64` | 3.9 GiB (4029 MB) |
| `Spike.Lib.A64HelloCode` | 3.9 GiB (3973 MB) |
| `Spike.Test.Ret0LinkedA64` | 3.8 GiB (3917 MB) |
| `Spike.Test.WakeLinkedX64A2` | 3.8 GiB (3907 MB) |
| `Spike.Test.Ret0LldX64` | 3.8 GiB (3893 MB) |
| `Spike.Test.WakeLinkedA64A2` | 3.8 GiB (3882 MB) |
| `Spike.Test.Ret0LinkedX64` | 3.7 GiB (3809 MB) |
| `Spike.Test.Frame0LinkedX64` | 3.7 GiB (3780 MB) |
| `Spike.Test.WakeLinkedX64Load` | 3.7 GiB (3761 MB) |
| `Spike.Lib.A64WakeCode` | 3.6 GiB (3702 MB) |

**Checking the `hello1` theorems.**

```
lake build Spike.Test.A64Hello1FinalCA Spike.Test.X64Hello1FinalC
```

builds the two statements with their `#print axioms` guards, the linked
layouts (`Spike.Test.Hello1LinkedA64`, `Spike.Test.Hello1LinkedX64`, which
read the checked-in executables and check their SHA-256) and the
certificates. A successful build is the check.

**Compiling, linking and running `hello1`.** From the repository root, with
the output in a temporary directory (`T=$(mktemp -d)`), using `run.sh`'s
link commands:

```
.lake/build/bin/scc --arch arm -o $T/hello1a.s Scc/Test/hello1.w
clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static \
  -fuse-ld=lld -o $T/hello1a $T/hello1a.s
qemu-aarch64 $T/hello1a; echo $?      # Hello, world / 0
.lake/build/bin/scc --arch x64 -o $T/hello1.s Scc/Test/hello1.w
as -o $T/hello1.o $T/hello1.s && ld -static -o $T/hello1 $T/hello1.o
$T/hello1; echo $?                    # Hello, world / 0
```

These binaries are not certified (§0); to compare them with the certified
ones, `cmp $T/hello1a.s Scc/Test/elf/hello1a64/hello1.s` (and the x86-64
pair), and `Scc/Test/elf.sh --relink-check` for the executables.

**Compiling and running `ret0`.**

```
.lake/build/bin/scc --arch arm -o $T/ret0a.s Scc/Test/ret0.w
clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static \
  -fuse-ld=lld -o $T/ret0a $T/ret0a.s
qemu-aarch64 $T/ret0a; echo $?        # 42
.lake/build/bin/scc --arch x64 -o $T/ret0.s Scc/Test/ret0.w
as -o $T/ret0.o $T/ret0.s && ld -static -o $T/ret0 $T/ret0.o
$T/ret0; echo $?                      # 42
```

**Checking the `wake` theorems.**

```
LEAN_NUM_THREADS=1 lake build Spike.Test.WakeLinkedA64Root
```

builds `wake_linkedU` with its `#print axioms` guard, the linked layout
(`Spike.Test.WakeLinkedA64Elf`, which reads the checked-in executable and
checks its SHA-256) and the certificate. A cold build time was not measured for this release. Its
largest module is the certificate `Spike.Test.Cert.A64WakeCert` (table
above), and no other module it builds needs more than 3.8 GiB RssAnon.

```
LEAN_NUM_THREADS=1 lake build Spike.Test.WakeLinkedX64Root
```

builds `wake_linkedX` with its `#print axioms` guard, the linked layout
(`Spike.Test.WakeLinkedX64Elf`, which reads the checked-in executable and
checks its SHA-256) and the certificate. A cold build time was not measured for this release. Its
largest modules are `Spike.Test.WakeLinkedX64A2` and the certificate
`Spike.Test.Cert.X64WakeCert` (tables above), and no other module it builds
needs more than 3.2 GiB.

**Checking the `hello` theorem (AArch64).**

```
LEAN_NUM_THREADS=1 lake build Spike.Test.HelloLinkedA64Root
```

builds `hello_linkedA` with its `#print axioms` guard, the linked layout
(`Spike.Test.HelloLinkedA64Elf`, which reads the checked-in executable and
checks its SHA-256) and the listing, and the certificate module
`Spike.Test.Cert.A64WakeCert` it depends on (table above). A cold build time was not measured for this release. The
placement modules `HelloLinkedA64A1` … `A8` each stay at or under about
1.4 GiB RssAnon; A2's loader check is split into one module
per conjunct, `Spike.Test.HelloLinkedA64A2{load,abort,image}`,
each under 1 GB in our build. No other module it builds needs more than 3.9 GiB
(`Spike.Lib.A64HelloCode`, table above).

**Checking the x86-64 `hello` theorem.**

```
LEAN_NUM_THREADS=1 lake build Spike.Test.HelloLinkedX64Root
```

builds `hello_linkedX` and `hello_linkedX_linux` with their `#print axioms`
guards, the linked layout (`Spike.Test.HelloLinkedX64Elf`, which reads the
checked-in executable and checks its SHA-256) and the listing. The x86-64
`hello` development's modules are listed in `Spike/HelloTargetsX64.txt` (557
modules, some of them outside this root's import closure). It depends on
the certificate module `Spike.Test.Cert.X64WakeCert` (table above). A cold build time was not measured for this release. A2's loader
checks at `Λe` and at `Λ1` are split into one module per conjunct,
`Spike.Test.HelloLinkedX64A2{size,nodup,quad,rest,abort,image}` and
`Spike.Test.HelloLinkedX64L1A2{size,nodup,quad,rest,abort,image}`, each
under 1 GB in our build. No other module it builds needs more than 3.2 GiB.

**Certifying a fresh build** (`Accepted0`/`Accepted1` programs,
`hello1.w`, and `wake.w` and `hello.w` on both ISAs at their checked-in executables). The last line is the verdict, followed by time and peak RssAnon
of the checking Lean process:

| Command | Verdict |
|---|---|
| `Scc/Test/certify.sh --arch arm --instantiate Scc/Test/ret0.w` | **certified** (379 s, 2383 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Scc/Test/ret0.w` | **certified** (294 s, 2103 MB) |
| `Scc/Test/certify.sh --arch arm --instantiate Spike/Gen/frame0.w` | **certified** (382 s, 2359 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Spike/Gen/frame0.w` | **certified** (289 s, 2085 MB) |
| `Scc/Test/certify.sh --arch arm --instantiate Scc/Test/hello1.w` | **certified** (54 s, 1377 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Scc/Test/hello1.w` | **certified** (49 s, 1382 MB) |
| `Scc/Test/certify.sh --arch arm --instantiate Scc/Test/wake.w` | **certified** (3 s, 154 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Scc/Test/wake.w` | **certified** (3 s, 145 MB) |
| `Scc/Test/certify.sh --arch arm --instantiate Scc/Test/hello.w` | **certified** (3 s, 153 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Scc/Test/hello.w` | **certified** (3 s, 155 MB) |
| `Scc/Test/certify.sh --arch arm --granule --instantiate Scc/Test/ret0.w` | **certified** (387 s, 2336 MB) |
| `Scc/Test/certify.sh --arch x64 --granule --instantiate Scc/Test/ret0.w` | **certified** (285 s, 2042 MB) |
| `Scc/Test/certify.sh --arch x64 --granule --instantiate Scc/Test/ifsub1.w` | **certified** (291 s, 2042 MB) |
| `Scc/Test/certify.sh --arch arm --granule --instantiate Scc/Test/hello1.w` | **not certifiable, exit 3** (1 s, no Lean check) |
| `Scc/Test/certify.sh --arch x64 --granule --instantiate Scc/Test/hello1.w` | **not certifiable, exit 3** (1 s, no Lean check) |

For `hello1.w`, the first run builds `Spike.Test.X64Hello1FinalC` /
`Spike.Test.A64Hello1FinalCA` if they are not built (peak 3.4 GiB RssAnon,
`Spike.Test.A64Hello1TgOk`; the cold build time was not measured for this
release).

`certify.sh -v` prints every command it runs and the Lean files it writes,
so a run can be repeated by hand. Any other program outside `Accepted1`,
`hello1.w` compiled to a different text, or `wake.w` or `hello.w` with
another text or executable, is **not certifiable**. For `wake.w` the first
run builds `Spike.Test.WakeLinkedA64Root` or `Spike.Test.WakeLinkedX64Root`
if it is not built (above), and for `hello.w`
`Spike.Test.HelloLinkedA64Root` or `Spike.Test.HelloLinkedX64Root`; the
times in the table are with it built.
**Tests.**

- Every `#print axioms` of a §1 final: `propext`, `Classical.choice` and
  `Quot.sound` (48 names in 32 modules; `ret0_codeEnd` on each ISA depends on
  no axiom); `#print axioms` over every non-test module (3627 modules)
  reports no other axiom.
- `Scc/Test/run.sh`, both ISAs: 85 checks, 79 passed, 0 failed,
  6 not certifiable; certificates 15 certified, 6 not certifiable
  (`deeprec`, `growmany`, `spill`, `stackcap` and `stackdepth` without a
  stack need table, `tailwide` refused by A12). The checks include a
  `--granule` run of each of the 21 programs (all ok); `run.sh` checks no
  granule certificate.
- `Scc/Test/blocks.sh --check`: 42 passed; `Spike/Gen/drift.sh`: clean;
  `Scc/Test/elf.sh`: ok; `Scc/Test/elf.sh --relink-check`: ok
  (including the eight `*g/` executables); `Scc/Test/elf.sh --raw-check`:
  ok; `Scc/Test/textalign.sh`: ok (21 programs).
- `Scc/Test/certify_test.sh`: 126 ok, 0 failed, 0 skipped, with `lake env`
  processes allowed 6 GiB (`KRAKEN_ENV_MAX=6G`, as in `tools/quick_gate.sh`),
  without
  `CERTIFY_TEST_SKIP_MISSING` (including the `--granule` cases: `ret0` on
  both ISAs, `ifsub1` on x86-64, `ret0` with `CERTIFY_X64_FRAGMENT=0`,
  `ret0`'s post-pass listing linked by `ld.lld`, and exit 3 for `hello1.w`
  with `--granule` on both ISAs; and the refusals of `reject_device.w`,
  `reject_devext.w` and `reject_spawni.w`). Tool versions of the linker
  matrix: GNU ld 2.47, gold 1.16, LLD 21.1.8 and clang 21.1.8.
- `tools/diff_place.sh`: ok on both ISAs (wide: 0 certifiable, 19 refused by
  A12, 11 without a stack need table; narrow: 21 certifiable, 9 without a
  stack need table; 0 failed). The AArch64 runs took 75 minutes and were
  run separately from the rest of the release run.
- `Kraken/AArch64/Test/asm_tests.py`: 66/66; `Kraken/X64/Test/asm_tests.py`:
  63/63.
- `Scc/Test/diff.sh -n 300`, each ISA: 300/300 agree with the reference
  interpreter, 0 mismatches; a placement sample of 30 generated programs:
  0 certifiable, 30 refused (19 by A12, 11 without a stack need table),
  0 failed.
- `tools/trusted_check.sh` at the release commit: no difference from
  `tools/trusted_paths.md5` (5826 trusted files); against the previous
  release, 20 added, 0 removed, 57 changed.
## 5. Scope and caveats

In this release `ret0.w` is certified at linked binaries and by `certify.sh
--instantiate` on a fresh build, `frame0.w` by `certify.sh --instantiate`,
`hello1.w` at every layout passing the placement check, by `certify.sh
--instantiate` on a fresh build, and at its two checked-in executables, and
`wake.w` and `hello.w` on AArch64 and x86-64 at their checked-in
executables, also by `certify.sh --instantiate` when a fresh build is those
files byte for byte; and, with `--granule`, `Accepted0`/`Accepted1` programs by `certify.sh
--granule --instantiate` at the `_final` theorems.

- **`wake`'s theorems are at one layout each.** They hold at `Λe`, the
  layout of `Scc/Test/elf/wakea64/wake` and of `Scc/Test/elf/wakex64/wake`
  respectively (x86-64 `.text` at `0x401000`, GNU `ld`'s default), only; a
  relink that moves anything is not certifiable. Each covers its
  checked-in text only.
- **`hello`'s theorems are at one layout each.** They hold at `Λe`, the
  layout of `Scc/Test/elf/helloa64/hello` (`.text` at `0x210550`, `.rodata`
  at `0x2001b8`, both placed by the link command) and of
  `Scc/Test/elf/hellox64/hello` (`.text` at `0x401000`, GNU `ld`'s default)
  respectively, only, and each covers its listing only. The canonical
  static link (`Scc.Cert.Link.canonical`, code at `0x400000`) is not such a
  layout.
- **The granule pass is certified only for `certify.sh`'s fragments.**
  With `--granule`, `certify.sh` instantiates the `_final` theorems for
  `Accepted0`/`Accepted1` programs (§1). The registry programs (`hello1`,
  `wake`, `hello`) answer exit 3 with `--granule`: their registry theorems
  are about the text without the pass. `hello1`'s and `ret0`'s checked-in
  post-pass executables have their own theorems at their layouts (§1);
  `call1`'s and `frame0`'s have the placement check only. The
  descriptor words are checked by the byte check (§3, item 18), not by a
  theorem, and nothing reads them at run time in the model.
- **The GC tables have no consumer.** The tables in `.rodata` (call maps at
  return addresses, successors, the descriptor) are proved equal to what
  scc's reference tables stage (`emitTables`) computes for the program
  (next item); this is not a claim about any collector's correctness. Nothing in this release
  reads them at run time, and no statement is about a collector.
- **GC tables.** A certificate does not run the reference liveness
  iteration. It checks a ranked witness per function
  (`Scc.Cert.Maps.leastOk`: a post-fixpoint whose every slot is justified at
  a rank below the iteration bound) and builds the tables from it.
  - The witness stage's result is the reference stage's
    (`emitTables_of_emitTablesW`, via `leastOk_mem` and
    `compute_of_computeWR`).
  - So the certificate's run is scc's run (`lowerAll_eq_of_tables`, the
    generated `prog_sameAsScc`, and `prog_tablesOk` gives the tables' data
    `tblLit` that ends the certificate's `.rodata`), and the statements are
    at scc's configuration.
  - The witness is untrusted: a wrong one makes the stage fail, and the
    certificate does not check.
- **Raw-host executables are not certified.**
  `Scc/Test/elf/hello1rawx64/hello1` and `Scc/Test/elf/hello1rawa64/hello1`
  (`scc --host raw`, linked with `Scc/Test/elf/raw.ld`) are only:
  - checked against the raw pipeline's listing and pinned by SHA-256
    (`Spike/Test/Hello1RawLinked{X64,A64}.lean`);
  - compared with the Linux build by `Scc/Test/elf.sh --raw-check`.

  The layout reader refuses them, because the entry is not the start of
  `.text`, and no placement check runs on them.
- **`wake`'s and `hello`'s root theorems.** `wake_linkedU`/`wake_linkedX`
  and `hello_linkedA`/`hello_linkedX` instantiate the root statements quoted
  in §1 (`wake_finalCA_genWP`, `wake_finalX_land` and the two
  `hello_root_final`) at `Λe`. Their premises are the boundary facts of §2,
  discharged at `Λe` by the `*Linked*` modules; the premises still open at
  the root level of `wake` are listed in §1.
- **Among the spawning programs, only `wake.w` and `hello.w` are proved**,
  on both ISAs, at their checked-in executables; `certify.sh` refuses any
  other spawning program (verdict 3 with `--instantiate`).
- **Superseded proof declarations remain in the tree**, off the final
  theorems' paths (x86-64 `hello`: the instances at the canonical map of
  owned words that have a generic twin, and an earlier chain of the root's
  obligations). No statement depends on them.
- **The cold builds of the `wake` and `hello` proofs are long** (§4).

- **`hello1`'s theorems are about one text.** They cover the checked-in
  certificate's `asm`; `certify.sh` certifies a build only when scc produces
  exactly that text. A change to scc that changes hello1's output makes
  `hello1.w` not certifiable until the theorems are redone.
- **The `Accepted2` statements are proved at the header bound only.**
  `Closed2StmtAH`/`Closed2StmtH` hold at configurations with
  `Scc.Obj.nShift cfg.layout.obj < 22`; without that premise
  `Closed2StmtA`/`Closed2Stmt` are proved only from the segment obligations
  `Closed2InA`/`Closed2In` (§1). `certify.sh` does not instantiate them.
- **`certify.sh` covers `Accepted0` and `Accepted1`.** It instantiates
  `a64_scc_correctE_text_closedAt1` on AArch64 and
  `x64_scc_correctE_text_closedAt1` (or `…_closedAt` for an `Accepted0`
  program whose `main` frame exceeds 4096 bytes) on x86-64 (their `_final` twins with `--granule`), and
  `hello1_finalCA_gen` / `hello1_finalC_gen` for `hello1.w`. Anything else
  that allocates, prints, spawns or recurses is outside it; scc's output for
  such programs is uncertified.
- **Placement check A12.** Functions with more than 6 (x86-64) or 8
  (AArch64) flattened parameter words are refused (the emitter's
  stack-passed parameters are not modelled), and so are programs whose
  runtime path reaches `spawn`. This costs completeness, not soundness: such
  programs fail closed. `Closed2Stmt(A)`'s placement premise includes A12, so
  it is non-vacuous only for programs within these limits.
- **Placement is not complete**, even within `Accepted0`: a program outside
  what `placeOKAt` accepts is refused, not certified, and certification cost
  grows with program size.
- **AArch64 runs under `qemu-aarch64` only** (`Scc/Test/armrun.sh`). qemu
  does not exhibit hardware weak-memory reorderings and is not the Linux
  kernel's ELF loader; the trusted loader facts of §3 are about Linux on
  hardware. No native AArch64 host was used. x86-64 binaries run natively.
- **Threads.** `hello1` and `ret0` run on one thread (`CorrectE 1`,
  `kernel 1`); `Accepted2` has no `spawn`. `wake` and `hello` run two threads
  (`CorrectE 2`) on the kernel model; under `qemu-aarch64` their runs do not
  exhibit hardware reorderings, but the theorem holds for every `arch`.
- The executable's **`.text` bytes are not compared with `asm`'s encoding**
  by any proof (trusted, §3 item 6), for `wake` and `hello` as for the
  others; `certify_test.sh` compares them for its links (`textcheck.py`), as
  a test.
- **The EFI runtime (`runtime/efi/`) is not verified and not covered.** It is ordinary C++ and
  assembly, tested only by `runtime/efi/qemu_smoke.py` under QEMU and by booting it. It
  implements 3 of the 14 kernel routines a raw unit calls (`scc_rt_alloc`, `scc_rt_print`,
  `scc_rt_exit_process`); the other 11 stop the machine with a panic message, so only raw units
  that use those three, such as `hello1`, run. There is one thread, on the boot CPU. The raw-host
  `hello1` executable it runs is the checked-in `Scc/Test/elf/hello1rawx64/hello1`, which is not
  certified either (see "Raw-host executables are not certified"). Building it needs GNU Unifont
  (`runtime/efi/stub/font.note`), which is not part of this repository.
- **Liveness/termination is not claimed** (§0). `CorrectE` is a trace-prefix
  refinement with justified aborts; that `wake`'s `main` is woken is not
  part of the statement.
- **`hello1`'s budget is fixed** to the allocator's cell count (`hB`); runs
  whose source would need more heap may abort with exit 101.
- **`print` is specified by its model.** The `hello1` theorem is about
  `hello1o`, with `print`'s WeakCore model linked; `hello`'s `print` is the
  model text written in `hello.w` (§3 item 9).
- **`emit` with outstanding promises.** Under WeakCore release 7 a thread
  cannot `emit` while it has outstanding promises; executions that need this
  (a store after an `emit`, promised before that `emit` runs,
  `TermRun.LBE`) are not part of the source semantics, and WeakCore lists
  them as not covered.
- **`write` and promises.** On AArch64, hello's print routine issues a full barrier (`dmb ish`) before its `write` system call, and only one thread prints a buffer that no thread writes after publishing it. So, for hello, the model's rule that no promise is outstanding across `write` rests on the same argued hardware facts as for `clone`, plus one model lemma about promises after a full barrier that is not yet proved.

  The argument and its known remaining points are in `Scc/DESIGN.md` §4 (*No promise across `clone`*, the
  paragraph on `write`), its trusted-base table, and §6 item 44.
- **Recursion depth.** Certificates set `maxRecDepth` right after the
  namespace: the reparse of a large asm can exceed the default. It changes no
  statement.
