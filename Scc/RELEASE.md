# scc release note: `wake.w` and `hello.w` certified on AArch64 and x86-64 at their executables; `hello1.w` and `ret0.w` on AArch64 and x86-64

This note states what this release of `scc` proves, what it trusts, and what
it does not cover. Statements are quoted from the source tree.

## New in this release: GC tables, relinked executables, memory, raw-host executables, and `write` after a barrier

The statements of the final theorems in §1 are those of the previous
release, word for word, and so are their axioms; the layouts and SHA-256
pins they are instantiated at change with the relink below. One premise of
the `wake` and `hello` root statements quoted in §1 changes: the bytes
required inside the pinned region from the first TCB's address grow from
168 to 200 (`hpin2`; §1 `hello`, x86-64). WeakCore stays at 621ec97a (next
section, unchanged).

- **GC tables are checked against scc's reference.** scc emits GC tables
  (the call maps at return addresses, successors and the descriptor
  `scc_gc_desc` in `.rodata`). Each certificate proves that the tables in
  its text are those scc's reference tables stage computes for the program
  (`prog_tablesOk`, `prog_sameAsScc`). It does so without running the
  reference iteration, by checking a least-fixpoint witness. Nothing reads
  the tables at run time, and no statement is about a collector (§5,
  *GC tables*).
- **Twelve executables are relinked.** `ret0` (x86-64 with GNU `ld`, x86-64
  with `ld.lld`, AArch64), `call1` (x86-64, AArch64), `frame0` (x86-64),
  `hello1` (x86-64, AArch64), `hello` (AArch64, x86-64) and `wake`
  (AArch64, x86-64). Their `.s` files are regenerated with the GC tables,
  and their SHA-256 pins and the layouts quoted in §1 and §2 change with
  them. `Scc/Test/elf.sh --relink-check` reproduces them byte for byte.
- **Building needs more memory.** The largest module, `WeakCore.TermStep`,
  needs about 6 GiB of anonymous memory, and the certificate modules
  2.0–5.4 GiB each (§4).
- **Raw-host executables.** `scc --host raw` builds of `hello1.w` for both
  ISAs are checked in (`Scc/Test/elf/hello1raw{x64,a64}/hello1`). They are
  pinned and compared with the Linux build, not certified (§4, §5).
- **`write` and promises.** On AArch64 the print routine issues `dmb ish`
  immediately before its `write`, and the placement check verifies it
  (`printIn`). What this argues and what remains open is in §5.

## WeakCore 621ec97a (unchanged since the previous release)

This section is carried over from the previous release; nothing in it
changes in this one. The vendored WeakCore (`WeakCore/`) is upstream
621ec97a, and scc and its proofs are adapted to it.

What changes for users:

- **Typed allocation, `new[T] a`.** A `new` in a source program now names
  the type it allocates at (`CoreTerm.Op.new a (some T)`). WeakCore's checker
  refuses a `new` without the annotation ("new: the allocation's type
  annotation is missing") and one whose annotation is not the value's type.
  The test programs now write, for example, `let o = new[Int] z`. scc lowers
  `new[T] a` as it lowered `new a`: the emitted assembly of the `Scc/Test`
  programs was unchanged on both ISAs by this change, and so were the
  checked-in texts and executables at the time (`Scc/Test/elf.sh
  --relink-check`, the `regen_*.sh --check` runs); this release regenerates
  them for the GC tables (above). The wake certificate's `source` changes by that line; its `asm` does
  not.
- **Certificate windows are proved.** WeakCore's soundness theorems assumed
  the certificate-window conditions `CertWinCN` and `CertWinPN` (and their
  spawn and extern forms). They are now discharged inside WeakCore's proof
  (`ObligationsFX.toObligationsCX`), so the obligations scc supplies no
  longer contain them.
- **`emit` takes no promises.** `emit` is now an `ExtNeedsNoProm` call
  (`TermRun.ExtNeedsNoProm`): a thread takes it only with no outstanding
  promise, and a certification run never takes it, so no promise spans an
  output byte. This removes from the source semantics the executions in
  which a store after an `emit` is promised, and read by another thread,
  before that `emit` runs (`TermRun.LBE`); WeakCore lists them as not
  covered (§5). On the scc side, the source step of `emit` takes
  `th.promises = []` as a hypothesis, discharged by `prom_nil_of_write`
  (`Scc/Sem/CertSys.lean`).
- **The opened-scope check.** The checker refuses an allocation inside an
  opened type package whose type mentions the hidden type and could be a
  type-test target, and a call that passes such a type to a callee that
  allocates so (`CoreTerm.scopeAllocOK`, at `annNew` and `progTgts`). scc's
  frontend refuses type tests (`isTy`), so an accepted program has no
  type-test target and this check refuses none of them.

**The premise guard.** WeakCore ships a guard,
`WeakCore/extras/tools/premises/guard.sh`, that freezes the meaning of the
statements of WeakCore's final theorems: the transitive closure of the
definitions each statement mentions, printed and compared with the vendored
set. It was run with this repository's toolchain on a cold build of
`WeakCore`, including the nine modules that only the guard imports
(`TermProgress`, `TermLiveL3`, `TermLiveCertRun`, `TermLiveCertScen`,
`TermLiveC`, `TermLiveG3`, `SceProof`, `TermStartD`, `DmaRing`):

```
cd WeakCore/extras
WM_BUILD=<repository>/.lake/build/lib/lean WM_LEAN=<lean> tools/premises/guard.sh
```

Its last lines:

```
premise set: sets/pr-release-15067-vendored (da7648300c64202c3b348dad50a81c22; lean: Lean (version 4.35.0-pre, x86_64-unknown-linux-gnu, commit d0d716161618bd9fbd0bf2d9b8bbb9b48cccd7dd, Release); layout: vendored)
premises: meaning unchanged (143 finals/premises; set sets/pr-release-15067-vendored da7648300c64202c3b348dad50a81c22)
```

**What the guard does not cover.** The closure stops at WeakCore's machine
and language layer (`CheckPremises.stopModules`, which includes `CoreTerm`
and `TermRun`). Definitions there are listed by name only; their bodies are
not frozen. Among them, the release depends on these bodies:
- `TermRun.tstep`, one step of one thread; its `new` step now records the
  allocation's type, and whether that type is a type-test target, in the
  thread's `tys`;
- `CoreTerm.scan`, `CoreTerm.annNew` and `CoreTerm.progTgts`: the walk of the
  opened-scope check, the allocation annotation, and the program's type-test
  targets;
- `TermRun.tysOf`, the type recorded for an allocation label in a
  configuration.

The guard would not report a change to these bodies. They are part of the
specification (§3, item 15).

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

### The fragment-generic statements (open)

`Spike/Lib/LowerA64/Closed2StmtA.lean` and
`Spike/Lib/LowerX64/Closed2Stmt.lean` state the compiler theorem for every
`Accepted2` program (setup block, `newBuf`, lane stores, `print`) whose
`main` ends on every path in a call returning its result or a literal
(`mainRetOk`). They are **stated as `Prop`s, not proved**:

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

What the tree proves about them is conditional:

- `a64_scc_correctE_text_closedAt2 (H : Closed2InA) : Closed2StmtA`
  (`Spike/Lib/LowerA64/Closed2AtA.lean`) and
  `x64_scc_correctE_text_closedAt2 (H : Closed2In) : Closed2Stmt`
  (`Spike/Lib/LowerX64/Closed2At.lean`): each from the segment obligations
  `Closed2In(A)` (`In2A`/`In2X` at every instance and admissible entry state),
  which are **not proved** for the fragment. No theorem in the tree proves
  `Closed2Stmt` or `Closed2StmtA` outright.
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
    (with `new`), `CoreTerm.scan`, `CoreTerm.annNew`, `CoreTerm.progTgts` and
    `TermRun.tysOf` are part of the source semantics and are not covered by
    WeakCore's premise guard (see "WeakCore 621ec97a (unchanged since the previous release)"). This is the
    definition text of WeakCore 621ec97a as vendored.

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

## 4. Reproducing

**Building.** `lake build Kraken KrakenAArch64 WeakCore Scc Spike scc`
(5953 jobs), then `lake build scc_x64 scc_arm` and the test modules.

**Memory.** Build with `LEAN_NUM_THREADS=1`: Lake may run several `lean`
processes at once, each single-threaded, and the figures below are per
process. The WeakCore and certificate modules in the tables below were built alone,
once their imports were built; the third table is from the release build,
where several single-threaded `lean` processes ran at once. The largest module, `WeakCore.TermStep`, needs about
6 GiB of anonymous memory; the largest certificate module,
`Spike.Test.Cert.A64Chain5Cert`, about 5.4 GiB.
The resident size also counts the mapped `.olean` files. Build each module
below alone once its imports are built, e.g.
`LEAN_NUM_THREADS=1 lake build WeakCore.TermStep`, with about 8 GB of memory
free and nothing else heavy running. To bound the total of a whole build,
build serially, e.g. `LEAN_NUM_THREADS=1 taskset -c 0 lake build Scc Spike`.
No module outside the three tables below needs more than 3.5 GiB of anonymous
memory.

WeakCore (unchanged since the previous release; peak anonymous memory / peak
resident size):

| Module | Anonymous | Resident |
|---|---|---|
| `WeakCore.TermStep` | 5.9 GiB | 7.4 GiB |
| `WeakCore.GenLayer` | 4.5 GiB | 6.1 GiB |
| `WeakCore.TermScopeFHM` | 4.0 GiB | 6.1 GiB |
| `WeakCore.TermPlant` | 2.9 GiB | 4.5 GiB |

A cold build of `WeakCore` with the nine guard-only modules took 52 minutes
on 16 cores.

The certificate modules need more memory than in the previous release. Peak
anonymous memory per module, each built alone with `LEAN_NUM_THREADS=1` once
its imports are built:

| Certificate module | Peak anonymous memory |
|---|---|
| `Spike.Test.Cert.A64Chain5Cert` | 5.4 GiB (5525 MB) |
| `Spike.Test.Cert.A64HelloCert` | 4.6 GiB (4742 MB) |
| `Spike.Test.Cert.A64WakeCert` | 4.0 GiB (4119 MB) |
| `Spike.Test.Cert.X64HelloCert` | 3.9 GiB (4040 MB) |
| `Spike.Test.Cert.X64WakeCert` | 3.5 GiB (3545 MB) |
| `Spike.Test.Cert.A64Hello1Cert` | 2.9 GiB (2953 MB) |
| `Spike.Test.Cert.A64Call1Cert` | 2.6 GiB (2659 MB) |
| `Spike.Test.Cert.X64Hello1Cert` | 2.5 GiB (2554 MB) |
| `Spike.Test.Cert.A64Ret0Cert` | 2.3 GiB (2378 MB) |
| `Spike.Test.Cert.X64Call1Cert` | 2.3 GiB (2307 MB) |
| `Spike.Test.Cert.X64Frame0Cert` | 2.0 GiB (2097 MB) |
| `Spike.Test.Cert.X64Ret0Cert` | 2.0 GiB (2092 MB) |

`Spike.Test.Cert.A64Chain5Cert` takes about 11 minutes.

These other modules need more than 3.5 GiB each (peak anonymous memory per
process in the release build):

| Module | Peak anonymous memory |
|---|---|
| `Spike.Test.X64Hello1PlaceOK` | 5.2 GiB (5291 MB) |
| `Spike.Test.A64HelloRootLitSmoke` | 4.0 GiB (4132 MB) |
| `Spike.Test.A64HelloRootBaseInhSmoke` | 4.0 GiB (4129 MB) |
| `Spike.Test.Call1LinkedX64` | 3.9 GiB (4019 MB) |
| `Spike.Lib.A64HelloCode` | 3.9 GiB (3967 MB) |
| `Spike.Test.Ret0LinkedA64` | 3.8 GiB (3927 MB) |
| `Spike.Test.WakeLinkedX64A2` | 3.8 GiB (3901 MB) |
| `Spike.Test.Ret0LldX64` | 3.8 GiB (3884 MB) |
| `Spike.Test.WakeLinkedA64A2` | 3.8 GiB (3873 MB) |
| `Spike.Test.Ret0LinkedX64` | 3.7 GiB (3811 MB) |
| `Spike.Test.Frame0LinkedX64` | 3.7 GiB (3768 MB) |
| `Spike.Test.WakeLinkedX64Load` | 3.7 GiB (3761 MB) |
| `Spike.Lib.A64WakeCode` | 3.6 GiB (3692 MB) |

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
| `Scc/Test/certify.sh --arch arm --instantiate Scc/Test/ret0.w` | **certified** (426 s, 2532 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Scc/Test/ret0.w` | **certified** (321 s, 4173 MB) |
| `Scc/Test/certify.sh --arch arm --instantiate Spike/Gen/frame0.w` | **certified** (405 s, 2518 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Spike/Gen/frame0.w` | **certified** (315 s, 4125 MB) |
| `Scc/Test/certify.sh --arch arm --instantiate Scc/Test/hello1.w` | **certified** (44 s, 2283 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Scc/Test/hello1.w` | **certified** (50 s, 4044 MB) |
| `Scc/Test/certify.sh --arch arm --instantiate Scc/Test/wake.w` | **certified** (3 s, 148 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Scc/Test/wake.w` | **certified** (3 s, 143 MB) |
| `Scc/Test/certify.sh --arch arm --instantiate Scc/Test/hello.w` | **certified** (3 s, 160 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Scc/Test/hello.w` | **certified** (3 s, 153 MB) |

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

- `#print axioms` over every non-test module (3404 modules) reports only
  `propext`, `Classical.choice` and `Quot.sound`.
- `Scc/Test/run.sh`, both ISAs: 60 checks, 54 passed, 0 failed,
  6 not certifiable; certificates 15 certified, 6 not certifiable
  (`deeprec`, `growmany`, `spill`, `stackcap` and `stackdepth` without a
  stack need table, `tailwide` refused by A12). Its `arith` certificate
  check peaks at about 10 GB of anonymous memory on x86-64 (9 GB on
  AArch64).
- `Scc/Test/blocks.sh --check`: 42 passed; `Spike/Gen/drift.sh`: clean;
  `Scc/Test/elf.sh`: ok; `Scc/Test/elf.sh --relink-check`: ok;
  `Scc/Test/elf.sh --raw-check`: ok; `Scc/Test/textalign.sh`: ok
  (21 programs).
- `Scc/Test/certify_test.sh`: 109 ok, 0 failed, 0 skipped,
  without `CERTIFY_TEST_SKIP_MISSING` (including `-v`, `hello1.w` on both ISAs at its `run.sh` link and at a
  moved link, `wake.w` and `hello.w` certified on both ISAs at their
  checked-in executables, `hello.w` refused at another link or with one byte
  changed, and refusals of other programs outside `Accepted1`). The linker
  matrix checks that each tool is installed and prints its version; the
  expectations were recorded with GNU ld 2.47, gold 1.16, LLD 21.1.8 and
  clang 21.1.8. A case whose tool is missing is skipped and counts as a
  failure unless `CERTIFY_TEST_SKIP_MISSING=1` is set, and a `.text` that
  differs from the assembled listing outside relocated fields
  (`Scc/Test/textcheck.py`) is a failure.
- `tools/diff_place.sh`: ok on both ISAs (narrow: 21 certifiable, 9 without a
  stack need table, 0 failed).
- `Kraken/AArch64/Test/asm_tests.py`: 66/66; `Kraken/X64/Test/asm_tests.py`:
  63/63.
- `Scc/Test/diff.sh -n 300`, each ISA: 300/300 agree with the reference
  interpreter, 0 mismatches; a placement sample of 30 generated programs:
  0 certifiable, 30 refused (19 by A12, 11 without a stack need table),
  0 failed.

## 5. Scope and caveats

In this release `ret0.w` is certified at linked binaries and by `certify.sh
--instantiate` on a fresh build, `frame0.w` by `certify.sh --instantiate`,
`hello1.w` at every layout passing the placement check, by `certify.sh
--instantiate` on a fresh build, and at its two checked-in executables, and
`wake.w` and `hello.w` on AArch64 and x86-64 at their checked-in
executables, also by `certify.sh --instantiate` when a fresh build is those
files byte for byte.

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
- **No `.text` granule pass in this release.** `scc` does not lay `.text`
  out in 64 KiB granules and writes no granule descriptor words. The layouts
  of §2 are the executables' as linked, and no statement mentions granules.
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
- **The `Accepted2` statements are open.** `Closed2Stmt`/`Closed2StmtA` are
  stated, and proved only from the segment obligations `Closed2In`/
  `Closed2InA`, which are not proved for the fragment (§1). `hello1` is
  proved for its own instance.
- **`certify.sh` covers `Accepted0` and `Accepted1`.** It instantiates
  `a64_scc_correctE_text_closedAt1` on AArch64 and
  `x64_scc_correctE_text_closedAt1` (or `…_closedAt` for an `Accepted0`
  program whose `main` frame exceeds 4096 bytes) on x86-64, and
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
- **Liveness/termination is not claimed** (§0). `CorrectE` is a trace-prefix
  refinement with justified aborts; that `wake`'s `main` is woken is not
  part of the statement.
- **`hello1`'s budget is fixed** to the allocator's cell count (`hB`); runs
  whose source would need more heap may abort with exit 101.
- **`print` is specified by its model.** The `hello1` theorem is about
  `hello1o`, with `print`'s WeakCore model linked; `hello`'s `print` is the
  model text written in `hello.w` (§3 item 9).
- **`emit` with outstanding promises.** Under WeakCore 621ec97a a thread
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
