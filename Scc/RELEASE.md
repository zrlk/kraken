# scc release note: `hello1.w` and `ret0.w` certified on AArch64 and x86-64

This note states what this release of `scc` proves, what it trusts, and what
it does not cover. Statements are quoted from the source tree.

## 0. The claim

### `hello1.w`

`Scc/Test/hello1.w` is one thread: a setup block `rodata` writes the 13 bytes
`Hello, world\n` into a fresh heap buffer, and `main` passes the slice to the
output extern `print` and returns 0. Compiled by `scc` to the assembler text
`asm` (AArch64) or `⟨asm, sizes, labelOffs⟩` (x86-64), its text is
`CorrectE` with respect to the program's WeakCore semantics with output, on
the kernel-model target with one thread slot, at **every** admissible entry
state, for every memory model `arch` and every budget `B` whose heap-cell
count is the allocator's (`Spike.Lib.LowerA64.hello1_finalCA`,
`Spike.Lib.LowerX64.hello1_finalC`).

> [!IMPORTANT]
> hello1's theorems are stated at **one layout**: `Λe`, read by the ELF
> reader from the executables checked in under
> `Scc/Test/elf/hello1a64/hello1` and `Scc/Test/elf/hello1x64/hello1`, each
> pinned by its SHA-256. A fresh build of `hello1.w` is **not** certified:
> `Scc/Test/certify.sh` covers only `Accepted0`/`Accepted1` programs, and
> `hello1.w` is in neither. The executables' sources (`hello1.s`, which is the
> certificate's `asm` verbatim) and their link commands are alongside, and
> `Scc/Test/elf.sh --relink-check` reproduces both executables byte for byte.

The only premises of the two theorems are `hpa`, the certificate's compiled
parse `#guard`, and `hB`, which fixes the budget's heap-cell count (§1). The
placement check at `Λe` and every correctness step are kernel-checked.

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
  For `hello1`, the observable events are the bytes written to fd 1 and the
  exit.
- *Aborts only where justified* (`Sim.abort`): the target may abort (exit
  101) only where `AbortJustified` holds: the related source thread's next
  step would leave the budget `B`, or (for `writeErr`, `threads`) the kernel
  refused an earlier `write` or `clone`.
- *The budget*: `B` bounds heap cells, threads ever created and per-thread
  call depth (`Scc.Sem.Budget`). The `ret0` theorems hold for every `B`. The
  `hello1` theorems hold for every `B` with `B.cells = allocCells`
  (4194304 16-byte cells, the allocator's arena, `Scc/Cert/PlaceOK.lean`); the
  thread and frame bounds are free.
- *No termination promise*: a target that diverges or blocks satisfies the
  statement. If the program exits, it exits as the source does, or aborts
  with exit 101 where `Correct` justifies it.

## 1. Statements (verbatim)

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
     `.rodata` and the stack map `scc_stackmap` below `.text` and adds a
     build-id note):

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
   file's SHA-256: `hello1` AArch64 `60378da8…`, `hello1` x86-64
   `e1b2ff37…`; `ret0` AArch64 `6087ccf2…`, x86-64 GNU `ld` `f202a51e…`,
   x86-64 `ld.lld` `56c83082…`. Guarded about the `hello1` layouts:
   - x86-64: `Λe.code.lo == 0x401000`, `.rodata` at or above the code's end,
     and every `.rodata` symbol at or above the code's start;
   - AArch64: `.rodata` ends at or below the code's start, the code's start
     is 16-aligned, and the only symbol below the code is `scc_stackmap`, at
     `.rodata`'s start. (The module doc gives `.text` at `0x210410`; that
     address is not guarded.)
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
`run.sh` link and prints **certified** (§4). For `hello1` there is no such
script: the chain above holds for the checked-in executables only.

What this chain still trusts is in §3.

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

1. **The ELF layout reader** (`Scc/Cert/Elf.lean`). Evaluated by the
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
   **Exercised** by `scc_stackmap` below the code in both AArch64 fixtures
   (`ret0`, `hello1`) and by `.rodata`'s labels in the x86-64 `ld.lld`
   fixture.
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
   the program with that model linked in.
10. **The allocator and the budget (`hello1`).** The allocator is runtime
    code in `hello1`'s text, checked by the placement check (A7 checks its
    arena constant) and covered by the proof, not trusted. What the
    statement fixes is the budget: `hB` ties `B.cells` to `allocCells`
    (4194304 cells of 16 bytes), so the guarantee is for runs whose source
    heap stays within that arena.

The trusted files' documentation states the above: `Scc/Sem/CorrectE.lean`
(the trusted Linux stack fact, separate from the proved witness),
`Scc/Sem/Correct.lean` (`Layout.WF`), `Scc/Sem/Kernel.lean` (the system
calls) and `Scc/DESIGN.md` §4 (the loader, the ELF reader, the `Entry.Ok`
quantifier) and its notes on AArch64 alignment.

## 4. Reproducing

**Building.** `lake build Spike Scc scc scc_x64 scc_arm` and the test
modules. Memory: `WeakCore/TermStep.lean` needs about 5.8 GB even with
`LEAN_NUM_THREADS=1`. The `hello1` certificate modules
`Spike.Test.Cert.A64Hello1Cert` and `Spike.Test.Cert.X64Hello1Cert` need
about **3.8 GiB per `lean` process** on a cold build, even with
`LEAN_NUM_THREADS=1`, and more at default threads; build them with
`LEAN_NUM_THREADS=1` and not alongside other heavy jobs. To bound the total
of a parallel build, build serially, e.g. `LEAN_NUM_THREADS=1 taskset -c 0
lake build Scc Spike`.

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

**Certifying a fresh build** (`Accepted0`/`Accepted1` programs only). The
last line is the verdict, followed by time and peak RssAnon of the checking
Lean process:

| Command | Verdict |
|---|---|
| `Scc/Test/certify.sh --arch arm --instantiate Scc/Test/ret0.w` | **certified** (66 s, 2009 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Scc/Test/ret0.w` | **certified** (59 s, 2052 MB) |
| `Scc/Test/certify.sh --arch arm --instantiate Spike/Gen/frame0.w` | **certified** (63 s, 2010 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Spike/Gen/frame0.w` | **certified** (57 s, 2057 MB) |

`certify.sh -v` prints every command it runs and the Lean files it writes,
so a run can be repeated by hand. On `hello1.w` it answers **not
certifiable** (outside `Accepted1`).

**Tests.**

- `#print axioms` over every non-test module reports only `propext`,
  `Classical.choice` and `Quot.sound`.
- `Scc/Test/run.sh`, both ISAs: 56 checks, 47 passed, 0 failed, 9 not
  certifiable; certificates 10 certified, 9 not certifiable.
- `Scc/Test/blocks.sh --check`: 38 passed; `Spike/Gen/drift.sh`: clean;
  `Scc/Test/elf.sh`: ok; `Scc/Test/elf.sh --relink-check`: ok;
  `Scc/Test/textalign.sh`: ok (19 programs).
- `Scc/Test/certify_test.sh`: all passed (including `-v`).
- `Kraken/AArch64/Test/asm_tests.py`: 66/66; `Kraken/X64/Test/asm_tests.py`:
  63/63.
- `Scc/Test/diff.sh -n 300`, each ISA: 300/300 agree with the reference
  interpreter, 0 mismatches; a placement sample of 30 generated programs:
  0 certifiable, 30 refused (19 by A12, 11 without a stack need table),
  0 failed.

## 5. Scope and caveats

In this release `ret0.w` is certified at linked binaries and by `certify.sh
--instantiate` on a fresh build, `frame0.w` by `certify.sh --instantiate`,
and `hello1.w` at its two checked-in executables.

- **`hello1` is certified at one layout.** Its theorems are stated at `Λe`,
  read from `Scc/Test/elf/hello1{a64,x64}/hello1` and pinned by SHA-256. A
  fresh build of `hello1.w`, or a link with another toolchain or command, is
  not certified, even if `elf.sh --relink-check` would reproduce it; the
  theorem covers the pinned files.
- **The `Accepted2` statements are open.** `Closed2Stmt`/`Closed2StmtA` are
  stated, and proved only from the segment obligations `Closed2In`/
  `Closed2InA`, which are not proved for the fragment (§1). `hello1` is
  proved for its own instance.
- **`certify.sh` covers `Accepted0` and `Accepted1`.** It instantiates
  `a64_scc_correctE_text_closedAt1` on AArch64 and
  `x64_scc_correctE_text_closedAt1` (or `…_closedAt` for an `Accepted0`
  program whose `main` frame exceeds 4096 bytes) on x86-64. Anything that
  allocates, prints, spawns or recurses is outside it; scc's output for such
  programs is uncertified.
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
- **One thread.** `hello1` and `ret0` run on one thread (`CorrectE 1`,
  `kernel 1`); `Accepted2` has no `spawn`. The statements hold for every
  `arch`, but a single thread does not exercise the memory model.
- The executable's **`.text` bytes are not compared with `asm`'s encoding**
  (trusted, §3 item 6).
- **Liveness/termination is not claimed** (§0).
- **`hello1`'s budget is fixed** to the allocator's cell count (`hB`); runs
  whose source would need more heap may abort with exit 101.
- **`print` is specified by its model.** The theorem is about `hello1o`, with
  `print`'s WeakCore model linked (§3 item 9).
- **Recursion depth.** Certificates set `maxRecDepth` right after the
  namespace: the reparse of a large asm can exceed the default. It changes no
  statement.
