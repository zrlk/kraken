# scc release note: `ret0.w` certified on x86-64

This note states what this release of `scc` proves, what it trusts, and what
it does not cover. Statements are quoted from the source tree.

## 0. The claim

For `Scc/Test/ret0.w` (`main` returns `40 + 2`), compiled by `scc --arch x64`
to the assembler text `⟨asm, sizes, labelOffs⟩`:

- **At any layout `Λ` at which the output passes the placement check**, the
  text is `CorrectE` with respect to the program's WeakCore semantics, on the
  kernel-model x86-64 target `Scc.Sem.X64.target (kernel 1) E` (one thread
  slot), at **every** admissible entry state `E`
  (`Spike.Test.Ret0ReleaseX64.ret0_correct`).
- **At the layout read off the executable** that GNU `as` + `ld -static` (no
  linker script, `Scc/Test/run.sh`'s command) link from that very text, the
  placement check is kernel-decided, so the theorem applies there
  (`Spike.Test.Ret0LinkedX64.ret0_linked_correct`). Its only premise is
  `hpa`, the certificate's compiled parse `#guard`.

**What `Correct` promises** (`Scc/Sem/Correct.lean`, module doc), and no
more:

- *Refinement of observations* (`Sim.sim`): the observable trace of every
  reachable target configuration (its trace less the `writeErr`, `cloneErr`
  and `abort` events) is a **prefix** of the trace of a related source run.
- *Aborts only where justified* (`Sim.abort`): the target may abort (exit
  101) only where `AbortJustified` holds: the related source thread's next
  step would leave the budget `B`, or (for `writeErr`, `threads`) the kernel
  refused an earlier `write` or `clone`.
- *The budget*: `B` is chosen by whoever produces the certificate, and the
  theorem holds for every `B`; the guarantee reads "correct for every run
  whose source stays within `B`". For `ret0` (no heap, threads or writes) the
  only reachable aborts are `overflow`/`stack` under a small `B`; the
  statement still admits them.
- *No termination promise*: a target that diverges or blocks satisfies the
  statement. If the program exits, it exits as the source does, or aborts
  with exit 101 where `Correct` justifies it.

## 1. Statements (verbatim)

`Spike/Test/Ret0ReleaseX64.lean`:

```lean
theorem ret0_correct (Λ : Scc.Sem.Layout) (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (h : Scc.Cert.PlaceOK.X64.placeOKAt placeCfg Λ out = true)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs = true) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) prog_src)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf main } B ⟨asm, sizes, labelOffs⟩

theorem ok_witness_of_placeOKAt {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt placeCfg Λ out = true) :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf main }
```

(`ret0_correct_tables` is `ret0_correct` at the certificate's own static
link, where the certificate proves `h`.)

`Spike/Test/Ret0LinkedX64.lean`, where `def elf := scc_elf_layout% "Scc/Test/elf/ret0x64/ret0"` and
`abbrev Λe := elf.1`:

```lean
theorem ret0_codeEnd : Scc.Sem.X64.codeEnd Λe.code.lo outLit.prog = Λe.code.lo + Λe.code.size
theorem ret0_placeOKAt : X64.placeOKAt placeCfg Λe out = true
theorem ret0_linked_correct (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs = true) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main } B
      ⟨asm, sizes, labelOffs⟩
```

The generic compiler theorem behind it (`Spike/Lib/LowerX64/Correct.lean`),
for every one-declaration program `[d]` that `scc` accepts:

```lean
theorem x64_scc_correctE_text_closedAt (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := immsOf d } B ⟨text, sizes, labelOffs⟩
```

`#print axioms` on the release theorems (`ret0_correct`, `ret0_correct_tables`,
`ok_witness_of_placeOKAt`, `ret0_linked_correct`, and the generic
`x64_scc_correctE_closedAt`/`_text_closedAt`): `[propext, Classical.choice, Quot.sound]`.
`ret0_codeEnd` and `ret0_placeOKAt` are on `ret0_linked_correct`'s guarded chain.

**Why the conclusion's layout overrides `static` and `imms`.** The placement
check reads neither field (`placeOKAt_static`); a program in the fragment
(`Accepted0`) allocates no static label, and `imms` is the proof's table of
constants folded into instructions, not an input of the loader nor of
anything `Correct` fixes outside the witness. `Spike/Test/X64StaticImmsOverride.lean`
checks that the loader, label resolution, the marks, `InLayout`, `Entry.Ok`,
well-formedness and the placement check agree at `Λ` and at the overridden
layout.

**Non-vacuity.** The entry quantifier is inhabited at every layout passing
the check (`ok_witness_of_placeOKAt`, and at `Λe`: `ret0_linked_witness`).
The source reaches `[exit 42]` (`src_reach_exit42`,
`Spike/Test/A64ReviewClosed.lean`, kernel-checked, every `arch`). It is
stated at the AArch64 certificate's `SccCertificate.prog_src`; the x86-64
certificate's `prog_src` is textually identical (the two certificates'
`source`/`prog_src` blocks agree under `diff`; not a theorem, as the two ISAs
cannot be imported together), and `srcP1 arch` is ISA-independent. Perturbed
layouts fail closed (`Ret0LinkedX64`): code one byte short (also
kernel-checked via `placeOKAt_eq_false_of_a1`), a wrong abort label, the code
base one byte off.

## 2. What ties the theorem to the linked binary

The theorem is not applied at an assumed static link: the placement check is
decided at the layout of the binary actually linked.

1. `ret0.s` is `SccCertificate.asm` verbatim (`#eval` guard in
   `Ret0LinkedX64`); the certificate's reproducibility guard ties `asm` to
   scc's output, and `Spike/Gen/drift.sh` ties the certificate to the current
   scc.
2. GNU `as` 2.47 + `ld -static` link it (no script); the binary runs and
   exits 42. `Scc/Test/elf.sh --relink` rebuilds it.
3. The ELF reader reads `Λe` off the file (`scc_elf_layout%`, fail closed);
   `#guard elf.2 == "f202a51e…"` pins the file's SHA-256.
4. The kernel decides `placeOKAt placeCfg Λe out` component by component
   (`decide +kernel`, combined by `placeOKAt_of`), including A1's
   `codeFits` (the code ends inside `.text`) and A2's `abortStd`. The guard
   `ret0_codeEnd` shows the code fills `.text` exactly.
5. `ret0_correct` at `Λe`.

What this chain still trusts is in §3 (the reader, the loader's mapping, GNU
`as`'s encoding vs Kraken's parser and semantics, the evaluated steps).

## 3. Trusted base

The Lean kernel and its standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); Kraken's ISA semantics and memory models; the kernel model of
the system calls; `Correct` and the WeakCore source semantics as the
specification. In addition:

1. **The ELF layout reader** (`Scc/Cert/Elf.lean`). Evaluated by the
   elaborator (`scc_elf_layout%`), not replayed by the kernel: a `#guard`'s
   trust. It reads the System V gABI header, program, section and symbol
   tables of an ELF64 LE `ET_EXEC` file and fails closed. It checks itself:
   `.text` in an `R+X` (not `W`) `PT_LOAD` and mapped from its file bytes;
   `.rodata` in an `R`-only `PT_LOAD`, mapped from its file bytes, 8-aligned,
   and disjoint from the code, `.data`, the heap, the pinned region and the
   pool; one `R+W` (not `X`) writable `PT_LOAD` whose file part is exactly
   `.data` (giving `Λ.image`), with `.bss` and the regions in its zero tail;
   each region non-empty (`region`, size ≠ 0); the regions pairwise disjoint
   (explicit check, and `Link.wfB`, which also checks their 16-alignment);
   no unknown mapped section, dynamic or relocation section, executable stack
   or overlapping `PT_LOAD`; no data symbol in the code (always) or below it
   (while `refuseBelowCode` holds); **`e_entry` is the start of `.text`**
   (where A1 puts `_start`; tested on both ISAs' fixtures). It does not check
   that `.text` is non-empty. Trusted: that Linux maps exactly
   the `PT_LOAD`s with their `p_flags`, zero-filling `[p_filesz, p_memsz)`,
   and starts the thread at `e_entry`; the emitter's region symbols
   `scc_rt_heap`/`scc_rt_pinned`/`scc_rt_stacks` (`OBJECT`, sized, last in
   `.bss`) mark the regions. Not checked by the reader: that `.text`'s
   bytes are the certified program (the placement check reads the code from
   `asm` through `parsesTo`; items 4 and 5).
2. **Linux stack facts** (the release statement's entry quantifier,
   `Entry.Ok`). `Entry.Ok E Λ` requires `E.clear Λ` (`Scc/Sem/Target.lean`):
   the stack lies inside `2 ^ 64` and is disjoint from `Λ.rodata` and every
   range of `Λ.regions = [code, data, heap, stackPool, pinned]`
   (`Scc/Sem/Correct.lean`), i.e. from the code, `.rodata` and the data
   regions; plus `sp` 16-aligned, `sp < 2 ^ 63` and at least 64 KiB of
   stack. More `E` admitted makes the theorem stronger; the trusted Linux
   fact only needs to imply it: Linux starts a static executable with `sp`
   16-aligned and below `2 ^ 63`, with at least 64 KiB of mapped zero bytes
   below `sp` in the main thread's private memory, disjoint from the code,
   `.rodata` and the data regions, and every other register zero (the
   target's entry state, `threadAt`; `Scc/DESIGN.md` §4). The model does not
   include argc/argv/envp/auxv at and above `sp` (scc never reads them). The
   four conjuncts are constants, not a computed need (the x86-64 start-up's
   callee region reaches 296 bytes below `sp`, `EC`).
3. **The trusted loader places data symbols below the code.** This is
   trusted behaviour of `T.load`, not a placement check:
   - `Layout.WF.symAbove` (and `wfB`) is two-sided: a data symbol is
     below the code's start or at or above its end (`WF.sym_not_code`
     follows);
   - the loaders' `symsAbove lo fin` refuses only symbols *inside* the
     code (the `symsAbove Λ.code.lo fin syms` conjunct of the AArch64 and
     x86-64 loaders);
   - `threadAt` lays out label cells below the code (`placeBelow`, `padTo`,
     the executable starting at `exeStart base syms`; `Scc/Sem/TargetX64.lean`),
     the others after it (`placeSyms`).

   The trust is that Linux's loader puts those symbols where `placeBelow`
   does. What still refuses symbols below the code is the reader
   (`refuseBelowCode := true`, `Scc/Cert/Elf.lean`) and the placement
   check's A2 `symsOk` (`Scc/Cert/LinkX64.lean`, `codeEnd < p.2`), until the
   layout lemmas take symbols below the code. `ret0`'s x86-64 executable has
   no symbol below the code, so this behaviour is not exercised by it.
4. **Evaluated, not kernel-checked, on the chain to the fixture** (each a
   `#guard`/`#eval` or elaboration-time evaluation; their trust is that of
   Lean's compiled evaluator):
   - `hpa`: the certificate's `#guard Scc.Cert.Link.X64.parsesTo ⟨asm,
     sizes, labelOffs⟩ out.prog out.secs` (the parser is `partial`); the
     theorems keep it as an explicit premise;
   - `#guard Scc.Cert.X64.reproduces config source asm` (scc on `source`
     gives `asm`) and `#guard Scc.Cert.SrcTerm.reads source prog_src` (the
     frontend's parse of `source` is `prog_src`), in the certificate;
   - `scc_elf_layout%` (item 1), the reader evaluated by the elaborator;
   - `#guard elf.2 == "f202a51e…"`, the pinned SHA-256 of the fixture
     (`Ret0LinkedX64`);
   - the `#eval` guard `ret0.s == asm` (`Ret0LinkedX64`).
5. **The artefact and its encoding.**
   - The binary that runs is the fixture file whose SHA-256 is pinned; no
     check ties a deployed binary to it beyond `elf.sh --relink` and that
     digest.
   - GNU `as` encodes each instruction of `asm` as the instruction Kraken's
     parser and ISA semantics read, at the size listed in `sizes`. `sizes`
     and `labelOffs` (read off GNU `as`'s object) are checked only for
     consistency (`sizes_ok`); `.text`'s bytes are never decoded or compared
     with `out.prog`. The reader checks only `.text`'s extent, through A1's
     `codeFits` and `ret0_codeEnd`.
6. **The target model's entry**: `target (kernel 1) E` for each admissible
   `E`, not only `Entry.linux`.

**Known documentation gaps.** The module docs of `Scc/Sem/CorrectE.lean` and
`Scc/DESIGN.md`'s §4 do not yet say all of the above: `Entry.Ok` admits
any stack inside `2 ^ 64` disjoint from the code, `.rodata` and the data
regions, above or below them, and that the quantifier is inhabited is a
separate, proved fact (`Entry.ok_witness`: a layout ending at or below
`2 ^ 32` admits the witness `⟨⟨2 ^ 32, 65536⟩⟩`). This note is the
authoritative statement of the trust base.

## 4. Reproducing

- `lake build` of `Spike Scc scc scc_x64 scc_arm` and the test modules;
  `#print axioms` over every non-test module reports only `propext`,
  `Classical.choice` and `Quot.sound`.
- `Scc/Test/run.sh`, both ISAs: 48 checks, 40 passed, 0 failed, 8 not
  certifiable; certificates 7 certified, 8 not certifiable.
- `Scc/Test/blocks.sh --check`: 30 passed; `Spike/Gen/drift.sh`: clean;
  `Scc/Test/elf.sh`: ok.
- `Scc/Test/certify_test.sh`: all passed; `Scc/Test/certify.sh --arch x64
  --instantiate Scc/Test/ret0.w`: **certified** (about 51 s, 1.45 GB).
- `Scc/Test/diff.sh -n 300`, both ISAs: 300/300 agree with the reference
  interpreter, 0 mismatches; a placement sample of 30 generated programs: 19
  certifiable, 11 not, 0 failed.
- The fixture binary exits 42 natively; an independent relink (GNU binutils
  2.47) is byte-identical.

## 5. Scope and caveats

In this release only `ret0.w` has been certified at a linked binary. The generic
theorem covers every `Accepted0` program at any layout passing `placeOKAt`, but
that is not a certificate for a given binary until it is instantiated, so scc's
output for any other program is uncertified.

- One program certified end to end on x86-64 at the linked layout:
  `ret0.w`. The compiler theorem covers `Accepted0` (one `main`, straight-line
  checked arithmetic); anything that calls, allocates, prints, spawns or
  branches is uncertified.
- AArch64: the compiler theorem has the same statement shape. Its end-to-end
  test is pending: `ld.lld` puts `.rodata` below `.text`, and the reader's
  `refuseBelowCode` and A2's `symsOk` still refuse symbols below the code.
- The executable's `.text` bytes are not compared with `asm`'s encoding;
  the link is GNU `as` on the very text the certificate checked (trusted,
  §3 item 5).
- Liveness/termination is not claimed (§0).
- **Placement is not complete, even within `Accepted0`.** A program
  outside what `placeOKAt` accepts is refused (fail closed), not certified.
  Known case: on x86-64, a `main` with no `+` at all (`ret N`; zero-slot
  frame) fails A9, at every layout; AArch64 accepts it. Found by a sample
  (`certify.sh --instantiate` on generated `Accepted0` programs: x86-64 17/20
  certified, the 3 others this case; AArch64 20/20). Under investigation; it
  does not affect `ret0.w`. Certification cost also grows with program size:
  about 130 `+`s already reaches 4 GB on AArch64 (measured).
- **hello1 is not covered.** Its certificate exists and `drift.sh` checks it
  against scc's output, but `hello1.w` is outside `Accepted0` (it prints;
  three declarations) and fails A11, so it is uncertified.
- **Recursion depth.** Certificates set `maxRecDepth` right after the
  namespace: the reparse of a large asm can exceed the default. Not needed for
  `ret0`; it changes no statement.
- **Runtime counters.** The hand-written runtime proofs (the `ret0` oracle
  layouts, e.g. `Spike/Lib/Rt/X64LayoutOfPlaceOK.lean`'s `ret0P`) use the
  counters at their fixed canonical addresses (`0x600000`, …), kept there,
  16-aligned. These proofs are not on `ret0_linked_correct`'s chain, which
  reads every address off `Λe`.
- **Tests**: AArch64 binaries run under `qemu-aarch64` by default
  (`Scc/Test/armrun.sh`, `--arm-run qemu|native|auto`); qemu does not exhibit
  hardware weak-memory reorderings. x86-64 binaries run natively.
