# scc release note: `ret0.w` certified on AArch64 and x86-64

This note states what this release of `scc` proves, what it trusts, and what
it does not cover. Statements are quoted from the source tree.

## 0. The claim

For `Scc/Test/ret0.w` (`main` returns `40 + 2`), compiled by `scc` to the
assembler text `asm` (AArch64, `--arch arm`) or `⟨asm, sizes, labelOffs⟩`
(x86-64, `--arch x64`):

- **At any layout `Λ` at which the output passes the placement check**, the
  text is `CorrectE` with respect to the program's WeakCore semantics, on the
  kernel-model target (`Scc.Sem.A64.target (kernel 1) E`, `Arch.armv8`
  hooks; `Scc.Sem.X64.target (kernel 1) E`; one thread slot), at **every**
  admissible entry state `E` (`Spike.Test.Ret0ReleaseA64.ret0_correct`,
  `Spike.Test.Ret0ReleaseX64.ret0_correct`).
- **At the layout read off the executable** linked from that very text, the
  placement check is kernel-decided, so the theorem applies there. Its only
  premise is `hpa`, the certificate's compiled parse `#guard`. Three links:
  - AArch64: `clang` + `ld.lld` with `Scc/Test/run.sh`'s command (`clang
    --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static
    -fuse-ld=lld`, no linker script), which puts `.rodata` and its data
    symbol `scc_stackmap` **below** `.text` and adds a build-id note
    (`Spike.Test.Ret0LinkedA64.ret0_linked_correct`);
  - x86-64: GNU `as` + `ld -static` (no linker script, `Scc/Test/run.sh`'s
    command) (`Spike.Test.Ret0LinkedX64.ret0_linked_correct`);
  - x86-64: GNU `as` + `ld.lld -static` (no linker script), which also puts
    `.rodata` below `.text` (`Spike.Test.Ret0LldX64.lld_linked_correct`).

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

### AArch64

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

The generic compiler theorem behind it (`Spike/Lib/LowerA64/Correct.lean`),
for every one-declaration program `[d]` that `scc` accepts:

```lean
theorem a64_scc_correctE_text_closedAt (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (O).prog (O).secs = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := immsOf d } B asm
```

On AArch64 the text is the bare `asm` string: instructions are 4 bytes, so
there is no `sizes`/`labelOffs` table.

### x86-64

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

(`ret0_correct_tables` as on AArch64.)

`Spike/Test/Ret0LinkedX64.lean` (GNU `ld`), where
`def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/ret0x64/ret0"`
and `abbrev Λe : Scc.Sem.Layout := elf.1`:

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

`Spike/Test/Ret0LldX64.lean` (`ld.lld`), the same text, where
`def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/ret0x64lld/ret0"`
and `abbrev Λe : Scc.Sem.Layout := elf.1`:

```lean
theorem lld_codeEnd : Scc.Sem.X64.codeEnd Λe.code.lo outLit.prog = Λe.code.lo + Λe.code.size
theorem lld_placeOKAt : X64.placeOKAt placeCfg Λe out = true
theorem lld_linked_correct (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs = true) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main } B
      ⟨asm, sizes, labelOffs⟩
theorem lld_linked_witness :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main }
```

The generic compiler theorem (`Spike/Lib/LowerX64/Correct.lean`):

```lean
theorem x64_scc_correctE_text_closedAt (Λ : Scc.Sem.Layout) (hd : Scc.Lower.Accepted0 [d] = true)
    (h : placeOKAt pcfg Λ (O) = true) {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩ (O).prog (O).secs = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) [d])
      { Λ with static := fun _ => none, imms := immsOf d } B ⟨text, sizes, labelOffs⟩
```

### Axioms

`#print axioms`, each checked by a `#guard_msgs`, gives `[propext,
Classical.choice, Quot.sound]` for `ret0_correct`, `ret0_correct_tables` and
`ok_witness_of_placeOKAt` (both ISAs); `ret0_linked_correct` (both ISAs);
`ret0_linked_witness` (AArch64); `lld_linked_correct`; and the generic
`a64_scc_correctE_closedAt`/`_text_closedAt` and
`x64_scc_correctE_closedAt`/`_text_closedAt`. The `codeEnd` and `placeOKAt`
theorems at `Λe` are on the linked theorems' chains, so their guards cover
them.

**Why the conclusion's layout overrides `static` and `imms`.** The placement
check reads neither field (`placeOKAt_static`); a program in the fragment
(`Accepted0`) allocates no static label, and `imms` is the proof's table of
constants folded into instructions, not an input of the loader nor of
anything `Correct` fixes outside the witness.
`Spike/Test/A64StaticImmsOverride.lean` and
`Spike/Test/X64StaticImmsOverride.lean` check that the loader, label
resolution, the marks, `InLayout`, `Entry.Ok`, well-formedness and the
placement check agree at `Λ` and at the overridden layout; the AArch64 file
also checks that `static := none` is the identity on the reader's AArch64
layouts.

**Non-vacuity.** The entry quantifier is inhabited at every layout passing
the check (`ok_witness_of_placeOKAt`; at each `Λe`: `ret0_linked_witness`,
`lld_linked_witness`). The source reaches `[exit 42]` (`src_reach_exit42`,
`Spike/Test/A64ClosedChecks.lean`, kernel-checked, every `arch`). It is
stated at the AArch64 certificate's `SccCertificate.prog_src`; the x86-64
certificate's `prog_src` is textually identical (the two certificates'
`source`/`prog_src` blocks agree under `diff`; not a theorem, as the two ISAs
cannot be imported together), and `srcP1 arch` is ISA-independent. Perturbed
layouts fail closed: code one instruction (AArch64) or one byte (x86-64)
short, also kernel-checked via `placeOKAt_eq_false_of_a1` (`Ret0LinkedA64`,
`Ret0LinkedX64`); a wrong abort label (`Ret0LinkedA64`, `Ret0LinkedX64`);
the code base one instruction or byte off (all three); and the AArch64 file
with its entry point moved off `.text`'s start is refused by the reader.

## 2. What ties the theorem to the linked binary

The theorem is not applied at an assumed static link: the placement check is
decided at the layout of the binary actually linked.

1. `ret0.s` next to each fixture is `SccCertificate.asm` verbatim (`#eval`
   guard in `Ret0LinkedA64`, `Ret0LinkedX64`, `Ret0LldX64`); the
   certificate's reproducibility guard ties `asm` to scc's output, and
   `Spike/Gen/drift.sh` ties the certificate to the current scc.
2. The links (no linker script in any):
   - AArch64: `clang` (integrated assembler) + `ld.lld` 21.1.8 with
     `run.sh`'s command; the binary exits 42 under `qemu-aarch64`. It has not
     been run natively: no AArch64 host was available.
   - x86-64: GNU `as` 2.47 + `ld -static` 2.47, and GNU `as` + `ld.lld
     -static` 21.1.8; both binaries exit 42 natively.

   `Scc/Test/elf.sh --relink` rebuilds the fixtures with the recorded
   commands; `elf.sh --relink-check` relinks every fixture and compares byte
   for byte.
3. The ELF reader reads `Λe` off the file (`scc_elf_layout%`, fail closed);
   a `#guard elf.2 == …` pins the file's SHA-256 (AArch64 `6087ccf2…`,
   x86-64 GNU `ld` `f202a51e…`, x86-64 `ld.lld` `56c83082…`). Addresses per
   `readelf`:
   - AArch64: `.rodata` ⟨0x2001b8, 0x1b8⟩, with `scc_stackmap` at its
     start, lies **below** the code ⟨0x210370, 0x1298⟩; the build-id note
     sits in the first, read-only `PT_LOAD`.
   - x86-64 `ld.lld`: `.rodata` ⟨0x200158, 0x1b8⟩ below the code
     ⟨0x201310, 0x1238⟩.
   - x86-64 GNU `ld`: the code ⟨0x401000, 0x1238⟩, `.rodata` above it.

   Guarded in the `ld.lld` files: `.rodata` ends at or below the code's
   start; on AArch64 also that the code's start is 16-aligned, and on x86-64
   that a placed symbol lies below the code (not the addresses themselves).
4. The kernel decides `placeOKAt placeCfg Λe out` component by component
   (`decide +kernel`, combined by `placeOKAt_of`), including A1's
   `codeFits` (the code ends inside `.text`) and A2's loader check
   (`Link.A64.loadOk`, `Link.X64.loadOk`: the abort labels, data symbols
   around the code, `noClash`, the code's end below `2 ^ 64`). The guards
   `ret0_codeEnd`/`lld_codeEnd` show the code fills `.text` exactly.
5. `ret0_correct` at `Λe`.

`Scc/Test/certify.sh [--arch arm] --instantiate Scc/Test/ret0.w` performs
steps 1–5 on a fresh build and `run.sh` link (AArch64: `clang` + `ld.lld`;
x86-64: GNU `as` + `ld`) and prints **certified** (§4).

What this chain still trusts is in §3 (the reader, the loader's mapping, the
assembler's encoding vs Kraken's parser and semantics, the evaluated steps).

### Other programs at linked layouts

- **`frame0.w`** (`Spike/Gen/frame0.w`, `def main(u : Unit) : Int = ret 42`:
  no `+`, so a zero-byte frame), x86-64, GNU `ld`
  (`Spike/Test/Frame0LinkedX64.lean`): the code fills `.text`
  (`frame0_codeEnd`) and `placeOKAt` holds at the executable's layout
  (`frame0_placeOKAt`, `#print axioms`: `[propext, Classical.choice,
  Quot.sound]`), each component by `decide +kernel`. The file states no
  correctness theorem; `certify.sh --instantiate` instantiates the compiler
  theorem for it at its `run.sh` link on both ISAs and prints **certified**
  (§4). The x86-64 emitter writes the prologue's `subq $0, %rsp` also at
  frame 0, the form the prologue check expects.
- **`hello1.w`**, AArch64, `ld.lld` (`Spike/Test/Hello1LinkedA64.lean`):
  **uncertified**. It is outside `Accepted0` (it prints; three
  declarations), and at its `ld.lld` layout the placement check fails at A11
  (each by `decide +kernel`: A1–A9 hold, `hello1_a1_9`; the code fills
  `.text`, `hello1_codeFills`; A11 fails, `hello1_a11`, its `.setup` tail;
  so `hello1_not_placeOKAt`). No correctness theorem is stated for it.

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
   `.bss` and the regions in its zero tail; each region non-empty (`region`,
   size ≠ 0); the regions pairwise disjoint (explicit check, and
   `Link.wfB`, which also checks their 16-alignment, the code's included,
   and that every data symbol lies in a data region); no unknown mapped
   section (but the build-id note, item 2), dynamic or relocation section,
   executable stack or overlapping `PT_LOAD`; no data symbol in the code;
   **`e_entry` is the start of `.text`** (where A1 puts `_start`; tested on
   both ISAs' fixtures). It does not check that `.text` is non-empty.
   Trusted: that Linux maps exactly the `PT_LOAD`s with their `p_flags`,
   zero-filling `[p_filesz, p_memsz)`, and starts the thread at `e_entry`;
   the emitter's region symbols `scc_rt_heap`/`scc_rt_pinned`/`scc_rt_stacks`
   (`OBJECT`, sized, last in `.bss`) mark the regions. Not checked by the
   reader: that `.text`'s bytes are the certified program (the placement
   check reads the code from `asm` through `parsesTo`; items 6 and 7).
2. **The linker's build-id note.** `.note.gnu.build-id` (`ld.lld`'s default
   on AArch64) is accepted only as an `SHT_NOTE` section mapped read-only
   (`SHF_ALLOC`, neither `SHF_WRITE` nor `SHF_EXECINSTR`), inside a `PT_LOAD`
   mapped `R` only, from its file bytes, disjoint from the code, `.rodata`,
   `.data`, `.bss` and the regions, with no symbol in or at it
   (`buildIdNote`). It is no part of the layout. Any other unknown mapped
   section is refused. Trusted: that Linux maps the note as its `PT_LOAD`
   says and nothing reads it (scc's code never does). The reader does not
   check the note against the entry stack: that disjointness is part of the
   Linux stack fact (item 3; the kernel places the stack clear of every
   `PT_LOAD`). Negative tests (`Scc/Test/ElfTest.lean`): the note in an
   `R+X` segment, writable, executable, not `SHT_NOTE`, overlapping
   `.rodata`, off its file bytes, outside every `PT_LOAD`, a symbol in its
   section, a symbol of another section at an address inside it, a renamed
   note.
3. **Linux stack facts** (the release statement's entry quantifier,
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
   callee region reaches 296 bytes below `sp`, `EC`). That the quantifier is
   inhabited is a separate, proved fact (`Entry.ok_witness`: a layout ending
   at or below `2 ^ 32` admits the witness `⟨⟨2 ^ 32, 65536⟩⟩`).
4. **Data symbols below the code.** The reader does not refuse a data symbol
   below the code (`refuseBelowCode := false`); one inside the code is
   refused (`Link.containsB code`), and a `.data`/`.bss` symbol below the
   code lies outside every data region and is refused by `wfB` (tested).
   - Trusted behaviour of `T.load`: `Layout.WF.symAbove` (and `wfB`) is
     two-sided, a data symbol is below the code's start or at or above its
     end (`WF.sym_not_code` follows); the loaders' `symsAbove lo fin`
     refuses only symbols *inside* the code; `threadAt` lays out label cells
     of the symbols below the code before it (`placeBelow`, `padTo`, the
     executable starting at `exeStart`) and of the others after it
     (`placeSyms`). The trust is that Linux's loader puts those symbols
     where `placeBelow` does. **Exercised**: `scc_stackmap` is below the
     code in the AArch64 fixture, and `.rodata`'s labels in the x86-64
     `ld.lld` fixture.
   - Untrusted, proved: the placement check's A2 (`Link.A64.loadOk`,
     `Link.X64.loadOk`) checks `symsAround` (every data symbol below the
     code's start or at or above its end, and below `exeStart + 2 ^ 64`,
     with the code's end below it too), `noClash` (no symbol below the code
     named like a code label, which it would shadow; all placed names
     distinct) and that the code ends below `2 ^ 64`. The runtime and
     compiler proofs are generic over the prefix the loader lays out below
     the code (`RuntimeLayout.pfx`).
5. **Evaluated, not kernel-checked, on the chain to each fixture** (each a
   `#guard`/`#eval` or elaboration-time evaluation; their trust is that of
   Lean's compiled evaluator):
   - `hpa`: the certificate's `#guard Scc.Cert.Link.A64.parsesTo asm out.prog
     out.secs` or `#guard Scc.Cert.Link.X64.parsesTo ⟨asm, sizes,
     labelOffs⟩ out.prog out.secs` (the parsers are `partial`); the theorems
     keep it as an explicit premise;
   - `#guard Scc.Cert.Arm.reproduces config source asm` or `#guard
     Scc.Cert.X64.reproduces config source asm` (scc on `source` gives
     `asm`) and `#guard Scc.Cert.SrcTerm.reads source prog_src` (the
     frontend's parse of `source` is `prog_src`), in the certificate;
   - `scc_elf_layout%` (item 1), the reader evaluated by the elaborator;
   - `#guard elf.2 == …`, the pinned SHA-256 of the fixture;
   - the `#eval` guard `ret0.s == asm`.
6. **The artefact and its encoding.**
   - The binary that runs is the fixture file whose SHA-256 is pinned; no
     check ties a deployed binary to it beyond `elf.sh --relink`/
     `--relink-check` and that digest.
   - The assembler encodes each instruction of `asm` as the instruction
     Kraken's parser and ISA semantics read: on AArch64 `clang`'s integrated
     assembler, 4 bytes each; on x86-64 GNU `as`, at the size listed in
     `sizes`. `sizes` and `labelOffs` (read off GNU `as`'s object) are
     checked only for consistency (`sizes_ok`). `.text`'s bytes are never
     decoded or compared with `out.prog`. The reader checks only `.text`'s
     extent, through A1's `codeFits` and the `codeEnd` theorems.
   - Alignment directives in AArch64 `.text` are dropped by Kraken's parser
     (`stripDirectives`); the trust includes that they pad nothing inside
     `.text` (true for 4-byte instructions with `.p2align ≤ 2`, and for the
     `.p2align 4` at offset 0 of `.text`, item 7).
7. **AArch64 `.text` alignment** (scc-side, untrusted). `wfB` requires every
   region, the code included, to be 16-aligned. Without a script, `ld.lld`
   places `.text` right after `.rodata` in the next page with the same page
   offset, rounded up to `.text`'s `sh_addralign`. The emitter opens `.text`
   with `.p2align 4` (`emitPost`): `sh_addralign` 16, so `ld.lld` aligns the
   code whatever precedes it, and it pads nothing (offset 0). With a
   `.p2align 2` header `.text` would start 8 past a 16-byte boundary
   whenever `.rodata` ended there (fail closed, by `wfB`). Regression test
   `Scc/Test/textalign.sh`: links every accepted program with `run.sh`'s
   command and checks `.text` and `e_entry` are 16-aligned (`readelf`), with
   `hello1` and `tailwide` pinned as programs whose `.rodata` ends 8 mod 16.
   x86-64 is unaffected (GNU `ld` page-aligns `.text`; the x86-64 `ld.lld`
   fixture's `.text` is 16-aligned and checked by `wfB`).
8. **The target model's entry**: `target (kernel 1) E` for each admissible
   `E`, not only `Entry.linux`.

The trusted files' documentation states the above: `Scc/Sem/CorrectE.lean`
(the trusted Linux stack fact, separate from the proved witness),
`Scc/Sem/Correct.lean` (`Layout.WF`: data symbols below or above the code),
and `Scc/DESIGN.md` §4 (the loader `T.load` in terms of the layout read off
the executable and the assembler per ISA; the ELF layout reader, with the
build-id note and data symbols below the code; the `Entry.Ok` quantifier,
of which `Entry.linux` is one for a layout ending below it) and its notes on
AArch64 alignment.

## 4. Reproducing

**Building.** `lake build Spike Scc scc scc_x64 scc_arm` and the test
modules. One module, `WeakCore/TermStep.lean`, needs about 6.5 GB of memory
to build even with `LEAN_NUM_THREADS=1` (about 3 minutes), and is killed
under a 4 GB per-process cap, so a build from a fresh checkout needs more
than 4 GB; the next largest, `WeakCore/TermPlant.lean`, needs about 4.2 GB.
Measured on a fresh clone with lake's default parallelism (64 cores):

| Command (fresh clone, nothing built) | Wall time |
|---|---|
| `lake build scc scc_x64 scc_arm` | 37 s (144 jobs) |
| `lake build Spike.Test.Ret0LinkedX64` | 18 min (743 jobs) |
| then `Scc/Test/certify.sh --instantiate Scc/Test/ret0.w` | 52 s, **certified** |

Run on its own on a fresh clone, `certify.sh --arch x64 --instantiate`
builds scc and the certificate modules in about 15 minutes and the compiler
theorem in about 3; `--arch arm` after it, about 4 + 3 minutes. It prints a
line before each build step and appends the build output to
`.lake/certify/ARCH/T/build.log`. Build `Spike.Test.Ret0LinkedA64` and
`Spike.Test.Ret0LinkedX64` first to follow the build directly.
`certify.sh -v` prints every command it runs (`+ cd DIR && CMD`) and the
Lean files it writes, so the run can be repeated by hand.

A parallel build runs several Lean processes at once; to bound their total,
build serially (`LEAN_NUM_THREADS=1`, lake on one CPU, e.g.
`LEAN_NUM_THREADS=1 taskset -c 0 lake build Scc Spike`; about 33 minutes
for the last 242 of 1151 modules, on one core).

**Compiling and running.** From the repository root, with the output in a
temporary directory (`T=$(mktemp -d)`):

```
.lake/build/bin/scc --arch arm -o $T/ret0a.s Scc/Test/ret0.w
clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static \
  -fuse-ld=lld -o $T/ret0a $T/ret0a.s
qemu-aarch64 $T/ret0a; echo $?        # 42
.lake/build/bin/scc --arch x64 -o $T/ret0.s Scc/Test/ret0.w
as -o $T/ret0.o $T/ret0.s && ld -static -o $T/ret0 $T/ret0.o
$T/ret0; echo $?                      # 42
```

**Certifying.** In each case the last line is the verdict, followed by time
and peak RssAnon of the checking Lean process:

| Command | Verdict |
|---|---|
| `Scc/Test/certify.sh --arch arm --instantiate Scc/Test/ret0.w` | **certified** (84 s, 1428 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Scc/Test/ret0.w` | **certified** (82 s, 1306 MB) |
| `Scc/Test/certify.sh --arch arm --instantiate Spike/Gen/frame0.w` | **certified** (94 s, 1418 MB) |
| `Scc/Test/certify.sh --arch x64 --instantiate Spike/Gen/frame0.w` | **certified** (79 s, 1300 MB) |

(Each run serially, under a 4 GB cap, with `LEAN_NUM_THREADS=1`; on an
unloaded machine with parallel threads the `ret0` checks take about 51–53 s.)

**Tests.**

- `#print axioms` over every non-test module reports only `propext`,
  `Classical.choice` and `Quot.sound`.
- `Scc/Test/run.sh`, both ISAs: 48 checks, 40 passed, 0 failed, 8 not
  certifiable; certificates 7 certified, 8 not certifiable.
- `Scc/Test/blocks.sh --check`: 30 passed; `Spike/Gen/drift.sh`: clean;
  `Scc/Test/elf.sh`: ok; `Scc/Test/elf.sh --relink-check`: ok;
  `Scc/Test/textalign.sh`: ok (15 programs).
- `Scc/Test/certify_test.sh`: all passed (8 cases, including `-v`).
- `Kraken/AArch64/Test/asm_tests.py`: 66/66; `Kraken/X64/Test/asm_tests.py`:
  63/63.
- `Scc/Test/diff.sh -n 300`, each ISA: 300/300 agree with the reference
  interpreter, 0 mismatches; a placement sample of 30 generated programs: 25
  certifiable, 5 not, 0 failed.
- The x86-64 fixtures exit 42 natively; the AArch64 fixture exits 42 under
  `qemu-aarch64`.

## 5. Scope and caveats

In this release `ret0.w` has been certified end to end at linked binaries,
with its theorems in the source tree, and `frame0.w` by `certify.sh
--instantiate` at its `run.sh` links (§4). The generic theorems cover
every `Accepted0` program at any layout passing `placeOKAt`, but that is not
a certificate for a given binary until it is instantiated, so scc's output
for any other program is uncertified.

- The compiler theorems cover `Accepted0` (one `main`, straight-line checked
  arithmetic); anything that calls, allocates, prints, spawns or branches is
  uncertified.
- The executable's `.text` bytes are not compared with `asm`'s encoding
  (trusted, §3 item 6).
- Liveness/termination is not claimed (§0).
- **Placement is not complete, even within `Accepted0`.** A program outside
  what `placeOKAt` accepts is refused (fail closed), not certified.
  Certification cost grows with program size. The largest chain of checked
  `+`s (`let x1 = x0 + 1` … `ret xN`) that certifies under 4 GB RssAnon is
  N = 195 on AArch64 and N = 236 on x86-64 (bisection step ±10: 201 and 242
  are killed at the cap). Before this release it was about 130 on AArch64.
- **hello1 is not covered**: outside `Accepted0`, and refused by A11 at its
  `ld.lld` layout (§2). Its certificate exists and `drift.sh` checks it
  against scc's output; it is uncertified.
- **AArch64 tests run under `qemu-aarch64`** by default (`Scc/Test/armrun.sh`,
  `--arm-run qemu|native|auto`). qemu runs the binary, but does not exhibit
  hardware weak-memory reorderings and is not the Linux kernel's ELF loader
  (`qemu-user` has its own); the trusted loader facts of §3 are about Linux
  on hardware. **Not run natively on AArch64 in this release**: no AArch64
  Linux host was available (`--arm-run auto` falls back to qemu; `native` is
  refused on an x86-64 host). x86-64 binaries run natively.
- The single-thread target (`kernel 1`) and `ret0`'s lack of shared memory
  make the memory model immaterial for this program; the statement holds for
  every `arch`.
- **Recursion depth.** Certificates set `maxRecDepth` right after the
  namespace: the reparse of a large asm can exceed the default. Not needed for
  `ret0`; it changes no statement.
- **Runtime counters.** The hand-written runtime proofs (the `ret0` oracle
  layouts, e.g. `Spike/Lib/Rt/X64LayoutOfPlaceOK.lean`'s `ret0P`) use the
  counters at their fixed canonical addresses (`0x600000`, …), kept there,
  16-aligned. These proofs are not on the linked theorems' chains, which read
  every address off `Λe`.
