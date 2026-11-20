# The next raw unit form (sample)

The compiler in this release emits raw units whose routine trampolines jump
through the thread control block's `kabi` word (`stub/runtime_x64.h`,
`SccKabi`). The next compiler release will emit the form described in
`stub/runtime_x64.h` under `SccUnitKabi`: each unit carries its own routine
table in a section `.scc_kabi`, and its trampolines reach their slots
RIP-relative. This directory holds a sample of that form, so that the kernel
side can be written and tested before the compiler emits it.

| File | What it is |
|---|---|
| `hello1rawx64/hello1.s` | `hello1` (`Scc/Test/hello1.w`) in the next raw form, x86-64: the compiler's assembler text |
| `hello1rawx64/hello1` | the same, assembled with GNU `as` and linked with `ld -static -T raw.ld -z max-page-size=65536 -z noexecstack` |
| `raw.ld` | the next release's link script for raw units: as `Scc/Test/elf/raw.ld`, with `.scc_kabi` first in the writable segment |

To reproduce the binary byte for byte, name the object `hello1rawk.o`, as
the compiler's test script did; the linker records the object's file name in
the symbol table:

```sh
as -o hello1rawk.o hello1rawx64/hello1.s
ld -static -T raw.ld -z max-page-size=65536 -z noexecstack -o hello1 hello1rawk.o
```

Its assembler text differs from `Scc/Test/elf/hello1rawx64/hello1.s`, which
the image embeds today, only in the trampolines (one RIP-relative `jmp`
instead of a load of `%fs:96` and a `jmp` through it) and in the table
section added at the end: its user code is the same. Its table holds the
magic, then 14 (the slots it uses), then 14 zero routine words.

When the compiler emits this form, its raw `hello1` must be byte-identical to
`hello1rawx64/hello1`, and this directory is then removed: the sample becomes
the compiler's own fixture.

Nothing here is built into the image yet; `build.sh` still embeds the current
form.
