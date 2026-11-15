# EFI runtime (manual path)

The starting point for Kraken's raw runtime as a UEFI application on x86-64
and AArch64. On x86-64 the stub exits boot services, sets up paging, its
descriptor tables and the local APICs, starts the other CPUs, and runs scc's
raw-host `hello1` (`Scc/Test/elf/hello1rawx64/hello1`, embedded in the image)
on one thread on the boot CPU, which prints `Hello, world` and halts. On
AArch64 it prints its banner, exits boot services and halts.

**Status: an unverified preview.** Nothing here is covered by any
correctness statements; it is ordinary C++ and assembly, tested only by
`qemu_smoke.py` and by booting it. Of the 14 kernel routines a raw unit calls
(`SccKabiSlot`), 3 are implemented (`scc_rt_alloc`, `scc_rt_print`,
`scc_rt_exit_process`); the other 11 stop the machine with a panic message, so
only raw units that use those 3 (such as `hello1`) run. There is one thread,
on the boot CPU; the other CPUs start and idle.

This directory is **not** part of the Lean build, the merge gates or
`Scc/Test`. The certified tests keep running as Linux ELF binaries (x86-64
native, AArch64 under `qemu-aarch64`); nothing here boots a full system on
that path.

## Files

| File | What it is |
|---|---|
| `stub/stub.cc` | the stub's ISA-independent part, freestanding C++ (no exceptions, RTTI or runtime library): the font tables embedded as `FontData` (`.incbin`, about 3.8 MB) with `GetBitsForCharacter` to look glyphs up (checked at startup: a warning if the font has no `'?'`), banner on the firmware console, GetMemoryMap + ExitBootServices (retrying on a changed map key), then the halt loop |
| `stub/stub_x64.cc`, `stub/stub_a64.cc` | the per-ISA parts (`build.sh` compiles the image's one): `InitPlatform` (x64: TSC calibration from CPUID, the PIT or `Stall`), `halt_forever`, and on x64 the embedded AP startup code (`ApBootstrap`) and the raw-host `hello1` executable (`Hello1Raw`..`Hello1RawEnd`: `Scc/Test/elf/hello1rawx64/hello1` byte for byte, 16 KiB aligned), which `CpuEntryPoint` runs on a thread on the boot CPU (`Hello1RawEntry`, `AllocThread`, `EnterThread`) |
| `stub/stub.h` | what they share: `InitPlatform`, `halt_forever`, and `debug.h` |
| `stub/debug.h`, `stub/debug.cc` | debugging aids for every file of the stub: `EFIConOut`, `DV`, `cpu_relax`, and in debug images the debugger wait (`debug_wait`, `kraken_debug_wait`) that `kraken-attach` finds by name |
| `stub/x64.h` | x86-64 helpers: port I/O (`inb`, `outb`), `rdtsc`, control registers (`readcr0`, `writecr0`, `readcr3`), `<cpuid.h>`, and local APIC and descriptor-table definitions |
| `stub/runtime_x64.h`, `stub/runtime_x64.cc` | the host side of scc's raw ABI (`scc --host raw`, `Scc/Lower/Raw.lean`), for raw units such as `Hello1Raw`: the TCB (`SccTcb`: scc's fields and argument words, offsets checked against `Scc/IR/Core.lean`, then the kernel's saved registers and XSAVE area), the kernel routine table and its slots (`SccKabi`, `SccKabiSlot`, `gKabi`), `KRAKEN_SCC_ABI` (System V, which raw units use, where the stub defaults to the Microsoft convention), and `AllocThread`/`EnterThread`; built into the x64 image |
| `stub/x64_mmu.h`, `stub/x64_mmu.cc` | x86-64 paging: the page-table entry types, `GetRootPageTable`, `DisableWriteProtection` (`x64_mmu.cc` is built into the x64 image) |
| `stub/entry.asm` | x64, NASM syntax: `EnterRuntime` (each CPU's switch to the stub's own descriptor tables and stack, enabling SSE, AVX and XSAVE, then `CpuEntryPoint`), the idle loop, the interrupt entry stubs, and `kraken_halt` (`cli`, then `hlt` / `jmp` back forever). AArch64 keeps an inline `msr daifset; wfi` loop (NASM has no AArch64 target) |
| `stub/runtime.asm` | the x64 runtime's assembler routines (NASM syntax), the host side of scc's raw ABI with `runtime_x64.h` and `runtime_x64.cc`; assembled with `nasm -f win64` and linked into the x64 image like `entry.asm`. Its header notes the two calling conventions in play (Microsoft for the stub's C++, System V for raw units and `KRAKEN_SCC_ABI`). It holds `RuntimeEnterThread`, which loads a thread's saved state from its TCB and enters it |
| `stub/ap_entry.asm` | startup code for the other CPUs (APs): flat binary at 0x8000, real mode to protected mode to long mode, then a jump to a kernel entry address it is given. `build.sh` assembles it with NASM `-f bin` and `stub_x64.cc` embeds it (`.incbin`) as `ApBootstrap`..`ApBootstrapEnd`; `SetupBootstrap` copies it to the bootstrap page (`gApBootstrapAddress`) and `WakeupAPs` starts the APs there |
| `build.sh` | builds `.lake/efi/{x64,a64}/stub.efi` with clang + lld-link (PE32+, subsystem EFI application) and a FAT16 `esp.img` per ISA |
| `generate_font.cc` | host tool: reads a GNU Unifont `.hex` font on standard input and writes the font tables (`build.sh` pipes in the gunzipped `stub/unifont_all-17.0.05.hex.gz`, giving `.lake/efi/font/offsets.bin` and `bits.bin`); the format is in its header comment |
| `mkesp.py` | writes the `esp.img`: `/EFI/BOOT/BOOTX64.EFI` or `BOOTAA64.EFI` on a bare FAT16 filesystem |
| `qemu_smoke.py` | boots `esp.img` under QEMU's bundled edk2 firmware, TCG only, inside `unshare -rn`; PASS = banner seen, then only the expected output (a64: none; x64, under `-cpu max`: AP startup, all 4 CPUs online, `EnterRuntime`, `BSP entry point`, then the raw `hello1`'s `Hello, world` and `scc_rt_exit_process: status 0`), then the CPU idle: a64 parked on `wfi`; x64, whose APIC timer keeps firing, inside the stub and either at its `hlt` or moving through the interrupt path (stuck anywhere else, as on a fault, fails) |
| `qemu_window.sh` | boots `esp.img` with a display window (x64: 4 CPUs) in the Windows QEMU from WSL, or the native QEMU on macOS, rebuilding the image first when it is missing or out of date; `--gdb` boots the debug image with QEMU's gdb server open |
| `run_nodebug.sh` | a program for an editor's "run without debugging" configuration: `qemu_window.sh` (the release image) in a child process, so that gdb does not trace it when the editor runs it under gdb, and closing QEMU when the session ends, even on SIGKILL |
| `gdb/kraken.py` | gdb command `kraken-attach`: finds the debug stub, loads its symbols at its load address, releases it |

Headers come from `third_party/gnu-efi/inc` (BSD; see its `VENDOR.md`). No
gnu-efi library or glue code is linked.

## Use

The font is not part of this repository: put the file named in
`stub/font.note` (GNU Unifont, `unifont_all-17.0.05.hex.gz`) in `stub/`;
`build.sh` checks it against the SHA-256 in that note and stops if it is
missing or different.

```sh
runtime/efi/build.sh                 # both ISAs; needs clang, lld-link, nasm (x64), mkfs.fat
runtime/efi/qemu_smoke.py            # both ISAs; ~25 s each under TCG
runtime/efi/build.sh compdb          # only .lake/efi/compile_commands.json; needs clang++, python3
```

On macOS, with Xcode's clang: `brew install lld nasm dosfstools qemu gdb`.

On hardware: write `.lake/efi/x64/esp.img` to a USB stick
(`dd if=.lake/efi/x64/esp.img of=/dev/sdX bs=1M conv=fsync`) and boot it
from the firmware's boot menu. Expected on x86-64: the banner, the CPU
count, `Hello, world` and `scc_rt_exit_process: status 0` on screen, then
the machine stays halted (no return to the boot menu). If a machine refuses the
partitionless image, copy `stub.efi` to `EFI/BOOT/BOOTX64.EFI` on a GPT ESP.

## Serial output

Before `ExitBootServices` the stub writes through the firmware console,
which the firmware mirrors to COM1. After it, on x86-64, the stub draws text
on the framebuffer itself and echoes it to COM1 (`debug.cc`: ASCII as is,
`?` for other characters). On AArch64 nothing is written after the banner.

| Path | Serial output |
|---|---|
| `qemu_window.sh`, the "run in QEMU" task, VS Code's "run" configuration | the terminal it runs in (`-serial stdio`) |
| `kraken-attach`, VS Code's "debug" configuration | `.lake/efi/qemu-<isa>-debug.log` |
| `qemu_smoke.py` | a temporary file the script checks and deletes; its tail is printed on FAIL |
| hardware | the screen; COM1 before `ExitBootServices` only if the machine's firmware mirrors its console there |

## Debugging (x64, Windows QEMU, gdb in WSL)

The debug image (`DEBUG=1 runtime/efi/build.sh x64`: `.lake/efi/x64-debug/`,
-O0, DWARF in the PE) prints `kraken efi stub: waiting for debugger` and spins
in `debug_wait`. From the repository root, in gdb:

```
gdb -ex 'source runtime/efi/gdb/kraken.py' -ex 'kraken-attach x64'
```

`kraken-attach` runs `qemu_window.sh --gdb` (which rebuilds the debug image
if it is out of date; serial output in `.lake/efi/qemu-x64-debug.log`) and
waits for the stub, or with `--no-launch` uses a QEMU already started that
way. It connects to the Windows host at WSL's default gateway, finds the CPU
in `debug_wait`, loads the symbols at the stub's load address (the firmware
picks it) and releases the stub with all CPUs stopped, with a temporary
breakpoint in `efi_main` where `debug_wait` returns: continuing stops there,
and breakpoints set earlier hit as usual. The QEMU it started closes when gdb
exits.

Editor launch configurations are not checked in. A debug configuration can
run the gdb command above; `build.sh` writes `.lake/efi/compile_commands.json`
for C/C++ tooling, and `run_nodebug.sh x64` is the program for running the
release image without a debugger.

From WSL, QEMU runs on
Windows, so Windows Firewall must allow inbound TCP 1234 on the
`vEthernet (WSL)` interface, and no Block rule for `qemu-system-x86_64.exe`
may cover the Public profile (WSL's network is Public; a Block rule wins over
any Allow).

## Debugging on macOS

QEMU runs natively, under TCG on Apple silicon, with its gdb server on
localhost, so there is no firewall to set up. The `gdb` command and `kraken-attach`
are as above, with Homebrew's `gdb`: it reads the PE stub, which `x86_64-elf-gdb`
does not. It needs no codesigning, because it only talks to QEMU's gdb server.

An editor's debug configuration works as above; to run the release image
without a debugger, use `run_nodebug.sh x64` directly, because gdb cannot
start a local program without codesigning.

## QEMU firmware

`qemu_smoke.py` uses the QEMU binaries in `$KRAKEN_QEMU_DIR` (required; it
exits with an error if unset). x86-64 needs
`edk2-x86_64-code.fd` and `edk2-i386-vars.fd` in `.lake/efi/fw/` (gitignored),
decompressed from QEMU's `pc-bios/*.fd.bz2`; AArch64 uses
`$KRAKEN_QEMU_DIR/fw/edk2-aarch64-code.fd`. On macOS `$KRAKEN_QEMU_DIR` is optional
(default: where the `PATH` finds QEMU), both firmwares come from `share/qemu` next
to it, and the script runs without `unshare`, which macOS lacks; only `-nic none`
then keeps the guest off the network. No firmware is checked into this repository.
