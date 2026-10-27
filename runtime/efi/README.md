# EFI runtime (manual path)

The starting point for Kraken's raw runtime as a UEFI application on x86-64
and AArch64. Today it holds only a stub that prints one line, calls
`ExitBootServices` and halts.

This directory is **not** part of the Lean build, the merge gates or
`Scc/Test`. The certified tests keep running as Linux ELF binaries (x86-64
native, AArch64 under `qemu-aarch64`); nothing here boots a full system on
that path.

## Files

| File | What it is |
|---|---|
| `stub/stub.c` | the stub: banner on the firmware console, GetMemoryMap + ExitBootServices (retrying on a changed map key), then the halt loop |
| `stub/halt_x64.asm` | the x64 halt loop, NASM syntax: `cli`, then `hlt` / `jmp` back forever. AArch64 keeps an inline `msr daifset; wfi` loop (NASM has no AArch64 target) |
| `build.sh` | builds `.lake/efi/{x64,a64}/stub.efi` with clang + lld-link (PE32+, subsystem EFI application) and a FAT16 `esp.img` per ISA |
| `mkesp.py` | writes the `esp.img`: `/EFI/BOOT/BOOTX64.EFI` or `BOOTAA64.EFI` on a bare FAT16 filesystem |
| `qemu_smoke.py` | boots `esp.img` under QEMU's bundled edk2 firmware, TCG only, inside `unshare -rn`; PASS = banner seen, no output after it, PC parked on the halt instruction |

Headers come from `third_party/gnu-efi/inc` (BSD; see its `VENDOR.md`). No
gnu-efi library or glue code is linked.

## Use

```sh
runtime/efi/build.sh                 # both ISAs; needs clang, lld-link, nasm (x64)
runtime/efi/qemu_smoke.py            # both ISAs; ~25 s each under TCG
```

On hardware: write `.lake/efi/x64/esp.img` to a USB stick
(`dd if=.lake/efi/x64/esp.img of=/dev/sdX bs=1M conv=fsync`) and boot it
from the firmware's boot menu. Expected: the banner on screen, then the
machine stays halted (no return to the boot menu). If a machine refuses the
partitionless image, copy `stub.efi` to `EFI/BOOT/BOOTX64.EFI` on a GPT ESP.

## QEMU firmware

`qemu_smoke.py` uses the QEMU binaries in `$KRAKEN_QEMU_DIR` (required; it
exits with an error if unset). x86-64 needs
`edk2-x86_64-code.fd` and `edk2-i386-vars.fd` in `.lake/efi/fw/` (gitignored),
decompressed from QEMU's `pc-bios/*.fd.bz2`; AArch64 uses
`$KRAKEN_QEMU_DIR/fw/edk2-aarch64-code.fd`. No firmware is checked into this repository.
