#!/usr/bin/env python3
"""Manual smoke test of the EFI stub under QEMU (TCG only, no network).

Usage: runtime/efi/qemu_smoke.py [x64|a64|all] [--wait SECONDS]

Boots .lake/efi/<isa>/esp.img (built by build.sh) as a virtio-blk disk with
QEMU's bundled edk2 firmware, which finds /EFI/BOOT/BOOT*.EFI by the
removable-media rule. The machine has what the stub requires: a display with
a linear framebuffer (InitVideo), and on x64 an IOMMU, for the ACPI DMAR table,
and 4 CPUs, as in qemu_window.sh, with -cpu max (EnterRuntime needs XSAVE).
After the wait it samples the boot CPU's program counter through the QEMU
monitor. PASS means: the stub's banner appeared on the serial console, what
followed it is what the stub prints after boot services are gone (a64:
nothing; x64: the APs' startup, ending with all CPUs online, EnterRuntime,
CpuEntryPoint's "BSP entry point", then hello1's "Hello, world" and its exit
status 0), and the CPU is where the stub leaves it:
- a64: in the halt loop (PC stable across samples, at a `wfi`);
- x64: idle, with the APIC timer re-armed on every interrupt, so a sample
  may land in the idle loop's `hlt` or in the interrupt path. Every sample
  must be inside the stub's image (the load address the stub prints, and
  SizeOfImage from stub.efi), and the CPU must not be stuck: samples all at
  one PC must be at a `hlt`. A fault parks it on `jmp $` in isr_stub
  (entry.asm), and a return to the firmware leaves the image; both FAIL.

Not part of the Lean build, the merge gates or Scc/Test: a manual check.
Policy: `-accel tcg`
only, run inside `unshare -rn` (no network interfaces; macOS has no unshare, so
there only `-nic none` keeps the guest off the network), `-nodefaults -nic
none`, no host directories or files exposed to the guest except our image.

QEMU binaries and firmware: $KRAKEN_QEMU_DIR (required on Linux; the directory
holding qemu-system-x86_64 and qemu-system-aarch64, tested with QEMU 11.0.5); x86-64 firmware from
.lake/efi/fw (edk2-x86_64-code.fd and edk2-i386-vars.fd, decompressed from
QEMU's pc-bios/), aarch64 firmware from $KRAKEN_QEMU_DIR/fw. QEMU's option
ROMs (vgabios-stdvga.bin, kvmvapic.bin, ...) are looked up in
$KRAKEN_QEMU_DIR/fw too (`-L`), for a QEMU that is not installed in its
configured prefix. On macOS, $KRAKEN_QEMU_DIR defaults to where the PATH finds
QEMU (brew install qemu), both firmwares come from share/qemu next to it, and
QEMU finds its ROMs itself.
"""
import os
import re
import shutil
import socket
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MACOS = sys.platform == "darwin"
QDIR = os.environ.get("KRAKEN_QEMU_DIR", "")
if MACOS and not QDIR:
    QDIR = os.path.dirname(shutil.which("qemu-system-x86_64") or "")
EFI = os.path.join(ROOT, ".lake", "efi")
FW_X64 = os.path.join(QDIR, "..", "share", "qemu") if MACOS else os.path.join(EFI, "fw")
FW_A64 = os.path.join(QDIR, "..", "share", "qemu") if MACOS else os.path.join(QDIR, "fw")
BANNER = "kraken efi stub: exiting boot services"
# What must end the serial output after the banner, by ISA. x64: the APs
# started, then EnterRuntime (entry.asm) reaches CpuEntryPoint on the BSP,
# which runs Hello1Raw (scc's raw hello1) on a thread: it prints its line
# through scc_rt_print and ends with scc_rt_exit_process(0), which halts.
X64_CPUS = 4
AFTER_BANNER = {"x64": r"\b%d total CPUs online\s+EnterRuntime\(\) on BSP\s*BSP entry point\s+"
           r"Hello, world\s+scc_rt_exit_process: status 0$" % X64_CPUS, "a64": r"^$"}


def cmdline(isa, tmp, mon):
    img = os.path.join(EFI, isa, "esp.img")
    # Linux: QEMU's data directory for option ROMs (macOS: QEMU's own default).
    roms = [] if MACOS else ["-L", os.path.join(QDIR, "fw")]
    common = roms + ["-nodefaults", "-nic", "none", "-accel", "tcg", "-display", "none",
              "-serial", "file:" + os.path.join(tmp, "serial.txt"), "-m", "256M",
              "-no-user-config", "-monitor", "unix:%s,server,nowait" % mon,
              "-drive", "if=none,id=esp,format=raw,snapshot=on,file=" + img,
              "-device", "virtio-blk-pci,drive=esp"]
    if isa == "x64":
        vars_copy = os.path.join(tmp, "vars.fd")
        shutil.copy(os.path.join(FW_X64, "edk2-i386-vars.fd"), vars_copy)
        return [os.path.join(QDIR, "qemu-system-x86_64"), "-M", "q35", "-cpu", "max",
                "-smp", str(X64_CPUS),
                # Before the other PCI devices, as QEMU wants.
                "-device", "intel-iommu", "-device", "VGA",
                "-drive", "if=pflash,format=raw,readonly=on,file=" +
                os.path.join(FW_X64, "edk2-x86_64-code.fd"),
                "-drive", "if=pflash,format=raw,file=" + vars_copy] + common
    return [os.path.join(QDIR, "qemu-system-aarch64"), "-M", "virt", "-cpu", "max",
            "-bios", os.path.join(FW_A64, "edk2-aarch64-code.fd"), "-device", "ramfb"] + common


def monitor(path, cmds):
    """Runs HMP commands; returns their outputs (echo stripped)."""
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.connect(path)
    s.settimeout(10)
    buf = b""
    def read_prompt():
        nonlocal buf
        while b"(qemu) " not in buf:
            buf += s.recv(65536)
        out, buf = buf.split(b"(qemu) ", 1)
        return re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", out.decode(errors="replace"))
    read_prompt()
    outs = []
    for cmd in cmds:
        s.sendall(cmd.encode() + b"\n")
        out = read_prompt()
        outs.append(out.split("\n", 1)[1] if "\n" in out else out)
    s.close()
    return outs


def pc_of(regs, isa):
    m = re.search(r"RIP=([0-9a-f]+)" if isa == "x64" else r"PC=([0-9a-f]+)", regs)
    return int(m.group(1), 16) if m else None


def image_range(serial):
    """The x64 stub's [base, end) at run time: the load address it prints
    (CheckLoadedBelow4G) and SizeOfImage from its PE optional header."""
    m = re.search(r"the stub is loaded at ([0-9a-fA-F]+)", serial)
    if not m:
        return None
    pe = open(os.path.join(EFI, "x64", "stub.efi"), "rb").read()
    e = int.from_bytes(pe[0x3C:0x40], "little")
    size = int.from_bytes(pe[e + 24 + 56:e + 24 + 60], "little")
    base = int(m.group(1), 16)
    return base, base + size


def run(isa, wait):
    tmp = tempfile.mkdtemp(prefix="kraken-efi-")
    mon = os.path.join(tmp, "mon.sock")
    argv = ([] if MACOS else ["unshare", "-rn"]) + cmdline(isa, tmp, mon)
    p = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    try:
        for _ in range(100):
            if os.path.exists(mon) or p.poll() is not None:
                break
            time.sleep(0.1)
        time.sleep(wait)
        if p.poll() is not None:
            print("%s: FAIL (QEMU exited with %d)\n%s" % (isa, p.returncode, p.stdout.read().decode()))
            return False
        pcs = []
        for _ in range(8 if isa == "x64" else 4):
            pcs.append(pc_of(monitor(mon, ["info registers"])[0], isa))
            time.sleep(0.3 if isa == "x64" else 0.5)
        dis = ""
        if None not in pcs:
            dis = monitor(mon, ["x /8xb 0x%x" % (min(pcs) - 4)])[0]
        serial = open(os.path.join(tmp, "serial.txt"), errors="replace").read()
    finally:
        if p.poll() is None:
            p.kill()
        p.wait()
    i = serial.find(BANNER)
    after = serial[i + len(BANNER):].strip() if i >= 0 else ""
    stable = None not in pcs and max(pcs) - min(pcs) <= 8
    rng = image_range(serial) if isa == "x64" else None
    in_image = rng is not None and None not in pcs and all(rng[0] <= pc < rng[1] for pc in pcs)
    # QEMU here has no disassembler: look for the instruction bytes just
    # before the PC (x86 `hlt` = f4 at pc-1; AArch64 `wfi` = d503207f at pc-4
    # or at pc while it is about to execute it).
    bs = [int(b, 16) for b in re.findall(r"0x([0-9a-f]{2})\b", dis.split(":", 1)[-1])]
    if isa == "x64":
        at_halt = len(bs) >= 4 and bs[3] == 0xF4
        # Moving between samples is the timer at work; stuck must be at hlt.
        idle = in_image and (not stable or at_halt)
    else:
        wfi = [0x7F, 0x20, 0x03, 0xD5]
        at_halt = bs[0:4] == wfi or bs[4:8] == wfi
    if isa == "x64":
        state = ("outside the stub's image %s" % ("[%#x, %#x)" % rng if rng else "(load address not printed)")
                 if not in_image else "stuck, not at a hlt" if not idle
                 else "idle at hlt" if stable else "servicing interrupts / idle")
        cpu_ok = idle
    else:
        state = "halt insn " + ("seen" if at_halt else "NOT seen")
        cpu_ok = stable and at_halt
    ok = i >= 0 and re.search(AFTER_BANNER[isa], after) is not None and cpu_ok
    print("%s: %s (banner %s; output after banner ends %r; pc samples %s; %s)" % (
        isa, "PASS" if ok else "FAIL", "seen" if i >= 0 else "MISSING", after[-60:],
        ",".join("?" if p is None else hex(p) for p in pcs), state))
    if not cpu_ok and dis:
        print("--- bytes from pc-4 ---\n" + dis)
    if not ok:
        print("--- serial (tail) ---\n" + serial[-2000:])
    shutil.rmtree(tmp, ignore_errors=True)
    return ok


def main():
    if not QDIR:
        sys.exit("qemu_smoke: set KRAKEN_QEMU_DIR to the directory holding "
                 "qemu-system-x86_64, qemu-system-aarch64 and fw/edk2-aarch64-code.fd")
    args = sys.argv[1:]
    wait = 20.0
    if "--wait" in args:
        k = args.index("--wait")
        wait = float(args[k + 1])
        del args[k:k + 2]
    which = args[0] if args else "all"
    isas = ["x64", "a64"] if which == "all" else [which]
    ok = all([run(i, wait) for i in isas])
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
