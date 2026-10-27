#!/usr/bin/env python3
"""Manual smoke test of the EFI stub under QEMU (TCG only, no network).

Usage: runtime/efi/qemu_smoke.py [x64|a64|all] [--wait SECONDS]

Boots .lake/efi/<isa>/esp.img (built by build.sh) as a virtio-blk disk with
QEMU's bundled edk2 firmware, which finds /EFI/BOOT/BOOT*.EFI by the
removable-media rule. After the wait it samples the program counter through
the QEMU monitor. PASS means: the stub's banner appeared on the serial
console, nothing followed it (boot services gone), and the CPU sits in the
stub's halt loop (PC stable across samples, at a `hlt` / `wfi`).

Not part of the Lean build, the merge gates or Scc/Test: a manual check.
Policy: `-accel tcg`
only, run inside `unshare -rn` (no network interfaces), `-nodefaults -nic
none`, no host directories or files exposed to the guest except our image.

QEMU binaries and firmware: $KRAKEN_QEMU_DIR (required; the directory holding
qemu-system-x86_64 and qemu-system-aarch64, tested with QEMU 11.0.5); x86-64 firmware from
.lake/efi/fw (edk2-x86_64-code.fd and edk2-i386-vars.fd, decompressed from
QEMU's pc-bios/), aarch64 firmware from $KRAKEN_QEMU_DIR/fw.
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
QDIR = os.environ.get("KRAKEN_QEMU_DIR", "")
EFI = os.path.join(ROOT, ".lake", "efi")
BANNER = "kraken efi stub: exiting boot services"


def cmdline(isa, tmp, mon):
    img = os.path.join(EFI, isa, "esp.img")
    common = ["-nodefaults", "-nic", "none", "-accel", "tcg", "-display", "none",
              "-serial", "file:" + os.path.join(tmp, "serial.txt"), "-m", "256M",
              "-no-user-config", "-monitor", "unix:%s,server,nowait" % mon,
              "-drive", "if=none,id=esp,format=raw,snapshot=on,file=" + img,
              "-device", "virtio-blk-pci,drive=esp"]
    if isa == "x64":
        vars_copy = os.path.join(tmp, "vars.fd")
        shutil.copy(os.path.join(EFI, "fw", "edk2-i386-vars.fd"), vars_copy)
        return [os.path.join(QDIR, "qemu-system-x86_64"), "-M", "q35", "-cpu", "qemu64",
                "-drive", "if=pflash,format=raw,readonly=on,file=" +
                os.path.join(EFI, "fw", "edk2-x86_64-code.fd"),
                "-drive", "if=pflash,format=raw,file=" + vars_copy] + common
    return [os.path.join(QDIR, "qemu-system-aarch64"), "-M", "virt", "-cpu", "max",
            "-bios", os.path.join(QDIR, "fw", "edk2-aarch64-code.fd")] + common


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


def run(isa, wait):
    tmp = tempfile.mkdtemp(prefix="kraken-efi-")
    mon = os.path.join(tmp, "mon.sock")
    argv = ["unshare", "-rn"] + cmdline(isa, tmp, mon)
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
        for _ in range(4):
            pcs.append(pc_of(monitor(mon, ["info registers"])[0], isa))
            time.sleep(0.5)
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
    # QEMU here has no disassembler: look for the instruction bytes just
    # before the PC (x86 `hlt` = f4 at pc-1; AArch64 `wfi` = d503207f at pc-4
    # or at pc while it is about to execute it).
    bs = [int(b, 16) for b in re.findall(r"0x([0-9a-f]{2})\b", dis.split(":", 1)[-1])]
    if isa == "x64":
        at_halt = len(bs) >= 4 and bs[3] == 0xF4
    else:
        wfi = [0x7F, 0x20, 0x03, 0xD5]
        at_halt = bs[0:4] == wfi or bs[4:8] == wfi
    ok = i >= 0 and after == "" and stable and at_halt
    print("%s: %s (banner %s; output after banner %r; pc samples %s; halt insn %s)" % (
        isa, "PASS" if ok else "FAIL", "seen" if i >= 0 else "MISSING", after[:200],
        ",".join("?" if p is None else hex(p) for p in pcs), "seen" if at_halt else "NOT seen"))
    if not at_halt:
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
