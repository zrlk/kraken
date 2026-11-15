"""gdb support for the Kraken EFI stub's debug image (DEBUG=1 runtime/efi/build.sh).

The firmware loads the stub at an address it picks, and the debug stub spins
in debug_wait until kraken_debug_wait is cleared. `kraken-attach` starts
runtime/efi/qemu_window.sh --gdb (which rebuilds the debug image if it is out
of date) and waits for the stub's "waiting for debugger" line, unless
--no-launch says a QEMU is already running; then connects to QEMU's gdb
server unless gdb is connected already, finds the CPU spinning in
debug_wait, loads the stub's symbols at the image's load address, selects
that CPU, clears the flag and sets a temporary breakpoint where debug_wait
returns. The CPUs stay stopped. A QEMU that kraken-attach started is closed
when gdb exits (VS Code: when debugging stops); its serial output is in
.lake/efi/qemu-<isa>-debug.log.

Usage (gdb):  source runtime/efi/gdb/kraken.py
              kraken-attach [--no-launch] [x64|a64]    (default x64)
Server: $KRAKEN_GDB_HOST (default: on macOS, localhost; from WSL, the default
gateway, which is the Windows host QEMU runs on) and $KRAKEN_GDB_PORT (default
1234). On macOS gdb must read PE: Homebrew's gdb does, x86_64-elf-gdb does not.
"""
import atexit
import os
import subprocess
import sys
import time

import gdb

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
PAGE = 0x1000  # the firmware loads images page-aligned, as the linker placed them


def default_host():
    if sys.platform == "darwin":
        return "localhost"
    words = subprocess.run(["ip", "route", "show", "default"], capture_output=True,
                           text=True, check=True).stdout.split()
    return words[words.index("via") + 1]


def u64(expr):
    return int(gdb.parse_and_eval("(unsigned long long)(%s)" % expr))


qemu = None  # the qemu_window.sh process kraken-attach started, if any


def stop_qemu():
    global qemu
    if qemu is not None and qemu.poll() is None:
        qemu.terminate()  # from WSL, through interop, this closes the Windows QEMU too
        try:
            qemu.wait(10)
        except subprocess.TimeoutExpired:
            qemu.kill()
    qemu = None


atexit.register(stop_qemu)


def launch_qemu(isa):
    """Starts qemu_window.sh --gdb ISA and waits until the stub waits for us."""
    global qemu
    stop_qemu()
    log = os.path.join(ROOT, ".lake", "efi", "qemu-%s-debug.log" % isa)
    os.makedirs(os.path.dirname(log), exist_ok=True)
    with open(log, "w") as out:
        qemu = subprocess.Popen([os.path.join(ROOT, "runtime", "efi", "qemu_window.sh"), "--gdb", isa],
                                stdin=subprocess.DEVNULL, stdout=out, stderr=subprocess.STDOUT,
                                start_new_session=True)
    end = time.time() + 180  # includes a rebuild of the debug image
    while time.time() < end:
        text = open(log, errors="replace").read()
        if "waiting for debugger" in text:
            return
        if qemu.poll() is not None:
            raise gdb.GdbError("kraken-attach: qemu_window.sh exited (%d):\n%s"
                               % (qemu.returncode, text[-2000:]))
        time.sleep(0.5)
    stop_qemu()
    raise gdb.GdbError("kraken-attach: the stub did not reach debug_wait in 180 s; see " + log)


def function_range(addr):
    b = gdb.block_for_pc(addr)
    while b.function is None:
        b = b.superblock
    return b.start, b.end


class KrakenAttach(gdb.Command):
    """Attach to the Kraken EFI debug stub: kraken-attach [--no-launch] [x64|a64]."""

    def __init__(self):
        super().__init__("kraken-attach", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        args = arg.split()
        launch = "--no-launch" not in args
        args = [a for a in args if a != "--no-launch"]
        isa = args[0] if args else "x64"
        inf = gdb.selected_inferior()
        if launch and not inf.threads():
            launch_qemu(isa)
        stub = os.path.join(ROOT, ".lake", "efi", isa + "-debug", "stub.efi")
        if not os.path.exists(stub):
            raise gdb.GdbError("no %s: run DEBUG=1 runtime/efi/build.sh %s" % (stub, isa))
        gdb.execute("set confirm off")
        gdb.execute("set pagination off")
        gdb.execute("symbol-file %s" % stub)  # at the linker's addresses, to find debug_wait
        lo, hi = function_range(u64("debug_wait"))
        flag = u64("&kraken_debug_wait")

        if not inf.threads():
            host = os.environ.get("KRAKEN_GDB_HOST") or default_host()
            gdb.execute("target remote %s:%s" % (host, os.environ.get("KRAKEN_GDB_PORT", "1234")))

        found = []
        for t in inf.threads():
            t.switch()
            pc = u64("$pc")
            delta = (pc - lo) // PAGE * PAGE
            if lo <= pc - delta < hi and u64("*(unsigned int *)%d" % (flag + delta)) == 1:
                found.append((t, delta))
        if len(found) != 1:
            raise gdb.GdbError("kraken-attach: %d CPUs in debug_wait (want 1): is the debug "
                               "image booted and past the banner?" % len(found))
        t, delta = found[0]
        t.switch()
        gdb.execute("symbol-file -o %#x %s" % (delta % (1 << 64), stub))
        gdb.execute("set var kraken_debug_wait = 0")
        # Stop in efi_main as debug_wait returns, so that continuing without
        # a breakpoint (VS Code resumes after attaching) does not run the stub
        # to its halt.
        ret = gdb.newest_frame().older().pc()
        gdb.execute("tbreak *%#x" % ret, to_string=True)
        print("kraken-attach: stub loaded at offset %#x from its link address (gdb thread %d), "
              "released from debug_wait; continuing stops in efi_main after debug_wait"
              % (delta, t.num))


KrakenAttach()
