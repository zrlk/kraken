#!/usr/bin/env bash
# Platform facts for the write-combining design (HB-10, HB-11). Read-only.
#
# Usage: sudo ./platform.sh [OUTDIR]
#
# HB-10: the MTRRs and the PAT, as the firmware and the kernel left them, on
# every CPU: IA32_MTRRCAP (0xfe), IA32_MTRR_DEF_TYPE (0x2ff), the variable
# MTRR pairs (0x200 on), the fixed MTRRs (0x250, 0x258, 0x259, 0x268-0x26f)
# and IA32_PAT (0x277), read through /dev/cpu/N/msr; also /proc/mtrr and the
# kernel's PAT memtype list.
# HB-11: where the firmware framebuffer is: /proc/iomem, the boot
# framebuffer lines of dmesg, the screen_info the kernel kept, and the
# graphics function's BARs.
#
# Loads the msr module if needed (read-only use). Writes nothing else.
set -u
[ "$(id -u)" -eq 0 ] || { echo "platform.sh: run as root" >&2; exit 1; }
OUT=${1:-platform-$(date -u +%Y%m%d-%H%M%S)}
mkdir -p "$OUT" || exit 1

[ -e /dev/cpu/0/msr ] || modprobe msr 2>"$OUT/msr-modprobe.err"
python3 - "$OUT/msr.txt" <<'EOF'
import glob, os, struct, sys
regs = [0xfe, 0x2ff] + list(range(0x200, 0x200 + 2 * 10)) + \
       [0x250, 0x258, 0x259] + list(range(0x268, 0x270)) + [0x277]
names = {0xfe: "MTRRCAP", 0x2ff: "MTRR_DEF_TYPE", 0x277: "PAT",
         0x250: "FIX64K_00000", 0x258: "FIX16K_80000", 0x259: "FIX16K_A0000"}
for i in range(8):
    names[0x268 + i] = "FIX4K_%05X" % (0xC0000 + i * 0x8000)
for i in range(10):
    names[0x200 + 2 * i] = "PHYSBASE%d" % i
    names[0x201 + 2 * i] = "PHYSMASK%d" % i
cpus = sorted(glob.glob("/dev/cpu/[0-9]*/msr"),
              key=lambda p: int(p.split("/")[3]))
with open(sys.argv[1], "w") as out:
    if not cpus:
        out.write("no /dev/cpu/*/msr\n")
    for path in cpus:
        cpu = path.split("/")[3]
        try:
            fd = os.open(path, os.O_RDONLY)
        except OSError as e:
            out.write("cpu%s: %s\n" % (cpu, e))
            continue
        for r in regs:
            try:
                v = struct.unpack("<Q", os.pread(fd, 8, r))[0]
                out.write("cpu%s 0x%03x %-14s 0x%016x\n" % (cpu, r, names.get(r, ""), v))
            except OSError as e:
                out.write("cpu%s 0x%03x %-14s error %s\n" % (cpu, r, names.get(r, ""), e))
        os.close(fd)
EOF
cat /proc/mtrr >"$OUT/proc-mtrr.txt" 2>&1
for f in /sys/kernel/debug/x86/pat_memtype_list /sys/kernel/debug/x86/pat_memtype; do
  [ -r "$f" ] && cp "$f" "$OUT/$(basename "$f").txt"
done
cat /proc/iomem >"$OUT/proc-iomem.txt" 2>&1
dmesg | awk 'tolower($0) ~ /efifb|simplefb|simple-framebuffer|sysfb|bootfb|fb0|screen_info|x86\/pat|mtrr/' >"$OUT/dmesg-fb-pat.txt"
for f in /sys/firmware/efi/systab /sys/kernel/boot_params/data; do
  [ -r "$f" ] && echo "present: $f"
done >"$OUT/firmware-files.txt"
[ -r /sys/kernel/boot_params/data ] && cp /sys/kernel/boot_params/data "$OUT/boot_params.bin"
lspci -nn -vvv -s 00:02.0 >"$OUT/lspci-00-02.0.txt" 2>&1
cat /sys/bus/pci/devices/0000:00:02.0/resource >"$OUT/resource-00-02.0.txt" 2>&1
tar -czf "$OUT.tar.gz" "$OUT" && echo "platform.sh: wrote $OUT.tar.gz"
