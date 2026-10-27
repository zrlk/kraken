#!/usr/bin/env python3
"""Makes a raw FAT16 EFI system partition image holding one boot file.

Usage: runtime/efi/mkesp.py OUT.img BOOTNAME FILE [--mib N]
  e.g. runtime/efi/mkesp.py esp.img BOOTX64.EFI .lake/efi/x64/stub.efi

The image is a bare FAT16 filesystem (no partition table) with
/EFI/BOOT/BOOTNAME, the removable-media default path that UEFI firmware
boots when it has no boot entries. It can be attached to QEMU as a raw drive
or written to a USB stick (most firmware accepts a partitionless FAT
"superfloppy"; if a machine does not, put it in a GPT ESP partition).

`mkfs.fat` formats the image; this script then writes the two directories and
the file directly (mtools is not needed). Only what is required for one file
is implemented: 8.3 upper-case names, contiguous clusters.
"""
import os
import struct
import subprocess
import sys


def name83(n):
    base, _, ext = n.partition(".")
    assert 1 <= len(base) <= 8 and len(ext) <= 3 and n == n.upper(), n
    return (base.ljust(8) + ext.ljust(3)).encode("ascii")


def dirent(name11, attr, cluster, size):
    # name, attr, nt-res, ctime(3), cdate, adate, clus_hi, wtime, wdate, clus_lo, size
    return struct.pack("<11sBBBHHHHHHHI", name11, attr, 0, 0, 0, 0x5821, 0x5821, 0, 0,
                       0x5821, cluster, size)


def main():
    args = sys.argv[1:]
    mib = 16
    if "--mib" in args:
        k = args.index("--mib")
        mib = int(args[k + 1])
        del args[k:k + 2]
    out, bootname, src = args
    data = open(src, "rb").read()
    if os.path.exists(out):
        os.remove(out)
    with open(out, "wb") as f:
        f.truncate(mib << 20)
    subprocess.run(["mkfs.fat", "-F", "16", "-s", "1", "-n", "KRAKENEFI", out],
                   check=True, stdout=subprocess.DEVNULL)
    img = bytearray(open(out, "rb").read())
    bps, spc, rsvd, nfats, nroot = struct.unpack_from("<HBHBH", img, 11)
    fatsz = struct.unpack_from("<H", img, 22)[0]
    assert bps == 512 and spc == 1, (bps, spc)
    fat0 = rsvd * bps
    root = fat0 + nfats * fatsz * bps
    data0 = root + nroot * 32
    csize = bps * spc

    def coff(c):
        return data0 + (c - 2) * csize

    def set_fat(c, v):
        for i in range(nfats):
            struct.pack_into("<H", img, fat0 + i * fatsz * bps + 2 * c, v)

    efi_c, boot_c, file_c = 2, 3, 4
    nfile = max(1, -(-len(data) // csize))
    set_fat(efi_c, 0xFFFF)
    set_fat(boot_c, 0xFFFF)
    for i in range(nfile):
        c = file_c + i
        set_fat(c, 0xFFFF if i == nfile - 1 else c + 1)
    # root: volume label entry written by mkfs stays at slot 0; EFI at slot 1
    slot = root
    while img[slot] not in (0x00, 0xE5):
        slot += 32
    img[slot:slot + 32] = dirent(name83("EFI"), 0x10, efi_c, 0)
    d = coff(efi_c)
    img[d:d + 32] = dirent(b".          ", 0x10, efi_c, 0)
    img[d + 32:d + 64] = dirent(b"..         ", 0x10, 0, 0)
    img[d + 64:d + 96] = dirent(name83("BOOT"), 0x10, boot_c, 0)
    d = coff(boot_c)
    img[d:d + 32] = dirent(b".          ", 0x10, boot_c, 0)
    img[d + 32:d + 64] = dirent(b"..         ", 0x10, efi_c, 0)
    img[d + 64:d + 96] = dirent(name83(bootname), 0x20, file_c, len(data))
    o = coff(file_c)
    img[o:o + len(data)] = data
    open(out, "wb").write(img)


if __name__ == "__main__":
    main()
