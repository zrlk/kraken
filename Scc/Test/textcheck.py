#!/usr/bin/env python3
"""Test-only (Scc/Test/certify_test.sh): compare an executable's `.text` with its listing's.

Usage: textcheck.py OBJ EXE
       textcheck.py --layout EXE

OBJ is the listing assembled to an object file (`as`, or clang -c for arm), EXE an executable
linked from it. Prints one line, `same: N bytes, M relocated sites masked` or `DIFFERENT: ...`,
and exits 0 or 1 (2 on a file it cannot read).

The object's `.text` has unresolved relocations, whose fields the linker fills in: those bytes are
masked (4 bytes per AArch64 relocation, which covers the whole instruction; 4 or 8 bytes per
x86-64 relocation by type). A linker relaxation that rewrites a relocated instruction is therefore
not seen; one that changes any other byte, or `.text`'s size (veneers, thunks, padding), is.

With --layout, prints `code LO SIZE rodata LO SIZE data LO` from EXE's section headers (`.text`,
`.rodata` or `0 0` without one, `.data`), in decimal: the harness compares it with what the ELF
reader (`Scc.Cert.Elf.elfParts`) reads, to catch a misread.

This is a harness check only: certify.sh itself does not compare `.text` with the listing, and
nothing here changes its verdicts. In certify_test.sh a DIFFERENT (including an x86-64 relocation
type not known here, which is reported rather than masked) fails the test.
"""
import struct
import sys

EM_X86_64, EM_AARCH64 = 62, 183
SHT_RELA = 4
# x86-64 relocation types and the width of the field each writes; an unknown type is an error.
X64_WIDTH = {1: 8, 2: 4, 4: 4, 9: 4, 10: 4, 11: 4, 24: 8, 41: 4, 42: 4}


def sections(b):
    if b[:4] != b'\x7fELF' or b[4] != 2 or b[5] != 1:
        raise ValueError('not a little-endian ELF64 file')
    machine, = struct.unpack_from('<H', b, 18)
    shoff, = struct.unpack_from('<Q', b, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from('<HHH', b, 0x3a)
    sh = [struct.unpack_from('<IIQQQQIIQQ', b, shoff + i * shentsize) for i in range(shnum)]
    strs = sh[shstrndx]

    def name(s):
        p = strs[4] + s[0]
        return bytes(b[p:b.index(0, p)]).decode()

    return machine, [(name(s), s) for s in sh]


def text_of(b, secs):
    found = [(i, s) for i, (n, s) in enumerate(secs) if n == '.text']
    if len(found) != 1:
        raise ValueError(f'{len(found)} sections .text')
    i, s = found[0]
    return i, bytes(b[s[4]:s[4] + s[5]])


def layout(path):
    b = open(path, 'rb').read()
    _, secs = sections(b)

    def rng(n):
        found = [s for m, s in secs if m == n]
        if len(found) > 1:
            raise ValueError(f'{len(found)} sections {n}')
        return (found[0][3], found[0][5]) if found else (0, 0)

    (tl, ts), (rl, rs), (dl, _) = rng('.text'), rng('.rodata'), rng('.data')
    print(f'code {tl} {ts} rodata {rl} {rs} data {dl}')
    return 0


def main():
    if len(sys.argv) == 3 and sys.argv[1] == '--layout':
        try:
            return layout(sys.argv[2])
        except (OSError, ValueError, IndexError, struct.error) as e:
            print(f'cannot read: {e}')
            return 2
    if len(sys.argv) != 3:
        print('usage: textcheck.py OBJ EXE | --layout EXE', file=sys.stderr)
        return 2
    try:
        ob = open(sys.argv[1], 'rb').read()
        eb = open(sys.argv[2], 'rb').read()
        om, osecs = sections(ob)
        em, esecs = sections(eb)
        oi, ot = text_of(ob, osecs)
        _, et = text_of(eb, esecs)
    except (OSError, ValueError, IndexError, struct.error) as e:
        print(f'cannot read: {e}')
        return 2
    if om != em:
        print(f'DIFFERENT: machine {om} (object) vs {em} (executable)')
        return 1
    if len(ot) != len(et):
        print(f'DIFFERENT: .text is {len(ot)} bytes in the object, {len(et)} in the executable')
        return 1
    mask = bytearray(len(ot))
    sites = 0
    for n, s in osecs:
        if s[1] != SHT_RELA or s[7] != oi:  # sh_type, sh_info (the section relocated)
            continue
        for off in range(s[4], s[4] + s[5], 24):
            r_off, r_info, _ = struct.unpack_from('<QQq', ob, off)
            typ = r_info & 0xffffffff
            if om == EM_AARCH64:
                w = 4
            elif typ in X64_WIDTH:
                w = X64_WIDTH[typ]
            else:
                print(f'DIFFERENT: unknown x86-64 relocation type {typ} at .text+{r_off:#x} (not masked)')
                return 1
            for k in range(r_off, min(r_off + w, len(ot))):
                mask[k] = 1
            sites += 1
    diff = [k for k in range(len(ot)) if not mask[k] and ot[k] != et[k]]
    if diff:
        print(f'DIFFERENT: {len(diff)} unrelocated .text bytes differ, first at .text+{diff[0]:#x} '
                    f'({ot[diff[0]]:#04x} in the object, {et[diff[0]]:#04x} in the executable)')
        return 1
    print(f'same: {len(ot)} bytes, {sites} relocated sites masked')
    return 0


if __name__ == '__main__':
    sys.exit(main())
