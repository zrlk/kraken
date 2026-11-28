#!/usr/bin/env python3
# Print facts (numbers only, no image bytes) about an iwlwifi .ucode file:
# its hashes, the TLV histogram, section lengths, capability and API bits
# and the table of command versions.
# Usage (read-only): python3 fwtlv.py /lib/firmware/iwlwifi-<name>.ucode[.zst]
# The file layout is the one Linux reads in
# drivers/net/wireless/intel/iwlwifi/fw/file.h.
import collections
import hashlib
import struct
import subprocess
import sys

NAMES = {19: 'SEC_RT', 24: 'SECURE_SEC_RT', 27: 'NUM_OF_CPU',
         29: 'API_CHANGES_SET', 30: 'ENABLED_CAPABILITIES', 32: 'PAGING',
         36: 'FW_VERSION', 48: 'CMD_VERSIONS', 52: 'IML',
         60: 'FW_FSEQ_VERSION'}


def load(path):
    if path.endswith('.zst'):
        return subprocess.run(['zstd', '-dc', path], check=True,
                              stdout=subprocess.PIPE).stdout
    with open(path, 'rb') as f:
        return f.read()


def main():
    path = sys.argv[1]
    raw = open(path, 'rb').read()
    data = load(path)
    print('file', path, 'size', len(raw), 'sha256', hashlib.sha256(raw).hexdigest())
    print('image size', len(data), 'sha256', hashlib.sha256(data).hexdigest())
    zero, magic = struct.unpack_from('<II', data, 0)
    if zero != 0 or magic != 0x0a4c5749:
        print('not a TLV ucode file'); return
    human = data[8:72].split(b'\0')[0].decode('ascii', 'replace')
    ver, build = struct.unpack_from('<II', data, 72)
    print('human_readable', human, 'ver 0x%08x build %d' % (ver, build))
    off = 88
    hist = collections.Counter()
    sizes = collections.defaultdict(int)
    sec = []
    cmdv = []
    capa = []
    api = []
    while off + 8 <= len(data):
        t, ln = struct.unpack_from('<II', data, off)
        body = data[off + 8:off + 8 + ln]
        hist[t] += 1
        sizes[t] += ln
        if t in (19, 24):
            sec.append((t, ln - 4))
        elif t == 48:
            for i in range(0, ln - ln % 4, 4):
                c, g, cv, nv = struct.unpack_from('<BBBB', body, i)
                cmdv.append((g, c, cv, nv))
        elif t == 30 and ln >= 8:
            idx, bits = struct.unpack_from('<II', body, 0)
            capa += [idx * 32 + b for b in range(32) if bits >> b & 1]
        elif t == 29 and ln >= 8:
            idx, bits = struct.unpack_from('<II', body, 0)
            api += [idx * 32 + b for b in range(32) if bits >> b & 1]
        elif t == 52:
            print('IML length', ln)
        elif t == 32 and ln >= 4:
            print('PAGING tlv value', struct.unpack_from('<I', body, 0)[0])
        off += 8 + ((ln + 3) & ~3)
    print('TLV types (type name count total_bytes):')
    for t in sorted(hist):
        print('  %d %s %d %d' % (t, NAMES.get(t, '-'), hist[t], sizes[t]))
    print('runtime sections (type payload_len), in file order:', len(sec))
    for t, ln in sec:
        print('  %s %d' % (NAMES[t], ln))
    print('capabilities set:', ' '.join(map(str, sorted(capa))))
    print('api flags set:', ' '.join(map(str, sorted(api))))
    print('cmd versions (group cmd cmd_ver notif_ver):', len(cmdv))
    for g, c, cv, nv in sorted(cmdv):
        print('  0x%02x 0x%02x %d %d' % (g, c, cv, nv))


if __name__ == '__main__':
    main()
