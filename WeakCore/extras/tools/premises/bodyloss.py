#!/usr/bin/env python3
"""bodyloss.py BASE_OUT NEW_OUT [ALLOW]  (mechanises the body-loss scan)

Compares two CheckPremises output dirs (one `<root>.txt` per final / `lang.<root>.txt` per language
root).  FAILS (exit 1) if, for some file present in BASE:
  - the file is missing from NEW                                    (DROPPED-FILE), or
  - a constant listed in BASE's file is absent from NEW's file      (DROPPED), or
  - a constant printed WITH a body in BASE (`:=`, `eq_def`, ctor `|` lines) is header-only in NEW
                                                                    (BODYLOSS)
unless allowed by ALLOW (one entry per line, `#` comments; default: none): an entry is a constant's
full name (allowed in every file), `Name@file.txt` (allowed in that file only), or, for DROPPED-FILE,
the file name.  Only `*.txt` files other than `lang_absent_ok.txt` are compared.  A BASE file reading `ABSENT` lists no constants.
An allowlist entry that matches nothing is itself a failure (UNUSED-ALLOW).
Additions and text changes are NOT failures: those are what the premise md5 diff shows the user.
Typical use: M0 freeze vs pre-M0 freeze (allow RunDRF/ThDRF, renamed); 2b freeze vs M0 freeze (empty).
"""
import os
import sys

BODY = ('  := ', '  eq_def ', '  | ', '  fields ')


def parse(path):
    """name -> has_body, for one rendered file (headers are the unindented `name : type` lines)."""
    d, cur = {}, None
    with open(path, encoding='utf-8') as fh:
        for line in fh:
            if line.strip() == 'ABSENT' and not d:
                return {}
            if not line.startswith(' ') and ' : ' in line:
                cur = line.split(' : ', 1)[0]
                d[cur] = False
            elif cur is not None and line.startswith(BODY):
                d[cur] = True
    return d


def main(argv):
    if len(argv) not in (3, 4):
        sys.exit(__doc__)
    base, new = argv[1], argv[2]
    allow = set()
    if len(argv) == 4:
        with open(argv[3], encoding='utf-8') as fh:
            allow = {l.strip() for l in fh if l.strip() and not l.strip().startswith('#')}
    bad, allowed, nfiles = [], set(), 0
    for f in sorted(os.listdir(base)):
        if not f.endswith('.txt') or f == 'lang_absent_ok.txt':
            continue
        nfiles += 1
        np_ = os.path.join(new, f)
        if not os.path.exists(np_):
            (allowed.add(f) if f in allow else bad.append(f'DROPPED-FILE {f}'))
            continue
        a, b = parse(os.path.join(base, f)), parse(np_)
        for n, body in sorted(a.items()):
            kind = 'DROPPED' if n not in b else 'BODYLOSS' if body and not b[n] else None
            if kind is None:
                continue
            hit = n if n in allow else f'{n}@{f}' if f'{n}@{f}' in allow else None
            (allowed.add(hit) if hit else bad.append(f'{kind} {n}  [{f}]'))
    for x in sorted(allowed):
        print(f'allowed: {x}')
    unused = sorted(allow - allowed)
    bad += [f'UNUSED-ALLOW {x}' for x in unused]  # a stale entry must not silently widen the gate
    for x in bad:
        print(x)
    print(f'bodyloss: {nfiles} base files, {len(bad)} failure(s), {len(allowed)} allowed')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
