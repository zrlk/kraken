#!/usr/bin/env python3
"""crossset.py A_DIR B_DIR SPEC   (cross-set check of the per-toolchain premise sets; tools/premises/crossset.py)

A_DIR: premise texts of the default set (frozen/ or a new premises.out); B_DIR: the same roots rendered on
another toolchain or in another module layout.  SPEC (the set's crossset.spec; one item per line, `#` comments):
    rename <old> -> <new>    a constant named <old> in A is named <new> in B (the source layout adds a
                             `_<module>` suffix to derived-instance names, the vendored layout none).  Checked: <old> occurs in A
                             and not in B, <new> occurs in B and not in A, pairs are 1:1, and the block of
                             <new> in B (its `name : type` line and indented body lines) equals the block of
                             <old> in A after the renames (identical body).
    rule decide-struct       B prints `isTrue h` / `isFalse h` as `{ decide := true|false, reflects_decide := h }`
    rule rewrap              one side has `L` + a more-indented continuation `C` where the other has `L C.strip()`
Every line of every file must match exactly after the renames (applied to A) and the decide-struct rule (applied
to B), except for rewrap joins (if enabled).  Anything else is OTHER.  The two dirs must have the same `*.txt`
files.  rc 0 iff OTHER = 0 and no spec problem (rc 1 otherwise); the last line is the summary.  rc 3: the
check did not run (usage error, unreadable input, crash).
"""
import os, re, sys

ID = r"[A-Za-z0-9_'!?]"
NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?.]*$")
DEC = re.compile(r'\{ decide := (true|false), reflects_decide := ([^ {}]+) \}')


def tokre(name):
    return re.compile(r'(?<![A-Za-z0-9_\'!?.])' + re.escape(name) + r'(?!' + ID + ')')


def files(d):
    return sorted(f for f in os.listdir(d) if f.endswith('.txt') and f != 'lang_absent_ok.txt')


def indent(l):
    return len(l) - len(l.lstrip(' '))


def blocks(lines):
    """name -> block (header + following indented lines) for the unindented `name : type` lines."""
    out, cur = {}, None
    for l in lines:
        if not l.startswith(' ') and ' : ' in l:
            cur = l.split(' : ', 1)[0]
            out[cur] = [l]
        elif cur is not None and l.startswith(' '):
            out[cur].append(l)
        else:
            cur = None
    return out


def main(argv):
    A, B, spec = argv[1:]
    probs, renames, rules = [], [], set()
    for k, raw in enumerate(open(spec, encoding='utf-8'), 1):
        l = raw.split('#', 1)[0].strip()
        if not l:
            continue
        m = re.fullmatch(r'rename\s+(\S+)\s+->\s+(\S+)', l)
        if m and NAME.match(m.group(1)) and NAME.match(m.group(2)) and m.group(1) != m.group(2):
            renames.append((m.group(1), m.group(2)))
        elif l in ('rule decide-struct', 'rule rewrap'):
            rules.add(l.split()[1])
        else:
            probs.append(f'SPEC line {k}: not understood: {l}')
    olds, news = [o for o, _ in renames], [n for _, n in renames]
    if len(set(olds)) != len(olds) or len(set(news)) != len(news) or set(olds) & set(news):
        probs.append('SPEC: rename pairs are not 1:1 (a name repeats, or a new name is also an old one)')
    fa, fb = files(A), files(B)
    if fa != fb:
        probs.append(f'FILES differ: only in A {sorted(set(fa) - set(fb))[:5]}, only in B {sorted(set(fb) - set(fa))[:5]}')
    res = [(o, n, tokre(o), tokre(n)) for o, n in renames]
    used = {o: 0 for o in olds}
    stats = {'renamed lines': 0, 'decide-struct lines': 0, 'rewrap joins': 0}
    other = []
    for f in sorted(set(fa) & set(fb)):
        ta = open(os.path.join(A, f), encoding='utf-8').read().split('\n')
        tb = open(os.path.join(B, f), encoding='utf-8').read().split('\n')
        for o, n, ro, rn in res:
            for l in ta:
                if rn.search(l):
                    probs.append(f'COLLISION: new name {n} already occurs in A [{f}]'); break
            for l in tb:
                if ro.search(l):
                    probs.append(f'STALE: old name {o} still occurs in B [{f}]'); break
        ma = []
        for l in ta:
            l2 = l
            for o, n, ro, rn in res:
                l2, c = ro.subn(n, l2)
                used[o] += c
            stats['renamed lines'] += l2 != l
            ma.append(l2)
        mb = []
        for l in tb:
            l2 = DEC.sub(lambda m: ('isTrue ' if m.group(1) == 'true' else 'isFalse ') + m.group(2), l) if 'decide-struct' in rules else l
            stats['decide-struct lines'] += l2 != l
            mb.append(l2)
        # identical body: the block of each renamed constant
        ba, bb = blocks(ma), blocks(mb)
        for o, n in renames:
            if n in ba and ba[n] != bb.get(n):
                if not ('rewrap' in rules and bb.get(n) is not None and
                        ' '.join(' '.join(ba[n]).split()) == ' '.join(' '.join(bb[n]).split())):
                    probs.append(f'RENAME-BODY: {o} -> {n}: body differs [{f}]')
        i = j = 0
        while i < len(ma) or j < len(mb):
            if i < len(ma) and j < len(mb) and ma[i] == mb[j]:
                i += 1; j += 1; continue
            if 'rewrap' in rules:
                if (i + 1 < len(ma) and j < len(mb) and indent(ma[i + 1]) > indent(ma[i])
                        and ma[i].rstrip() + ' ' + ma[i + 1].strip() == mb[j]):
                    stats['rewrap joins'] += 1; i += 2; j += 1; continue
                if (j + 1 < len(mb) and i < len(ma) and indent(mb[j + 1]) > indent(mb[j])
                        and mb[j].rstrip() + ' ' + mb[j + 1].strip() == ma[i]):
                    stats['rewrap joins'] += 1; i += 1; j += 2; continue
            other.append((f, i + 1, ma[i] if i < len(ma) else '<eof>', mb[j] if j < len(mb) else '<eof>'))
            break
    for o in olds:
        if used[o] == 0:
            probs.append(f'UNUSED rename: {o} does not occur in A')
    for f, ln, a, b in other:
        print(f'OTHER {f} line {ln}:\n  A(normalised): {a[:160]}\n  B(normalised): {b[:160]}')
    for p in sorted(set(probs)):
        print(p)
    print(f'crossset: {len(fa)} files, {len(renames)} renames, rules {sorted(rules)}, '
          + ', '.join(f'{k} {v}' for k, v in stats.items()) + f', OTHER {len(other)}, problems {len(set(probs))}')
    return 0 if not other and not probs else 1


if __name__ == '__main__':
    # rc 3: the check itself did not run (usage error, unreadable file, crash); never reported as 0 or 1
    if len(sys.argv) != 4:
        print(__doc__)
        sys.exit(3)
    try:
        rc = main(sys.argv)
    except Exception as e:
        print(f'crossset: could not check ({type(e).__name__}: {e})')
        sys.exit(3)
    sys.exit(rc)
