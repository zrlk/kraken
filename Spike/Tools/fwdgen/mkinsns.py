#!/usr/bin/env python3
"""sim.out -> insns.txt: `i pc (W) text [event]` per step (compact directive text)."""
import re, sys

src = sys.argv[1] if len(sys.argv) > 1 else '/tmp/fwdgen/sim.out'
for l in open(src):
    m = re.match(r'^(\d+) pc=(\d+) \[(.*?)\] F=(⟨.*?⟩) D=(.*)$', l.rstrip('\n'))
    if not m:
        continue
    i, pc, d = m.group(1), m.group(2), m.group(5)
    ev = ''
    tail = ''
    e = re.search(r' (\["[^\]]*"\])$', d)
    if e:
        ev = ' [' + e.group(1)[2:-2] + ']'
        d = d[:e.start()]
    e = re.search(r' (SYSCALL nr=\d+|TAKE \d+ \d+)$', d)
    if e:
        tail = ' ' + e.group(1)
        d = d[:e.start()]
    d = re.sub(r'\s+', ' ', d).strip()
    w = re.match(r'Directive\.instr \(Instr\.regular \(Width\.W64\) \(Width\.(W\d+)\) (.*)$', d)
    if w:
        W, body = w.group(1), w.group(2)
    else:
        W, body = 'W64', d
    for a, b in [('Operation.', ''), ('RegOrMem.', ''), ('Reg.low ', ''), ('Reg64.', ''), ('Width.', ''),
                 ('Operand.regOrMem ', ''), ('Operand.', ''), ('RegOrRip.', ''), ('ConstExpr.', ''),
                 ('idx := none, ', ''), ('RelRegOrMem.', 'Rel')]:
        body = body.replace(a, b)
    print(f'{i} {pc} ({W}) {body}{tail}{ev}')
