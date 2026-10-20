#!/usr/bin/env python3
"""An independent operational reading of the Intel SDM's ordering rules for
non-temporal stores, for the small x86_64 litmus subset of this corpus.

Used to write (and re-check) the hand-argued `<test>.litmus.sdm` oracles:

    sdm_model.py [--write] TEST.litmus...

prints the outcome report (herd's format) for each test; with `--write` it
also writes it to `<test>.litmus.sdm` when it differs from herd's
`<test>.litmus.herd`, and removes a stale `.sdm` when they agree.

The machine (SDM vol. 3A §8.2.2, §8.2.5, §11.3.1; MOVNTI's description):
- every thread executes in program order; a load reads the latest pending
  store of its own thread to that location (forwarding), else memory;
- an ordinary store enters the thread's FIFO store buffer (x86-TSO);
- a non-temporal store (`movnti`) enters the thread's write-combining
  buffer, whose entries drain to memory in any order ("weakly ordered");
- two pending stores of a thread to the same location drain in program
  order (coherence);
- `sfence`: a store after it drains only once every store before it has
  drained; it does not hold up loads;
- `mfence` and a locked instruction (`xchg` with memory) wait until both
  buffers are empty; a locked instruction then reads and writes memory
  atomically;
- `lfence` orders nothing here (loads are already in order).
A store executes after the loads before it in program order (writes are not
reordered with older reads, with no exception for NT stores).
"""
import pathlib
import re
import sys

REG64 = {}
for b in "abcd":
    for n in (f"r{b}x", f"e{b}x", f"{b}x", f"{b}l"):
        REG64[n] = f"r{b}x"
for b in ("si", "di", "sp", "bp"):
    for n in (f"r{b}", f"e{b}", b, f"{b}l"):
        REG64[n] = f"r{b}"
for i in range(8, 16):
    for n in (f"r{i}", f"r{i}d", f"r{i}w", f"r{i}b"):
        REG64[n] = f"r{i}"


def reg(s):
    return REG64[s.strip().lstrip("%").lower()]


def parse(path):
    text = pathlib.Path(path).read_text()
    name = text.split("\n", 1)[0].split()[1]
    init_txt = text[text.index("{") + 1:text.index("}")]
    init = {}
    for item in init_txt.replace("\n", " ").split(";"):
        item = item.strip()
        if not item or "=" not in item:
            continue  # a type declaration such as `int64_t x`
        lhs, rhs = (x.strip() for x in item.split("="))
        if ":" in lhs:
            tid, r = lhs.split(":")
            rhs = int(rhs) if re.fullmatch(r"-?\d+", rhs) else rhs
            init[(int(tid), reg(r))] = rhs
    body = text[text.index("}") + 1:]
    cond = body[body.index("exists"):].strip()
    rows = [l for l in body[:body.index("exists")].split("\n") if "|" in l or l.strip().endswith(";")]
    rows = [l.strip().rstrip(";") for l in rows if l.strip()]
    header = [c.strip() for c in rows[0].split("|")]
    nthreads = len(header)
    progs = [[] for _ in range(nthreads)]
    for row in rows[1:]:
        cells = [c.strip() for c in row.split("|")]
        for t, c in enumerate(cells):
            if c:
                progs[t].append(c)
    return name, init, progs, cond


def operand(o):
    o = o.strip()
    if o.startswith("$"):
        return ("imm", int(o[1:]))
    if o.startswith("%"):
        return ("reg", reg(o))
    m = re.fullmatch(r"\((.*)\)", o)
    if m:
        a = m.group(1).strip()
        return ("mem", ("reg", reg(a)) if a.startswith("%") else ("sym", a))
    raise ValueError(o)


def decode(ins):
    parts = ins.split(None, 1)
    mn = parts[0].lower()
    ops = [operand(o) for o in parts[1].split(",")] if len(parts) > 1 else []
    if mn in ("mfence", "lfence", "sfence"):
        return (mn,)
    if mn in ("movl", "movq"):
        src, dst = ops
        if dst[0] == "mem":
            return ("st", src, dst[1])
        if src[0] == "mem":
            return ("ld", src[1], dst[1])
        return ("mov", src, dst[1])
    if mn in ("movntil", "movntiq", "movnti"):
        src, dst = ops
        return ("stnt", src, dst[1])
    if mn in ("xchgl", "xchgq", "xchg"):
        a, b = ops
        m, r = (a, b) if a[0] == "mem" else (b, a)
        return ("xchg", m[1], r[1])
    raise ValueError(ins)


def run(init, progs):
    """Every final (registers, memory) the machine can reach."""
    n = len(progs)
    code = [[decode(i) for i in p] for p in progs]
    # thread state: (pc, regs(frozenset), buffer(tuple of (seq, nt, epoch, loc, val)), epoch, seq)
    def regs0(t):
        return tuple(sorted((r, v) for (tt, r), v in init.items() if tt == t))
    start = (tuple((0, regs0(t), (), 0, 0) for t in range(n)), ())
    finals = set()
    seen = set()
    stack = [start]

    def getr(regs, r):
        return dict(regs).get(r, 0)

    def setr(regs, r, v):
        d = dict(regs)
        d[r] = v
        return tuple(sorted(d.items()))

    def val(regs, o):
        return o[1] if o[0] == "imm" else getr(regs, o[1])

    def loc(regs, a):
        return a[1] if a[0] == "sym" else getr(regs, a[1])

    def memget(mem, l):
        return dict(mem).get(l, 0)

    def memset(mem, l, v):
        d = dict(mem)
        d[l] = v
        return tuple(sorted(d.items()))

    while stack:
        st = stack.pop()
        if st in seen:
            continue
        seen.add(st)
        threads, mem = st
        moved = False
        for t, (pc, regs, buf, epoch, seq) in enumerate(threads):
            def upd(th, m=mem):
                ts = list(threads)
                ts[t] = th
                return (tuple(ts), m)
            # drain one buffered store
            for i, (s, nt, e, l, v) in enumerate(buf):
                earlier = buf[:i]
                if not nt and any(not x[1] for x in earlier):
                    continue  # the store buffer is FIFO
                if any(x[3] == l for x in earlier):
                    continue  # coherence: same-location stores in order
                if any(x[2] < e for x in earlier):
                    continue  # sfence: earlier stores first
                stack.append(upd((pc, regs, buf[:i] + buf[i + 1:], epoch, seq), memset(mem, l, v)))
                moved = True
            if pc >= len(code[t]):
                continue
            ins = code[t][pc]
            k = ins[0]
            nxt = None
            if k == "mov":
                nxt = upd((pc + 1, setr(regs, ins[2], val(regs, ins[1])), buf, epoch, seq))
            elif k in ("st", "stnt"):
                entry = (seq, k == "stnt", epoch, loc(regs, ins[2]), val(regs, ins[1]))
                nxt = upd((pc + 1, regs, buf + (entry,), epoch, seq + 1))
            elif k == "ld":
                l = loc(regs, ins[1])
                fw = [x for x in buf if x[3] == l]
                v = max(fw)[4] if fw else memget(mem, l)
                nxt = upd((pc + 1, setr(regs, ins[2], v), buf, epoch, seq))
            elif k == "sfence":
                nxt = upd((pc + 1, regs, buf, epoch + 1, seq))
            elif k == "lfence":
                nxt = upd((pc + 1, regs, buf, epoch, seq))
            elif k == "mfence":
                if not buf:
                    nxt = upd((pc + 1, regs, buf, epoch, seq))
            elif k == "xchg":
                if not buf:
                    l = loc(regs, ins[1])
                    old = memget(mem, l)
                    nxt = upd((pc + 1, setr(regs, ins[2], old), buf, epoch, seq),
                              memset(mem, l, getr(regs, ins[2])))
            if nxt is not None:
                stack.append(nxt)
                moved = True
        if all(pc >= len(code[t]) and not buf for t, (pc, _, buf, _, _) in enumerate(threads)):
            finals.add(st)
    return finals


def observe(cond, finals):
    """herd's state lines for the condition's observables, and the verdict."""
    atoms = re.findall(r"(\d+:\w+|\[\w+\]|\b[a-z]\w*\b)\s*=\s*(-?\w+)", cond[len("exists"):])
    obs = []
    for a, _ in atoms:
        if a not in obs:
            obs.append(a)

    def get(st, a):
        threads, mem = st
        if ":" in a:
            t, r = a.split(":")
            return dict(threads[int(t)][1]).get(reg(r), 0)
        return dict(mem).get(a.strip("[]"), 0)

    states = set()
    for st in finals:
        states.add(tuple((a, get(st, a)) for a in obs))
    expr = cond[len("exists"):].strip()
    py = expr.replace("/\\", " and ").replace("\\/", " or ").replace("~", " not ")

    def holds(s):
        e = py
        for a, v in s:
            e = re.sub(r"(?<![\w\[:])" + re.escape(a) + r"\s*=\s*(-?\w+)",
                       lambda m: str(str(v) == m.group(1)), e)
        return eval(e)
    pos = sum(1 for s in states if holds(s))
    return obs, states, pos, expr


def report(name, cond, finals):
    obs, states, pos, expr = observe(cond, finals)
    lines = sorted("".join(f"{a}={v}; " for a, v in s).rstrip() for s in states)
    neg = len(states) - pos
    word = "Never" if pos == 0 else ("Always" if neg == 0 else "Sometimes")
    out = [f"Test {name} Allowed", f"States {len(states)}"] + lines + [
        "Ok" if pos else "No", "Witnesses", f"Positive: {pos} Negative: {neg}",
        f"Condition exists {expr}", f"Observation {name} {word} {pos} {neg}", ""]
    return "\n".join(out) + "\n"


def states_of(text):
    st = set()
    for l in text.split("\n"):
        if re.match(r"^\s*(\d+:|\[)\w", l) and "=" in l and not l.startswith("Condition"):
            st.add(frozenset(e.strip() for e in l.strip().rstrip(";").split(";") if e.strip()))
    return st


def main():
    write = "--write" in sys.argv
    for f in [a for a in sys.argv[1:] if not a.startswith("--")]:
        name, init, progs, cond = parse(f)
        rep = report(name, cond, run(init, progs))
        herd = pathlib.Path(f + ".herd")
        sdm = pathlib.Path(f + ".sdm")
        same = herd.exists() and states_of(herd.read_text()) == states_of(rep)
        tag = "same as herd" if same else "differs from herd"
        if herd.exists() and not states_of(herd.read_text()) <= states_of(rep):
            tag = "STRICTER THAN HERD"
        print(f"{name}: {tag}")
        if write:
            if same and sdm.exists():
                sdm.unlink()
            elif not same:
                sdm.write_text(rep)


if __name__ == "__main__":
    main()
