#!/usr/bin/env python3
"""Per-process memory watch for the lean processes of one checkout, with caps from tools/memory_caps.tsv.

Usage: tools/memwatch.py OUT.tsv REPO [--kill] [--caps FILE] [--override FILE]

Every second, for every `lean` process whose working directory is REPO, the
peak RssAnon and VmHWM are recorded per source file. The module is the source
path relative to REPO (`Spike/Test/Foo.lean` -> `Spike.Test.Foo`); its cap is
its row in the caps file (default: tools/memory_caps.tsv next to this script),
else the `*` row. A process above its cap is logged as OVER in OUT.tsv.events
and, with --kill, sent SIGTERM (that PID only, once).

--override FILE: lines `MODULE CAP_MIB`, re-read every second, take precedence
over the caps file (a gate raises one module's cap for a solo re-run and
removes the line afterwards).

OUT.tsv, rewritten every 10 s and on SIGTERM/SIGINT, one line per source file:
  peak_rssanon_mib  peak_vmhwm_mib  cap_mib  over(0/1)  killed(0/1)  module
OUT.tsv.conc: the most lean processes of REPO seen at once, and a histogram.
Samples are one second apart, so a peak is a lower bound.
"""
import os
import signal
import sys
import time


def parse_args(argv):
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    out, repo = argv[0], os.path.realpath(argv[1])
    kill, caps, override = False, os.path.join(os.path.dirname(os.path.abspath(__file__)), "memory_caps.tsv"), None
    i = 2
    while i < len(argv):
        a = argv[i]
        if a == "--kill":
            kill = True
        elif a == "--caps" and i + 1 < len(argv):
            caps, i = argv[i + 1], i + 1
        elif a == "--override" and i + 1 < len(argv):
            override, i = argv[i + 1], i + 1
        else:
            print(f"memwatch: unknown argument {a}", file=sys.stderr)
            sys.exit(2)
        i += 1
    return out, repo, kill, caps, override


def read_caps(path):
    caps = {}
    with open(path) as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            cols = line.rstrip("\n").split("\t")
            if len(cols) >= 3 and cols[2].isdigit():
                caps[cols[0]] = int(cols[2])
    if "*" not in caps:
        print(f"memwatch: {path} has no `*` row", file=sys.stderr)
        sys.exit(2)
    return caps


def read_override(path):
    res = {}
    if not path:
        return res
    try:
        with open(path) as f:
            for line in f:
                cols = line.split()
                if len(cols) == 2 and cols[1].isdigit():
                    res[cols[0]] = int(cols[1])
    except OSError:
        pass
    return res


def status_kb(pid, keys):
    vals = dict.fromkeys(keys, 0)
    try:
        with open(f"/proc/{pid}/status") as f:
            for line in f:
                k = line.split(":", 1)[0]
                if k in vals:
                    vals[k] = int(line.split()[1])
    except OSError:
        return None
    return vals


def main():
    out, repo, kill, capsfile, override = parse_args(sys.argv[1:])
    caps = read_caps(capsfile)
    peak = {}   # module -> [anon, hwm, cap, over, killed]
    hit = set()
    maxc, hist = 0, {}
    events = open(out + ".events", "a", buffering=1)

    def dump(*_):
        with open(out + ".tmp", "w") as f:
            for m, (a, h, c, o, k) in sorted(peak.items(), key=lambda kv: -kv[1][0]):
                f.write(f"{a}\t{h}\t{c}\t{o}\t{k}\t{m}\n")
        os.replace(out + ".tmp", out)
        with open(out + ".conc", "w") as f:
            f.write(f"max_concurrent_seen {maxc}\n")
            f.write("histogram " + " ".join(f"{k}:{v}" for k, v in sorted(hist.items())) + "\n")

    def stop(*_):
        dump()
        sys.exit(0)

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    tick = 0
    while True:
        ov = read_override(override)
        n = 0
        for pid in os.listdir("/proc"):
            if not pid.isdigit():
                continue
            try:
                with open(f"/proc/{pid}/comm") as f:
                    if f.read().strip() != "lean":
                        continue
                if os.path.realpath(f"/proc/{pid}/cwd") != repo:
                    continue
                with open(f"/proc/{pid}/cmdline", "rb") as f:
                    args = [a.decode(errors="replace") for a in f.read().split(b"\0")]
            except OSError:
                continue
            src = next((a for a in args if a.endswith(".lean")), None)
            if src is None:
                continue
            n += 1
            rel = os.path.relpath(os.path.join(repo, src), repo)
            mod = rel[:-5].replace("/", ".")
            cap = ov.get(mod, caps.get(mod, caps["*"]))
            st = status_kb(pid, ("RssAnon", "VmHWM"))
            if st is None:
                continue
            a, h = st["RssAnon"] // 1024, st["VmHWM"] // 1024
            p = peak.setdefault(mod, [0, 0, cap, 0, 0])
            p[0], p[1], p[2] = max(p[0], a), max(p[1], h), cap
            if a > cap and pid not in hit:
                hit.add(pid)
                p[3] = 1
                msg = f"{time.strftime('%H:%M:%S', time.gmtime())} OVER {mod} pid {pid} {a} MiB > cap {cap} MiB"
                if kill:
                    try:
                        os.kill(int(pid), signal.SIGTERM)
                        p[4] = 1
                        msg += " - killed"
                    except OSError:
                        msg += " - kill failed"
                events.write(msg + "\n")
        if n:
            hist[n] = hist.get(n, 0) + 1
        maxc = max(maxc, n)
        tick += 1
        if tick % 10 == 0:
            dump()
        time.sleep(1)


if __name__ == "__main__":
    main()
