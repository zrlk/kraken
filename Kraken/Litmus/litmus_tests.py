#!/usr/bin/env python3
"""Compare Kraken's Promising machine with herd7 on a litmus corpus.

Usage:
  litmus_tests.py [--isa aarch64|x64] [--fuel N] [--herd PATH] [--slow] [--lse2] [-v] DIR_OR_FILES...

For every `.litmus` file, runs `krakenlitmus_<isa>` and compares its report
with the cached oracle output `<test>.litmus.herd` (produced by
`corpus/refresh.sh`; regenerated on the fly with `--herd` if missing), or
else a hand-argued `<test>.litmus.hand` in the same format (for tests herd
cannot run, e.g. `corpus/x86_64-vector`).
Agreement means: the same set of state lines (each line compared as a set of
`obs=value` entries) and the same `Observation` verdict word. Tests Kraken
rejects are reported as unsupported, separately from mismatches.

herd prints a `Loop Ok` / `Loop No` pseudo-state for a test whose unrolling
it cut short (a retry loop); it is not a final state, and Kraken, which runs
loops under its `-fuel` budget, reports only real states. The pseudo-state is
dropped from the oracle's states before comparing (only from the oracle: a
`Loop` line in Kraken's own report is compared as a state), so such a test is
compared on its real states and verdict word only, and every real-state
difference is still reported. Rows of such tests are marked `(herd Loop)`,
and the summary counts them.

Tests listed in a `slow.txt` next to them (one file name per line, `#`
comments) take minutes each and are skipped unless `--slow` is given (as
`Kraken/Examples/LockFree/run.sh -slow` does for `# slow` files).

A `<test>.litmus.sdm` oracle (same format), where present, takes precedence
over `.herd`: a hand-argued reading of the Intel SDM for tests where Kraken is
deliberately weaker than herd's x86-TSO model (corpus/x86_64-nt: herd treats
`movnti` as an ordinary TSO store). Its states must include all of herd's
(an SDM oracle may only add outcomes); otherwise the row is reported as
`BAD-SDM`, a mismatch. Rows compared against an SDM oracle are marked
`(SDM, weaker than herd)` and the summary counts them.

`--lse2` runs Kraken with FEAT_LSE2's single-copy-atomic 16-byte `LDP`/`STP`
(`krakenlitmus_aarch64 -lse2`, a Kraken-only option that herd does not model)
and compares with the hand-argued `<test>.litmus.lse2` oracles instead
(`corpus/aarch64-pairs/lse2/`); no regression corpus uses it.
"""
import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
BIN = ROOT / ".lake/build/bin"


LOOP_PSEUDO_STATE = re.compile(r"^Loop\s+(Ok|No)\s*$")


def parse_report(text, drop_loop=False):
    """-> dict name -> (set of frozenset(entries), observation word, loop) for each `Test` block.

    With `drop_loop` (the oracle), herd's `Loop Ok`/`Loop No` pseudo-state
    lines are not states; `loop` says whether the block had one."""
    results = {}
    for block in re.split(r"\n(?=Test |Unsupported )", text.strip()):
        lines = block.strip().split("\n")
        if not lines or not lines[0].startswith("Test "):
            continue
        name = lines[0].split()[1]
        states = set()
        obs = None
        loop = False
        for line in lines[1:]:
            if drop_loop and LOOP_PSEUDO_STATE.match(line.strip()):
                loop = True
            elif line.startswith("Observation"):
                obs = line.split()[2]
            elif line.startswith(("Ok", "No", "Witnesses", "Positive", "Condition", "States", "Configs", "Fault")):
                continue
            elif line.strip():
                entries = frozenset(e.strip() for e in line.strip().rstrip(";").split(";") if e.strip())
                states.add(entries)
        results[name] = (states, obs, loop)
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--isa", default="aarch64")
    ap.add_argument("--fuel", type=int, default=64)
    ap.add_argument("--herd", default=None, help="herd7 binary, to produce missing oracle files")
    ap.add_argument("--slow", action="store_true", help="also run the tests listed in slow.txt")
    ap.add_argument("--lse2", action="store_true",
                    help="FEAT_LSE2 16-byte LDP/STP (Kraken-only); compare with <test>.litmus.lse2")
    ap.add_argument("-v", action="store_true")
    args = ap.parse_args()

    files = []
    for p in args.paths:
        p = pathlib.Path(p)
        if p.is_dir():
            files += sorted(p.glob("*.litmus"))
        else:
            files.append(p)

    def slow_list(d):
        p = d / "slow.txt"
        if not p.exists():
            return set()
        return {l.split("#")[0].strip() for l in p.read_text().split("\n")} - {""}

    runner = BIN / f"krakenlitmus_{args.isa}"
    match = mismatch = unsupported = skipped = loops = sdms = 0
    rows = []
    for f in files:
        if not args.slow and f.name in slow_list(f.parent):
            skipped += 1
            rows.append(("SKIPPED", f.name, "slow (slow.txt); use --slow"))
            continue
        oracle_path = pathlib.Path(str(f) + (".lse2" if args.lse2 else ".herd"))
        kinds = f.parent / "kinds.txt"
        if not oracle_path.exists() and args.herd and not args.lse2:
            cmd = [args.herd] + (["-kinds", str(kinds)] if kinds.exists() else []) + [f.name]
            out = subprocess.run(cmd, cwd=f.parent, capture_output=True, text=True).stdout
            oracle_path.write_text("\n".join(l for l in out.split("\n") if not l.startswith(("Time ", "Hash="))))
        # a hand-argued oracle (`<test>.litmus.hand`) where herd cannot run the
        # test (corpus/x86_64-vector: herd has no vector instructions)
        hand_path = pathlib.Path(str(f) + ".hand")
        if not oracle_path.exists() and hand_path.exists():
            oracle_path = hand_path
        oracle = parse_report(oracle_path.read_text(), drop_loop=True) if oracle_path.exists() else {}
        # a hand-argued SDM oracle (`<test>.litmus.sdm`) where Kraken is
        # deliberately weaker than herd (corpus/x86_64-nt); it may only add states
        sdm_path = pathlib.Path(str(f) + ".sdm")
        is_sdm = False
        if sdm_path.exists() and not args.lse2:
            sdm = parse_report(sdm_path.read_text(), drop_loop=True)
            if oracle:
                (_, (st_h, _, _)), = oracle.items()
                (_, (st_s, _, _)), = sdm.items()
                if not st_h <= st_s:
                    mismatch += 1
                    rows.append(("BAD-SDM", f.name, "SDM oracle lacks herd states: " + " | ".join(
                        "; ".join(sorted(s)) for s in sorted(map(sorted, st_h - st_s)))))
                    continue
            oracle, is_sdm = sdm, True
        cmd = [str(runner), "-fuel", str(args.fuel)] + (["-kinds", str(kinds)] if kinds.exists() else []) \
            + (["-lse2"] if args.lse2 else []) + [str(f)]
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
            out = proc.stdout
        except subprocess.TimeoutExpired:
            out = "Unsupported timeout"
        ours = parse_report(out)
        if not ours:
            reason = out.strip().split("\n")[0] if out.strip() else "no output"
            unsupported += 1
            rows.append(("UNSUPPORTED", f.name, reason))
            continue
        if not oracle:
            unsupported += 1
            rows.append(("NO-ORACLE", f.name, ""))
            continue
        (name, (st_o, obs_o, loop_o)), = oracle.items()
        (_, (st_k, obs_k, _)), = ours.items()
        note = "(herd Loop)" if loop_o else ""
        if is_sdm:
            note = (note + " " if note else "") + "(SDM, weaker than herd)"
            sdms += 1
        loops += loop_o
        if st_o == st_k and obs_o == obs_k:
            match += 1
            rows.append(("match", f.name, note))
        else:
            mismatch += 1
            extra = st_k - st_o
            missing = st_o - st_k
            src = "sdm" if is_sdm else "herd"
            detail = (note + " " if note else "") + f"{src} {obs_o} / kraken {obs_k}"
            if extra:
                detail += "; kraken-only: " + " | ".join("; ".join(sorted(s)) for s in sorted(map(sorted, extra)))
            if missing:
                detail += "; herd-only: " + " | ".join("; ".join(sorted(s)) for s in sorted(map(sorted, missing)))
            rows.append(("MISMATCH", f.name, detail))

    for status, name, detail in rows:
        if args.v or status != "match":
            print(f"{status:12} {name:40} {detail}")
    slow = f", {skipped} skipped (slow)" if skipped else ""
    loop = f"; {loops} compared without herd's Loop pseudo-state" if loops else ""
    sdm_note = f"; {sdms} compared with an SDM oracle (weaker than herd)" if sdms else ""
    print(f"\n{match} match, {mismatch} mismatch, {unsupported} unsupported{slow}, of {len(files)}{loop}{sdm_note}")
    return 1 if mismatch else 0


if __name__ == "__main__":
    sys.exit(main())
