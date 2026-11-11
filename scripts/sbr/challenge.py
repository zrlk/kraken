#!/usr/bin/env python3
"""The static half of the challenge step (`challenge.sh`), run from the repository root.

Checks that `KrakenSbrChallenge/Challenge.lean` states exactly the theorems `challenge.json`
names (so that nothing stated there goes unjudged), that each of their proofs is `by sorry`, and
that it has no other forbidden token (`srcscan.py`'s list); and that
`KrakenSbrChallenge/Solution.lean` has only imports, so the judged theorems are the proof's
own. Exit 1 on a violation."""
import json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from srcscan import pat, strip

CFG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "challenge.json")
CH = "KrakenSbrChallenge/Challenge.lean"
SOL = "KrakenSbrChallenge/Solution.lean"


def declared(code):
  """The theorems `code` declares, with their full names (from the enclosing namespaces)."""
  ns, out = [], []
  for line in code.split("\n"):
    if m := re.match(r"namespace\s+(\S+)", line):
      ns.append(m.group(1))
    elif m := re.match(r"end\s+(\S+)", line):
      if ns and ns[-1] == m.group(1):
        ns.pop()
    elif m := re.match(r"theorem\s+(\S+)", line):
      out.append(".".join(ns + [m.group(1)]))
  return out


def main():
  fails = []
  cfg = json.load(open(CFG))
  code = strip(open(CH, encoding="utf-8").read())
  names = declared(code)
  if sorted(names) != sorted(cfg["theorem_names"]):
    fails.append(f"{CH} states {sorted(names)}, challenge.json names {sorted(cfg['theorem_names'])}")
  # every proof is `by` followed by `sorry`, and nothing else is forbidden
  proofs = re.findall(r":=\s*by\s+(\S+)", code)
  if len(proofs) != len(names) or any(p != "sorry" for p in proofs):
    fails.append(f"{CH}: {len(names)} theorems, proofs {proofs}: each must be `by sorry`")
  other = [l for l in code.split("\n") if pat.search(re.sub(r"\bsorry\b", "", l))]
  fails += [f"{CH}: forbidden token: {l.strip()[:100]}" for l in other]
  sol = [l for l in strip(open(SOL, encoding="utf-8").read()).split("\n") if l.strip()]
  fails += [f"{SOL}: not an import: {l.strip()[:100]}" for l in sol if not l.startswith("import ")]
  for f in fails:
    print("FAIL", f)
  print(f"challenge: {len(names)} theorems stated, {len(fails)} problems")
  sys.exit(1 if fails else 0)


if __name__ == "__main__":
  main()
