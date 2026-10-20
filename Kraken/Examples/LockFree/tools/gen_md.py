# Writes Kraken/Examples/LockFree/THEOREMS.md from inv.py and THEOREMS.tmpl.md
# Run from the repository root:
#   python3 Kraken/Examples/LockFree/tools/gen_md.py
import sys, glob, os
TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
from inv import A, X

LF = "Kraken/Examples/LockFree"

def cell(items, sep="<br>"):
    return sep.join("`%s` (%s)" % (n, f) for n, f in items)

def kls(isa):
    return sorted(os.path.basename(p)[:-3] for p in glob.glob("%s/%s/*.kl" % (LF, isa)))

def table(D, isa):
    rows = ["| Program | Whole-image safety | Runner-exact safety | No-fault, `decls = {}` | No-fault, `decls = ds` | Safe ∧ `FaultFree` (runner) | Reachability (`Reach`/`Cert`) | Liveness | Open gaps |",
            "|---|---|---|---|---|---|---|---|---|"]
    for k in kls(isa):
        d = D[k]
        whole = cell(d.get("whole", []))
        if d.get("extra"):
            whole += ("<br>" if whole else "") + "also: " + cell(d["extra"], "; ")
        rows.append("| [`%s`](%s/%s.kl) | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            k, isa, k, whole or "—", cell(d.get("runner", [])) or "—", cell(d.get("nf0", [])) or "—",
            cell(d.get("nfd", [])) or "—", cell(d.get("sff", [])) or "—", cell(d.get("reach", [])) or "—",
            cell(d.get("live", [])) or "—", d.get("open", "") or "—"))
    return "\n".join(rows)

def ff(D, isa):
    rows = ["| Program | `Config.FaultFree` at the runner's declarations | File |", "|---|---|---|"]
    for k in kls(isa):
        for n, f in D[k].get("ff", []):
            rows.append("| `%s` | `%s` | %s |" % (k, n, f))
    return "\n".join(rows)

def verdicts():
    rows = ["| Program | Theorem | File |", "|---|---|---|"]
    for isa, D in (("AArch64", A), ("X64", X)):
        for k in sorted(D):
            for n, f in D[k].get("verdict", []):
                rows.append("| `%s/%s.kl` | `%s` | %s |" % (isa, k, n, f))
    return "\n".join(rows)

if __name__ == "__main__":
    tmpl = open(os.path.join(TOOLS, "THEOREMS.tmpl.md")).read()
    out = (tmpl.replace("@A64TABLE@", table(A, "AArch64")).replace("@X64TABLE@", table(X, "X64"))
           .replace("@A64FF@", ff(A, "AArch64")).replace("@X64FF@", ff(X, "X64"))
           .replace("@VERDICTS@", verdicts()))
    open("%s/THEOREMS.md" % LF, "w").write(out)
