# The `ReachableSem` twins gate and listing. Run from
# the repository root, after `lake build`:
#   python3 Kraken/Examples/LockFree/tools/sem_twins.py           # check
#   python3 Kraken/Examples/LockFree/tools/sem_twins.py --write   # regenerate
#
# For every twin `t` added by `#sem_twin` (the constants of the modules
# `TWIN_MODULES` named `semName n` for an existing `n`), a generated Lean
# file checks, independently of `ChainK/SemTwin.lean`:
#   - type(t) == semType(type(n)), where semType replaces every
#     `Reachable A fuel c c'` by `ReachableSem A fuel c c'` and every
#     `Config.FaultFree` by `Config.FaultFreeSem`, and changes something;
#   - type(t) mentions neither `Reachable` nor `Config.FaultFree`;
#   - t's axioms are among propext, Classical.choice, Quot.sound;
#   - n is named in THEOREMS.md.
# It then writes (--write) or compares (default) the listing SEM_TWINS.md:
# one line per twin with its statement. Exit status 1 on any failure.
import os, re, subprocess, sys

LF = "Kraken/Examples/LockFree"
OUT = LF + "/SEM_TWINS.md"
LAKE = os.environ.get("LAKE", "lake")
# (side, module importing the twins, modules whose constants are scanned)
TWIN_MODULES = [
    ("AArch64", "Kraken.Promising.SLR.ChainK.SemTwinsA64",
     ["Kraken.Promising.SLR.ChainK.SemTwinsA64", "Kraken.Promising.SLR.ChainK.TicketA64Demo"]),
    ("X64", "Kraken.Promising.SLR.ChainK.SemTwinsX64", ["Kraken.Promising.SLR.ChainK.SemTwinsX64"]),
]

CHECK = r'''
open Lean Meta Elab Command

namespace SemTwinsCheck

/-- `semName` (TWINS naming rule): `_sem` before the first `_concrete`,
otherwise appended before any trailing primes. -/
def semName : Name → Name
  | .str p s =>
    match s.splitOn "_concrete" with
    | a :: b :: rest => .str p (a ++ "_sem_concrete" ++ "_concrete".intercalate (b :: rest))
    | _ =>
      let core := (s.toList.reverse.dropWhile (· == '\'')).reverse
      .str p (String.ofList core ++ "_sem" ++ String.ofList (s.toList.drop core.length))
  | n => n

partial def semType (e : Expr) : Expr :=
  match e with
  | .app .. =>
    let f := e.getAppFn
    let xs := e.getAppArgs.map semType
    if f.isConstOf ``Kraken.Promising.Reachable && xs.size == 5 then
      -- `@Reachable A I fuel c c'` ↦ `@ReachableSem I A fuel c c'`
      mkAppN (.const ``Kraken.Promising.Live.Bridge.ReachableSem f.constLevels!) #[xs[1]!, xs[0]!, xs[2]!, xs[3]!, xs[4]!]
    else mkAppN (semType f) xs
  | .const n us => if n == ``Kraken.Promising.Config.FaultFree then .const ``Kraken.Promising.Config.FaultFreeSem us else e
  | .forallE n d b bi => .forallE n (semType d) (semType b) bi
  | .lam n d b bi => .lam n (semType d) (semType b) bi
  | .letE n t v b nd => .letE n (semType t) (semType v) (semType b) nd
  | .mdata m b => .mdata m (semType b)
  | .proj s i b => .proj s i (semType b)
  | _ => e

/-- Collapse every run of whitespace to one space. -/
def oneLine (s : String) : String := Id.run do
  let mut out : List Char := []
  let mut sp := false
  for c in s.toList do
    if c.isWhitespace then sp := true
    else
      if sp && !out.isEmpty then out := ' ' :: out
      sp := false
      out := c :: out
  return String.ofList out.reverse

elab "#sem_twins_check " side:str mods:str* : command => do
  let env ← getEnv
  let mods := mods.map (·.getString.toName)
  let idxs := mods.filterMap env.getModuleIdx?
  unless idxs.size == mods.size do throwError "sem_twins_check: module not imported"
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  for (t, ci) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? t | continue
    unless idxs.contains i do continue
    let .str p s := t | continue
    let parts := s.splitOn "_sem"
    -- every way of deleting one `_sem` from the last component
    let cands := (List.range (parts.length - 1)).map fun k =>
      Name.str p ("_sem".intercalate (parts.take (k + 1)) ++ "_sem".intercalate (parts.drop (k + 1)))
    let some n := cands.find? (fun n => env.contains n && semName n == t) | continue
    let ci0 := (env.find? n).get!
    let tS := semType ci0.type
    let mut errs : Array String := #[]
    if tS == ci0.type then errs := errs.push "semType changes nothing"
    if tS != ci.type then errs := errs.push "type ≠ semType(type of original)"
    if (ci.type.find? fun x => x.isConstOf ``Kraken.Promising.Reachable ||
        x.isConstOf ``Kraken.Promising.Config.FaultFree).isSome then
      errs := errs.push "mentions Reachable/FaultFree"
    let axs ← liftCoreM <| collectAxioms t
    if axs.any (fun a => !ok.contains a) then errs := errs.push s!"axioms {axs}"
    let sig ← liftTermElabM do return oneLine ((← ppExpr ci.type).pretty 100000)
    IO.println s!"TWIN\t{side.getString}\t{t}\t{n}\t{if errs.isEmpty then "OK" else ", ".intercalate errs.toList}\t{sig}"

end SemTwinsCheck
'''

def run_side(side, imp, mods):
    os.makedirs(".lake/docs", exist_ok=True)
    f = ".lake/docs/sem_twins_%s.lean" % side
    with open(f, "w") as h:
        h.write("import %s\n" % imp + CHECK + '\nopen Kraken Kraken.Promising Kraken.Promising.Live.Bridge\n#sem_twins_check "%s" %s\n' % (side, " ".join('"%s"' % m for m in mods)))
    r = subprocess.run([LAKE, "env", "lean", f], capture_output=True, text=True)
    rows = [l.split("\t") for l in r.stdout.splitlines() if l.startswith("TWIN\t")]
    if r.returncode != 0:
        sys.stdout.write(r.stdout + r.stderr)
        sys.exit("sem_twins: lean failed on %s" % f)
    return rows

def main():
    write = "--write" in sys.argv
    theorems = open(LF + "/THEOREMS.md").read()
    rows = []
    for side, imp, mods in TWIN_MODULES:
        rows += run_side(side, imp, mods)
    bad = 0
    for r in rows:
        _, side, t, n, st, sig = r
        short = n[len("Kraken.Promising."):] if n.startswith("Kraken.Promising.") else n
        if "`%s`" % short.split(".")[-1] not in theorems and short not in theorems:
            st = (st + ", " if st != "OK" else "") + "original not in THEOREMS.md"
        if st != "OK":
            bad += 1
            print("BAD", t, ":", st)
    rows.sort(key=lambda r: (r[1], r[2]))
    lines = ["# `ReachableSem` twins of the published theorems",
             "",
             "Generated by `python3 Kraken/Examples/LockFree/tools/sem_twins.py --write`; do not edit.",
             "Each twin `n_sem` (`ChainK/SemTwin.lean`, `#sem_twin`) has the statement of the",
             "published theorem `n` (THEOREMS.md) with `Reachable A fuel c₀ c` replaced by",
             "`ReachableSem A fuel c₀ c` (same fuel binder, now the certification fuel) and",
             "`Config.FaultFree` by `Config.FaultFreeSem`. `sem_twins.py` re-checks every line.",
             "Names are relative to `Kraken.Promising`; statements are printed with",
             "`open Kraken Kraken.Promising Kraken.Promising.Live.Bridge`.",
             "",
             "%d twins (AArch64 %d, X64 %d)." % (len(rows), sum(r[1] == "AArch64" for r in rows),
                                                sum(r[1] == "X64" for r in rows)),
             ""]
    side = None
    for r in rows:
        if r[1] != side:
            side = r[1]
            lines += ["", "## " + side, ""]
        sh = lambda n: n[len("Kraken.Promising."):] if n.startswith("Kraken.Promising.") else n
        lines.append("- `%s` (twin of `%s`): `%s`" % (sh(r[2]), sh(r[3]), r[5]))
    text = "\n".join(lines) + "\n"
    if write:
        open(OUT, "w").write(text)
        print("wrote", OUT, len(rows), "twins")
    else:
        old = open(OUT).read() if os.path.exists(OUT) else ""
        if old != text:
            bad += 1
            print("BAD: %s is out of date (run with --write)" % OUT)
    print("sem_twins: %d twins, %d failures" % (len(rows), bad))
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
