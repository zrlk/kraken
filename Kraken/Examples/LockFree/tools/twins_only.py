#!/usr/bin/env python3
# The `only [...]` lists of the TWINS clone modules.
# Run from the repository root, after `lake build`:
#   python3 Kraken/Examples/LockFree/tools/twins_only.py           # check
#   python3 Kraken/Examples/LockFree/tools/twins_only.py --write   # rewrite the lists
#
# `Kraken/Promising/SLR/ChainK/TwinsClone*.lean` call
#   #chaink_clone' "../../SLR/<M>.lean" only ["d1", ...]
# for every module M of the dependency closure of the `#sem_twin` targets
# (`ChainK/SemTwins{A64,X64}.lean`). A listed name that the clone walk never
# clones is a build error, and so is (in general) a missing one, so the lists
# must be exactly what the twins need. This script computes them:
#
# 1. A generated Lean file per ISA (`.lake/twins_only/dump_<side>.lean`, run
#    through `lake env lean`, importing `ChainK.SemTwins<side>`) dumps
#    - every `Kraken.*` constant with its module (`C` rows);
#    - the executable-machine taint of `ChainK/Clone`'s gate (`T`
#      rows: name, module, the tainted constants of its type, and the
#      constants of its value that are tainted, have a tainted type, or are
#      `succs_cases`), private constants included;
#    - the old names of the hand-written K-world twins `ChainK.kTwins` (`W`).
# 2. From each target, a walk through `T` rows (value and type references)
#    collects the constants the twin needs. It stops at the machine atoms
#    and at *twinned* constants: those with a K counterpart (`K` appended to
#    one component of the name) defined outside the TWINS modules (the
#    K-world chain hubs, `TicketA64Demo`, ...), and the `kTwins` old names.
# 3. For each `#chaink_clone'` command of module M, the list is the
#    declarations of M's source (names as written, in source order) whose
#    last component is the last component of a collected constant of M.
#
# Check mode (default) compares every list with the computed one, and also
# reports collected modules that no clone command covers (unless listed in
# EXEMPT) and clone commands whose module collected nothing. Exit status 1
# on any difference. `--write` rewrites the lists in place (the module order
# and the split into files are left alone).
import collections, os, re, subprocess, sys

CK = "Kraken/Promising/SLR/ChainK"
P = "Kraken.Promising."
LAKE = os.environ.get("LAKE", "lake")
SIDES = [("a64", P + "SLR.ChainK.SemTwinsA64", CK + "/SemTwinsA64.lean"),
         ("x64", P + "SLR.ChainK.SemTwinsX64", CK + "/SemTwinsX64.lean")]
# Modules that the walk may reach but that are deliberately not cloned
# (module -> reason). Empty today: every module the walk reaches is either
# cloned or stopped at by a hand-written twin.
EXEMPT = {}
ATOMS = {P + x for x in ["Reachable", "succs", "succs_cases", "SLR.Path", "Config.Live", "succsL",
                         "succsR", "certify", "certifiedPromises", "Step"]}

DUMP = r'''
open Lean Meta Elab Command

/-- TWINS `only`-list dump (`Kraken/Examples/LockFree/tools/twins_only.py`). -/
elab "#twins_only_dump" : command => do
  let env ← getEnv
  let atomsS := [`Kraken.Promising.succs, `Kraken.Promising.succsL, `Kraken.Promising.succsR,
    `Kraken.Promising.certify, `Kraken.Promising.certifiedPromises, `Kraken.Promising.Reachable,
    `Kraken.Promising.Step]
  for a in atomsS do
    unless env.contains a do throwError "missing atom {a}"
  let user (n : Name) : Name := (privateToUserName? n).getD n
  let isK (n : Name) : Bool := (user n).getRoot == `Kraken
  let modOf (n : Name) : String := match env.getModuleIdxFor? n with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none => "?"
  let consts := env.constants.map₁.toList.filter (fun (n, _) => isK n)
  -- the executable machine: atoms, closed under "type, value or constructor mentions"
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ci) in consts do
    if ci matches .thmInfo _ then continue
    let mut deps : NameSet := ci.type.getUsedConstantsAsSet
    if let some v := ci.value? (allowOpaque := true) then
      deps := v.getUsedConstants.foldl (·.insert ·) deps
    if let .inductInfo ii := ci then
      for c in ii.ctors do
        if let some cc := env.find? c then
          deps := cc.type.getUsedConstants.foldl (·.insert ·) deps
    for d in deps do
      rev := rev.insert d ((rev.getD d #[]).push n)
  let mut tainted : NameSet := {}
  let mut work : Array Name := atomsS.toArray
  for a in atomsS do tainted := tainted.insert a
  while 0 < work.size do
    let n := work.back!
    work := work.pop
    for m in rev.getD n #[] do
      unless tainted.contains m do
        tainted := tainted.insert m
        work := work.push m
  let mut tthm : NameSet := {}
  for (n, ci) in consts do
    if ci matches .thmInfo _ then
      if ci.type.getUsedConstants.any tainted.contains then tthm := tthm.insert n
  let interesting (d : Name) : Bool :=
    tainted.contains d || tthm.contains d || d == `Kraken.Promising.succs_cases
  let s (a : Array Name) : String := ",".intercalate ((a.map toString).qsort (· < ·)).toList
  let mut out : Array String := #[]
  for (n, ci) in consts do
    let u := user n
    unless u.isInternalDetail do out := out.push s!"C\t{u}\t{modOf n}"
    if ci matches .recInfo _ then continue
    let ty := ci.type.getUsedConstants.filter tainted.contains
    let vr : Array Name := match ci with
      | .thmInfo ti => ti.value.getUsedConstants.filter interesting
      | .defnInfo di => di.value.getUsedConstants.filter interesting
      | _ => #[]
    if 0 < ty.size || 0 < vr.size then
      out := out.push s!"T\t{n}\t{modOf n}\t{s ty}\t{s vr}"
  for (a, _) in Kraken.Promising.ChainK.kTwins do
    out := out.push s!"W\t{a}"
  for (a, b) in Kraken.Promising.ChainK.kBase do
    out := out.push s!"B\t{a}\t{b}"
  IO.FS.writeFile "OUTFILE" ("\n".intercalate out.toList ++ "\n")

#twins_only_dump
'''


def user(n):
    m = re.match(r"^_private\.(?:.*?)\.0\.(.*)$", n)
    return m.group(1) if m else n


def dump(side, imp):
    os.makedirs(".lake/twins_only", exist_ok=True)
    f = ".lake/twins_only/dump_%s.lean" % side
    o = os.path.abspath(".lake/twins_only/dump_%s.tsv" % side)
    with open(f, "w") as h:
        h.write("import %s\n" % imp + DUMP.replace("OUTFILE", o))
    r = subprocess.run([LAKE, "env", "lean", f], capture_output=True, text=True)
    if r.returncode != 0:
        sys.stdout.write(r.stdout + r.stderr)
        sys.exit("twins_only: lean failed on %s" % f)
    C, T, W, B = {}, {}, [], {}
    for l in open(o):
        x = l.rstrip("\n").split("\t")
        if x[0] == "C":
            C[x[1]] = x[2]
        elif x[0] == "T":
            T[x[1]] = (x[2], [y for y in x[3].split(",") if y] + [y for y in x[4].split(",") if y])
        elif x[0] == "W":
            W.append(x[1])
        elif x[0] == "B" and x[1] != x[2] and "." not in x[1]:
            B[x[1]] = x[2]
    return C, T, W, B


def is_clone_mod(m):
    last = m.split(".")[-1]
    return m.startswith(P + "SLR.ChainK.") and (last.startswith("TwinsClone") or last.startswith("SemTwins"))


def collect(side, imp, path):
    """Module -> constants (full names) that the twins of `path` need."""
    C, T, W, B = dump(side, imp)
    korig = set()
    for a in W:
        if P + a in C:
            korig.add(P + a)
        else:
            korig |= {n for n in C if n.endswith("." + a)}

    def twinned(n):
        u = user(n)
        if u in korig:
            return True
        cs = u.split(".")
        for i in range(2, len(cs)):
            for c in {cs[i] + "K", B.get(cs[i], cs[i] + "K")}:
                v = ".".join(cs[:i] + [c] + cs[i + 1:])
                if v in C and not is_clone_mod(C[v]):
                    return True
        return False

    targets = [l.split()[1] for l in open(path) if l.startswith("#sem_twin ")]
    seen, acc = set(), set()

    def walk(n):
        stack = [n]
        while stack:
            n = stack.pop()
            if n in seen:
                continue
            seen.add(n)
            if n in ATOMS or twinned(n):
                continue
            base = re.sub(r"\.(match_\d+|proof_\d+|_proof_\d+|eq_\d+)$", "", n)
            if base != n:
                stack.append(base)
                continue
            if n not in T:
                continue
            acc.add(n)
            stack.extend(T[n][1])

    need = collections.defaultdict(set)
    for t in targets:
        if t not in T:
            sys.exit("twins_only: target %s is not tainted (%s)" % (t, side))
        need[T[t][0]].add(t)
        walk(t)
    for a in acc:
        need[T[a][0]].add(a)
    return need


DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*"
                  r"(?:theorem|def|lemma|abbrev|structure|inductive|instance|class)\s+([^\s:({\[]+)", re.M)
CMD = re.compile(r'#chaink_clone\' "([^"]+)"((?:\s+skip \[[^\]]*\])?)(\s+only \[([^\]]*)\])((?:\s+keep_names \[[^\]]*\])?)')


def mod_of(rel):
    p = os.path.normpath(os.path.join(CK, rel))
    return p[:-len(".lean")].replace("/", "."), p


def main():
    write = "--write" in sys.argv
    need = collections.defaultdict(set)
    for side, imp, path in SIDES:
        for m, s in collect(side, imp, path).items():
            need[m] |= s
    files = sorted(os.path.join(CK, f) for f in os.listdir(CK) if f.startswith("TwinsClone") and f.endswith(".lean"))
    bad = 0
    covered = set()
    for fn in files:
        src = open(fn).read()

        def fix(mt):
            nonlocal bad
            m, p = mod_of(mt.group(1))
            covered.add(m)
            old = re.findall(r'"([^"]*)"', mt.group(4))
            nd = {user(x).split(".")[-1] for x in need.get(m, ())}
            new = [d for d in DECL.findall(open(p).read()) if d.split(".")[-1] in nd]
            if not new:
                bad += 1
                print("BAD %s: %s collects nothing" % (fn, m))
            if sorted(new) != sorted(old):
                bad += 1
                print("DIFF %s %s\n  file:     %s\n  computed: %s" % (fn, m, old, new))
                if write:
                    # keep the file's order for names that stay; append the new ones
                    new = [x for x in old if x in new] + [x for x in new if x not in old]
                    return mt.group(0).replace(mt.group(3), "\n  only [" + ", ".join('"%s"' % x for x in new) + "]")
            return mt.group(0)
        out = CMD.sub(fix, src)
        if write and out != src:
            open(fn, "w").write(out)
            print("wrote", fn)
    for m in sorted(set(need) - covered):
        if m in EXEMPT:
            continue
        if is_clone_mod(m):
            continue
        bad += 1
        print("BAD uncovered module %s: %s" % (m, ", ".join(sorted(user(x).split(".")[-1] for x in need[m]))))
    print("twins_only: %d clone commands in %d files, %d differences" % (len(covered), len(files), bad))
    sys.exit(1 if bad and not write else 0)


if __name__ == "__main__":
    main()
