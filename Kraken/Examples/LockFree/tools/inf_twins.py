# The fuel-free (`ReachableSemInf`) twins gate and listing.
# Run from the repository root, after `lake build`:
#   python3 Kraken/Examples/LockFree/tools/inf_twins.py           # check
#   python3 Kraken/Examples/LockFree/tools/inf_twins.py --write   # regenerate INF_TWINS.md
#   python3 Kraken/Examples/LockFree/tools/inf_twins.py --gen     # regenerate the twin modules
#
# `--gen` writes `Kraken/Promising/SLR/ChainK/InfTwins{A64,X64}.lean`: one
# `#inf_twin` (`ChainK/InfTwin.lean`) per twin listed in SEM_TWINS.md.
#
# The check: for every twin `u` of the modules `TWIN_MODULES` named
# `semInfName t` for an existing `t`, a generated Lean file checks,
# independently of `ChainK/InfTwin.lean` (its own `infType`, on de Bruijn
# indices rather than free variables):
#   - type(u) == infType(type(t)), where infType drops the first `∀ fuel : Nat`
#     binder whose variable is the fuel argument of a `ReachableSem` or
#     `Config.FaultFreeSem`, replaces `ReachableSem A fuel c c'` by
#     `ReachableSemInf A c c'` and `Config.FaultFreeSem A fuel i` by
#     `Config.FaultFreeSemInf A i`, and fails if the fuel occurs elsewhere;
#   - type(u) mentions none of `Reachable`, `Config.FaultFree`,
#     `ReachableSem`, `Config.FaultFreeSem`;
#   - u's axioms are among propext, Classical.choice, Quot.sound.
# Then: every `t` is a twin listed in SEM_TWINS.md, and every twin listed
# there has its fuel-free twin. It writes (--write) or compares (default) the
# listing INF_TWINS.md. Exit status 1 on any failure.
import os, re, subprocess, sys

LF = "Kraken/Examples/LockFree"
OUT = LF + "/INF_TWINS.md"
SEM = LF + "/SEM_TWINS.md"
LAKE = os.environ.get("LAKE", "lake")
SIDES = [("AArch64", "A64"), ("X64", "X64")]
MOD = "Kraken.Promising.SLR.ChainK.InfTwins%s"

CHECK = r'''
open Lean Meta Elab Command

namespace InfTwinsCheck

/-- `semInfName`: `_sem` ↦ `_semInf` at the twin's `_sem` (before
`_concrete`, or at the end before primes). -/
def semInfName : Name → Name
  | .str p s =>
    match s.splitOn "_sem_concrete" with
    | a :: b :: rest => .str p (a ++ "_semInf_concrete" ++ "_sem_concrete".intercalate (b :: rest))
    | _ =>
      let core := String.ofList (s.toList.reverse.dropWhile (· == '\'')).reverse
      let pr := String.ofList (s.toList.drop core.length)
      if core.endsWith "_sem" then .str p (core ++ "Inf" ++ pr) else .str p (core ++ "_semInf" ++ pr)
  | n => n

/-- Replace the uses of the fuel `bvar k`. -/
partial def sub (k : Nat) (e : Expr) : Expr :=
  match e with
  | .app .. =>
    let f := e.getAppFn
    let a := e.getAppArgs
    let xs := a.map (sub k)
    if f.isConstOf ``Kraken.Promising.Live.Bridge.ReachableSem && a.size == 5 && a[2]! == .bvar k then
      mkAppN (.const ``Kraken.Promising.Live.Inf.ReachableSemInf f.constLevels!) #[xs[0]!, xs[1]!, xs[3]!, xs[4]!]
    else if f.isConstOf ``Kraken.Promising.Config.FaultFreeSem && a.size == 4 && a[2]! == .bvar k then
      mkAppN (.const ``Kraken.Promising.Config.FaultFreeSemInf f.constLevels!) #[xs[0]!, xs[1]!, xs[3]!]
    else mkAppN (sub k f) xs
  | .forallE n d b bi => .forallE n (sub k d) (sub (k + 1) b) bi
  | .lam n d b bi => .lam n (sub k d) (sub (k + 1) b) bi
  | .letE n t v b nd => .letE n (sub k t) (sub k v) (sub (k + 1) b) nd
  | .mdata m b => .mdata m (sub k b)
  | .proj s i b => .proj s i (sub k b)
  | _ => e

/-- The fuel-free statement, or `none`. -/
partial def infType : Expr → Option Expr
  | .forallE n d b bi =>
    let b' := sub 0 b
    if d.isConstOf ``Nat && b' != b then
      if b'.hasLooseBVar 0 then none else some (b'.lowerLooseBVars 1 1)
    else (infType b).map (.forallE n d · bi)
  | .mdata _ b => infType b
  | _ => none

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

elab "#inf_twins_check " side:str mods:str* : command => do
  let env ← getEnv
  let mods := mods.map (·.getString.toName)
  let idxs := mods.filterMap env.getModuleIdx?
  unless idxs.size == mods.size do throwError "inf_twins_check: module not imported"
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := [``Kraken.Promising.Reachable, ``Kraken.Promising.Config.FaultFree,
    ``Kraken.Promising.Live.Bridge.ReachableSem, ``Kraken.Promising.Config.FaultFreeSem]
  for (u, ci) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? u | continue
    unless idxs.contains i do continue
    let .str p s := u | continue
    let parts := s.splitOn "Inf"
    -- every way of deleting one `Inf` from the last component
    let cands := (List.range (parts.length - 1)).map fun k =>
      Name.str p ("Inf".intercalate (parts.take (k + 1)) ++ "Inf".intercalate (parts.drop (k + 1)))
    let some t := cands.find? (fun t => env.contains t && semInfName t == u) | continue
    let ct := (env.find? t).get!
    let mut errs : Array String := #[]
    match infType ct.type with
    | none => errs := errs.push "no fuel binder, or the fuel has another use"
    | some tI => if tI != ci.type then errs := errs.push "type ≠ infType(type of the sem twin)"
    if (ci.type.find? fun x => bad.any x.isConstOf).isSome then
      errs := errs.push "mentions Reachable/FaultFree/ReachableSem/FaultFreeSem"
    let axs ← liftCoreM <| collectAxioms u
    if axs.any (fun a => !ok.contains a) then errs := errs.push s!"axioms {axs}"
    let sig ← liftTermElabM do return oneLine ((← ppExpr ci.type).pretty 100000)
    IO.println s!"TWIN\t{side.getString}\t{u}\t{t}\t{if errs.isEmpty then "OK" else ", ".intercalate errs.toList}\t{sig}"

/-- The `…SemU` ↦ `…SemInf` constants of `#semU_inf_twin`. -/
def uConsts : List (Name × Name) :=
  [(``Kraken.Promising.Live.CertBounded.TermBoundSemU, ``Kraken.Promising.Live.Inf.TermBoundSemInf),
   (``Kraken.Promising.Live.CertBounded.LiveFromSemU, ``Kraken.Promising.Live.Inf.LiveFromSemInf),
   (``Kraken.Promising.Live.CertBounded.ProgressFromSemU, ``Kraken.Promising.Live.Inf.ProgressFromSemInf),
   (``Kraken.Promising.Live.CertBounded.TermFromSemU, ``Kraken.Promising.Live.Inf.TermFromSemInf),
   (``Kraken.Promising.Live.CertBounded.WeakFairSemU, ``Kraken.Promising.Live.Inf.WeakFairSemInf)]

/-- The headline's statement: head definitions named `…SemU` unfolded under
`∀`/`∧`, then the `uConsts` replaced in the conclusions. -/
partial def uType (env : Environment) (e : Expr) : Expr :=
  let e := e.consumeMData
  let e := match e.getAppFn with
    | .const n us =>
      if n.toString.endsWith "SemU" && !(uConsts.any (·.1 == n)) then
        match env.find? n with
        | some (.defnInfo d) => (d.value.instantiateLevelParams d.levelParams us).beta e.getAppArgs
        | _ => e
      else e
    | _ => e
  match e with
  | .forallE n d b bi => .forallE n d (uType env b) bi
  | _ =>
    if e.isAppOfArity ``And 2 then mkApp2 (.const ``And []) (uType env (e.getArg! 0)) (uType env (e.getArg! 1))
    else e.replace fun
      | .const n us => (uConsts.lookup n).map (.const · us)
      | _ => none

elab "#semU_inf_check " side:str mods:str* : command => do
  let env ← getEnv
  let mods := mods.map (·.getString.toName)
  let idxs := mods.filterMap env.getModuleIdx?
  unless idxs.size == mods.size do throwError "semU_inf_check: module not imported"
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  for (u, ci) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? u | continue
    unless idxs.contains i do continue
    let .str p s := u | continue
    let parts := s.splitOn "_semInf"
    unless parts.length == 2 do continue
    let t := Name.str p (parts[0]! ++ "_semU" ++ parts[1]!)
    let some ct := env.find? t | continue
    let mut errs : Array String := #[]
    if uType env ct.type != ci.type then errs := errs.push "type ≠ uType(type of the semU theorem)"
    if (ci.type.find? fun x => uConsts.any (x.isConstOf ·.1)).isSome then
      errs := errs.push "mentions a …SemU predicate"
    if !(ci.type.find? fun x => uConsts.any (x.isConstOf ·.2)).isSome then
      errs := errs.push "mentions no …SemInf predicate"
    let axs ← liftCoreM <| collectAxioms u
    if axs.any (fun a => !ok.contains a) then errs := errs.push s!"axioms {axs}"
    let sig ← liftTermElabM do return oneLine ((← ppExpr ci.type).pretty 100000)
    IO.println s!"HEAD\t{side.getString}\t{u}\t{t}\t{if errs.isEmpty then "OK" else ", ".intercalate errs.toList}\t{sig}"

end InfTwinsCheck
'''
HEAD_MOD = "Kraken.Promising.LiveCertBoundedInf"
# The modules of `#semU_inf_twin` headlines, per side (the ticket locks; ticketlock_loop; treiber_pp A64; x64 ticket2).
HEAD_MODS = {"AArch64": [HEAD_MOD, "Kraken.Promising.LiveCertBoundedInfTicket",
                         "Kraken.Promising.LiveCertBoundedInfTicketLoop", "Kraken.Promising.LiveCertBoundedInfTreiberPpA64"], "X64": ["Kraken.Promising.LiveCertBoundedInfCmpx", "Kraken.Promising.LiveCertBoundedInfTicketX64", "Kraken.Promising.LiveCertBoundedInfTicket2X64"]}

HDR = '''/-
**The fuel-free twins of the {isa} `ReachableSem` twins**
(generated by `tools/inf_twins.py --gen`; additive). For each `#sem_twin`
twin `n_sem` of `ChainK/SemTwins{sfx}.lean` (listing `SEM_TWINS.md`),
`#inf_twin` (`ChainK/InfTwin.lean`) adds `n_semInf`: the same statement on
the fuel-free semantic machine (`LiveSemInf.lean`), with the `∀ fuel` binder
dropped, `ReachableSem A fuel` ↦ `ReachableSemInf A` and
`Config.FaultFreeSem A fuel` ↦ `Config.FaultFreeSemInf A`. Listing:
`Kraken/Examples/LockFree/INF_TWINS.md` (checked by `tools/inf_twins.py`).
-/
import Kraken.Promising.SLR.ChainK.SemTwins{sfx}
import Kraken.Promising.SLR.ChainK.InfTwin

'''

def sem_listing():
    names = {"AArch64": [], "X64": []}
    side = None
    for sd, n in re.findall(r"^## (\w+)$|^- `([^`]+)` \(twin of", open(SEM).read(), re.M):
        if sd:
            side = sd
        else:
            names[side].append("Kraken.Promising." + n)
    return names

def gen():
    names = sem_listing()
    for side, sfx in SIDES:
        with open("Kraken/Promising/SLR/ChainK/InfTwins%s.lean" % sfx, "w") as h:
            h.write(HDR.format(isa=side, sfx=sfx))
            for n in names[side]:
                h.write("#inf_twin %s\n" % n)
        print("wrote InfTwins%s.lean: %d twins" % (sfx, len(names[side])))

def run_side(side, sfx):
    os.makedirs(".lake/docs", exist_ok=True)
    f = ".lake/docs/inf_twins_%s.lean" % side
    hmods = HEAD_MODS[side]
    with open(f, "w") as h:
        h.write("import %s\n" % (MOD % sfx) + "".join("import %s\n" % m for m in hmods) + CHECK +
                '\nopen Kraken Kraken.Promising Kraken.Promising.Live.Bridge Kraken.Promising.Live.Inf\n'
                '#inf_twins_check "%s" "%s"\n' % (side, MOD % sfx) +
                ('#semU_inf_check "%s" %s\n' % (side, " ".join('"%s"' % m for m in hmods)) if hmods else ""))
    r = subprocess.run([LAKE, "env", "lean", f], capture_output=True, text=True)
    rows = [l.split("\t") for l in r.stdout.splitlines() if l.startswith(("TWIN\t", "HEAD\t"))]
    if r.returncode != 0:
        sys.stdout.write(r.stdout + r.stderr)
        sys.exit("inf_twins: lean failed on %s" % f)
    return rows

def main():
    if "--gen" in sys.argv:
        gen()
        return
    write = "--write" in sys.argv
    listed = sem_listing()
    allrows = []
    for side, sfx in SIDES:
        allrows += run_side(side, sfx)
    rows = [r for r in allrows if r[0] == "TWIN"]
    heads = [r for r in allrows if r[0] == "HEAD"]
    bad = 0
    for r in allrows:
        kind, side, u, t, st, sig = r
        if kind == "TWIN" and t not in listed[side]:
            st = (st + ", " if st != "OK" else "") + "sem twin not in SEM_TWINS.md"
        if st != "OK":
            bad += 1
            print("BAD", u, ":", st)
    have = {(r[1], r[3]) for r in rows}
    for side, _ in SIDES:
        for t in listed[side]:
            if (side, t) not in have:
                bad += 1
                print("BAD: no fuel-free twin of", t)
    rows.sort(key=lambda r: (r[1], r[2]))
    heads.sort(key=lambda r: r[2])
    sh = lambda n: n[len("Kraken.Promising."):] if n.startswith("Kraken.Promising.") else n
    lines = ["# Fuel-free (`ReachableSemInf`) twins of the published theorems",
             "",
             "Generated by `python3 Kraken/Examples/LockFree/tools/inf_twins.py --write`; do not edit.",
             "Each twin `n_semInf` (`ChainK/InfTwin.lean`, `#inf_twin`) has the statement of the",
             "`ReachableSem` twin `n_sem` (SEM_TWINS.md) with the `∀ fuel` binder dropped,",
             "`ReachableSem A fuel c₀ c` replaced by `ReachableSemInf A c₀ c` and",
             "`Config.FaultFreeSem A fuel` by `Config.FaultFreeSemInf A`: the statement on the",
             "fuel-free semantic machine (`Promising/LiveSemInf.lean`), the lowering target.",
             "`inf_twins.py` re-checks every line. Names are relative to `Kraken.Promising`;",
             "statements are printed with",
             "`open Kraken Kraken.Promising Kraken.Promising.Live.Bridge Kraken.Promising.Live.Inf`.",
             "",
             "%d twins (AArch64 %d, X64 %d); %d liveness/termination headlines." % (
                 len(rows), sum(r[1] == "AArch64" for r in rows), sum(r[1] == "X64" for r in rows), len(heads)),
             ""]
    side = None
    for r in rows:
        if r[1] != side:
            side = r[1]
            lines += ["", "## " + side, ""]
        lines.append("- `%s` (twin of `%s`): `%s`" % (sh(r[2]), sh(r[3]), r[5]))
    lines += ["", "## Headlines (AArch64)", "",
              "`#semU_inf_twin` (`Promising/LiveCertBoundedInf.lean`; `treiber_pp`:",
              "`Promising/LiveCertBoundedInfTreiberPpA64.lean`): the fuel-free CertBounded",
              "headlines `n_semU…` restated on the Inf machine as `n_semInf…` (`TermBoundSemU`,",
              "`LiveFromSemU`, `ProgressFromSemU`, `TermFromSemU`, `WeakFairSemU` ↦ `…SemInf`; head",
              "definitions named `…SemU` unfolded). No extra hypothesis.", ""]
    for r in heads:
        if r[1] == "AArch64":
            lines.append("- `%s` (from `%s`): `%s`" % (sh(r[2]), sh(r[3]), r[5]))
    xheads = [r for r in heads if r[1] == "X64"]
    if xheads:
        lines += ["", "## Headlines (X64)", "",
                  "As above, x64 side (`Promising/LiveCertBoundedInfCmpx.lean`: the `lock cmpxchg` spinlock;", "`Promising/LiveCertBoundedInfTicketX64.lean`: ticket3). No extra hypothesis.", ""]
        for r in xheads:
            lines.append("- `%s` (from `%s`): `%s`" % (sh(r[2]), sh(r[3]), r[5]))
    text = "\n".join(lines) + "\n"
    if write:
        open(OUT, "w").write(text)
        print("wrote", OUT, len(rows), "twins")
    else:
        old = open(OUT).read() if os.path.exists(OUT) else ""
        if old != text:
            bad += 1
            print("BAD: %s is out of date (run with --write)" % OUT)
    print("inf_twins: %d twins, %d headlines, %d failures" % (len(rows), len(heads), bad))
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
