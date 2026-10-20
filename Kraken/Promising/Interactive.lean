/-
An interactive stepper over the Promising machine, in the spirit of the
Promising-ARM tool's interactive mode: show the configuration, list the
transitions a thread may take (instruction outcomes with the timestamps
they read and write, certified promises), take one, undo.

Commands:
  s            show the configuration (threads, views, promises, memory)
  t N          list the transitions of thread N
  t N k        take transition k of thread N
  p N          list the certified promises of thread N
  p N k        take promise k of thread N
  u            undo the last transition
  a            list every transition (all threads)
  q            quit
-/
import Kraken.Promising.Machine

namespace Kraken.Promising

structure Session (I : ISA) where
  A : Arch
  opts : ExploreOpts
  locName : Loc → String
  history : List (Config I × List TraceEv)
  current : Config I
  cache : CertCache I := {}

namespace Session

variable {I : ISA}

def showViews (v : Views) : String :=
  s!"vrNew={v.vrNew} vwNew={v.vwNew} vrOld={v.vrOld} vwOld={v.vwOld} vCAP={v.vCAP} vRel={v.vRel}"
    -- only `noRet` atomics (`STADD`, ...) raise it; shown when they have
    ++ (if v.vrOldNR != 0 then s!" vrOldNR={v.vrOldNR}" else "")
    ++ (if v.vwOldNT != 0 then s!" vwOldNT={v.vwOldNT}" else "")
    ++ (match v.xclb with | some (t, _, _) => s!" xclb@{t}" | none => "")

def showConfig (s : Session I) : String := Id.run do
  let mut out := ""
  let c := s.current
  out := out ++ "memory:\n  @0: initial" ++ (if c.mem.init.isEmpty then "" else
    " " ++ " ".intercalate (c.mem.init.map fun (l, v) => s!"{s.locName l}={v.toNat}")) ++ "\n"
  for (w, i) in c.mem.msgs.toList.zipIdx do
    out := out ++ s!"  @{i + 1}: {s.locName w.loc}={w.val.toNat} (P{w.tid})\n"
  for (t, tid) in c.threads.toList.zipIdx do
    let next := if t.halted then "halted" else I.showInstr t.st
    let coh := " ".intercalate (t.views.coh.map fun (l, v) => s!"{s.locName l}:{v}")
    out := out ++ s!"P{tid}: {next}\n    {showViews t.views}\n    coh[{coh}] prom={t.prom}\n"
  return out

/-- The transitions of one thread, with descriptions. -/
def transitions (s : Session I) (tid : Nat) : List (Config I × List TraceEv) × CertCache I :=
  let c := s.current
  let steps := match stepThread s.A c tid with
    | none => []
    | some outs => outs.filterMap fun
      | .ok o => some (c.withThread tid o.thread o.mem, o.log)
      | .error _ => none
  (steps, s.cache)

def promises (s : Session I) (tid : Nat) : List (Config I × List TraceEv) × CertCache I :=
  let (ps, _, cache) := certifiedPromises s.A s.cache s.current tid s.opts.fuel
  (ps.map fun (c, e) => (c, [e]), cache)

def describe (s : Session I) (tr : List TraceEv) : String :=
  " | ".intercalate (tr.map fun ev => (TraceEv.format s.locName ev).trimAscii.copy)

partial def repl (s : Session I) : IO Unit := do
  IO.print "> "
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.isEmpty then return   -- EOF
  let ws := (line.trimAscii.copy.splitOn " ").filter (· ≠ "")
  let pick (items : List (Config I × List TraceEv)) (k : Option Nat) (cache : CertCache I) : IO Unit := do
    match k with
    | none =>
      if items.isEmpty then IO.println "  (none)"
      for (it, i) in items.zipIdx do IO.println s!"  {i}: {s.describe it.2}"
      repl { s with cache }
    | some k =>
      match items[k]? with
      | some (c', ev) =>
        IO.println s!"  took: {s.describe ev}"
        let s' := { s with history := (s.current, ev) :: s.history, current := c', cache }
        if c'.final then IO.println "  (final configuration)"
        repl s'
      | none => IO.println "  no such transition"; repl { s with cache }
  match ws with
  | ["q"] => return
  | ["s"] => IO.print s.showConfig; repl s
  | ["u"] =>
    match s.history with
    | (c, _) :: h => repl { s with current := c, history := h }
    | [] => IO.println "  nothing to undo"; repl s
  | ["a"] =>
    let (all, cache) := (List.range s.current.threads.size).foldl (init := ([], s.cache)) fun (acc, cache) tid =>
      let (ts, cache) := ({ s with cache }).transitions tid
      let (ps, cache) := ({ s with cache }).promises tid
      (acc ++ ts ++ ps, cache)
    pick all none cache
  | "t" :: n :: rest =>
    match n.toNat? with
    | some tid =>
      let (ts, cache) := s.transitions tid
      pick ts (rest.head?.bind String.toNat?) cache
    | none => IO.println "  usage: t N [k]"; repl s
  | "p" :: n :: rest =>
    match n.toNat? with
    | some tid =>
      let (ps, cache) := s.promises tid
      pick ps (rest.head?.bind String.toNat?) cache
    | none => IO.println "  usage: p N [k]"; repl s
  | _ => IO.println "  commands: s | t N [k] | p N [k] | a | u | q"; repl s

end Session

/-- Start an interactive session from an initial configuration. -/
def interactive {I : ISA} (A : Arch) (opts : ExploreOpts) (locName : Loc → String) (c0 : Config I) : IO Unit := do
  IO.println "Promising machine. Commands: s (show) | t N [k] (thread transitions) | p N [k] (promises) | a | u (undo) | q"
  let s : Session I := { A, opts, locName, history := [], current := c0 }
  IO.print s.showConfig
  s.repl

end Kraken.Promising
