import WeakCore.TermLiveCert
import WeakCore.TermLive
/-! # TermLiveCertGen — the untrusted certificate generator (item 38 v1)

Breadth-first over `movesPF` (POR off, promise-free), configurations identified by `cfgKey` (derived `BEq`/`Hashable`;
nothing here is trusted: `TermLiveCert.check` re-derives everything). Ranks are `TermLive.sccs` numbers of the quiet
subgraph; a rank's justification is chosen by the criterion `check` verifies. -/

namespace TermLiveCert
open CoreLang CoreTerm TermRun
open WeakMem (Arch)

/-- The certificate for `c0` (at most `fuel` nodes expanded), crash set `X`, device value set `V`. -/
def certOf (p : Prog) (k : Promises.Knobs) (arch : Arch) (X : List Nat) (V : List Nat) (fuel : Nat) (c0 : Cfg) : Cert := Id.run do
  let mut ids : Std.HashMap CfgKey Nat := Std.HashMap.emptyWithCapacity.insert (cfgKey c0) 0
  let mut nodes : Array Cfg := #[c0]
  let mut succ : Array (Array (List Nat)) := #[]
  let mut envs : Array (List Nat) := #[]
  let mut v := 0
  while v < nodes.size && v < fuel do
    let c := canon nodes[v]!
    let mut row : Array (List Nat) := #[]
    for i in List.range c.ths.size do
      let mut ws : List Nat := []
      for e in movesPF p k arch V c i do
        match ids.get? (cfgKey e) with
        | some w => ws := w :: ws
        | none =>
          ids := ids.insert (cfgKey e) nodes.size
          ws := nodes.size :: ws
          nodes := nodes.push e
      row := row.push ws.reverse
    succ := succ.push row
    let mut er : List Nat := []
    for e in envsPF p k arch c do
      match ids.get? (cfgKey e) with
      | some w => er := w :: er
      | none =>
        ids := ids.insert (cfgKey e) nodes.size
        er := nodes.size :: er
        nodes := nodes.push e
    envs := envs.push er.reverse
    v := v + 1
  let pre : Cert := ⟨nodes, succ, #[], #[], envs⟩
  let n := nodes.size
  let q : Array Bool := (Array.range n).map fun v => pre.quiet p k arch X V v
  let qe : Array (List Nat) := (Array.range n).map fun v =>
    if q[v]! then ((List.range (pre.nd v).ths.size).flatMap (pre.tg v) ++ pre.te v).filter (q[·]!) else []
  let comp := TermLive.sccs qe
  let ncomp := comp.foldl max 0 + 1
  -- per rank: labels of inside edges; threads disabled at some quiet node of the rank
  let mut ins : Array (List Nat) := Array.replicate ncomp []
  let mut dis : Array (List Nat) := Array.replicate ncomp []
  let mut mx := 0
  for u in [0:n] do
    if q[u]! then
      let c := pre.nd u
      mx := max mx c.ths.size
      for i in List.range c.ths.size do
        if (movesPF p k arch V c i).isEmpty then dis := dis.set! comp[u]! (i :: dis[comp[u]!]!)
        for w in pre.tg u i do
          if q[w]! && comp[w]! == comp[u]! then ins := ins.set! comp[u]! (i :: ins[comp[u]!]!)
  let js : Array Just := (Array.range ncomp).map fun r =>
    if ins[r]!.isEmpty then .noSpin
    else match (List.range mx).find? (fun i => !X.contains i && !dis[r]!.contains i && !ins[r]!.contains i) with
      | some i => .unfair i
      | none => .noSpin
  return ⟨nodes, succ, comp, js, envs⟩

end TermLiveCert

/-! Smoke: the generator's certificate for the mutex scenarios is accepted with no crash set (and has no spawn move
and no stuck node), and rejected with thread 0 in the crash set (a spinning thread then has no fair blocker). -/

open CoreLang CoreTerm TermLiveCert TermSmoke TermRun in
#guard mSetup.all fun s =>
  let c0 := spawn s (mThr s)
  let ct := certOf mutexLib Promises.Knobs.all .arm [] [] 100000 c0
  check mutexLib Promises.Knobs.all .arm [] [] ct c0 && noSpawnB ct && noStuckB mutexLib Promises.Knobs.all .arm [] ct

open CoreLang CoreTerm TermLiveCert TermSmoke TermRun in
#guard mSetup.all fun s =>
  let c0 := spawn s (mThr s)
  let ct := certOf mutexLib Promises.Knobs.all .arm [0] [] 100000 c0
  !check mutexLib Promises.Knobs.all .arm [0] [] ct c0
