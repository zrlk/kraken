import WeakCore.TermLiveMachE
import WeakCore.TermSpawnSuccs
/-! # TermLiveCert — item 38 v1: the certificate and its checker (definitions)

The theorem statements are in
`TermLiveCertRun`. The `DecidableEq` instances below are global (a scoped variant is not possible
with `deriving`: `attribute [-instance]` does not persist to importers). -/

namespace TermLiveCert
open CoreLang CoreTerm TermRun TermLiveMach TermLiveL3 TermProgress TermLiveProps
open WeakMem (Arch Address Val)

deriving instance DecidableEq for Promises.TVal, WeakMem.Msg
deriving instance DecidableEq for Op, Expr
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
deriving instance DecidableEq for ThKey
deriving instance DecidableEq for CfgKey

/-- The addresses in memory. -/
def locs (c : Cfg) : List Address := (c.mem.toList.map (·.loc)).eraseDups

/-- `c` with every coherence view zeroed off `locs c` (where `CfgCoh` makes it `0` anyway). -/
def canon (c : Cfg) : Cfg :=
  { c with ths := c.ths.map fun th =>
      { th with vs := { th.vs with coh := fun b => if b ∈ locs c then th.vs.coh b else 0 } } }

/-- Thread `i`'s `machineE` thread-label moves from a promise-free configuration: thread, extern and spawn steps
(a promise-free successor is certified by `Solo.refl`; `certB 0` is `noPromises`). (M1) Device values from the scenario
set `V`: a `devChoice w` site offers one successor per in-range value of `V`. -/
def movesPF (p : Prog) (k : Promises.Knobs) (arch : Arch) (V : List Nat) (c : Cfg) (i : Nat) : List Cfg :=
  threadSteps p k arch c i ++ extSuccs p k arch { solo := 0, io := V } c i ++ TermSpawnSuccs.spawnSuccsAt c i

/-- (D4) Thread `i`'s `machineE` environment moves (spurious wakes) from a promise-free configuration. -/
def wakesPF (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) (i : Nat) : List Cfg :=
  wakeSuccs p k arch { solo := 0 } c i

/-- (D4) All environment moves at `c`: every thread's spurious wakes, in thread order. -/
def envsPF (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) : List Cfg :=
  (List.range c.ths.size).flatMap (wakesPF p k arch c)

/-- `Progress c c' i`, decided at the addresses of `c'`'s memory. -/
def progB (c c' : Cfg) (i : Nat) : Bool :=
  decide (c.mem.size < c'.mem.size) || (locs c').any fun b => decide (cohOf c i b < cohOf c' i b)

/-- Why a rank holds no fair livelock: no move inside it, or a thread outside the crash set that can move at every
quiet node of the rank and never moves inside it. -/
inductive Just
  | noSpin
  | unfair (i : Nat)
  deriving DecidableEq, Repr

/-- The certificate: `nodes[0]` is the start; `succ[v][i]` lists the node of each move of
`movesPF (canon nodes[v]) i`, in that order; `rank` and `just` are the liveness part; (D4) `envs[v]` lists the node
of each environment move of `envsPF (canon nodes[v])`, in that order (absent: none). -/
structure Cert where
  nodes : Array Cfg
  succ  : Array (Array (List Nat))
  rank  : Array Nat
  just  : Array Just
  envs  : Array (List Nat) := #[]

/-- No thread of `c` has a promise out. -/
def pfB (c : Cfg) : Bool := c.ths.all fun th => th.promises.isEmpty

section
variable (p : Prog) (k : Promises.Knobs) (arch : Arch) (X : List Nat) (V : List Nat) (ct : Cert)

/-- Node `v`, canonical. -/
def Cert.nd (v : Nat) : Cfg := canon (ct.nodes[v]?.getD default)
/-- The claimed targets of thread `i`'s moves at node `v`. -/
def Cert.tg (v i : Nat) : List Nat := ((ct.succ[v]?.getD #[])[i]?).getD []
def Cert.rk (v : Nat) : Nat := ct.rank[v]?.getD 0
def Cert.js (v : Nat) : Just := ct.just[ct.rk v]?.getD .noSpin

/-- Thread `i`'s moves at node `v`, paired with their claimed targets. -/
def Cert.mt (v i : Nat) : List (Cfg × Nat) := (movesPF p k arch V (ct.nd v) i).zip (ct.tg v i)
/-- (D4) The claimed targets of the environment moves at node `v`. -/
def Cert.te (v : Nat) : List Nat := ct.envs[v]?.getD []
/-- (D4) The environment moves at node `v`, paired with their claimed targets. -/
def Cert.me (v : Nat) : List (Cfg × Nat) := (envsPF p k arch (ct.nd v)).zip (ct.te v)

/-- No thread outside `X` has a `Progress` move at node `v`. -/
def Cert.quiet (v : Nat) : Bool :=
  (List.range (ct.nd v).ths.size).all fun i =>
    X.contains i || (movesPF p k arch V (ct.nd v) i).all fun e => !progB (ct.nd v) e i

/-- The local conditions at node `v`. (D4) An environment edge needs a node and a non-increasing rank between
quiet nodes (it is no thread's move, so it may stay inside any rank); the justification test is made per edge, as
for thread edges. -/
def Cert.nodeOK (v : Nat) : Bool :=
  let c := ct.nd v
  pfB c && decide (ct.rk v < ct.just.size) &&
  ((List.range c.ths.size).all fun i =>
    decide ((movesPF p k arch V c i).length = (ct.tg v i).length) &&
    (ct.mt p k arch V v i).all fun (e, w) =>
      decide (w < ct.nodes.size) && decide (cfgKey e = cfgKey (ct.nodes[w]?.getD default)) &&
      (!(ct.quiet p k arch X V v && ct.quiet p k arch X V w) ||
        (decide (ct.rk w ≤ ct.rk v) &&
          (!decide (ct.rk w = ct.rk v) || (decide (ct.js v ≠ .noSpin) && decide (ct.js v ≠ .unfair i))))) &&
  (!ct.quiet p k arch X V v ||
    match ct.js v with
    | .noSpin => true
    | .unfair i => !X.contains i && !(movesPF p k arch V c i).isEmpty)) &&
  decide ((envsPF p k arch c).length = (ct.te v).length) &&
  (ct.me p k arch v).all fun (e, w) =>
    decide (w < ct.nodes.size) && decide (cfgKey e = cfgKey (ct.nodes[w]?.getD default)) &&
    (!(ct.quiet p k arch X V v && ct.quiet p k arch X V w) || decide (ct.rk w ≤ ct.rk v)) &&
    (!ct.quiet p k arch X V v ||
      match ct.js v with
      | .noSpin => true
      | .unfair i => !X.contains i && !(movesPF p k arch V c i).isEmpty)

/-- **The checker.** -/
def check (c0 : Cfg) : Bool :=
  decide (0 < ct.nodes.size) && decide (ct.succ.size = ct.nodes.size) && decide (ct.rank.size = ct.nodes.size) &&
  decide (cfgKey c0 = cfgKey (ct.nodes[0]?.getD default)) &&
  (List.range ct.nodes.size).all (ct.nodeOK p k arch X V)

/-- No node has a spawn move. -/
def noSpawnB : Bool :=
  (List.range ct.nodes.size).all fun v =>
    (List.range (ct.nd v).ths.size).all fun i => (TermSpawnSuccs.spawnSuccsAt (ct.nd v) i).isEmpty

/-- Every node without a move is final. -/
def noStuckB : Bool :=
  (List.range ct.nodes.size).all fun v =>
    (ct.nd v).final || (List.range (ct.nd v).ths.size).any fun i => !(movesPF p k arch V (ct.nd v) i).isEmpty
end

/-- A thread present at some point of the run that never crashes (`Live` counting spawned threads). -/
def LiveS {L : Type} (r : LRun L) (D : Nat → Option Nat) (i : Nat) : Prop :=
  (∃ n, i < (r.cfg n).ths.size) ∧ D i = none

/-- `Fair` (F4) with `LiveS` for `Live`: spawned threads are scheduled fairly too. -/
structure FairS (sys : LSys) (r : LRun sys.L) (D : Nat → Option Nat) : Prop where
  weak : ∀ i, LiveS r D i → Ev (fun n => ∃ c', sys.S (r.cfg n) (sys.thr i) c') →
    Often (fun n => r.lbl n = some (sys.thr i))
  prog : ∀ i, LiveS r D i →
    Often (fun n => ∃ c', sys.S (r.cfg n) (sys.thr i) c' ∧ Progress (r.cfg n) c' i) →
    Often (fun n => r.lbl n = some (sys.thr i) ∧ Progress (r.cfg n) (r.cfg (n + 1)) i)

/-- `Livelock` with `LiveS`. -/
def LivelockS (sys : LSys) (r : LRun sys.L) (D : Nat → Option Nat) : Prop :=
  ∃ n₀, Frozen r n₀ ∧ ∃ i, LiveS r D i ∧ Often (fun n => r.lbl n = some (sys.thr i))

/-- The run takes no promise step (environment wakes are allowed in promise-free runs). -/
def PromiseFreeRun {p : Prog} {k : Promises.Knobs} {arch : Arch} (r : LRun (machineE p k arch).L) : Prop :=
  ∀ n i, r.lbl n ≠ some (i, .prom)

/-- The run's `devChoice` results lie in the scenario's device value set `V`: every thread move `(i, .thr)` taken at a
`devChoice` site binds `cst (.num v)` with `v ∈ V`. Environment and promise moves are unconstrained; vacuous for programs
without `devChoice`. (`V` is not `X`, the exempt thread set.) -/
def ScriptedRun {p : Prog} {k : Promises.Knobs} {arch : Arch} (V : List Nat) (r : LRun (machineE p k arch).L) : Prop :=
  ∀ n i th x w a e, r.lbl n = some (i, .thr) → (r.cfg n).ths[i]? = some th →
    th.term = .let_ x (.ext (.devChoice w) a) e →
    ∃ v, v ∈ V ∧ ((r.cfg (n + 1)).ths[i]?).bind (·.env.head?) = some (x, (ExtName.devChoice w).sig.2, [cst (.num v)])

/-- `Doc.finalOutcomes`' row of a configuration: each thread's result, then the last value at each watched
`(label, offset)`. -/
def outcome (m : Nat) (watch : List (Nat × Nat)) (c : Cfg) : List (Option (List Val)) × List (Option Val) :=
  ((List.range m).map fun i => (c.ths[i]?).bind TermSmoke.resWs,
   watch.map fun (l, o) => TermSmoke.lastAt c ⟨l, o⟩)

end TermLiveCert
