/-
The promise-free normal form: statements, the shape
check, and the proof outline. No proofs of the main statements here; they are
`Prop` definitions.

## What the experiments found

Experiments (Toy ISA, `#guard_msgs` tests in `PFCompleteTests.lean`; AArch64
`.kl` runs) compare the final
configurations of `explore` with promises (`maxPromises := none`) and without
(`some 0`, i.e. `ReachablePF`).

1. **Same final configuration is false in general**, as §5.1 suspected:
   `STR x; STR y` alone has two final memories, `[x, y]` and `[y, x]`
   (promise `y` first); only the first is promise-free.
2. **`≈` (per-location write order, registers and final values equal) is
   false for any syntactic store shape that admits plain stores**:
   `A: LDAR z; STR x; STR y ∥ B: LDAR y; LDR x` has the outcome
   `B: y = 1, x = 0` with promises and not without; the *registers* differ, so
   no renaming of timestamps helps. A racy observer sees the reordering of
   two plain stores, and whether one exists is a property of the whole
   program (data-race freedom), not of the storing thread's code.
   Renaming views along with timestamps does not work either: views are maxima
   over locations and a renaming that permutes locations' writes does not
   commute with `max` (`STR x; STR y`: `vwOld` is `2` in both runs, but the
   renaming maps it to `1`).
3. **Same final configuration is true for write-ordered runs**: if every
   write's timestamp exceeds the writer's frontier `max vrOld vrOldNR vwOld` when it
   is performed (`RunOrdered`) and no instruction writes twice, then every
   `Reachable` promise-free configuration is `ReachablePF` — the very same
   configuration (memory, views and all). Checked on every Toy example of
   that shape (`identical = all`). The argument is direct and does not go
   through the paper's promises-first normal form; see the outline.
   - Every x64 (TSO) program is write-ordered: a plain store is a release
     store, and a locked RMW is fenced.
   - An AArch64 program is write-ordered when every store is `STLR`, or is
     preceded since the last write by a `DMB SY`/acquire-release RMW, or
     depends on a register whose view covers the frontier (`ReleaseAcquireShaped`
     below checks this).
   - The AArch64 lock examples as written are **not** write-ordered: the
     critical section's plain `STR` can be promised before the acquiring
     write (`STXR`, `SWPA`'s or `LDADDA`'s write), which only has acquire
     ordering on its read. The resulting final configurations are `≈`, not
     identical, to promise-free ones (explorer). With an acquire-release
     acquisition (`SWPAL`, `LDADDAL`, `CASAL`) they are write-ordered.
4. For the AArch64 examples as written, the remaining route is `≈` under a
   *semantic* data-race-freedom hypothesis over promise-free runs
   (`pf_complete_drf`), which the Stage 2 logic would have to discharge as part
   of the proof (it is mutual exclusion). Research; unknown.

## Proof outline for `pf_complete_ordered`

| Lemma | Statement | Rating |
|---|---|---|
| `frontier_dominates` | in every reachable thread, every view component (`coh`, `vrNew`, `vwNew`, `vCAP`, `vRel`, `fwdb`, register views) is `≤ max vrOld vrOldNR vwOld`, and `rview ≤ wview` | routine |
| `views_le_last` | every view is `≤ |M|` and is `0` or the timestamp of a message | routine (as `Ctx.Seq`) |
| `run_trace` | a `Reachable` run is a list of labelled steps: an instruction of thread `i` with its `Outcome`, or a promise of thread `i` | routine, tedious (`succsL` is a fold; `foldl_outcomes_spec` in `Conservative.lean` does one thread) |
| `key_mono` | in a write-ordered run, a thread's key `K` (its frontier after the instruction) is monotone in program order, strictly increasing at a write, and equal to the write's timestamp there | easy given `frontier_dominates` |
| `stepOne_prefix` | the outcomes of `stepOne` that read only timestamps `≤ K` and write at `t` are the same against any memory that agrees on `[1, K]` (with `|M| = t - 1` for a writer), up to `fulfil` becoming promise-now and the promise list | hard (the one real lemma: `readSuccs`/`writeSuccs`/`atomic`/`writeIn` against a memory prefix; the fulfil/promise-now coincidence) |
| `schedule` | sorting the run's instruction steps by `(K, writer first, program order)` gives a sequence of `succs` steps, each promise-free, ending in the same configuration | hard (combinatorics of interleavings: a permutation of a step list in Lean) |
| `shape_sound` | `ReleaseAcquireShaped` on an abstraction of the program implies `RunOrdered` | routine (abstract interpretation invariant, per event rule) |
| `Abstracts` for an ISA | the CFG extracted from a program covers `exec`'s event trees | per ISA; routine for Toy, real work for AArch64/x64 (extraction from `Executable` and the decoder) |

The paper's route (`PtoPF.v`: promises first, then delay each promise to the
step that fulfils it) is subsumed: write-ordering is exactly what lets a
promise be delayed to its fulfilment without moving any other message, so
the promises-first stage is not needed. **The first lemma that fails** on that
route is the delay step for plain stores: delaying a promised plain store to
its fulfilment changes the global write order, and a racy reader can see the
difference (item 2 above). For `pf_complete_drf` that lemma becomes "the
reordering is invisible to race-free programs", which is unknown.
-/
import Kraken.Promising.Rel
import Kraken.Promising.Conservative

namespace Kraken.Promising

variable {I : ISA}

/-! ## The `≈` relation -/

/-- The messages to `l`, in timestamp order. -/
def Memory.history (m : Memory) (l : Loc) : List Msg :=
  m.msgs.toList.filter (·.loc == l)

/-- `c ≈ c'`: the same thread states, the same initial memory, and the same
writes to each location in the same order. Timestamps (the interleaving of
different locations' writes) and views may differ: views are not
observable in a final configuration, and they do not rename along with
timestamps (see the header). Equal histories give equal final values
(`Memory.finalVal`). Promise sets are not compared; the statements below
only relate promise-free configurations. -/
structure Config.Equiv (c c' : Config I) : Prop where
  states : c.threads.toList.map (·.st) = c'.threads.toList.map (·.st)
  init : c.mem.init = c'.mem.init
  history : ∀ l, c.mem.history l = c'.mem.history l

theorem Config.Equiv.refl (c : Config I) : c.Equiv c := ⟨rfl, rfl, fun _ => rfl⟩

theorem Config.Equiv.symm {c c' : Config I} (h : c.Equiv c') : c'.Equiv c :=
  ⟨h.states.symm, h.init.symm, fun l => (h.history l).symm⟩

theorem Config.Equiv.trans {c c' c'' : Config I} (h : c.Equiv c') (h' : c'.Equiv c'') : c.Equiv c'' :=
  ⟨h.states.trans h'.states, h.init.trans h'.init, fun l => (h.history l).trans (h'.history l)⟩

/-- An initial configuration: fresh threads, no messages. -/
def Config.Initial (c : Config I) : Prop :=
  ∃ (states : List I.State) (initMem : List (Loc × Val)), c = Config.init states initMem

/-! ## Write-ordered runs -/

/-- A thread's frontier: every view of the thread is at most this
(`frontier_dominates` in the outline). `vrOldNR` (the `noRet` reads' view)
is part of it: a `noRet` read raises `coh` to its post-view like any read. -/
def Thread.frontier (t : Thread I) : View := max (max t.views.vrOld t.views.vrOldNR) t.views.vwOld

/-- Every outcome of every thread's next instruction writes at most once, and
at a timestamp above the thread's frontier before the instruction. The
writes of an outcome are its `.write` trace events (`afterWrite` emits one per
write, fulfilled or promise-now). -/
def Config.StepOrdered (A : Arch) (c : Config I) : Prop :=
  ∀ (tid : Nat) (t : Thread I) (outs : List (Except String (Outcome I))) (o : Outcome I),
    c.threads[tid]? = some t → stepThread A c tid = some outs → .ok o ∈ outs →
      (o.log.filter fun | .write .. => true | _ => false).length ≤ 1 ∧
      ∀ l ts v f, TraceEv.write l ts v f ∈ o.log → t.frontier < ts

/-- Every configuration reachable from `c` is `StepOrdered`. -/
def RunOrdered (A : Arch) (fuel : Nat) (c : Config I) : Prop :=
  ∀ c', Reachable A fuel c c' → c'.StepOrdered A

/-! ## The statements -/

/-- §5.1 as first written, for a class `P` of start configurations:
every reachable promise-free configuration is reachable promise-free. False
for `P := Config.Initial` (`STR x; STR y`, `PFCompleteTests.lean`). -/
def PFCompleteExact (A : Arch) (fuel : Nat) (P : Config I → Prop) : Prop :=
  ∀ c c', P c → Reachable A fuel c c' → c'.PromFree → ReachablePF A fuel c c'

/-- §5.1's "safe form": up to `≈`. False for any class that admits two plain
stores observed by a racy reader (`mpRacy`, `PFCompleteTests.lean`). -/
def PFCompleteEquiv (A : Arch) (fuel : Nat) (P : Config I → Prop) : Prop :=
  ∀ c c', P c → Reachable A fuel c c' → c'.PromFree → ∃ c'', ReachablePF A fuel c c'' ∧ c''.Equiv c'

/-- **The provable form** (outline in the header): for write-ordered runs from
an initial configuration, the exact statement holds. -/
def pf_complete_ordered (A : Arch) (fuel : Nat) : Prop :=
  PFCompleteExact (I := I) A fuel fun c => c.Initial ∧ RunOrdered A fuel c

/-- Exact implies `≈`. -/
theorem PFCompleteExact.equiv {A : Arch} {fuel : Nat} {P : Config I → Prop}
    (h : PFCompleteExact A fuel P) : PFCompleteEquiv A fuel P :=
  fun c c' hP hr hpf => ⟨c', h c c' hP hr hpf, .refl c'⟩

/-! ### The data-race-free form (for plain stores in critical sections) -/

/-- Does some path of an event tree access `l`? (Loads apply `ret` to the
value `0` only: a probe, enough for a definition used as a hypothesis.) -/
def EvTree.Accesses {σ : Type} (l : Loc) : EvTree σ → Prop
  | .done _ | .fault _ => False
  | .choose _ k => ∃ i, (k i).Accesses l
  | .load _ _ l' ret => l' = l ∨ ∃ v, (ret v).Accesses l
  | .store _ _ l' _ ret => l' = l ∨ ∃ b, (ret b).Accesses l
  | .rmw _ _ l' _ ret => l' = l ∨ ∃ v, (ret v).Accesses l
  | .fence _ ret => (ret ()).Accesses l

/-- Data-race freedom on the `data` locations, over promise-free runs: in
every configuration reachable promise-free from `c`, a thread whose next
instruction may access a data location `l` has already seen its last write
(`lastWrite l ≤ coh l`, or below its `vrNew`: an acquire has made it
visible), so it can neither read a stale value nor write out of coherence
order with a concurrent writer. -/
def DataRaceFreePF (A : Arch) (fuel : Nat) (data : Loc → Prop) (c : Config I) : Prop :=
  ∀ c', ReachablePF A fuel c c' → ∀ t ∈ c'.threads, ∀ tree l, I.exec t.st = some tree → data l →
    tree.Accesses l → c'.mem.lastWrite l ≤ max (t.views.getCoh l) t.views.vrNew

/-- Writes to locations outside `data` are ordered (`StepOrdered` restricted
to them). -/
def RunOrderedOff (A : Arch) (fuel : Nat) (data : Loc → Prop) (c : Config I) : Prop :=
  ∀ c', Reachable A fuel c c' →
  ∀ (tid : Nat) (t : Thread I) (outs : List (Except String (Outcome I))) (o : Outcome I),
    c'.threads[tid]? = some t → stepThread A c' tid = some outs → .ok o ∈ outs →
      ∀ l ts v f, TraceEv.write l ts v f ∈ o.log → ¬ data l → t.frontier < ts

/-- **The reshaped target for the AArch64 lock examples as written**
(unknown): synchronisation writes ordered, data accesses race-free in
promise-free runs, conclusion up to `≈`. Not attempted. -/
def pf_complete_drf (A : Arch) (fuel : Nat) : Prop :=
  ∀ (data : Loc → Prop), PFCompleteEquiv (I := I) A fuel fun c =>
    c.Initial ∧ RunOrderedOff A fuel data c ∧ DataRaceFreePF A fuel data c

/-! ## `ReleaseAcquireShaped`: a decidable sufficient check for `RunOrdered`

An abstract interpretation over a control-flow graph whose nodes summarise
instructions by the *kinds* of their memory events (no locations, no values)
and their register dependencies. The abstract state is a handful of facts
of the form "view `≥` frontier" (`frontier = max vrOld vrOldNR vwOld`); a write is
ordered when its pre-view provably covers the frontier. ISA-generic: an ISA
supplies the graph (`Toy.shapeCFG` below; AArch64/x64 extraction is future
work) and the `Abstracts` link.
-/

/-- The kind of a memory event, as the check sees it. -/
inductive EvKind
  | load (k : LoadKind)
  /-- A store; `xcl`: a store exclusive (it may fail and not write). -/
  | store (k : StoreKind) (xcl : Bool)
  /-- An RMW: a read, then possibly a write. `noRet`: as `EvTree.rmw`. -/
  | rmw (k : RmwKind) (noRet : Bool)
  | fence (k : FenceKind)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One instruction: the event-kind sequences of its paths, its register
dependencies (registers as indices), and the successor nodes (indices out
of range: halted). -/
structure ShapeNode where
  paths : List (List EvKind)
  deps : InstrDeps Nat
  next : List Nat
  deriving Repr, Inhabited

structure ShapeCFG where
  nodes : Array ShapeNode
  entries : List Nat
  numRegs : Nat
  deriving Repr, Inhabited

/-- The abstract state: facts about the thread's views relative to the
frontier `F = max vrOld vrOldNR vwOld`. -/
structure OrdBits where
  /-- `vwNew ≥ vrOld`. -/
  r : Bool
  /-- `vwNew ≥ vrOldNR` (`fence .sy` restores it, `fence .ld` does not). -/
  q : Bool
  /-- `vwNew ≥ vwOld`. -/
  w : Bool
  /-- `vrNew ≥ F`. -/
  nr : Bool
  /-- `vRel ≥ F`. -/
  rel : Bool
  /-- Registers whose read-ordering view is `≥ F` (hence also the write view). -/
  cov : List Nat
  deriving Repr, BEq, Inhabited

namespace OrdBits

/-- A fresh thread: every view is `0`. -/
def init (n : Nat) : OrdBits := { r := true, q := true, w := true, nr := true, rel := true, cov := List.range n }

def meet (a b : OrdBits) : OrdBits :=
  { r := a.r && b.r, q := a.q && b.q, w := a.w && b.w, nr := a.nr && b.nr, rel := a.rel && b.rel,
    cov := a.cov.filter (b.cov.contains ·) }

end OrdBits

/-- Per-instruction scratch: the abstract state, whether the instruction's
input registers still cover the frontier (`rdep`: address registers, for a
load's pre-view; `wdep`: address, data and condition registers, for a
write's), the number of writes so far, whether every write was ordered, and
whether a load of this instruction left its result covering the frontier
(`loadCov`, only kept for a single-load instruction). -/
structure OrdScratch where
  s : OrdBits
  rdep : Bool
  wdep : Bool
  writes : Nat
  ok : Bool
  memEvents : Nat
  loadCov : Bool

section Check

variable (A : Arch)

/-- The read rule's effect: `ge` is "the pre-view covers the frontier". A
`noRet` read (plain) raises `vrOldNR` instead of `vrOld`, so it clears `q`
and keeps `r`. -/
def absRead (x : OrdScratch) (k : LoadKind) (noRet : Bool := false) : OrdScratch × Bool :=
  let k := A.loadKind k
  let s := x.s
  let ge := x.rdep || s.nr || (k == .acq && s.rel)
  let acq := k.isAcquire
  ({ x with s := { r := if noRet then s.r else acq && (s.r || ge),
                   q := if noRet then false else if acq then s.q || ge else s.q,
                   w := if acq then s.w || ge else s.w,
                   nr := acq && (s.nr || ge), rel := false, cov := [] },
            rdep := false, wdep := false, memEvents := x.memEvents + 1, loadCov := ge }, ge)

/-- A write's effect, given whether it is ordered. `relK`: a release write. -/
def absWrite (x : OrdScratch) (ordered relK : Bool) : OrdScratch :=
  { x with s := { x.s with w := false, nr := false, rel := relK, cov := [] },
           rdep := false, wdep := false, writes := x.writes + 1, ok := x.ok && ordered,
           memEvents := x.memEvents + 1, loadCov := false }

def absFence (x : OrdScratch) : FenceKind → OrdScratch
  | .sy => { x with s := { x.s with r := true, q := true, w := true, nr := true } }
  | .ld => { x with s := { x.s with r := true } }
  | .st | .stAll => { x with s := { x.s with w := true } }
  | .isb => x

def OrdScratch.meet (a b : OrdScratch) : OrdScratch :=
  { s := a.s.meet b.s, rdep := a.rdep && b.rdep, wdep := a.wdep && b.wdep,
    writes := max a.writes b.writes, ok := a.ok && b.ok, memEvents := max a.memEvents b.memEvents,
    loadCov := a.loadCov && b.loadCov }

/-- One event. -/
def absEvent (x : OrdScratch) : EvKind → OrdScratch
  | .load k => (absRead A x k).1
  | .store k xcl =>
    let relK := A.storeKind k == .rel
    let ordered := relK || (x.s.r && x.s.q && x.s.w) || x.wdep
    let wrote := absWrite x ordered relK
    -- a store exclusive may fail: nothing but `xclb` changes
    if xcl then wrote.meet { x with memEvents := x.memEvents + 1 } else wrote
  | .rmw k noRet =>
    let k := A.rmwKind k
    let x := if A.rmwFence then absFence x .sy else x
    let wdep0 := x.wdep
    let (y, ge) := absRead A x (if noRet then .plain else k.loadKind) noRet
    let relK := k.storeKind == .rel
    -- the write's pre-view joins the read's post-view (`extraData`)
    let ordered := relK || (y.s.r && y.s.q && y.s.w) || wdep0 || ge
    let z := absWrite y ordered relK
    let z := if k == .acqRel && !noRet then { z with s := { z.s with r := true, q := true, w := true, nr := true } } else z
    let z := if A.rmwFence then absFence z .sy else z
    let y := if A.rmwFence then absFence y .sy else y
    z.meet y
  | .fence k => absFence x k

/-- One path of an instruction from state `s`: the scratch at its end, then
the register views of `finishInstr`. -/
def absPath (n : Nat) (d : InstrDeps Nat) (s : OrdBits) (path : List EvKind) : OrdBits × Bool :=
  let cv (r : Nat) := s.cov.contains r
  let rdep := d.addrRegs.any cv
  -- with per-store data registers (`STP`), only a dependency of every store
  -- counts (`absWrite` clears `wdep` after the first write anyway)
  let dataDep := if d.dataRegsPer.isEmpty then d.dataRegs.any cv else d.dataRegsPer.all (·.any cv)
  let wdep := (d.addrRegs ++ d.condRegs).any cv || dataDep
  let x0 : OrdScratch := { s, rdep, wdep, writes := 0, ok := true, memEvents := 0, loadCov := false }
  let x := path.foldl (absEvent A) x0
  -- registers: with no memory event the frontier is unchanged
  let frontierSame := x.memEvents == 0
  -- per-store data (`STP`) feeds the stores only (`instrViews`)
  let inCov := (d.addrRegs ++ (if d.dataRegsPer.isEmpty then d.dataRegs else []) ++
    (if d.isPick then [] else d.condRegs)).any cv
  let written := d.defs ++ d.loadDefs ++ d.statusDefs
  let keep := if frontierSame then x.s.cov.filter (!written.contains ·) else x.s.cov
  let defsCov := if frontierSame && inCov then d.defs else []
  let loadCov := if x.memEvents == 1 && x.loadCov && !d.casLike then d.loadDefs else []
  let cov := (keep ++ defsCov ++ loadCov).eraseDups.filter (· < n)
  ({ x.s with cov }, x.ok && x.writes ≤ 1)

/-- The meet over an instruction's paths, and whether all its writes are ordered. -/
def absNode (n : Nat) (nd : ShapeNode) (s : OrdBits) : OrdBits × Bool :=
  match nd.paths.map (absPath A n nd.deps s) with
  | [] => (s, true)
  | p :: ps => ps.foldl (fun (a, ok) (b, ok') => (a.meet b, ok && ok')) p

/-- Fixpoint: the abstract state at each node (`none`: unreachable). -/
def absFix (g : ShapeCFG) : Array (Option OrdBits) :=
  let n := g.nodes.size
  let start : Array (Option OrdBits) := (Array.replicate n (none : Option OrdBits)).mapIdx fun i _ =>
    if g.entries.contains i then some (OrdBits.init g.numRegs) else none
  let join (a : Option OrdBits) (b : OrdBits) : Option OrdBits :=
    some (match a with | some a => a.meet b | none => b)
  let pass (st : Array (Option OrdBits)) : Array (Option OrdBits) :=
    (List.range n).foldl (init := st) fun st i =>
      match st[i]!, g.nodes[i]? with
      | some s, some nd =>
        let (out, _) := absNode A g.numRegs nd s
        nd.next.foldl (fun st j => if j < n then st.set! j (join st[j]! out) else st) st
      | _, _ => st
  -- the lattice has height ≤ n * (6 + numRegs) + n: that many passes suffice
  (List.range (n * (7 + g.numRegs) + 1)).foldl (fun st _ => pass st) start

/-- **`ReleaseAcquireShaped`**: at every reachable node, every path of the
instruction writes at most once and every write is ordered. -/
def ReleaseAcquireShaped (g : ShapeCFG) : Bool :=
  let st := absFix A g
  (List.range g.nodes.size).all fun i =>
    match st[i]!, g.nodes[i]? with
    | some s, some nd => (absNode A g.numRegs nd s).2
    | _, _ => true

/-- The nodes whose instruction has an unordered write (for diagnostics). -/
def unorderedNodes (g : ShapeCFG) : List Nat :=
  let st := absFix A g
  (List.range g.nodes.size).filter fun i =>
    match st[i]!, g.nodes[i]? with
    | some s, some nd => !(absNode A g.numRegs nd s).2
    | _, _ => false

end Check

/-! ### The link from programs to the graph (stated, not proved) -/

/-- The event-kind paths of an event tree, each with its final state. -/
inductive EvTree.KindPath {σ : Type} : EvTree σ → List EvKind → σ → Prop
  | done (s : σ) : KindPath (.done s) [] s
  | choose {n : Nat} {k : Fin n → EvTree σ} (i : Fin n) {p s} : KindPath (k i) p s → KindPath (.choose n k) p s
  | load {k x l ret} (v : Val) {p s} : KindPath (ret v) p s → KindPath (.load k x l ret) (.load k :: p) s
  | store {k x l v ret} (b : Bool) {p s} : KindPath (ret b) p s → KindPath (.store k x l v ret) (.store k x :: p) s
  | rmw {k nr l op ret} (v : Val) {p s} : KindPath (ret v) p s → KindPath (.rmw k nr l op ret) (.rmw k nr :: p) s
  | fence {k ret} {p s} : KindPath (ret ()) p s → KindPath (.fence k ret) (.fence k :: p) s

/-- `g` abstracts the ISA on the states satisfying `Inv` (closed under
execution), with `node` locating a state in the graph: every path of the
instruction is one of the node's paths, ends at a successor node, and the
instruction's dependencies are the node's (registers by `regIndex`). -/
structure Abstracts (g : ShapeCFG) (Inv : I.State → Prop) (node : I.State → Nat) : Prop where
  closed : ∀ s tree p s', Inv s → I.exec s = some tree → tree.KindPath p s' → Inv s'
  node_lt : ∀ s tree, Inv s → I.exec s = some tree → node s < g.nodes.size
  paths : ∀ s tree p s', Inv s → I.exec s = some tree → tree.KindPath p s' →
    p ∈ (g.nodes[node s]!).paths ∧ node s' ∈ (g.nodes[node s]!).next
  deps : ∀ s, Inv s → I.exec s ≠ none →
    let d := I.deps s
    let d' := (g.nodes[node s]!).deps
    d'.addrRegs = d.addrRegs.map (I.regIndex · |>.val) ∧ d'.dataRegs = d.dataRegs.map (I.regIndex · |>.val) ∧
    d'.dataRegsPer = d.dataRegsPer.map (·.map (I.regIndex · |>.val)) ∧
    d'.condRegs = d.condRegs.map (I.regIndex · |>.val) ∧ d'.defs = d.defs.map (I.regIndex · |>.val) ∧
    d'.loadDefs = d.loadDefs.map (I.regIndex · |>.val) ∧ d'.statusDefs = d.statusDefs.map (I.regIndex · |>.val) ∧
    d'.isPick = d.isPick ∧ d'.casLike = d.casLike
  numRegs : g.numRegs = I.numRegs

/-- The check is sound (outline: `shape_sound`, routine): a shaped graph that
abstracts every thread of an initial configuration makes its runs ordered. -/
def shape_sound (A : Arch) (fuel : Nat) : Prop :=
  ∀ (g : ShapeCFG) (Inv : I.State → Prop) (node : I.State → Nat) (states : List I.State) initMem,
    Abstracts g Inv node → (∀ s ∈ states, Inv s ∧ node s ∈ g.entries) → ReleaseAcquireShaped A g = true →
    RunOrdered A fuel (Config.init states initMem)

end Kraken.Promising
