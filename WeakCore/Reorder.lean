/-
# Reorder — may a compiler swap two independent plain accesses?  (menu item 2)

The term layer (`TermRun`) runs every access on `Promises`' machine, at an
architecture `arch`.  An optimiser that swaps two adjacent accesses in one
thread is sound for that semantics iff the swapped program has no final state
the original lacks.  This file checks that, executably, on:

  * **the suite**: every adjacent pair in every litmus test of `suite` that a
    compiler could legally consider swapping (`swappable`: both plain — no
    `acq`/`rel`, no fence, branch or `isb`; disjoint locations; no register
    dependence either way, including anti- and output dependences); and
  * **generated tests**: thread 0 is one such pair over `x`, `y` (load, store,
    or plain swap-RMW, in either order, optionally followed by a store to `z`
    that depends on the first access's register), against every two-access
    observer over `x`, `y` with a `dmb sy` between (16 observers).

The comparison is of *full* final states — every register any thread
defines, and every location — not of a test's target outcome only.

Findings (asserted below):

  * **ARM: every swap is sound, and in fact an equivalence** (same state set
    both ways) on the suite's 19 ARM swaps; and sound on all 768 generated ARM
    swaps (`ReorderSlow.lean`; 288 of them are re-run here).
  * **TSO: exactly the reorderings TSO forbids add states** — load→load,
    store→store, load→store, and any swap involving an RMW; store→load swaps
    are sound.  12 of the suite's 14 TSO swaps fail (pinned by name below), and 92 of
    the 768 generated (`ReorderSlow.lean`).

Consequence: compiler reordering of independent plain accesses is sound for
the *ARM* semantics, and not for the TSO one.  So the semantics an optimiser
reasons against must be the ARM machine; code for x86 is then justified by
`Promises.tso_outcomes_subset_arm` (§16), which is proved for every program.

Not covered here, and recorded there: same-location transformations
(redundant-load elimination, store forwarding, dead-store elimination), a
general commutation theorem, and accesses the term layer emits in multi-unit
steps.
-/
import WeakCore.Promises
open WeakMem

namespace Reorder

/-- A plain memory access: one a compiler may move at all. -/
def plainAccess : Instr → Bool
  | .load _ _ _ acq => !acq
  | .store _ _ _ rel => !rel
  | .rmw _ _ _ _ _ acq rel => !acq && !rel
  | .rmwPair _ _ _ _ _ _ _ _ acq rel => !acq && !rel
  | .storePair _ _ _ _ rel => !rel
  | .loadPair _ _ _ _ acq => !acq
  | _ => false

/-- `L`oad, `S`tore, or `U`pdate (RMW), for labels. -/
def kind : Instr → String
  | .load .. | .loadPair .. => "L"
  | .store .. | .storePair .. => "S"
  | .rmw .. | .rmwPair .. => "U"
  | _ => "?"

def disjRegs (a b : List Reg) : Bool := a.all fun r => !b.contains r

/-- The compiler's side condition for swapping adjacent `i; j`: both plain,
disjoint locations, no true, anti- or output register dependence. -/
def swappable (i j : Instr) : Bool :=
  plainAccess i && plainAccess j && addrsDisjoint i j &&
  disjRegs (instrDefs i) (instrDeps j) && disjRegs (instrDefs j) (instrDeps i) &&
  disjRegs (instrDefs i) (instrDefs j)

/-- Every variant of `L` obtained by one adjacent swap, labelled
`T<thread>@<index>:<kinds>`. -/
def swaps (L : Litmus) : List (String × Litmus) :=
  (List.range L.threads.length).flatMap fun t =>
    let p := L.threads[t]!
    (List.range (p.length - 1)).filterMap fun k =>
      let i := p[k]!; let j := p[k+1]!
      if swappable i j then
        some (s!"T{t}@{k}:{kind i}{kind j}",
              { L with threads := L.threads.set t (p.set k j |>.set (k+1) i) })
      else none

/-- The full final state: every register any thread defines, every location
(and the word after it, for pair accesses). -/
def fullObs (L : Litmus) : List Obs :=
  ((List.range L.threads.length).flatMap fun t =>
    ((L.threads[t]!).flatMap instrDefs).eraseDups.map (Obs.reg t)) ++
  (L.locs.flatMap fun a => [Obs.mem a, Obs.mem a.next]).eraseDups

def states (L : Litmus) (obs : List Obs) : List (List Nat) :=
  let fs := Promises.finals Promises.Knobs.all L.arch 64 (Promises.start L)
  (fs.map fun c => obs.map (Promises.obsNat c)).eraseDups

def subset (a b : List (List Nat)) : Bool := a.all (b.contains ·)

structure Row where
  test : String
  arch : String
  swap : String
  /-- The swapped program's states ⊆ the original's: the swap is sound. -/
  sub : Bool
  /-- And conversely: the swap is an equivalence. -/
  eq : Bool
  deriving Repr

def check (L : Litmus) : List Row :=
  let obs := fullObs L
  let base := states L obs
  (swaps L).map fun (lbl, L') =>
    let s := states L' obs
    { test := L.name, arch := Promises.archStr L.arch, swap := lbl,
      sub := subset s base, eq := subset base s }

/-! ## Generated tests -/

def z : Address := ⟨2, 0⟩
def two' : Val := .num 2

/-- Thread 0's accesses: 0 load, 1 store, 2 plain swap-RMW; loads into `r`. -/
def acc0 (k : Nat) (a : Address) (r : Reg) : Instr :=
  match k with
  | 0 => .load r a [] false
  | 1 => .store a (.const one) [] false
  | _ => .rmw r a .swap (.const one) [] false false

/-- Observer accesses store 2, so the two threads' writes are told apart. -/
def accO (k : Nat) (a : Address) (r : Reg) : Instr :=
  if k == 0 then .load r a [] false else .store a (.const two') [] false

/-- Every two-access observer over `x`, `y`, fully fenced. -/
def observers : List (List Instr) :=
  [x, y].flatMap fun a => [x, y].flatMap fun b => [0, 1].flatMap fun ka => [0, 1].map fun kb =>
    [accO ka a 0, .fence .sy, accO kb b 1]

/-- Thread-0 programs: a pair over (`x`, `y`) in both orders, optionally
followed by a store to `z` that depends (address and data) on the first
access's register.  Named `<kinds><r?><ctx>`. -/
def pairs0 : List (String × Bool × List Instr) :=
  [0, 1, 2].flatMap fun k1 => [0, 1, 2].flatMap fun k2 => [false, true].flatMap fun ctx =>
    let p := [acc0 k1 x 0, acc0 k2 y 1]
    let q := [acc0 k2 y 1, acc0 k1 x 0]
    let tail := if ctx && k1 != 1 then [Instr.store z (.reg 0) [0] false] else []
    let tailq := if ctx && k2 != 1 then [Instr.store z (.reg 1) [1] false] else []
    [(s!"{k1}{k2}{ctx}", ctx, p ++ tail), (s!"{k2}{k1}r{ctx}", ctx, q ++ tailq)]

def gen (arch : Arch) (withCtx : Bool) : List Litmus :=
  (pairs0.filter fun (_, c, _) => withCtx || !c).flatMap fun (n, _, t0) =>
    (List.range observers.length).map fun o =>
      { name := s!"G{n}/o{o}", arch := arch, threads := [t0, observers[o]!],
        locs := [x, y, z], obs := [], target := [], archAllows := true }

/-! ## The suite

Each dataset is computed once and summarised; the guards test the summary
(a `#guard` re-evaluates its expression, and the exploration dominates). -/

structure Summary where
  total : Nat
  arm : Nat
  armSound : Bool
  armEquiv : Bool
  tso : Nat
  tsoUnsound : List String
  tsoSLSound : Bool
  deriving Repr

def summarise (rows : List Row) : Summary :=
  let arm := rows.filter (·.arch == "arm")
  let tso := rows.filter (·.arch == "tso")
  { total := rows.length, arm := arm.length
    armSound := arm.all (·.sub), armEquiv := arm.all (·.eq)
    tso := tso.length
    tsoUnsound := (tso.filter (!·.sub)).map fun r => s!"{r.test} {r.swap}"
    tsoSLSound := (tso.filter (·.swap.endsWith ":SL")).all (·.sub) }

def suiteSummary : Summary := summarise (suite.flatMap check)

-- ARM: all 39 swaps sound (11 from `b4Tests`), and equivalences.  TSO: of 26, exactly these 22
-- add states; the two store→load swaps are sound, and so are `SB+rfi-pos`'s
-- two load→load swaps (the first load is forwarded from the thread's own
-- store, so it orders nothing).  `SB+cmpxchg-fails` is locked in place: a
-- `lock cmpxchg` is a barrier on both sides even when it fails.  The fetch-op shapes
-- behave exactly as their CAS originals: a plain `LDADD` swaps freely on ARM
-- and is locked in place on x86.
#guard
  let s := suiteSummary
  s.total == 65 && s.arm == 39 && s.armSound && s.armEquiv && s.tso == 26 && s.tsoSLSound &&
  s.tsoUnsound ==
    ["MP T0@0:SS", "MP T1@0:LL", "LB T0@0:LS", "LB T1@0:LS", "IRIW T2@0:LL", "IRIW T3@0:LL",
     "SB+cas T0@0:UL", "SB+cas T1@0:UL", "MP+cas+po T0@0:SU", "MP+cas+po T1@0:LL",
     "LB+cas T0@0:LU", "LB+cas T1@0:LU", "WRC+xchgdata T2@0:LL", "WRC+cmpxchgdata T2@0:LL",
     "SB+xadd T0@0:UL", "SB+xadd T1@0:UL", "MP+xadd+po T0@0:SU", "MP+xadd+po T1@0:LL",
     "LB+xadd T0@0:LU", "LB+xadd T1@0:LU",
     "SB+cmpxchg-fails T0@0:SU", "SB+cmpxchg-fails T1@0:SU"]

/-! ## Generated, ARM, without the dependent store (the rest: `ReorderSlow.lean`) -/

#guard
  let s := summarise ((gen .arm false).flatMap check)
  s.total == 288 && s.armSound

end Reorder
