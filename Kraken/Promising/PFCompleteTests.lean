/-
Tests for `Kraken.Promising.PFComplete` on the Toy ISA: the shape check
(`ReleaseAcquireShaped`) on the lock shapes, and the explorer experiments
behind the prototype's findings: final configurations
with promises against those without (`maxPromises := some 0`), compared
exactly, up to `≈`, and on registers alone.
-/
import Kraken.Promising.PFComplete
import Kraken.Promising.Toy

namespace Kraken.Promising.Toy

open Instr

/-! ## The Toy control-flow graph -/

/-- The event kinds of one Toy instruction (one path each). -/
def Instr.kinds : Instr → List EvKind
  | .ld k _ _ _ _ => [.load k]
  | .ldw .. => [.load .plain]
  | .st k xcl _ _ _ _ => [.store k xcl]
  | .rmw k _ _ _ _ noRet => [.rmw k noRet]
  | .fence k => [.fence k]
  | .mov .. | .add .. | .beq .. => []

def Instr.succs (pc : Nat) : Instr → List Nat
  | .beq _ _ target => [pc + 1, target]
  | _ => [pc + 1]

def depsToNat (d : InstrDeps Reg) : InstrDeps Nat :=
  { addrRegs := d.addrRegs.map (·.val), dataRegs := d.dataRegs.map (·.val),
    dataRegsPer := d.dataRegsPer.map (·.map (·.val)),
    condRegs := d.condRegs.map (·.val), loadDefs := d.loadDefs.map (·.val),
    statusDefs := d.statusDefs.map (·.val), defs := d.defs.map (·.val),
    isBranch := d.isBranch, isPick := d.isPick, casLike := d.casLike }

/-- The graph of a Toy program: one node per instruction, entry `0`. -/
def shapeCFG (prog : List Instr) : ShapeCFG :=
  { nodes := (prog.zipIdx.map fun (i, pc) =>
      ({ paths := [i.kinds], deps := depsToNat (deps { prog := prog.toArray, pc }), next := i.succs pc } : ShapeNode)).toArray,
    entries := [0], numRegs := 4 }

def shaped (A : Arch) (progs : List (List Instr)) : Bool :=
  progs.all fun p => ReleaseAcquireShaped A (shapeCFG p)

/-! ## Programs -/

/-- `LDAXR/STXR` spinlock (locations: 0 lock, 1 counter), plain `STR` in the
critical section, `STLR` release: the `spinlock2.kl` shape. -/
def spin : List Instr :=
  [ld .acq true 0 0, beq 0 1 0, st .plain true 0 (.i 1) (status := some 1), beq 1 1 0,
   ld .plain false 2 1, add 2 (.r 2) (.i 1), st .plain false 1 (.r 2), st .rel false 0 (.i 0)]

/-- Its relaxed variant: plain `STR` release (`spinlock_relaxed2.kl`). -/
def spinRelaxed : List Instr := spin.set 7 (st .plain false 0 (.i 0))

/-- Acquisition by an acquire-release CAS (`CASAL`): write-ordered. -/
def spinAcqRel : List Instr :=
  [rmw .acqRel 0 0 (.i 1) (cmp := some (.i 0)), beq 0 1 0,
   ld .plain false 2 1, add 2 (.r 2) (.i 1), st .plain false 1 (.r 2), st .rel false 0 (.i 0)]

/-- The same with a relaxed (plain) release. -/
def spinAcqRelRelaxed : List Instr := spinAcqRel.set 5 (st .plain false 0 (.i 0))

/-- Ticket-lock shape for two threads with fixed tickets (Toy's `beq`
compares with an immediate): `LDADDA` on `next` (0), spin with `LDAR` on
`owner` (1) until it equals the ticket, counter (2), `STLR owner`. Thread
`i` assumes ticket `i`, so the program is only a shape test. -/
def ticket (my : Nat) (rk : RmwKind) (spinK : LoadKind) : List Instr :=
  [rmw rk 0 0 (.i 1), ld spinK false 1 1, beq 1 my 4, beq 0 0 1,
   ld .plain false 2 2, add 2 (.r 2) (.i 1), st .plain false 2 (.r 2), st .rel false 1 (.i (my + 1))]

/-- A racy observer of two plain stores. -/
def mpRacy : List (List Instr) :=
  [[ld .acq false 3 2, st .plain false 0 (.i 1), st .plain false 1 (.i 1)],
   [ld .acq false 0 1, ld .plain false 1 0]]

/-! ## The shape check -/

-- The lock shapes as written (`LDAXR/STXR`, `LDADDA`) are not write-ordered:
-- the critical section's store (node 6) may precede the acquiring write.
-- Node 2 (the plain `STXR`) is a false alarm: the check does not correlate
-- the status register with the retry branch, so the retry path is joined
-- with the successful store's state (a release `STLXR` would pass).
/-- info: (false, [2, 6]) -/
#guard_msgs in #eval (shaped .armv8 [spin], unorderedNodes .armv8 (shapeCFG spin))
/-- info: (false, [6]) -/
#guard_msgs in #eval (shaped .armv8 [ticket 0 .acq .acq], unorderedNodes .armv8 (shapeCFG (ticket 0 .acq .acq)))
-- An acquire-release acquisition makes them write-ordered (the counter store
-- is ordered by its data dependency on a load that covers the frontier).
/-- info: true -/
#guard_msgs in #eval shaped .armv8 [spinAcqRel]
/-- info: true -/
#guard_msgs in #eval shaped .armv8 [ticket 0 .acqRel .acq, ticket 1 .acqRel .acq]
-- Relaxed variants are rejected.
/-- info: (false, [5]) -/
#guard_msgs in #eval (shaped .armv8 [spinAcqRelRelaxed], unorderedNodes .armv8 (shapeCFG spinAcqRelRelaxed))
/-- info: false -/
#guard_msgs in #eval shaped .armv8 [spinRelaxed]
/-- info: false -/
#guard_msgs in #eval shaped .armv8 [ticket 0 .acqRel .plain]
-- `noRet` RMWs (`LDADDAL W0,WZR`): the read is not an acquire, so the
-- acquire-release ordering after the write is lost and a later plain store
-- is unordered; `fence .sy` orders it (it folds `vrOldNR`), `fence .ld` not.
/-- info: (true, false) -/
#guard_msgs in #eval (shaped .armv8 [[rmw .acqRel 0 0 (.i 1), st .plain false 1 (.i 1)]],
  shaped .armv8 [[rmw .acqRel 0 0 (.i 1) (noRet := true), st .plain false 1 (.i 1)]])
/-- info: (true, false) -/
#guard_msgs in #eval (shaped .armv8 [[rmw .plain 0 0 (.i 1) (noRet := true), fence .sy, st .plain false 1 (.i 1)]],
  shaped .armv8 [[rmw .plain 0 0 (.i 1) (noRet := true), fence .ld, st .plain false 1 (.i 1)]])
-- The plain spin read leaves the counter load uncovered: rejected.
/-- info: false -/
#guard_msgs in #eval shaped .armv8 mpRacy
-- Under TSO every Toy program here is write-ordered.
/-- info: true -/
#guard_msgs in #eval shaped .tso ([spin, spinRelaxed, spinAcqRelRelaxed, ticket 0 .plain .plain] ++ mpRacy ++ SB [] [])
-- `STR x; STR y` is not; `STR x; STLR y` and LB with release stores are.
/-- info: (false, true, true) -/
#guard_msgs in #eval (shaped .armv8 [[st .plain false 0 (.i 1), st .plain false 1 (.i 1)]],
  shaped .armv8 [[st .plain false 0 (.i 1), st .rel false 1 (.i 1)]],
  shaped .armv8 [[ld .plain false 0 0, st .rel false 1 (.i 1)], [ld .plain false 0 1, st .rel false 0 (.i 1)]])

/-! ## Promising against promise-free final configurations -/

/-- Everything of a final configuration but Toy's program text. -/
abbrev FullKey := (List (List Nat × Array View × Array View × Views)) × List Msg

def fullKey (c : Config isa) : FullKey :=
  (c.threads.toList.map fun t => (t.st.regs.toList.map (·.toNat), t.rview, t.wview, t.views), c.mem.msgs.toList)

/-- The `≈` projection: registers and per-location histories. -/
def equivKey (k : FullKey) : List (List Nat) × List (List Msg) :=
  let locs := (k.2.map (·.loc)).eraseDups.mergeSort (fun a b => a.addr.toNat ≤ b.addr.toNat)
  (k.1.map (·.1), locs.map fun l => k.2.filter (·.loc == l))

/-- `(all, pf, identical, ≈, same registers)`: the number of final
configurations with promises, without, and of the former that have an
identical / `≈` / same-registers promise-free counterpart. -/
def comparePF (A : Arch) (progs : List (List Instr)) : Nat × Nat × Nat × Nat × Nat :=
  let c0 : Config isa := Config.init (progs.map fun p => ({ prog := p.toArray } : State)) []
  let all := (explore (I := isa) A c0 fullKey {}).finals
  let pf := (explore (I := isa) A c0 fullKey { maxPromises := some 0 }).finals
  (all.length, pf.length, (all.filter pf.contains).length,
   (all.filter fun k => pf.any fun k' => equivKey k' == equivKey k).length,
   (all.filter fun k => pf.any fun k' => k'.1.map (·.1) == k.1.map (·.1)).length)

-- `STR x; STR y`: two final memories, one promise-free; equal up to `≈`.
/-- info: (2, 1, 1, 2, 2) -/
#guard_msgs in #eval comparePF .armv8 [[st .plain false 0 (.i 1), st .plain false 1 (.i 1)]]
-- The racy observer: one outcome (B: y = 1, x = 0) needs a promise; not even
-- the registers agree.
/-- info: (7, 3, 3, 6, 6) -/
#guard_msgs in #eval comparePF .armv8 mpRacy
-- Write-ordered programs: identical.
/-- info: (4, 4, 4, 4, 4) -/
#guard_msgs in #eval comparePF .armv8 [[ld .plain false 0 0, st .rel false 1 (.i 1)], [ld .plain false 0 1, st .rel false 0 (.i 1)]]
/-- info: (8, 8, 8, 8, 8) -/
#guard_msgs in #eval comparePF .tso (SB [] [])
-- The `LDAXR/STXR` spinlock: `≈` but not identical (the counter store is
-- promised before the `STXR`).
/-- info: (8, 2, 2, 8, 8) -/
#guard_msgs in #eval comparePF .armv8 [spin, spin]
-- Likewise the `LDADDA` ticket shape.
/-- info: (57, 24, 24, 57, 57) -/
#guard_msgs in #eval comparePF .armv8 [ticket 0 .acq .acq, ticket 1 .acq .acq]
-- With an acquire-release acquisition (shaped above): identical.
/-- info: (2, 2, 2, 2, 2) -/
#guard_msgs in #eval comparePF .armv8 [spinAcqRel, spinAcqRel]
/-- info: (19, 19, 19, 19, 19) -/
#guard_msgs in #eval comparePF .armv8 [ticket 0 .acqRel .acq, ticket 1 .acqRel .acq]
-- Its relaxed release loses an update only with promises: not even `≈`.
/-- info: (32, 2, 2, 14, 20) -/
#guard_msgs in #eval comparePF .armv8 [spinAcqRelRelaxed, spinAcqRelRelaxed]

end Kraken.Promising.Toy
