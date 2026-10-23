import Scc.Cert.Rt.PhasesA64

/-!
# The phases of the runtime's blocks

The hand proofs of the runtime's functions (`Spike/Lib/Rt/A64RtTcb.lean`,
`A64RtTake.lean`, `A64RtTi.lean`, `A64RtMainU.lean`) take phase facts at
the runtime's pcs: each block's phase check (`Spike.Lib.A64Consumer.blkPh`:
every pc off the sites and in the entry's phase, and so every target but a
dead one), single instructions off the sites and in their next pc's phase,
pcs off the sites, two pcs distinct, a pc's phase index. A6's row check (`phasesOk`) gives the
rows' pcs but not their targets; this check gives the rest.

A **fact** (`PhFact`) names its pcs by a code label plus a number of
instructions; `factOk` checks one with the labels resolved by `code`, the
sites `okPc` and the phases `ph`, over addresses modulo `2 ^ 64` (as the
pcs are). It fails closed: a label that does not resolve, an instruction
that `classify` does not cover, or a `ret` in a fact without a return
address fails it. `rtPhOk` checks a table of facts with A6's phase table
and sites, the labels resolved in one keyed table (`codeT`);
`factOk_of_rtPhOk` gives each fact back with `codeOf`, `okPcOf` and `phOf`.
The runtime's table is `Spike/Lib/Rt/A64RtPhTab.lean`'s `rtPhTab`.
-/

namespace Scc.Cert.Rt.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow
open Scc.Cert.Link.A64

/-- **A phase fact** of the runtime's code, its pcs named by a code label
plus a number of instructions. -/
inductive PhFact where
  /-- The block `b` at `l + 4 k` passes the phase check, a `ret` returning
  to the label `ra`, the label `dead`'s address its one dead target. -/
  | blk (l : String) (k : Nat) (b : List Directive) (ra : Option String) (dead : Option String)
  /-- The pc `l + 4 k` is off the sites and in its next pc's phase. -/
  | step (l : String) (k : Nat)
  /-- The pc `l + 4 k` is off the sites. -/
  | ok (l : String) (k : Nat)
  /-- The pcs `l1 + 4 k1` and `l2 + 4 k2` are distinct. -/
  | ne (l1 : String) (k1 : Nat) (l2 : String) (k2 : Nat)
  /-- The pc `l + 4 k` has the phase index `v`. -/
  | ph (l : String) (k : Nat) (v : Nat)

/-- The pc `k` instructions after the label `l`, resolved by `code`. -/
def pcAt (code : String → Option Nat) (l : String) (k : Nat) : Option Nat :=
  (code l).map fun a => (a + 4 * k) % 2 ^ 64

/-- **An instruction's targets**, its labels resolved by `code`: the
branch's label, both for a conditional branch, the return address `ra` for
a `ret` (none without one), the next pc `fall` otherwise. -/
def tgtsN (code : String → Option Nat) (fall : Nat) (ra : Option String) : AI → Option (List Nat)
  | .b L => (pcAt code L 0).map fun t => [t]
  | .bl L => (pcAt code L 0).map fun t => [t]
  | .bcond _ L => (pcAt code L 0).map fun t => [t, fall]
  | .cbz _ L => (pcAt code L 0).map fun t => [t, fall]
  | .cbnz _ L => (pcAt code L 0).map fun t => [t, fall]
  | .ret _ => match ra with
    | some r => (pcAt code r 0).map fun t => [t]
    | none => none
  | _ => some [fall]

/-- The dead target: the label `dead`'s address, if any. -/
def deadN (code : String → Option Nat) : Option String → Nat → Bool
  | some D, t => match pcAt code D 0 with
    | some d => t == d
    | none => false
  | none, _ => false

/-- **A block's phase check** at the address `a` of its label, `k`
instructions after it: every pc off the sites and in the entry's phase,
every instruction covered, its targets in the entry's phase or dead. -/
def blkOkN (code : String → Option Nat) (okPc : Nat → Bool) (ph : Nat → Nat) (a k : Nat) (b : List Directive)
    (ra dead : Option String) : Bool :=
  (List.range b.length).all fun j =>
    okPc ((a + 4 * (k + j)) % 2 ^ 64) && ph ((a + 4 * (k + j)) % 2 ^ 64) == ph ((a + 4 * k) % 2 ^ 64) &&
    match b[j]? with
    | some d => match classify d with
      | some ai => match tgtsN code ((a + 4 * (k + j) + 4) % 2 ^ 64) ra ai with
        | some ts => ts.all fun t => ph t == ph ((a + 4 * k) % 2 ^ 64) || deadN code dead t
        | none => false
      | none => false
    | none => false

/-- **A fact's check**, the labels resolved by `code`, the sites `okPc`,
the phases `ph`; false on a label that does not resolve. -/
def factOk (code : String → Option Nat) (okPc : Nat → Bool) (ph : Nat → Nat) : PhFact → Bool
  | .blk l k b ra dead => match code l with
    | some a => blkOkN code okPc ph a k b ra dead
    | none => false
  | .step l k => match code l with
    | some a => okPc ((a + 4 * k) % 2 ^ 64) && ph ((a + 4 * k + 4) % 2 ^ 64) == ph ((a + 4 * k) % 2 ^ 64)
    | none => false
  | .ok l k => match code l with
    | some a => okPc ((a + 4 * k) % 2 ^ 64)
    | none => false
  | .ne l1 k1 l2 k2 => match code l1, code l2 with
    | some a1, some a2 => (a1 + 4 * k1) % 2 ^ 64 != (a2 + 4 * k2) % 2 ^ 64
    | _, _ => false
  | .ph l k v => match code l with
    | some a => ph ((a + 4 * k) % 2 ^ 64) == v
    | none => false

/-- The check of a table of facts with the labels resolved by `code`. -/
def rtPhOkBy (code : String → Option Nat) (Λ : Scc.Sem.Layout) (tab : List PhFact) : Bool :=
  match phTabBy code, sitesBy code Λ with
  | some T, some ss => tab.all (factOk code (fun pc => !(ss.contains pc)) T.ph)
  | _, _ => false

/-- **The runtime's phase facts**: the phase table and the sites resolve,
and every fact of `tab` passes its check (`factOk`) with them; the labels
resolved in one keyed table (`codeT`). -/
def rtPhOk (lo : Nat) (prog : Program) (Λ : Scc.Sem.Layout) (tab : List PhFact) : Bool :=
  rtPhOkBy (codeT lo prog) Λ tab

/-- **A fact of a checked table** passes its check with `codeOf`,
`okPcOf` and `phOf`. -/
theorem factOk_of_rtPhOk {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {tab : List PhFact}
    (h : rtPhOk lo prog Λ tab = true) {f : PhFact} (hf : f ∈ tab) :
    factOk (codeOf lo prog) (okPcOf lo prog Λ) (phOf lo prog) f = true := by
  unfold rtPhOk at h
  rw [codeT_eq] at h
  unfold rtPhOkBy at h
  split at h
  · next T ss hT hs =>
    have hph : phOf lo prog = T.ph := by unfold phOf phTabOf; rw [hT]
    have hok : okPcOf lo prog Λ = fun pc => !(ss.contains pc) := by
      funext pc; unfold okPcOf sitesOf; rw [hs]
    rw [hph, hok]
    exact List.all_eq_true.mp h f hf
  · cases h

end Scc.Cert.Rt.A64
