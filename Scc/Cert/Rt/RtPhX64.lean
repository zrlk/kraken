import Scc.Cert.Rt.PhasesX64

/-!
# The phases of the runtime's blocks (x86-64)

The twin of `Scc/Cert/Rt/RtPhA64.lean`. The hand proofs of the runtime's
functions (`Spike/Lib/Rt/X64RtTcb.lean`, `X64RtTake.lean`, `X64RtTi.lean`,
`X64RtMainU.lean`) take phase facts at the runtime's pcs: each block's
phase check (`Spike.Lib.X64Consumer.blkPh`: every pc off the sites and in
the entry's phase, and so every target but a dead one), single
instructions off the sites and in their next pc's phase, pcs off the
sites, two pcs distinct, a pc's phase index. A6's row check (`phasesOk`)
gives the rows' pcs but not their targets; this check gives the rest.

A **fact** (`PhFact`) names its pcs by a code label plus a byte offset;
`factOk` checks one with the labels resolved by `code`, the sites `okPc`
and the phases `ph`, over addresses modulo `2 ^ 64` (as the pcs are). A
block's pcs are its offset plus the sizes of the cells before each
(`cellOff`), an instruction's fall-through its pc plus its cell's size. It
fails closed: a label that does not resolve, an instruction that
`classify` does not cover, or a `ret` in a fact without a return address
fails it. A return address is a label plus a byte offset: the return
point of `scc_rt_thread_init`'s call is a program-numbered local label
(`.Lscc_rt_thread_init.x7` in `ret0`), named from `.entry` instead (as
`PhasesX64.lean`'s ranges do). `rtPhOk` checks a table of facts with A6's phase table and
sites, the labels resolved in one keyed table (`codeT`); `factOk_of_rtPhOk`
gives each fact back with `codeLabel`, `okPcOf` and `phOf`. The runtime's
table is `Spike/Lib/Rt/X64RtPhTab.lean`'s `rtPhTab`.
-/

namespace Scc.Cert.Rt.X64

open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib.X64
open Scc.Sem Scc.Sem.X64

/-- **A phase fact** of the runtime's code, its pcs named by a code label
plus a byte offset. -/
inductive PhFact where
  /-- The block `b` at `l + o` passes the phase check, a `ret` returning
  to `ra` (a label plus a byte offset), the label `dead`'s address its one
  dead target. -/
  | blk (l : String) (o : Nat) (b : List (Directive × Nat)) (ra : Option (String × Nat)) (dead : Option String)
  /-- The pc `l + o` is off the sites and in the phase of its next pc
  `l + o + z`. -/
  | step (l : String) (o z : Nat)
  /-- The pc `l + o` is off the sites. -/
  | ok (l : String) (o : Nat)
  /-- The pcs `l1 + o1` and `l2 + o2` are distinct. -/
  | ne (l1 : String) (o1 : Nat) (l2 : String) (o2 : Nat)
  /-- The pc `l + o` has the phase index `v`. -/
  | ph (l : String) (o : Nat) (v : Nat)

/-- The pc `o` bytes after the label `l`, resolved by `code`. -/
def pcAt (code : String → Option Nat) (l : String) (o : Nat) : Option Nat :=
  (code l).map fun a => (a + o) % 2 ^ 64

/-- **An instruction's targets**, its labels resolved by `code`: the
jump's or call's label, both for a conditional jump, the return address
`ra` (a label plus a byte offset) for a `ret` (none without one), the next pc `fall` otherwise. -/
def tgtsN (code : String → Option Nat) (fall : Nat) (ra : Option (String × Nat)) : AI → Option (List Nat)
  | .jmp L => (pcAt code L 0).map fun t => [t]
  | .call L => (pcAt code L 0).map fun t => [t]
  | .jcc _ L => (pcAt code L 0).map fun t => [t, fall]
  | .ret => match ra with
    | some (r, o) => (pcAt code r o).map fun t => [t]
    | none => none
  | _ => some [fall]

/-- The dead target: the label `dead`'s address, if any. -/
def deadN (code : String → Option Nat) : Option String → Nat → Bool
  | some D, t => match pcAt code D 0 with
    | some d => t == d
    | none => false
  | none, _ => false

/-- **A block's phase check** at the address `a` of its label, `o` bytes
after it: every pc off the sites and in the entry's phase, every
instruction covered, its targets in the entry's phase or dead. -/
def blkOkN (code : String → Option Nat) (okPc : Nat → Bool) (ph : Nat → Nat) (a o : Nat)
    (b : List (Directive × Nat)) (ra : Option (String × Nat)) (dead : Option String) : Bool :=
  (List.range b.length).all fun j =>
    okPc ((a + o + cellOff b j) % 2 ^ 64) && ph ((a + o + cellOff b j) % 2 ^ 64) == ph ((a + o) % 2 ^ 64) &&
    match b[j]? with
    | some dz => match classify dz.1 with
      | some ai => match tgtsN code ((a + o + cellOff b j + dz.2) % 2 ^ 64) ra ai with
        | some ts => ts.all fun t => ph t == ph ((a + o) % 2 ^ 64) || deadN code dead t
        | none => false
      | none => false
    | none => false

/-- **A fact's check**, the labels resolved by `code`, the sites `okPc`,
the phases `ph`; false on a label that does not resolve. -/
def factOk (code : String → Option Nat) (okPc : Nat → Bool) (ph : Nat → Nat) : PhFact → Bool
  | .blk l o b ra dead => match code l with
    | some a => blkOkN code okPc ph a o b ra dead
    | none => false
  | .step l o z => match code l with
    | some a => okPc ((a + o) % 2 ^ 64) && ph ((a + o + z) % 2 ^ 64) == ph ((a + o) % 2 ^ 64)
    | none => false
  | .ok l o => match code l with
    | some a => okPc ((a + o) % 2 ^ 64)
    | none => false
  | .ne l1 o1 l2 o2 => match code l1, code l2 with
    | some a1, some a2 => (a1 + o1) % 2 ^ 64 != (a2 + o2) % 2 ^ 64
    | _, _ => false
  | .ph l o v => match code l with
    | some a => ph ((a + o) % 2 ^ 64) == v
    | none => false

/-- The check of a table of facts with the labels resolved by `code`. -/
def rtPhOkBy (code : String → Option Nat) (Λ : Scc.Sem.Layout) (tab : List PhFact) : Bool :=
  match phTabBy code, sitesBy code Λ with
  | some T, some ss => tab.all (factOk code (fun pc => !(ss.contains pc)) T.ph)
  | _, _ => false

/-- **The runtime's phase facts**: the phase table and the sites resolve,
and every fact of `tab` passes its check (`factOk`) with them; the labels
resolved in one keyed table (`codeT`). -/
def rtPhOk (lo : Nat) (cells : List (Directive × Nat)) (Λ : Scc.Sem.Layout) (tab : List PhFact) : Bool :=
  rtPhOkBy (codeT lo cells) Λ tab

/-- **A fact of a checked table** passes its check with `codeLabel`,
`okPcOf` and `phOf`. -/
theorem factOk_of_rtPhOk {lo : Nat} {cells : List (Directive × Nat)} {Λ : Scc.Sem.Layout} {tab : List PhFact}
    (h : rtPhOk lo cells Λ tab = true) {f : PhFact} (hf : f ∈ tab) :
    factOk (codeLabel lo cells) (okPcOf lo cells Λ) (phOf lo cells) f = true := by
  unfold rtPhOk at h
  rw [codeT_eq] at h
  unfold rtPhOkBy at h
  split at h
  · next T ss hT hs =>
    have hph : phOf lo cells = T.ph := by unfold phOf phTabOf; rw [hT]
    have hok : okPcOf lo cells Λ = fun pc => !(ss.contains pc) := by
      funext pc; unfold okPcOf sitesOf; rw [hs]
    rw [hph, hok]
    exact List.all_eq_true.mp h f hf
  · cases h

end Scc.Cert.Rt.X64
