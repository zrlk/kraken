/-
Test support: the private-memory domain invariant (`Kernel.OwnDom`,
`Scc/Sem/OwnDom.lean`) checked along a deterministic run (`Run.lean`).

Not part of the statement and not trusted: a satisfiability check of
`OwnDom`'s fields on real compiler output, with `E := initDom Entry.linux`.

- `domCheap`: at a configuration, every thread's private memory has as many
  mapped bytes as its initial stack (thread 0) plus the ranges it holds;
  the held ranges are nonempty, inside the pool and the address space, held
  by slots that are not dormant and pairwise disjoint; the initial stack
  avoids the pool and slot 0 is not dormant.
- `domFull`: `domCheap`, and every byte of the initial stack and of each
  held range is mapped in its owner's private memory. With the count, the
  domain is exactly `initDom ∪ HeldAt`.
- `checkRun`: the run, `domCheap` at every configuration, `domFull` at the
  first and last ones and on both sides of every take and release, and at a
  take no byte of the range mapped before it (`OwnDom.take_unmapped`).
-/
import Scc.Sem.Test.Run

namespace Scc.Sem.Test

open Kraken.Promising

variable {I : ISA} (K : Kernel.Abi I) (A : Arch)

/-- The cheap half of `OwnDom` at `c`, for the initial stack `E`. -/
def domCheap (E : Range) (c : Config I × Kernel.KState) : Bool :=
  let held := c.2.held
  let ts := (List.range c.1.threads.size).filterMap fun i => (c.1.threads[i]?).map (i, ·)
  ts.all (fun (i, t) =>
      (K.dmem t.st).size ==
        (if i = 0 then E.size else 0) + ((held.filter (·.1 == i)).map (·.2.size)).sum) &&
    held.all (fun h => 0 < h.2.size && c.2.pool.lo ≤ h.2.lo && h.2.lo + h.2.size ≤ c.2.pool.lo + c.2.pool.size &&
      h.2.lo + h.2.size ≤ 2 ^ 64 && c.2.slots[h.1]? != some .dormant) &&
    (held.zipIdx.all fun (h, i) => (held.drop (i + 1)).all fun h' => !Kernel.overlaps h.2 h'.2.lo h'.2.size) &&
    !Kernel.overlaps c.2.pool E.lo E.size && c.2.slots[0]? != some .dormant

/-- Every byte of `r` is mapped in `m`. -/
def allMapped (m : _root_.Mem 64) (r : Range) : Bool := (Kernel.addrs r).all fun a => (m[a]?).isSome

/-- No byte of `r` is mapped in `m`. -/
def noneMapped (m : _root_.Mem 64) (r : Range) : Bool := (Kernel.addrs r).all fun a => (m[a]?).isNone

/-- `OwnDom` at `c`, for the initial stack `E`: `domCheap`, and every byte
of the initial stack and of each held range mapped in its owner's private
memory. -/
def domFull (E : Range) (c : Config I × Kernel.KState) : Bool :=
  domCheap K E c &&
    (c.1.threads[0]?).all (fun t => allMapped (K.dmem t.st) E) &&
    c.2.held.all fun (j, r) => (c.1.threads[j]?).all fun t => allMapped (K.dmem t.st) r

/-- The result of `checkRun`. -/
structure DomRun where
  steps : Nat := 0
  stop : String := "out of fuel"
  cheap : Nat := 0
  full : Nat := 0
  takes : Nat := 0
  releases : Nat := 0
  /-- The first step at which a check failed, and which. -/
  bad : Option (Nat × String) := none
  deriving Repr

/-- **The run with `OwnDom` checked**: as `run`, and at each configuration
`domCheap`; at a take or a release (the held list changes) `domFull` on
both sides, and before a take no byte of the range mapped. -/
def checkRun (pcf : I.State → Nat) (μ : Test.RunMarks) (E : Range) :
    Nat → Nat → (Config I × Kernel.KState) → DomRun → DomRun
  | 0, _, c, r =>
    if domFull K E c then { r with full := r.full + 1 } else { r with bad := r.bad <|> some (r.steps, "final") }
  | fuel + 1, tid, c, r =>
    let r := if domCheap K E c then { r with cheap := r.cheap + 1 }
      else { r with bad := r.bad <|> some (r.steps, "cheap") }
    let fin (r : DomRun) (stop : String) : DomRun :=
      let r := { r with stop }
      if domFull K E c then { r with full := r.full + 1 } else { r with bad := r.bad <|> some (r.steps, "final") }
    if c.2.exited.isSome then fin r "exited" else
    let n := c.1.threads.size
    match (List.range n).map (fun i => (tid + i) % n) |>.find? (c.2.runs ·) with
    | none => fin r "no running thread"
    | some t =>
      match stepOf K A pcf μ t c with
      | .error m => fin r m
      | .ok (_, c') =>
        let r := { r with steps := r.steps + 1 }
        let r :=
          if c'.2.held.length > c.2.held.length then
            let ok := domFull K E c && domFull K E c' &&
              (c.1.threads[t]?).all fun th => noneMapped (K.dmem th.st) (Kernel.siteRange K th.st)
            if ok then { r with takes := r.takes + 1, full := r.full + 2 }
            else { r with bad := r.bad <|> some (r.steps, "take") }
          else if c'.2.held.length < c.2.held.length then
            if domFull K E c && domFull K E c' then { r with releases := r.releases + 1, full := r.full + 2 }
            else { r with bad := r.bad <|> some (r.steps, "release") }
          else r
        checkRun pcf μ E fuel (t + 1) c' r

end Scc.Sem.Test
