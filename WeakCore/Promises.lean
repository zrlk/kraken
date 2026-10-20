/-
# Stage 2, take two: promises instead of out-of-order issue

The other candidate for stage 2 was a *staged* front-end, where bind returns a
register name rather than a value.  It was prototyped: it reproduced all 23
litmus tests exactly, and it cost `mvcgen` entirely, because its Hoare triples
range over the code generator rather than the machine.  The prototype itself
is deleted.

The reason it needed staging at all was that half the relaxed behaviour in
`WeakMem.lean` lives in the *scheduler* (`issuable`), which lets an agent
execute an instruction before an earlier one.  A `do`-block runs in program
order and so cannot drive that rule.

This file removes the need for it.  Instructions are issued strictly in program
order -- `stepThread` looks only at `th.prog.head?`, and `mayReorder` /
`issuable` are gone.  The relaxed behaviour they used to provide comes instead
from **promises** (Promising-ARM, PLDI 2019):

  * a thread may append a message to memory *ahead of time*, recording its
    timestamp in `Thread.promises`;
  * a later store may **fulfill** a matching promise instead of appending, so
    it lands at a timestamp *below* stores that were issued after the promise;
  * `Config.done` requires every promise set to be empty, so a thread cannot
    promise something it never writes.

That is what buys back store→store and load→store reordering *as observed by
other agents*, without the issuing agent ever running out of order.  Program
order is preserved, so a `do`-notation front-end over this machine drives every
rule -- which is what D4 needs.

The point of the prototype is that this is checkable rather than arguable: the
same `Litmus` values -- 89<!--@suite--> of them now -- with the same herd7-derived
expectations, are re-run against this machine.  §4 additionally ablates each new
rule, which is where the non-obvious content is.

## Credits

The promise mechanism is not ours.  It is due to:

  * Jeehoon Kang, Chung-Kil Hur, Ori Lahav, Viktor Vafeiadis, Derek Dreyer.
    "A promising semantics for relaxed-memory concurrency."  POPL 2017.
    doi:10.1145/3009837.3009850 -- the origin of promises.
  * Christopher Pulte, Jean Pichon-Pharabod, Jeehoon Kang, Sung-Hwan Lee,
    Chung-Kil Hur.  "Promising-ARM/RISC-V: a simpler and faster operational
    concurrency model."  PLDI 2019.  doi:10.1145/3314221.3314624 --
    the hardware-level form this file follows: program-order issue, per-thread
    views, `coh`, read bounds, promises in place of a reordering scheduler.
    Artifact: github.com/snu-sf/promising-arm.

    The discharge rule above -- promises need only be empty when the run ends,
    with no per-step certification -- is that paper's **Global-Promising**
    variant, not the certified one.

The architectures and the reference models this is gated against are likewise
other people's:

  * Christopher Pulte, Shaked Flur, Will Deacon, Jon French, Susmit Sarkar,
    Peter Sewell.  "Simplifying ARM concurrency: multicopy-atomic axiomatic and
    operational models for ARMv8."  POPL 2018.  doi:10.1145/3158107.
  * Peter Sewell, Susmit Sarkar, Scott Owens, Francesco Zappa Nardelli,
    Magnus O. Myreen.  "x86-TSO: a rigorous and usable programmer's model for
    x86 multiprocessors."  CACM 53(7):89-97, 2010.  doi:10.1145/1785414.1785443
    -- the `.tso` architecture threaded through this file.
  * Jade Alglave, Luc Maranget, Michael Tautschnig.  "Herding cats: modelling,
    simulation, testing, and data mining for weak memory."  TOPLAS 36(2):7,
    2014.  doi:10.1145/2627752 -- the `cat` language and herd7, which
    `check-herd.sh` runs.  The models under `cats/` are herdtools7's, with our
    axioms added.

Note what is *not* claimed: Promising-ARM/RISC-V is proved equivalent to the
official ARMv8 axiomatic model in Coq, by its authors, and that proof is not
reproduced here.  This machine also is not theirs -- it has `undef`,
allocations, ownership and a `do`-notation front end, and no ISA semantics.  The
evidence it offers instead is the 40-shape herd7 agreement and §16's containment
theorem.

Build:  ./check-promises.sh
-/

import WeakCore.WeakMem
import Std.Tactic.Do
import Lean

namespace Promises

open WeakMem Std.Do

set_option mvcgen.warning false

/-! ## 0. A tactic, because the proofs below would otherwise be unmaintainable

`mvcgen` discharges into goals whose hypotheses are all *inaccessible*, and the
only core tactic for getting at them is `rename_i`, which names the last `n` by
position.  That does not scale here.  The composition proof in §9.1 needs
thirty-five names to reach the thirteen it uses, and the count includes the
`__do_jp` continuations an `if` leaves behind and the scrutinee equations of
every `match` -- none of which correspond to anything in the program.  Worse,
`rename_i` given too few names silently binds the *wrong* hypotheses, which is
how a proof ends up establishing something other than what it appears to.

`name_hyps` counts within one type instead.  `name_hyps Post a b c` names the
hypotheses whose type head ends in `Post`, in context order, so the names line
up with the *operations in the `do`-block* -- something a reader can check
against the program three lines above.  A trailing `..` allows further unnamed
ones; without it the count must be exact, and either way a mismatch is an error
rather than a shift. -/

open Lean Elab Tactic Meta in
/-- Rename inaccessible hypotheses whose type head ends in `tag`, in context
    order.  `_` skips one; a trailing `..` allows extras. -/
elab "name_hyps " tag:ident ids:(colGt Lean.binderIdent)* rest:("..")? : tactic => do
  let suffix := tag.getId.toString
  let g ← getMainGoal
  let targets ← g.withContext do
    let mut ts : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      unless d.userName.hasMacroScopes do continue
      let ty ← instantiateMVars d.type
      if let .const n _ := ty.getAppFn then
        if n.getString!.endsWith suffix then
          ts := ts.push d.fvarId
    return ts
  if rest.isSome then
    if targets.size < ids.size then
      throwError "name_hyps {tag}: only {targets.size} in context, {ids.size} names given"
  else if targets.size != ids.size then
    throwError "name_hyps {tag}: {targets.size} in context, {ids.size} names given"
  let mut g := g
  for (fv, id) in targets.zip ids do
    match id with
    | `(Lean.binderIdent| $n:ident) => g ← g.rename fv n.getId
    | _ => pure ()
  replaceMainGoal [g]

/-! ## 1. State

Two changes to the machine state, both forced.

**`TVal.rts`.**  A register now records the *timestamp* it was read from as well
as the message view it inherited.  These must stay separate and are consumed
asymmetrically; see the ablations in §4 for the
tests that pin each half down.

**`Thread.promises`.**  Timestamps this thread has promised and not yet
fulfilled. -/

structure TVal where
  val : Val
  /-- Inherited from the message.  What the *writer* published. -/
  view : Ts
  /-- The timestamp this value was read from.  What the *reader* did. -/
  rts : Ts
  deriving Repr, Inhabited

def TVal.mk0 (v : Val) : TVal := ⟨v, 0, 0⟩

structure Thread where
  prog : List Instr
  regs : Reg → TVal
  vs : VState
  /-- Outstanding promises, as timestamps into `Config.mem`. -/
  promises : List Ts
  deriving Inhabited

def Thread.mk' (prog : List Instr) : Thread :=
  { prog := prog, regs := fun _ => TVal.mk0 (Val.num 0), vs := VState.init
    promises := [] }

structure Config where
  mem : Memory
  ths : Array Thread
  /-- Timestamps at which some pair RMW wrote its first word; the second is
      always at `p + 1`, because both are pushed in one step.  Exactly
      `WeakMem.Config.pairs`, and consulted the same way -- see the pair
      atomicity section of `WeakMem.lean` for why this is a separate field
      rather than something read off memory.

      Last field, and defaulted, so the three `Config` literals in this file
      keep working unchanged. -/
  pairs : List Ts := []
  deriving Inhabited

/-- Switches for §4.  Two kinds, and they are checked against opposite
    expectations:

    * **Rules that forbid** (`ctrlRts`, `storeDepRts`, `tsoStoreOrder`, and
      `promises` itself), and the two permissions tests need
      (`promiseViews` and `fwdView`, see their fields). Turning one off must
      break a test; one
      that breaks nothing is unjustified and should be deleted.
    * **Permissions** (`headPromise`). These widen the model.  Turning one off
      must change *nothing*, because each is either a generalisation no test
      needs or a pruning argued to be equivalence-preserving. A change here
      means the argument was wrong. -/
structure Knobs where
  /-- Allow promise steps at all.  Off = strictly in-order, no early writes. -/
  promises : Bool := true
  /-- `branch` joins the read timestamp (`rts`) rather than the message view. -/
  ctrlRts : Bool := true
  /-- A store's ordering bound uses `rts` of its dependencies, not their view. -/
  storeDepRts : Bool := true
  /-- Under TSO a store's timestamp is additionally bounded by `vRd`/`vWr`,
      i.e. store→store and load→store are ordered. -/
  tsoStoreOrder : Bool := true
  /-- Promise with any view below the promise's own timestamp.  Off = view 0,
      which is where this started and which had no justification.  It was a
      generality check (off changed nothing) until an RMW's write began to
      carry its read's view: `LB+casp`'s relaxed outcome needs a promised pair
      write whose read half sees the initial pair at timestamps 0 and 1, so a
      view-0 promise can no longer be fulfilled.  Now an ablation. -/
  promiseViews : Bool := true
  /-- Also allow promising the store at the head of the program.  Off is the
      pruning; on is the unpruned model it is claimed to be equivalent to. -/
  headPromise : Bool := false
  /-- A read of one of the thread's own plain writes contributes the write's
      forwarding view (`WeakMem.VState.fwd`) rather than its timestamp and
      message view.  A permission: off, `SB+rfi-pos`, `SB+rfi-dmb.ld` and
      `SB+dmb.st-rfi-ldar+dmb.sy` come out forbidden against herd7's
      `Sometimes`.  Gates only the entries `stepStore` records; `stepStorePair`
      (no knobs) always records its own. -/
  fwdView : Bool := true
  deriving Inhabited

def Knobs.all : Knobs := {}

/-! ## 2. Transition rules -/

def depView (regs : Reg → TVal) (deps : List Reg) : Ts :=
  deps.foldl (fun acc r => max acc (regs r).view) 0

def depRts (regs : Reg → TVal) (deps : List Reg) : Ts :=
  deps.foldl (fun acc r => max acc (regs r).rts) 0

/-- The dependency bound a **load** must respect: both the view a dependency
    inherited and the timestamp it was read from.

    The `rts` half is the one that does the work, and it was missing until the
    generated suite (§10) found it.  ARM has `ob ⊇ obs; dob`: a read that
    reads-from an external write is ordered after that write, and a
    dependency-ordered access is ordered after the read.  In a timestamp model
    "ordered after the write at `t`" is exactly "bound ≥ t", and only `rts`
    carries `t`.  Using `view` alone models the *writer's* release path and
    silently drops the `rf` edge, which is why `WRC+data+addr`, `WRC+addrs`,
    `IRIW+addrs` and five siblings came out allowed against herd7's `forbidden`.

    This is the same asymmetry `depRts` already gives a *store*'s bound
    (`storeDepRts`); the load was the last consumer still on `view` alone.

    It does **not** forbid `MP+po+addr`, although it was once claimed it
    would: there the writer may publish `y` before `x`, so the reader's bound
    does not reach the later write of `x` and reading `0` stays legal.  The
    freedom comes from promising here and from `issuable` in `WeakMem.lean`, and
    the §8.1 claim predates both. -/
def depBound (regs : Reg → TVal) (deps : List Reg) : Ts :=
  max (depView regs deps) (depRts regs deps)


/-- **The read bound, and one of the nine places the architecture shows up.**

    Factored out because `stepLoad`, `stepRmw` and `stepRmwPair` had it written
    out identically three times, and §15's refinement needs to say something
    about it once rather than three times.  Naming it also makes the
    architecture-sensitive points auditable: they are exactly the `def`s that
    take an `Arch`.

    `ordered` is the whole difference.  TSO orders load→load, so a load may not
    take a timestamp below anything already read; ARM does not, and passes `0`,
    which is no constraint at all.  Since the two differ only by a `max` against
    a non-negative quantity, **ARM's bound is always the smaller** -- which is
    the direction the containment argument needs, because a smaller bound hides
    fewer writes (`readable_antitone`, §15). -/
def readBoundOf (arch : Arch) (vs : VState) (dv : Ts) (a : Address) : Ts :=
  let ordered := if arch = .tso then vs.vRd else 0
  max (max (max vs.vPreBase dv) (vs.coh a)) ordered

/-- **Single-copy atomicity, reader side.**  See `WeakMem.pairTop` for the
    argument; this is the same function, restated here because `Promises` does
    not import the rules it replaces.

    In one line: observing either word of a pair RMW's write means observing
    the whole of it, so a read at the pair's first word contributes `t + 1`,
    not `t`, to `vRd`.  Without it the model forbids a torn ordered read in one
    word order and allows it in the other. -/
def pairTop (pairs : List Ts) (t : Ts) : Ts :=
  if pairs.contains t then t + 1 else t

/-- `pairTop` only ever moves a timestamp up, so every bound that used to be
    stated against `t` still holds. -/
theorem le_pairTop (pairs : List Ts) (t : Ts) : t <= pairTop pairs t := by
  unfold pairTop
  split
  . exact Nat.le_succ t
  . exact Nat.le_refl t

/-- The shape `LoadPost.rd` needs: what a load *reports* is bounded by `t` and
    the message view, while what it *records* is bounded by `pairTop t` and the
    message view, and the first is below the second.  Stated separately because
    `le_max_le` lives in §15, far below this. -/
theorem pairTop_max_le (pairs : List Ts) (t w base : Ts) :
    max t w <= max base (max (pairTop pairs t) w) := by
  -- Not `omega`: `Ts` is an `abbrev` for `Nat`, and `omega` does not see `max`
  -- through it.  Same trap as with `Offset`.
  refine Nat.max_le.mpr ⟨?_, ?_⟩
  . exact Nat.le_trans (Nat.le_trans (le_pairTop pairs t) (Nat.le_max_left _ _))
      (Nat.le_max_right _ _)
  . exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- What a read of `t` carrying message view `mv` adds to `vRd`: the forwarding
    view of an own plain write (`WeakMem.ownFwd`), else `pairTop t` and `mv`.
    `WeakMem.fwdRd`, restated against this file's `pairTop`. -/
def rdV (vs : VState) (pairs : List Ts) (t mv : Ts) : Ts :=
  (ownFwd vs t).getD (max (pairTop pairs t) mv)

/-- What an acquire read of `t` adds to `vPreBase`: the forwarding view of an
    own plain write, else `mv` and `extTs`.  `WeakMem.fwdAcq`. -/
def acqV (vs : VState) (pairs : List Ts) (t mv : Ts) : Ts :=
  (ownFwd vs t).getD (max mv (extTs vs pairs t))

/-- The forwarding view a plain store records: its address and data registers'
    `depBound`.  `WeakMem.storeFwdW`, over this file's registers. -/
def fwdOf (regs : Reg → TVal) (e : Expr) (deps : List Reg) : Ts :=
  depBound regs (deps ++ match e with | .const _ => [] | .reg r => [r])

/-- A wide store's forwarding view, shared by both words: the dependencies of
    both data registers and the address. -/
def pairFwdOf (regs : Reg → TVal) (e0 e1 : Expr) (deps : List Reg) : Ts :=
  fwdOf regs e0 (deps ++ match e1 with | .const _ => [] | .reg r => [r])

theorem ownFwd_le {vs : VState} {t f : Ts} (h : ownFwd vs t = some f) : f ≤ t := by
  unfold ownFwd at h
  split at h
  · cases hf : vs.fwd.find? (fun p => p.1 == t) with
    | none => rw [hf] at h; cases h
    | some p => rw [hf] at h; cases h; exact Nat.min_le_left _ _
  · cases h

theorem rdV_le (vs : VState) (pairs : List Ts) (t mv : Ts) :
    rdV vs pairs t mv ≤ max (pairTop pairs t) mv := by
  unfold rdV
  cases h : ownFwd vs t with
  | none => exact Nat.le_refl _
  | some f =>
      exact Nat.le_trans (ownFwd_le h)
        (Nat.le_trans (le_pairTop pairs t) (Nat.le_max_left _ _))

theorem acqV_le (vs : VState) (pairs : List Ts) (t mv : Ts) :
    acqV vs pairs t mv ≤ max mv (extTs vs pairs t) ∨ acqV vs pairs t mv ≤ t := by
  unfold acqV
  cases h : ownFwd vs t with
  | none => exact Or.inl (Nat.le_refl _)
  | some f => exact Or.inr (ownFwd_le h)

theorem rdV_none {vs : VState} {pairs : List Ts} {t : Ts} (mv : Ts) (h : ownFwd vs t = none) :
    rdV vs pairs t mv = max (pairTop pairs t) mv := by
  unfold rdV; rw [h]; rfl

theorem acqV_none {vs : VState} {pairs : List Ts} {t : Ts} (mv : Ts) (h : ownFwd vs t = none) :
    acqV vs pairs t mv = max mv (extTs vs pairs t) := by
  unfold acqV; rw [h]; rfl

/-- Unchanged from `WeakMem.stepLoad` except that the register now also records
    `t`.  A load's dependency bound is `depBound`, which joins the read
    timestamp; see there for why, and for why that does not forbid
    `MP+po+addr`. -/
def stepLoad (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst : Reg) (a : Address) (deps : List Reg) (acq : Bool) : List Thread :=
  let vs := th.vs
  let bound := readBoundOf arch vs (depBound th.regs deps) a
  let cands := (List.range mem.size).filter fun t => readable mem a t bound
  cands.map fun t =>
    let m := mem[t]!
    let tv : TVal := ⟨m.val, m.view, t⟩
    let vs' : VState :=
      { vs with
        coh := fun b => if b = a then max (vs.coh a) t else vs.coh b
        vRd := max vs.vRd (rdV vs pairs t m.view)
        vPreBase := if acq then max vs.vPreBase (acqV vs pairs t m.view) else vs.vPreBase }
    { th with
      regs := fun r => if r = dst then tv else th.regs r
      vs := vs' }

/-- What a store publishes to its readers.  Identical to `WeakMem.stepStore`'s
    `mview`, including its use of the dependency *view* rather than `rts` --
    this half of the rule was validated against herd7 in stage 1 and is left
    alone. -/
def storeMview (th : Thread) (e : Expr) (deps : List Reg) (rel : Bool) : Ts :=
  let vs := th.vs
  let dataView := match e with
    | .const _ => 0
    | .reg r => (th.regs r).view
  let dv := max (depView th.regs deps) dataView
  if rel then max (max vs.vRelSt (max vs.vRd vs.vWr)) dv
  else max vs.vRelSt dv

/-- **Side condition 2**, and the entire forbidding power of the promise rule.

    A store may not take a timestamp below anything that orders it: preceding
    fences (`vPreBase`), its own dependencies, a preceding branch (`vCtrl`), or
    a preceding write to the same location (`coh a`).  For an ordinary append
    this is free -- `t = mem.size` exceeds every timestamp in existence -- so it
    only ever bites on a fulfillment, which is exactly where it should.

    Note what is *absent* on ARM: `vRd` and `vWr`.  ARM reorders load→store and
    store→store, so a preceding load or store must not bound this one.  TSO does
    order both, and that single addition is what keeps `MP` and `LB` forbidden
    there. -/
def storeOb (k : Knobs) (arch : Arch) (th : Thread) (a : Address) (e : Expr)
    (deps : List Reg) : Ts :=
  let vs := th.vs
  let dataRegs := match e with
    | .const _ => []
    | .reg r => [r]
  let all := deps ++ dataRegs
  let dTs := if k.storeDepRts then depRts th.regs all else depView th.regs all
  let base := max (max vs.vPreBase dTs) (max vs.vCtrl (vs.coh a))
  if arch = .tso && k.tsoStoreOrder then max base (max vs.vRd vs.vWr) else base

/-- A store either appends, or fulfills one of its thread's promises. -/
def stepStore (k : Knobs) (arch : Arch) (mem : Memory) (th : Thread) (a : Address)
    (e : Expr) (deps : List Reg) (rel : Bool) : List (Memory × Thread) :=
  let v := match e with
    | .const c => c
    | .reg r => (th.regs r).val
  let mview := storeMview th e deps rel
  let ob := storeOb k arch th a e deps
  let vs := th.vs
  let commit (mem' : Memory) (t : Ts) (prom : List Ts) : Memory × Thread :=
    (mem', { th with
      vs := { vs with
              coh := fun b => if b = a then t else vs.coh b
              vWr := max vs.vWr t, mine := t :: vs.mine
              fwd := if k.fwdView then (t, fwdOf th.regs e deps) :: vs.fwd else vs.fwd }
      promises := prom })
  let appended := [commit (mem.push ⟨a, v, mview⟩) mem.size th.promises]
  let fulfilled := th.promises.filterMap fun t =>
    match mem[t]? with
    | none => none
    | some m =>
        -- Side condition 1: the promised message view must cover what this
        -- store actually publishes.  Promises are made with view 0 (see
        -- `promiseSteps`), so in practice this says a promised store may not
        -- follow a `dmb ishst` or carry a dependency -- which is precisely why
        -- `MP+dmb.st+po` stays forbidden while `MP+po+dmb.ld` does not.
        if m.loc == a && m.val == v && mview ≤ m.view && ob < t then
          some (commit mem t (th.promises.erase t))
        else none
  appended ++ fulfilled

def stepFence (th : Thread) (f : Fence) : Thread :=
  let vs := th.vs
  let vs' := match f with
    | .ld => { vs with vPreBase := max vs.vPreBase vs.vRd }
    | .st => { vs with vRelSt := max vs.vRelSt vs.vWr }
    | .sy => { vs with
                 vPreBase := max vs.vPreBase (max vs.vRd vs.vWr)
                 vRelSt := max vs.vRelSt (max vs.vRd vs.vWr) }
  { th with vs := vs' }

/-- The value an RMW writes: its constant, or its register's value.  The same
    function as the `v` of `stepStore`, named because the RMW rule uses it twice
    (append and fulfil) and its simulation proof states it. -/
def rmwNewVal (regs : Reg → TVal) : Expr → Val
  | .const c => c
  | .reg r => (regs r).val

/-- What an RMW leaves in its destination register.  The value read, with the
    read's view and timestamp -- except after a *successful non-acquire*
    `CAS`, which returns the value with no dependency at all (herd7's
    `aarch64_cas_ok`): not on the read, and not on whatever the comparand
    register depended on before -- herd7 allows `MP+dmb.sy+ldr-cas-addrRs`,
    where it was loaded first, and forbids the same shape without the
    `CAS`.
    `MP+dmb.sy+cas-addrRs` and `MP+dmb.sy+casl-addrRs` are the tests; the
    `casa`/`casal` variants are the controls. -/
def rmwDst (kind : RmwKind) (acq : Bool) (m : Msg) (t : Ts) : TVal :=
  match kind with
  | .cas _ => if rmwSucceeds kind m.val && !acq then ⟨m.val, 0, 0⟩ else ⟨m.val, m.view, t⟩
  | _ => ⟨m.val, m.view, t⟩

/-- An RMW, which may append *or fulfill a promise* like any other write.

    This is where the promise machine earns the generality of
    `WeakMem.rmwAdjacent`.  In the stage-1 machine the write always lands at
    `mem.size`, so "adjacent in modification order" could have been written as
    the much simpler "the read is from the coherence-latest write".  Here the
    write may land at a promised timestamp in the *middle* of memory, and only
    the general form still says the right thing.

    It also turns out to be exactly what keeps atomicity intact under
    promising, which was the thing most likely to go wrong.  Two agents
    promising a take of the same location cannot both fulfill: the later slot's
    RMW would have to read either a value that fails its comparison, or one
    with the other promise sitting between it and its own write.  That is not
    an extra side condition -- it is `rmwAdjacent` doing its job, and
    `CASAtomic` is the test that checks it. -/
def stepRmwAt (k : Knobs) (arch : Arch) (mem : Memory) (pairs : List Ts)
    (th : Thread) (dst : Reg)
    (a : Address) (kind : RmwKind) (newv : Expr) (deps : List Reg)
    (acq rel : Bool) : List (Memory × Thread) :=
  let vs := th.vs
  let bound := readBoundOf arch vs (depBound th.regs deps) a
  -- On x86 a locked read-modify-write is a full barrier, so an RMW there
  -- carries `MFENCE`'s view update too.  Mirrors `WeakMem.stepRmw`; see the
  -- comment there for why it applies to a failed CAS as well.
  let lockFence (t : Thread) : Thread :=
    if arch = .tso then stepFence t .sy else t
  let cands := (List.range mem.size).filter fun t => readable mem a t bound
  cands.flatMap fun t =>
    let m := mem[t]!
    -- The read half, identical to `stepLoad`, `pairTop` included.
    let readVs : VState :=
      { vs with
        coh := fun b => if b = a then max (vs.coh a) t else vs.coh b
        vRd := max vs.vRd (rdV vs pairs t m.view)
        vPreBase := if acq then max vs.vPreBase (acqV vs pairs t m.view) else vs.vPreBase }
    let readTh : Thread :=
      { th with
        regs := fun r => if r = dst then rmwDst kind acq m t else th.regs r
        vs := readVs }
    if !rmwSucceeds kind m.val then
      -- Failed CAS: an ordinary load.  It cannot fulfill anything, because it
      -- writes nothing.
      [(mem, lockFence readTh)]
    else
      -- The write half.  Both halves of the store rule apply, computed against
      -- the views the read already updated: the write of an RMW follows its
      -- own read, and in particular `readVs.coh a ≥ t`.
      --
      -- The new value's register, if it is one, is a data dependency of the
      -- write, exactly as a store's is (`storeMview`, `storeOb`): it joins
      -- `dv` and `dTs`, and stays out of the read's `bound`.  Value and
      -- dependency are taken from the registers before the read, since `dst`
      -- may be the same register.
      -- A fetch-op's write is a function of the value read; a swap's or a
      -- CAS's is the operand itself (`RmwKind.apply`).
      let wv := kind.apply m.val (rmwNewVal th.regs newv)
      let wdeps := newv.writeDeps deps
      let dv := depView th.regs wdeps
      -- `rv`, the read half's view, rides in the message so that an acquire
      -- reading this write -- the thread's own included -- is ordered after
      -- the RMW's read (ARM `aob`, via `rmw` then `lrs`).  Mirrors
      -- `WeakMem.stepRmw`; see the comment there.
      let rv := max (pairTop pairs t) m.view
      let wvs := { readVs with vRelSt := max readVs.vRelSt rv }
      let mview :=
        if rel then max (max wvs.vRelSt (max wvs.vRd wvs.vWr)) dv
        else max wvs.vRelSt dv
      let dTs := if k.storeDepRts then depRts th.regs wdeps else dv
      let base := max (max readVs.vPreBase dTs) (max readVs.vCtrl (readVs.coh a))
      let ob :=
        if arch = .tso && k.tsoStoreOrder then max base (max readVs.vRd readVs.vWr)
        else base
      let commit (mem' : Memory) (tw : Ts) (prom : List Ts) : Memory × Thread :=
        (mem', lockFence
          { readTh with
            vs := { readVs with
                    coh := fun b => if b = a then tw else readVs.coh b
                    vWr := max readVs.vWr tw, mine := tw :: readVs.mine }
            promises := prom })
      let appended :=
        if rmwAdjacent mem a t mem.size then
          [commit (mem.push ⟨a, wv, mview⟩) mem.size th.promises]
        else []
      let fulfilled := th.promises.filterMap fun tw =>
        match mem[tw]? with
        | none => none
        | some pm =>
            if pm.loc == a && pm.val == wv && mview ≤ pm.view && ob < tw &&
               rmwAdjacent mem a t tw then
              some (commit mem tw (th.promises.erase tw))
            else none
      appended ++ fulfilled

/-- **The RMW rule**: `stepRmwAt` after a leading `lockFence`.  On x86 a
    locked read-modify-write is a full barrier on *both* sides: its read is
    ordered after every earlier access, so the fence comes before the read
    bound is taken as well as after the write (`stepRmwAt`'s own `lockFence`).
    Without the leading fence a *failed* `lock cmpxchg` read ahead of an
    earlier store and `SB+cmpxchg-fails` was allowed, against herd7 and
    `cats/x86tso-mixed-rmw.cat`.  ARM's `CAS`/`SWP` carry no fence, and on ARM
    this is `stepRmwAt` itself. -/
def stepRmw (k : Knobs) (arch : Arch) (mem : Memory) (pairs : List Ts)
    (th : Thread) (dst : Reg)
    (a : Address) (kind : RmwKind) (newv : Expr) (deps : List Reg)
    (acq rel : Bool) : List (Memory × Thread) :=
  stepRmwAt k arch mem pairs (if arch = .tso then stepFence th .sy else th) dst a kind newv deps acq rel

/-- Two-word compare-and-swap, the promise-machine copy of
    `WeakMem.stepRmwPair`.  Same rule, plus this file's `TVal.rts` and a
    fulfilment branch.

    **A pair fulfils two promises at once, or none.**  This was not the first
    attempt.  A pair write is two messages and a promise is one timestamp, so
    the obvious reading is that a pair cannot be promised at all, and the
    obvious argument for it is that promises model a store buffer while an RMW
    is the synchronisation point a buffer drains at.

    That argument is wrong, and `LB+casp` says so.  Its relaxed outcome needs
    each thread's pair write to be visible to the other thread's *earlier*
    load, which on the stage-1 machine comes from out-of-order issue -- and
    out-of-order issue is exactly what this file replaced with promises.  Made
    append-only, `LB+casp` came out with fewer states here than in
    `WeakMem.lean` and the harness said so.

    This is the same failure, in pair form, that `constStores` already records
    for `LB+cas`: an RMW's write is a promise candidate on the same terms as a
    store's.

    What stays true is that the two words move together.  `pairPromiseCands`
    and the pair branch of `promiseSteps` push both at `(n, n+1)` in one step
    and promise both timestamps; this function will only discharge them
    together.  There is no state in which one word of a pair is promised and
    the other is not, which is what pair atomicity means. -/
def stepRmwPairAt (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst0 dst1 : Reg) (a : Address) (cmp0 cmp1 : Val) (new0 new1 : Expr)
    (deps : List Reg) (acq rel : Bool) : List (Memory × List Ts × Thread) :=
  let a0 := a
  let a1 := a.next
  let vs := th.vs
  -- Two different dependency quantities, and they must not be conflated: the
  -- *read* side joins `rts` (`depBound`), the *publication* view does not (it
  -- is `storeMview`'s rule, validated in stage 1 and left alone).
  --
  -- The new values' registers, if any, are data dependencies of both writes:
  -- they join `dv` and `dTs`, never the read's bound.  Values come from the
  -- registers before the read (`dst0`/`dst1` may alias them), as in `stepRmw`.
  let wdeps := new1.writeDeps (new0.writeDeps deps)
  let wv0 := rmwNewVal th.regs new0
  let wv1 := rmwNewVal th.regs new1
  let dv := depView th.regs wdeps
  let bnd := fun (b : Address) => readBoundOf arch vs (depBound th.regs deps) b
  let lockFence (t : Thread) : Thread :=
    if arch = .tso then stepFence t .sy else t
  let c0 := (List.range mem.size).filter fun t => readable mem a0 t (bnd a0)
  let c1 := (List.range mem.size).filter fun t => readable mem a1 t (bnd a1)
  c0.flatMap fun t0 => c1.flatMap fun t1 =>
    -- The reads must be a consistent snapshot.  Unlike the write side this
    -- does not fall out of adjacency, because a *failing* pair writes nothing.
    if pairStraddles mem pairs a0 t0 t1 then []
    else
      let m0 := mem[t0]!
      let m1 := mem[t1]!
      let readVs : VState :=
        { vs with
          coh := fun b =>
            if b = a0 then max (vs.coh a0) t0
            else if b = a1 then max (vs.coh a1) t1
            else vs.coh b
          vRd := max vs.vRd (max (rdV vs pairs t0 m0.view) (rdV vs pairs t1 m1.view))
          vPreBase :=
            if acq then max vs.vPreBase (max (acqV vs pairs t0 m0.view) (acqV vs pairs t1 m1.view))
            else vs.vPreBase }
      let readTh : Thread :=
        { th with
          regs := fun r =>
            if r = dst0 then ⟨m0.val, m0.view, t0⟩
            else if r = dst1 then ⟨m1.val, m1.view, t1⟩
            else th.regs r
          vs := readVs }
      if !(decide (m0.val = cmp0) && decide (m1.val = cmp1)) then
        -- Failed compare: two ordinary loads.  It cannot fulfil anything,
        -- because it writes nothing.
        [(mem, pairs, lockFence readTh)]
      else
        -- `rv`: see `stepRmw`.
        let rv := max (max (pairTop pairs t0) m0.view) (max (pairTop pairs t1) m1.view)
        let wvs := { readVs with vRelSt := max readVs.vRelSt rv }
        let mview :=
          if rel then max (max wvs.vRelSt (max wvs.vRd wvs.vWr)) dv
          else max wvs.vRelSt dv
        let dTs := depRts th.regs wdeps
        let base := max (max readVs.vPreBase dTs) (max readVs.vCtrl (readVs.coh a0))
        let ob :=
          if arch = .tso then max base (max readVs.vRd readVs.vWr) else base
        let commit (mem' : Memory) (pairs' : List Ts) (tw0 tw1 : Ts)
            (prom : List Ts) : Memory × List Ts × Thread :=
          (mem', pairs', lockFence
            { readTh with
              vs := { readVs with
                      coh := fun b =>
                        if b = a0 then tw0
                        else if b = a1 then tw1
                        else readVs.coh b
                      vWr := max readVs.vWr tw1, mine := (tw1 - 1) :: tw1 :: readVs.mine }
              promises := prom })
        let appended :=
          if rmwAdjacent mem a0 t0 mem.size && rmwAdjacent mem a1 t1 (mem.size + 1) then
            [commit ((mem.push ⟨a0, wv0, mview⟩).push ⟨a1, wv1, mview⟩)
               (pairs ++ [mem.size]) mem.size (mem.size + 1) th.promises]
          else []
        -- Fulfilment.  `tw0` and `tw0 + 1` must *both* be outstanding and both
        -- must match, and both are erased: a pair never discharges half of
        -- itself.  `pairs` is not extended -- the promise step already did it,
        -- and `tw0 ∈ pairs` is *required* rather than assumed: two adjacent
        -- *single* promises (from `promiseCands`, say of later plain stores of
        -- the same values) are not a pair, and discharging them here would
        -- leave a pair write that `pairTop` and `pairStraddles` do not know
        -- about, so a reader could see it torn.  `CASPFulfilSingles` is the
        -- witness; without this conjunct it is reachable and herd forbids it.
        let fulfilled := th.promises.filterMap fun tw0 =>
          let tw1 := tw0 + 1
          match mem[tw0]?, mem[tw1]? with
          | some pm0, some pm1 =>
              if pairs.contains tw0 && th.promises.contains tw1 &&
                 pm0.loc == a0 && pm0.val == wv0 && mview ≤ pm0.view &&
                 pm1.loc == a1 && pm1.val == wv1 && mview ≤ pm1.view &&
                 ob < tw0 &&
                 rmwAdjacent mem a0 t0 tw0 && rmwAdjacent mem a1 t1 tw1 then
                some (commit mem pairs tw0 tw1
                  ((th.promises.erase tw0).erase tw1))
              else none
          | _, _ => none
        appended ++ fulfilled

/-- **The pair RMW rule**: `stepRmwPairAt` after a leading `lockFence`, for
    the reason given at `stepRmw`. -/
def stepRmwPair (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst0 dst1 : Reg) (a : Address) (cmp0 cmp1 : Val) (new0 new1 : Expr)
    (deps : List Reg) (acq rel : Bool) : List (Memory × List Ts × Thread) :=
  stepRmwPairAt arch mem pairs (if arch = .tso then stepFence th .sy else th) dst0 dst1 a cmp0 cmp1
    new0 new1 deps acq rel


/-! ### The promise step

Promising-ARM lets a thread promise an arbitrary message and then requires it to
*certify* that it can run to completion fulfilling every promise.  Certification
is a fixpoint and is not cheap to execute, so the candidate set is narrowed
syntactically instead.  Each narrowing is stated with the reason it is safe,
because a narrowing that is *not* safe makes the model forbid behaviours real
hardware allows -- the unsound direction.

**Which `(address, value)` pairs.**  Those that some `store a (.const v)` still
ahead in this thread's program will write.  This is not really an
approximation: a promise must be fulfilled for the run to count
(`Config.done`), and only a matching store of this thread can fulfill it, so
promising anything else is a dead branch.  The one genuine gap is
`store a (.reg r)`, whose value is not known at promise time.  The suite
contains no such store -- `wellFormedPromises` below checks that -- so for what
is tested here the narrowing is exact.

**Not the head store.**  Promising the store at the head of the program is
pointless: nothing of this thread's can run between the promise and its
fulfilment, so it produces exactly the schedules that executing the store now
already produces.  This is what keeps IRIW cheap (its writers are a single
store each, so they promise nothing).  The argument is a hand-wave until it is
checked, so `Knobs.headPromise` turns the pruning off and §4 reports that the
outcomes are unchanged on 50 of the 89<!--@suite--> tests -- the four it skips are the IRIW
variants, whose cost is the whole reason the pruning exists and where the
argument is anyway trivial.  See `generality` for why that exclusion is cheap.

**Which view.**  Any timestamp *strictly below the promise's own*.  This
replaces an earlier restriction to view 0, which was an artifact with no
architectural justification.

> The bound that remains is not an artifact.  A message may only publish things
> that have already happened, i.e. `view < own timestamp`.  Every store in the
> herd7-validated machine satisfies this, because `mview` joins timestamps of
> prior events and the array only grows.  It is also load-bearing for
> *soundness*: `hiddenFrom` is evaluated against memory as it stands, so a view
> pointing past the end of memory would order a reader after a write that does
> not exist yet, and that write could not hide anything.  Allowing it makes
> `MP+dmb.st+addr` reachable -- forbidden on the machine, so the bound stays.

Relaxing view 0 to "any existing timestamp" only *adds* behaviours, which is the
safe direction.  §4 reports whether any test distinguishes the two. -/

/-- The location and value of message `t`: what `promiseCands` may look at
    (`MemLe` pins both). -/
def locVal (mem : Memory) (t : Ts) : Option (Address × Val) :=
  mem[t]?.map fun m => (m.loc, m.val)

/-- The value of the latest message at `a`.  A fetch-op promised now would
    read exactly this message: its write takes the next timestamp, and
    `rmwAdjacent` lets no message at `a` come between the read and the write,
    so the read is the latest message at `a` *as memory stands at promise
    time* -- later appends land after the promise. -/
def latestVal (mem : Memory) (a : Address) : Option Val :=
  (List.range mem.size).reverse.findSome? fun t =>
    (locVal mem t).bind fun lv => if lv.1 = a then some lv.2 else none

def constStores (mem : Memory) : List Instr → List (Address × Val)
  | [] => []
  | .store a (.const v) _ _ :: rest => (a, v) :: constStores mem rest
  -- An RMW with a constant new value is a promise candidate on the same terms
  -- as a constant store, and one with a register new value is not, again like
  -- a store.  The exactness argument above
  -- survives the extra case: a *failed* CAS writes nothing, so a promise of it
  -- can never be fulfilled and the branch dies at `Config.done`, exactly as a
  -- promise no store matches does.  Without this case `LB+cas` comes out
  -- `Never` here and `Sometimes` on the stage-1 machine, which is how the
  -- omission was found.
  --
  -- A fetch-op with a constant operand writes a function of the value it
  -- reads, and `latestVal` says which value that is, so it too has exactly
  -- one candidate.  (A location never written has none, and `Litmus.initMem`
  -- seeds every location, so this does not arise in the suite.)
  | .rmw _ a kind (.const v) _ _ _ :: rest =>
      if kind.isFetch then
        match latestVal mem a with
        | some old => (a, kind.apply old v) :: constStores mem rest
        | none => constStores mem rest
      else (a, v) :: constStores mem rest
  | _ :: rest => constStores mem rest

/-- The pair writes still ahead in a program, as `(base, first, second)`.

    Deliberately *not* folded into `constStores`.  A pair write is not two
    writes that happen to be next to each other: promising its two words
    independently would let one of them be outstanding while the other was
    not, and a half-committed pair is precisely the state pair atomicity
    exists to forbid -- it is the `H-diag` witness that stock `aarch64.cat`
    admits and `cats/aarch64-pair.cat` rules out.  So pairs get their own
    candidate list and their own promise step, which pushes both words at
    once. -/
def pairStores : List Instr → List (Address × Val × Val)
  | [] => []
  -- Constant new values only, as in `constStores`.
  | .rmwPair _ _ a _ _ (.const v0) (.const v1) _ _ _ :: rest => (a, v0, v1) :: pairStores rest
  | _ :: rest => pairStores rest

/-- Does any thread store a register-valued expression?  If so the promise
    candidate set is incomplete and the suite's results are weaker than they
    look.  Reported in §4 rather than assumed. -/
def hasRegStore (L : Litmus) : Bool :=
  L.threads.any fun p => p.any fun
    | .store _ (.reg _) _ _ => true
    | _ => false

/-- The locations of the fetch-ops with a constant operand still ahead in a
    program: the candidates `constStores` computed from `latestVal` rather
    than read off the instruction. -/
def fetchLocs : List Instr → List Address
  | [] => []
  | .rmw _ a kind (.const _) _ _ _ :: rest =>
      if kind.isFetch then a :: fetchLocs rest else fetchLocs rest
  | _ :: rest => fetchLocs rest

def promiseCands (k : Knobs) (th : Thread) (mem : Memory) : List (Address × Val) :=
  let prog := if k.headPromise then th.prog else th.prog.drop 1
  let later := constStores mem prog
  let outstanding (a : Address) (v : Val) : Nat :=
    th.promises.countP fun t =>
      mem[t]?.elim false fun m => m.loc == a && m.val == v
  let wanted (a : Address) (v : Val) : Nat :=
    later.countP fun p => p.1 == a && p.2 == v
  -- A fetch-op's candidate *value* moves with memory: once `x + 1` is
  -- promised it is the latest message, and the next candidate is `x + 2`.
  -- Counting outstanding promises by value would then never catch up with
  -- `wanted`, and the chain of promises would be bounded by nothing but the
  -- fuel -- `MP+xadd+po` did not finish.  So at a location a fetch-op writes,
  -- the count is by *location*: one outstanding promise per write still ahead
  -- at `a`, whatever its value.  That is the bound `certFuel` argues from, and
  -- it is what the value count was for everywhere else.
  let fetchAt := fetchLocs prog
  let outstandingAt (a : Address) : Nat :=
    th.promises.countP fun t => (locVal mem t).any fun lv => lv.1 == a
  let writesAt (a : Address) : Nat := later.countP fun p => p.1 == a
  let uniq := later.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []
  uniq.filter fun (a, v) =>
    if fetchAt.contains a then outstandingAt a < writesAt a else outstanding a v < wanted a v

/-- `promiseCands` for pair writes.  Same exactness argument, counted over
    *pairs*: a pair is outstanding when `t` and `t + 1` are both promised and
    hold the two words. -/
def pairPromiseCands (k : Knobs) (th : Thread) (mem : Memory) :
    List (Address × Val × Val) :=
  let later := pairStores (if k.headPromise then th.prog else th.prog.drop 1)
  let outstanding (a : Address) (v0 v1 : Val) : Nat :=
    th.promises.countP fun t =>
      th.promises.contains (t + 1) &&
      (mem[t]?.elim false fun m => m.loc == a && m.val == v0) &&
      (mem[t + 1]?.elim false fun m => m.loc == a.next && m.val == v1)
  let wanted (a : Address) (v0 v1 : Val) : Nat :=
    later.countP fun p => p.1 == a && p.2.1 == v0 && p.2.2 == v1
  let uniq := later.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []
  uniq.filter fun (a, v0, v1) => outstanding a v0 v1 < wanted a v0 v1

def promiseSteps (k : Knobs) (c : Config) (i : Nat) : List Config :=
  if !k.promises then [] else
  match c.ths[i]? with
  | none => []
  | some th =>
    -- `c.mem.size` is the timestamp this promise will take, so `List.range`
    -- gives exactly the views strictly below it.
    let views := if k.promiseViews then List.range c.mem.size else [0]
    ((promiseCands k th c.mem).flatMap fun (a, v) =>
      views.map fun w =>
        -- `{ c with ... }`, not a fresh literal: a promise must not erase the
        -- record of where earlier pair writes landed.
        { c with
          mem := c.mem.push ⟨a, v, w⟩
          ths := c.ths.set! i { th with promises := th.promises ++ [c.mem.size] } })
    ++
    -- **The pair promise, and it must be one step.**  Two separate promise
    -- steps would be wrong twice over: another thread could push between them,
    -- and more importantly there would be a reachable state in which one word
    -- of the pair is visible and the other is not.
    --
    -- `pairs` is extended *here*, not at fulfilment.  A promised message is
    -- already in `mem` and already readable by everybody, so the moment the
    -- pair becomes visible is the moment it must start forbidding torn reads.
    -- Registering it at fulfilment instead would leave a window in which
    -- `pairStraddles` knew nothing about it.
    ((pairPromiseCands k th c.mem).flatMap fun (a, v0, v1) =>
      views.map fun w =>
        { c with
          mem := (c.mem.push ⟨a, v0, w⟩).push ⟨a.next, v1, w⟩
          pairs := c.pairs ++ [c.mem.size]
          ths := c.ths.set! i
            { th with promises := th.promises ++ [c.mem.size, c.mem.size + 1] } })

/-! ### The wide access (FEAT_LSE2)

`WeakMem.lean`'s two rules, transposed to this machine.  The read side is
identical -- it was already written against `readBoundOf` and `pairStraddles`,
neither of which knows which machine it is in.

The write side is **append-only**, and that is a restriction worth stating
rather than hiding.  `stepStore` above may fulfil a promise instead of
appending; `stepStorePair` may not.  Two reasons, and the second is the real
one.  A wide store would have to discharge *two* promises at adjacent
timestamps simultaneously, which is a new rule; and nothing exercises it,
because no test in the suite promises a wide write.  Machinery with no test
behind it is the thing this project keeps finding to be wrong (§6.11, §6.14),
so it is not written.  If a wide store ever needs to be promised, item 1 of
`check-promises.sh` is what will say so: the state sets would stop matching
`WeakMem.lean`'s. -/

/-- A two-word plain store.  Append-only; see the section note. -/
def stepStorePair (mem : Memory) (pairs : List Ts) (th : Thread) (a : Address)
    (e0 e1 : Expr) (deps : List Reg) (rel : Bool) :
    Memory × List Ts × Thread :=
  let vs := th.vs
  let valOf : Expr → Val := fun e =>
    match e with | .const c => c | .reg r => (th.regs r).val
  -- `storeMview` takes one expression, and a pair publishes the join of both
  -- data views, so it is applied twice rather than generalised -- keeping the
  -- single-word rule the one definition that says what a store publishes.
  let mview := max (storeMview th e0 deps rel) (storeMview th e1 deps rel)
  let a0 := a
  let a1 := a.next
  let t0 := mem.size
  let t1 := mem.size + 1
  (( mem.push ⟨a0, valOf e0, mview⟩).push ⟨a1, valOf e1, mview⟩,
   pairs ++ [t0],
   { th with
     vs := { vs with
             coh := fun b => if b = a0 then t0 else if b = a1 then t1 else vs.coh b
             vWr := max vs.vWr t1, mine := (t1 - 1) :: t1 :: vs.mine
             fwd := (t1 - 1, pairFwdOf th.regs e0 e1 deps) :: (t1, pairFwdOf th.regs e0 e1 deps) :: vs.fwd } })

/-- A two-word plain load.  Identical to `WeakMem.stepLoadPair` except for
    going through `readBoundOf`, which is how every read bound is spelled in
    this file. -/
def stepLoadPair (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst0 dst1 : Reg) (a : Address) (deps : List Reg) (acq : Bool) :
    List Thread :=
  let a0 := a
  let a1 := a.next
  let vs := th.vs
  let d := depBound th.regs deps
  let c0 := (List.range mem.size).filter fun t =>
    readable mem a0 t (readBoundOf arch vs d a0)
  let c1 := (List.range mem.size).filter fun t =>
    readable mem a1 t (readBoundOf arch vs d a1)
  c0.flatMap fun t0 => c1.filterMap fun t1 =>
    if pairStraddles mem pairs a0 t0 t1 then none
    else
      let m0 := mem[t0]!
      let m1 := mem[t1]!
      some
        { th with
          regs := fun r =>
            if r = dst0 then ⟨m0.val, m0.view, t0⟩
            else if r = dst1 then ⟨m1.val, m1.view, t1⟩
            else th.regs r
          vs := { vs with
                  coh := fun b =>
                    if b = a0 then max (vs.coh a0) t0
                    else if b = a1 then max (vs.coh a1) t1
                    else vs.coh b
                  vRd := max vs.vRd (max (rdV vs pairs t0 m0.view) (rdV vs pairs t1 m1.view))
                  vPreBase :=
                    if acq then max vs.vPreBase (max (acqV vs pairs t0 m0.view) (acqV vs pairs t1 m1.view))
                    else vs.vPreBase } }

/-! ### Issue: strictly in program order

This is the whole reason the file exists.  Compare `WeakMem.stepThread`, which
consults `issuable` and may run any instruction whose predecessors all permit
it.  Here the thread runs `prog.head?` and nothing else. -/

def stepThread (k : Knobs) (arch : Arch) (c : Config) (i : Nat) : List Config :=
  match c.ths[i]? with
  | none => []
  | some th =>
    match th.prog with
    | [] => []
    | ins :: rest =>
      -- `{ c with ... }` rather than a fresh literal, so `pairs` -- which
      -- records where atomic pair writes landed and is consulted by every
      -- later pair read -- survives an intervening single-word step.
      let setTh (mem : Memory) (th' : Thread) : Config :=
        { c with mem := mem, ths := c.ths.set! i { th' with prog := rest } }
      match ins with
      | .load dst a deps acq =>
          (stepLoad arch c.mem c.pairs th dst a deps acq).map (setTh c.mem)
      | .store a e deps rel =>
          (stepStore k arch c.mem th a e deps rel).map fun (mem', th') =>
            setTh mem' th'
      | .fence f => [setTh c.mem (stepFence th f)]
      | .branch r =>
          let vs := th.vs
          -- The `rts` half of the asymmetry.  Joining the message *view* here
          -- leaves `vCtrl = 0` whenever the writer published nothing, which
          -- makes the store bound vacuous and wrongly allows `LB+ctrl`.
          let w := if k.ctrlRts then (th.regs r).rts else (th.regs r).view
          [setTh c.mem { th with vs := { vs with vCtrl := max vs.vCtrl w } }]
      | .isb =>
          let vs := th.vs
          [setTh c.mem { th with vs := { vs with vPreBase := max vs.vPreBase vs.vCtrl } }]
      | .rmw dst a kind newv deps acq rel =>
          (stepRmw k arch c.mem c.pairs th dst a kind newv deps acq rel).map
            fun (mem', th') =>
            setTh mem' th'
      | .rmwPair d0 d1 a cmp0 cmp1 new0 new1 deps acq rel =>
          -- One of the two rules that rewrite `pairs`, so one of the two cases
          -- that cannot go through `setTh` alone.
          (stepRmwPair arch c.mem c.pairs th d0 d1 a cmp0 cmp1 new0 new1
              deps acq rel).map fun (mem', pairs', th') =>
            { setTh mem' th' with pairs := pairs' }
      | .storePair a e0 e1 deps rel =>
          -- The other one, and the line that takes FEAT_LSE2.
          let (mem', pairs', th') :=
            stepStorePair c.mem c.pairs th a e0 e1 deps rel
          [{ setTh mem' th' with pairs := pairs' }]
      | .loadPair d0 d1 a deps acq =>
          (stepLoadPair arch c.mem c.pairs th d0 d1 a deps acq).map (setTh c.mem)

/-! ### 2.4 Certification -- the condition this model does not have

Promising Semantics only lets a thread promise a write it can then *keep*: after
every step, the stepping thread must have a run of its own, with every other
thread stopped, that discharges all its outstanding promises.  Nothing above
does that.  `promiseCands` is a *syntactic* over-approximation -- it offers
`(a, v)` only when a constant store of `v` to `a` literally appears later in
this thread's program -- which is strong enough to exclude out-of-thin-air (you
cannot promise a value your own code never writes) and far too weak to be
certification (syntactically present later is not the same as reachable).

The consequence is not cosmetic, and it is why this section exists.  Read as
language metatheory, **progress is false for the machine above**, and the
witness is already in this file: `fenced_writer_cannot_discharge` (§11.3) proves
that after a release fence the promising writer can *never* take its promised
timestamp.  That configuration has no run to a final state and no rule that
stops it existing -- it is a reachable stuck state, reached by a promise the
thread was never able to keep.

**Why it is decidable here and not in the literature.**  Certification is the
hard part of the Promising Semantics metatheory because real programs loop, so
"can this thread finish on its own" is reachability over an unbounded execution.
`Instr` has no loops and no jumps: `.branch` is a view-join, not a control
transfer, and `stepThread` consumes `ins :: rest` to `rest` unconditionally.  So
a thread-local run is at most `prog.length` instruction steps, and the promises
it may make along the way are capped by the constant stores remaining in that
same program.  `2 * prog.length + 1` is therefore not a fuel parameter in the
usual apologetic sense; it is a bound.

**Why thread-local is the right notion here, and not a restriction.**  In
general this is a restriction: certifying alone forbids promises another thread
could have helped you keep.  Not in this model.  Fulfilment needs the thread's
store view to sit *below* the promised message's view, and reading another
thread's write only ever *raises* views.  Other threads can only make fulfilment
harder, so a promise that fails thread-local certification could not have been
discharged with anyone's help either.  That is the same shape as §15's
`readable_antitone` / `depBound_mono`, which is some evidence it is provable and
not merely true.  §4.2 is the measurement rather than the proof.

**Why it should change nothing observable.**  An uncertifiable promise already
contributes no outcome: `Config.done` requires `promises.isEmpty`, so a branch
that cannot discharge is dropped at the *end* instead of at the start.
Certification moves the drop earlier.  It prunes; it does not re-weight.

All of that is an argument, so §4.2 measures it instead of believing it, and
measures the other three things that could have gone wrong: that it prunes
nothing (the check would be vacuous), that it costs more than it saves, and
that the stuck configurations survive it anyway. -/

/-- Can thread `i` discharge all of its promises running *alone* from `c`?

    `stepThread` and `promiseSteps` are the uncertified rules on purpose:
    certification is a thread-local property of the ordinary machine, not a
    recursive appeal to itself. -/
def dischargesAlone (k : Knobs) (arch : Arch) (fuel : Nat) (c : Config) (i : Nat) :
    Bool :=
  match c.ths[i]? with
  | none => true
  | some th =>
    if th.promises.isEmpty then true
    else
      match fuel with
      | 0 => false
      | fuel + 1 =>
        (stepThread k arch c i ++ promiseSteps k c i).any fun c' =>
          dischargesAlone k arch fuel c' i

/-- The bound argued for above: every instruction once, and at most one promise
    per constant store still ahead of it. -/
def certFuel (c : Config) (i : Nat) : Nat :=
  match c.ths[i]? with
  | none => 0
  | some th => 2 * th.prog.length + 1

/-- The certified step relation: every step thread `i` may take from `c` and
    still be able to keep its word.

    Deliberately a *separate* relation rather than a knob inside `finals`.
    `finals` is unfolded by §16's simulation proof, which pattern-matches on the
    step list; making that list depend on a `Bool` breaks the induction even
    when the `Bool` is `false`.  So the certification sub-relation is
    literally a sub-relation here too, and nothing above this line moves. -/
def stepsCert (k : Knobs) (arch : Arch) (c : Config) (i : Nat) : List Config :=
  (stepThread k arch c i ++ promiseSteps k c i).filter fun c' =>
    dischargesAlone k arch (certFuel c' i) c' i

/-- Steps that certification rejects, and the total offered, at one node.
    Used by §4.2 to show the check is not vacuous. -/
def prunedAt (k : Knobs) (arch : Arch) (c : Config) (i : Nat) : Nat × Nat :=
  let raw := stepThread k arch c i ++ promiseSteps k c i
  ((raw.filter fun c' => !dischargesAlone k arch (certFuel c' i) c' i).length,
   raw.length)

/-- A configuration is final only when every promise has been made good. -/
def Config.done (c : Config) : Bool :=
  c.ths.all fun th => th.prog.isEmpty && th.promises.isEmpty

def finals (k : Knobs) (arch : Arch) (fuel : Nat) (c : Config) : List Config :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if c.done then [c]
    else
      (List.range c.ths.size).flatMap fun i =>
        (stepThread k arch c i ++ promiseSteps k c i).flatMap (finals k arch fuel)

/-- `finals` over `stepsCert`.  Selected by `Knobs.certify`; see §4.2. -/
def finalsCert (k : Knobs) (arch : Arch) (fuel : Nat) (c : Config) : List Config :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if c.done then [c]
    else
      (List.range c.ths.size).flatMap fun i =>
        (stepsCert k arch c i).flatMap (finalsCert k arch fuel)

/-! ## 3. Harness

The same `Litmus` values, the same herd7-derived expectations, the same
`Result` rendering.  Nothing about the oracle changes; only the machine does. -/

def regNat (th : Thread) (r : Reg) : Nat :=
  match (th.regs r).val with
  | .num n => n
  | _ => 999

def start (L : Litmus) : Config :=
  { mem := L.initMem, ths := (L.threads.map Thread.mk').toArray }

/-- `WeakMem.Obs.read`, against *this* file's `Config`.  The two machines have
    separate `Thread` and `Config` types, so the register case has to be
    rewritten; the memory case does not, because both files agree that memory
    is an append-only `Array Msg` and `memNat` only reads `loc` and `val`. -/
def obsNat (c : Config) : Obs → Nat
  | .reg i r => regNat c.ths[i]! r
  | .mem a   => memNat c.mem a

def outcomesOf (k : Knobs) (L : Litmus) : List (List Nat) :=
  let fs := finals k L.arch 64 (start L)
  let raw := fs.map fun c => L.obs.map (obsNat c)
  raw.foldl (fun acc o => if acc.contains o then acc else acc ++ [o]) []

/-- `outcomesOf` over the certified relation of §2.4.

    Separate for the same reason `finalsCert` is: §16's simulation unfolds
    `outcomesOf`, and an `if` on a `Bool` defeats that even when the `Bool` is
    `false`.  `Knobs.certify` therefore selects the *function* -- at the two
    call sites in §4.2 -- rather than a branch inside one. -/
def outcomesCert (k : Knobs) (L : Litmus) : List (List Nat) :=
  let fs := finalsCert k L.arch 64 (start L)
  let raw := fs.map fun c => L.obs.map (obsNat c)
  raw.foldl (fun acc o => if acc.contains o then acc else acc ++ [o]) []

def archStr : Arch → String
  | .arm => "arm"
  | .tso => "tso"

/-- One full pass of the suite under `k`.  Exploring the state space is by far
    the expensive thing here, so every comparison below is phrased against a
    pass that was computed once rather than recomputing the baseline per row. -/
def pass (k : Knobs) : List Result :=
  suite.map fun L =>
    let os := outcomesOf k L
    { name := L.name, arch := L.arch, observed := os
      modelAllows := os.contains L.target, archAllows := L.archAllows
      states := L.states, xfail := L.xfail }

def sameSet (a b : List (List Nat)) : Bool :=
  a.all (fun o => b.contains o) && b.all (fun o => a.contains o)

def say (b : Bool) : String := if b then "allowed" else "forbidden"

/-- Stronger than agreeing on the verdict: the promise machine must reach the
    same *set* of final states as `WeakMem.lean`.  If promises are a faithful
    replacement for out-of-order issue, nothing is gained or lost. -/
def suiteReport (base : List Result) : String × Nat :=
  let lines := (suite.zip base).map fun (L, r) =>
    let same := sameSet r.observed L.outcomes
    let tag := if r.agrees && same then "ok   " else "FAIL "
    let note := if same then "" else "   (state set differs from WeakMem)"
    (r.agrees && same, s!"{tag} | [{archStr L.arch}] {L.name}{note}\n" ++
      s!"        model: {say r.modelAllows}   arch: {say r.archAllows}" ++
      s!"   states: {r.observed.length}")
  let bad := lines.filter fun l => !l.1
  (String.intercalate "\n" (lines.map Prod.snd), bad.length)

/-! ## 4. Ablations and generality checks

Two tables, checked against opposite expectations.

**Ablations** turn off a rule that *forbids*.  Each must break a test: a rule
you cannot break is a rule you have not justified, and one that breaks nothing
should be deleted rather than kept "for safety" -- the same discipline that
removed the redundant TSO store-publication rule in stage 1.

**Generality checks** turn off a *permission*.  Each must change nothing,
because each is either a generalisation no current test needs or a pruning
argued to be equivalence-preserving.  A change here is not a failure of the
model, it is a refutation of the argument in §2, which is more interesting. -/

def failingUnder (k : Knobs) : List String :=
  ((pass k).zip suite).filterMap fun (r, L) =>
    if r.agrees then none else some s!"{archStr L.arch}/{L.name}"

/-- Tests whose reachable state set changes under `k`, together with how many
    tests were actually checked.  Finer than `failingUnder`: a permission could
    add a state without flipping a verdict.

    `keep` exists because one generality row is far more expensive than the rest
    (see `generality`), and a check whose coverage is silently partial is worse
    than one that says so. -/
def differingOn (base : List Result) (k : Knobs) (keep : Litmus → Bool) :
    List String × Nat :=
  let rows := (base.zip suite).filter fun (_, L) => keep L
  let diffs := rows.filterMap fun (b, L) =>
    if sameSet (outcomesOf k L) b.observed then none
    else some s!"{archStr L.arch}/{L.name}"
  (diffs, rows.length)

def ablation : String :=
  let rows : List (String × Knobs) :=
    [ ("promise steps at all",            { promises := false })
    , ("branch joins rts (not view)",     { ctrlRts := false })
    , ("store dep bound uses rts",        { storeDepRts := false })
    , ("TSO orders store→store, ld→st",   { tsoStoreOrder := false })
    , ("promised views (view 0 only)",    { promiseViews := false })
    , ("own-write forwarding view",       { fwdView := false }) ]
  let body := rows.map fun (nm, k) =>
    let f := failingUnder k
    let names := if f.isEmpty then "nothing -- DELETE THIS RULE"
                 else String.intercalate ", " f
    s!"  remove {nm}\n    -> {f.length} failing: {names}"
  String.intercalate "\n" body

/-- Why the second row is not run on the whole suite.

    Turning head-store pruning off costs ~320s against ~1s for a full pass: a
    promise/fulfil pair doubles the depth at which every store can act, and each
    promise branches over every existing timestamp, so the cost is worst exactly
    where the state space is already widest.  The four-thread IRIW variants
    account for essentially all of it.

    Dropping them loses very little, because they are the tests where the
    pruning argument is *most* obviously true rather than least: each IRIW
    writer's whole program is a single store, so there is provably nothing that
    could run between promising it and fulfilling it.  The remaining tests
    include every thread that has instructions after its first store, which is
    the only situation in which the pruning could hide a behaviour.

    The cut is on thread *count*, and the bound is 3 rather than 2 on purpose.
    It read `≤ 2` until the three `WRC+*` tests arrived, at which point it
    started silently excluding them -- and WRC's middle thread reads and then
    writes, so it is precisely a thread with instructions after its first store.
    The sentence above would have become false without anything in this file
    changing.  Three threads are cheap; four are not.

    The row prints its own coverage so this stays visible rather than becoming
    a footnote nobody reads. -/
def generality (base : List Result) : String :=
  let rows : List (String × Knobs × (Litmus → Bool) × String) :=
    [ ("head-store pruning (promise head too)", { headPromise := true },
       fun L => L.threads.length ≤ 3, " (4-thread tests excluded: cost)") ]
  let body := rows.map fun (nm, k, keep, why) =>
    let (d, n) := differingOn base k keep
    let verdict :=
      if d.isEmpty then s!"no state set changes in {n}/{suite.length} -- argument holds"
      else s!"CHANGES {d.length}: " ++ String.intercalate ", " d ++
           " -- the §2 argument for this is WRONG"
    s!"  toggle {nm}{why}\n    -> {verdict}"
  String.intercalate "\n" body

/-- The promise candidate set is exact only for constant stores.  Say so out
    loud rather than leaving it as a footnote. -/
def regStoreReport : String :=
  let bad := suite.filter hasRegStore
  if bad.isEmpty then
    "  no .reg stores in the suite -- promise candidates are exact for these tests"
  else
    "  WARNING: .reg stores in " ++
    String.intercalate ", " (bad.map Litmus.name) ++
    " -- promise candidates are incomplete there"

/-! ## 4.1 TSO ⊆ ARM

The reason both architectures share one rule set is so that a proof done
against `arm` is also a proof about x86.  That needs every outcome the `tso`
rules admit to be one the `arm` rules admit too, and `WeakMem.lean` §8 checks
exactly that -- against the *stage-1* machine.  Everything from §7 onwards is
proved against this one, so the check has to exist here as well, or the
transfer argument is evidence about a machine nobody uses any more.

A real theorem is a later stage, and the route there is not the obvious
one: eight of this model's nine architecture-sensitive points are a `max` that
enlarges a bound under `tso`, which is a restriction and behaves, but the ninth
(`lockFence`) gives a TSO RMW an extra `.sy` fence that the ARM one does not
perform.  That is an additional step rather than a restricted one, so the two
runs cannot be matched state for state.  §15 now carries the relation that
replaces state equality, and the lemmas it rests on; until the simulation
itself is proved, this table is the testable shadow.

Two deliberate differences from the stage-1 version.

**It runs on all 89<!--@suite--> shapes, not the 20<!--@herd-x86--> `tso` ones.**  The extra 42 are ARM
programs run under TSO rules, which is not a program anyone would write.  But a
simulation theorem quantifies over every program in `Instr`, not over the ones
we happened to write for x86 -- so those 40 are precisely the cases it would
have to cover, and the 12 are already checked next door.  If a counterexample
exists, this is where it is.

**It reports slack as well as escapes.**  `escapes` (reachable under `tso`, not
under `arm`) must be empty.  `slack` (the other direction) must *not* be empty
everywhere, or the two rule sets agree on everything tested and the containment
check is vacuous -- the same discipline every other table here follows.

Both guards are live rather than decorative.  Computing the table with the two
architectures swapped -- asking whether `arm` stays inside `tso` -- reports all
89<!--@suite--> shapes with 32<!--@slack--> escaping and none where `tso` is
strictly weaker, which trips the escape assertion and the vacuity assertion at
once.  Those 32<!--@slack--> are the shapes where ARM is genuinely the weaker
model, and they are the same ones counted in the `slack` column here.  (These
numbers are measured, not estimated: the swapped computation is a five-line
driver over the same `suite`.  They are also *marked*, which they were not
until the `diy7` increment -- the sentence used to quote the swapped summary
line inside backticks, where neither item 28 nor item 29 could see it, and it
went stale the moment the suite grew.)

§15 states the refinement relation this table is the shadow of, and proves the
monotonicity lemmas it needs; the simulation itself is still open. -/

structure Contain where
  name : String
  arch : Arch
  /-- Outcomes reachable under `tso` but not under `arm`.  Must be empty. -/
  escapes : List (List Nat)
  /-- Outcomes reachable under `arm` but not under `tso`.  May be empty for any
      one shape; must not be empty for all of them. -/
  slack : List (List Nat)

def containOf (L : Litmus) : Contain :=
  let tso := outcomesOf {} { L with arch := .tso }
  let arm := outcomesOf {} { L with arch := .arm }
  { name := L.name, arch := L.arch
    escapes := tso.filter fun o => !arm.contains o
    slack := arm.filter fun o => !tso.contains o }

/-- Returns the rendered table, the number of escaping shapes (must be 0) and
    the number of discriminating shapes (must not be 0). -/
def containment : String × Nat × Nat :=
  let cs := suite.map containOf
  let bad := cs.filter fun c => !c.escapes.isEmpty
  let disc := cs.filter fun c => !c.slack.isEmpty
  let lines := cs.map fun c =>
    let tag := if c.escapes.isEmpty then "ok   " else "FAIL "
    let note :=
      if !c.escapes.isEmpty then s!"   escapes: {repr c.escapes}"
      else if c.slack.isEmpty then "   (arm = tso)"
      else s!"   (arm admits {c.slack.length} more)"
    s!"  {tag}| [{archStr c.arch}] {c.name}{note}"
  (String.intercalate "\n" lines ++
    s!"\n  {cs.length} shapes, {bad.length} escaping, " ++
    s!"{disc.length} where arm is strictly weaker",
   bad.length, disc.length)

def containmentReport : String :=
  let (body, bad, disc) := containment
  body ++
    (if bad == 0 then "" else "\n  FAIL: tso escapes arm") ++
    (if disc == 0 then "\n  FAIL: arm never admits more -- this check is vacuous"
     else "")

/-! ## 4.2 Certification, and the progress counterexample it removes

§2.4 adds the condition Promising Semantics has and this model did not: a step
is only allowed if it leaves the stepping thread able to discharge its own
promises running alone.  Four claims are made there, and each could have been
wrong in a different direction, so each is measured here rather than argued.

1.  **It changes nothing observable.**  Every shape must reach the same set of
    states under `finalsCert` as under `finals`.  This is the claim that lets
    certification be added without re-validating anything against herd7: the
    89<!--@suite--> shapes are the same shapes, and their verdicts are the
    same verdicts.

2.  **It is not vacuous.**  If certification rejected no step anywhere, claim 1
    would be true for the least interesting reason and this whole section would
    be decoration.  The same discipline as the ablation table.

3.  **The thing it fixes is real.**  A *stuck* configuration is one with no step
    available that is not `done`: every thread's program is exhausted and a
    promise is still outstanding.  That is a counterexample to progress, stated
    operationally, and `fenced_writer_cannot_discharge` (§11.3) is the same
    phenomenon proved for one program.  If the suite reached none of them, the
    problem certification solves would not be a problem the suite can see, and
    claim 4 would be vacuous in turn.

4.  **None of them survives it.**  Zero stuck configurations under `stepsCert`.

Claim 4 is the interesting one, and it is stronger than the certification
condition literally guarantees.  Certification is re-checked for the *stepping*
thread only; nothing re-checks thread `j` after thread `i` moves.  In general
that is unsound -- `i`'s writes grow memory, and coherence conditions on `j`'s
fulfilment are evaluated against memory as it stands -- so a thread certified at
promise time could in principle be stranded by somebody else later.  The
measurement says it does not happen here, on any shape, which is evidence for
the monotonicity argument in §2.4 and the reason to expect the certification
bridge theorem to go through with thread-local certification rather than a
global one.

A note on cost, because the expectation was the opposite.  Certification is a
nested search at every node, so it looks like it must be slower; it is not,
because the subtree it prunes is larger than the search that finds it.  The
report prints both passes. -/

/-- Steps rejected by certification, and steps offered, summed over the
    certified search tree.  Counted with path multiplicity -- the question is
    whether it is nonzero, not how many distinct configurations there are. -/
def certPruned (k : Knobs) (arch : Arch) (fuel : Nat) (c : Config) : Nat × Nat :=
  match fuel with
  | 0 => (0, 0)
  | fuel + 1 =>
    if c.done then (0, 0)
    else
      (List.range c.ths.size).foldl (init := ((0, 0) : Nat × Nat)) fun acc i =>
        let (p, t) := prunedAt k arch c i
        let sub := (stepsCert k arch c i).foldl (init := ((0, 0) : Nat × Nat))
          fun a c' =>
            let r := certPruned k arch fuel c'
            (a.1 + r.1, a.2 + r.2)
        (acc.1 + p + sub.1, acc.2 + t + sub.2)

/-- Reachable configurations that are stuck: no step available, and not `done`.
    With `cert` on the search uses `stepsCert`, so this is the count that must
    come out zero. -/
def stuckCount (cert : Bool) (k : Knobs) (arch : Arch) (fuel : Nat) (c : Config) :
    Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    if c.done then 0
    else
      let steps := (List.range c.ths.size).flatMap fun i =>
        if cert then stepsCert k arch c i
        else stepThread k arch c i ++ promiseSteps k c i
      if steps.isEmpty then 1
      else steps.foldl (init := 0) fun a c' => a + stuckCount cert k arch fuel c'

structure CertRow where
  name : String
  arch : Arch
  /-- Same reachable state set as the uncertified machine.  Must be true. -/
  same : Bool
  pruned : Nat
  offered : Nat
  /-- Stuck configurations reachable without certification, and with it. -/
  stuck : Nat
  stuckCert : Nat

def certRow (base : Result) (L : Litmus) : CertRow :=
  let (p, t) := certPruned {} L.arch 64 (start L)
  { name := L.name, arch := L.arch
    same := sameSet base.observed (outcomesCert {} L)
    pruned := p, offered := t
    stuck := stuckCount false {} L.arch 64 (start L)
    stuckCert := stuckCount true {} L.arch 64 (start L) }

/-- Only the shapes certification touches are printed: on a shape it prunes
    nothing it also unsticks nothing, and 29 rows of "0, 0" would bury the
    43<!--@certprune--> that say something. -/
def certReport (base : List Result) : String :=
  let rows := (base.zip suite).map fun (b, L) => certRow b L
  let changed := rows.filter fun r => !r.same
  let pruning := rows.filter fun r => r.pruned > 0
  let stuckly := rows.filter fun r => r.stuck > 0
  let survive := rows.filter fun r => r.stuckCert > 0
  let totP := rows.foldl (fun a r => a + r.pruned) 0
  let totT := rows.foldl (fun a r => a + r.offered) 0
  let lines := pruning.map fun r =>
    s!"  ok   | [{archStr r.arch}] {r.name}: pruned {r.pruned}/{r.offered}, " ++
    s!"stuck {r.stuck} -> {r.stuckCert}"
  String.intercalate "\n" lines ++
  s!"\n  {rows.length} shapes, {changed.length} with a different state set" ++
  s!"\n  prunes on {pruning.length} shapes: {totP}/{totT} offered steps rejected" ++
  s!"\n  stuck configurations: on {stuckly.length} shapes uncertified, " ++
  s!"{survive.length} under certification" ++
  (if changed.isEmpty then "" else
    "\n  FAIL: certification changed a state set -- the §2.4 argument is WRONG: " ++
    String.intercalate ", " (changed.map fun r => s!"{archStr r.arch}/{r.name}")) ++
  (if totP == 0 then
    "\n  FAIL: certification rejects nothing -- this check is vacuous" else "") ++
  (if stuckly.isEmpty then
    "\n  FAIL: no stuck configuration anywhere -- progress is not at risk on " ++
    "these shapes, so claim 4 is vacuous" else "") ++
  (if survive.isEmpty then "" else
    "\n  FAIL: stuck under certification -- thread-local certification is not " ++
    "enough here: " ++
    String.intercalate ", " (survive.map fun r => s!"{archStr r.arch}/{r.name}"))


/-! ## 5. The payoff: `do`-notation over the machine, and `mvcgen` on memory

This is the comparison with the staged front-end that was the other candidate
for stage 2, and the reason to prefer promises.  (That prototype was built,
measured, and then deleted.)

There, the front-end monad's state was the code generator, so a Hoare triple
could only talk about emitted instructions.  Here the state *is* the machine, so
a triple talks about memory and views.  The reason that is now possible is
exactly the change §2 made: instructions run in program order, so a `do`-block
drives every rule.  Nothing is hidden from a scheduler, because there is no
scheduler.

Three things to notice in the definitions below.

* **Bind carries values.**  `mload` returns a `TVal`, not a register name.  So
  `let v ← mload a` gives you the loaded value, and `if v.val = ...` is an
  ordinary Lean `if` -- the first of the three things staging could not write.
* **Dependencies are values, not names.**  `deps : List TVal` means passing a
  value *is* keeping the dependency; there is no separate register list to get
  wrong.  This is D3, and it fixes the staged design's third complaint: an
  omitted dependency now changes what you can prove rather than silently
  changing the test.
* **Promising is an ordinary operation.**  `mpromise` is a statement you write
  in the `do`-block.  Compare `WeakMem.issuable`, which no `do`-block can reach.

Nondeterminism is the demonic oracle of D4: a list of choices in the state,
consumed left to right, with `stuck` set if the adversary asks for a successor
that does not exist.  Specs are conditional on `¬ stuck`, which is the right
reading -- an oracle that picks a nonexistent successor has not exhibited a
behaviour of the program. -/

/-- An address Remote holds, together with the dependency view it was obtained
    with.  The view is what makes an address dependency mean something: a load
    through this address is ordered after whatever the load that produced it
    inherited.  Roots carry view `0`; they were not obtained by reading. -/
structure RAddr where
  addr : Address
  view : Ts := 0
  deriving Repr, Inhabited

structure Machine where
  arch : Arch := .arm
  mem : Memory
  vs : VState := VState.init
  promises : List Ts := []
  /-- Demonic resolution of every nondeterministic choice. -/
  oracle : List Nat
  stuck : Bool := false
  /-- Remote's views (D2).  Separate from `vs`: Remote reorders independently. -/
  rvs : VState := VState.init
  /-- Every address Remote holds.  **The only way in is a load** -- this is
      where the no-forging assumption lives, and it is operational rather than
      axiomatic.  See §7. -/
  rknow : List RAddr := []
  /-- The values Remote's loads returned, in order.  The privacy theorem is a
      statement about this list. -/
  rreads : List Val := []
  /-- Addresses that are global by fiat: the program did not publish them, they
      were always there.  Fixed for the life of the machine. -/
  roots : List Address := []
  /-- Allocations the environment has given up (§9).
      **This is an assumption, not a mechanism.**  Nothing in the machine
      enforces it and no hardware feature corresponds to it; it is a *rely*
      condition, discharged by the other thread's proof exactly as ownership is
      discharged in separation logic.
      Note what it is not: Remote does not *forget* a disowned allocation.
      `rknow` stays monotone, so D2's over-approximation of reachability is
      untouched and §7's theorems keep their proofs.  Remote still knows the
      address and may still read it -- it may not *write* it.  Forbidding is
      sound where forgetting would not be, because Remote stands for every
      other thread at once and "they all forgot" is not something one agent can
      say. -/
  rdisowned : List AllocLabel := []
  /-- The size of each allocation, indexed by label (§10).

      `sizes.length` is therefore also the next unused label, which is why
      there is no separate counter: "fresh" and "unallocated" are the same
      condition, and keeping them in one field makes that true by
      construction rather than by an invariant.

      An address is *allocated* when its label has an entry and its offset is
      inside it.  Nothing else in the machine consults this: it exists so that
      a load from an allocated-but-unwritten cell can return `undef` instead
      of getting stuck. -/
  sizes : List Nat := []
  /-- Timestamps at which a pair RMW wrote its first word, the second being at
      `p + 1`.  `Config.pairs` at the proof layer; see §11.4.

      It is a field rather than something derived from `mem` because the
      distinction it records is not visible in the messages: two *ordinary*
      adjacent stores may be torn across, and an atomic pair may not. -/
  pairs : List Ts := []
  deriving Inhabited


abbrev M := StateM Machine

def tvView (ds : List TVal) : Ts := ds.foldl (fun acc d => max acc d.view) 0
def tvRts (ds : List TVal) : Ts := ds.foldl (fun acc d => max acc d.rts) 0

/-- `depBound` for the `M` front end, whose dependencies are the `TVal`s
    themselves rather than register names. -/
def tvBound (ds : List TVal) : Ts := max (tvView ds) (tvRts ds)

/-! ### The demonic oracle (D4)

Nondeterminism is resolved by a list of choices in the state, consumed left to
right.  Two decisions here are what keep the verification conditions small
enough to read, and both are also the honest reading of an adversary:

* **The oracle is total.**  It picks *among the successors that exist* rather
  than naming one that might not.  `pick` walks the candidate list and falls
  back to its head, so a garbage oracle value yields a real successor rather
  than a stuck state.  An adversary that names a nonexistent successor has not
  exhibited a behaviour, so nothing is lost.
* **It does not branch on the shape of the oracle.**  `headD`/`tail` instead of
  a `match`, which halves the case split at every operation.

The one genuine stuck case survives: a load of a location with no readable
message at all.  That is a real possibility, not an artifact, so it stays. -/

/-- Generic in the element type because Remote also has to choose an *address*
    (§7).  The point of a `pick`/`pick_mem` pair rather than an index plus a
    default is that the choice comes with a membership proof, so no lemma ever
    has to rule out an out-of-range index. -/
def pick {α : Type} (i : Nat) (c : α) (cs : List α) : α :=
  match i, cs with
  | _, [] => c
  | 0, _ => c
  | i + 1, d :: ds => pick i d ds

@[simp] theorem pick_nil {α : Type} (i : Nat) (c : α) : pick i c [] = c := by
  cases i <;> rfl

theorem pick_mem {α : Type} (i : Nat) (c : α) (cs : List α) : pick i c cs ∈ c :: cs := by
  induction i generalizing c cs with
  | zero => cases cs <;> simp [pick]
  | succ i ih =>
    cases cs with
    | nil => simp [pick]
    | cons d ds =>
        show pick i d ds ∈ c :: d :: ds
        exact List.mem_cons_of_mem c (ih d ds)

/-- Resolve one choice among `c :: cs`. -/
def demonic {α : Type} (c : α) (cs : List α) : M α :=
  modifyGet fun s =>
    (pick (s.oracle.headD 0) c cs, { s with oracle := s.oracle.tail })

/-- The ordering bound a load must respect, named rather than inlined so that
    `mload_spec` can state what the load was allowed to see without anyone
    having to unfold `mload`.  Same rule as `stepLoad` in §2. -/
def loadBound (s : Machine) (a : Address) (deps : List TVal) : Ts :=
  let vs := s.vs
  let ordered := if s.arch = .tso then vs.vRd else 0
  max (max (max vs.vPreBase (tvBound deps)) (vs.coh a)) ordered

/-- **The acquire barrier is always part of the bound.**  One `max` chain, but
    worth a name: it is the only route by which an acquiring RMW's ordering
    reaches a *later, dependency-free* load, and §17's reader is exactly that.

    Note the direction.  `loadBound` is a floor, not a ceiling -- `hiddenFrom`
    hides a timestamp behind any later write at or below the bound -- so a
    *larger* bound sees *less*, and raising `vPreBase` is what forces a reader
    onto the writer's message rather than an older one. -/
theorem vPreBase_le_loadBound (s : Machine) (a : Address) (deps : List TVal) :
    s.vs.vPreBase ≤ loadBound s a deps := by
  unfold loadBound
  exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (Nat.le_max_left _ _)

/-- Is this cell inside a live allocation?

    Used by the load and the store below, and the reason it exists is D1.  A
    cell that has been allocated and not yet written holds `undef`, which is a
    *value*; a cell outside any allocation is not a cell, and touching it is
    undefined behaviour.  Conflating the two is what forces a model to choose
    between "reading uninitialised memory is UB" and "you can never tell", and
    D1 says it is neither.

    The asymmetry between the two callers is worth noting.  The load consults
    `allocated` only on the *empty* branch, because finding a readable message
    at `a` is already proof that `a` is a cell someone wrote.  The store has no
    such branch -- appending is always available -- so it checks
    unconditionally. -/
def allocated (s : Machine) (a : Address) : Bool :=
  match s.sizes[a.label]? with
  | some n => a.offset < n
  | none => false

/-! ### Why the `undef` result carries nothing

The load below returns `TVal.mk0 Val.undef` when no timestamp is readable: value
`undef`, view 0, timestamp 0.  Giving a *read* a zero view is the kind of thing
that should be argued rather than assumed -- it is the reader-side analogue of
publishing a store with no ordering, and if it were wrong it would be wrong
silently, by letting a later dependent access run earlier than it should.

The argument is that an empty candidate list does not mean "nothing readable
*under this bound*", it means **nothing was ever written to `a` at all** -- and a
read of a cell no write exists for has nothing to be ordered against.

That is not obvious from the definition, because `readable` is stated in terms
of a bound and one might expect a large enough `coh` to hide everything.  It
cannot: `hiddenFrom` only hides `t` behind a *later* write to the same location,
so the newest write to `a` is never hidden by anything, and is therefore always
readable.  The lemmas below make that precise, and `unwritten_of_no_readable` is
the form callers want -- note it quantifies over `bound`, so the conclusion is
independent of the architecture, the dependency set and the coherence state.

Every timestamp binder here is `Nat` rather than `Ts`, deliberately.  `omega`
will not look at a hypothesis whose atoms are declared at type `Ts`, even though
`abbrev Ts := Nat` is reducible, and it fails with "no usable constraints found"
rather than anything that points at the cause. -/

/-- A written cell that is not readable is hidden, and being hidden produces a
    strictly later written cell within the bound.  One step of the search. -/
theorem hidden_of_written_not_readable (mem : Memory) (a : Address) (t bound : Nat)
    (ht : (mem[t]?.elim false fun m => decide (m.loc = a)) = true)
    (hr : ¬ readable mem a t bound = true) :
    ∃ t', t < t' ∧ t' ≤ bound ∧
      (mem[t']?.elim false fun m => decide (m.loc = a)) = true := by
  have hh : hiddenFrom mem a t bound = true := by
    simp only [readable, ht, Bool.true_and, Bool.not_eq_true'] at hr
    simpa using hr
  rw [hiddenFrom, List.any_eq_true] at hh
  obtain ⟨t', hmem, hcond⟩ := hh
  rw [List.mem_range] at hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨hlt, hw⟩ := hcond
  refine ⟨t', hlt, ?_, hw⟩
  omega

/-- Iterate the step.  Each hop strictly increases the timestamp and stays below
    `bound`, so `bound - t` is fuel.  Written with explicit fuel rather than
    well-founded recursion: `decreasing_by` could not see the two hypotheses that
    make the measure shrink. -/
theorem readable_of_written_fuel (mem : Memory) (a : Address) (bound : Nat) :
    ∀ (fuel t : Nat), bound - t ≤ fuel →
      (mem[t]?.elim false fun m => decide (m.loc = a)) = true →
      ∃ t', readable mem a t' bound = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro t hf ht
      by_cases hr : readable mem a t bound = true
      · exact ⟨t, hr⟩
      · -- Out of fuel means `bound ≤ t`, so there is no room for a later write.
        exfalso
        obtain ⟨t', hlt, hle, _⟩ := hidden_of_written_not_readable mem a t bound ht hr
        omega
  | succ fuel ih =>
      intro t hf ht
      by_cases hr : readable mem a t bound = true
      · exact ⟨t, hr⟩
      · obtain ⟨t', hlt, hle, hw⟩ := hidden_of_written_not_readable mem a t bound ht hr
        refine ih t' ?_ hw
        omega

/-- If `a` was ever written, *something* at `a` is readable -- at every bound. -/
theorem readable_of_written (mem : Memory) (a : Address) (bound t : Nat)
    (ht : (mem[t]?.elim false fun m => decide (m.loc = a)) = true) :
    ∃ t', readable mem a t' bound = true :=
  readable_of_written_fuel mem a bound (bound - t) t (Nat.le_refl _) ht

/-- The contrapositive, and the form the load rule needs: an empty candidate
    list means the cell is unwritten, full stop.  This is what licenses
    `TVal.mk0` -- there is no message to carry a view and no timestamp to
    order against, so returning zeroes loses nothing. -/
theorem unwritten_of_no_readable (mem : Memory) (a : Address) (bound : Nat)
    (h : ∀ t, readable mem a t bound = false) (t : Nat) :
    (mem[t]?.elim false fun m => decide (m.loc = a)) = false := by
  cases hw : (mem[t]?.elim false fun m => decide (m.loc = a)) with
  | false => rfl
  | true =>
      obtain ⟨t', ht'⟩ := readable_of_written mem a bound t hw
      rw [h t'] at ht'
      exact absurd ht' (by simp)


def mload (a : Address) (deps : List TVal := []) (acq : Bool := false) : M TVal := do
  let s ← get
  let vs := s.vs
  let bound := loadBound s a deps
  match (List.range s.mem.size).filter fun t => readable s.mem a t bound with
  | [] =>
      -- Nothing readable at `a`.  Inside an allocation that means the cell has
      -- not been written yet, and the answer is `undef` -- no message, no
      -- timestamp, nothing for coherence to order against.  Outside one it is
      -- genuinely stuck, and not an oracle artifact.
      modifyGet fun s =>
        (TVal.mk0 Val.undef, { s with stuck := s.stuck || !allocated s a })
  | c :: cs =>
      let t ← demonic c cs
      modifyGet fun s =>
        let m := s.mem[t]?.getD ⟨a, Val.undef, 0⟩
        (⟨m.val, m.view, t⟩,
         { s with vs :=
             { vs with
               coh := fun b => if b = a then max (vs.coh a) t else vs.coh b
               vRd := max vs.vRd (rdV vs s.pairs t m.view)
               vPreBase := if acq then max vs.vPreBase (acqV vs s.pairs t m.view) else vs.vPreBase } })

/-- What a store publishes to readers.  Same rule as `storeMview` in §2. -/
def mstoreView (s : Machine) (deps : List TVal) (rel : Bool) : Ts :=
  if rel then max (max s.vs.vRelSt (max s.vs.vRd s.vs.vWr)) (tvView deps)
  else max s.vs.vRelSt (tvView deps)

/-- The ordering bound a store must respect.  Same rule as `storeOb` in §2:
    absent on ARM are `vRd`/`vWr`, because ARM reorders load→store and
    store→store; TSO adds them back. -/
def mstoreOb (s : Machine) (a : Address) (deps : List TVal) : Ts :=
  let ob0 := max (max s.vs.vPreBase (tvRts deps)) (max s.vs.vCtrl (s.vs.coh a))
  if s.arch = .tso then max ob0 (max s.vs.vRd s.vs.vWr) else ob0

/-- The promises this store could fulfill instead of appending: same location,
    same value, a view it is allowed to publish, and a timestamp its ordering
    bound permits.

    Named rather than inlined because `mstore_spec` has to case on the oracle's
    choice, and a half-page filter term in a `have` is unreadable. -/
def fulfillable (s : Machine) (a : Address) (v : Val) (deps : List TVal)
    (rel : Bool) : List Ts :=
  s.promises.filter fun t =>
    (s.mem[t]?.elim false fun m =>
      m.loc == a && m.val == v && mstoreView s deps rel ≤ m.view) &&
    decide (mstoreOb s a deps ≤ t)

def mstore (a : Address) (v : Val) (deps : List TVal := []) (rel : Bool := false) :
    M Unit := do
  let s ← get
  let vs := s.vs
  let mview := mstoreView s deps rel
  -- Appending is always available, so a store never gets stuck: the choice is
  -- only ever *which* promise to fulfill instead.
  let t ← demonic s.mem.size (fulfillable s a v deps rel)
  modify fun s =>
    { s with
      -- Mirrors `mload`.  A cell outside every allocation is not a cell, and
      -- writing to one is undefined behaviour just as reading one is.  Note
      -- this is a *capacity* check, not a length check: writing into
      -- allocated-but-unwritten space is exactly what §6.6's growable array
      -- needs to do, and stays legal.
      stuck := s.stuck || !allocated s a
      mem := if t = s.mem.size then s.mem.push ⟨a, v, mview⟩ else s.mem
      promises := if t = s.mem.size then s.promises else s.promises.erase t
      vs := { vs with
              coh := fun b => if b = a then t else vs.coh b
              vWr := max vs.vWr t, mine := t :: vs.mine,
              fwd := (t, tvBound deps) :: vs.fwd } }

/-- An early write.  In `WeakMem.lean` the corresponding behaviour is produced
    by the harness reordering instructions, which a program logic cannot see.
    Here it is a line of the program.

    `view` is what a reader of this message will inherit, and must be below the
    timestamp the promise takes -- you cannot publish something that has not
    happened.  That is checked, not assumed: promising with too large a view is
    a no-op. -/
def mpromise (a : Address) (v : Val) (view : Ts := 0) : M Unit :=
  modify fun s =>
    if view < s.mem.size then
      { s with mem := s.mem.push ⟨a, v, view⟩
               promises := s.promises ++ [s.mem.size] }
    else s

/-! ### Rule 3, in the front end

`mpromise` is rules 1 and 2 of §2.3, and `fulfillable` is their side
conditions.  Rule 3 -- **discharge** -- has no operation to attach itself to,
because it is not a step: it is a condition on the *run*, and on the
multi-thread machine of §2 it lives in `Config.done`.

For a long time it was simply absent here, and the note in §11.3 called that
harmless.  It is not, and the demo at the end of §11.3 is the reason.  A
promise that cannot be fulfilled still **leaves its message in memory**, where
a reader will read it exactly as if the write had happened.  So the rendered
outcome of a forbidden run is indistinguishable from an allowed one, and a
demo that does not check discharge will report that a fence does nothing when
what the fence actually did was make the promise impossible to keep.

Two consequences worth stating, because they are what the check buys:

* Every `#eval` in this file that does not use `mpromise` is unaffected --
  `promises` is `[]` throughout, so `exhibits` is `!stuck`, which is what the
  demos already reported.
* A demo that *does* promise is now obliged to say whether the run counts.
  That is the difference between exhibiting a behaviour and exhibiting a
  memory state. -/

/-- Rule 3 of §2.3: a promise that was never made good means the run did not
    happen.  A claim about the future has to be settled before the execution
    counts. -/
def Machine.discharged (s : Machine) : Bool := s.promises.isEmpty

/-- A run exhibits a behaviour only if the oracle stayed inside the machine
    and every promise was kept.  The two failures are different in kind --
    `stuck` is the adversary naming a successor that does not exist,
    `discharged` is the program failing to keep its word -- but a demo has to
    discard both, so they are reported together. -/
def Machine.exhibits (s : Machine) : Bool := !s.stuck && s.discharged

/-- Run a program and return its result *only* if the run is a behaviour.

    Provided for clients that want the check to be unavoidable rather than
    remembered; the demos below print `exhibits` instead, because a row that
    silently disappeared would be a worse control than a row that says
    `behaviour=false` next to the outcome it would have had. -/
def behaviourOf {α : Type} (prog : M α) (s₀ : Machine) : Option (α × Machine) :=
  let r := prog.run s₀
  if r.2.exhibits then some r else none

def mfence (f : Fence) : M Unit :=
  modify fun s =>
    { s with vs := match f with
        | .ld => { s.vs with vPreBase := max s.vs.vPreBase s.vs.vRd }
        | .st => { s.vs with vRelSt := max s.vs.vRelSt s.vs.vWr }
        | .sy => { s.vs with
                     vPreBase := max s.vs.vPreBase (max s.vs.vRd s.vs.vWr)
                     vRelSt := max s.vs.vRelSt (max s.vs.vRd s.vs.vWr) } }

/-- A control dependency.  Takes the *value* it branched on, and uses its read
    timestamp -- the `rts` half of the asymmetry, now visible in the API. -/
def mbranch (d : TVal) : M Unit :=
  modify fun s => { s with vs := { s.vs with vCtrl := max s.vs.vCtrl d.rts } }

def misb : M Unit :=
  modify fun s => { s with vs := { s.vs with vPreBase := max s.vs.vPreBase s.vs.vCtrl } }

/-! ## 6. Specs, so that proofs do not unfold the machine

`load_reads_own_write` below was originally proved by handing `mstore` and
`mload` to `mvcgen` as unfoldings.  That works for two operations and does not
survive ten: every operation's definition lands in the goal, the case split on
the oracle multiplies, and the proof is about `Array.push` rather than about
memory.

The fix is the standard one: give each operation a `@[spec]` lemma stating what
it guarantees, then never unfold it again.  Two things make the lemmas usable.

* **The precondition is `s = s₀`.**  `s₀` is a ghost that `mvcgen` instantiates
  with whatever the state is at the call site, so the spec applies in any
  context.  Postconditions are then *relations* between the state before and the
  state after, which is what composition needs.
* **The postconditions are deliberately weak.**  They say what survives, not
  what happened.  A spec that pinned the exact resulting `Machine` would compose
  no better than unfolding, because the next operation's proof would have to
  take it apart again.

`publish_orders_data_before_flag` at the end is the test: three operations,
proved with nothing unfolded. -/

/-- Memory is append-only: it only grows, and an existing message never changes.

    This is the fact that makes composition work at all.  Every operation
    preserves it, so a value read out of memory at one point in a program is
    still there later, and no lemma about the intervening operations is
    needed. -/
def Extends (s₀ s : Machine) : Prop :=
  s₀.mem.size ≤ s.mem.size ∧ ∀ t, t < s₀.mem.size → s.mem[t]? = s₀.mem[t]?

theorem Extends.refl (s : Machine) : Extends s s := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Extends.trans {s₀ s₁ s₂ : Machine}
    (h₁ : Extends s₀ s₁) (h₂ : Extends s₁ s₂) : Extends s₀ s₂ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun t ht => by
    rw [h₂.2 t (Nat.lt_of_lt_of_le ht h₁.1), h₁.2 t ht]⟩

/-- The payoff of `Extends`: a message you found earlier is still there. -/
theorem Extends.msg {s₀ s : Machine} {t : Ts} {m : Msg}
    (h : Extends s₀ s) (ht : s₀.mem[t]? = some m) : s.mem[t]? = some m := by
  rcases Nat.lt_or_ge t s₀.mem.size with hlt | hge
  · rw [h.2 t hlt]; exact ht
  · rw [Array.getElem?_eq_none hge] at ht; simp at ht

/-- What a store guarantees, whichever branch the oracle takes.

    Note what is *not* here: which timestamp was used, whether memory grew, and
    anything about `coh`.  Appending and fulfilling a promise differ in all of
    those, and a caller that had to know which happened would be back to case
    analysis on the oracle. -/
structure StorePost (a : Address) (v : Val) (deps : List TVal) (rel : Bool)
    (s₀ s : Machine) : Prop where
  ext : Extends s₀ s
  /-- A store is stuck exactly when it was already stuck or the cell is outside
      every allocation.  Callers that need "not stuck" must therefore supply
      `allocated s₀ a`, which is the bounds obligation the load has always
      had. -/
  stuck : s.stuck = (s₀.stuck || !allocated s₀ a)
  /-- A plain store does not publish; only a fence or a release does.  (Named
      `pub` rather than `rel`: a field named `rel` would shadow the `rel`
      parameter in the fields below, which typechecks and means something
      else.) -/
  pub : s.vs.vRelSt = s₀.vs.vRelSt
  /-- The write is in memory, its view covers everything a preceding fence
      published, and `vWr` covers the write.  The last conjunct is what lets a
      later `dmb ishst` order against it. -/
  msg : ∃ t mv, s.mem[t]? = some ⟨a, v, mv⟩ ∧ s₀.vs.vRelSt ≤ mv ∧ t ≤ s.vs.vWr
  /-- **Where the write went, when nothing could be fulfilled.**  Coherence
      arguments need the first conjunct: knowing only that the write is
      *somewhere* in memory says nothing about what a later read of the same
      address must see.  §7's privacy argument needs it too, for a different
      reason: `reaches_push` is a statement about `push`.

      The last two conjuncts are what let a *sequence* of stores be analysed.
      Without the promise list being carried, the second store in a publication
      protocol cannot invoke this field at all; without `s₀.mem.size ≤ s.vs.vWr`
      a following `dmb ishst` publishes a bound that says nothing about the
      write just made.  `msg` almost gives the latter, but only for *some*
      timestamp holding that message -- an older, identical-looking message
      would satisfy it, which is exactly the ambiguity a coherence argument
      cannot afford.

      **The hypothesis is about candidates, not about promises.**  It used to
      be `s₀.promises = []`, which is the case every proof before §11.3 lives
      in, and `StorePost.append` below is still that specialisation.  But a
      promise at *another address* does not stop this store appending, and a
      writer that promises needs exactly that distinction -- so the hypothesis
      is the one the machine actually branches on. -/
  grew : fulfillable s₀ a v deps rel = [] →
    s.mem = s₀.mem.push ⟨a, v, mstoreView s₀ deps rel⟩ ∧
    s.vs.coh a = s₀.mem.size ∧
    s.promises = s₀.promises ∧
    s₀.mem.size ≤ s.vs.vWr
  /-- **Which promises survive.**  A store removes at most one promise, and
      only one it was allowed to keep.

      This is the clause that makes a *failed* promise provable.  Without it,
      nothing rules out a store quietly discharging an obligation it had no
      right to, and §11.3's fenced writer could not be a theorem -- only a
      demo. -/
  keep : ∀ p ∈ s₀.promises, p ∉ fulfillable s₀ a v deps rel → p ∈ s.promises
  /-- A local store changes neither the roots nor what Remote holds.  Both are
      needed to move a `Reaches` across it (§7). -/
  roots : s.roots = s₀.roots
  rknow : s.rknow = s₀.rknow
  /-- Nor does it change who owns what (§9), which is what lets a store and an
      environment step be chained in an ownership argument. -/
  disowned : s.rdisowned = s₀.rdisowned
  /-- A store does not allocate.  `stuck` above already says the store *checks*
      the allocation table; this says it does not *change* it, which is what
      lets a sequence of stores share one bounds argument. -/
  sizes : s.sizes = s₀.sizes

/-- `grew`, specialised to the promise-free world.  With nothing promised there
    is nothing to fulfil, so the candidate list is empty and the store appends.

    This was a *field* until §11.3 needed a writer that promises; it is a
    theorem with the same name, the same argument and the same shape, so every
    caller that says `hstore.append hprom` is untouched.  That is the point of
    keeping it: the promise-free specialisation is what almost every proof in
    this file actually wants, and making them all reason about candidate lists
    would be a cost with no reader. -/
theorem StorePost.append {a : Address} {v : Val} {deps : List TVal} {rel : Bool}
    {s₀ s : Machine} (h : StorePost a v deps rel s₀ s) (h0 : s₀.promises = []) :
    s.mem = s₀.mem.push ⟨a, v, mstoreView s₀ deps rel⟩ ∧
    s.vs.coh a = s₀.mem.size ∧
    s.promises = [] ∧
    s₀.mem.size ≤ s.vs.vWr := by
  have hf : fulfillable s₀ a v deps rel = [] := by rw [fulfillable, h0]; rfl
  obtain ⟨hmem, hcoh, hprom, hvw⟩ := h.grew hf
  exact ⟨hmem, hcoh, by rw [hprom, h0], hvw⟩

/-- What a load guarantees.  Conditional on not being stuck, which is the
    honest reading: an oracle that picked a nonexistent successor has not
    exhibited a behaviour of the program. -/
structure LoadPost (a : Address) (deps : List TVal) (s₀ : Machine)
    (r : TVal) (s : Machine) : Prop where
  mem : s.mem = s₀.mem
  rel : s.vs.vRelSt = s₀.vs.vRelSt
  /-- Three cases now, not two.  The middle one is what §10's load rule
      introduced: inside an allocation with nothing readable, the load returns
      `undef` and is *not* stuck, so neither of the old disjuncts holds.

      Stating it as "nothing at all was readable" rather than "the cell was
      unwritten" keeps it a fact about memory, and makes it exactly the
      hypothesis a coherence argument contradicts: any caller that knows one
      readable timestamp can discharge this case.

      The two readings are in fact the same, which is not obvious and is now a
      theorem: `unwritten_of_no_readable` turns this disjunct into "no write to
      `a` exists anywhere in `mem`", at every bound.  That is what justifies the
      `TVal.mk0` in the load rule -- a read with nothing to read carries no view
      and no timestamp because there is nothing for it to carry. -/
  read : s.stuck = true
    ∨ (r.val = Val.undef ∧
       ∀ t, readable s₀.mem a t (loadBound s₀ a deps) = false)
    ∨ (s₀.mem[r.rts]? = some ⟨a, r.val, r.view⟩ ∧
       readable s₀.mem a r.rts (loadBound s₀ a deps) = true)
  /-- A load is local and reads nothing into Remote, so none of the three
      things a reachability invariant depends on can move (§10). -/
  roots : s.roots = s₀.roots
  rknow : s.rknow = s₀.rknow
  promises : s.promises = s₀.promises
  /-- **What the load contributes to `vRd`** -- both the timestamp it took and
      the view that message carried.

      This is the reader-side mirror of `StorePost.append`'s `s₀.mem.size ≤
      s.vs.vWr`, and it was missing until §11.3 needed it, for a reason worth
      recording: no earlier theorem ordered one *load* against another through a
      fence.  §8's reader is ordered by an address dependency, which reaches
      `loadBound` through `tvView deps` and never touches `vRd` at all.  A
      seqlock's validating read has no dependency to exploit, so the ordering
      has to come the other way: into `vRd` here, out through `FencePost.pre`
      below.

      **Not for a read of this thread's own plain write** (`ownFwd`).  That
      read is forwarded from the store buffer, and contributes the store's
      forwarding view rather than its timestamp -- `rdV`, and the reason
      `SB+rfi-pos` is allowed.  `none` is the hypothesis any read of another
      thread's write discharges by `mine`. -/
  rd : ownFwd s₀.vs r.rts = none → max r.rts r.view ≤ s.vs.vRd
  /-- **`stuck` is sticky across a load.**  Every other `*Post` in this file
      pins `stuck` exactly; this one only claims monotonicity, because the two
      branches of `mload` disagree -- the empty branch may set it, the demonic
      branch cannot.

      A one-directional claim is all any caller has wanted, and it is what lets
      a loop invariant carry a per-item "…or the run is stuck" escape clause:
      once one iteration gives up, every later iteration inherits the excuse. -/
  stuck : s₀.stuck = true → s.stuck = true
  /-- A load does not allocate. -/
  sizes : s.sizes = s₀.sizes
  /-- **The converse of `stuck`, and the reason `stuck` alone was never enough**
      (§6.6).  Monotonicity lets a proof say "if it was already broken it stays
      broken"; a client that claims never to go wrong needs the other
      direction, and the other direction has a price: the caller must show the
      address is in bounds.

      Note what is *not* claimed.  The exact characterisation
      `s.stuck = true ↔ s₀.stuck = true ∨ allocated s₀ a = false` is **false**:
      a load of an out-of-bounds address that nonetheless has a readable message
      takes the second branch and does not get stuck (`readBackScenario` is
      exactly that state).  Only this implication holds in both branches, and it
      is the one a bounds discipline is trying to establish anyway. -/
  clean : s₀.stuck = false → allocated s₀ a = true → s.stuck = false
  /-- **A load never lowers the acquire barrier.**  A plain load leaves
      `vPreBase` exactly alone and an acquiring one raises it, so monotonicity
      is the clause that covers both.

      Third of the "only as strong as its first client" additions, and the one
      that made §17's reader provable.  A reader holding a lock needs its bound
      to keep reaching the cell's words across every load in the loop, and
      `loadBound` reaches them through `vPreBase`.  `rel` pins `vRelSt` because
      publication needed it; nothing before this needed the *reader's* barrier
      to survive a read. -/
  pre : s₀.vs.vPreBase ≤ s.vs.vPreBase

theorem mstoreView_ge_rel (s : Machine) (deps : List TVal) (rel : Bool) :
    s.vs.vRelSt ≤ mstoreView s deps rel := by
  unfold mstoreView
  split
  · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  · exact Nat.le_max_left _ _

/-- Fulfilling a promise means the filter already checked it, so the message is
    there with the right location and value, and with a view the store is
    allowed to publish. -/
theorem fulfillable_msg {s : Machine} {a : Address} {v : Val} {deps : List TVal}
    {rel : Bool} {t : Ts} (h : t ∈ fulfillable s a v deps rel) :
    ∃ mv, s.mem[t]? = some ⟨a, v, mv⟩ ∧ mstoreView s deps rel ≤ mv := by
  rw [fulfillable, List.mem_filter] at h
  have h2 := h.2
  cases hm : s.mem[t]? with
  | none => rw [hm] at h2; simp at h2
  | some m =>
    rw [hm] at h2
    simp only [Option.elim, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨hl, hv⟩, hview⟩, _⟩ := h2
    refine ⟨m.view, ?_, hview⟩
    subst hl; subst hv
    rfl

theorem fulfillable_lt {s : Machine} {a : Address} {v : Val} {deps : List TVal}
    {rel : Bool} {t : Ts} (h : t ∈ fulfillable s a v deps rel) : t < s.mem.size := by
  obtain ⟨mv, hmv, _⟩ := fulfillable_msg h
  rcases Nat.lt_or_ge t s.mem.size with hlt | hge
  · exact hlt
  · rw [Array.getElem?_eq_none hge] at hmv; simp at hmv

/-- The content of `mstore_spec`, stated about the resulting state rather than
    about the monad.  Everything hard is here, where it can be read: the monadic
    lemma below is one line.

    `t` is whatever the oracle chose; `ht` says only that it was one of the
    candidates, which is all `pick` guarantees.

    Written as `{ s₀ with … }` rather than field by field.  The first version
    listed every field, and adding Remote's state to `Machine` broke it with a
    page-long type mismatch; a record update names only what the store
    changes. -/
theorem store_post (a : Address) (v : Val) (deps : List TVal) (rel : Bool)
    (s₀ : Machine) (t : Ts) (ht : t ∈ s₀.mem.size :: fulfillable s₀ a v deps rel) :
    StorePost a v deps rel s₀
      { s₀ with
        stuck := s₀.stuck || !allocated s₀ a,
        mem := if t = s₀.mem.size then
                 s₀.mem.push ⟨a, v, mstoreView s₀ deps rel⟩ else s₀.mem,
        vs := { s₀.vs with
                  coh := fun b => if b = a then t else s₀.vs.coh b,
                  vWr := max s₀.vs.vWr t, mine := t :: s₀.vs.mine,
                  fwd := (t, tvBound deps) :: s₀.vs.fwd },
        promises := if t = s₀.mem.size then s₀.promises else s₀.promises.erase t,
        oracle := s₀.oracle.tail } := by
  rcases List.mem_cons.mp ht with rfl | hin
  · -- appended at the end of memory
    refine ⟨⟨?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp
    · intro u hu
      simp [Array.getElem?_push, Nat.ne_of_lt hu]
    · refine ⟨s₀.mem.size, mstoreView s₀ deps rel, ?_, mstoreView_ge_rel _ _ _,
        Nat.le_max_right _ _⟩
      simp
    · intro _; exact ⟨by simp, by simp, by simp, Nat.le_max_right _ _⟩
    · -- Nothing was erased, so every promise is still outstanding.
      intro p hp _; simpa using hp
  · -- fulfilled a promise, so memory does not change at all
    have hne : t ≠ s₀.mem.size := Nat.ne_of_lt (fulfillable_lt hin)
    obtain ⟨mv, hmv, hview⟩ := fulfillable_msg hin
    refine ⟨⟨?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [hne]
    · intro u _; simp [hne]
    · refine ⟨t, mv, ?_, Nat.le_trans (mstoreView_ge_rel _ _ _) hview,
        Nat.le_max_right _ _⟩
      simp only [ite_eq_right hne]; exact hmv
    · -- This branch exists only because there *was* a candidate.
      intro hf; rw [hf] at hin; simp at hin
    · -- Only `t` was erased, and `p` is not `t` because `t` was a candidate.
      intro p hp hnot
      have hpt : p ≠ t := fun h => hnot (h ▸ hin)
      simp only [ite_eq_right hne]
      exact (List.mem_erase_of_ne hpt).2 hp

@[spec]
theorem mstore_spec (a : Address) (v : Val) (deps : List TVal) (rel : Bool)
    (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    mstore a v deps rel
    ⦃⇓ _ s => ⌜StorePost a v deps rel s₀ s⌝⦄ := by
  mvcgen [mstore, demonic]
  subst_vars
  -- `mvcgen` leaves the post-state as a stack of let-bound variables, which
  -- definitional unfolding does not look through; `+zetaDelta` inlines them.
  simp +zetaDelta only []
  exact store_post a v deps rel _ _ (pick_mem _ _ _)

/-- What a promise guarantees.  Nothing about views -- a promise publishes
    nothing and reads nothing -- and everything about the two lists.

    The point of having this at all is composition.  `mpromise` has been in the
    front end since §5, but with no spec it could only appear in an `#eval`, so
    every claim about a promising program was a printed row rather than a
    proof.  `fenced_writer_cannot_discharge` in §11.3 is the first theorem that
    needs one.

    `made` is conditional because promising with a view at or above the current
    memory size is a no-op (see `mpromise`): you cannot publish something that
    has not happened.  Callers supply `view < s₀.mem.size`, which is the
    check. -/
structure PromisePost (a : Address) (v : Val) (view : Ts)
    (s₀ s : Machine) : Prop where
  ext : Extends s₀ s
  stuck : s.stuck = s₀.stuck
  /-- A promise moves no view at all.  This is what makes the fence in §11.3
      the only thing that raises `vRelSt` between the promise and the store. -/
  vs : s.vs = s₀.vs
  sizes : s.sizes = s₀.sizes
  roots : s.roots = s₀.roots
  rknow : s.rknow = s₀.rknow
  disowned : s.rdisowned = s₀.rdisowned
  /-- The message is appended and its timestamp is recorded as outstanding.
      Both halves are needed: the message is what a reader will find, the
      timestamp is what rule 3 will later demand be discharged. -/
  made : view < s₀.mem.size →
    s.mem = s₀.mem.push ⟨a, v, view⟩ ∧
    s.promises = s₀.promises ++ [s₀.mem.size]

@[spec]
theorem mpromise_spec (a : Address) (v : Val) (view : Ts) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    mpromise a v view
    ⦃⇓ _ s => ⌜PromisePost a v view s₀ s⌝⦄ := by
  mvcgen [mpromise]
  subst_vars
  simp +zetaDelta only []
  -- `mpromise` is one `if`, so every field splits on it; the else branch is
  -- the identity state, and `made`'s hypothesis contradicts it.
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · split <;> simp
  · intro u hu; split <;> simp [Array.getElem?_push, Nat.ne_of_lt hu]
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · intro h
    split
    · exact ⟨rfl, rfl⟩
    · next hn => exact absurd h hn

/-- What a fence guarantees.  Memory is untouched; the content is in `rel`. -/
structure FencePost (f : Fence) (s₀ s : Machine) : Prop where
  mem : s.mem = s₀.mem
  stuck : s.stuck = s₀.stuck
  wr : s.vs.vWr = s₀.vs.vWr
  /-- A fence issues nothing, so it cannot promise.  Needed so that a store
      *after* a fence can still appeal to `StorePost.append`. -/
  promises : s.promises = s₀.promises
  /-- `dmb ishst` (and `dmb ish`) publish every write issued so far, so a later
      store's message view covers them.  This single line is the whole reason a
      publication protocol works, and it is why the theorem below needs the
      fence. -/
  rel : f ≠ .ld → s₀.vs.vWr ≤ s.vs.vRelSt
  /-- Nor does a fence change who owns what (§9). -/
  disowned : s.rdisowned = s₀.rdisowned
  /-- **The mirror of `rel`, and the reason it took until §11.3 to appear.**
      `dmb ishld` (and `dmb ish`) push everything read so far into `vPreBase`,
      which bounds every *later* load.  `rel` is what makes a publication
      protocol work; this is what makes a *validation* protocol work, and a
      seqlock is the first thing here that needs one. -/
  pre : f ≠ .st → s₀.vs.vRd ≤ s.vs.vPreBase
  /-- A fence does not allocate. -/
  sizes : s.sizes = s₀.sizes

@[spec]
theorem mfence_spec (f : Fence) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄ mfence f ⦃⇓ _ s => ⌜FencePost f s₀ s⌝⦄ := by
  mvcgen [mfence]
  subst_vars
  simp +zetaDelta only []
  refine ⟨rfl, rfl, ?_, rfl, ?_, rfl, ?_, rfl⟩
  · cases f <;> rfl
  · intro hf
    cases f
    · exact absurd rfl hf
    · exact Nat.le_max_right _ _
    · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  · intro hf
    cases f
    · exact Nat.le_max_right _ _
    · exact absurd rfl hf
    · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- A fence does not touch memory, so it extends it vacuously. -/
theorem FencePost.ext {f : Fence} {s₀ s : Machine} (h : FencePost f s₀ s) :
    Extends s₀ s := by
  rw [Extends, h.mem]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩

/-! ### The test: does this compose?

Three operations, and a conclusion about memory that mentions neither the
oracle nor `Array.push`.  Nothing is unfolded -- `mvcgen` is given only
`publish` itself, and the three specs above do the rest.

The property is the one stage 3 exists to prove: after the fence, the flag's
message view covers the timestamp of the data write.  A reader that sees the
flag and inherits its view is therefore ordered after the data write, so it
cannot read anything the data write hid.  Remove the `mfence` and the proof
stops going through at exactly `FencePost.rel`, which is the honest place for
it to fail. -/

def publish (data flag : Address) (v : Val) : M Unit := do
  mstore data v
  mfence .st
  mstore flag (Val.num 1)

theorem publish_orders_data_before_flag
    (data flag : Address) (v : Val) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    publish data flag v
    ⦃⇓ _ s => ⌜∃ (td mvd tf mvf : Ts),
      s.mem[td]? = some (Msg.mk data v mvd) ∧
      s.mem[tf]? = some (Msg.mk flag (Val.num 1) mvf) ∧
      td ≤ mvf⌝⦄ := by
  mvcgen [publish]
  -- One hypothesis per operation, and not a `push` or an oracle in sight.
  rename_i _ _ _ _ hstore _ _ hfence _ _
  intro hflag
  obtain ⟨td, mvd, hd, _, hdw⟩ := hstore.msg
  obtain ⟨tf, mvf, hf, hrel, _⟩ := hflag.msg
  exact ⟨td, mvd, tf, mvf,
    hflag.ext.msg (hfence.ext.msg hd), hf,
    Nat.le_trans hdw (Nat.le_trans (hfence.rel (by simp)) hrel)⟩


/-! ### A `do`-block the staged design could not write

Staging had to replace `if` on a loaded value with the object language's
`branch`/`isb`, because its bind variable was the name `W0`.  Here the bind
variable is the value, so both are available and they mean different things:
the Lean `if` is a *proof-level* case split, the `mbranch` is the
*machine-level* control dependency. -/

def consumeFlag (flag data : Address) : M Val := do
  let f ← mload flag
  mbranch f
  misb
  if f.val = Val.num 1 then
    let d ← mload data [f]
    pure d.val
  else
    pure Val.undef

/-! ### The pure content

Read-own-write coherence: immediately after appending a write to `a`, the only
timestamp a reader of `a` can be at is the one just written.  This is where the
actual work is; the triple below is then a two-line composition.

Note this is a statement about `readable`/`hiddenFrom` -- the memory subsystem
that herd7 validated -- not about anything the front-end invented. -/

theorem readable_push_eq (mem : Memory) (a : Address) (v : Val) (w bound t : Ts)
    (hb : mem.size ≤ bound)
    (h : readable (mem.push ⟨a, v, w⟩) a t bound = true) : t = mem.size := by
  rcases Nat.lt_trichotomy t mem.size with hlt | heq | hgt
  · -- Below the new write, so the new write hides it.
    exfalso
    have hhid : hiddenFrom (mem.push ⟨a, v, w⟩) a t bound = true := by
      unfold hiddenFrom
      rw [List.any_eq_true]
      refine ⟨mem.size, ?_, ?_⟩
      · simp only [List.mem_range]; omega
      · simp [hlt]
    unfold readable at h
    simp [hhid] at h
  · exact heq
  · -- Past the end, so there is nothing there to read.
    exfalso
    have hsz : (mem.push (⟨a, v, w⟩ : Msg)).size ≤ t := by
      simp only [Array.size_push]; omega
    have hnone : (mem.push (⟨a, v, w⟩ : Msg))[t]? = none :=
      Array.getElem?_eq_none hsz
    unfold readable at h
    simp [hnone] at h

/-- The existence half, which the new load rule made necessary.

    `readable_push_eq` says *at most* one timestamp is readable; §10's load can
    now also report that *none* is, so a caller who has just written the
    location needs to say that at least one is.  Uniqueness without existence
    was enough only while "nothing readable" implied "stuck".

    There is deliberately no `mem.size ≤ bound` hypothesis: `readable` never
    asks that the timestamp be at or below the bound.  The bound only says which
    timestamps are allowed to *hide* it, so it can only ever make a timestamp
    less readable, and the uniqueness half is the one that needs it. -/
theorem readable_push_top (mem : Memory) (a : Address) (v : Val) (w bound : Ts) :
    readable (mem.push ⟨a, v, w⟩) a mem.size bound = true := by
  have hhid : hiddenFrom (mem.push ⟨a, v, w⟩) a mem.size bound = false := by
    unfold hiddenFrom
    rw [List.any_eq_false]
    intro t' _
    -- Anything above the new write is past the end of memory.
    by_cases hlt : mem.size < t'
    · have hge : (mem.push (⟨a, v, w⟩ : Msg)).size ≤ t' := by
        simp only [Array.size_push]; omega
      simp [Array.getElem?_eq_none hge]
    · simp [hlt]
  -- The new message itself is found by `Array.getElem?_push_size`.
  unfold readable
  simp [hhid]


/-! ### The load spec -/

theorem readable_of_pick (mem : Memory) (a : Address) (bound : Ts)
    (c : Ts) (cs : List Ts)
    (hf : (List.range mem.size).filter (fun t => readable mem a t bound) = c :: cs)
    (i : Nat) : readable mem a (pick i c cs) bound = true := by
  have hmem := pick_mem i c cs
  rw [← hf, List.mem_filter] at hmem
  exact hmem.2

theorem msg_of_readable {mem : Memory} {a : Address} {t bound : Ts}
    (h : readable mem a t bound = true) : ∃ m, mem[t]? = some m ∧ m.loc = a := by
  unfold readable at h
  rw [Bool.and_eq_true] at h
  cases hm : mem[t]? with
  | none => rw [hm] at h; simp at h
  | some m =>
    refine ⟨m, rfl, ?_⟩
    rw [hm] at h
    simpa using h.1

@[spec]
theorem mload_spec (a : Address) (deps : List TVal) (acq : Bool) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    mload a deps acq
    ⦃⇓ r s => ⌜LoadPost a deps s₀ r s⌝⦄ := by
  mvcgen [mload, demonic]
  case vc1.h_1 =>
    -- Nothing readable at `a`.  The filter being empty is a statement about
    -- `List.range mem.size` only, so the out-of-range timestamps have to be
    -- handled separately -- they are unreadable because there is no message.
    subst_vars
    simp +zetaDelta only []
    -- Five names: the state, its two let-bound projections, the filter's
    -- equation, and the let-bound result pair.
    rename_i s _ _ hfilter _
    refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, fun t => ?_⟩), rfl, rfl, rfl,
      fun _ => Nat.zero_le _, fun h => by simp [h], rfl, fun h1 h2 => by simp [h1, h2],
      Nat.le_refl _⟩
    rcases Nat.lt_or_ge t s.mem.size with hlt | hge
    · -- Inside the range the filter looked at, so the filter ruled it out.
      have hno := List.filter_eq_nil_iff.mp hfilter t (List.mem_range.mpr hlt)
      simpa using hno
    · -- Past the end of memory: no message, so nothing to read.
      unfold readable
      rw [Array.getElem?_eq_none hge]
      simp
  case vc2.h_2 =>
    subst_vars
    simp +zetaDelta only []
    -- Eight names: the state, its two let-bound projections, the filter's
    -- cons pattern, and the two let-bound intermediate states.
    rename_i s _ _ c cs hf _ _
    have hr := readable_of_pick _ a _ c cs hf (s.oracle.headD 0)
    obtain ⟨m, hm, hloc⟩ := msg_of_readable hr
    refine ⟨rfl, rfl, Or.inr (Or.inr ⟨?_, hr⟩), rfl, rfl, rfl,
      fun hnf => by rw [rdV_none _ hnf]; exact pairTop_max_le _ _ _ _,
      fun h => h, rfl, fun h _ => h, ?_⟩
    · rw [hm]
      simp [← hloc]
    · -- `pre`: the plain branch leaves `vPreBase` alone, the acquiring one
      -- raises it.  Monotone either way.
      dsimp only
      split
      · exact Nat.le_max_left _ _
      · exact Nat.le_refl _

/-! ### The triple

What `mvcgen` proves here is a fact about *memory*: whatever the oracle does,
the load either gets stuck or returns the value just written.  The best the
staged design could manage was a triple whose postcondition said how many
instructions the compiler had emitted.

The `promises = []` hypothesis keeps the store deterministic (with an
outstanding promise it could also fulfill, at a different timestamp); the
statement is true without it, but the extra case is bookkeeping, not content.

This was originally proved by unfolding `mstore` and `mload` into `mvcgen`.
It is proved from the specs now, and the difference in what the proof mentions
is the point: `Array.push` appears only inside `readable_push_eq`, which is a
statement about memory that has nothing to do with the monad. -/

theorem load_reads_own_write (a : Address) (v : Val) :
    ⦃fun s => ⌜s.promises = [] ∧ s.stuck = false⌝⦄
    (do mstore a v; mload a : M TVal)
    ⦃⇓ r s => ⌜s.stuck = true ∨ r.val = v⌝⦄ := by
  mvcgen
  rename_i s₀ hpre _ s₁ hstore _ _
  intro hload
  obtain ⟨hmem, hcoh, _, _⟩ := hstore.append hpre.1
  -- The load's bound is at least `coh a`, which the store set to the
  -- timestamp it wrote at, so coherence forces the read to that timestamp.
  have hb : s₀.mem.size ≤ loadBound s₁ a [] := by
    rw [← hcoh]
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  rcases hload.read with hstuck | ⟨_, hnone⟩ | ⟨hmsg, hr⟩
  · exact Or.inl hstuck
  · -- Nothing readable -- but the store's own write is, so this cannot happen.
    exfalso
    have := hnone s₀.mem.size
    rw [hmem, readable_push_top s₀.mem a v _ _] at this
    simp at this
  · right
    rw [hmem] at hr hmsg
    have ht := readable_push_eq s₀.mem a v _ _ _ hb hr
    rw [ht] at hmsg
    simp at hmsg
    exact hmsg.1.symm



/-- The triple's postcondition is a disjunction, so it could in principle be
    satisfied by a program that always gets stuck.  It is not: running the same
    `do`-block concretely returns the written value with `stuck = false`.  A
    disjunctive spec deserves this check. -/
def coherenceDemo : String :=
  let s0 : Machine := { mem := #[⟨x, Val.num 0, 0⟩], sizes := [1], oracle := [0, 0] }
  let (r, s) := (do mstore x (Val.num 7); mload x : M TVal).run s0
  s!"read-own-write: loaded {repr r.val} from t={r.rts}, stuck={s.stuck}, " ++
  s!"mem.size={s.mem.size}"

/-! ## 7. Remote (D2)

One adversary, not one per thread.  That is sound *because* POWER was dropped:
ARMv8 and x86-TSO are both other-multi-copy-atomic, so a write that becomes
visible to anyone becomes visible to everyone, and the only per-thread freedom
left is local reordering -- which one maximally-permissive observer covers.

> [!WARNING]
> The abstraction is sound for *per-observer* properties ("no remote load ever
> reads `undef`") and **not** for properties relating two distinct remote
> observers ("T2 and T3 agree on the order of these two writes").  Two
> independent reorderers are not one sequential reorderer.  Everything below is
> in the sound class; stepping outside it needs a second agent.

### Where the no-forging assumption lives

The privacy theorem is only true if Remote cannot fabricate an address.  The
design sketch made this an axiom about the environment step.  It is better as a
*data structure*: `Machine.rknow` is every address Remote holds, and the only
rule that extends it is `rload`, when the value it read happens to be a pointer.
Forging is not forbidden, it is unrepresentable.

So the theorem to prove is not "Remote does not forge" -- that is true by
construction -- but that `rknow` never escapes what is genuinely reachable:

* `Reaches s l` -- `l` is reachable from the roots through pointers in memory.
* `RKnowSound s` -- every address Remote holds has a reachable label.
* `renv` preserves both, and preserves `¬ Reaches s l` for any `l`.

The last one is the content.  A remote store writes a pointer, which is exactly
the operation that could make something newly reachable -- and does not, because
the pointer it writes came out of `rknow`.

### What is deliberately missing

Remote does not promise.  Promises change which *orderings* are observable, not
which addresses are *touchable*, so this does not weaken the privacy results
below; it would matter for a liveness or ordering claim about Remote, and there
are none.  Flagged because it is the kind of asymmetry that silently becomes
unsound when the theorems change. -/

/-- Reachability from the roots, through pointers stored in memory.

    Depends on `s.roots` and `s.mem` only -- never on `rknow`, which is the
    point: this is the *ground truth* that `RKnowSound` measures Remote
    against.  Making it depend on `rknow` would make `RKnowSound` a tautology.

    Granularity is the allocation label, not the address.  That is coarser than
    necessary, which is the safe direction: it gives Remote more reach than it
    really has, so a privacy proof that goes through here goes through. -/
inductive Reaches (s : Machine) : AllocLabel → Prop
  | root {a : Address} : a ∈ s.roots → Reaches s a.label
  | ptr {t : Ts} {m : Msg} {b : Address} {g : Nat} :
      s.mem[t]? = some m → Reaches s m.loc.label → m.val = Val.loc b g →
      Reaches s b.label

/-- Remote holds nothing it could not have reached. -/
def RKnowSound (s : Machine) : Prop :=
  ∀ ra ∈ s.rknow, Reaches s ra.addr.label

/-! ### The master lemma

Everything about exposure reduces to this: appending one message cannot make a
label reachable unless that message is itself the pointer that reaches it.
Stated for arbitrary `s'` rather than for a `push` helper so that it applies to
`mstore`'s append branch and to `rstore` without either having to be unfolded. -/

theorem reaches_push {s s' : Machine} {a : Address} {v : Val} {w : Ts}
    (hroots : s'.roots = s.roots) (hmem : s'.mem = s.mem.push ⟨a, v, w⟩)
    (hnew : ∀ b g, v = Val.loc b g → Reaches s a.label → Reaches s b.label)
    {l : AllocLabel} (h : Reaches s' l) : Reaches s l := by
  induction h with
  | root hr => exact Reaches.root (hroots ▸ hr)
  | @ptr t m b g hm _ hv ih =>
    rw [hmem] at hm
    rcases Nat.lt_or_ge t s.mem.size with hlt | hge
    · -- An old message: unchanged, so the same step is available in `s`.
      rw [Array.getElem?_push_lt hlt] at hm
      exact Reaches.ptr (by rw [Array.getElem?_eq_getElem hlt]; exact hm) ih hv
    · -- The new message.  `ih` says its *address* was already reachable, and
      -- `hnew` is exactly the obligation that its *value* then is too.
      have ht : t = s.mem.size := by
        rw [Array.getElem?_push] at hm
        by_cases he : t = s.mem.size
        · exact he
        · rw [ite_eq_right he] at hm
          rw [Array.getElem?_eq_none hge] at hm
          simp at hm
      subst ht
      rw [Array.getElem?_push_size] at hm
      cases hm
      exact hnew b g hv ih

/-- The case the program side needs: storing a non-pointer exposes nothing. -/
theorem reaches_push_nonptr {s s' : Machine} {a : Address} {v : Val} {w : Ts}
    (hroots : s'.roots = s.roots) (hmem : s'.mem = s.mem.push ⟨a, v, w⟩)
    (hv : ∀ b g, v ≠ Val.loc b g) {l : AllocLabel} (h : Reaches s' l) : Reaches s l :=
  reaches_push hroots hmem (fun b g hb => absurd hb (hv b g)) h

/-! ### Reachability is about memory, not about the machine

Two congruences.  `reaches_of_eq` is for operations that do not touch memory --
which is every remote *load*, and is why a load can never expose anything.
`reaches_mono` is the growth direction, needed to carry the invariant forward
across an operation that appends. -/

theorem reaches_of_eq {s s' : Machine} (hr : s'.roots = s.roots)
    (hm : s'.mem = s.mem) {l : AllocLabel} (h : Reaches s' l) : Reaches s l := by
  induction h with
  | root hx => exact Reaches.root (hr ▸ hx)
  | ptr hmsg _ hv ih => exact Reaches.ptr (hm ▸ hmsg) ih hv

/-- Memory only grows, so reachability only grows.  Needed to carry
    `RKnowSound` across a remote store. -/
theorem reaches_mono {s₀ s : Machine} (hr : s.roots = s₀.roots)
    (he : Extends s₀ s) {l : AllocLabel} (h : Reaches s₀ l) : Reaches s l := by
  induction h with
  | root hx => exact Reaches.root (hr ▸ hx)
  | ptr hm _ hv ih => exact Reaches.ptr (he.msg hm) ih hv

/-! ### The rely lemma

`EnvPost` is what the program may assume about a step it does not control.

Every privacy conclusion is *guarded* by `RKnowSound s₀` rather than asserted
outright, for the same reason `StorePost.append` is guarded by
`s₀.promises = []`: it keeps the precondition at `s = s₀`, so `mvcgen` applies
the spec everywhere with nothing to discharge, and the caller pays only where it
uses the conclusion.  `sound` is what makes that work across a whole program --
it hands the invariant back, so a chain of environment steps needs it
established once. -/

structure EnvPost (s₀ s : Machine) : Prop where
  ext : Extends s₀ s
  /-- Remote does not touch Local's views.  This is the clause that makes an
      environment step *free* in an ordering proof: every bound Local computes
      is the bound it would have computed had the step not happened. -/
  vs : s.vs = s₀.vs
  stuck : s.stuck = s₀.stuck
  promises : s.promises = s₀.promises
  roots : s.roots = s₀.roots
  /-- **No new exposure.**  Remote writing a pointer is the one operation that
      could make something newly reachable, and it does not, because the
      pointer came out of `rknow`. -/
  priv : RKnowSound s₀ → ∀ l, Reaches s l → Reaches s₀ l
  /-- The invariant chains. -/
  sound : RKnowSound s₀ → RKnowSound s
  /-- Anything Remote wrote, it wrote somewhere it could already reach.  Read
      contrapositively with `¬ Reaches s₀ l`: Remote did not write to `l`. -/
  wrote : RKnowSound s₀ → ∀ t m, s₀.mem.size ≤ t → s.mem[t]? = some m →
            Reaches s₀ m.loc.label
  /-- The environment cannot transfer ownership to itself. -/
  disowned : s.rdisowned = s₀.rdisowned
  /-- **The ownership clause** (§9).  Nothing the environment appended lies in
      an allocation it has given up.

      Note the difference in strength from `wrote`.  `wrote` says Remote only
      writes where it can *reach*, which is a statement about the pointer graph
      and says nothing once you have published.  `frozen` survives publication:
      Remote may hold the address, may read it, may reach everything through
      it -- and still may not write it.  That is what makes transfer *into* the
      program statable, and it is unconditional rather than guarded by
      `RKnowSound`, because it does not depend on reachability at all. -/
  frozen : ∀ t m, s₀.mem.size ≤ t → s.mem[t]? = some m →
             m.loc.label ∉ s₀.rdisowned
  /-- **Remote does not allocate** (§6.6).  The allocation table is Local's
      alone, so `allocated s a` is the same question after an environment step
      as before it.

      Every earlier theorem here was about what is *in* memory, and none of them
      asked whether an address was in bounds; a growable array is the first
      client whose correctness is a bounds property, and a bounds property that
      the environment could invalidate would not survive a single `renv`.  This
      is a modelling decision, not a hardware fact -- a real allocator is shared
      -- and it is the same decision as "`roots` never changes": the parts of
      the state that describe the *shape* of the heap belong to the program. -/
  sizes : s.sizes = s₀.sizes

theorem EnvPost.refl (s : Machine) : EnvPost s s where
  ext := Extends.refl s
  vs := rfl
  stuck := rfl
  promises := rfl
  roots := rfl
  priv := fun _ _ h => h
  sound := fun h => h
  wrote := fun _ t m hge hm => by
    rw [Array.getElem?_eq_none hge] at hm; simp at hm
  disowned := rfl
  frozen := fun t m hge hm => by
    rw [Array.getElem?_eq_none hge] at hm; simp at hm
  sizes := rfl

theorem EnvPost.trans {s₀ s₁ s₂ : Machine}
    (h₁ : EnvPost s₀ s₁) (h₂ : EnvPost s₁ s₂) : EnvPost s₀ s₂ where
  ext := h₁.ext.trans h₂.ext
  vs := by rw [h₂.vs, h₁.vs]
  stuck := by rw [h₂.stuck, h₁.stuck]
  promises := by rw [h₂.promises, h₁.promises]
  roots := by rw [h₂.roots, h₁.roots]
  priv := fun hs l h => h₁.priv hs l (h₂.priv (h₁.sound hs) l h)
  sound := fun hs => h₂.sound (h₁.sound hs)
  wrote := fun hs t m hge hm => by
    rcases Nat.lt_or_ge t s₁.mem.size with hlt | hge1
    · -- written by the first step
      exact h₁.wrote hs t m hge (h₂.ext.2 t hlt ▸ hm)
    · -- written by the second; pull its conclusion back through the first
      exact h₁.priv hs _ (h₂.wrote (h₁.sound hs) t m hge1 hm)
  disowned := by rw [h₂.disowned, h₁.disowned]
  frozen := fun t m hge hm => by
    -- Same split as `wrote`, but the second case needs no invariant carried
    -- forward -- only that the disowned set did not change under the first
    -- step, which is what `disowned` is for.
    rcases Nat.lt_or_ge t s₁.mem.size with hlt | hge1
    · exact h₁.frozen t m hge (h₂.ext.2 t hlt ▸ hm)
    · exact h₁.disowned ▸ h₂.frozen t m hge1 hm
  sizes := by rw [h₂.sizes, h₁.sizes]

/-! ### Remote's operations

Remote's ordering rules are the same as Local's, read off `rvs` instead of `vs`.
They are deliberately *weak*: a remote load is bounded by `vPreBase`, the
per-location coherence view, and the dependency view of the address it went
through -- and by nothing else on ARM.  So two remote loads in sequence are
unordered unless the second goes through the first, which is the whole point.
It is what makes the reader-side half of publication a real obligation rather
than something the model hands you.

Each operation is a `modify` by a **named state function** (`rloadStep`,
`rstoreStep`) rather than an inline record update, including the oracle bump.
That is what lets the pure lemmas below be stated as `EnvPost s (rloadStep …)`
instead of quoting a half-page term, and it is the same move that made §6's
`loadBound`/`mstoreView` worth naming. -/

/-- Clamped choice among `n` alternatives.  Clamping rather than failing means
    no proof ever has to reason about "the oracle was bad". -/
def demonicIdx (n : Nat) : M Nat :=
  modifyGet fun s =>
    (if n = 0 then 0 else s.oracle.headD 0 % n, { s with oracle := s.oracle.tail })

def rloadBound (s : Machine) (ra : RAddr) : Ts :=
  let ordered := if s.arch = .tso then s.rvs.vRd else 0
  max (max (max s.rvs.vPreBase (s.rvs.coh ra.addr)) ra.view) ordered

/-- The address dependency, as a function of the message read.

    Factored out because §8's reader chains a dereference through exactly this
    pointer, and a second copy of the rule would be a second thing to keep in
    sync.  `max ra.view m.view` is the whole mechanism: the pointer carries
    both what its own address was ordered after and what the message that
    produced it published. -/
def rlearnedOf (ra : RAddr) (m : Msg) : Option RAddr :=
  match m.val with
  | .loc b _ => some ⟨b, max ra.view m.view⟩
  | _ => none

/-- The effect of Remote reading timestamp `t` through `ra`. -/
def rloadStep (s : Machine) (ra : RAddr) (t : Ts) : Machine :=
  let m := s.mem[t]?.getD ⟨ra.addr, Val.undef, 0⟩
  { s with
    oracle := s.oracle.tail
    rvs := { s.rvs with
               coh := fun b => if b = ra.addr then max (s.rvs.coh ra.addr) t
                               else s.rvs.coh b,
               vRd := max s.rvs.vRd m.view }
    rknow := match rlearnedOf ra m with
             | some rb => s.rknow ++ [rb]
             | none => s.rknow
    rreads := s.rreads ++ [m.val] }

/-- Returns the message read, so a reader can dereference through it.  `none`
    means nothing at `ra.addr` was readable -- Remote simply does not read.  Not
    stuck: this is the environment, not the program under test. -/
def rload (ra : RAddr) : M (Option Msg) := do
  let s ← get
  match (List.range s.mem.size).filter
          fun t => readable s.mem ra.addr t (rloadBound s ra) with
  | [] => pure none
  | c :: cs =>
      let t := pick (s.oracle.headD 0) c cs
      modify fun s' => rloadStep s' ra t
      pure s.mem[t]?

/-- The value a remote store writes.  `j = 0` writes a scalar; otherwise it
    writes a pointer **taken from `rknow`**.  There is no third case, and that
    absence is the no-forging assumption: forging is not forbidden by a side
    condition, it is unrepresentable.

    Nested matches rather than one match on the pair: `split` on a two-scrutinee
    match produces binders in an order that is painful to name. -/
def rstoreVal (s : Machine) (j : Nat) : Val :=
  match j with
  | 0 => Val.num 0
  | k + 1 =>
      match s.rknow[k]? with
      | some rb => Val.loc rb.addr 0
      | none => Val.num 0

/-- The whole content of no-forging, in one lemma. -/
theorem rstoreVal_reaches {s : Machine} {j : Nat} {b : Address} {g : Nat}
    (hs : RKnowSound s) (h : rstoreVal s j = Val.loc b g) : Reaches s b.label := by
  cases j with
  | zero => simp [rstoreVal] at h
  | succ k =>
    cases hrb : s.rknow[k]? with
    | none => simp [rstoreVal, hrb] at h
    | some rb =>
      simp only [rstoreVal, hrb] at h
      have hin : rb ∈ s.rknow := by
        rw [List.getElem?_eq_some_iff] at hrb
        obtain ⟨hlt, he⟩ := hrb
        exact he ▸ List.getElem_mem hlt
      have hb : rb.addr = b := (Val.loc.inj h).1
      exact hb ▸ hs rb hin

/-- The write itself, with no ownership check.  Named separately so that
    `rstore_post` can be proved once about the append and then lifted through
    the guard: with the `if` in the way, even `vs := rfl` stops working, because
    the record projections cannot reduce past an undecided branch. -/
def rstoreAppend (s : Machine) (ra : RAddr) (j : Nat) : Machine :=
  { s with
    mem := s.mem.push ⟨ra.addr, rstoreVal s j, max s.rvs.vRelSt ra.view⟩
    rvs := { s.rvs with
               coh := fun b => if b = ra.addr then s.mem.size else s.rvs.coh b,
               vWr := max s.rvs.vWr s.mem.size, mine := s.mem.size :: s.rvs.mine } }

/-- A remote write, unless the allocation has been transferred away (§9).

    The guard is a no-op branch rather than a precondition on `rstore`, so that
    `renv` keeps its shape and `renv_spec`'s case structure is unchanged: the
    environment still *attempts* every step, it just has no effect on an
    allocation it does not own.  That also means ownership costs nothing
    anywhere it is not used -- with `rdisowned = []` this is the old
    definition. -/
def rstoreStep (s : Machine) (ra : RAddr) (j : Nat) : Machine :=
  if ra.addr.label ∈ s.rdisowned then s else rstoreAppend s ra j

def rstore (ra : RAddr) (j : Nat) : M Unit :=
  modify fun s => rstoreStep s ra j

/-- One environment step: stutter, read, or write, at an address Remote holds.

    Written in the `do`-block by hand rather than woven into every operation.
    `renv_spec` is what makes that cheap -- `mvcgen` discharges it wherever it
    appears, so an interleaving costs one line of program and nothing in the
    proof. -/
def renv : M Unit := do
  let s ← get
  match s.rknow with
  | [] => pure ()        -- Remote holds nothing, so it can do nothing.
  | r :: rs =>
      let ra ← demonic r rs
      let act ← demonicIdx 3
      match act with
      | 0 => pure ()
      | 1 => do let _ ← rload ra; pure ()
      | _ => do
          let j ← demonicIdx (s.rknow.length + 1)
          rstore ra j

/-! ### The pure content

As in §6, the work is in lemmas about the resulting state, and the monadic
lemmas are three lines each.

Every reachability lemma below is applied with its machine arguments named.
They are all definitionally equal on `roots` and (for a load) `mem`, so a bare
`rfl` unifies the two machines into one and the implication collapses to the
identity -- which typechecks in the wrong direction and produces an error
several lines away from the cause. -/

/-- A remote load exposes nothing, because it does not write.  The only thing
    to check is that a pointer it *learns* was already reachable. -/
theorem rload_post (s : Machine) (ra : RAddr) (t : Ts)
    (hr : readable s.mem ra.addr t (rloadBound s ra) = true)
    (hk : ra ∈ s.rknow) : EnvPost s (rloadStep s ra t) := by
  obtain ⟨m, hm, hloc⟩ := msg_of_readable hr
  have hmval : (s.mem[t]?.getD ⟨ra.addr, Val.undef, 0⟩) = m := by rw [hm]; rfl
  have hmemeq : (rloadStep s ra t).mem = s.mem := rfl
  refine ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, rfl, ?_, rfl⟩
  · exact fun _ l h => reaches_of_eq (s := s) (s' := rloadStep s ra t) rfl rfl h
  · -- `rknow` may have gained the pointer just read.  It was already reachable:
    -- the message sits at an address Remote could reach.
    intro hs rb hrb
    refine reaches_of_eq (s := rloadStep s ra t) (s' := s) rfl rfl ?_
    simp only [rloadStep, hmval] at hrb
    cases hv : m.val with
    | undef =>  simp only [rlearnedOf, hv] at hrb; exact hs rb hrb
    | null =>   simp only [rlearnedOf, hv] at hrb; exact hs rb hrb
    | num n =>  simp only [rlearnedOf, hv] at hrb; exact hs rb hrb
    | loc b =>
      simp only [rlearnedOf, hv] at hrb
      simp only [List.mem_append, List.mem_singleton] at hrb
      rcases hrb with hin | rfl
      · exact hs rb hin
      · exact Reaches.ptr hm (hloc ▸ hs ra hk) hv
  · intro _ t' m' hge hm'
    rw [hmemeq, Array.getElem?_eq_none hge] at hm'
    simp at hm'
  · intro t' m' hge hm'
    rw [hmemeq, Array.getElem?_eq_none hge] at hm'
    simp at hm'

/-- A remote store *does* write, and writes a pointer, so this is where
    `reaches_push` earns its keep.

    Stated about `rstoreAppend`: the guarded version is the corollary below.
    `hd` is used by exactly one field -- `frozen` -- which is the whole content
    of the ownership discipline. -/
theorem rstore_append_post (s : Machine) (ra : RAddr) (j : Nat)
    (hk : ra ∈ s.rknow) (hd : ra.addr.label ∉ s.rdisowned) :
    EnvPost s (rstoreAppend s ra j) := by
  have hext : Extends s (rstoreAppend s ra j) := by
    refine ⟨by simp [rstoreAppend], fun u hu => ?_⟩
    simp [rstoreAppend, Array.getElem?_push, Nat.ne_of_lt hu]
  -- Every appended message is the one at `s.mem.size`, so both `wrote` and
  -- `frozen` reduce to a fact about a single known message.
  have hone : ∀ u m', s.mem.size ≤ u → (rstoreAppend s ra j).mem[u]? = some m' →
      m' = ⟨ra.addr, rstoreVal s j, max s.rvs.vRelSt ra.view⟩ := by
    intro u m' hge hm'
    have hu : u = s.mem.size := by
      simp only [rstoreAppend] at hm'
      rw [Array.getElem?_push] at hm'
      by_cases he : u = s.mem.size
      · exact he
      · rw [ite_eq_right he, Array.getElem?_eq_none hge] at hm'; simp at hm'
    subst hu
    simp only [rstoreAppend, Array.getElem?_push_size] at hm'
    exact (Option.some.inj hm').symm
  refine ⟨hext, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl, ?_, rfl⟩
  · exact fun hs l h =>
      reaches_push (s := s) (s' := rstoreAppend s ra j) rfl rfl
        (fun b g hb _ => rstoreVal_reaches hs hb) h
  · exact fun hs rb hrb =>
      reaches_mono (s₀ := s) (s := rstoreAppend s ra j) rfl hext (hs rb hrb)
  · intro hs u m' hge hm'
    rw [hone u m' hge hm']
    exact hs ra hk
  · intro u m' hge hm'
    rw [hone u m' hge hm']
    exact hd

/-- The guarded step.  On a disowned allocation the environment does nothing at
    all, so the rely condition is trivially satisfied. -/
theorem rstore_post (s : Machine) (ra : RAddr) (j : Nat)
    (hk : ra ∈ s.rknow) : EnvPost s (rstoreStep s ra j) := by
  unfold rstoreStep
  split
  · exact EnvPost.refl s
  · rename_i hd
    exact rstore_append_post s ra j hk hd

/-! ### The specs

The side condition `ra ∈ s₀.rknow` is a *guard on the postcondition*, not a
precondition.  Stated as a precondition -- `⦃fun s => ⌜s = s₀ ∧ ra ∈ s₀.rknow⌝⦄`
-- `mvcgen` stops resolving the ghost from the conjunction and unifies `s₀` with
the caller's ghost instead, which leaves a goal saying the state after two
oracle bumps equals the state before them.  Guarding matches what `StorePost`
and `EnvPost` already do, and it keeps the precondition at `s = s₀` so the spec
fires everywhere. -/

/-- What a remote load guarantees.  `env` is the rely half; `read` is what §8
    needs -- that the message came from a timestamp the ordering bound allowed,
    which is the hook coherence is applied through. -/
structure RLoadPost (ra : RAddr) (s₀ : Machine) (r : Option Msg) (s : Machine) :
    Prop where
  env : ra ∈ s₀.rknow → EnvPost s₀ s
  mem : s.mem = s₀.mem
  read : ∀ m, r = some m → ∃ t, s₀.mem[t]? = some m ∧
           readable s₀.mem ra.addr t (rloadBound s₀ ra) = true
  /-- Unconditional, unlike `env`: a reader that is *not* holding `ra` still
      has not changed who owns what.  §9 needs this, because the ownership of
      the transferred object has to survive loads that the rely lemma says
      nothing about. -/
  disowned : s.rdisowned = s₀.rdisowned
  /-- **What the read absorbs into Remote's `vRd`** -- the message's view, and
      not its timestamp.

      `mload`'s mirror (`LoadPost.rd`) exposes `max r.rts r.view`, because for
      Local the timestamp is honest: Local's own writes are subject to promises,
      so array order is not a free ordering guarantee.  For Remote it is *not*
      honest -- Remote's stores append in program order (the "Remote does not
      promise" gap, §7), so ordering a remote read by the raw timestamp would
      lean on something the model supplies and the machine does not.

      This clause first existed to *hide* a timestamp `rloadStep` was absorbing
      anyway, which made the unsound route unavailable to proofs without making
      it false.  `rloadStep` no longer absorbs it, so the two now agree.  That
      change was the sound direction (a smaller `vRd` bounds fewer reads, so
      Remote may see strictly more), it altered exactly one executable outcome
      in the whole report, and the outcome it altered was the one §11.3 had
      recorded as a gap: with the timestamp gone, the reader's ordering has to
      come from the writer's `dmb ishst`, which is where it comes from in
      hardware, and dropping that fence is now a visible counterexample. -/
  rdView : ∀ m, r = some m → m.view ≤ s.rvs.vRd
  /-- Remote's read view only grows, so an earlier read's contribution survives
      a later one. -/
  rdMono : s₀.rvs.vRd ≤ s.rvs.vRd
  /-- **Remote declines only when there is nothing to read.**  The other clauses
      all constrain the `some` case; this one constrains the `none` case, and
      without it "the load returned nothing" is indistinguishable from "the
      model chose not to model this".

      §12 is what needs it.  A pointer chase that stops has either run off the
      end of the list or stalled, and only the first is a fact about the
      program; a traversal theorem that cannot tell them apart is satisfied by
      a reader that gives up immediately. -/
  declined : r = none → ∀ (t : Nat) (m : Msg), s₀.mem[t]? = some m →
               readable s₀.mem ra.addr t (rloadBound s₀ ra) = false
  /-- What the machine wrote down.  `rreads` has been the demos' window on
      Remote since §7, but no postcondition connected it to the value the load
      returned, so no *theorem* could talk about it.

      One clause rather than two: `Option.toList` is `[]` on the branch that
      read nothing, which is also the branch on which the state does not
      change at all. -/
  reads : s.rreads = s₀.rreads ++ (r.map Msg.val).toList

/-- Naming the `vRd` update so the two view clauses can be proved by rewriting
    rather than by hoping the projection reduces past `rloadStep`'s `let`. -/
theorem rloadStep_vRd (s : Machine) (ra : RAddr) (t : Ts) :
    (rloadStep s ra t).rvs.vRd
      = max s.rvs.vRd (s.mem[t]?.getD ⟨ra.addr, Val.undef, 0⟩).view :=
  rfl

@[spec]
theorem rload_spec (ra : RAddr) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    rload ra
    ⦃⇓ r s => ⌜RLoadPost ra s₀ r s⌝⦄ := by
  mvcgen [rload]
  case vc1.h_1 =>
    -- Nothing readable: Remote does not read, and nothing changes.
    subst_vars
    rename_i s hf
    refine ⟨fun _ => EnvPost.refl _, rfl, fun _ h => by simp at h, rfl,
      fun _ h => by simp at h, Nat.le_refl _, ?_, by simp⟩
    -- The filter came back empty, so nothing in range was readable -- and
    -- nothing out of range is a message at all.
    intro _ t m hm
    rcases Nat.lt_or_ge t s.mem.size with hlt | hge
    · simpa using List.filter_eq_nil_iff.mp hf t (List.mem_range.mpr hlt)
    · rw [Array.getElem?_eq_none hge] at hm; simp at hm
  case vc2.h_2 =>
    subst_vars
    simp +zetaDelta only []
    -- Six names: the state, the filter's cons pattern and its equation, the
    -- let-bound timestamp, and the let-bound result pair.
    rename_i s c cs hf _ _
    have hr := readable_of_pick _ _ _ c cs hf (s.oracle.headD 0)
    obtain ⟨mr, hmr, _⟩ := msg_of_readable hr
    refine ⟨fun hk => rload_post _ _ _ hr hk, rfl,
      fun m hm => ⟨pick (s.oracle.headD 0) c cs, hm, hr⟩, rfl, ?_, ?_, ?_, ?_⟩
    · intro m hm
      rw [rloadStep_vRd, hm]
      simp only [Option.getD_some]
      exact Nat.le_max_right _ _
    · rw [rloadStep_vRd]
      exact Nat.le_max_left _ _
    · -- Vacuous: what was picked is readable, so it is a message, so the load
      -- returned one.
      intro hnone
      rw [hmr] at hnone; simp at hnone
    · show s.rreads ++ [(s.mem[pick (s.oracle.headD 0) c cs]?.getD
              ⟨ra.addr, Val.undef, 0⟩).val] = _
      rw [hmr]; simp

/-! ### Remote's fence

Remote has had views since §7 (`rvs`) but no way to order them, because no
theorem needed one: §7 is about reachability, §8 orders Remote's reader with an
*address dependency*, and §9–§11.2 order Remote by forbidding it outright.  A
seqlock reader has nothing to depend on -- the validating read is of a different
location than the data read, and its address was known all along -- so it needs
the real thing.

Exactly `mfence`, on `rvs` instead of `vs`.  Nothing here is new physics; it is
the same rule applied to the other agent. -/

def rfence (f : Fence) : M Unit :=
  modify fun s =>
    { s with rvs := match f with
        | .ld => { s.rvs with vPreBase := max s.rvs.vPreBase s.rvs.vRd }
        | .st => { s.rvs with vRelSt := max s.rvs.vRelSt s.rvs.vWr }
        | .sy => { s.rvs with
                     vPreBase := max s.rvs.vPreBase (max s.rvs.vRd s.rvs.vWr)
                     vRelSt := max s.rvs.vRelSt (max s.rvs.vRd s.rvs.vWr) } }

structure RFencePost (f : Fence) (s₀ s : Machine) : Prop where
  mem : s.mem = s₀.mem
  /-- Remote fencing itself is not an event for Local, so every local view --
      and `stuck`, and the promise list -- is untouched.  This is what lets a
      remote fence be dropped into a program between two local operations at no
      proof cost, the same way `EnvPost.vs` does for a remote store. -/
  vs : s.vs = s₀.vs
  stuck : s.stuck = s₀.stuck
  promises : s.promises = s₀.promises
  disowned : s.rdisowned = s₀.rdisowned
  /-- The clause the seqlock reader needs: `dmb ishld` bounds every later
      remote load by everything read so far. -/
  pre : f ≠ .st → s₀.rvs.vRd ≤ s.rvs.vPreBase

@[spec]
theorem rfence_spec (f : Fence) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄ rfence f ⦃⇓ _ s => ⌜RFencePost f s₀ s⌝⦄ := by
  mvcgen [rfence]
  subst_vars
  simp +zetaDelta only []
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro hf
  cases f
  · exact Nat.le_max_right _ _
  · exact absurd rfl hf
  · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

@[spec]
theorem rstore_spec (ra : RAddr) (j : Nat) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    rstore ra j
    ⦃⇓ _ s => ⌜ra ∈ s₀.rknow → EnvPost s₀ s⌝⦄ := by
  mvcgen [rstore]
  subst_vars
  simp +zetaDelta only []
  exact fun hk => rstore_post _ _ _ hk

/-- Resolving a choice is not an observable step.  `renv` consumes two or three
    oracle entries before it does anything, and this is what lets the two
    operation specs compose across them. -/
theorem EnvPost.ofOracle (s : Machine) (o : List Nat) :
    EnvPost s { s with oracle := o } where
  ext := ⟨Nat.le_refl _, fun _ _ => rfl⟩
  vs := rfl
  stuck := rfl
  promises := rfl
  roots := rfl
  priv := fun _ _ h =>
    reaches_of_eq (s := s) (s' := { s with oracle := o }) rfl rfl h
  sound := fun hs rb hrb =>
    reaches_of_eq (s := { s with oracle := o }) (s' := s) rfl rfl (hs rb hrb)
  wrote := fun _ t m hge hm => by
    rw [show ({ s with oracle := o } : Machine).mem = s.mem from rfl,
      Array.getElem?_eq_none hge] at hm
    simp at hm
  disowned := rfl
  frozen := fun t m hge hm => by
    rw [show ({ s with oracle := o } : Machine).mem = s.mem from rfl,
      Array.getElem?_eq_none hge] at hm
    simp at hm
  sizes := rfl

/-- The rely lemma the program uses.  No precondition beyond the ghost: an
    environment step is always allowed to happen.

    All four branches reduce to the same two facts -- resolving choices is
    invisible (`ofOracle`), and the address Remote acts on is one it holds
    (`pick_mem`, against the equation the `match` on `rknow` produced). -/
@[spec]
theorem renv_spec (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄ renv ⦃⇓ _ s => ⌜EnvPost s₀ s⌝⦄ := by
  mvcgen [renv, demonic, demonicIdx]
  case vc1.h_1 =>
    -- Remote holds nothing, so it did nothing.
    subst_vars
    exact EnvPost.refl _
  case vc2.h_2.h_1 =>
    -- Stutter: two oracle entries consumed and nothing else.
    subst_vars
    simp +zetaDelta only []
    exact EnvPost.ofOracle _ _
  case vc3.h_2.h_2.post.success =>
    -- Remote read.  `rload` now returns the message it read, so its spec is a
    -- structure rather than a bare implication: the rely half is `.env`.
    -- Ten names: the state, the `rknow` cons pattern and its equation, the two
    -- let-bound choice pairs, the branch equation, the result, the final state,
    -- and the load's own postcondition.
    rename_i _ c cs hrk _ _ _ _ _ h
    subst_vars
    exact EnvPost.trans (EnvPost.ofOracle _ _)
      (h.env (by rw [hrk]; exact pick_mem _ _ _))
  case vc4.h_2.h_3.post.success =>
    -- Remote wrote.  One more oracle entry (the value index), hence ten.
    rename_i hrk _ _ _ _ _ _ _ _ _
    subst_vars
    simp +zetaDelta only []
    intro h
    exact EnvPost.trans (EnvPost.ofOracle _ _) (h (by rw [hrk]; exact pick_mem _ _ _))

/-! ### The privacy theorem

Three operations, two of which the program does not control.  The interleaved
`renv`s cost one line each in the program and nothing in the proof: `mvcgen`
applies `renv_spec` without being asked, exactly as D5 wanted.

The conclusion is the *stability of unreachability*.  Stated positively --
`Reaches s l → Reaches s₀ l` -- because that is the form that composes; the
privacy reading is the contrapositive, and is the corollary below.

Note which hypothesis does the real work.  `v` not being a pointer is what
makes the store non-publishing: a program that stores a pointer to the private
object into a reachable location has published it, and should not be able to
prove this.  Remove that hypothesis and the proof fails at `reaches_push`,
which is the right place for it to fail. -/

theorem rknowSound_of_ext {s₀ s : Machine} (hr : s.roots = s₀.roots)
    (hk : s.rknow = s₀.rknow) (he : Extends s₀ s) (hs : RKnowSound s₀) :
    RKnowSound s :=
  fun rb hrb => reaches_mono hr he (hs rb (hk ▸ hrb))

/-- The whole argument, over the three postconditions and nothing else.  The
    two triples below are one line each. -/
theorem privacy_chain {s₀ s₁ s₂ s₃ : Machine} {p : Address} {v : Val}
    (h1 : EnvPost s₀ s₁) (h2 : StorePost p v [] false s₁ s₂) (h3 : EnvPost s₂ s₃)
    (hs0 : RKnowSound s₀) (hp0 : s₀.promises = []) (hv : ∀ b g, v ≠ Val.loc b g)
    {l : AllocLabel} (hl : Reaches s₃ l) : Reaches s₀ l := by
  -- The invariant has to be pushed forward before it can be used on the right.
  have hs1 := h1.sound hs0
  have hs2 := rknowSound_of_ext h2.roots h2.rknow h2.ext hs1
  obtain ⟨hmem, _⟩ := h2.append (h1.promises ▸ hp0)
  exact h1.priv hs0 l (reaches_push_nonptr h2.roots hmem hv (h3.priv hs2 l hl))

theorem private_stays_private (p : Address) (v : Val) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    (do renv; mstore p v; renv : M Unit)
    ⦃⇓ _ s => ⌜RKnowSound s₀ → s₀.promises = [] → (∀ b g, v ≠ Val.loc b g) →
              ∀ l, Reaches s l → Reaches s₀ l⌝⦄ := by
  mvcgen
  subst_vars
  rename_i h1 _ _ h2 _ _
  intro h3 hs0 hp0 hv _ hl
  exact privacy_chain h1 h2 h3 hs0 hp0 hv hl

/-- The contrapositive, which is the thing you actually want to say. -/
theorem private_unreachable (p : Address) (v : Val) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    (do renv; mstore p v; renv : M Unit)
    ⦃⇓ _ s => ⌜RKnowSound s₀ → s₀.promises = [] → (∀ b g, v ≠ Val.loc b g) →
              ¬ Reaches s₀ p.label → ¬ Reaches s p.label⌝⦄ := by
  mvcgen
  subst_vars
  rename_i h1 _ _ h2 _ _
  intro h3 hs0 hp0 hv hnr hl
  exact hnr (privacy_chain h1 h2 h3 hs0 hp0 hv hl)

/-! ### Is `renv` vacuous?

A rely lemma about an environment that can do nothing is true and useless, and
every theorem above would still hold.  So run it.

Two scenarios with the *same* secret address, differing only in whether a
pointer to it is reachable.  The negative one alone would prove nothing --
"Remote never touched the secret" is also what an inert environment reports.
The positive one is the control: when the pointer is published, Remote does
find it and does write to it. -/

def remoteScenario (published : Bool) : String :=
  let root : Address := ⟨0, 0⟩
  let secret : Address := ⟨1, 0⟩
  -- The root holds a pointer.  In the published case it points at the secret;
  -- otherwise at an unrelated cell.  Nothing else differs -- same oracle, same
  -- memory shape, same starting knowledge.
  let target : Address := if published then secret else ⟨2, 0⟩
  let s0 : Machine :=
    { mem := #[⟨root, Val.loc target 0, 0⟩, ⟨secret, Val.num 42, 0⟩],
      sizes := [1, 1, 1],
      roots := [root], rknow := [⟨root, 0⟩],
      -- Three steps, three entries each: address choice, action, operand.
      --   (0, load, ts 0)  read the root, learning `target`
      --   (1, store, j=0)  write a scalar to `target`
      --   (0, load, ts 0)  read the root again
      oracle := [0, 1, 0, 1, 2, 0, 0, 1, 0] }
  let (_, s) := (do renv; renv; renv : M Unit).run s0
  let touched := (List.range s.mem.size).any fun t =>
    decide (s0.mem.size ≤ t) &&
      (s.mem[t]?.elim false fun m => decide (m.loc = secret))
  s!"published={published}: reads={s.rreads.length}, knows={s.rknow.length}, " ++
  s!"mem {s0.mem.size}→{s.mem.size}, wrote-to-secret={touched}"

def remoteDemo : String :=
  "  " ++ remoteScenario false ++ "\n  " ++ remoteScenario true

/-! ## 8. Safe publication -- the experiment

§7 proved that Remote cannot touch what it cannot reach.  The other half of the
uninitialised-object theorem is about what happens *when you do publish*: the
reader must not see the object's pre-initialisation contents.

The mechanism is supposed to be the address dependency.  A pointer entering
`rknow` carries `max ra.view m.view`, so a dereference through it is bounded by
the view of the message the pointer came out of; a release (or a preceding
`dmb ishst`) makes that view cover the initialising write; coherence then hides
the stale value.  That chain has been prose since the start and
has never been run.

So run it before proving anything.  Two scenarios, identical but for the fence.
The prediction is that the unfenced one lets Remote read `undef` and the fenced
one does not.  If that is wrong, the theorem below is not worth attempting. -/

def publishVia (root data : Address) (v : Val) (fenced : Bool) : M Unit := do
  mstore data v
  if fenced then mfence .st else pure ()
  mstore root (Val.loc data 0)

/-- The RCU reader: load through `ra`, then dereference whatever pointer came
    out, and return what the dereference read.

    The chain goes through `rlearnedOf`, which is the same function `rloadStep`
    uses to extend `rknow`.  That is deliberate: the ordering the theorem relies
    on and the knowledge the privacy theorems rely on are then the same rule. -/
def rderefChain (ra : RAddr) : M (Option Msg) := do
  match ← rload ra with
  | none => pure none
  | some m =>
      match rlearnedOf ra m with
      | none => pure none
      | some rb => rload rb

def publicationScenario (fenced : Bool) : String :=
  let root : Address := ⟨0, 0⟩
  let data : Address := ⟨1, 0⟩
  let s0 : Machine :=
    { mem := #[⟨data, Val.undef, 0⟩, ⟨root, Val.num 0, 0⟩],
      sizes := [1, 1],
      roots := [root], rknow := [⟨root, 0⟩],
      -- store, store, then Remote: pick the *new* root write (1), then try the
      -- *stale* data write (0).  The oracle is doing its best to break us.
      oracle := [0, 0, 1, 0] }
  let (r, s) :=
    (do publishVia root data (Val.num 7) fenced
        rderefChain ⟨root, 0⟩ : M (Option Msg)).run s0
  let derefd := match r with | some m => repr m.val | none => "nothing"
  let sawUndef := s.rreads.any fun v => match v with | .undef => true | _ => false
  s!"fenced={fenced}: deref-read={derefd}, saw-undef={sawUndef}"

def publicationDemo : String :=
  "  " ++ publicationScenario false ++ "\n  " ++ publicationScenario true

/-! ### The pure content

The experiment says the mechanism is there.  Now say what it guarantees.

`readable_push_eq` was the coherence lemma for reading your *own* write; this
is its general form, and it is the only new fact about memory the theorem
needs.  Everything else is bookkeeping about which timestamp holds what. -/

theorem not_readable_of_later {mem : Memory} {a : Address} {t t' bound : Ts}
    {m' : Msg} (hlt : t < t') (hb : t' ≤ bound) (hm' : mem[t']? = some m')
    (hloc : m'.loc = a) : readable mem a t bound = false := by
  have hhid : hiddenFrom mem a t bound = true := by
    unfold hiddenFrom
    rw [List.any_eq_true]
    refine ⟨t', ?_, ?_⟩
    · simp only [List.mem_range]; exact Nat.lt_succ_of_le hb
    · simp [hlt, hm', hloc]
  unfold readable
  simp [hhid]

/-- Coherence in the form both halves of publication need: if nothing above `N`
    is at `a`, and `N` is at or below the bound, then `N` is the only readable
    timestamp.

    This is `readable_push_eq` with the `push` replaced by a hypothesis, which
    is what makes it reusable -- the hypothesis can be discharged by "I just
    wrote it and nothing else has" (§8) or by "I own it, so nobody may write
    it" (§9, via `EnvPost.frozen`).  Those are different arguments about
    different agents, and this is the one lemma they share. -/
theorem readable_eq_of_frozen {mem : Memory} {a : Address} {N bound t : Ts}
    {m : Msg} (hN : mem[N]? = some m) (hloc : m.loc = a) (hb : N ≤ bound)
    (hfroz : ∀ (t' : Ts) (m' : Msg), mem[t']? = some m' → m'.loc = a → t' ≤ N)
    (h : readable mem a t bound = true) : t = N := by
  obtain ⟨m', hm', hloc'⟩ := msg_of_readable h
  have hle : t ≤ N := hfroz t m' hm' hloc'
  rcases Nat.lt_or_ge t N with hlt | hge
  · rw [not_readable_of_later hlt hb hN hloc] at h; simp at h
  · exact Nat.le_antisymm hle hge

/-- The existence dual of `readable_eq_of_frozen`.

    `readable_eq_of_frozen` says the frozen top is the *only* candidate; this
    says it *is* a candidate.  Both halves became necessary when §10's load
    stopped getting stuck on an empty candidate list: "no timestamp is readable"
    is now a reportable outcome, so a caller who knows the location is frozen at
    a live message has to rule it out explicitly.

    Like `readable_push_top`, and unlike the uniqueness half, this needs no
    `N ≤ bound`.  The bound only restricts which timestamps may hide `N`, so
    lowering it can only help. -/
theorem readable_top_of_frozen {mem : Memory} {a : Address} {N bound : Ts}
    {m : Msg} (hN : mem[N]? = some m) (hloc : m.loc = a)
    (hfroz : ∀ (t' : Ts) (m' : Msg), mem[t']? = some m' → m'.loc = a → t' ≤ N) :
    readable mem a N bound = true := by
  have hhid : hiddenFrom mem a N bound = false := by
    unfold hiddenFrom
    rw [List.any_eq_false]
    intro t' _
    by_cases hlt : N < t'
    · -- Anything strictly above `N` is either absent or not at `a`, since
      -- `hfroz` would otherwise force it to be at or below `N`.
      cases hm' : mem[t']? with
      | none => simp
      | some m' =>
        have : ¬ (m'.loc = a) := fun hl => Nat.not_le_of_gt hlt (hfroz t' m' hm' hl)
        simp [this]
    · simp [hlt]
  unfold readable
  simp [hN, hloc, hhid]

/-- What publication leaves behind, beyond the value the reader got.

    §8 only needs `m₂.val = v`, but that conclusion is about *one* read and is
    unusable afterwards: it says nothing about where the value lives or whether
    anything else could be read later.  §9 needs all four of these, so
    `publication_chain` reports them rather than proving them twice.

    `top` is the interesting one.  It is a statement about `data` only -- the
    root write sits above `N`, and is excluded by being at a different address.
    That is what makes the transferred object, and not the publication slot,
    the thing whose contents are pinned. -/
structure PubTop (data : Address) (v : Val) (N : Ts) (s : Machine) (rb : RAddr) :
    Prop where
  /-- The dependency landed on the object. -/
  addr : rb.addr = data
  /-- ... carrying a view that covers the initialising write.  This is the
      fence's contribution, and it is what a *later* read can still appeal to. -/
  view : N ≤ rb.view
  /-- The initialising write is at `N`. -/
  msg : ∃ m, s.mem[N]? = some m ∧ m.loc = data ∧ m.val = v
  /-- ... and it is the last write to `data`.  Coherence then leaves `N` as the
      only readable timestamp for anyone whose bound reaches it. -/
  top : ∀ (t : Ts) (m : Msg), s.mem[t]? = some m → m.loc = data → t ≤ N

/-- Safe publication, as a statement about five states.

    Read the hypotheses as the protocol.  `hs1`/`hs2`/`hs3` are the writer:
    initialise, `dmb ishst`, publish the pointer.  `hl1`/`hrb` are the reader:
    load the root and take the address dependency.  Nothing here mentions the
    oracle, `Array.push`, or the monad.

    `hfresh` is the formal content of "this is *the* publishing store".  Without
    it the root could already hold a pointer published earlier and unsafely,
    whose view is small; Remote could learn that one instead and the
    dereference would be unordered.  It is not a technicality -- it is the
    reason a publication protocol has to own its root word.

    `h0` (no outstanding promise) keeps both stores appending, so the timestamps
    are determined.  Remote does not promise, so nothing else can appear in
    memory between the two loads.

    The conclusion deliberately stops *before* the dereference.  Phrasing it as
    "the reader's next load returns `v`" conflates two different facts -- what
    the publication established, and what one particular reader then did with
    it -- and only the first is reusable.  §9.1 uses this with a load several
    environment steps later, which the old phrasing could not express. -/
theorem publication_top
    {root data : Address} {v : Val} {s₀ s₁ s₂ s₃ s₄ : Machine}
    {ra rb : RAddr} {m₁ : Msg}
    (hne : root ≠ data) (hra : ra.addr = root)
    (h0 : s₀.promises = [])
    (hfresh : ∀ (t : Ts) (m : Msg), s₀.mem[t]? = some m → m.loc = root →
      ∀ b g, m.val ≠ Val.loc b g)
    (hs1 : StorePost data v [] false s₀ s₁)
    (hs2 : FencePost .st s₁ s₂)
    (hs3 : StorePost root (Val.loc data 0) [] false s₂ s₃)
    (hl1 : RLoadPost ra s₃ (some m₁) s₄)
    (hrb : rlearnedOf ra m₁ = some rb) :
    PubTop data v s₀.mem.size s₃ rb := by
  obtain ⟨hm1, _, hp1, hwr1⟩ := hs1.append h0
  have hp2 : s₂.promises = [] := by rw [hs2.promises, hp1]
  obtain ⟨hm3, _, _, _⟩ := hs3.append hp2
  -- The shape of memory after the writer is done: two new messages, in order.
  -- `set` is Mathlib; `obtain` against a trivial existential is the core-Lean
  -- way to get an opaque local plus its defining equation.
  obtain ⟨N, hN⟩ : ∃ N, N = s₀.mem.size := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Msg, D = ⟨data, v, mstoreView s₀ [] false⟩ := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Msg, R = ⟨root, Val.loc data 0, mstoreView s₂ [] false⟩ :=
    ⟨_, rfl⟩
  have hmem3 : s₃.mem = (s₀.mem.push D).push R := by
    rw [hD, hR, hm3, hs2.mem, hm1]
  have hdata : s₃.mem[N]? = some D := by
    rw [hmem3, hN]; simp [Array.getElem?_push]
  have hroot : s₃.mem[N + 1]? = some R := by
    rw [hmem3, hN, show s₀.mem.size + 1 = (s₀.mem.push D).size from by simp]
    exact Array.getElem?_push_size
  have hDloc : D.loc = data := by rw [hD]
  have hold : ∀ t, t < N → s₃.mem[t]? = s₀.mem[t]? := by
    intro t ht
    rw [hN] at ht
    rw [hmem3]
    have h1 : t ≠ s₀.mem.size := Nat.ne_of_lt ht
    have h2 : t ≠ s₀.mem.size + 1 := by omega
    simp [Array.getElem?_push, h1, h2]
  have hbig : ∀ t, N + 1 < t → s₃.mem[t]? = none := by
    intro t ht
    rw [hN] at ht
    rw [hmem3]
    exact Array.getElem?_eq_none (by simp only [Array.size_push]; omega)
  -- The published pointer's view covers the initialising write: this is the
  -- one place the fence is used, and removing it breaks exactly here.
  have hview : N ≤ R.view := by
    rw [hN, hR]
    exact Nat.le_trans (Nat.le_trans hwr1 (hs2.rel (by simp)))
      (mstoreView_ge_rel s₂ [] false)
  -- Step 1: the pointer Remote learned came out of *our* root write.
  obtain ⟨t₁, ht₁, hr₁⟩ := hl1.read m₁ rfl
  obtain ⟨_, ht₁', hloc1⟩ := msg_of_readable hr₁
  rw [ht₁] at ht₁'
  have hloc1 : m₁.loc = root := by rw [← hra]; exact Option.some.inj ht₁' ▸ hloc1
  have hm₁R : m₁ = R := by
    rcases Nat.lt_trichotomy t₁ N with hlt | heq | hgt
    · -- an old message at `root`, which `hfresh` says is not a pointer
      exfalso
      rw [hold t₁ hlt] at ht₁
      unfold rlearnedOf at hrb
      cases hv : m₁.val with
      | undef =>  rw [hv] at hrb; simp at hrb
      | null =>   rw [hv] at hrb; simp at hrb
      | num n =>  rw [hv] at hrb; simp at hrb
      | loc b g => exact hfresh t₁ m₁ ht₁ hloc1 b g hv
    · -- the initialising write itself, which is not at `root`
      exfalso
      rw [heq, hdata] at ht₁
      rw [← Option.some.inj ht₁, hDloc] at hloc1
      exact hne hloc1.symm
    · rcases Nat.lt_or_ge (N + 1) t₁ with hbg | hle
      · exfalso; rw [hbig t₁ hbg] at ht₁; simp at ht₁
      · have ht : t₁ = N + 1 := Nat.le_antisymm hle hgt
        rw [ht, hroot] at ht₁
        exact (Option.some.inj ht₁).symm
  -- Step 2: the dependency carries that view into the dereference's bound.
  have hrbeq : rb = ⟨data, max ra.view R.view⟩ := by
    have hlearn : rlearnedOf ra R = some ⟨data, max ra.view R.view⟩ := by
      unfold rlearnedOf; rw [hR]
    rw [hm₁R, hlearn] at hrb
    exact (Option.some.inj hrb).symm
  have hrbaddr : rb.addr = data := by rw [hrbeq]
  have hbound : N ≤ rloadBound s₄ rb := by
    have hrv : N ≤ rb.view := by
      rw [hrbeq]; exact Nat.le_trans hview (Nat.le_max_right _ _)
    refine Nat.le_trans hrv ?_
    unfold rloadBound
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  -- Everything §9 needs, assembled here because this is the only place the
  -- exact shape of memory after the writer is still in hand.
  have htop : PubTop data v N s₃ rb := by
    refine ⟨hrbaddr, ?_, ⟨D, hdata, hDloc, by rw [hD]⟩, ?_⟩
    · rw [hrbeq]; exact Nat.le_trans hview (Nat.le_max_right _ _)
    · intro t m hm hloc
      rcases Nat.lt_trichotomy t N with hlt | heq | hgt
      · exact Nat.le_of_lt hlt
      · exact Nat.le_of_eq heq
      · exfalso
        rcases Nat.lt_or_ge (N + 1) t with hbg | hle
        · rw [hbig t hbg] at hm; simp at hm
        · have ht : t = N + 1 := Nat.le_antisymm hle hgt
          rw [ht, hroot] at hm
          rw [← Option.some.inj hm, hR] at hloc
          exact hne hloc
  rw [hN] at htop
  exact htop

/-- What §8 originally proved, now a corollary: the dereference reads `v`.

    The whole of the old "step 3" -- a trichotomy on the timestamp the reader
    picked -- collapses into `readable_eq_of_frozen`, because `PubTop.top` is
    exactly the hypothesis that lemma wants.  That is the payoff of having
    stated what publication leaves behind rather than only what one reader
    saw. -/
theorem publication_chain
    {root data : Address} {v : Val} {s₀ s₁ s₂ s₃ s₄ s₅ : Machine}
    {ra rb : RAddr} {m₁ m₂ : Msg}
    (hne : root ≠ data) (hra : ra.addr = root)
    (h0 : s₀.promises = [])
    (hfresh : ∀ (t : Ts) (m : Msg), s₀.mem[t]? = some m → m.loc = root →
      ∀ b g, m.val ≠ Val.loc b g)
    (hs1 : StorePost data v [] false s₀ s₁)
    (hs2 : FencePost .st s₁ s₂)
    (hs3 : StorePost root (Val.loc data 0) [] false s₂ s₃)
    (hl1 : RLoadPost ra s₃ (some m₁) s₄)
    (hrb : rlearnedOf ra m₁ = some rb)
    (hl2 : RLoadPost rb s₄ (some m₂) s₅) :
    m₂.val = v := by
  have htop := publication_top hne hra h0 hfresh hs1 hs2 hs3 hl1 hrb
  obtain ⟨D, hD, hDloc, hDval⟩ := htop.msg
  obtain ⟨t₂, ht₂, hr₂⟩ := hl2.read m₂ rfl
  rw [hl1.mem] at ht₂ hr₂
  rw [htop.addr] at hr₂
  have hb : s₀.mem.size ≤ rloadBound s₄ rb := by
    refine Nat.le_trans htop.view ?_
    unfold rloadBound
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  rw [readable_eq_of_frozen hD hDloc hb htop.top hr₂, hD] at ht₂
  rw [← Option.some.inj ht₂]
  exact hDval

/-! ### The theorem

The writer publishes, the reader dereferences, and whatever comes back is the
initialised value.  `mvcgen` produces exactly three goals -- the first load
found nothing, the root held no pointer, or both loads succeeded -- and the
first two are vacuous because `rderefChain` returns `none`.

Two things are worth noticing about the case list.  The `if fenced` has already
been resolved (`isTrue`), so the fence costs no case split.  And the three
interleaved specs (`mstore_spec`, `mfence_spec`, `rload_spec`) fire without
being named: what reaches the proof is six `Machine`s and five hypotheses
relating them, which is precisely the input `publication_chain` wants.

`Val.undef` is not mentioned anywhere, and that is the point: the conclusion is
`m.val = v`, which *excludes* `undef` along with every other stale value.  A
theorem phrased as "does not read `undef`" would be satisfied by a model that
handed out a different stale value instead. -/

theorem published_read_is_initialised (root data : Address) (v : Val)
    (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    (do publishVia root data v true; rderefChain ⟨root, 0⟩ : M (Option Msg))
    ⦃⇓ r _s => ⌜s₀.promises = [] → root ≠ data →
      (∀ (t : Ts) (m : Msg), s₀.mem[t]? = some m → m.loc = root →
        ∀ b g, m.val ≠ Val.loc b g) →
      ∀ m, r = some m → m.val = v⌝⦄ := by
  mvcgen [publishVia, rderefChain]
  case vc1.post.success.isTrue.post.success.post.success.post.success.h_1 =>
    -- Nothing readable at the root, so the reader returns `none`.
    intro _ _ _ m hm; simp at hm
  case vc2.post.success.isTrue.post.success.post.success.post.success.h_2.h_1 =>
    -- The root held a scalar, so there was no dependency to follow.
    intro _ _ _ m hm; simp at hm
  case
    vc3.post.success.isTrue.post.success.post.success.post.success.h_2.h_2.post.success
    =>
    -- Four operations, so four postconditions.  This proof names no
    -- intermediate state at all: everything it needs is carried by the
    -- postconditions and the two `match` equations.
    name_hyps Post hst1 hfen hst2 hl1
    name_hyps Eq hs₀ _ hrb
    intro hl2 h0 hne hfresh m hm
    subst hs₀
    subst hm
    exact publication_chain hne rfl h0 hfresh hst1 hfen hst2 hl1 hrb hl2

/-! ## 9. Ownership transfer (prototype)

§7 and §8 cover transfer *out*: an object is private while being built, then
published, and the receiver sees it initialised.  What they do not cover is
transfer *in* -- acquiring an object from someone else and then being able to
rely on it.

The obstacle is not an oversight.  `rknow` is monotone (only `rloadStep`
extends it, and only by `++`), and `renv` may write to *anything* in `rknow`.
So the instant you publish, Remote holds a permanent licence to scribble, and a
receiver-side proof of "after I take this, it is stable" is **false in the
model**, not merely unproven.

Nor can it be fixed by making Remote forget.  Remote is a maximally-permissive
over-approximation of *all* other threads; over-approximating its knowledge is
the safe direction for the safety properties §7 proves, and shrinking `rknow`
would mean asserting that every other thread forgot -- unsayable with one
agent.

So: **forbid, do not forget.**  `rdisowned` is a set of allocation labels the
environment may not write.  `rknow` stays monotone, Remote may still read and
still reach, and the reachability arguments of §7 are untouched.  The single
enforcement point is the guard in `rstoreStep`, and the single new obligation
is `EnvPost.frozen`.

> [!WARNING]
> `rdisowned` is an **assumption**, not a mechanism.  No hardware feature
> corresponds to it.  It is the rely half of a rely-guarantee pair, and its
> soundness is an obligation on the *other* thread's proof, exactly as
> ownership is discharged in separation logic.  A theorem proved under
> `rdisowned` is conditional on a discipline this file cannot check.
>
> **§11.2 discharges it for one important case.**  When the object is guarded
> by a lock, `lock_protects_data` proves this section's conclusion with no
> `rdisowned` hypothesis at all: the environment is stopped because it cannot
> win the CAS.  What stays assumed is the lock-free half -- publication,
> transfer, and objects that are simply never shared again, which is what §9.1
> is about.

### The pure content

The coherence lemma this needs -- `readable_eq_of_frozen`, "if nothing above
`N` is at `a` then `N` is the only readable timestamp" -- turned out to be
§8's as well, and lives up there with the other facts about memory. -/

/-- The transfer event, such as it is: record that the environment has given up
    `l`.  It has no machine effect -- no fence, no message, not even an oracle
    bump -- because it is not a machine operation.  It is the point in the
    program at which the discipline starts, and naming it is the only way the
    assumption appears in the code rather than in a comment. -/
def assumeExclusive (l : AllocLabel) : M Unit :=
  modify fun s => { s with rdisowned := l :: s.rdisowned }

/-- Its spec is an equation rather than a `…Post` structure, because there is
    nothing to abstract: every field but one is literally unchanged, and a
    caller wants to rewrite rather than to project. -/
@[spec]
theorem assumeExclusive_spec (l : AllocLabel) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    assumeExclusive l
    ⦃⇓ _ s => ⌜s = { s₀ with rdisowned := l :: s₀.rdisowned }⌝⦄ := by
  mvcgen [assumeExclusive]
  subst_vars
  rfl

/-! ### The payoff

Unique ownership, stated operationally: **your loads become deterministic
again.**  That is what ownership buys, and it is exactly `load_reads_own_write`
from §6 -- the same statement, but now with two uncontrolled environment steps
interleaved between the store and the load.

Without `a.label ∈ s.rdisowned` this is false, and the scenario below exhibits
a run where it fails, under the same oracle.

Note which hypothesis is doing the work.  Nothing here is about reachability:
`a` may be reachable, published, and sitting in `rknow`.  `EnvPost.wrote` would
give nothing in that situation, which is precisely why `frozen` had to be a
separate clause rather than a corollary of the existing ones. -/

theorem owned_load_reads_own_write (a : Address) (v : Val) :
    ⦃fun s => ⌜s.promises = [] ∧ a.label ∈ s.rdisowned⌝⦄
    (do mstore a v; renv; renv; mload a : M TVal)
    ⦃⇓ r s => ⌜s.stuck = true ∨ r.val = v⌝⦄ := by
  mvcgen
  -- Three operations: the store, then the two uncontrolled environment steps.
  -- The precondition here is a plain conjunction rather than a ghost equation,
  -- so it is reached by its own type.
  name_hyps Post hstore henv1 henv2
  name_hyps Machine s₀ s₁ _ s₃ _
  name_hyps And hpre
  intro hload
  obtain ⟨hmem, hcoh, _, _⟩ := hstore.append hpre.1
  have henv : EnvPost s₁ s₃ := henv1.trans henv2
  have hsz : s₁.mem.size = s₀.mem.size + 1 := by rw [hmem]; simp
  have hown : a.label ∈ s₁.rdisowned := by rw [hstore.disowned]; exact hpre.2
  -- The write is still where the store left it.
  have hD : s₁.mem[s₀.mem.size]? = some ⟨a, v, mstoreView s₀ [] false⟩ := by
    rw [hmem]; simp
  have hD3 := henv.ext.msg hD
  -- Remote did not touch Local's views, so the bound is what §6 computed.
  have hb : s₀.mem.size ≤ loadBound s₃ a [] := by
    have hc : s₃.vs.coh a = s₀.mem.size := by rw [henv.vs, hcoh]
    rw [← hc]
    unfold loadBound
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  -- ... and appended nothing at `a`, which is the ownership clause.
  have hfroz : ∀ (t' : Ts) (m' : Msg), s₃.mem[t']? = some m' → m'.loc = a →
      t' ≤ s₀.mem.size := by
    intro t' m' hm' hlo
    rcases Nat.lt_or_ge t' s₁.mem.size with hlt | hge
    · -- below the store's own write, so below `N` by arithmetic alone
      rw [hsz] at hlt
      exact Nat.le_of_lt_succ hlt
    · exact absurd (hlo ▸ hown) (henv.frozen t' m' hge hm')
  rcases hload.read with hstuck | ⟨_, hnone⟩ | ⟨hmsg, hr⟩
  · exact Or.inl hstuck
  · -- "Nothing was readable" is refuted by the write we ourselves made: it is
    -- still there, and ownership says nothing hides it.
    exfalso
    have hcontra := hnone s₀.mem.size
    rw [readable_top_of_frozen hD3 rfl hfroz] at hcontra
    simp at hcontra
  · right
    have ht := readable_eq_of_frozen hD3 rfl hb hfroz hr
    rw [ht, hD3] at hmsg
    simp at hmsg
    exact hmsg.1.symm

/-! ### The control

Every "the environment cannot disturb this" result is satisfied by an
environment that does nothing, and `rstoreStep`'s guard is exactly the kind of
change that could silently disable the whole environment.  So run the same
program both ways under the same oracle.

The oracle is adversarial on both counts: each `renv` is steered into its
*store* branch, and the final load is steered to the *last* readable
timestamp -- which is Remote's write when there is one. -/

def ownershipScenario (owned : Bool) : String :=
  let a : Address := ⟨1, 0⟩
  let s0 : Machine :=
    { mem := #[⟨a, Val.num 0, 0⟩],
      sizes := [1, 1],
      roots := [a], rknow := [⟨a, 0⟩],
      rdisowned := if owned then [1] else [],
      -- store; then two env steps of (address, action=store, operand); then
      -- the load, taking the last candidate.
      oracle := [0, 0, 2, 0, 0, 2, 0, 2] }
  let (r, s) := (do mstore a (Val.num 7); renv; renv; mload a : M TVal).run s0
  s!"owned={owned}: read={repr r.val}, mem {s0.mem.size}→{s.mem.size}, " ++
  s!"stuck={s.stuck}"

def ownershipDemo : String :=
  "  " ++ ownershipScenario false ++ "\n  " ++ ownershipScenario true

/-! ## 9.1 The transfer theorem

§8 and §9 are each half of a handoff.  §8 says the receiver's *first* read of a
published object sees it initialised; §9 says an owner's loads are
deterministic.  Neither on its own is a transfer: the first says nothing about
what happens next, and the second assumes the object was already yours.

Composing them is a theorem about one program.  The sender declares the object
exclusively spoken for, initialises it, fences, and publishes a pointer.  The
receiver -- Remote, since Remote is everyone else -- loads the root, follows the
address dependency, reads the object, and then, after two *uncontrolled*
environment steps, reads it again through the same dependency.  The claim is
that the second read still returns the initialised value.

> [!NOTE]
> Which agent gets which guarantee is forced by D2, and is worth being precise
> about.  With the sender as Local, the receiver *is* Remote, so what this
> theorem grants the receiver is a stable object to read, not a licence to
> write it: a receiver's writes are indistinguishable from a third party's
> here.  The write side of a handoff is the role-swapped proof, with the
> receiver as Local, and that is `owned_load_reads_own_write`.  Two theorems,
> because there are two agents -- that is the shape of the model, not a gap
> in it.

What makes this more than §8 run twice is that nothing the *program* does
protects the second read.  The writer is finished; the dependency's view is a
fact about a message issued in the past.  What rules out a stale read and a
clobbered one is the conjunction of coherence (`PubTop.top`) and ownership
(`EnvPost.frozen`), and neither half suffices: without ownership Remote may
append a newer write, and without coherence the reader may take an older one. -/

/-- The second read, given what publication left behind.

    Note how little of the program survives into the hypotheses.  There is no
    root, no fence, no dependency and no first read here -- all of that has
    already been discharged into `PubTop`.  What is left is the two facts that
    keep a guarantee alive: nothing newer at `data` exists (`top`), and nothing
    newer can appear (`frozen`, via `hown`). -/
theorem transfer_chain {data : Address} {v : Val} {N : Ts}
    {sP sR s' s'' : Machine} {rb : RAddr} {m : Msg}
    (htop : PubTop data v N sP rb)
    (hmem : sR.mem = sP.mem)
    (hown : data.label ∈ sR.rdisowned)
    (henv : EnvPost sR s')
    (hl : RLoadPost rb s' (some m) s'') :
    m.val = v := by
  obtain ⟨D, hD, hDloc, hDval⟩ := htop.msg
  have hD' : s'.mem[N]? = some D := henv.ext.msg (by rw [hmem]; exact hD)
  -- The dependency's view is still a lower bound on the reader's bound: views
  -- are carried by the pointer, so time passing does not erode them.
  have hb : N ≤ rloadBound s' rb := by
    refine Nat.le_trans htop.view ?_
    unfold rloadBound
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  -- Below the handoff point, coherence; above it, ownership.
  have hfroz : ∀ (t' : Ts) (m' : Msg), s'.mem[t']? = some m' → m'.loc = data →
      t' ≤ N := by
    intro t' m' hm' hlo
    rcases Nat.lt_or_ge t' sR.mem.size with hlt | hge
    · rw [henv.ext.2 t' hlt, hmem] at hm'
      exact htop.top t' m' hm' hlo
    · exact absurd (hlo ▸ hown) (henv.frozen t' m' hge hm')
  obtain ⟨t, ht, hr⟩ := hl.read m rfl
  rw [htop.addr] at hr
  rw [readable_eq_of_frozen hD' hDloc hb hfroz hr, hD'] at ht
  rw [← Option.some.inj ht]
  exact hDval

/-- The handoff.  `assumeExclusive` comes first because an object is owned from
    birth: the sender does not acquire exclusivity, it declares that nothing
    else ever had it.  What changes at the publishing store is only who can
    *see* it.

    After the publish the sender performs no further store, which is the other
    half of the discipline and the half the model checks for free -- it is
    visible in the program text. -/
def transferVia (root data : Address) (v : Val) (owned : Bool) : M (Option Msg) := do
  if owned then assumeExclusive data.label else pure ()
  publishVia root data v true
  match ← rload ⟨root, 0⟩ with
  | none => pure none
  | some m₁ =>
      match rlearnedOf ⟨root, 0⟩ m₁ with
      | none => pure none
      | some rb => do
          let _ ← rload rb        -- the acquiring read: §8 covers this one
          renv                    -- ... and now anything at all happens
          renv
          rload rb                -- the receiver reads again

theorem transferred_read_is_stable (root data : Address) (v : Val)
    (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    transferVia root data v true
    ⦃⇓ r _s => ⌜s₀.promises = [] → root ≠ data →
      (∀ (t : Ts) (m : Msg), s₀.mem[t]? = some m → m.loc = root →
        ∀ b g, m.val ≠ Val.loc b g) →
      ∀ m, r = some m → m.val = v⌝⦄ := by
  mvcgen [transferVia, publishVia]
  -- The two vacuous branches: no pointer at the root, or none readable there.
  · intro _ _ _ m hm; simp at hm
  · intro _ _ _ m hm; simp at hm
  · -- Seven operations, so seven postconditions; the names below line up with
    -- the `do`-block above, not with the thirty-five binders `mvcgen` emits.
    name_hyps Post hst1 hfen hst2 hl1 hl2 henv1 henv2
    name_hyps Machine sI ..
    name_hyps Eq hsI hsX _ hrb
    intro hl3 h0 hne hfresh m hm
    subst hsI
    subst hsX
    subst hm
    -- Everything the publication established, in one object.  `s₀` has to be
    -- pinned: the writer starts from the post-`assumeExclusive` state, which
    -- differs from `s₀` only definitionally, and left to itself unification
    -- picks the wrong one off `h0`.
    have htop := publication_top
      (s₀ := { sI with rdisowned := data.label :: sI.rdisowned })
      hne rfl h0 hfresh hst1 hfen hst2 hl1 hrb
    -- Ownership survives the writer and both of the reader's loads.  This is
    -- the chain `RLoadPost.disowned` and `FencePost.disowned` were added for;
    -- without them it stops at the first load, because the rely lemma only
    -- speaks about addresses Remote is known to hold.
    exact transfer_chain htop (by rw [hl2.mem, hl1.mem])
      (by rw [hl2.disowned, hl1.disowned, hst2.disowned, hfen.disowned,
            hst1.disowned]
          exact List.mem_cons_self)
      (henv1.trans henv2) hl3

/-! ### The control

The theorem is an implication with `owned = true` baked in, so it is satisfied
by a model in which ownership is what stops the environment *and* by one in
which the environment never does anything.  The two runs below are the same
program, the same memory and the same oracle, differing only in the flag the
theorem fixes.

The oracle is adversarial throughout: it steers the root load to the *new*
pointer, and both environment steps into a store to the transferred object --
which is reachable, in `rknow`, and therefore fair game for everything except
the ownership guard. -/

def transferScenario (owned : Bool) : String :=
  let root : Address := ⟨0, 0⟩
  let data : Address := ⟨1, 0⟩
  let s0 : Machine :=
    { mem := #[⟨data, Val.undef, 0⟩, ⟨root, Val.num 0, 0⟩],
      sizes := [1, 1],
      roots := [root], rknow := [⟨root, 0⟩],
      --   0      mstore data 7
      --   0      mstore root (loc data)
      --   1      rload root      -- take the *new* root write
      --   0      rload data      -- the acquiring read
      --   1,2,0  renv            -- address = data, action = store, value = 0
      --   1,2,0  renv            -- and again
      --   5      rload data      -- take the *last* readable timestamp
      oracle := [0, 0, 1, 0, 1, 2, 0, 1, 2, 0, 5] }
  let (r, s) := (transferVia root data (Val.num 7) owned).run s0
  let got := match r with | some m => repr m.val | none => "nothing"
  s!"owned={owned}: second-read={got}, mem {s0.mem.size}→{s.mem.size}"

def transferDemo : String :=
  "  " ++ transferScenario false ++ "\n  " ++ transferScenario true


/-! ## 10. Allocation, and the first program with a loop

Everything above is straight-line: three to six operations over a hand-built
`Machine`, with every address written down in advance.  That is enough to state
the memory-model results and it is how they stayed readable, but it is not a
program, and the development it is meant to succeed -- `Heap`/`malloc`/`copy`
over `HeapM` -- is made of loops over allocations.

This section closes that gap with the smallest thing that actually exercises
it: allocate a buffer, copy into it with a `for` loop, and prove the buffer
stays private *while the environment runs between every pair of iterations*.

Three pieces had to exist first.

**Allocation is a `sizes` list, and the label is its length.**  No separate
counter, so "fresh" and "unallocated" are the same condition by construction
rather than by an invariant that could drift.

**`undef` is what an allocated-but-unwritten cell holds** (D1).  §10's `mload`
no longer gets stuck when no timestamp is readable: inside an allocation it
returns `Val.undef` with no timestamp and no message, and only a load from
outside every allocation is stuck.  That is the difference between "reading
uninitialised memory is undefined behaviour" and "reading unallocated memory
is", and it is the reason the loop below can copy out of a buffer nobody has
written.  It cost two lemmas -- `readable_push_top` and `readable_top_of_frozen`
-- because "nothing is readable" became a *reportable outcome* rather than a
contradiction, so every caller that knows better now has to say so.

**Labels cannot be forged** is a property of the state, not an axiom.  The user
asked for it as an assumption; it turns out not to need to be one.  `Reaches`
only ever produces a label that is already in `roots` or already stored in a
message, so if every such label is below `sizes.length` -- which is
`LabelsBelow`, and which every operation preserves -- then the *next* label is
unreachable, full stop.  `reaches_lt` is a two-line `cases`. -/

/-- Allocate `n` cells.  The returned label is `sizes.length`, and appending to
    `sizes` is what makes it no longer fresh.

    No memory is written.  The cells hold `undef` not because anything says so
    but because nothing has written them, and `mload` reports exactly that. -/
def malloc (n : Nat) : M Address :=
  modifyGet fun s => (⟨s.sizes.length, 0⟩, { s with sizes := s.sizes ++ [n] })

/-- Like `assumeExclusive_spec`, an equation rather than a `…Post` structure:
    eleven of twelve fields are literally unchanged and a caller wants to
    rewrite, not project. -/
@[spec]
theorem malloc_spec (n : Nat) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    malloc n
    ⦃⇓ r s => ⌜r = ⟨s₀.sizes.length, 0⟩ ∧
              s = { s₀ with sizes := s₀.sizes ++ [n] }⌝⦄ := by
  mvcgen [malloc]
  subst_vars
  exact ⟨rfl, rfl⟩

/-- Every label anyone could name is already allocated.

    Two clauses because `Reaches` has two constructors, and that is the whole
    design: this is exactly strong enough to make `reaches_lt` a `cases`, and
    no stronger. -/
def LabelsBelow (s : Machine) : Prop :=
  (∀ a ∈ s.roots, a.label < s.sizes.length) ∧
  (∀ (t : Ts) (m : Msg) (b : Address) (g : Nat), s.mem[t]? = some m → m.val = Val.loc b g →
     b.label < s.sizes.length)

/-- Reachability cannot outrun allocation.  Not an induction: both constructors
    conclude directly from a clause of `LabelsBelow`, because reachability
    bottoms out either in a root or in a pointer someone stored. -/
theorem reaches_lt {s : Machine} (h : LabelsBelow s) {l : AllocLabel}
    (hr : Reaches s l) : l < s.sizes.length := by
  cases hr with
  | root ha => exact h.1 _ ha
  | ptr hm _ hv => exact h.2 _ _ _ _ hm hv

/-- The formal content of "allocation labels cannot be forged": the next label
    is unreachable, and that is a theorem rather than an assumption. -/
theorem fresh_unreachable {s : Machine} (h : LabelsBelow s) :
    ¬ Reaches s s.sizes.length :=
  fun hr => Nat.lt_irrefl _ (reaches_lt h hr)

/-- Copy `n` cells, with the environment running between every pair of
    iterations.

    The `renv` in the body is the point.  D5 claims interference is free
    because `renv_spec` is an `@[spec]` lemma that `mvcgen` applies wherever it
    appears; that claim had only ever been tested on straight-line code, where
    the interleaving is written out by hand.  Here `mvcgen` meets it inside a
    loop body it generated itself. -/
def copy (src dst : Address) (n : Nat) : M Unit := do
  for i in [:n] do
    let v ← mload ⟨src.label, src.offset + i⟩
    mstore ⟨dst.label, dst.offset + i⟩ v.val
    renv

/-- A freshly allocated buffer stays private for the whole of a copy into it,
    through `n` uncontrolled environment steps.

    The precondition is a plain predicate rather than the `s = s₀` ghost used
    by the `@[spec]` lemmas.  That is not a style choice: the loop invariant has
    to *see* `LabelsBelow`, and a hypothesis parked in the postcondition as a
    guard is not in scope when `mvcgen` asks for the invariant.  Top-level
    theorems can afford it -- nothing unifies against them.

    Two things are worth noticing about what is *not* assumed.

    There is no "the source holds scalars" hypothesis, so the buffer may be
    filled with pointers.  `reaches_push`'s obligation on a stored pointer is
    conditional on the *target* being reachable, and the target is the private
    buffer, so the obligation is vacuous.  Copying a pointer into a place nobody
    can find does not publish it.

    And there is no hypothesis putting `src` in bounds.  The *destination* side
    needs none: `dst` comes from `malloc n` and the loop writes `dst[0..n-1]`,
    so every store is inside its allocation by construction, which is what
    `mstore`'s `allocated` check wants.  The source is unconstrained, so a copy
    may read off the end of `src` and set `stuck`.  That is deliberate.  Privacy
    is a statement about reachability, and `stuck` touches neither `roots` nor
    `mem`; a program that has wandered out of bounds has done something wrong,
    but it has not thereby published the buffer.  Keeping the two separate is
    what lets this theorem say something about a program the bounds discipline
    would reject. -/
theorem copy_stays_private (src : Address) (n : Nat) :
    ⦃fun s => ⌜LabelsBelow s ∧ RKnowSound s ∧ s.promises = []⌝⦄
    (do let dst ← malloc n; copy src dst n; pure dst)
    ⦃⇓ dst s => ⌜¬ Reaches s dst.label⌝⦄ := by
  mvcgen [copy]
  case inv1 =>
    rename_i sI hpre dst sM hM
    exact ⇓ ⟨_, _⟩ s => ⌜RKnowSound s ∧ s.promises = [] ∧ ¬ Reaches s dst.label⌝
  -- One iteration: load, store into the buffer, and an environment step.
  · rename_i s₀ hpre dst sM hM pref cur suff hsplit b s1 hinv v s2 hload u1 s3
      hstore u2 s4 henv
    obtain ⟨hsound1, hprom1, hun1⟩ := hinv
    -- The load moves nothing at all.
    have hext12 : Extends s1 s2 :=
      ⟨Nat.le_of_eq (by rw [hload.mem]), fun t _ => by rw [hload.mem]⟩
    have hsound2 : RKnowSound s2 :=
      rknowSound_of_ext hload.roots hload.rknow hext12 hsound1
    have hprom2 : s2.promises = [] := by rw [hload.promises]; exact hprom1
    have hun2 : ¬ Reaches s2 dst.label := fun hr =>
      hun1 (reaches_of_eq hload.roots hload.mem hr)
    -- The store appends into the buffer.  The obligation `reaches_push` would
    -- impose on the stored value is discharged by `hun2` alone: it is
    -- conditional on the target being reachable, and it is not.
    obtain ⟨hmem3, _, hprom3, _⟩ := hstore.append hprom2
    have hun3 : ¬ Reaches s3 dst.label := fun hr =>
      hun2 (reaches_push hstore.roots hmem3 (fun b _ _ hb => absurd hb hun2) hr)
    have hsound3 : RKnowSound s3 :=
      rknowSound_of_ext hstore.roots hstore.rknow hstore.ext hsound2
    -- ... and the environment step is `EnvPost.priv`, exactly as in §7.
    exact ⟨henv.sound hsound3, by rw [henv.promises]; exact hprom3,
           fun hr => hun3 (henv.priv hsound3 _ hr)⟩
  -- Entry.  This is the one place freshness is used.
  · rename_i s₀ hpre dst sM hM
    obtain ⟨hLB, hsound, hprom⟩ := hpre
    obtain ⟨hdst, hsM⟩ := hM
    subst hdst
    -- `malloc` touches `sizes` and nothing else, so reachability is literally
    -- the same relation before and after.  Projected rather than substituted:
    -- the implicit machine arguments below have to be pinned, and a record
    -- literal is not something unification will orient for you.
    have hroots : sM.roots = s₀.roots := by rw [hsM]
    have hmem : sM.mem = s₀.mem := by rw [hsM]
    have hknow : sM.rknow = s₀.rknow := by rw [hsM]
    have hprm : sM.promises = s₀.promises := by rw [hsM]
    refine ⟨fun ra hra => reaches_of_eq (s' := s₀) (s := sM) hroots.symm hmem.symm
              (hsound ra (hknow ▸ hra)),
            by rw [hprm]; exact hprom, ?_⟩
    intro hr
    exact Nat.lt_irrefl _
      (reaches_lt hLB (reaches_of_eq (s' := sM) (s := s₀) hroots hmem hr))
  -- Exit: the invariant is the conclusion.
  · rename_i _ _ _ _ _ _ _ hinv
    exact hinv.2.2


/-! ### What the copy actually copies

`copy_stays_private` is a safety property and says nothing about the data.  The
obvious thing to want next is `dst[i] = src[i]`, and under interference that is
not a theorem: Remote may write `src` between two iterations, and then the
destination holds a mixture of values that were all genuinely there at some
point and never all there at once.  Torn reads are what a concurrent memcpy
does.

So the statement splits in two, and the split is the interesting part.

**The weak half is unconditional.**  Every cell of the destination holds either
`undef` or a value that genuinely appeared at the corresponding source cell.
That is the strongest thing true of *every* run, and it needs no hypothesis
about the environment at all.

**The strong half is the weak half plus "the source did not change".**  It is a
ten-line consequence, not a second induction -- which is the point.  All the
memory-model content is in the weak half; the strong half is arithmetic on its
conclusion.  Stating it this way also keeps the interference assumption where a
reader can see it, instead of burying it in a precondition: §9's ownership and
§11.2's lock are the two ways to *buy* the antecedent, and both are proved.

The one subtlety is the `undef` case, and it is why this section could not have
been written before `unwritten_of_no_readable`.  When the load returns `undef`
it has told us something -- the cell was unwritten -- but "unwritten" is a fact
about the state *at the time of the read*, and the postcondition can only talk
about the end.  Remote may write that cell afterwards, so the fact does not
survive as stated.  What does survive is its shadow in the *initial* memory:
memory only grows, so a cell that was unwritten then was unwritten at the start
too.  Hence `CopiedFrom` mentions two memories rather than one, and both of its
disjuncts are monotone. -/

/-- A readable index is in range.  Hoisted here from §11.1, where it is used
    again by the exclusion argument; this block is its first user. -/
theorem lt_size_of_getElem? {mem : Memory} {t : Ts} {m : Msg} (h : mem[t]? = some m) :
    t < mem.size := by
  rcases Nat.lt_or_ge t mem.size with hl | hg
  · exact hl
  · rw [Array.getElem?_eq_none hg] at h; simp at h

/-- `mem` contains everything `mem₀` did, at the same timestamps.  Memory is
    append-only, so every step of every agent establishes this. -/
def MemPrefix (mem₀ mem : Memory) : Prop :=
  ∀ (t : Nat) (m : Msg), mem₀[t]? = some m → mem[t]? = some m

theorem MemPrefix.refl (mem : Memory) : MemPrefix mem mem := fun _ _ h => h

theorem MemPrefix.trans {a b c : Memory} (h₁ : MemPrefix a b) (h₂ : MemPrefix b c) :
    MemPrefix a c := fun t m h => h₂ t m (h₁ t m h)

theorem memPrefix_push (mem : Memory) (msg : Msg) : MemPrefix mem (mem.push msg) := by
  intro t m h
  have hlt := lt_size_of_getElem? h
  rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]
  exact h

theorem memPrefix_of_ext {s s' : Machine} (h : Extends s s') :
    MemPrefix s.mem s'.mem := by
  intro t m hm
  rw [h.2 t (lt_size_of_getElem? hm)]
  exact hm

/-- What a single copied cell is allowed to hold.

    Two disjuncts, and the asymmetry between them is deliberate.  The first is
    about the *current* memory: the value really is one that was written to `a`,
    and since memory is append-only that stays true.  The second is about the
    *initial* memory: the load found nothing, so nothing had been written to `a`
    yet, so nothing had been written to `a` at the start either.  Phrasing the
    second one about `mem₀` is what makes it survive an environment step that
    writes `a` after the read. -/
def CopiedFrom (mem₀ mem : Memory) (a : Address) (v : Val) : Prop :=
  (∃ (t : Nat) (m : Msg), mem[t]? = some m ∧ m.loc = a ∧ m.val = v)
  ∨ (v = Val.undef ∧ ∀ (t : Nat) (m : Msg), mem₀[t]? = some m → m.loc ≠ a)

theorem CopiedFrom.mono {mem₀ mem mem' : Memory} {a : Address} {v : Val}
    (hp : MemPrefix mem mem') (h : CopiedFrom mem₀ mem a v) :
    CopiedFrom mem₀ mem' a v := by
  rcases h with ⟨t, m, hm, hl, hv⟩ | h
  · exact Or.inl ⟨t, m, hp t m hm, hl, hv⟩
  · exact Or.inr h

/-- Every message sits in an allocation that exists.

    Needed at exactly one point -- to know the fresh buffer starts empty -- and
    never re-established, so it is a precondition rather than an invariant.
    `LabelsBelow` does not imply it: that constrains the labels a message's
    *value* mentions, which is what reachability needs, and says nothing about
    where the message *is*.  The two are genuinely different, and §10's
    `allocated` check is the rule that keeps this one true. -/
def MsgLabelsBelow (s : Machine) : Prop :=
  ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label < s.sizes.length

/-- The destination holds only copied data: every message in the buffer is at
    one of its offsets and carries a value the source supplied.

    The `s.stuck = true` escape is per-message rather than global because that
    is the form a loop invariant can carry: an iteration that gives up hands the
    excuse to every later one, via `LoadPost.stuck`. -/
def CopyAgrees (mem₀ : Memory) (src dst : Address) (s : Machine) : Prop :=
  ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label = dst.label →
    ∃ i, m.loc = (⟨dst.label, dst.offset + i⟩ : Address) ∧
         (s.stuck = true ∨
          CopiedFrom mem₀ s.mem ⟨src.label, src.offset + i⟩ m.val)

/-- **The weak half.**  Whatever the environment does, the destination holds
    only values the source really had.

    No hypothesis constrains Remote.  It may write `src` on every iteration, and
    the buffer will hold a torn mixture -- but every word of that mixture was at
    the address it came from when it was read. -/
theorem copy_copies_something (src : Address) (n : Nat) (mem₀ : Memory) :
    ⦃fun s => ⌜LabelsBelow s ∧ MsgLabelsBelow s ∧ RKnowSound s ∧ s.promises = [] ∧
               s.mem = mem₀⌝⦄
    (do let dst ← malloc n; copy src dst n; pure dst)
    ⦃⇓ dst s => ⌜CopyAgrees mem₀ src dst s⌝⦄ := by
  mvcgen [copy]
  case inv1 =>
    rename_i sI hpre dst sM hM
    exact ⇓ ⟨_, _⟩ s => ⌜RKnowSound s ∧ s.promises = [] ∧
      ¬ Reaches s dst.label ∧ MemPrefix mem₀ s.mem ∧ CopyAgrees mem₀ src dst s⌝
  -- One iteration: load, store into the buffer, and an environment step.
  · rename_i s₀ hpre dst sM hM pref cur suff hsplit b s1 hinv v s2 hload u1 s3
      hstore u2 s4 henv
    obtain ⟨hsound1, hprom1, hun1, hp01, hdst1⟩ := hinv
    -- Privacy, exactly as in `copy_stays_private`.
    have hext12 : Extends s1 s2 :=
      ⟨Nat.le_of_eq (by rw [hload.mem]), fun t _ => by rw [hload.mem]⟩
    have hsound2 : RKnowSound s2 :=
      rknowSound_of_ext hload.roots hload.rknow hext12 hsound1
    have hprom2 : s2.promises = [] := by rw [hload.promises]; exact hprom1
    have hun2 : ¬ Reaches s2 dst.label := fun hr =>
      hun1 (reaches_of_eq hload.roots hload.mem hr)
    have hp12 : MemPrefix s1.mem s2.mem := memPrefix_of_ext hext12
    obtain ⟨hmem3, _, hprom3, _⟩ := hstore.append hprom2
    have hun3 : ¬ Reaches s3 dst.label := fun hr =>
      hun2 (reaches_push hstore.roots hmem3 (fun b _ _ hb => absurd hb hun2) hr)
    have hsound3 : RKnowSound s3 :=
      rknowSound_of_ext hstore.roots hstore.rknow hstore.ext hsound2
    have hp23 : MemPrefix s2.mem s3.mem := by rw [hmem3]; exact memPrefix_push _ _
    have hp34 : MemPrefix s3.mem s4.mem := memPrefix_of_ext henv.ext
    have hp24 : MemPrefix s2.mem s4.mem := hp23.trans hp34
    have hp14 : MemPrefix s1.mem s4.mem := hp12.trans hp24
    -- `stuck` only ever grows, and each rule says so in its own way.
    have hs23 : s2.stuck = true → s3.stuck = true := fun h => by
      rw [hstore.stuck, h]; simp
    have hs34 : s3.stuck = true → s4.stuck = true := fun h => by
      rw [henv.stuck]; exact h
    have hs24 : s2.stuck = true → s4.stuck = true := fun h => hs34 (hs23 h)
    have hs14 : s1.stuck = true → s4.stuck = true := fun h => hs24 (hload.stuck h)
    refine ⟨henv.sound hsound3, by rw [henv.promises]; exact hprom3,
            fun hr => hun3 (henv.priv hsound3 _ hr), hp01.trans hp14, ?_⟩
    intro t m hm hlab
    -- The buffer is unreachable, so `EnvPost.wrote` says Remote did not add
    -- this message: it predates the environment step.
    have hm3 : s3.mem[t]? = some m := by
      rcases Nat.lt_or_ge t s3.mem.size with hlt | hge
      · rw [← henv.ext.2 t hlt]; exact hm
      · exact absurd (hlab ▸ henv.wrote hsound3 t m hge hm) hun3
    rw [hmem3] at hm3
    rcases Nat.lt_or_ge t s2.mem.size with hlt | hge
    · -- A cell an earlier iteration filled: the invariant already covers it,
      -- and both disjuncts survive the three steps.
      rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt] at hm3
      rw [hload.mem] at hm3
      obtain ⟨i, hi, hor⟩ := hdst1 t m hm3 hlab
      refine ⟨i, hi, ?_⟩
      rcases hor with hst | hcf
      · exact Or.inl (hs14 hst)
      · exact Or.inr (hcf.mono hp14)
    · -- The cell this iteration just wrote.
      have ht : t = s2.mem.size := by
        rw [Array.getElem?_push] at hm3
        by_cases he : t = s2.mem.size
        · exact he
        · rw [ite_eq_right he] at hm3
          rw [Array.getElem?_eq_none hge] at hm3
          simp at hm3
      subst ht
      rw [Array.getElem?_push_size] at hm3
      cases hm3
      refine ⟨cur, rfl, ?_⟩
      rcases hload.read with hst | ⟨hundef, hnone⟩ | ⟨hmsg, _⟩
      · exact Or.inl (hs24 hst)
      · -- Nothing was readable, so by `unwritten_of_no_readable` the source
        -- cell was unwritten -- and memory only grows, so it was unwritten at
        -- the start too.  This is the disjunct that has to be about `mem₀`.
        refine Or.inr (Or.inr ⟨hundef, ?_⟩)
        intro t' m' hm' hloc'
        have hm1' : s1.mem[t']? = some m' := hp01 t' m' hm'
        have hno := unwritten_of_no_readable s1.mem
          ⟨src.label, src.offset + cur⟩ _ hnone t'
        rw [hm1'] at hno
        simp [hloc'] at hno
      · exact Or.inr (Or.inl ⟨v.rts, _, hp14 _ _ hmsg, rfl, rfl⟩)
  -- Entry.
  · rename_i s₀ hpre dst sM hM
    obtain ⟨hLB, hMLB, hsound, hprom, hmem0⟩ := hpre
    obtain ⟨hdst, hsM⟩ := hM
    subst hdst
    have hroots : sM.roots = s₀.roots := by rw [hsM]
    have hmem : sM.mem = s₀.mem := by rw [hsM]
    have hknow : sM.rknow = s₀.rknow := by rw [hsM]
    have hprm : sM.promises = s₀.promises := by rw [hsM]
    refine ⟨fun ra hra => reaches_of_eq (s' := s₀) (s := sM) hroots.symm hmem.symm
              (hsound ra (hknow ▸ hra)),
            by rw [hprm]; exact hprom, ?_, ?_, ?_⟩
    · intro hr
      exact Nat.lt_irrefl _
        (reaches_lt hLB (reaches_of_eq (s' := sM) (s := s₀) hroots hmem hr))
    · rw [hmem, hmem0]; exact MemPrefix.refl _
    · -- Vacuous: the buffer's label did not exist, so no message is in it.
      intro t m hm hlab
      exfalso
      rw [hmem] at hm
      exact Nat.lt_irrefl _ (hlab ▸ hMLB t m hm)
  -- Exit.
  · rename_i _ _ _ _ _ _ _ hinv
    exact hinv.2.2.2.2

/-- `v` describes the contents of `src`: every message at `src[i]` carries
    `v i`, and a cell nobody wrote is described as `undef`.

    The second clause is not padding.  Without it the description says nothing
    about cells that were never written, and the copy's `undef` case could not
    be matched against it. -/
def Describes (mem : Memory) (src : Address) (v : Nat → Val) : Prop :=
  ∀ i : Nat,
    (∀ (t : Nat) (m : Msg), mem[t]? = some m →
       m.loc = (⟨src.label, src.offset + i⟩ : Address) → m.val = v i)
    ∧ ((∀ (t : Nat) (m : Msg), mem[t]? = some m →
         m.loc ≠ (⟨src.label, src.offset + i⟩ : Address)) → v i = Val.undef)

/-- **The strong half.**  If the source still holds what it held, the copy is
    exact.

    The antecedent `Describes s.mem src v` is the interference assumption, and
    putting it in the *postcondition* rather than the precondition is what keeps
    this a corollary: nothing here re-runs the loop.  Two things in this file
    discharge it -- §9's `rdisowned` (via `EnvPost.frozen`, which forbids Remote
    from appending to an owned label) and §11.2's lock (which derives the same
    exclusion from a CAS instead of assuming it).

    `s.stuck = false` is the other antecedent, and it is the bounds discipline:
    an out-of-bounds source read gives up, and a run that gave up promises
    nothing. -/
theorem copy_is_exact (src : Address) (n : Nat) (mem₀ : Memory) (v : Nat → Val) :
    ⦃fun s => ⌜LabelsBelow s ∧ MsgLabelsBelow s ∧ RKnowSound s ∧ s.promises = [] ∧
               s.mem = mem₀⌝⦄
    (do let dst ← malloc n; copy src dst n; pure dst)
    ⦃⇓ dst s => ⌜Describes mem₀ src v → Describes s.mem src v → s.stuck = false →
        ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label = dst.label →
          ∃ i, m.loc = (⟨dst.label, dst.offset + i⟩ : Address) ∧ m.val = v i⌝⦄ := by
  refine Triple.of_entails_wp
    (Triple.entails_wp_of_post (copy_copies_something src n mem₀) ⟨?_, ?_⟩)
  · intro dst s h hd0 hd1 hstuck t m hm hlab
    obtain ⟨i, hi, hor⟩ := h t m hm hlab
    refine ⟨i, hi, ?_⟩
    rcases hor with hst | hcf
    · rw [hstuck] at hst; exact absurd hst (by simp)
    rcases hcf with ⟨t', m', hm', hloc', hval'⟩ | ⟨hundef, hno⟩
    · -- A real message at the source cell, and the source is described by `v`
      -- at the end, so that message carries `v i`.
      rw [← hval']; exact (hd1 i).1 t' m' hm' hloc'
    · -- The source cell was unwritten at the start, so `v` describes it as
      -- `undef`, which is what the copy took.
      rw [hundef, (hd0 i).2 hno]
  · exact .rfl

/-! ### The control

Two differentials, because §10 introduced two things.

The first is D1: `undef` is a *value*, not a fault.  A load from a cell that has
been allocated and never written returns it and carries on; a load from outside
every allocation is stuck.  Before this section those were the same outcome,
which is why the distinction is worth exhibiting rather than asserting.

The store is shown too, because the two rules read the same predicate but not in
the same place, and the difference is visible.  A load has a branch where no
message exists, so it consults `allocated` only there.  A store has no such
branch -- appending is always available -- so an out-of-bounds store is recorded
*and* flagged, rather than being suppressed.  That looks careless and is not:
suppression would need the store rule to have two shapes, and `stuck` is sticky,
so a later load of the cell the bad store created runs in an already-flagged
state.  The check is conditional in one rule and unconditional in the other, and
the composition is still sound.

The second is the privacy claim.  "Nothing wrote to the buffer" is also what an
inert environment reports, and this run has more moving parts than any before
it, so the negative result is worth less than usual on its own.  Same memory,
same oracle, same adversary, same number of iterations; the only difference is
where the copy goes -- into a buffer `malloc` just produced, or into one the
root already points at.  The oracle steers Remote to read the root and then
write through what it learned, which is the best it can do in both runs. -/

def allocScenario (inBounds : Bool) : String :=
  let s0 : Machine := { mem := #[], oracle := [] }
  let (r, s) :=
    (do let a ← malloc 4
        mload ⟨a.label, if inBounds then 3 else 4⟩ : M TVal).run s0
  s!"in-bounds={inBounds}: read={repr r.val}, stuck={s.stuck}"

def allocDemo : String :=
  "  " ++ allocScenario true ++ "\n  " ++ allocScenario false

/-- The store-side companion.  Same allocation, same two offsets.

    The third row is the one that matters.  It stores out of bounds and then
    loads the cell it just created -- so the load *does* find a readable message
    and takes the conditional branch that never consults `allocated`.  If
    `stuck` were not sticky that run would report clean, and the bounds check
    would be defeated by the simplest possible program.  It reports stuck
    because the store already said so. -/
def storeBoundsScenario : Bool → String
  | true =>
      let s0 : Machine := { mem := #[], oracle := [] }
      let ((), s) :=
        (do let a ← malloc 4
            mstore ⟨a.label, 3⟩ (Val.num 7) : M Unit).run s0
      s!"in-bounds=true:  writes={s.mem.size}, stuck={s.stuck}"
  | false =>
      let s0 : Machine := { mem := #[], oracle := [] }
      let ((), s) :=
        (do let a ← malloc 4
            mstore ⟨a.label, 4⟩ (Val.num 7) : M Unit).run s0
      s!"in-bounds=false: writes={s.mem.size}, stuck={s.stuck}"

/-- Store out of bounds, then read back what you wrote.  See
    `storeBoundsScenario`. -/
def readBackScenario : String :=
  let s0 : Machine := { mem := #[], oracle := [0] }
  let (r, s) :=
    (do let a ← malloc 4
        mstore ⟨a.label, 4⟩ (Val.num 7)
        mload ⟨a.label, 4⟩ : M TVal).run s0
  s!"store-then-load out of bounds: read={repr r.val}, stuck={s.stuck}"

def storeBoundsDemo : String :=
  "  " ++ storeBoundsScenario true ++ "\n  " ++ storeBoundsScenario false ++
  "\n  " ++ readBackScenario


def copyScenario (fresh : Bool) : String :=
  let root : Address := ⟨0, 0⟩
  let src : Address := ⟨1, 0⟩
  let buf : Address := ⟨2, 0⟩
  let s0 : Machine :=
    { mem := #[⟨⟨1, 0⟩, Val.num 5, 0⟩, ⟨⟨1, 1⟩, Val.num 6, 0⟩,
               ⟨root, Val.loc buf 0, 0⟩],
      roots := [root], rknow := [⟨root, 0⟩],
      -- Labels 0, 1, 2 exist, so `malloc` hands out label 3.
      sizes := [1, 2, 2],
      -- Per iteration: mload (1), mstore (1), renv (3).
      --   iter 1  renv = (addr 0 = root, act 1 = load, ts 0)  -- learn `buf`
      --   iter 2  renv = (addr 1 = buf,  act 2 = store, j 0)  -- clobber it
      oracle := [0, 0, 0, 1, 0, 0, 0, 1, 2, 0] }
  let prog : M Address :=
    if fresh then (do let dst ← malloc 2; copy src dst 2; pure dst)
    else (do copy src buf 2; pure buf)
  let (dst, s) := prog.run s0
  -- Every message appended to the destination allocation.  The copy itself
  -- accounts for two; anything beyond that is Remote.
  let writes := (List.range s.mem.size).countP fun t =>
    decide (s0.mem.size ≤ t) &&
      (s.mem[t]?.elim false fun m => decide (m.loc.label = dst.label))
  s!"fresh={fresh}: dst=label {dst.label}, writes-to-dst={writes} " ++
  s!"(copy made 2), stuck={s.stuck}"

def copyDemo : String :=
  "  " ++ copyScenario false ++ "\n  " ++ copyScenario true

def valStr : Val → String
  | Val.undef => "undef"
  | Val.null  => "null"
  | Val.num n => toString n
  | Val.loc a _ => s!"@{a.label}.{a.offset}"

/-- Every value ever written to `a`, oldest first.  Not "the value of `a`" --
    there is no such thing here, which is the point of the row below. -/
def histAt (mem : Memory) (a : Address) : List Val :=
  (List.range mem.size).filterMap fun t =>
    match mem[t]? with
    | some m => if m.loc = a then some m.val else none
    | none => none

def histStr (mem : Memory) (a : Address) : String :=
  "[" ++ String.intercalate ", " ((histAt mem a).map valStr) ++ "]"

/-- The most recent value at `a`. -/
def cellStr (mem : Memory) (a : Address) : String :=
  match (histAt mem a).getLast? with
  | some v => valStr v
  | none => "undef"

/-- **What the copy copied.**  `copyScenario` counts the destination's messages;
    this one reads them, which is what `copy_copies_something` and
    `copy_is_exact` actually talk about.

    Both rows produce the *same buffer*, `[5, 6]`.  They differ only in the
    source's history, and that is the whole argument:

    Row 1 is `copy_is_exact`.  The environment stutters, `src[0]` was written
    once, so the single-valued function `v = [5, 6]` satisfies
    `Describes s.mem src v`, the antecedent discharges, and the buffer is a
    word-for-word duplicate.

    Row 2 is why that antecedent has to be there.  Remote overwrites `src[0]`
    *after* the first iteration has already copied it, so the source's history
    at offset 0 is `[5, 0]`: two messages, two different values.  No `v`
    describes that memory -- `Describes` demands every message at a cell carry
    the same value, which is precisely the statement that the cell is frozen --
    so `copy_is_exact` says nothing about this run, correctly, because the
    buffer no longer matches the source.  `copy_copies_something` still holds
    of it, and holds for the right reason: the message carrying `5` is still in
    memory at `src[0]`, merely superseded.

    So `Describes` is not a technicality bolted onto the strong theorem.  It is
    the frozen-source hypothesis, and §9's `rdisowned` and §11.2's lock are the
    two ways to buy it. -/
def copyValuesScenario (clobber : Bool) : String :=
  let root : Address := ⟨0, 0⟩
  let src : Address := ⟨1, 0⟩
  let s0 : Machine :=
    { mem := #[⟨⟨1, 0⟩, Val.num 5, 0⟩, ⟨⟨1, 1⟩, Val.num 6, 0⟩,
               ⟨root, Val.loc src 0, 0⟩],
      roots := [root],
      -- `RKnowSound` holds: label 0 is a root and label 1 is reachable through
      -- the pointer stored in it, so Remote is entitled to both.  That is what
      -- makes the source clobberable here and not in `copyScenario`, where the
      -- source is unreachable and Remote can only touch the buffer.
      rknow := [⟨root, 0⟩, ⟨src, 0⟩],
      sizes := [1, 2],
      -- Per iteration: mload (1), mstore (1), renv (2 to stutter, 3 to store).
      -- The clobber is `(addr 1 = src, act 2 = store, j 0)`, which writes
      -- `Val.num 0`, and it fires at the end of iteration 1 -- after `src[0]`
      -- has been read.  The empty oracle stutters throughout.
      oracle := if clobber then [0, 0, 1, 2, 0] else [] }
  let (dst, s) := (do let d ← malloc 2; copy src d 2; pure d).run s0
  let dstShown := "[" ++ String.intercalate ", "
    ((List.range 2).map fun i => cellStr s.mem ⟨dst.label, dst.offset + i⟩) ++ "]"
  let srcShown := histStr s.mem src
  let tag := if clobber then "clobber=true: " else "clobber=false:"
  s!"{tag} dst={dstShown}, src[0] history={srcShown}, " ++
  s!"stuck={s.stuck}"

def copyValuesDemo : String :=
  "  " ++ copyValuesScenario false ++ "\n  " ++ copyValuesScenario true


/-! ## 11. Read-modify-write, and the beginning of a lock

Everything before this section constrains *which* write a read may see.  An RMW
constrains something else: whether a read and a write may have anything between
them.  That is the one property locks cannot be built without, and building
locks rather than assuming them is the point -- §9's `rdisowned` is an
assumption with no mechanism behind it, and the only honest way to discharge it
is to derive exclusion from something the hardware actually provides.

`WeakMem.lean` has the operational rule and it is herd7-validated (`CASAtomic`,
`SWPAtomic`, `SB+cas`, `MP+cas+po`, `MP+casl+ldar`, `LB+cas`).  What this
section adds is the front-end operation and its spec, so that RMW can appear in
a `do`-block and be reasoned about without unfolding the machine.

Three things fall out of atomicity rather than being stipulated, and they are
what make the spec worth having:

* **A successful RMW cannot read stale.**  Its write lands at the end of memory,
  so adjacency says nothing at the location may sit between; that is exactly
  "the read was the coherence-latest write".  It holds however far behind this
  thread's views are, and `CasPost.append` states it directly.
* **A failed compare is an ordinary load.**  It writes nothing, so atomicity
  constrains nothing, and it may read stale like any other load.
* **An RMW never runs out of successors.**  A read the atomicity rule rejects
  simply yields no outcome, so in principle every candidate could drop out.
  `casOutcomes_nil` shows it cannot: the coherence-latest message is never
  hidden, so it is always readable, and it is always adjacent.

The front end takes a plain `Val` to compare against rather than
`WeakMem.Instr`'s `Option Val`.  The unconditional swap is a stage-1 instruction
with nothing to prove about it; the comparison is the whole content of a lock.
-/

/-- The timestamps a load -- or the read half of an RMW -- may see. -/
def readCands (s : Machine) (a : Address) (deps : List TVal) : List Ts :=
  (List.range s.mem.size).filter fun t => readable s.mem a t (loadBound s a deps)

/-- The message an RMW read.  Total, with a dummy for an out-of-range index that
    no reachable call can produce. -/
def casMsg (s : Machine) (a : Address) (tr : Ts) : Msg :=
  s.mem[tr]?.getD ⟨a, Val.undef, 0⟩

/-- The views after the read half.  Same rule as `mload`, `pairTop` and all. -/
def casReadVs (s : Machine) (a : Address) (acq : Bool) (tr : Ts) : VState :=
  let m := casMsg s a tr
  { s.vs with
    coh := fun b => if b = a then max (s.vs.coh a) tr else s.vs.coh b
    vRd := max s.vs.vRd (rdV s.vs s.pairs tr m.view)
    vPreBase := if acq then max s.vs.vPreBase (acqV s.vs s.pairs tr m.view) else s.vs.vPreBase }

/-- `mstoreView`, but against the views the read half already updated: the write
    of an RMW follows its own read. -/
def casView (vs : VState) (deps : List TVal) (rel : Bool) : Ts :=
  if rel then max (max vs.vRelSt (max vs.vRd vs.vWr)) (tvView deps)
  else max vs.vRelSt (tvView deps)

/-- `mstoreOb`, likewise. -/
def casOb (arch : Arch) (vs : VState) (a : Address) (deps : List TVal) : Ts :=
  let ob0 := max (max vs.vPreBase (tvRts deps)) (max vs.vCtrl (vs.coh a))
  if arch = .tso then max ob0 (max vs.vRd vs.vWr) else ob0

/-- Where a successful RMW that read `tr` may put its write: at the end of
    memory, or into an outstanding promise -- and in both cases only where
    atomicity permits. -/
def casSlots (s : Machine) (a : Address) (newv : Val) (deps : List TVal)
    (rel acq : Bool) (tr : Ts) : List Ts :=
  let rvs := casReadVs s a acq tr
  (if rmwAdjacent s.mem a tr s.mem.size then [s.mem.size] else []) ++
  s.promises.filter fun tw =>
    (s.mem[tw]?.elim false fun m =>
      m.loc == a && m.val == newv && casView rvs deps rel ≤ m.view) &&
    decide (casOb s.arch rvs a deps ≤ tw) &&
    rmwAdjacent s.mem a tr tw

/-- Every outcome of one RMW: which message it read, and where its write went.
    `none` is a failed compare, which writes nothing.

    One list resolved by one oracle choice, rather than a read choice followed by
    a write choice.  Every other front-end operation consumes exactly one oracle
    entry and keeping that true here is what makes the spec a single case
    analysis instead of a nested one.

    A successful compare on a read that atomicity will not let this thread write
    after contributes *no* outcome, which is exactly what `stepRmw` does -- it
    returns no successor.  It is not a stuck state, and it cannot make the whole
    list empty: the coherence-latest message at `a` is never hidden, so it is
    always among `readCands`, and it is always adjacent to `mem.size`. -/
def casOutcomes (s : Machine) (a : Address) (cmp newv : Val) (deps : List TVal)
    (rel acq : Bool) : List (Ts × Option Ts) :=
  (readCands s a deps).flatMap fun tr =>
    if (casMsg s a tr).val = cmp then
      (casSlots s a newv deps rel acq tr).map fun tw => (tr, some tw)
    else [(tr, none)]

/-- The effect of one chosen outcome. -/
def casApply (s : Machine) (a : Address) (newv : Val) (deps : List TVal)
    (rel acq : Bool) (o : Ts × Option Ts) : Machine :=
  let rvs := casReadVs s a acq o.1
  match o.2 with
  | none => { s with vs := rvs }
  | some tw =>
      { s with
        mem := if tw = s.mem.size then s.mem.push ⟨a, newv, casView rvs deps rel⟩
               else s.mem
        promises := if tw = s.mem.size then s.promises else s.promises.erase tw
        vs := { rvs with
                coh := fun b => if b = a then tw else rvs.coh b
                vWr := max rvs.vWr tw, mine := tw :: rvs.mine } }

/-- Compare-and-swap.  Returns what it read and whether it succeeded.

    The front end takes a plain `Val` to compare against rather than
    `WeakMem.Instr`'s `Option Val`: the unconditional swap is a stage-1
    instruction with nothing to prove about it, and the comparison is the whole
    content of a lock.

    **An RMW on a location that has never been written fails.**  There is no
    message for the write to be adjacent *to*, so atomicity has nothing to
    attach it to.  The cell reads `undef` -- a value, by D1 -- and the operation
    is not stuck unless the address is outside every allocation, exactly as for
    a load.  Read as a rule about programs: a lock word must be initialised
    before it can be taken. -/
def mcas (a : Address) (cmp newv : Val) (deps : List TVal := [])
    (rel : Bool := false) (acq : Bool := false) : M (TVal × Bool) := do
  let s ← get
  match casOutcomes s a cmp newv deps rel acq with
  | [] =>
      modifyGet fun s' =>
        ((TVal.mk0 Val.undef, false), { s' with stuck := s'.stuck || !allocated s' a })
  | o :: os =>
      let out ← demonic o os
      modifyGet fun s' =>
        let m := casMsg s' a out.1
        ((if out.2.isSome && !acq then ⟨m.val, 0, 0⟩ else ⟨m.val, m.view, out.1⟩,
          out.2.isSome),
         casApply s' a newv deps rel acq out)

/-! ### The spec -/

/-- What an RMW guarantees.

    `acq` is a parameter and `rel` is not, which is not an oversight: the
    release flag only affects the *view the write carries*, and nothing outside
    `mcas` has yet needed to say anything about that, whereas the acquire flag
    affects the *reader's own barrier* and §17 needs exactly that. -/
structure CasPost (a : Address) (cmp newv : Val) (deps : List TVal) (acq : Bool)
    (s₀ : Machine) (r : TVal × Bool) (s : Machine) : Prop where
  ext : Extends s₀ s
  pub : s.vs.vRelSt = s₀.vs.vRelSt
  roots : s.roots = s₀.roots
  rknow : s.rknow = s₀.rknow
  disowned : s.rdisowned = s₀.rdisowned
  /-- Success means the comparison matched what was read. -/
  matched : r.2 = true → r.1.val = cmp
  /-- A failed RMW is a plain load: it writes nothing. -/
  fail : r.2 = false → s.mem = s₀.mem ∧ s.promises = s₀.promises
  /-- What was read.  Three cases, as for a load, plus a fourth: a successful
      non-acquire CAS reports the value only.  Its destination register keeps
      the comparand's dependencies, which here are none (`stepRmw`'s
      `rmwDst`), so `r.1` names no message. -/
  read : s.stuck = true
    ∨ (r.1.val = Val.undef ∧ r.2 = false ∧
       ∀ t, readable s₀.mem a t (loadBound s₀ a deps) = false)
    ∨ (r.2 = true ∧ acq = false)
    ∨ (s₀.mem[r.1.rts]? = some ⟨a, r.1.val, r.1.view⟩ ∧
       readable s₀.mem a r.1.rts (loadBound s₀ a deps) = true)
  /-- **Atomicity, in the form an exclusion argument uses.**  A successful RMW
      with nothing promised appends its write, and nothing at `a` lies above
      what it read: the value it compared against was the coherence-latest one,
      however far behind this thread's views were. -/
  append : r.2 = true → s₀.promises = [] →
    (∃ mv, s.mem = s₀.mem.push ⟨a, newv, mv⟩) ∧
    s.vs.coh a = s₀.mem.size ∧
    s.promises = [] ∧
    s₀.mem.size ≤ s.vs.vWr ∧
    (acq = true → betweenAt s₀.mem a r.1.rts s₀.mem.size = false)
  /-- **What the acquire is for.**  An acquiring RMW pulls the view of the
      message it read into `vPreBase`, so everything the previous holder
      published before releasing is ordered before everything the critical
      section does.

      Fourth of the "only as strong as its first client" additions, and the one
      that made §17's reader provable.  The weaker `s₀.vs.vPreBase ≤
      s.vs.vPreBase` would have been enough to *carry* a barrier the reader
      already had; this is what lets the reader *acquire* one it did not.  The
      distinction matters because a reader that has done nothing yet has
      `vPreBase = 0`, and the whole question is how the writer's timestamps get
      under its load bound. -/
  acqv : acq = true → ownFwd s₀.vs r.1.rts = none → r.1.view ≤ s.vs.vPreBase

/-! ### An RMW never runs out of slots

`mcas` is stuck only when `casOutcomes` is empty, and the spec's "nothing was
readable" case has to be justified from that.  It does not follow for free: a
read whose compare succeeds but which atomicity will not let this thread write
after contributes no outcome, so in principle every readable timestamp could
drop out.

It cannot, and the reason is the one named in `WeakMem`'s RMW section: the
coherence-latest message at `a` is never hidden, so it is always readable, and
it is by definition adjacent to the end of memory.  It therefore always supplies
an outcome.  Two lemmas, and then the fact. -/

/-- Walking up the modification order of `a` terminates at a message with
    nothing above it.  `n` is a fuel argument: `mem.size` always suffices. -/
theorem exists_latest (mem : Memory) (a : Address) :
    ∀ n tr, mem.size ≤ tr + n → tr < mem.size →
      (mem[tr]?.elim false fun m => decide (m.loc = a)) = true →
      ∃ u, u < mem.size ∧ (mem[u]?.elim false fun m => decide (m.loc = a)) = true ∧
        betweenAt mem a u mem.size = false := by
  intro n
  induction n with
  | zero =>
    intro tr h1 h2 _
    simp only [Nat.add_zero] at h1
    exact absurd (Nat.lt_of_lt_of_le h2 h1) (Nat.lt_irrefl _)
  | succ n ih =>
    intro tr h1 h2 h3
    cases hb : betweenAt mem a tr mem.size with
    | false => exact ⟨tr, h2, h3, hb⟩
    | true =>
      rw [betweenAt, List.any_eq_true] at hb
      obtain ⟨t', _, hcond⟩ := hb
      rw [Bool.and_eq_true, Bool.and_eq_true] at hcond
      obtain ⟨⟨hl1, hl2⟩, hat⟩ := hcond
      have hl1' : tr < t' := by simpa using hl1
      have hl2' : t' < mem.size := by simpa using hl2
      exact ih t' (by omega) hl2' hat

/-- A message with nothing above it at `a` is readable whatever the bound.  This
    is the same observation as `readable_top_of_frozen` in §8, in the form the
    RMW rule needs it. -/
theorem readable_of_latest {mem : Memory} {a : Address} {u bound : Ts}
    (hat : (mem[u]?.elim false fun m => decide (m.loc = a)) = true)
    (hb : betweenAt mem a u mem.size = false) :
    readable mem a u bound = true := by
  have hh : hiddenFrom mem a u bound = false := by
    rw [hiddenFrom, List.any_eq_false]
    intro t' _ hcond
    rw [Bool.and_eq_true] at hcond
    obtain ⟨h1, h2⟩ := hcond
    have hu' : u < t' := by simpa using h1
    -- A message exists at `t'`, so `t'` is inside memory, so `betweenAt` saw it.
    have ht's : t' < mem.size := by
      rcases Nat.lt_or_ge t' mem.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at h2; simp at h2
    have hcontra : betweenAt mem a u mem.size = true := by
      rw [betweenAt, List.any_eq_true]
      exact ⟨t', List.mem_range.mpr ht's, by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hu', ht's⟩, h2⟩⟩
    rw [hcontra] at hb
    simp at hb
  rw [readable, hat, hh]
  rfl

/-- So the outcome list is empty only when nothing at `a` was readable at all --
    which, since an unhidden message is always readable, means there is no
    message at `a` anywhere. -/
theorem casOutcomes_nil (s : Machine) (a : Address) (cmp newv : Val)
    (deps : List TVal) (rel acq : Bool)
    (h : casOutcomes s a cmp newv deps rel acq = []) : readCands s a deps = [] := by
  cases hrc : readCands s a deps with
  | nil => rfl
  | cons tr rest =>
    exfalso
    have htr : tr ∈ readCands s a deps := by rw [hrc]; exact List.mem_cons_self ..
    have hread : readable s.mem a tr (loadBound s a deps) = true := by
      rw [readCands, List.mem_filter] at htr; exact htr.2
    obtain ⟨m, hm, hloc⟩ := msg_of_readable hread
    have hat : (s.mem[tr]?.elim false fun mm => decide (mm.loc = a)) = true := by
      rw [hm]; simpa using hloc
    have htrs : tr < s.mem.size := by
      rcases Nat.lt_or_ge tr s.mem.size with hl | hg
      · exact hl
      · rw [Array.getElem?_eq_none hg] at hm; simp at hm
    obtain ⟨u, hus, hau, hbu⟩ :=
      exists_latest s.mem a s.mem.size tr (Nat.le_add_left _ _) htrs hat
    have huread : u ∈ readCands s a deps := by
      rw [readCands, List.mem_filter]
      exact ⟨List.mem_range.mpr hus, readable_of_latest hau hbu⟩
    have hadj : rmwAdjacent s.mem a u s.mem.size = true := by
      simp [rmwAdjacent, hbu, hus]
    have hmem : ∃ o, o ∈ casOutcomes s a cmp newv deps rel acq := by
      by_cases hc : (casMsg s a u).val = cmp
      · refine ⟨(u, some s.mem.size), ?_⟩
        rw [casOutcomes, List.mem_flatMap]
        refine ⟨u, huread, ?_⟩
        rw [ite_eq_left hc, List.mem_map]
        exact ⟨s.mem.size, by simp [casSlots, hadj], rfl⟩
      · exact ⟨(u, none), by
          rw [casOutcomes, List.mem_flatMap]
          exact ⟨u, huread, by rw [ite_eq_right hc]; simp⟩⟩
    obtain ⟨o, ho⟩ := hmem
    rw [h] at ho
    simp at ho

/-- The pure content of the empty case. -/
theorem cas_post_empty (a : Address) (cmp newv : Val) (deps : List TVal)
    (rel acq : Bool) (s₀ : Machine)
    (hf : casOutcomes s₀ a cmp newv deps rel acq = []) :
    CasPost a cmp newv deps acq s₀ (TVal.mk0 Val.undef, false)
      { s₀ with stuck := s₀.stuck || !allocated s₀ a } := by
  have hrc := casOutcomes_nil s₀ a cmp newv deps rel acq hf
  refine ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, rfl, rfl, rfl, rfl, ?_, fun _ => ⟨rfl, rfl⟩,
    Or.inr (Or.inl ⟨rfl, rfl, fun t => ?_⟩), ?_, fun _ _ => Nat.zero_le _⟩
  · intro h; simp at h
  · rcases Nat.lt_or_ge t s₀.mem.size with hlt | hge
    · have hno := List.filter_eq_nil_iff.mp hrc t (List.mem_range.mpr hlt)
      simpa using hno
    · unfold readable
      rw [Array.getElem?_eq_none hge]
      simp
  · intro h; simp at h

/-- The pure content of the interesting case.

    `tl` is the oracle after `demonic` has consumed its entry.  It has to be a
    parameter rather than `s₀.oracle`: the state the effect is applied to is the
    one `demonic` left behind, and nothing in `CasPost` mentions the oracle, but
    structure eta means the two records are *not* definitionally equal, so the
    lemma has to be stated at the right one. -/
theorem cas_post (a : Address) (cmp newv : Val) (deps : List TVal) (rel acq : Bool)
    (s₀ : Machine) (tl : List Nat) (o : Ts × Option Ts)
    (ho : o ∈ casOutcomes s₀ a cmp newv deps rel acq) :
    CasPost a cmp newv deps acq s₀
      (if o.2.isSome && !acq then ⟨(casMsg s₀ a o.1).val, 0, 0⟩
       else ⟨(casMsg s₀ a o.1).val, (casMsg s₀ a o.1).view, o.1⟩, o.2.isSome)
      (casApply { s₀ with oracle := tl } a newv deps rel acq o) := by
  rw [casOutcomes, List.mem_flatMap] at ho
  obtain ⟨tr, htr, ho⟩ := ho
  -- The read half, common to both branches.
  have hread : readable s₀.mem a tr (loadBound s₀ a deps) = true := by
    rw [readCands, List.mem_filter] at htr; exact htr.2
  obtain ⟨m, hm, hloc⟩ := msg_of_readable hread
  have hcas : casMsg s₀ a tr = m := by rw [casMsg, hm]; rfl
  by_cases hc : (casMsg s₀ a tr).val = cmp
  · -- Compare succeeded: `o = (tr, some tw)` for some slot `tw`.
    rw [ite_eq_left hc, List.mem_map] at ho
    obtain ⟨tw, htw, rfl⟩ := ho
    simp only [Option.isSome_some, Bool.true_and]
    -- The register a successful CAS returns: the value only unless it
    -- acquires (`rmwDst`).  Everything below but `read`, `append`'s last
    -- conjunct and `acqv` is about the state and does not look at it.
    have hres : ∀ (P : TVal → Prop),
        P ⟨(casMsg s₀ a tr).val, 0, 0⟩ → P ⟨(casMsg s₀ a tr).val, (casMsg s₀ a tr).view, tr⟩ →
        P (if (!acq) = true then ⟨(casMsg s₀ a tr).val, 0, 0⟩
           else ⟨(casMsg s₀ a tr).val, (casMsg s₀ a tr).view, tr⟩) := by
      intro P h0 h1; split <;> assumption
    refine ⟨?_, rfl, rfl, rfl, rfl, hres (fun r => true = true → r.val = cmp) (fun _ => hc) (fun _ => hc),
      ?_, ?_, ?_, ?_⟩
    · -- Extends: either a push or no change at all.
      by_cases hsz : tw = s₀.mem.size
      · refine ⟨?_, ?_⟩
        · show s₀.mem.size ≤ (if tw = s₀.mem.size then _ else s₀.mem).size
          rw [ite_eq_left hsz]; simp
        · intro u hu
          show (if tw = s₀.mem.size then _ else s₀.mem)[u]? = s₀.mem[u]?
          rw [ite_eq_left hsz]
          simp [Array.getElem?_push, Nat.ne_of_lt hu]
      · refine ⟨?_, ?_⟩
        · show s₀.mem.size ≤ (if tw = s₀.mem.size then _ else s₀.mem).size
          rw [ite_eq_right hsz]
          exact Nat.le_refl _
        · intro u _
          show (if tw = s₀.mem.size then _ else s₀.mem)[u]? = s₀.mem[u]?
          rw [ite_eq_right hsz]
    · intro h; simp at h
    · cases acq
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨?_, hread⟩))
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [hm, hcas]; simp [← hloc]
    · intro _ hp
      -- With nothing promised the only slot is the end of memory.
      have hslot : tw = s₀.mem.size ∧ rmwAdjacent s₀.mem a tr s₀.mem.size = true := by
        rw [casSlots, hp] at htw
        simp only [List.filter_nil, List.append_nil] at htw
        by_cases hadj : rmwAdjacent s₀.mem a tr s₀.mem.size
        · rw [ite_eq_left hadj] at htw; exact ⟨by simpa using htw, hadj⟩
        · rw [ite_eq_right hadj] at htw; simp at htw
      obtain ⟨rfl, hadj⟩ := hslot
      refine ⟨⟨casView (casReadVs s₀ a acq tr) deps rel, ?_⟩, ?_, ?_, ?_, ?_⟩
      · show (if s₀.mem.size = s₀.mem.size then _ else s₀.mem) = _
        rw [ite_eq_left rfl]
        rfl
      · show (if a = a then s₀.mem.size else _) = s₀.mem.size
        rw [ite_eq_left rfl]
      · show (if s₀.mem.size = s₀.mem.size then s₀.promises else _) = []
        rw [ite_eq_left rfl]; exact hp
      · exact Nat.le_max_right _ _
      · intro hacq
        subst hacq
        rw [rmwAdjacent, Bool.and_eq_true] at hadj
        simpa using hadj.2
    · -- `acqv`: the write branch keeps the read half's `vPreBase`, and an
      -- acquiring read half raises it to the view of the message it read --
      -- unless it read this thread's own plain write, which is forwarded.
      intro hacq hnf
      subst hacq
      dsimp only [casApply, casReadVs]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hnf ⊢
      rw [acqV_none _ hnf]
      exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  · -- Compare failed: a plain load.
    rw [ite_eq_right hc] at ho
    simp only [List.mem_singleton] at ho
    subst ho
    simp only [Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, rfl, rfl, rfl, rfl, ?_, fun _ => ⟨rfl, rfl⟩,
      Or.inr (Or.inr (Or.inr ⟨?_, hread⟩)), ?_, ?_⟩
    · intro h; simp at h
    · rw [hm, hcas]; simp [← hloc]
    · intro h; simp at h
    · -- `acqv`: a failed compare is a plain load, and the read half is all of it.
      intro hacq hnf
      subst hacq
      dsimp only [casApply, casReadVs]
      rw [acqV_none _ hnf]
      exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

@[spec]
theorem mcas_spec (a : Address) (cmp newv : Val) (deps : List TVal) (rel acq : Bool)
    (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    mcas a cmp newv deps rel acq
    ⦃⇓ r s => ⌜CasPost a cmp newv deps acq s₀ r s⌝⦄ := by
  mvcgen [mcas, demonic]
  case vc1.h_1 =>
    subst_vars
    simp +zetaDelta only []
    rename_i s hf _
    exact cas_post_empty a cmp newv deps rel acq s hf
  case vc2.h_2 =>
    subst_vars
    simp +zetaDelta only []
    -- Six names: the state, the outcome list's cons pattern and its equation,
    -- and the two let-bound intermediate states.
    rename_i s c cs hf _ _
    have hmem := pick_mem (s.oracle.headD 0) c cs
    rw [← hf] at hmem
    exact cas_post a cmp newv deps rel acq s s.oracle.tail _ hmem

/-! ### The control

The differential for atomicity has to show a stale read being *available* and
then being refused, on the same memory.

Two writes to the lock word: it was free, and then somebody took it.  This
thread's views are still at the beginning, so coherence does not forbid it from
seeing the first one -- and a load duly does, because the oracle asks for it.

The plain row is a test-and-set written the obvious way: load, check, store.  It
reads the stale `0`, concludes the lock is free, and takes it -- while somebody
else holds it.  Nothing in the load rule is wrong; the bug is that two
operations were used where one atomic one was needed.

The `mcas` row has the same memory, the same oracle and the same thread views,
and cannot do it.  The stale timestamp is still readable -- `readCands` contains
it -- but it yields no *outcome*, because a write after it would not be
adjacent.  The only outcome left reads the value that is really there. -/

def casScenario (atomic : Bool) : String :=
  let lock : Address := ⟨0, 0⟩
  let s0 : Machine :=
    { mem := #[⟨lock, Val.num 0, 0⟩, ⟨lock, Val.num 1, 0⟩],
      sizes := [1],
      -- Ask for the first readable candidate, i.e. the stale one.
      oracle := [0] }
  let prog : M (Val × Bool) :=
    if atomic then
      (do let (r, got) ← mcas lock (Val.num 0) (Val.num 1)
          pure (r.val, got))
    else
      (do let r ← mload lock
          if r.val = Val.num 0 then
            (do mstore lock (Val.num 1); pure (r.val, true))
          else pure (r.val, false))
  let ((v, got), s) := prog.run s0
  s!"atomic={atomic}: read={repr v}, acquired={got}, mem {s0.mem.size}→{s.mem.size}"

def casDemo : String :=
  "  " ++ casScenario false ++ "\n  " ++ casScenario true

/-! ### Small facts about memory that the exclusion argument needs -/

theorem betweenAt_of_witness {mem : Memory} {a : Address} {t t' : Ts} {m' : Msg}
    (h1 : t < t') (hm' : mem[t']? = some m') (hloc' : m'.loc = a) :
    betweenAt mem a t mem.size = true := by
  have h2 := lt_size_of_getElem? hm'
  rw [betweenAt, List.any_eq_true]
  refine ⟨t', List.mem_range.mpr h2, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨h1, h2⟩, ?_⟩
  rw [hm']
  simpa using hloc'

theorem betweenAt_push_top (mem : Memory) (a : Address) (m : Msg) :
    betweenAt (mem.push m) a mem.size (mem.push m).size = false := by
  rw [betweenAt, List.any_eq_false]
  intro t' _ hc
  rw [Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, _⟩ := hc
  have h1' : mem.size < t' := by simpa using h1
  have h2' : t' < (mem.push m).size := by simpa using h2
  rw [Array.size_push] at h2'
  omega

/-- Raising the upper bound from the end of memory to one past it changes
    nothing.  There is no message there to be in the way, so the extra slot the
    bound now admits contributes `false` either way.

    Needed because a pair's second write goes to `mem.size + 1`, so its
    adjacency obligation is stated at a bound one higher than the first
    word's. -/
theorem betweenAt_succ_top (mem : Memory) (a : Address) (t : Ts) :
    betweenAt mem a t (mem.size + 1) = betweenAt mem a t mem.size := by
  rw [betweenAt, betweenAt]
  congr 1
  funext t'
  rcases Nat.lt_or_ge t' mem.size with h | h
  · rw [decide_eq_true h, decide_eq_true (Nat.lt_succ_of_lt h)]
  · -- Outside the array the message lookup is `none`, so both sides are false.
    rw [Array.getElem?_eq_none h]
    simp

/-- There is at most one message at `a` with nothing above it, which is what
    makes "the coherence-latest value" a well-defined thing to reason about. -/
theorem latest_unique {mem : Memory} {a : Address} {t t' : Ts} {m m' : Msg}
    (hm : mem[t]? = some m) (hloc : m.loc = a)
    (hb : betweenAt mem a t mem.size = false)
    (hm' : mem[t']? = some m') (hloc' : m'.loc = a)
    (hb' : betweenAt mem a t' mem.size = false) : t = t' := by
  rcases Nat.lt_trichotomy t t' with h | h | h
  · rw [betweenAt_of_witness h hm' hloc'] at hb; simp at hb
  · exact h
  · rw [betweenAt_of_witness h hm hloc] at hb'; simp at hb'

/-! ### 11.1 A lock, derived

`rdisowned` (§9) says the environment does not write an allocation, and nothing
in the machine makes that true -- it is a rely condition with no mechanism
behind it.  Atomicity is the mechanism.  This section replaces the assumption
with a protocol: both agents run the *same* lock code, and exclusion is then a
theorem rather than a hypothesis.

What remains assumed is much weaker and of a different kind.  It is no longer
"the environment mysteriously refrains from writing"; it is "the environment
obeys the discipline", which is a statement about a program and is discharged by
that program's own proof.  That is the ordinary shape of a rely condition in
separation logic, and unlike `rdisowned` it is the sort of thing a type system
could enforce.

`renv` is left alone.  Its oracle protocol is (address, act in 0..2, operand)
and six scenarios in §7-§10 are tuned to it, so folding a fourth action in would
silently retune all of them.  Contention is exhibited where it is the point. -/

/-- `a` holds `v`, and that is the last word on the subject: nothing at `a` sits
    above it in the modification order.

    A predicate on `Memory` rather than on `Machine`, so that "the operation did
    not write" and "the invariant survives" are the same step. -/
def LatestIs (mem : Memory) (a : Address) (v : Val) : Prop :=
  ∃ t m, mem[t]? = some m ∧ m.loc = a ∧ m.val = v ∧
    betweenAt mem a t mem.size = false

theorem latestIs_push (mem : Memory) (a : Address) (v : Val) (mv : Ts) :
    LatestIs (mem.push ⟨a, v, mv⟩) a v :=
  ⟨mem.size, ⟨a, v, mv⟩, by simp, rfl, rfl, betweenAt_push_top _ _ _⟩

/-- The payoff.  An RMW can only read the coherence-latest message, so if the
    latest value is not the one it compares against, it cannot succeed. -/
theorem cas_cannot_match {mem : Memory} {a : Address} {v w : Val}
    (hl : LatestIs mem a v) (hne : v ≠ w)
    {tr : Ts} {m : Msg} (hm : mem[tr]? = some m) (hloc : m.loc = a) (hv : m.val = w)
    (hb : betweenAt mem a tr mem.size = false) : False := by
  obtain ⟨t, m0, hm0, hloc0, hv0, hb0⟩ := hl
  have ht : t = tr := latest_unique hm0 hloc0 hb0 hm hloc hb
  subst ht
  rw [hm0] at hm
  have : m0 = m := Option.some.inj hm
  subst this
  exact hne (hv0.symm.trans hv)

/-! ### Remote's half of the protocol -/

/-- The outcomes of a remote RMW: which message it read, and whether it took the
    location.  Same shape as `casOutcomes`, minus promises -- Remote does not
    promise -- so the write, when there is one, is always at the end of memory
    and adjacency is the only condition. -/
def rcasOutcomes (s : Machine) (ra : RAddr) (cmp : Val) : List (Ts × Bool) :=
  ((List.range s.mem.size).filter fun t =>
      readable s.mem ra.addr t (rloadBound s ra)).filterMap fun tr =>
    if (s.mem[tr]?.getD ⟨ra.addr, Val.undef, 0⟩).val = cmp then
      (if rmwAdjacent s.mem ra.addr tr s.mem.size then some (tr, true) else none)
    else some (tr, false)

/-- The read half is `rloadStep` unchanged -- a remote RMW reads exactly as a
    remote load does, including learning any pointer it saw.  The only new
    content is the write, and its only new condition is adjacency, which
    `rcasOutcomes` has already checked. -/
def rcasStep (s : Machine) (ra : RAddr) (newv : Val) (o : Ts × Bool) : Machine :=
  let s1 := rloadStep s ra o.1
  if o.2 then
    { s1 with
      mem := s.mem.push ⟨ra.addr, newv, max s.rvs.vRelSt ra.view⟩
      rvs := { s1.rvs with
                 coh := fun b => if b = ra.addr then s.mem.size else s1.rvs.coh b,
                 vWr := max s1.rvs.vWr s.mem.size, mine := s.mem.size :: s1.rvs.mine } }
  else s1

/-- Remote attempting the same protocol.  Not guarded by `rdisowned`: the lock
    word is precisely the thing nobody gives up. -/
def rcas (ra : RAddr) (cmp newv : Val) : M Bool := do
  let s ← get
  match rcasOutcomes s ra cmp with
  | [] => pure false
  | o :: os =>
      let out := pick (s.oracle.headD 0) o os
      modify fun s' => rcasStep s' ra newv out
      pure out.2

/-- What a remote attempt guarantees.  Only two things are needed, and both are
    about memory: a failure writes nothing, and a success read a message holding
    the compared-against value with nothing above it. -/
structure RcasPost (a : Address) (cmp : Val) (s₀ : Machine) (r : Bool)
    (s : Machine) : Prop where
  fail : r = false → s.mem = s₀.mem
  ok : r = true → ∃ tr m, s₀.mem[tr]? = some m ∧ m.loc = a ∧ m.val = cmp ∧
    betweenAt s₀.mem a tr s₀.mem.size = false
  /-- Remote touches its own views, never Local's.  `EnvPost` carries the same
      clause; without it a caller cannot compute a local load's bound across a
      remote step, which is what §11.2 needs. -/
  vs : s.vs = s₀.vs
  /-- Nor Local's promises.  Remote has none of its own -- it appends at the end
      of memory and never fulfils -- so this is `rfl` in both branches.  It is
      here because §17's critical section runs a whole loop of stores, and every
      one of them needs `StorePost.append`, whose hypothesis is that the promise
      list is empty.  Without this clause the first environment step in the loop
      body loses that hypothesis and the induction stops. -/
  promises : s.promises = s₀.promises
  /-- Nor Local's `stuck` flag: the three remote step functions are record
      updates that do not mention it.

      Added for the same reason as `promises`, one theorem later.  §17's reader
      loop carries a per-iteration "...or the run is stuck" escape clause -- the
      one `LoadPost.stuck` exists to support -- and an escape clause is only
      inheritable if *every* step in the body preserves it.  The environment step
      was the one that did not say so. -/
  stuck : s.stuck = s₀.stuck

theorem rcas_post (ra : RAddr) (cmp newv : Val) (s₀ : Machine) (o : Ts × Bool)
    (ho : o ∈ rcasOutcomes s₀ ra cmp) :
    RcasPost ra.addr cmp s₀ o.2 (rcasStep s₀ ra newv o) := by
  rw [rcasOutcomes, List.mem_filterMap] at ho
  obtain ⟨tr, htr, hf⟩ := ho
  have hread : readable s₀.mem ra.addr tr (rloadBound s₀ ra) = true := by
    rw [List.mem_filter] at htr; exact htr.2
  obtain ⟨m, hm, hloc⟩ := msg_of_readable hread
  have hgetD : (s₀.mem[tr]?.getD ⟨ra.addr, Val.undef, 0⟩) = m := by rw [hm]; rfl
  by_cases hc : (s₀.mem[tr]?.getD ⟨ra.addr, Val.undef, 0⟩).val = cmp
  · rw [ite_eq_left hc] at hf
    by_cases hadj : rmwAdjacent s₀.mem ra.addr tr s₀.mem.size
    · rw [ite_eq_left hadj] at hf
      have ho : o = (tr, true) := (Option.some.inj hf).symm
      subst ho
      refine ⟨fun h => by simp at h, fun _ => ⟨tr, m, hm, hloc, ?_, ?_⟩, rfl, rfl, rfl⟩
      · rw [← hgetD]; exact hc
      · rw [rmwAdjacent, Bool.and_eq_true] at hadj
        simpa using hadj.2
    · rw [ite_eq_right hadj] at hf; simp at hf
  · rw [ite_eq_right hc] at hf
    have ho : o = (tr, false) := (Option.some.inj hf).symm
    subst ho
    exact ⟨fun _ => rfl, fun h => by simp at h, rfl, rfl, rfl⟩

@[spec]
theorem rcas_spec (ra : RAddr) (cmp newv : Val) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    rcas ra cmp newv
    ⦃⇓ r s => ⌜RcasPost ra.addr cmp s₀ r s⌝⦄ := by
  mvcgen [rcas]
  case vc1.h_1 =>
    subst_vars
    -- Nothing at `ra.addr` can be read, so Remote does nothing and reports
    -- failure.  No let-bound names here, so no `zetaDelta` step.
    exact ⟨fun _ => rfl, fun h => by simp at h, rfl, rfl, rfl⟩
  case vc2.h_2 =>
    subst_vars
    simp +zetaDelta only []
    -- Six names: the state, the outcome list's cons pattern and its equation,
    -- and the two let-bound intermediate values.
    rename_i s o os hf _ _
    have hmem := pick_mem (s.oracle.headD 0) o os
    rw [← hf] at hmem
    exact rcas_post ra cmp newv s _ hmem

/-! ### The lock itself

Nothing in the machine knows what a lock is.  These are `mcas` and `mstore`,
and `lock_is_exclusive` below is a theorem about them. -/

/-- Take the lock: swap `0` for `1`, with acquire semantics so that whatever the
    previous holder released is ordered before anything the critical section
    does. -/
def acquire (l : Address) : M Bool := do
  let (_, got) ← mcas l (Val.num 0) (Val.num 1) [] false true
  pure got

/-- Give it back, with release semantics. -/
def release (l : Address) : M Unit :=
  mstore l (Val.num 0) [] true

/-- **Mutual exclusion.**  Once the local acquire has succeeded, Remote cannot
    also acquire -- and it stays that way across repeated attempts, because a
    failed attempt writes nothing and so cannot disturb the invariant.

    `s₀.promises = []` is a hypothesis of the theorem rather than a conjunct of
    the precondition: a conjunctive precondition alongside the `s = s₀` ghost
    makes `mvcgen` unify `s₀` with the caller's ghost. -/
theorem lock_is_exclusive (l : Address) (ra : RAddr) (s₀ : Machine)
    (hra : ra.addr = l) (hp : s₀.promises = []) :
    ⦃fun s => ⌜s = s₀⌝⦄
    (do let got ← acquire l
        let g1 ← rcas ra (Val.num 0) (Val.num 1)
        let g2 ← rcas ra (Val.num 0) (Val.num 1)
        pure (got, g1, g2))
    ⦃⇓ r _s => ⌜r.1 = true → r.2.1 = false ∧ r.2.2 = false⌝⦄ := by
  subst hra
  mvcgen [acquire]
  -- Three operations: the local acquire, then Remote's two attempts.  The two
  -- outcome flags are reached by their own type.
  name_hyps Post hcas h1 h2
  name_hyps Machine _ s1 s2 ..
  name_hyps Bool g1 g2
  name_hyps Eq hA ..
  subst hA
  intro hgot
  -- The acquire appended `1` to the lock word, so `1` is what is there now.
  obtain ⟨⟨mv, hmem⟩, _, _, _, _⟩ := hcas.append hgot hp
  have hne : (Val.num 1 : Val) ≠ Val.num 0 := by simp
  have hlat1 : LatestIs s1.mem ra.addr (Val.num 1) := by
    rw [hmem]; exact latestIs_push _ _ _ _
  -- Remote's attempt would have to read the latest value, and the latest value
  -- is not the one it compares against.  This is the whole argument.
  have hg1 : g1 = false := by
    cases hb : g1 with
    | false => rfl
    | true =>
      obtain ⟨tr, m, hm, hloc, hv, hbt⟩ := h1.ok hb
      exact (cas_cannot_match hlat1 hne hm hloc hv hbt).elim
  -- A failed attempt wrote nothing, so the invariant is still there for the
  -- second one.  Repetition costs nothing, which is the point.
  have hlat2 : LatestIs s2.mem ra.addr (Val.num 1) := by
    rw [h1.fail hg1]; exact hlat1
  have hg2 : g2 = false := by
    cases hb : g2 with
    | false => rfl
    | true =>
      obtain ⟨tr, m, hm, hloc, hv, hbt⟩ := h2.ok hb
      exact (cas_cannot_match hlat2 hne hm hloc hv hbt).elim
  exact ⟨hg1, hg2⟩

/-! ### The control

`lock_is_exclusive` is satisfied by a `rcas` that never succeeds, so the
interesting row is the one where Remote *does* take the lock.

Same memory, same oracle, same two remote attempts; the only difference is
whether the local thread acquired first.

With the lock free, Remote's first attempt takes it and its *second* fails --
so exclusion is not a privilege of the local agent, it is a property of the
operation.  With the lock already held, both fail, and the reason is visible in
the first row: the stale `0` at timestamp 0 is still readable to Remote, it just
cannot be written after. -/

def lockScenario (localFirst : Bool) : String :=
  let l : Address := ⟨0, 0⟩
  let ra : RAddr := ⟨l, 0⟩
  let s0 : Machine :=
    { mem := #[⟨l, Val.num 0, 0⟩], sizes := [1], roots := [l], rknow := [ra],
      oracle := [0, 0, 0] }
  let prog : M (Bool × Bool × Bool) := do
    let got ← if localFirst then acquire l else pure false
    let g1 ← rcas ra (Val.num 0) (Val.num 1)
    let g2 ← rcas ra (Val.num 0) (Val.num 1)
    pure (got, g1, g2)
  let ((got, g1, g2), s) := prog.run s0
  s!"local-acquires={localFirst}: local={got}, remote1={g1}, remote2={g2}, " ++
  s!"mem 1→{s.mem.size}"

def lockDemo : String :=
  "  " ++ lockScenario false ++ "\n  " ++ lockScenario true

/-! ## 11.2 From the lock to the data

§11.1 proved that the lock excludes: once the local acquire succeeds, no remote
attempt can take it.  That is a theorem about *the lock word*, and on its own it
protects nothing.  The step this section takes is the one §9 declined to take --
from "the environment cannot hold the lock" to "the environment cannot touch the
data".

The gap is exactly where `rdisowned` lives.  §9's guarantee is conditional on a
discipline the file cannot check: `assumeExclusive` is an annotation, and
`EnvPost.frozen` is what the environment is *assumed* to respect.  Here the
discipline is code.  `renvLocked` is an environment that runs the protocol -- it
attempts the CAS, and touches the data only if it won -- and nothing else about
it is assumed.  In particular the protected allocation is deliberately **not**
in `rdisowned`: the whole point is that the protection comes from the lock
instead.

The result, `lock_protects_data`, is `owned_load_reads_own_write` with the
assumption discharged.  Same program, same statement; the hypothesis "the
environment has given this allocation up" is replaced by "the local thread won
the CAS", and the environment's inaction is *derived*.

> [!NOTE]
> This does not make `rdisowned` redundant.  It covers handoffs with no lock at
> all -- publication, transfer, an object that is simply never shared again --
> and §9.1 composes it with §8 over a program in which no CAS appears.  What
> §11.2 shows is that one common use of it is a theorem, and so that the
> assumption is dischargeable rather than merely plausible.

The proof is in three moves, and the middle one is the only new work:

1.  The acquire's write makes `1` coherence-latest at the lock (`latestIs_push`,
    from §11.1).
2.  The critical section's own store is at a different address, so the lock
    invariant survives it (`latestIs_push_ne`, below).  This is why `a ≠ lk` is
    a hypothesis and not pedantry.
3.  Each environment step therefore fails its CAS, by `lock_is_exclusive`'s
    argument -- and having failed, writes nothing at all.

Note how much *stronger* the conclusion of step 3 is than §9's.  `EnvPost.frozen`
says Remote appended nothing *at the protected allocation*; `LockedEnvPost.quiet`
says Remote appended nothing, full stop.  A disciplined environment that cannot
take the lock never gets as far as choosing an address.  That makes the freshness
argument at the end pure arithmetic about `mem.size`, where §9 had to appeal to
ownership. -/

/-! ### One more fact about memory

`latestIs_push` says a push *at* `a` makes the pushed value latest.  What the
protection argument needs is the complementary fact: a push *elsewhere* leaves
`a`'s latest value alone.  That is what lets the lock invariant survive the
critical section's own stores. -/

theorem latestIs_push_ne {mem : Memory} {a : Address} {v : Val} (m : Msg)
    (hne : m.loc ≠ a) (hl : LatestIs mem a v) :
    LatestIs (mem.push m) a v := by
  obtain ⟨t, m0, hm0, hloc0, hv0, hb0⟩ := hl
  have hlt : t < mem.size := lt_size_of_getElem? hm0
  refine ⟨t, m0, ?_, hloc0, hv0, ?_⟩
  · rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]; exact hm0
  -- Nothing at `a` lies above `t`.  Below the old top that is `hb0`; at the old
  -- top it is `hne`.
  · rw [betweenAt] at hb0 ⊢
    simp only [Bool.not_eq_true, List.any_eq_false] at hb0 ⊢
    intro t' ht'
    simp only [List.mem_range] at ht'
    have hsz : (mem.push m).size = mem.size + 1 := by simp
    rw [hsz] at ht'
    rcases Nat.lt_or_ge t' mem.size with hlt' | hge'
    · -- Below the old top: reuse `hb0`.  Its bound is `mem.size` and ours is
      -- `mem.size + 1`, so the disjunct that differs has to be discharged by
      -- `hlt'` rather than matched up.
      have h := hb0 t' (by simp [List.mem_range, hlt'])
      rw [Array.getElem?_push_lt hlt', ← Array.getElem?_eq_getElem hlt']
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl h)
      · omega
      · exact Or.inr h
    · -- At the old top: the pushed message is not at `a`.
      have ht'e : t' = mem.size := Nat.le_antisymm (by omega) hge'
      subst ht'e
      simp only [Array.getElem?_push_size]
      simp only [Bool.and_eq_false_iff]
      right
      simpa using hne

/-! ### A protocol-respecting environment

`renv` is a *free* environment: it writes wherever it likes, and §9 stops it
only by `rdisowned`, which is an assumption.  This is the other kind of
environment -- one that runs the same protocol the local thread does, and
touches the protected data only while holding the lock.

Kept as its own operation rather than a fourth `renv` action, for the same
reason `rcas` was: `renv`'s oracle triple is `(address, act = oracle % 3,
operand)`, and six scenarios in §7--§10 are tuned to that modulus.  A fourth
action would silently retune all of them.

Note what is *not* assumed.  `ra.addr.label` need not be in `rdisowned` -- the
whole point is that protection comes from the lock instead. -/

def renvLocked (lk ra : RAddr) (j : Nat) : M Unit := do
  let got ← rcas lk (Val.num 0) (Val.num 1)
  if got then rstore ra j else pure ()

/-- What a protocol-respecting environment step guarantees: **if the lock is
    held, it does nothing to memory at all.**

    One clause, and it is deliberately about `mem` rather than about the
    protected address specifically.  A disciplined environment that cannot take
    the lock cannot write *anything* -- it does not get as far as choosing an
    address -- and that is both stronger and easier to use than a
    per-address statement. -/
structure LockedEnvPost (lk : Address) (s₀ s : Machine) : Prop where
  quiet : LatestIs s₀.mem lk (Val.num 1) → s.mem = s₀.mem
  /-- Remote does not touch Local's views.  `EnvPost` carries the same clause
      for the same reason (§7): it is what makes an environment step free in an
      ordering argument.  Here it is unguarded, because it is true whether or
      not the lock was taken. -/
  vs : s.vs = s₀.vs
  /-- Nor Local's promises, also unguarded.  §17 needs this one inside a loop:
      see `RcasPost.promises`. -/
  promises : s.promises = s₀.promises
  /-- Nor Local's `stuck` flag; see `RcasPost.stuck`.  §17's *reader* loop needs
      this one, for the reason that clause records. -/
  stuck : s.stuck = s₀.stuck

/-- A remote store leaves Local's views alone, whether or not the ownership
    guard lets it through.  `EnvPost.vs` says this too, but only for a `ra`
    Remote holds; the protection argument needs it unconditionally, so it is
    proved here about the step function instead of about the rely lemma. -/
theorem rstoreStep_vs (s : Machine) (ra : RAddr) (j : Nat) :
    (rstoreStep s ra j).vs = s.vs := by
  rw [rstoreStep]; split <;> rfl

/-- And it leaves Local's promises alone, for the same reason and with the same
    shape of proof.  See `RcasPost.promises` for why this is needed. -/
theorem rstoreStep_promises (s : Machine) (ra : RAddr) (j : Nat) :
    (rstoreStep s ra j).promises = s.promises := by
  rw [rstoreStep]; split <;> rfl

/-- And Local's `stuck` flag.  Third of the same shape; see `RcasPost.stuck`. -/
theorem rstoreStep_stuck (s : Machine) (ra : RAddr) (j : Nat) :
    (rstoreStep s ra j).stuck = s.stuck := by
  rw [rstoreStep]; split <;> rfl

@[spec]
theorem renvLocked_spec (lk ra : RAddr) (j : Nat) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    renvLocked lk ra j
    ⦃⇓ _ s => ⌜LockedEnvPost lk.addr s₀ s⌝⦄ := by
  -- `rstore` is unfolded rather than left to `rstore_spec`, because
  -- `rstore_spec`'s conclusion is guarded by `ra ∈ rknow` and `vs` is not.
  mvcgen [renvLocked, rstore]
  · -- The acquire succeeded.  Under the hypothesis that the lock is held that
    -- is impossible, so `quiet` is vacuous -- which is exactly
    -- `lock_is_exclusive`'s argument, reused as a lemma about one step.
    -- Seven names, and the seventh matters: unfolding `rstore` leaves the
    -- result pair as a `let`, which `rename_i` counts.
    rename_i sA hA r hrt s1 hrcas _t
    subst hA
    simp +zetaDelta only []
    refine ⟨fun hheld => ?_, ?_, ?_, ?_⟩
    · obtain ⟨tr, m, hm, hloc, hv, hbt⟩ := hrcas.ok hrt
      have hnv : (Val.num 1 : Val) ≠ Val.num 0 := by simp
      exact (cas_cannot_match hheld hnv hm hloc hv hbt).elim
    · rw [rstoreStep_vs]; exact hrcas.vs
    · rw [rstoreStep_promises]; exact hrcas.promises
    · rw [rstoreStep_stuck]; exact hrcas.stuck
  · -- The acquire failed, so it wrote nothing and the `rstore` never ran.
    rename_i sA hA r hrf s1 hrcas
    subst hA
    exact ⟨fun _ => hrcas.fail (by simpa using hrf), hrcas.vs, hrcas.promises,
      hrcas.stuck⟩

/-! ### The theorem

This is `owned_load_reads_own_write` (§9) with the assumption discharged.
There, `a.label ∈ s.rdisowned` was a hypothesis and the environment was
forbidden by fiat.  Here the only hypothesis is that the local thread took the
lock, and the environment is forbidden because it *cannot take the lock* --
which is `lock_is_exclusive`, and is a theorem about `mcas`.

The two `renvLocked` steps are uncontrolled: any address, any value, any oracle.

`a ≠ lk` is needed and is not pedantry: the critical section's own store must
not be the thing that releases the lock. -/

theorem lock_protects_data (lk : Address) (lkra : RAddr) (ra : RAddr)
    (a : Address) (v : Val) (s₀ : Machine)
    (hlk : lkra.addr = lk) (hne : a ≠ lk) (hp : s₀.promises = []) :
    ⦃fun s => ⌜s = s₀⌝⦄
    (do let got ← acquire lk
        mstore a v
        renvLocked lkra ra 0
        renvLocked lkra ra 0
        let r ← mload a
        pure (got, r))
    ⦃⇓ res s => ⌜res.1 = true → (s.stuck = true ∨ res.2.val = v)⌝⦄ := by
  subst hlk
  mvcgen [acquire]
  -- Five operations: acquire, the protected store, two environment steps, the
  -- read back.  The states are named for the program points between them.
  name_hyps Post hcas hstore henv1 henv2 hload
  name_hyps Machine _ s1 s2 s3 s4 ..
  name_hyps Eq hA ..
  subst hA
  intro hgot
  obtain ⟨⟨mv, hmem1⟩, _, hprom1, _, _⟩ := hcas.append hgot hp
  obtain ⟨hmem2, hcoh2, _, _⟩ := hstore.append hprom1
  -- **The lock is held, and stays held.**  Taking it wrote `1`, which is
  -- therefore coherence-latest; the critical section's own store is at a
  -- different address, so it does not disturb that.
  have hlat1 : LatestIs s1.mem lkra.addr (Val.num 1) := by
    rw [hmem1]; exact latestIs_push _ _ _ _
  have hlat2 : LatestIs s2.mem lkra.addr (Val.num 1) := by
    rw [hmem2]; exact latestIs_push_ne _ hne hlat1
  -- **So the environment did nothing.**  Not "nothing to `a`" -- nothing at
  -- all.  This is the step §9 had to assume.
  have hm3 : s3.mem = s2.mem := henv1.quiet hlat2
  have hlat3 : LatestIs s3.mem lkra.addr (Val.num 1) := by rw [hm3]; exact hlat2
  have hm4 : s4.mem = s2.mem := by rw [henv2.quiet hlat3, hm3]
  -- The rest is §9's argument, only easier: memory is *literally unchanged*
  -- across the environment, so "nothing above the write is at `a`" is
  -- arithmetic about `mem.size` rather than an appeal to `frozen`.
  have hD4 : s4.mem[s1.mem.size]? = some ⟨a, v, mstoreView s1 [] false⟩ := by
    rw [hm4, hmem2]; simp
  have hsz : s2.mem.size = s1.mem.size + 1 := by rw [hmem2]; simp
  have hfroz : ∀ (t' : Ts) (m' : Msg), s4.mem[t']? = some m' → m'.loc = a →
      t' ≤ s1.mem.size := by
    intro t' m' hm' _
    have hlt := lt_size_of_getElem? hm'
    rw [hm4, hsz] at hlt
    exact Nat.le_of_lt_succ hlt
  -- Remote did not touch Local's views either, so the bound is the one §6
  -- computed.  This is what `LockedEnvPost.vs` is for.
  have hb : s1.mem.size ≤ loadBound s4 a [] := by
    have hc : s4.vs.coh a = s1.mem.size := by rw [henv2.vs, henv1.vs, hcoh2]
    rw [← hc]
    unfold loadBound
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  rcases hload.read with hstuck | ⟨_, hnone⟩ | ⟨hmsg, hr⟩
  · exact Or.inl hstuck
  · exfalso
    have hcontra := hnone s1.mem.size
    rw [readable_top_of_frozen hD4 rfl hfroz] at hcontra
    simp at hcontra
  · right
    have ht := readable_eq_of_frozen hD4 rfl hb hfroz hr
    rw [ht, hD4] at hmsg
    simp at hmsg
    exact hmsg.1.symm

/-! ### The control

Every "the environment cannot disturb this" result is satisfied by an
environment that does nothing, and `renvLocked` is exactly the kind of
environment that might be doing nothing for the wrong reason.  So run the same
program both ways, with the same adversary, under the same oracle.

The control is the honest one: Local still *looks* at the lock, and still
believes it holds it.  What it does not do is win a CAS.  So the two rows
differ in one instruction, the environment is identical in both, and the oracle
is consumed identically -- a `mload` and a `mcas` each take one entry. -/

def protectScenario (localLocks : Bool) : String :=
  let l : Address := ⟨0, 0⟩
  let d : Address := ⟨1, 0⟩
  let lra : RAddr := ⟨l, 0⟩
  let dra : RAddr := ⟨d, 0⟩
  let s0 : Machine :=
    { mem := #[⟨l, Val.num 0, 0⟩, ⟨d, Val.num 0, 0⟩], sizes := [1, 1],
      roots := [l, d], rknow := [lra, dra],
      -- One entry each for: the acquire (or the read that stands in for it),
      -- the data store, the two environment CASes, and the load -- which is
      -- steered to the *last* readable timestamp, so it finds Remote's write
      -- whenever there is one.
      oracle := [0, 0, 0, 0, 9] }
  let prog : M (Bool × TVal) := do
    let got ← if localLocks then acquire l
              else do let _ ← mload l; pure true
    mstore d (Val.num 7)
    renvLocked lra dra 0
    renvLocked lra dra 0
    let r ← mload d
    pure (got, r)
  let ((got, r), s) := prog.run s0
  s!"local-locks={localLocks}: acquired={got}, read={repr r.val}, " ++
  s!"mem {s0.mem.size}→{s.mem.size}, stuck={s.stuck}"

def protectDemo : String :=
  "  " ++ protectScenario false ++ "\n  " ++ protectScenario true

/-! ## 11.3 The seqlock, and ordering without exclusion

Every protection result so far has had the same shape: *the environment cannot
write*.  §9 assumed it, §11.2 derived it from a lock.  A seqlock has no such
property and cannot be given one -- the writer takes no lock the reader
respects, the reader takes no lock at all, and the two genuinely run
concurrently over the same words.  What a seqlock promises instead is that the
reader **finds out**: it reads a counter, reads the data, re-reads the counter,
and accepts only if the two agree.

So the theorem cannot say "the data did not change".  It says:

> if the reader's data read saw anything from inside the transaction, its
> validating read is forced to see the transaction open.

which is the same guarantee, moved from exclusion to detection, and it is
the first result here that is about *ordering* rather than about permission.

### Who is Local, and why it is not the obvious way round

The reader is the interesting party, so the tempting assignment is reader =
Local.  That is **wrong**, and the reason is worth recording because the
mistake is invisible once made.

Remote's stores append to the global array in program order -- the "Remote does
not promise" gap (§7).  With Remote as the writer, the array order would hand
the reader a store→store ordering that the writer's `dmb ishst` is supposed to
provide, and the theorem would come out *true in the model and false on the
machine*: on real hardware an unfenced writer's data write can be observed
before its counter write.  Local's stores go through the promise machinery,
which is validated against herd7, so:

**Writer = Local, reader = Remote.**  It is the reverse of §11.2, and it is
forced by which agent's reordering the model is entitled to claim.

`RLoadPost.rdView` is the same guard at the level of a single clause: it
exposes the *view* a remote read absorbed and deliberately not its timestamp,
so that a proof cannot reach for the array order by accident.

### What had to be added

Nothing here is new physics -- it is the reader-side mirror of machinery that
already existed on the writer side, and it was missing for a specific reason:
**no earlier theorem ordered one load against another through a fence.**  §8's
reader is ordered by an address dependency, which reaches `loadBound` through
`tvView deps` and never touches `vRd`.  A seqlock's validating read has nothing
to depend on -- its address was known before the protocol started.

| Piece | Mirror of |
|---|---|
| `LoadPost.rd` | `StorePost.append`'s `s₀.mem.size ≤ s.vs.vWr` |
| `FencePost.pre` | `FencePost.rel` |
| `rfence`, `RFencePost` | `mfence`, `FencePost` |
| `RLoadPost.rdView` / `rdMono` | `LoadPost.rd`, weakened on purpose |

### The two fences

The theorem's two conjuncts are one fence each, which is why they are stated
together over one program:

1.  **The writer's `dmb ishst`** puts the opening write into the data word's
    message view.  Without it a reader that sees the data has been told nothing
    about the counter.
2.  **The reader's `dmb ishld`** turns that view into a bound on the validating
    read.  Without it the reader may accept a counter value it read from before
    the transaction began.

> [!NOTE]
> **This section once recorded a gap here, and closing it was a model fix.**
> As first written, the control witnessed the *reader's* fence but not the
> writer's: dropping the `mfence .st` changed nothing executable, because the
> reader's bound arrived by a shorter route -- `rloadStep` folded the raw read
> timestamp `t` into Remote's `vRd`, so array order was doing the work the
> writer's fence is supposed to do.
>
> That shortcut was unsound, for the reason at the top of this section:
> Remote's stores append in program order, so its timestamps are not an
> ordering the machine provides.  `rloadStep` now absorbs `m.view` only.
> Remote is strictly weaker as a result (a smaller `vRd` bounds fewer reads),
> which is the safe direction, and it is what "Remote does not promise" should
> have meant all along.
>
> The change altered exactly one line of the whole report: the writer-fence
> row of the demo below, which now tears.  Both fences are counterexamples and
> the proof is unchanged, because `RLoadPost.rdView` had been shaped to keep
> the shortcut out of proofs even while the step still took it.
>
> The note used to end by saying the other half of the gap was unfixable here,
> because `M` had no way to promise.  That was wrong twice over: `mpromise`
> exists, and the missing piece was rule 3 rather than rules 1 and 2.  "The
> writer, reordered" below is what the gap actually wanted. -/

theorem seqlock_validation_detects
    (d1 : Address) (v : Val) (rsq rd1 : RAddr) (s₀ : Machine)
    (hne : d1 ≠ rsq.addr) (hp : s₀.promises = []) :
    ⦃fun s => ⌜s = s₀⌝⦄
    (do mstore rsq.addr (Val.num 1)
        mfence .st
        mstore d1 v
        let a ← rload rd1
        rfence .ld
        let b ← rload rsq
        pure (a, b))
    ⦃⇓ res s => ⌜(∀ m, s.mem[s₀.mem.size + 1]? = some m → s₀.mem.size ≤ m.view)
        ∧ (∀ ma mb, res.1 = some ma → res.2 = some mb →
             s₀.mem.size ≤ ma.view → mb.val = Val.num 1)⌝⦄ := by
  mvcgen
  -- Six operations: the writer's counter store, its `dmb ishst`, its data
  -- store, then the reader's data load, its `dmb ishld` and its validating
  -- load.  The states are named for the program points between them.
  name_hyps Post hst1 hf hst2 hrl1 hrf hrl2
  name_hyps Machine sA _ s2 s3 s4 s5 s6
  name_hyps Eq hA ..
  subst hA
  obtain ⟨hmem1, _hcoh1, hprom1, hwr1⟩ := hst1.append hp
  obtain ⟨hmem2, _hcoh2, _, _⟩ := hst2.append (by rw [hf.promises]; exact hprom1)
  -- Memory after the writer, and unchanged by everything Remote did.
  have hmem3 : s3.mem
      = (sA.mem.push ⟨rsq.addr, Val.num 1, mstoreView sA [] false⟩).push
          ⟨d1, v, mstoreView s2 [] false⟩ := by
    rw [hmem2, hf.mem, hmem1]
  have hm5 : s5.mem = s3.mem := by rw [hrf.mem, hrl1.mem]
  have hm6 : s6.mem = s3.mem := by rw [hrl2.mem, hm5]
  have hopen : s5.mem[sA.mem.size]?
      = some ⟨rsq.addr, Val.num 1, mstoreView sA [] false⟩ := by
    rw [hm5, hmem3, Array.getElem?_push_lt (by simp)]
    simp
  have hdata : s5.mem[sA.mem.size + 1]?
      = some ⟨d1, v, mstoreView s2 [] false⟩ := by
    rw [hm5, hmem3]
    have hs : (sA.mem.push (⟨rsq.addr, Val.num 1, mstoreView sA [] false⟩ : Msg)).size
        = sA.mem.size + 1 := by simp
    rw [← hs]
    exact Array.getElem?_push_size
  refine ⟨?_, ?_⟩
  · -- **The writer's `dmb ishst`.**  The data word's message view covers the
    -- write that opened the transaction, so a reader that sees the data has
    -- already been told about the counter.
    intro m hm
    rw [hm6, ← hm5, hdata] at hm
    rw [← Option.some.inj hm]
    exact Nat.le_trans (Nat.le_trans hwr1 (hf.rel (by simp)))
      (mstoreView_ge_rel s2 [] false)
  · -- **The reader's `dmb ishld`.**  Whatever view the data read absorbed
    -- bounds the validating read, which therefore cannot reach back past the
    -- opening write.
    intro ma mb hma hmb hview
    have hrd : sA.mem.size ≤ s4.rvs.vRd := Nat.le_trans hview (hrl1.rdView ma hma)
    have hpre : sA.mem.size ≤ s5.rvs.vPreBase := Nat.le_trans hrd (hrf.pre (by simp))
    have hb : sA.mem.size ≤ rloadBound s5 rsq := by
      refine Nat.le_trans hpre ?_
      unfold rloadBound
      exact Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    obtain ⟨t, hmt, hrt⟩ := hrl2.read mb hmb
    rcases Nat.lt_trichotomy t sA.mem.size with hlt | heq | hgt
    · -- Below the opening write, and hidden by it.
      rw [not_readable_of_later hlt hb hopen rfl] at hrt
      simp at hrt
    · -- The opening write itself, which is the conclusion.
      rw [heq, hopen] at hmt
      rw [← Option.some.inj hmt]
    · -- Above it: the only message there is the data word, at a different
      -- address, and `readable` insists on the address.
      exfalso
      have hsz : s5.mem.size = sA.mem.size + 2 := by rw [hm5, hmem3]; simp
      have hlt2 : t < sA.mem.size + 2 := hsz ▸ lt_size_of_getElem? hmt
      have ht : t = sA.mem.size + 1 :=
        Nat.le_antisymm (Nat.le_of_lt_succ hlt2) hgt
      rw [ht, hdata] at hmt
      obtain ⟨m', hm', hloc'⟩ := msg_of_readable hrt
      rw [ht, hdata] at hm'
      exact hne (by rw [← hloc', ← Option.some.inj hm'])

/-! ### The control -/

def seqShow (m : Option Msg) : String :=
  match m with
  | none => "nothing"
  | some m => toString (repr m.val)

def seqlockScenario (writerFence readerFence : Bool) : String :=
  let sq : Address := ⟨0, 0⟩
  let d : Address := ⟨1, 0⟩
  let rsq : RAddr := ⟨sq, 0⟩
  let rd : RAddr := ⟨d, 0⟩
  let s0 : Machine :=
    { mem := #[⟨sq, Val.num 0, 0⟩, ⟨d, Val.num 0, 0⟩], sizes := [1, 1],
      roots := [sq, d], rknow := [rsq, rd],
      -- Two store choices (one candidate each), then the reader's two picks:
      -- the data read is steered to the *newest* timestamp and the validating
      -- read to the *oldest*, which is the adversarial combination.
      oracle := [0, 0, 9, 0] }
  let prog : M (Option Msg × Option Msg) := do
    mstore sq (Val.num 1)
    if writerFence then mfence .st else pure ()
    mstore d (Val.num 7)
    let a ← rload rd
    if readerFence then rfence .ld else pure ()
    let b ← rload rsq
    pure (a, b)
  let ((a, b), _s) := prog.run s0
  let torn := match a, b with
    | some ma, some mb => decide (ma.val = Val.num 7 ∧ mb.val = Val.num 0)
    | _, _ => false
  s!"writer-fence={writerFence}, reader-fence={readerFence}: " ++
  s!"data={seqShow a}, validate={seqShow b}, torn-accepted={torn}"

def seqlockDemo : String :=
  "  " ++ seqlockScenario true false ++ "\n  " ++
  seqlockScenario false true ++ "\n  " ++
  seqlockScenario true true

/-! ### The writer, reordered

The three rows above vary the fences and let the writer's two stores land in
program order.  That is the weaker half of what a store→store fence forbids.
The other half is the one the model is actually built for: the writer's data
write landing **before** its counter write, with nothing executed out of
order, which in §2.3's terms is a promise.

The two rows below are the same program with the data store promised, and the
reader's `dmb ishld` always present, so that the only variable is the writer's
`dmb ishst`.  What makes them worth printing is that **the observable outcome
is identical**: both read the promised data message and validate against the
stale counter, so both tear.  The fence changes nothing a reader can see.

What it changes is whether the run is a run.  Fulfilment requires
`mstoreView s deps rel ≤ m.view` -- side condition 1 of §2.5 -- and after a
`dmb ishst` the store's view has risen above the view the promise was made
with, so the store cannot take the promised timestamp.  It appends instead,
the promise stays outstanding, and rule 3 discards the whole execution.

This is the demo that made rule 3 necessary in the front end rather than
merely tidy.  Read the rows without the `behaviour=` column and the writer's
fence looks inert; that is exactly the mistake the §11.3 note above records
finding once already, by a different route. -/

/-- **A store after `dmb ishst` cannot keep a promise made before it.**  The
    fence raises `vRelSt`, which is what a plain store publishes, above the
    view the promised message carries -- and a store may not publish more than
    the promise already published.

    One line of `fulfillable`, but it is the line the rows below turn on, and
    stating it separately is what makes those rows a consequence rather than
    an observation. -/
theorem no_fulfil_after_release_fence (s : Machine) (a : Address) (v : Val)
    (t : Ts) (m : Msg) (ht : s.mem[t]? = some m) (hview : m.view < s.vs.vRelSt) :
    t ∉ fulfillable s a v [] false := by
  intro hmem
  have h := (List.mem_filter.1 hmem).2
  rw [ht] at h
  simp [mstoreView, tvView] at h
  -- `omega` will not take this: the conjunction it sits in also contains
  -- equations between addresses and values, and omega skips a hypothesis it
  -- cannot read whole.
  exact absurd h.1.2 (Nat.not_le.2 hview)

def seqlockPromiseScenario (writerFence : Bool) : String :=
  let sq : Address := ⟨0, 0⟩
  let d : Address := ⟨1, 0⟩
  let rsq : RAddr := ⟨sq, 0⟩
  let rd : RAddr := ⟨d, 0⟩
  let s0 : Machine :=
    { mem := #[⟨sq, Val.num 0, 0⟩, ⟨d, Val.num 0, 0⟩], sizes := [1, 1],
      roots := [sq, d], rknow := [rsq, rd],
      -- The counter store (no choice available), the data store (`1` = fulfil
      -- the promise if that is legal), the data read (`1` = the promised
      -- message, which is present either way), and the validating read (`0` =
      -- the oldest counter value).  Both rows use the same oracle, which is
      -- the point: the adversary makes the same choices.
      oracle := [0, 1, 1, 0] }
  let prog : M (Option Msg × Option Msg) := do
    mpromise d (Val.num 7) 0
    mstore sq (Val.num 1)
    if writerFence then mfence .st else pure ()
    mstore d (Val.num 7)
    let a ← rload rd
    rfence .ld
    let b ← rload rsq
    pure (a, b)
  let ((a, b), s) := prog.run s0
  let torn := match a, b with
    | some ma, some mb => decide (ma.val = Val.num 7 ∧ mb.val = Val.num 0)
    | _, _ => false
  s!"writer-fence={writerFence}, data-promised: data={seqShow a}, " ++
  s!"validate={seqShow b}, torn={torn}, outstanding={s.promises}, " ++
  s!"behaviour={s.exhibits}"

def seqlockPromiseDemo : String :=
  "  " ++ seqlockPromiseScenario false ++ "\n  " ++
  seqlockPromiseScenario true

/-! ### ... and the same thing as a theorem

The row above is one oracle, two addresses and one value.  The claim it is
evidence for is bigger, and here it is: **a writer that promises its data
write, then separates it from the counter write with `dmb ishst`, has no run
at all.**  Not "no torn run" -- no run: the promise is still outstanding when
the program ends, and rule 3 throws the execution away.

It is the first theorem in this file that mentions a promise, which is why
`PromisePost` had to exist (§5).  Four operations, composed by `mvcgen` from
the four specs, with nothing unfolded -- the same shape as
`publish_orders_data_before_flag`, and deliberately so: `publish` is this
program with the fence doing its job, and this is the same program with the
writer trying to cheat.

The three hypotheses are exactly the ones the seqlock supplies: nothing is
promised yet, the counter and the data are different objects, and the promise
names a view that already exists.  Notice what is *not* assumed -- nothing
about the oracle.  The adversary may resolve every other choice however it
likes. -/

/-- The writer of §11.3's seqlock, promising its data write.  `view` is what a
    reader inheriting the promised message will get; `mpromise` requires it to
    name a message that already exists, which is what `hview` below says. -/
def promisedWriter (sq d : Address) (v : Val) (view : Ts) : M Unit := do
  mpromise d v view
  mstore sq (Val.num 1)
  mfence .st
  mstore d v

/-- **The fenced promising writer exhibits no behaviour.**  The promised
    timestamp is still outstanding in the final state, so `exhibits` is false
    however the oracle resolved everything else.

    The argument is three steps and each is one field of one `Post`:

    1.  the counter store is at a different address, so the promise is not a
        candidate for it, so it appends (`StorePost.grew`) and `vWr` rises
        above the promised message's view;
    2.  the fence publishes `vWr` into `vRelSt` (`FencePost.rel`), which puts
        the promised view strictly below what a plain store must publish;
    3.  the data store therefore has no candidate (`no_fulfil_after_release_fence`)
        and keeps every promise it had (`StorePost.keep`).

    Step 3 is the one that needed new machinery.  `StorePost` used to say only
    what happened when nothing could be fulfilled; `keep` is what lets a proof
    say that a particular promise *survived* a store. -/
theorem fenced_writer_cannot_discharge (sq d : Address) (v : Val) (view : Ts)
    (s₀ : Machine) (hclean : s₀.promises = []) (hne : sq ≠ d)
    (hview : view < s₀.mem.size) :
    ⦃fun s => ⌜s = s₀⌝⦄
    promisedWriter sq d v view
    ⦃⇓ _ s => ⌜s₀.mem.size ∈ s.promises ∧ s.exhibits = false⌝⦄ := by
  mvcgen [promisedWriter]
  name_hyps Post hprom hstore hfence ..
  intro hlast
  rename_i sA hA _ s1 _ s2 _ s3 _ s4
  subst hA
  -- The promise is in memory, at a timestamp that is outstanding.
  obtain ⟨hmem1, hp1⟩ := hprom.made hview
  have hmsg1 : s1.mem[sA.mem.size]? = some ⟨d, v, view⟩ := by rw [hmem1]; simp
  -- The counter store is at another address, so it cannot take that timestamp.
  have hf1 : fulfillable s1 sq (Val.num 1) [] false = [] := by
    rw [fulfillable, hp1, hclean]
    simp [hmsg1, Ne.symm hne]
  obtain ⟨_, _, hp2, hvw2⟩ := hstore.grew hf1
  -- ... and it appends, which pushes `vWr` past the promised message's view.
  have hlt : view < s2.vs.vWr :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hview (by rw [hmem1]; simp)) hvw2
  -- The fence publishes `vWr`, so the promised view is now strictly below it.
  have hrel : view < s3.vs.vRelSt := Nat.lt_of_lt_of_le hlt (hfence.rel (by simp))
  have hmsg3 : s3.mem[sA.mem.size]? = some ⟨d, v, view⟩ :=
    hfence.ext.msg (hstore.ext.msg hmsg1)
  have hin3 : sA.mem.size ∈ s3.promises := by
    rw [hfence.promises, hp2, hp1, hclean]; simp
  -- So the data store has no candidate to fulfil, and the promise survives it.
  have hin4 : sA.mem.size ∈ s4.promises :=
    hlast.keep _ hin3 (no_fulfil_after_release_fence s3 d v _ _ hmsg3 hrel)
  refine ⟨hin4, ?_⟩
  have : s4.promises ≠ [] := by intro h; rw [h] at hin4; simp at hin4
  simp [Machine.exhibits, Machine.discharged, this]

-- The demo row above is this theorem's `sq = ⟨0,0⟩`, `d = ⟨1,0⟩`,
-- `v = num 7`, `view = 0` instance, with a reader appended.
#print axioms fenced_writer_cannot_discharge

-- Without the fence the theorem is false, and this is the witness: the same
-- writer with `dmb ishst` removed does discharge its promise.
#guard
  let sq : Address := ⟨0, 0⟩
  let d : Address := ⟨1, 0⟩
  let s0 : Machine :=
    { mem := #[⟨sq, Val.num 0, 0⟩], sizes := [1, 1], oracle := [0, 1] }
  let prog : M Unit := do
    mpromise d (Val.num 7) 0
    mstore sq (Val.num 1)
    mstore d (Val.num 7)
  (prog.run s0).2.exhibits



/-! ### 11.4 The two-word compare-and-swap

`mcas` makes one word atomic.  The atomicity ladder has a second row --
two adjacent words -- and for most of this project's life that row was going to
be *derived* from the lock of §11.1, because a probe said herd7 forbade nothing
about `CASP` that a pair of `CAS`es did not already forbid.

That probe was right about herd7 and wrong about the architecture.  Stock
`aarch64.cat` decomposes a `CASP` into two independent single-word RMWs
(`AArch64Sem.ml`, `casp`), and its failure path writes the already-present value
back *per location*, which lets a losing thread overwrite half of a winner's
pair.  `cats/aarch64-pair.cat` adds the axiom that stops it -- and a second one,
later, for the observer that reads the pair with two ordinary loads rather than
one pair access (`pairTop` in §2 is this model's half of it).
With them the pair tests come out `Never` where they should.  So the row is
primitive after all, and this section is its front end.

Two properties, and they come from different places -- which is the whole
content of the section:

* **The writes land together.**  Free, by construction: both messages are
  pushed in one step at `mem.size` and `mem.size + 1`, and per-location
  adjacency does the rest.  If a pair lands at `(n, n+1)` and a second pair
  reads `t0 = n` but `t1 < n+1`, the second one's write to the second word
  cannot be adjacent to `t1`, because the first pair's write at `n+1` is in the
  way.  A half-committed pair is not expressible.
* **The reads are a consistent snapshot.**  Not free.  A *failing* pair CAS
  writes nothing, so adjacency constrains nothing and its two reads would
  otherwise be free to come from either side of somebody else's pair write.
  `pairStraddles` is that rule, and `CasPairPost.snapshot` is what it buys.

The second is the one that matters for clients, because it is the one a pair of
single-word CASes does not give you.

**What is not here.**  `LDXP`/`STXP` are out of scope (a settled design decision): we
model `CASP`, i.e. FEAT_LSE.  On x86 the corresponding instruction is
`CMPXCHG16B`, which herd7 does not implement at all -- not the semantics, not
even the mnemonic -- so `wellFormed` rejects a pair RMW on the `tso` front end
and the architectural claim for x86 rests on the SDM rather than on a checked
model. -/

/-- The views after the read half of a pair: `casReadVs` at both words at once.

    Both coherence entries move, because both words were read.  A pair read is
    a read of `a` *and* of `a.next`, and a later access to either is ordered
    after it. -/
def casPairReadVs (s : Machine) (a : Address) (acq : Bool) (t0 t1 : Ts) : VState :=
  let m0 := casMsg s a t0
  let m1 := casMsg s a.next t1
  { s.vs with
    coh := fun b =>
      if b = a then max (s.vs.coh a) t0
      else if b = a.next then max (s.vs.coh a.next) t1
      else s.vs.coh b
    vRd := max s.vs.vRd (max (rdV s.vs s.pairs t0 m0.view) (rdV s.vs s.pairs t1 m1.view))
    vPreBase :=
      if acq then max s.vs.vPreBase (max (acqV s.vs s.pairs t0 m0.view) (acqV s.vs s.pairs t1 m1.view))
      else s.vs.vPreBase }

/-- Where a successful pair CAS that read `(t0, t1)` may put its writes,
    identified by the timestamp of the *first* word; the second is always the
    next one.

    `casSlots` with everything doubled, plus the one thing that is genuinely
    new: a promised slot is usable only if `tw + 1` is promised too.  A pair
    discharges two promises or none.  There is no state in which half a pair is
    outstanding, which is the same statement as "no state in which half a pair
    is visible". -/
def casPairSlots (s : Machine) (a : Address) (new0 new1 : Val) (deps : List TVal)
    (rel acq : Bool) (t0 t1 : Ts) : List Ts :=
  let rvs := casPairReadVs s a acq t0 t1
  let mv := casView rvs deps rel
  (if rmwAdjacent s.mem a t0 s.mem.size &&
      rmwAdjacent s.mem a.next t1 (s.mem.size + 1) then [s.mem.size] else []) ++
  s.promises.filter fun tw =>
    s.promises.contains (tw + 1) &&
    (s.mem[tw]?.elim false fun m => m.loc == a && m.val == new0 && mv ≤ m.view) &&
    (s.mem[tw + 1]?.elim false fun m =>
      m.loc == a.next && m.val == new1 && mv ≤ m.view) &&
    decide (casOb s.arch rvs a deps ≤ tw) &&
    rmwAdjacent s.mem a t0 tw && rmwAdjacent s.mem a.next t1 (tw + 1)

/-- Every outcome of one pair CAS: which two messages it read, and where its
    writes went.  `none` is a failed compare.

    Torn snapshots are filtered out *before* the comparison, so they are not
    outcomes at all -- not even failing ones.  That is the point: a pair CAS
    that read half of one update and half of another has not read anything the
    machine is willing to call a value of the pair. -/
def casPairOutcomes (s : Machine) (a : Address) (cmp0 cmp1 new0 new1 : Val)
    (deps : List TVal) (rel acq : Bool) : List ((Ts × Ts) × Option Ts) :=
  (readCands s a deps).flatMap fun t0 =>
    (readCands s a.next deps).flatMap fun t1 =>
      if pairStraddles s.mem s.pairs a t0 t1 then []
      else if (casMsg s a t0).val = cmp0 ∧ (casMsg s a.next t1).val = cmp1 then
        (casPairSlots s a new0 new1 deps rel acq t0 t1).map fun tw =>
          ((t0, t1), some tw)
      else [((t0, t1), none)]

/-- The effect of one chosen outcome.

    `pairs` grows only on the appending branch.  A fulfilment discharges a pair
    that the promise step already registered -- registering it again would be
    harmless but would say the wrong thing, namely that the pair became visible
    when it was fulfilled rather than when it was promised. -/
def casPairApply (s : Machine) (a : Address) (new0 new1 : Val) (deps : List TVal)
    (rel acq : Bool) (o : (Ts × Ts) × Option Ts) : Machine :=
  let rvs := casPairReadVs s a acq o.1.1 o.1.2
  match o.2 with
  | none => { s with vs := rvs }
  | some tw =>
      let mv := casView rvs deps rel
      { s with
        mem := if tw = s.mem.size then
                 (s.mem.push ⟨a, new0, mv⟩).push ⟨a.next, new1, mv⟩
               else s.mem
        pairs := if tw = s.mem.size then s.pairs ++ [tw] else s.pairs
        promises := if tw = s.mem.size then s.promises
                    else (s.promises.erase tw).erase (tw + 1)
        vs := { rvs with
                coh := fun b =>
                  if b = a then tw else if b = a.next then tw + 1 else rvs.coh b
                vWr := max rvs.vWr (tw + 1), mine := ((tw + 1) - 1) :: (tw + 1) :: rvs.mine } }

/-- Two-word compare-and-swap.  Returns both words as read, and whether it
    succeeded.

    **Both words are returned whether or not it succeeded**, which mirrors the
    instruction: `CASP` writes the loaded pair back into its comparand
    registers either way.  So "both registers hold what I expected" does *not*
    mean "I won" -- `r.2.2` is the only thing that means that.  This confound
    has now cost this project three times, once for `CAS`, once for `SWP`, and
    once for `CASP`, and it is why the boolean is in the return type at all.

    **A pair CAS on an unwritten pair fails**, for the same reason `mcas` does:
    there is nothing for the write to be adjacent to.  A pair must be
    initialised before it can be swapped. -/
def mcasPair (a : Address) (cmp0 cmp1 new0 new1 : Val) (deps : List TVal := [])
    (rel : Bool := false) (acq : Bool := false) : M (TVal × TVal × Bool) := do
  let s ← get
  match casPairOutcomes s a cmp0 cmp1 new0 new1 deps rel acq with
  | [] =>
      modifyGet fun s' =>
        ((TVal.mk0 Val.undef, TVal.mk0 Val.undef, false),
         { s' with stuck := s'.stuck ||
             !allocated s' a || !allocated s' a.next })
  | o :: os =>
      let out ← demonic o os
      modifyGet fun s' =>
        let m0 := casMsg s' a out.1.1
        let m1 := casMsg s' a.next out.1.2
        ((⟨m0.val, m0.view, out.1.1⟩, ⟨m1.val, m1.view, out.1.2⟩, out.2.isSome),
         casPairApply s' a new0 new1 deps rel acq out)

/-! ### The spec -/

/-- What a pair CAS guarantees. -/
structure CasPairPost (a : Address) (cmp0 cmp1 new0 new1 : Val) (deps : List TVal)
    (s₀ : Machine) (r : TVal × TVal × Bool) (s : Machine) : Prop where
  ext : Extends s₀ s
  pub : s.vs.vRelSt = s₀.vs.vRelSt
  roots : s.roots = s₀.roots
  rknow : s.rknow = s₀.rknow
  disowned : s.rdisowned = s₀.rdisowned
  /-- Success means both comparisons matched. -/
  matched : r.2.2 = true → r.1.val = cmp0 ∧ r.2.1.val = cmp1
  /-- A failed pair CAS writes nothing, exactly like a failed `mcas`. -/
  fail : r.2.2 = false → s.mem = s₀.mem ∧ s.promises = s₀.promises ∧
    s.pairs = s₀.pairs
  /-- What was read at each word, and -- in the case where it read at all --
      **the snapshot property, which is the reason this is a primitive**.

      The two words came from timestamps that do not straddle any atomic pair
      write.  A pair of single-word `mcas`es cannot promise this: each is
      atomic on its own word and neither says anything about the other.  This
      is what herd7's `C-read-tear` probe pins down and what stock
      `aarch64.cat` fails to forbid.

      It holds **even when the compare failed**, which is the strong form and
      the one that matters: a failing pair CAS writes nothing, so adjacency
      constrains nothing, and tearing would otherwise be free exactly there.

      It is a conjunct of the last disjunct rather than a clause of its own
      because that is where it is true.  In the first three cases the operation
      did not read a pair -- it was stuck, or one of the two words had nothing
      readable at all -- and both returned timestamps are the placeholder `0`,
      about which nothing can be promised.  A guarantee about a snapshot
      belongs to the case where there was a snapshot. -/
  read : s.stuck = true
    ∨ (r.1.val = Val.undef ∧ r.2.2 = false ∧
       ∀ t, readable s₀.mem a t (loadBound s₀ a deps) = false)
    ∨ (r.2.1.val = Val.undef ∧ r.2.2 = false ∧
       ∀ t, readable s₀.mem a.next t (loadBound s₀ a.next deps) = false)
    ∨ (s₀.mem[r.1.rts]? = some ⟨a, r.1.val, r.1.view⟩ ∧
       readable s₀.mem a r.1.rts (loadBound s₀ a deps) = true ∧
       s₀.mem[r.2.1.rts]? = some ⟨a.next, r.2.1.val, r.2.1.view⟩ ∧
       readable s₀.mem a.next r.2.1.rts (loadBound s₀ a.next deps) = true ∧
       pairStraddles s₀.mem s₀.pairs a r.1.rts r.2.1.rts = false)
  /-- **Atomicity at both words, in the form an exclusion argument uses.**  A
      successful pair CAS with nothing promised appends both writes adjacently,
      and nothing at either word lies above what it read there.

      Note `s.pairs = s₀.pairs ++ [s₀.mem.size]`: the pair is registered, so
      every later reader is held to the snapshot it just created.  Without that
      clause the writes would be atomic and nobody would be obliged to notice. -/
  append : r.2.2 = true → s₀.promises = [] →
    (∃ mv, s.mem = (s₀.mem.push ⟨a, new0, mv⟩).push ⟨a.next, new1, mv⟩) ∧
    s.vs.coh a = s₀.mem.size ∧
    s.vs.coh a.next = s₀.mem.size + 1 ∧
    s.promises = [] ∧
    s.pairs = s₀.pairs ++ [s₀.mem.size] ∧
    s₀.mem.size + 1 ≤ s.vs.vWr ∧
    betweenAt s₀.mem a r.1.rts s₀.mem.size = false ∧
    betweenAt s₀.mem a.next r.2.1.rts (s₀.mem.size + 1) = false

/-! ### A pair CAS never runs out of outcomes either

The `mcas` version of this (`casOutcomes_nil`) turns on the coherence-latest
message being readable and adjacent.  The pair version needs one thing more:
that the *pair* of coherence-latest messages does not straddle.

It does not, and the argument is short once `pairStraddles` is stated the way
it is.  Take `u0` latest at `a` and `u1` latest at `a.next`.  For a recorded
pair `p` to straddle, the predicate itself demands a message at `a` at `p` and
a message at `a.next` at `p + 1`.  Latest-ness then forces `p ≤ u0` and
`p + 1 ≤ u1`, so both sides of the `!=` are `true` and there is no straddle.

This is exactly why `pairStraddles` checks both words rather than relying on
`pairs` having been built correctly: the second conjunct is what supplies
`p + 1` is at `a.next`, and without it this argument would need an invariant
carried through every step of the machine. -/

/-- The coherence-latest messages at the two words of a pair never straddle. -/
theorem pairStraddles_latest (mem : Memory) (pairs : List Ts) (a : Address)
    {u0 u1 : Ts}
    (h0 : betweenAt mem a u0 mem.size = false)
    (h1 : betweenAt mem a.next u1 mem.size = false) :
    pairStraddles mem pairs a u0 u1 = false := by
  rw [pairStraddles, List.any_eq_false]
  intro p _ hc
  rw [Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨hp0, hp1⟩, hne⟩ := hc
  -- `p` holds `a` and `p + 1` holds `a.next`, both read off the predicate
  -- itself rather than from an invariant on how `pairs` was built.
  obtain ⟨m0, hm0⟩ : ∃ m, mem[p]? = some m := by
    cases hq : mem[p]? with
    | none => rw [hq] at hp0; simp at hp0
    | some m => exact ⟨m, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ m, mem[p + 1]? = some m := by
    cases hq : mem[p + 1]? with
    | none => rw [hq] at hp1; simp at hp1
    | some m => exact ⟨m, rfl⟩
  have hloc0 : m0.loc = a := by rw [hm0] at hp0; simpa using hp0
  have hloc1 : m1.loc = a.next := by rw [hm1] at hp1; simpa using hp1
  -- Latest-ness at each word bounds `p` and `p + 1`: a message above the
  -- latest one would be a witness that it was not the latest.
  have hle0 : p ≤ u0 := by
    rcases Nat.lt_or_ge u0 p with h | h
    · rw [betweenAt_of_witness h hm0 hloc0] at h0; simp at h0
    · exact h
  have hle1 : p + 1 ≤ u1 := by
    rcases Nat.lt_or_ge u1 (p + 1) with h | h
    · rw [betweenAt_of_witness h hm1 hloc1] at h1; simp at h1
    · exact h
  -- Both sides of the `!=` are therefore `true`.
  rw [decide_eq_true hle0, decide_eq_true hle1] at hne
  simp at hne

/-- So the outcome list is empty only when one of the two words had nothing
    readable at all.  Neither the straddle filter nor the adjacency requirement
    can empty it on their own: the coherence-latest messages at the two words
    are readable, adjacent, and -- by `pairStraddles_latest` -- not a torn
    snapshot, so they always supply an outcome. -/
theorem casPairOutcomes_nil (s : Machine) (a : Address) (cmp0 cmp1 new0 new1 : Val)
    (deps : List TVal) (rel acq : Bool)
    (h : casPairOutcomes s a cmp0 cmp1 new0 new1 deps rel acq = []) :
    readCands s a deps = [] ∨ readCands s a.next deps = [] := by
  cases hrc0 : readCands s a deps with
  | nil => exact Or.inl rfl
  | cons tr0 rest0 =>
    cases hrc1 : readCands s a.next deps with
    | nil => exact Or.inr rfl
    | cons tr1 rest1 =>
      exfalso
      -- At each word separately, walk up to the coherence-latest message.
      have hlat : ∀ (b : Address) (tr : Ts), tr ∈ readCands s b deps →
          ∃ u, u < s.mem.size ∧ u ∈ readCands s b deps ∧
            betweenAt s.mem b u s.mem.size = false := by
        intro b tr htr
        have hread : readable s.mem b tr (loadBound s b deps) = true := by
          rw [readCands, List.mem_filter] at htr; exact htr.2
        obtain ⟨m, hm, hloc⟩ := msg_of_readable hread
        have hat : (s.mem[tr]?.elim false fun mm => decide (mm.loc = b)) = true := by
          rw [hm]; simpa using hloc
        have htrs : tr < s.mem.size := by
          rcases Nat.lt_or_ge tr s.mem.size with hl | hg
          · exact hl
          · rw [Array.getElem?_eq_none hg] at hm; simp at hm
        obtain ⟨u, hus, hau, hbu⟩ :=
          exists_latest s.mem b s.mem.size tr (Nat.le_add_left _ _) htrs hat
        exact ⟨u, hus, by
          rw [readCands, List.mem_filter]
          exact ⟨List.mem_range.mpr hus, readable_of_latest hau hbu⟩, hbu⟩
      have htr0 : tr0 ∈ readCands s a deps := by rw [hrc0]; exact List.mem_cons_self ..
      have htr1 : tr1 ∈ readCands s a.next deps := by
        rw [hrc1]; exact List.mem_cons_self ..
      obtain ⟨u0, hu0s, hu0r, hu0b⟩ := hlat a tr0 htr0
      obtain ⟨u1, hu1s, hu1r, hu1b⟩ := hlat a.next tr1 htr1
      -- The two latest messages are a consistent snapshot.  This is the step
      -- the single-word proof does not have.
      have hnostr : pairStraddles s.mem s.pairs a u0 u1 = false :=
        pairStraddles_latest s.mem s.pairs a hu0b hu1b
      have hadj0 : rmwAdjacent s.mem a u0 s.mem.size = true := by
        simp [rmwAdjacent, hu0b, hu0s]
      have hadj1 : rmwAdjacent s.mem a.next u1 (s.mem.size + 1) = true := by
        rw [rmwAdjacent, betweenAt_succ_top, hu1b]
        simp [Nat.lt_succ_of_lt hu1s]
      have hmem : ∃ o, o ∈ casPairOutcomes s a cmp0 cmp1 new0 new1 deps rel acq := by
        by_cases hc : (casMsg s a u0).val = cmp0 ∧ (casMsg s a.next u1).val = cmp1
        · refine ⟨((u0, u1), some s.mem.size), ?_⟩
          rw [casPairOutcomes, List.mem_flatMap]
          refine ⟨u0, hu0r, ?_⟩
          rw [List.mem_flatMap]
          refine ⟨u1, hu1r, ?_⟩
          rw [ite_eq_right (by simp [hnostr]), ite_eq_left hc, List.mem_map]
          exact ⟨s.mem.size, by simp [casPairSlots, hadj0, hadj1], rfl⟩
        · refine ⟨((u0, u1), none), ?_⟩
          rw [casPairOutcomes, List.mem_flatMap]
          refine ⟨u0, hu0r, ?_⟩
          rw [List.mem_flatMap]
          refine ⟨u1, hu1r, ?_⟩
          rw [ite_eq_right (by simp [hnostr]), ite_eq_right hc]
          simp
      obtain ⟨o, ho⟩ := hmem
      rw [h] at ho
      simp at ho

/-- The pure content of the empty case. -/
theorem casPair_post_empty (a : Address) (cmp0 cmp1 new0 new1 : Val)
    (deps : List TVal) (rel acq : Bool) (s₀ : Machine)
    (hf : casPairOutcomes s₀ a cmp0 cmp1 new0 new1 deps rel acq = []) :
    CasPairPost a cmp0 cmp1 new0 new1 deps s₀
      (TVal.mk0 Val.undef, TVal.mk0 Val.undef, false)
      { s₀ with stuck := s₀.stuck || !allocated s₀ a || !allocated s₀ a.next } := by
  have hrc := casPairOutcomes_nil s₀ a cmp0 cmp1 new0 new1 deps rel acq hf
  -- Nothing at one of the two words was readable, which is the second or third
  -- disjunct of `read` depending on which word it was.
  refine ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, rfl, rfl, rfl, rfl, ?_,
    fun _ => ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro h; simp at h
  · rcases hrc with h | h
    · exact Or.inr (Or.inl ⟨rfl, rfl, fun t => by
        rcases Nat.lt_or_ge t s₀.mem.size with hlt | hge
        · have hno := List.filter_eq_nil_iff.mp h t (List.mem_range.mpr hlt)
          simpa using hno
        · unfold readable
          rw [Array.getElem?_eq_none hge]
          simp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, fun t => by
        rcases Nat.lt_or_ge t s₀.mem.size with hlt | hge
        · have hno := List.filter_eq_nil_iff.mp h t (List.mem_range.mpr hlt)
          simpa using hno
        · unfold readable
          rw [Array.getElem?_eq_none hge]
          simp⟩))
  · intro h; simp at h

/-- The pure content of the interesting case.  `cas_post` with everything
    doubled; `tl` is the oracle after `demonic` consumed its entry, for the
    structure-eta reason spelled out there. -/
theorem casPair_post (a : Address) (cmp0 cmp1 new0 new1 : Val) (deps : List TVal)
    (rel acq : Bool) (s₀ : Machine) (tl : List Nat) (o : (Ts × Ts) × Option Ts)
    (ho : o ∈ casPairOutcomes s₀ a cmp0 cmp1 new0 new1 deps rel acq) :
    CasPairPost a cmp0 cmp1 new0 new1 deps s₀
      (⟨(casMsg s₀ a o.1.1).val, (casMsg s₀ a o.1.1).view, o.1.1⟩,
       ⟨(casMsg s₀ a.next o.1.2).val, (casMsg s₀ a.next o.1.2).view, o.1.2⟩,
       o.2.isSome)
      (casPairApply { s₀ with oracle := tl } a new0 new1 deps rel acq o) := by
  rw [casPairOutcomes, List.mem_flatMap] at ho
  obtain ⟨t0, ht0, ho⟩ := ho
  rw [List.mem_flatMap] at ho
  obtain ⟨t1, ht1, ho⟩ := ho
  -- The read halves, common to both branches.
  have hread0 : readable s₀.mem a t0 (loadBound s₀ a deps) = true := by
    rw [readCands, List.mem_filter] at ht0; exact ht0.2
  have hread1 : readable s₀.mem a.next t1 (loadBound s₀ a.next deps) = true := by
    rw [readCands, List.mem_filter] at ht1; exact ht1.2
  obtain ⟨m0, hm0, hloc0⟩ := msg_of_readable hread0
  obtain ⟨m1, hm1, hloc1⟩ := msg_of_readable hread1
  have hcas0 : casMsg s₀ a t0 = m0 := by rw [casMsg, hm0]; rfl
  have hcas1 : casMsg s₀ a.next t1 = m1 := by rw [casMsg, hm1]; rfl
  -- A torn snapshot contributes no outcome at all, so membership already says
  -- the pair did not straddle.  This is the extra step over `cas_post`.
  by_cases hstr : pairStraddles s₀.mem s₀.pairs a t0 t1
  · rw [ite_eq_left hstr] at ho; simp at ho
  · have hnostr : pairStraddles s₀.mem s₀.pairs a t0 t1 = false := by simpa using hstr
    rw [ite_eq_right hstr] at ho
    by_cases hc : (casMsg s₀ a t0).val = cmp0 ∧ (casMsg s₀ a.next t1).val = cmp1
    · -- Both compares succeeded: `o = ((t0, t1), some tw)` for some slot.
      rw [ite_eq_left hc, List.mem_map] at ho
      obtain ⟨tw, htw, rfl⟩ := ho
      simp only []
      refine ⟨?_, rfl, rfl, rfl, rfl, fun _ => hc, ?_,
        Or.inr (Or.inr (Or.inr ⟨?_, hread0, ?_, hread1, hnostr⟩)), ?_⟩
      · -- Extends: either a two-message push or no change at all.
        by_cases hsz : tw = s₀.mem.size
        · refine ⟨?_, ?_⟩
          · show s₀.mem.size ≤
              (if tw = s₀.mem.size then (s₀.mem.push _).push _ else s₀.mem).size
            rw [ite_eq_left hsz]
            simp only [Array.size_push]
            omega
          · intro u hu
            show (if tw = s₀.mem.size then (s₀.mem.push _).push _
                  else s₀.mem)[u]? = s₀.mem[u]?
            rw [ite_eq_left hsz]
            simp [Array.getElem?_push, Nat.ne_of_lt hu,
              Nat.ne_of_lt (Nat.lt_succ_of_lt hu)]
        · refine ⟨?_, ?_⟩
          · show s₀.mem.size ≤
              (if tw = s₀.mem.size then (s₀.mem.push _).push _ else s₀.mem).size
            rw [ite_eq_right hsz]
            exact Nat.le_refl _
          · intro u _
            show (if tw = s₀.mem.size then (s₀.mem.push _).push _
                  else s₀.mem)[u]? = s₀.mem[u]?
            rw [ite_eq_right hsz]
      · intro h; simp at h
      · rw [hm0, hcas0]; simp [← hloc0]
      · rw [hm1, hcas1]; simp [← hloc1]
      · intro _ hp
        -- With nothing promised the only slot is the end of memory, and it is
        -- available only if *both* words are adjacent.
        have hslot : tw = s₀.mem.size ∧
            rmwAdjacent s₀.mem a t0 s₀.mem.size = true ∧
            rmwAdjacent s₀.mem a.next t1 (s₀.mem.size + 1) = true := by
          rw [casPairSlots, hp] at htw
          simp only [List.filter_nil, List.append_nil] at htw
          by_cases hadj : rmwAdjacent s₀.mem a t0 s₀.mem.size &&
              rmwAdjacent s₀.mem a.next t1 (s₀.mem.size + 1)
          · rw [ite_eq_left hadj] at htw
            rw [Bool.and_eq_true] at hadj
            exact ⟨by simpa using htw, hadj.1, hadj.2⟩
          · rw [ite_eq_right hadj] at htw; simp at htw
        obtain ⟨rfl, hadj0, hadj1⟩ := hslot
        refine ⟨⟨casView (casPairReadVs s₀ a acq t0 t1) deps rel, ?_⟩,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show (if s₀.mem.size = s₀.mem.size then (s₀.mem.push _).push _
                else s₀.mem) = _
          rw [ite_eq_left rfl]
          rfl
        · show (if a = a then s₀.mem.size else _) = s₀.mem.size
          rw [ite_eq_left rfl]
        · show (if a.next = a then _ else if a.next = a.next then s₀.mem.size + 1
                else _) = s₀.mem.size + 1
          rw [ite_eq_right (Address.next_ne a), ite_eq_left rfl]
        · show (if s₀.mem.size = s₀.mem.size then s₀.promises else _) = []
          rw [ite_eq_left rfl]; exact hp
        · show (if s₀.mem.size = s₀.mem.size then s₀.pairs ++ [s₀.mem.size]
                else _) = _
          rw [ite_eq_left rfl]
        · exact Nat.le_max_right _ _
        · rw [rmwAdjacent, Bool.and_eq_true] at hadj0
          simpa using hadj0.2
        · rw [rmwAdjacent, Bool.and_eq_true] at hadj1
          simpa using hadj1.2
    · -- A compare failed: two plain loads, and still a consistent snapshot.
      rw [ite_eq_right hc] at ho
      simp only [List.mem_singleton] at ho
      subst ho
      simp only []
      refine ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, rfl, rfl, rfl, rfl, ?_,
        fun _ => ⟨rfl, rfl, rfl⟩,
        Or.inr (Or.inr (Or.inr ⟨?_, hread0, ?_, hread1, hnostr⟩)), ?_⟩
      · intro h; simp at h
      · rw [hm0, hcas0]; simp [← hloc0]
      · rw [hm1, hcas1]; simp [← hloc1]
      · intro h; simp at h

@[spec]
theorem mcasPair_spec (a : Address) (cmp0 cmp1 new0 new1 : Val) (deps : List TVal)
    (rel acq : Bool) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    mcasPair a cmp0 cmp1 new0 new1 deps rel acq
    ⦃⇓ r s => ⌜CasPairPost a cmp0 cmp1 new0 new1 deps s₀ r s⌝⦄ := by
  mvcgen [mcasPair, demonic]
  case vc1.h_1 =>
    subst_vars
    simp +zetaDelta only []
    rename_i s hf _
    exact casPair_post_empty a cmp0 cmp1 new0 new1 deps rel acq s hf
  case vc2.h_2 =>
    subst_vars
    simp +zetaDelta only []
    rename_i s c cs hf _ _
    have hmem := pick_mem (s.oracle.headD 0) c cs
    rw [← hf] at hmem
    exact casPair_post a cmp0 cmp1 new0 new1 deps rel acq s s.oracle.tail _ hmem

/-! ### The control

`casScenario` showed a stale read being available and then refused.  This is
the pair analogue, and it has to show something a *pair of* `mcas`es cannot do,
or the primitive is not earning its place.

The memory holds one complete pair update: somebody swapped `(0,0)` to `(1,1)`
atomically, so the only two values the pair has ever had are `(0,0)` and
`(1,1)`.  A reader whose views are still at the beginning may see either.

**The comparand deliberately matches neither**, so every compare here fails.
That is not a weakness of the control, it is the whole point.  A *successful*
CAS cannot read stale -- `casScenario` is the demonstration, and it is why the
obvious version of this scenario shows nothing: adjacency already forces a
winning CAS to read the latest value at its word.  Tearing lives on the failing
path, where nothing is written and adjacency constrains nothing, and that is
exactly where herd7's `C-read-tear` probe found it.  `CasPairPost.snapshot` is
stated unconditionally for the same reason.

Row 1 is two independent `mcas`es, one per word.  Each is atomic on its own
word and neither says anything about the other, so the first can read the old
value and the second the new: the reader comes away with `(0, 1)`, a pair that
was never in memory.

Row 2 is one `mcasPair` on the same memory, and rather than trust a single
oracle choice it lists *every* snapshot `casPairOutcomes` admits.  There are
two, and they are the two that really existed. -/

/-- Every pair of values a `mcasPair` here could come away with, deduplicated.
    Reported instead of a single run so the claim is "the torn snapshot is not
    available" rather than "the oracle did not pick it". -/
def casPairSnapshots (s : Machine) (a : Address) (cmp0 cmp1 new0 new1 : Val) :
    List (Val × Val) :=
  (casPairOutcomes s a cmp0 cmp1 new0 new1 [] false false).foldl
    (fun acc o =>
      let vv := ((casMsg s a o.1.1).val, (casMsg s a.next o.1.2).val)
      if acc.contains vv then acc else acc ++ [vv]) []

def casPairS0 : Machine :=
  let p : Address := ⟨0, 0⟩
  { mem := #[⟨p, Val.num 0, 0⟩, ⟨p.next, Val.num 0, 0⟩,
             ⟨p, Val.num 1, 0⟩, ⟨p.next, Val.num 1, 0⟩],
    sizes := [2],
    -- The pair write is the one at timestamps 2 and 3.
    pairs := [2],
    -- Ask for the oldest readable candidate at the first word and the newest
    -- at the second: the torn combination, if it is available.
    oracle := [0, 9] }

def casPairScenario (atomic : Bool) : String :=
  let p : Address := ⟨0, 0⟩
  let q : Address := p.next
  -- Matches neither `(0,0)` nor `(1,1)`: every compare below fails, which is
  -- where a torn read is possible at all.
  let cmp := Val.num 7
  if atomic then
    let snaps := casPairSnapshots casPairS0 p cmp cmp (Val.num 5) (Val.num 5)
    let torn := snaps.any fun vv => decide (vv.1 ≠ vv.2)
    s!"atomic=true : snapshots available={repr snaps}, torn-available={torn}"
  else
    let prog : M (Val × Val) := do
      let (r0, _) ← mcas p cmp (Val.num 5)
      let (r1, _) ← mcas q cmp (Val.num 5)
      pure (r0.val, r1.val)
    let ((v0, v1), _s) := prog.run casPairS0
    s!"atomic=false: read=({repr v0}, {repr v1}), " ++
    s!"torn-read={decide (v0 ≠ v1)}"

def casPairDemo : String :=
  "  " ++ casPairScenario false ++ "\n  " ++ casPairScenario true


/-! ## 12. Pointer chasing: traversal with no reader-side barrier

§8 showed that a remote reader can dereference a published pointer safely
without a fence, because the *address dependency* carries the ordering.  That
was one hop.  This section is the general case: an arbitrarily deep traversal
of an immutable structure, with **no barrier anywhere on the reader**, and one
store-store fence on the writer for the whole structure regardless of its size.

That is the cheap-ordering story the whole development was pointed at.  On
AArch64 `ldr x1,[x0]; ldr x2,[x1]` needs nothing between the two loads -- the
second load's address depends on the first load's result, and the architecture
orders them for free.  A `dmb ishld` there would be correct and would cost
real time on real hardware, and the claim that it is unnecessary is the sort of
claim that is easy to believe and hard to justify.  Here it is a theorem, with
an executable counterexample on each side of it.

### What the traversal actually needs

The mechanism is one line, and it already existed: `rlearnedOf` gives the
learned pointer the view `max ra.view m.view`.  So the view along a dependency
chain is **non-decreasing**, and a bound established once at the top survives
to the bottom no matter how far down it goes.  Everything else in this section
is saying what "the structure was published" means and checking that coherence
then pins each read.

`Settled` is that definition.  A cell is settled on `v` below `N` when the
write carrying `v` is at or below `N` and nothing at that cell sits above it.
Two clauses, and both are needed for different reasons: the bound is what the
chased view has to reach, and the maximality is what makes coherence hand back
that write rather than some other one.  An immutable structure built before a
fence satisfies this for every one of its cells, with a single `N`.

### Where this section starts, and why not at the root

`chased_reads_are_published` assumes the traversal begins on a pointer that
already carries the view.  That is not a gap -- it is the honest division of
labour, and the demo below exhibits the reason.  The *root* word is exactly the
place where there is no dependency to exploit: the reader knew the root's
address all along, so its load of the root is ordered by nothing, and the model
correctly permits it to return the stale scalar that was there before
publication.  Ruling that out is §8's job and it needs §8's hypothesis -- that
the root held no pointer before this one (`hfresh`), so a *pointer* read from
it can only be the published one.

So: **entry costs an assumption about the root word; the rest of the traversal
costs nothing, at any depth.**  `chase_after_publication` is the seam, and it
is a one-line proof, which is the point -- `PubTop.view` and `PubTop.addr` are
already precisely the two hypotheses the chase wants. -/

/-- The cell `a` has settled on `v`, as of `N`.

    `Na ≤ N` is what a chased view has to reach; the last clause is what makes
    coherence hand back *that* write.  Neither implies the other, and the proof
    uses them at two different points. -/
def Settled (mem : Memory) (N : Ts) (a : Address) (v : Val) : Prop :=
  ∃ (Na : Nat) (m : Msg), Na ≤ N ∧ mem[Na]? = some m ∧ m.loc = a ∧ m.val = v ∧
    ∀ (t : Nat) (m' : Msg), mem[t]? = some m' → m'.loc = a → t ≤ Na

/-- A maximal write is readable at *every* bound, including 0.

    The converse of `not_readable_of_later`, and the clause that makes
    `RLoadPost.declined` bite: if the cell is settled then the candidate list is
    never empty, so the traversal cannot stall on a published cell. -/
theorem readable_of_settled {mem : Memory} {a : Address}
    {Na : Nat} {m : Msg} (hm : mem[Na]? = some m) (hloc : m.loc = a)
    (hfroz : ∀ (t : Nat) (m' : Msg), mem[t]? = some m' → m'.loc = a → t ≤ Na)
    (bound : Ts) : readable mem a Na bound = true := by
  unfold readable
  rw [hm]
  simp only [Option.elim, hloc, decide_true, Bool.true_and, Bool.not_eq_true']
  cases hh : hiddenFrom mem a Na bound with
  | false => rfl
  | true =>
    exfalso
    rw [hiddenFrom, List.any_eq_true] at hh
    obtain ⟨t', _, ht'⟩ := hh
    rw [Bool.and_eq_true] at ht'
    obtain ⟨hlt, hmsg⟩ := ht'
    cases hm' : mem[t']? with
    | none => rw [hm'] at hmsg; simp at hmsg
    | some m' =>
      rw [hm'] at hmsg
      simp only [Option.elim, decide_eq_true_eq] at hmsg
      -- Explicit `Nat` steps: `omega` does not see through `abbrev Ts := Nat`.
      have h1 : t' ≤ Na := hfroz t' m' hm' hmsg
      have h2 : Na < t' := by simpa using hlt
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 h1)

/-- A remote read is bounded below by the view of the pointer it arrived on.
    One `max` projection, and the only thing the traversal needs from
    `rloadBound`. -/
theorem view_le_rloadBound (s : Machine) (ra : RAddr) : ra.view ≤ rloadBound s ra :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

/-- Follow `k` pointers from `ra`.

    `rfenced` inserts a `dmb ishld` before every load.  It exists only so the
    control below can run the 2x2; the theorem is stated at `false`, which is
    the claim. -/
def rchase (ra : RAddr) (k : Nat) (rfenced : Bool) : M (Option RAddr) := do
  let mut cur : Option RAddr := some ra
  for _ in [:k] do
    if let some c := cur then
      if rfenced then rfence .ld
      match ← rload c with
      | none => cur := none
      | some m => cur := rlearnedOf c m
  return cur

/-- **The traversal theorem.**  Every value the chase reads is the published
    value of the cell it came from, at any depth, with no barrier on the reader.

    `L` is the published structure and `val` its contents.  Two hypotheses
    describe it: every cell is settled below one common `N`, and the structure
    is closed under its own pointers.  A list built before a single `dmb ishst`
    satisfies both, and the `N` is the same for all of it -- which is why the
    writer pays for one fence rather than one per node.

    Three conclusions, and the third is the one that keeps this honest.  A
    safety property about "everything the reader read" is satisfied by a reader
    that read nothing, so the theorem also says the traversal stops only at a
    genuine end of list: if it came back empty-handed, the cell it stopped on
    holds a published value that is not a pointer.  `RLoadPost.declined` and
    `readable_of_settled` exist for that clause. -/
theorem chased_reads_are_published
    (L : Address → Prop) (val : Address → Val) (N : Ts) (mem₀ : Memory)
    (ra : RAddr) (k : Nat)
    (hsettled : ∀ a, L a → Settled mem₀ N a (val a))
    (hclosed : ∀ a b g, L a → val a = Val.loc b g → L b)
    (hroot : L ra.addr) (hview : N ≤ ra.view) :
    ⦃fun s => ⌜s.mem = mem₀ ∧ s.rreads = []⌝⦄
    rchase ra k false
    ⦃⇓ r s => ⌜(∀ v ∈ s.rreads, ∃ a, L a ∧ val a = v) ∧
               (∀ c, r = some c → L c.addr) ∧
               (r = none → ∃ a, L a ∧ ∀ b g, val a ≠ Val.loc b g)⌝⦄ := by
  mvcgen [rchase]
  case inv1 =>
    -- The cursor is the loop's mutable state, so the invariant is indexed by
    -- `Cursor × Option RAddr` rather than `Cursor × PUnit`.  `N ≤ c.view` is
    -- the whole inductive content: the chase never loses the ordering it
    -- started with.
    exact ⇓ ⟨_, cur⟩ s => ⌜s.mem = mem₀ ∧
      (∀ v ∈ s.rreads, ∃ a, L a ∧ val a = v) ∧
      (∀ c, cur = some c → N ≤ c.view ∧ L c.addr) ∧
      (cur = none → ∃ a, L a ∧ ∀ b g, val a ≠ Val.loc b g)⌝
  -- The load found nothing.  Impossible on a published cell: it is settled, a
  -- settled write is readable at every bound, so the candidate list was not
  -- empty and `declined` is contradicted.
  · rename_i _b c _hbc _cont s₁ hinv _r _hrn _cur _s₂ hl
    obtain ⟨hmem1, _, hsome1, _⟩ := hinv
    obtain ⟨_, hL⟩ := hsome1 c rfl
    exfalso
    obtain ⟨Na, m₀, _, hm₀, hloc₀, _, hfroz⟩ := hsettled c.addr hL
    rw [← hmem1] at hm₀ hfroz
    have h1 := hl.declined rfl Na m₀ hm₀
    rw [readable_of_settled hm₀ hloc₀ hfroz (rloadBound s₁ c)] at h1
    simp at h1
  -- The load found something, and coherence says it was the settled write.
  · rename_i _b c _hbc _cont s₁ hinv _r m _hrm _cur _s₂ hl
    simp +zetaDelta only []
    obtain ⟨hmem1, hreads1, hsome1, _⟩ := hinv
    obtain ⟨hvc, hL⟩ := hsome1 c rfl
    obtain ⟨Na, m₀, hNaN, hm₀, hloc₀, hval₀, hfroz⟩ := hsettled c.addr hL
    rw [← hmem1] at hm₀ hfroz
    obtain ⟨t, ht, hrd⟩ := hl.read m rfl
    -- The reader's bound reaches the settled write because the *pointer it
    -- arrived on* carries a view that does.  No fence appears here, and this
    -- is the only place ordering is used.
    have hb : Na ≤ rloadBound s₁ c :=
      Nat.le_trans (Nat.le_trans hNaN hvc) (view_le_rloadBound s₁ c)
    have hteq : t = Na := readable_eq_of_frozen hm₀ hloc₀ hb hfroz hrd
    rw [hteq, hm₀] at ht
    have hmval : m.val = val c.addr := by rw [← Option.some.inj ht]; exact hval₀
    refine ⟨by rw [hl.mem, hmem1], ?_, ?_, ?_⟩
    · rw [hl.reads]
      intro v hv
      simp only [Option.map_some, Option.toList_some, List.mem_append,
        List.mem_singleton] at hv
      rcases hv with hv | hv
      · exact hreads1 v hv
      · exact ⟨c.addr, hL, by rw [hv]; exact hmval.symm⟩
    · -- The dependency carries the view forward: `max c.view m.view`, so the
      -- next cell inherits the bound and the induction closes.
      intro c' hc'
      unfold rlearnedOf at hc'
      cases hvm : m.val with
      | undef =>  rw [hvm] at hc'; simp at hc'
      | null =>   rw [hvm] at hc'; simp at hc'
      | num n =>  rw [hvm] at hc'; simp at hc'
      | loc bb gg =>
        rw [hvm] at hc'
        simp only [Option.some.injEq] at hc'
        subst hc'
        exact ⟨Nat.le_trans hvc (Nat.le_max_left _ _),
               hclosed c.addr bb gg hL (by rw [← hmval]; exact hvm)⟩
    · -- It stopped, and the published value here is not a pointer: that is a
      -- real end of list, not a stall.
      intro hstop
      refine ⟨c.addr, hL, fun bb gg hcontra => ?_⟩
      rw [← hmval] at hcontra
      unfold rlearnedOf at hstop
      rw [hcontra] at hstop
      simp at hstop
  -- The chase had already stopped; the body does nothing.
  · rename_i _b _cur _hnone _hbcur _s hinv
    exact hinv
  -- Entry.
  · rename_i _s hpre
    simp +zetaDelta only []
    obtain ⟨hmem, hreads⟩ := hpre
    refine ⟨hmem, ?_, ?_, ?_⟩
    · rw [hreads]; intro v hv; simp at hv
    · intro c hc
      rw [show c = ra from by simpa using hc.symm]
      exact ⟨hview, hroot⟩
    · intro h; simp at h
  -- Exit.
  · rename_i _r _s hinv
    obtain ⟨_, hreads, hsome, hstop⟩ := hinv
    exact ⟨hreads, fun c hc => (hsome c hc).2, hstop⟩

/-- The seam with §8, and it is a one-liner.

    `PubTop.addr` and `PubTop.view` are exactly `hroot` and `hview`, which is
    not a coincidence: §8 was deliberately stated as "what publication leaves
    behind" rather than "what one reader saw", and this is the second caller to
    benefit (§9.1 was the first).  Nothing is inserted between the publication
    and the traversal -- no fence, no re-read, no assumption. -/
theorem chase_after_publication
    (L : Address → Prop) (val : Address → Val) (N : Ts) (mem₀ : Memory)
    (data : Address) (v : Val) (sPub : Machine) (rb : RAddr) (k : Nat)
    (htop : PubTop data v N sPub rb)
    (hsettled : ∀ a, L a → Settled mem₀ N a (val a))
    (hclosed : ∀ a b g, L a → val a = Val.loc b g → L b)
    (hL : L data) :
    ⦃fun s => ⌜s.mem = mem₀ ∧ s.rreads = []⌝⦄
    rchase rb k false
    ⦃⇓ r s => ⌜(∀ v ∈ s.rreads, ∃ a, L a ∧ val a = v) ∧
               (∀ c, r = some c → L c.addr) ∧
               (r = none → ∃ a, L a ∧ ∀ b g, val a ≠ Val.loc b g)⌝⦄ :=
  chased_reads_are_published L val N mem₀ rb k hsettled hclosed
    (htop.addr ▸ hL) htop.view

/-! ### The control

Four rows, because there are two fences to vary and the interesting facts are
in the comparisons rather than in any single row. -/

/-- Write the spine: each node points at the next, the last holds `tail`. -/
def storeChain (tail : Val) : List Address → M Unit
  | [] => pure ()
  | [a] => mstore a tail
  | a :: b :: rest => do
      mstore a (Val.loc b 0)
      storeChain tail (b :: rest)

/-- Build the whole structure, then publish its head with **one** store-store
    fence -- not one per node.  `mfence .st` promotes `vWr`, which already
    covers every write made so far, so the single fence orders the entire
    structure before the pointer that exposes it.  That is why the writer's
    cost does not grow with the list. -/
def publishChain (root : Address) (nodes : List Address) (tail : Val)
    (fenced : Bool) : M Unit := do
  storeChain tail nodes
  if fenced then mfence .st else pure ()
  match nodes with
  | [] => pure ()
  | h :: _ => mstore root (Val.loc h 0)

/-- **The 2x2.**  Three links ending in a payload, a stale value planted at
    every cell, and an oracle that steers the reader to the *new* root pointer
    and then to the *stale* value at every node it reaches.

    Read it as two comparisons.

    Rows 1 and 2 are the writer's fence: with it the reader walks all three
    links and reads the payload; without it the reader gets the right pointer
    out of the root and then `undef` from the very first node, because the
    pointer it chased carries view 0 and the bound never reaches the
    initialising write.

    Rows 2 and 3 are the interesting pair, and they are why a reader-side
    barrier is not an alternative.  Row 3 puts a `dmb ishld` in front of every
    load and changes nothing: without the writer's fence the messages carry no
    view, so the reader's load absorbs nothing into `vRd`, and a fence that
    promotes `vRd` promotes zero.  A reader cannot buy with a barrier what the
    writer declined to publish.

    Rows 1 and 4 are the claim in the section title.  The reader's barrier is
    *redundant* when the writer did its job -- same depth, same values, same
    everything -- because the address dependency had already supplied the
    ordering the fence would have supplied.  That is the sense in which the
    traversal is cheaper than `dmb`: not that the barrier is wrong, but that it
    is three instructions of nothing. -/
def chaseScenario (wfenced rfenced : Bool) : String :=
  let root : Address := ⟨0, 0⟩
  let n0 : Address := ⟨1, 0⟩
  let n1 : Address := ⟨2, 0⟩
  let n2 : Address := ⟨3, 0⟩
  let s0 : Machine :=
    { mem := #[⟨n0, Val.undef, 0⟩, ⟨n1, Val.undef, 0⟩, ⟨n2, Val.undef, 0⟩,
               ⟨root, Val.num 0, 0⟩],
      sizes := [1, 1, 1, 1],
      roots := [root], rknow := [⟨root, 0⟩],
      -- Four stores (one candidate each), then four reads: take the *new* root
      -- pointer (1), then the *stale* cell at every node (0).  The oracle is
      -- doing its best to break us, and the reader's fence never helps it.
      oracle := [0, 0, 0, 0, 1, 0, 0, 0] }
  let (_, s) :=
    (do publishChain root [n0, n1, n2] (Val.num 7) wfenced
        rchase ⟨root, 0⟩ 4 rfenced : M (Option RAddr)).run s0
  let reads := String.intercalate ", " (s.rreads.map valStr)
  let sawUndef := s.rreads.any fun v => match v with | .undef => true | _ => false
  s!"writer-fence={wfenced}, reader-fence={rfenced}: depth={s.rreads.length}, " ++
  s!"reads=[{reads}], saw-undef={sawUndef}"

def chaseDemo : String :=
  "  " ++ chaseScenario true false ++ "\n  " ++ chaseScenario false false ++
  "\n  " ++ chaseScenario false true ++ "\n  " ++ chaseScenario true true


/-! ## 13. A growable array: capacity is not length

§6.6 asked what a doubling array needs from this model, and split the answer
into three pieces: (a) allocation whose cells start undefined, (b) reachability
that can shrink, and (c) a `zap` primitive.  Stage 2 delivered (a).  This
section is the claim that (a) is *all* a private growable array needs -- that
(b) and (c) are about something else -- and the way to make that claim is to
write the array and prove it never goes wrong.

Three things make it worth doing here rather than as an exercise.

**It is the first client.**  Everything above is a litmus test or a protocol: a
shape chosen to exhibit one phenomenon.  A vector is chosen by its interface,
and the proof has to survive whatever the interface drags in -- a loop inside a
conditional inside a loop, an allocation whose label did not exist when the
theorem was stated, and a `copy` that was written for §10 and knows nothing
about vectors.

**It is the first bounds property.**  Every theorem so far is about *what is in*
memory.  This one is about what is *addressable*, and that turns out to need two
things the `*Post` structures did not have.  `sizes` had to be pinned in
`LoadPost`, `StorePost`, `FencePost` and `EnvPost`: `allocated` reads `s.sizes`,
so without those clauses a bounds fact established before an operation says
nothing after it -- and in `EnvPost` that is a real modelling decision, recorded
there, that the allocator is Local's.  And `LoadPost.stuck` had to gain a
converse, `LoadPost.clean`: monotonicity ("if it was broken it stays broken") is
what a *safety* argument wants, and a client claiming never to go wrong wants
the other direction.

**The split is the whole content.**  `len ≤ cap` is not decoration.  The
arithmetic that makes `vpush` safe is exactly
`v.len ≤ v.cap → v.len < max 1 (2 * v.cap)`, and it has to hold at `cap = 0`,
where doubling doubles nothing -- which is why the growth is `max 1 (2 * cap)`
and not `2 * cap`.  The demo shows the three regimes the split creates, and the
last row of the control shows what happens to a `vpush` that skips the test. -/

/-- The loop variable of `for i in [:n]` is below `n`.

    `mvcgen` hands the body a `Cursor`, whose content is an equation splitting
    the range's `toList`; nothing in scope says the element is small.  §10's
    `copy` proofs never needed this -- they talk about the address the iteration
    touched, not about whether it was in bounds -- and a bounds argument needs
    nothing else. -/
theorem lt_of_cursor {n cur : Nat} {pref suff : List Nat}
    (h : [:n].toList = pref ++ cur :: suff) : cur < n := by
  have hm : cur ∈ [:n].toList := by rw [h]; simp
  simp [Std.Legacy.Range.toList, List.mem_range'_1] at hm
  omega

/-- Bounds, in the form the client produces them: a label with a known size and
    an offset below it. -/
theorem allocated_at {s : Machine} {l : AllocLabel} {n i : Nat}
    (h : s.sizes[l]? = some n) (hi : i < n) :
    allocated s ⟨l, i⟩ = true := by
  unfold allocated
  simp only []
  rw [h]
  simpa using hi

/-- The array descriptor.  `len` and `cap` are Lean-level naturals, not heap
    cells: a settled design decision says Lean-level bindings are registers, and for a
    *private* array that is exactly right -- nobody else may read them, so
    nothing is lost by keeping them out of memory.  A shared vector would need
    them in the heap and would need a protocol, which is §11's business, not
    this section's. -/
structure Vec where
  buf : AllocLabel
  len : Nat
  cap : Nat

/-- Offset zero of the backing store, which is the address `malloc` returns. -/
def Vec.base (v : Vec) : Address := ⟨v.buf, 0⟩

/-- **The invariant, and it is two lines.**  The logical length is within the
    physical capacity, and the capacity is the truth: it is what the allocation
    table says.

    Nothing here mentions views, coherence, promises or Remote.  That is the
    point of doing a private structure first -- the difficulty is entirely in
    the arithmetic and the plumbing, and if that were not separable from the
    concurrency the concurrent structures would be hopeless. -/
def VecOk (s : Machine) (v : Vec) : Prop :=
  v.len ≤ v.cap ∧ s.sizes[v.buf]? = some v.cap

/-! ### What `copy` needs to be told

§10's `copy` was proved private (`copy_stays_private`) and correct
(`copy_copies_something`), and both theorems are silent about bounds: they
tolerate a stuck run by carrying an "…or the run gave up" escape clause.  A
vector cannot tolerate that, because a `vgrow` that quietly got stuck would
satisfy every theorem in §10 and lose the data.

So `copy` gets a third theorem.  The hypotheses are *antecedents in the
postcondition* rather than preconditions, for the reason recorded in §7: a
conjunctive precondition next to the ghost `s = s₀` makes `mvcgen` unify `s₀`
with the caller's ghost.  Putting them after the arrow costs nothing -- they
mention only `s₀`, which is fixed -- and it keeps the spec firing everywhere. -/

@[spec]
theorem copy_stays_clean (src dst : Address) (n : Nat) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    copy src dst n
    ⦃⇓ _ s => ⌜s.sizes = s₀.sizes ∧
      (s₀.stuck = false →
       (∀ i, i < n → allocated s₀ ⟨src.label, src.offset + i⟩ = true) →
       (∀ i, i < n → allocated s₀ ⟨dst.label, dst.offset + i⟩ = true) →
       s.stuck = false)⌝⦄ := by
  mvcgen [copy]
  case inv1 =>
    exact ⇓ ⟨_, _⟩ s => ⌜s.sizes = s₀.sizes ∧
      (s₀.stuck = false →
       (∀ i, i < n → allocated s₀ ⟨src.label, src.offset + i⟩ = true) →
       (∀ i, i < n → allocated s₀ ⟨dst.label, dst.offset + i⟩ = true) →
       s.stuck = false)⌝
  -- One iteration: load, store, environment step.  The allocation table is
  -- unchanged by all three, which is what lets the caller's bounds facts --
  -- stated about `s₀` -- be applied at the current state.
  · rename_i sI hI pref cur suff hsplit b s1 hinv v s2 hload u1 s3 hstore u2 s4
      henv
    obtain ⟨hsz1, hst1⟩ := hinv
    have hcur : cur < n := lt_of_cursor hsplit
    refine ⟨by rw [henv.sizes, hstore.sizes, hload.sizes]; exact hsz1,
            fun h0 hs hd => ?_⟩
    have hst2 : s2.stuck = false :=
      hload.clean (hst1 h0 hs hd)
        (by rw [show allocated s1 ⟨src.label, src.offset + cur⟩
                  = allocated s₀ ⟨src.label, src.offset + cur⟩ from by
                unfold allocated; rw [hsz1]]
            exact hs cur hcur)
    have hst3 : s3.stuck = false := by
      rw [hstore.stuck, hst2,
        show allocated s2 ⟨dst.label, dst.offset + cur⟩
            = allocated s₀ ⟨dst.label, dst.offset + cur⟩ from by
          unfold allocated; rw [hload.sizes, hsz1],
        hd cur hcur]
      rfl
    rw [henv.stuck]; exact hst3
  · rename_i sI hI
    subst hI
    exact ⟨rfl, fun h _ _ => h⟩
  · rename_i hinv
    exact hinv

/-! ### The operations -/

def vnew (cap : Nat) : M Vec := do
  let b ← malloc cap
  pure ⟨b.label, 0, cap⟩

/-- Allocate a bigger buffer and move the live prefix into it.

    `max 1 (2 * v.cap)` rather than `2 * v.cap`, because doubling zero is zero
    and the very first push would then write out of bounds.  That single `max`
    is the only arithmetic subtlety in the section, and it is load-bearing: the
    control at the end starts from `cap = 0`.

    The old buffer is simply abandoned.  Garbage collection is out of scope by
    design, so there is no `free`, no label reuse, and no ABA --
    which is also why a *private* vector needs nothing from §6.6's piece (b):
    the stale buffer was never reachable, so nothing has to become unreachable
    for the array to be safe. -/
def vgrow (v : Vec) : M Vec := do
  let b ← malloc (max 1 (2 * v.cap))
  copy v.base b v.len
  pure ⟨b.label, v.len, max 1 (2 * v.cap)⟩

/-- Grow if full, then write at `len`.  The conditional is the entire bounds
    discipline; `vpushNoGrow` below is the same function without it. -/
def vpush (v : Vec) (x : Val) : M Vec := do
  let w ← if v.len < v.cap then pure v else vgrow v
  mstore ⟨w.buf, w.len⟩ x
  pure ⟨w.buf, w.len + 1, w.cap⟩

/-- Deliberately unchecked, so the demo can exhibit all three regimes.  A
    checked `vget` would return an `Option` and the interesting rows would be
    `none`; here the *machine* says what happens instead. -/
def vget (v : Vec) (i : Nat) : M TVal := mload ⟨v.buf, i⟩

def vpushAll (cap0 : Nat) (xs : List Val) : M Vec := do
  let mut v ← vnew cap0
  for x in xs do
    v ← vpush v x
  pure v

/-! ### The specs

Each is ghost-form with the hypotheses as antecedents, so they compose by being
tagged `@[spec]` and nothing else: `vgrow_spec` consumes `copy_stays_clean`,
`vpush_spec` consumes `vgrow_spec`, and the loop consumes `vpush_spec`.  No
theorem below re-runs a loop that a theorem above already ran. -/

@[spec]
theorem vnew_spec (cap : Nat) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    vnew cap
    ⦃⇓ w s => ⌜s.stuck = s₀.stuck ∧ VecOk s w ∧ w.len = 0 ∧ w.cap = cap⌝⦄ := by
  mvcgen [vnew]
  rename_i sA hA b sM hM
  obtain ⟨hb, hs⟩ := hM
  subst hb
  subst hA
  refine ⟨by rw [hs], ?_⟩
  exact ⟨Nat.zero_le _, by rw [hs]; simp⟩

/-- Growth is safe and gives strict headroom.

    `v.len < w.cap` rather than `v.len ≤ w.cap` is what `vpush` needs: after the
    growth there must be room for the element that provoked it. -/
@[spec]
theorem vgrow_spec (v : Vec) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    vgrow v
    ⦃⇓ w s => ⌜s₀.stuck = false → VecOk s₀ v →
        s.stuck = false ∧ VecOk s w ∧ w.len = v.len ∧ v.len < w.cap⌝⦄ := by
  mvcgen [vgrow]
  rename_i sA hA b sM hM u sC hC
  obtain ⟨hb, hsM⟩ := hM
  obtain ⟨hszC, hstC⟩ := hC
  subst hb
  subst hA
  intro h0 hv
  obtain ⟨hlen, hsize⟩ := hv
  -- The old buffer's label is in range, so extending the table leaves its entry
  -- exactly where it was.  This is `fresh_unreachable`'s arithmetic cousin: the
  -- new label is `sizes.length`, so it cannot collide with an old one.
  have hbuf : v.buf < sA.sizes.length := by
    rcases Nat.lt_or_ge v.buf sA.sizes.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hsize; simp at hsize
  -- The one piece of arithmetic in the section, and the reason for the `max`.
  have hcap : v.len < max 1 (2 * v.cap) := by omega
  have hold : sM.sizes[v.buf]? = some v.cap := by
    rw [hsM]
    show (sA.sizes ++ [max 1 (2 * v.cap)])[v.buf]? = some v.cap
    rw [List.getElem?_append_left hbuf]
    exact hsize
  have hnew : sM.sizes[sA.sizes.length]? = some (max 1 (2 * v.cap)) := by
    rw [hsM]
    show (sA.sizes ++ [max 1 (2 * v.cap)])[sA.sizes.length]? = _
    simp
  -- Both of `copy`'s obligations: the source offsets are below the old
  -- capacity, the destination offsets below the new one.
  have hst : sC.stuck = false := by
    refine hstC (by rw [hsM]; exact h0) (fun i hi => ?_) (fun i hi => ?_)
    · show allocated sM ⟨v.buf, 0 + i⟩ = true
      exact allocated_at hold (by omega)
    · show allocated sM ⟨sA.sizes.length, 0 + i⟩ = true
      exact allocated_at hnew (by omega)
  exact ⟨hst, ⟨Nat.le_of_lt hcap, by rw [hszC]; exact hnew⟩, trivial, hcap⟩

/-- **One push never gets stuck.**  Two branches, and they need different
    reasons: with room the bound is the loop test itself, and without it the
    bound is what the growth just bought. -/
@[spec]
theorem vpush_spec (v : Vec) (x : Val) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    vpush v x
    ⦃⇓ w s => ⌜s₀.stuck = false → VecOk s₀ v →
        s.stuck = false ∧ VecOk s w ∧ w.len = v.len + 1⌝⦄ := by
  mvcgen [vpush]
  -- Room already.
  · rename_i hlt sA hA _ sS hstore
    subst hA
    intro h0 hv
    obtain ⟨hlen, hsize⟩ := hv
    have hal : allocated sA ⟨v.buf, v.len⟩ = true := allocated_at hsize hlt
    refine ⟨by rw [hstore.stuck, h0, hal]; rfl,
      ⟨show v.len + 1 ≤ v.cap by omega, ?_⟩⟩
    rw [hstore.sizes]; exact hsize
  -- Full: grow first, and `vgrow_spec`'s strict headroom is what puts `len`
  -- back in bounds.
  · rename_i hnlt sA hA w sG hgrow _ sS hstore
    subst hA
    intro h0 hv
    obtain ⟨hst1, hok1, hwlen, hwcap⟩ := hgrow h0 hv
    obtain ⟨_, hsize1⟩ := hok1
    have hal : allocated sG ⟨w.buf, w.len⟩ = true :=
      allocated_at hsize1 (by omega)
    refine ⟨by rw [hstore.stuck, hst1, hal]; rfl,
      ⟨show w.len + 1 ≤ w.cap by omega, ?_⟩, by omega⟩
    rw [hstore.sizes]; exact hsize1

/-- **The headline: pushing never gets stuck, at any length.**

    Three conclusions, and the third is the non-vacuity guard.  Without
    `v.len = xs.length` the theorem is satisfied by a `vpush` that discards its
    argument, and "a vector that stores nothing never goes out of bounds" is not
    the claim.  The length comes out of the loop cursor: `c.prefix.length`
    counts the iterations that have happened, and `vpush_spec`'s
    `w.len = v.len + 1` is what keeps the two in step.

    The capacity is *not* in the conclusion, and that is deliberate -- it is
    whatever the doubling produced, and no caller should depend on it. -/
theorem vpushes_never_stick (cap0 : Nat) (xs : List Val) (s₀ : Machine) :
    ⦃fun s => ⌜s = s₀⌝⦄
    vpushAll cap0 xs
    ⦃⇓ v s => ⌜s₀.stuck = false →
        s.stuck = false ∧ VecOk s v ∧ v.len = xs.length⌝⦄ := by
  mvcgen [vpushAll]
  case inv1 =>
    exact ⇓ ⟨c, w⟩ s => ⌜s₀.stuck = false →
      s.stuck = false ∧ VecOk s w ∧ w.len = c.«prefix».length⌝
  -- One push.
  · rename_i sA hA v0 sN hnew pref cur suff hsplit b s1 hinv w s2 hpush
    intro h0
    obtain ⟨hst1, hok1, hlen1⟩ := hinv h0
    obtain ⟨hst2, hok2, hlen2⟩ := hpush hst1 hok1
    exact ⟨hst2, hok2, by rw [hlen2, hlen1]; simp⟩
  -- Entry: a fresh array is well formed and empty.
  · rename_i sA hA v0 sN hnew
    subst hA
    intro h0
    obtain ⟨hstk, hok, hl0, _⟩ := hnew
    exact ⟨by rw [hstk]; exact h0, hok, by simpa using hl0⟩
  -- Exit.
  · rename_i sA hA v0 sN hnew w sF hinv
    exact hinv

/-! ### The control

Two tables.  The first exhibits the three regimes the capacity/length split
creates -- which is precisely what §6.8 said allocation-without-bounds could not
distinguish.  The second is the non-vacuity check. -/

/-- Push 1, 2, 3 into a vector that starts with **no** capacity, so the run
    reallocates three times (0 → 1 → 2 → 4) and copies twice, and then read one
    cell.

    Rows 1-3 are the live prefix: the values survived two `copy`s into two
    different allocations, so the array is doing its job.

    Row 4 is the gap between `len` and `cap`.  The cell is inside the
    allocation and nobody wrote it, so it reads `undef` and the run is **not**
    stuck.  That is stage 2's contribution, and it is what makes the
    capacity/length split expressible at all -- in a model where reading an
    unwritten cell is an error, a vector with spare capacity would be a program
    that is one unlucky read away from being wrong.

    Row 5 is past the capacity, and the run is stuck.  Nothing distinguishes
    rows 4 and 5 except the allocation table. -/
def vgetScenario (i : Nat) : String :=
  let prog : M (Vec × TVal) := do
    let v ← vpushAll 0 [Val.num 1, Val.num 2, Val.num 3]
    let r ← vget v i
    pure (v, r)
  let ((v, r), s) := prog.run { mem := #[], oracle := [] }
  s!"vget {i}: len={v.len}, cap={v.cap}, read={valStr r.val}, stuck={s.stuck}"

/-- `vpush` with the growth test deleted, and nothing else changed. -/
def vpushNoGrow (v : Vec) (x : Val) : M Vec := do
  mstore ⟨v.buf, v.len⟩ x
  pure ⟨v.buf, v.len + 1, v.cap⟩

/-- **Why `vpushes_never_stick` is not free.**  Same loop, same allocation, same
    values -- and the third push into a capacity-2 buffer gets stuck.  So the
    store's bounds check does bite, and the theorem above is a statement about
    `vpush`'s conditional rather than about the model being lenient. -/
def vNoGrowScenario (k : Nat) : String :=
  let prog : M Vec := do
    let mut v ← vnew 2
    for x in (List.range k).map (fun n => Val.num (n + 1)) do
      v ← vpushNoGrow v x
    pure v
  let (v, s) := prog.run { mem := #[], oracle := [] }
  s!"no-grow, {k} pushes into cap 2: len={v.len}, cap={v.cap}, stuck={s.stuck}"

def vecDemo : String :=
  "  " ++ String.intercalate "\n  "
    ((List.range 5).map vgetScenario ++ [vNoGrowScenario 2, vNoGrowScenario 3])


/-! ## 14. Per-location protocols: knowledge that travels with a value

Every theorem so far stops the environment by *exclusion*: it cannot reach the
address (§7), it does not own the allocation (§9), or it lost the CAS (§11.1).
These are the ownership modes of a `Guard`, and there is a third,
`protocol`, for locations that are concurrently written and read, where safety
comes from **ordering** rather than exclusion.  This section builds it.

Three things are worth stating before the definitions, because each one is a
place the obvious design goes wrong.

**A protocol invariant cannot be a predicate on "the heap".**  There isn't one.
Under weak memory two agents disagree about what is in memory, so the invariant
has to be phrased over *reads-from*: not "the state satisfies `I`" but "a value
you loaded entitles you to conclude `I`".  That is why `knows` takes the
timestamp the value was read at.

**`Proto` is deliberately not part of `Machine`.**  The natural sketch is
`Machine.guard : Address -> Guard` with `Guard.protocol (P : Proto)`, and that
does not typecheck: `knows` returns `Machine -> Prop`, so `Machine` would occur
negatively in its own definition and the kernel rejects it with *"arg #2 of
'Proto.mk' has a non positive occurrence of the datatypes being declared"*.
Keeping protocols out of the state is not a workaround for that -- it is the
reason the full-strength `knows` is available at all.  A `Proto` stored in the
state would have to be weakened to `Memory -> Prop`, and then it could not
mention `rknow`, `sizes`, or ownership.

**And it should not be part of `Machine` anyway.**  A `guard` field consulted
by `rstoreStep` is how `rdisowned` works, and §11.1 exists to record what is
wrong with that: it is an assumption with no mechanism behind it.  Exclusion is
already a *theorem* in both modes that have one (`private_stays_private`,
`lock_is_exclusive`), and a field asserting it would replace those proofs with
a hypothesis.  `Governs` below is a predicate, so it can only ever be
*discharged*, never assumed into existence by the machine. -/

/-- A per-location protocol.

    `wf` is the easy half: every value ever written here looks like this.

    `knows` is the half that does the work.  Observing `v` at `a` with view `t`
    entitles the reader to conclude `knows v t`, which is a statement about the
    whole machine -- typically about what is readable *elsewhere* under the
    bound `t`.  That is how a protocol relates locations without locking any of
    them: the ordering is carried by the view, and `knows` is what cashes it
    in. -/
structure Proto where
  wf    : Val → Prop
  knows : Val → Ts → (Machine → Prop)

/-- `a` is governed by `P`: **every** message at `a` satisfies the protocol.

    Note the quantifier is over all of `mem`, not over what is currently
    readable.  A weaker version indexed by a bound would be unstable in the
    worst way -- a reader with a smaller view would satisfy it vacuously and
    then learn nothing -- and an agent that is behind must still be entitled to
    the protocol's conclusion about the stale value it reads.  Stale but
    coherent is exactly the guarantee §6.5 says RCU buys. -/
def Governs (P : Proto) (a : Address) (s : Machine) : Prop :=
  ∀ (t : Ts) (m : Msg), s.mem[t]? = some m → m.loc = a →
    P.wf m.val ∧ P.knows m.val m.view s

/-- `P`'s knowledge survives memory growth.

    This is the settled two-state invariant, specialised: `Extends` is
    the only thing every operation in this file preserves, so it is the only
    hypothesis a stability obligation may use.

    A protocol that fails this is not usable, and the failure mode is worth
    naming: `knows` may say "nothing above `t` is readable at `b`", which a
    later write to `b` falsifies.  A *stable* protocol says "nothing at or
    below `t` at `b` is `undef`", which no append can disturb.  The difference
    is whether the claim is about the future or about the past, and only
    claims about the past survive. -/
def Stable (P : Proto) : Prop :=
  ∀ (v : Val) (t : Ts) (s s' : Machine), Extends s s' → P.knows v t s →
    P.knows v t s'

/-! ### The load

The natural form is an `@[spec]` lemma on `load`.  It is a derived
lemma here instead, and deliberately **not** tagged `@[spec]`: `mvcgen` picks
specs by the head symbol of the operation, so a second spec for `mload` would
compete with `mload_spec` at every one of its ~40 call sites.  As a pure
consequence of `LoadPost` it composes the same way and costs nothing anywhere
it is not used.

The conclusion is a three-way disjunction for the same reason `LoadPost.read`
is.  The middle case -- inside an allocation with nothing readable -- returns
`undef`, and `undef` need not satisfy `wf`; a protocol that wanted to exclude
it would have to say so by ruling out the case, which is what `Governs` plus a
coherence argument does at the call site. -/

/-- Reading a governed location yields the protocol's knowledge. -/
theorem proto_of_load (P : Proto) (a : Address) (deps : List TVal)
    {s₀ r s} (hS : Stable P) (hg : Governs P a s₀)
    (h : LoadPost a deps s₀ r s) :
    s.stuck = true ∨ r.val = Val.undef ∨
      (P.wf r.val ∧ P.knows r.val r.view s) := by
  rcases h.read with hstuck | ⟨hu, _⟩ | ⟨hmsg, _⟩
  · exact Or.inl hstuck
  · exact Or.inr (Or.inl hu)
  · refine Or.inr (Or.inr ?_)
    obtain ⟨hwf, hk⟩ := hg r.rts ⟨a, r.val, r.view⟩ hmsg rfl
    -- `LoadPost.mem` makes the two machines agree on memory, so `Extends`
    -- holds in the forward direction and stability moves `knows` across.
    refine ⟨hwf, hS _ _ s₀ s ⟨Nat.le_of_eq (congrArg Array.size h.mem.symm), ?_⟩ hk⟩
    intro t _; rw [h.mem]

/-! ### Keeping a protocol alive

`Governs` is a statement about the state, so every operation has to be shown to
preserve it.  One general lemma does all of them, because every operation in
this file only ever *appends*: the obligation splits into the messages that
were already there (stability) and the ones that are new (the writer's
discipline). -/

/-- Preservation, in the form every caller wants: old messages are handled by
    `Stable`, new ones by whatever the writer promised. -/
theorem governs_mono (P : Proto) (a : Address) {s₀ s : Machine}
    (hS : Stable P) (hg : Governs P a s₀) (hext : Extends s₀ s)
    (hnew : ∀ (t : Ts) (m : Msg), s₀.mem.size ≤ t → s.mem[t]? = some m →
      m.loc = a → P.wf m.val ∧ P.knows m.val m.view s) :
    Governs P a s := by
  intro t m hm hloc
  rcases Nat.lt_or_ge t s₀.mem.size with hlt | hge
  · rw [hext.2 t hlt] at hm
    obtain ⟨hwf, hk⟩ := hg t m hm hloc
    exact ⟨hwf, hS _ _ s₀ s hext hk⟩
  · exact hnew t m hge hm hloc

/-- A store somewhere else leaves the protocol alone.

    `s₀.promises = []` is what pins the new memory to a single `push`; with an
    outstanding promise the store could fulfil instead, and `StorePost` on
    purpose does not say which happened.  Every client of this lemma is in a
    program that has not promised. -/
theorem governs_of_store_other (P : Proto) (a b : Address) (v : Val)
    (deps : List TVal) (rel : Bool) {s₀ s : Machine}
    (hS : Stable P) (hg : Governs P a s₀) (hne : b ≠ a)
    (hp : s₀.promises = []) (h : StorePost b v deps rel s₀ s) :
    Governs P a s := by
  refine governs_mono P a hS hg h.ext ?_
  intro t m hge hm hloc
  -- The only new message is the one just pushed, and it is at `b`.
  exfalso
  obtain ⟨hmem, _, _, _⟩ := h.append hp
  -- `Array.getElem?_push` splits on `t = size`, not on `t < size`.
  rw [hmem, Array.getElem?_push] at hm
  by_cases ht : t = s₀.mem.size
  · rw [ite_eq_left ht] at hm
    injection hm with hm
    rw [← hm] at hloc
    exact hne hloc
  · rw [ite_eq_right ht, Array.getElem?_eq_none hge] at hm
    simp at hm

/-- A store **at** the governed location, which is where the protocol is paid
    for.

    `hwf` and `hk` are the writer's proof obligations, and `hk` is the whole
    discipline: to publish `v` you must *prove* the protocol's knowledge clause
    holds at the view your store will carry.  Publishing is proving.

    Note `hk` is about the post-state `s`, not `s₀`.  That is deliberate and it
    is the only way round: the writer typically establishes `knows` by pointing
    at a write it made earlier in the same program, and that write has to be
    visible in the state being described. -/
theorem governs_of_store_at (P : Proto) (a : Address) (v : Val)
    (deps : List TVal) (rel : Bool) {s₀ s : Machine}
    (hS : Stable P) (hg : Governs P a s₀) (hp : s₀.promises = [])
    (h : StorePost a v deps rel s₀ s)
    (hwf : P.wf v) (hk : P.knows v (mstoreView s₀ deps rel) s) :
    Governs P a s := by
  refine governs_mono P a hS hg h.ext ?_
  intro t m hge hm _
  obtain ⟨hmem, _, _, _⟩ := h.append hp
  rw [hmem, Array.getElem?_push] at hm
  by_cases ht : t = s₀.mem.size
  · rw [ite_eq_left ht] at hm
    injection hm with hm
    rw [← hm]
    exact ⟨hwf, hk⟩
  · rw [ite_eq_right ht, Array.getElem?_eq_none hge] at hm
    simp at hm

/-! ### The protocol under interference

Everything above is about Local's own operations.  The question that decides
whether `Proto` is worth anything is the other one: does a protocol survive an
arbitrary step by Remote?

The answer needs less machinery than it looks like it should.  The tempting
move is to parameterise `Stable` by a rely relation -- to say that `knows` must
survive not just `Extends` but whatever Remote can do.  That is unnecessary,
and it would be a mistake, because it would weaken every protocol in the file
to buy something only one of them needs.  `Stable` is already the right
obligation: `pubProto.knows` survives *any* append, by anyone, and that is
exactly what `pubProto_stable` proves.  What an environment step additionally
threatens is not the knowledge already carried by old messages, it is the
arrival of **new** messages at the governed location -- and that is
`governs_mono`'s `hnew`, which already exists.

So the work is entirely in discharging `hnew`, and there turn out to be three
ways to do it, two of which are free from clauses `EnvPost` already carries:

* **Unreachability** (`EnvPost.wrote`) -- Remote draws its store address out of
  `rknow`, so a location it cannot reach is a location it cannot write.
* **Ownership** (`EnvPost.frozen`) -- a label in `rdisowned` is one Remote has
  given up.  Stronger than the first in the way that matters here: it survives
  publication.  Remote may hold the address, read through it, reach everything
  behind it, and still may not write it.
* **Rely** -- Remote writes, but respects the protocol.  This is the only one
  that is a hypothesis rather than a consequence, and it is also the only one
  that is not free: someone has to prove Remote's code obeys `P`.

None of the three needed a change to `Stable`.  That the discharge is doing
real work, rather than following from `Extends` alone, is
`governs_not_free_of_extends`, with the other controls below. -/

/-- Preservation across an environment step, in the general form: whatever
    Remote appended at `a`, it respected the protocol.

    This is `governs_mono` with `EnvPost.ext`, and it is here to make the point
    that a rely condition is a hypothesis *on the step*, not a parameter of the
    protocol.  The two lemmas below discharge it outright. -/
theorem governs_of_env_rely (P : Proto) (a : Address) {s₀ s : Machine}
    (hS : Stable P) (hg : Governs P a s₀) (henv : EnvPost s₀ s)
    (hrely : ∀ (t : Ts) (m : Msg), s₀.mem.size ≤ t → s.mem[t]? = some m →
      m.loc = a → P.wf m.val ∧ P.knows m.val m.view s) :
    Governs P a s :=
  governs_mono P a hS hg henv.ext hrely

/-- The degenerate rely condition: Remote did not write at `a` at all.

    Stated separately because it is what the two routes below actually
    establish, and because it isolates the single fact an environment step has
    to be shown not to disturb. -/
theorem governs_of_env_other (P : Proto) (a : Address) {s₀ s : Machine}
    (hS : Stable P) (hg : Governs P a s₀) (henv : EnvPost s₀ s)
    (hquiet : ∀ (t : Ts) (m : Msg), s₀.mem.size ≤ t → s.mem[t]? = some m →
      m.loc ≠ a) :
    Governs P a s :=
  governs_of_env_rely P a hS hg henv fun t m hge hm hloc =>
    absurd hloc (hquiet t m hge hm)

/-- **A protocol at a location Remote cannot reach survives arbitrary
    interference.**

    No rely condition, no cooperation from Remote, and no restriction on what
    Remote does anywhere else: the whole hypothesis is `¬ Reaches s₀ a.label`,
    and `EnvPost.wrote` does the rest.  This is the privacy argument of §7
    cashed in for protocols rather than for values. -/
theorem governs_of_env_unreachable (P : Proto) (a : Address) {s₀ s : Machine}
    (hS : Stable P) (hg : Governs P a s₀) (henv : EnvPost s₀ s)
    (hsound : RKnowSound s₀) (hun : ¬ Reaches s₀ a.label) :
    Governs P a s :=
  governs_of_env_other P a hS hg henv fun t m hge hm hloc =>
    hun (hloc ▸ henv.wrote hsound t m hge hm)

/-- **A protocol at a location Remote has disowned survives arbitrary
    interference, even after publication.**

    The strictly more useful of the two free routes, and the one a real
    single-writer structure uses.  Unreachability is lost the moment you
    publish; ownership is not.  Remote may hold the address, read it, and chase
    pointers out of it -- it still may not write there, so the protocol holds.

    Note the absence of `RKnowSound`: `EnvPost.frozen` is unconditional, where
    `EnvPost.wrote` is not. -/
theorem governs_of_env_disowned (P : Proto) (a : Address) {s₀ s : Machine}
    (hS : Stable P) (hg : Governs P a s₀) (henv : EnvPost s₀ s)
    (hown : a.label ∈ s₀.rdisowned) :
    Governs P a s :=
  governs_of_env_other P a hS hg henv fun t m hge hm hloc =>
    henv.frozen t m hge hm (hloc ▸ hown)

/-! ### The client: RCU publication as a protocol

§8 proves `published_read_is_initialised` directly, as a chain of five
hypotheses about six machines.  Here is the same guarantee expressed as a
`Proto`, which is the test of whether the abstraction is worth anything.

The protocol at the root word says two things:

* `wf` -- the root holds null or the descriptor pointer.  **Never `undef`**,
  which is already a real claim: a reader that gets a value out of the root got
  a meaningful one.
* `knows` -- if you read the pointer at view `t`, then the descriptor's
  initialising write sits at or below `t`.

The shape of `knows` is the whole lesson of `Stable`.  The tempting phrasing is
universal -- *"everything you can see at the descriptor is initialised"* -- and
it is **not stable**: someone writing garbage at the descriptor falsifies it,
and no amount of fencing prevents that.  That is not a modelling artefact, it
is true of the hardware, and it is the same unstable universal in yet another form.

The existential phrasing -- *"the good write exists, at or below your view"* --
is stable, because `Extends` preserves existentials over an append-only
structure.  And it is enough, because coherence turns a lower bound into an
exclusion: everything **below** the initialising write is hidden.  Claims about
the past survive; claims about the future do not. -/

/-- The publication protocol at a root word pointing at descriptor `d`. -/
def pubProto (d : Address) (v : Val) : Proto where
  wf x := x = Val.num 0 ∨ x = Val.loc d 0
  knows x t s := x = Val.loc d 0 →
    ∃ (t' : Ts) (m : Msg), s.mem[t']? = some m ∧ m.loc = d ∧ m.val = v ∧ t' ≤ t

/-- `pubProto` is stable: the witness moves across an append unchanged.

    One line, and that is the point of choosing the existential form. -/
theorem pubProto_stable (d : Address) (v : Val) : Stable (pubProto d v) := by
  intro _ _ _ _ hext hk hx
  obtain ⟨t', m, hm, hloc, hval, hle⟩ := hk hx
  exact ⟨t', m, hext.msg hm, hloc, hval, hle⟩

/-- **The payoff.**  A reader that got the pointer out of the root cannot see
    anything older than the initialising write, at any bound its view covers.

    This is `published_read_is_initialised`'s content, obtained from the
    protocol rather than from a bespoke five-machine chain: `knows` supplies
    the lower bound and `not_readable_of_later` turns it into an exclusion.

    Stated as "everything below `t'` is unreadable" rather than "the read
    returns `v`", because that is the part coherence actually gives.  Pinning
    the value needs a second protocol, at `d` -- which is the composition this
    abstraction exists to allow, and which §8 hard-codes. -/
theorem pub_hides_stale (d : Address) (v : Val) {s : Machine} {t bound : Ts}
    (hk : (pubProto d v).knows (Val.loc d 0) t s) (hb : t ≤ bound) :
    ∃ (t' : Ts) (m : Msg), s.mem[t']? = some m ∧ m.loc = d ∧ m.val = v ∧
      ∀ tu, tu < t' → readable s.mem d tu bound = false := by
  obtain ⟨t', m, hm, hloc, hval, hle⟩ := hk rfl
  exact ⟨t', m, hm, hloc, hval, fun tu hlt =>
    not_readable_of_later hlt (Nat.le_trans hle hb) hm hloc⟩

/-- Reading a `pubProto`-governed root: null, or a pointer that already carries
    the ordering.  `undef` is excluded on the third branch by `wf`.

    This is `proto_of_load` specialised, and it is what a client would actually
    call. -/
theorem pub_load (d : Address) (v : Val) (root : Address) (deps : List TVal)
    {s₀ r s} (hg : Governs (pubProto d v) root s₀)
    (h : LoadPost root deps s₀ r s) :
    s.stuck = true ∨ r.val = Val.undef ∨ r.val = Val.num 0 ∨
      (r.val = Val.loc d 0 ∧
        ∃ (t' : Ts) (m : Msg), s.mem[t']? = some m ∧ m.loc = d ∧
          m.val = v ∧ t' ≤ r.view) := by
  rcases proto_of_load (pubProto d v) root deps (pubProto_stable d v) hg h with
    hstuck | hu | ⟨hwf, hk⟩
  · exact Or.inl hstuck
  · exact Or.inr (Or.inl hu)
  · rcases hwf with hnull | hptr
    · exact Or.inr (Or.inr (Or.inl hnull))
    · exact Or.inr (Or.inr (Or.inr ⟨hptr, hk hptr⟩))

/-- **The composition, and the point of the whole subsection above.**

    Same conclusion as `pub_load`, but the load happens in `s₁`, which Remote
    reached from `s₀` by doing whatever it liked: reading the root, chasing the
    descriptor pointer, writing anywhere it can reach that it has not disowned,
    for arbitrarily many steps.  The reader still gets the ordering.

    The one hypothesis is `root.label ∈ s₀.rdisowned` -- single-writer RCU,
    which is what RCU is.  Note what is *not* hypothesised: nothing about `d`.
    Remote may write the descriptor to its heart's content; the protocol lives
    at the root, and the bound it hands out is a claim about the past, which is
    why interference at `d` cannot retract it.  That is `Stable` earning its
    keep rather than being bookkeeping.

    For a multi-writer root, swap `governs_of_env_disowned` for
    `governs_of_env_rely` and discharge the rely condition from Remote's code.
    Nothing else changes. -/
theorem pub_load_under_env (d : Address) (v : Val) (root : Address)
    (deps : List TVal) {s₀ s₁ r s}
    (hg : Governs (pubProto d v) root s₀)
    (hown : root.label ∈ s₀.rdisowned) (henv : EnvPost s₀ s₁)
    (h : LoadPost root deps s₁ r s) :
    s.stuck = true ∨ r.val = Val.undef ∨ r.val = Val.num 0 ∨
      (r.val = Val.loc d 0 ∧
        ∃ (t' : Ts) (m : Msg), s.mem[t']? = some m ∧ m.loc = d ∧
          m.val = v ∧ t' ≤ r.view) :=
  pub_load d v root deps
    (governs_of_env_disowned (pubProto d v) root (pubProto_stable d v) hg henv
      hown) h

/-! ### Composing two protocols: pinning the value

`pub_hides_stale` *bounds* -- everything below the initialising write is
unreadable -- where what a client wants is a *pin*: the dereference returns `v`.
Closing that gap is the test of whether `Proto` is an abstraction or just a
repackaging of §8, because the pin is supposed to come from **composing** a
second protocol at the descriptor with the first one at the root.

It does, but only after one attempt fails, and the failure is the interesting
part.

**The attempt that does not work** is to say the descriptor is immutable
outright: `Governs (immProto v) d`, every message at `d` holds `v`. That is
trivially stable, it pins immediately, and it is **worthless**, because it is
false in any state where RCU is hard. The pre-initialisation message at `d` --
the one holding `undef` -- is exactly what an unfenced reader can still see, and
a hypothesis that excludes it has assumed the bug away. §8's scenario seeds that
message deliberately; delete it and the model says a lone write is visible to
everyone, which is true and useless.

**What works** is to notice that immutability is not a property of the location
but of the location *from publication on*. So the second protocol is indexed by
a floor:

* below the floor, `pub_hides_stale` (ordering) does the work -- coherence hides
  the stale message because the reader's view covers the publishing write;
* at or above the floor, the descriptor protocol (exclusion) does the work --
  nothing else was ever written there.

Neither half suffices and they meet exactly at `t₀`. That is the real content of
"publish then don't touch it", and it is why the headline claim of this section
is safety *without* exclusion rather than safety *from ordering alone*: the
bound is free, the pin is not. -/

/-- `Governs`, from a timestamp on.

    `Governs P a = GovernsFrom P a 0`, and the generalisation is forced by the
    client above rather than added speculatively: a protocol that only starts
    holding at publication cannot be stated any other way. -/
def GovernsFrom (P : Proto) (a : Address) (t₀ : Ts) (s : Machine) : Prop :=
  ∀ (t : Ts) (m : Msg), t₀ ≤ t → s.mem[t]? = some m → m.loc = a →
    P.wf m.val ∧ P.knows m.val m.view s

theorem governsFrom_of_governs (P : Proto) (a : Address) (t₀ : Ts)
    {s : Machine} (hg : Governs P a s) : GovernsFrom P a t₀ s :=
  fun t m _ hm hloc => hg t m hm hloc

/-- Ownership preserves the floor-indexed form too, so the composition inherits
    everything the subsection above proved.  Same two-case split as
    `governs_mono`; the new messages are excluded rather than checked. -/
theorem governsFrom_of_env_disowned (P : Proto) (a : Address) (t₀ : Ts)
    {s₀ s : Machine} (hS : Stable P) (hg : GovernsFrom P a t₀ s₀)
    (henv : EnvPost s₀ s) (hown : a.label ∈ s₀.rdisowned) :
    GovernsFrom P a t₀ s := by
  intro t m ht hm hloc
  rcases Nat.lt_or_ge t s₀.mem.size with hlt | hge
  · rw [henv.ext.2 t hlt] at hm
    obtain ⟨hwf, hk⟩ := hg t m ht hm hloc
    exact ⟨hwf, hS _ _ s₀ s henv.ext hk⟩
  · exact absurd (hloc ▸ hown) (henv.frozen t m hge hm)

/-- The descriptor protocol: whatever is here is the published value.

    `knows` is `True`, and that is the honest shape -- this protocol carries no
    ordering at all.  All of the ordering in the composed theorem comes from
    `pubProto` at the root; this one contributes only exclusion.  Keeping the
    two in separate protocols is what makes that visible. -/
def immProto (v : Val) : Proto where
  wf x := x = v
  knows _ _ _ := True

theorem immProto_stable (v : Val) : Stable (immProto v) :=
  fun _ _ _ _ _ _ => True.intro

/-! Two arithmetic lemmas so a caller can discharge the dependency bound from
`r ∈ deps` rather than by unfolding `loadBound` at the call site. -/

private theorem foldl_view_ge : ∀ (ds : List TVal) (acc : Ts),
    acc ≤ ds.foldl (fun a d => max a d.view) acc := by
  intro ds
  induction ds with
  | nil => intro acc; exact Nat.le_refl _
  | cons d ds ih => intro acc; exact Nat.le_trans (Nat.le_max_left acc d.view) (ih _)

private theorem foldl_view_mem (r : TVal) : ∀ (ds : List TVal), r ∈ ds →
    ∀ (acc : Ts), r.view ≤ ds.foldl (fun a d => max a d.view) acc := by
  intro ds
  induction ds with
  | nil => intro h; simp at h
  | cons d ds ih =>
      intro h acc
      rcases List.mem_cons.mp h with he | ht
      · subst he
        exact Nat.le_trans (Nat.le_max_right acc r.view) (foldl_view_ge ds _)
      · exact ih ht _

/-- A dependency's view is covered by the bound of a load that carries it.
    This is `keepDep`'s guarantee, stated where a proof can use it. -/
theorem le_loadBound_of_mem (s : Machine) (a : Address) (deps : List TVal)
    (r : TVal) (h : r ∈ deps) : r.view ≤ loadBound s a deps := by
  have h1 : r.view ≤ tvView deps := foldl_view_mem r deps h 0
  simp only [loadBound, tvBound]
  exact Nat.le_trans h1 (Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))))

/-- **The pin.**  Given a write at `t₀` that the reader's bound covers, and a
    descriptor settled from `t₀` on, the dereference returns `v`.

    Three cases, and each is discharged by a different one of the two
    hypotheses, which is what makes the composition non-trivial:

    * *stuck* -- conceded, as everywhere in this file.
    * *nothing readable* -- impossible, because `unwritten_of_no_readable` turns
      that disjunct into "no message at `d` anywhere" and `hinit` is one.  Note
      this needs only **existence**, not ordering.
    * *a message was read* -- it cannot be below `t₀`, because
      `not_readable_of_later` says the publishing write hides everything under
      it at any bound that covers it; so the floor applies and `wf` pins the
      value.

    The middle case is worth dwelling on: it is the one that says the reader
    does not get `undef`, and it is bought by the *existence* of the write
    rather than by any fence. The ordering is spent entirely on the third
    case. -/
theorem deref_pins (d : Address) (v : Val) (depsD : List TVal)
    {s₁ r' s : _} {t₀ : Ts} {m₀ : Msg}
    (hinit : s₁.mem[t₀]? = some m₀) (hloc : m₀.loc = d)
    (hcov : t₀ ≤ loadBound s₁ d depsD)
    (himm : GovernsFrom (immProto v) d t₀ s₁)
    (h : LoadPost d depsD s₁ r' s) :
    s.stuck = true ∨ r'.val = v := by
  rcases h.read with hstuck | ⟨_, hnone⟩ | ⟨hmsg, hrd⟩
  · exact Or.inl hstuck
  · exfalso
    have hw := unwritten_of_no_readable s₁.mem d (loadBound s₁ d depsD) hnone t₀
    rw [hinit] at hw
    simp [hloc] at hw
  · refine Or.inr ?_
    have hge : t₀ ≤ r'.rts := by
      rcases Nat.lt_or_ge r'.rts t₀ with hlt | hge
      · exfalso
        rw [not_readable_of_later hlt hcov hinit hloc] at hrd
        simp at hrd
      · exact hge
    exact (himm r'.rts ⟨d, r'.val, r'.view⟩ hge hmsg rfl).1

/-- **The composition**, and what §14 was built to be able to say.

    A reader loads the root, gets the pointer, and dereferences it *carrying the
    dependency* (`hdep : r ∈ depsD` -- which is what `keepDep` is for).  What
    comes back is the published value: not `undef`, and not a stale one either.

    This is `published_read_is_initialised` (§8) obtained by composition rather
    than as a five-hypothesis chain about six machines, and the two hypotheses
    are now separable and individually meaningful: `hroot` is ordering, `himm`
    is exclusion, and the proof shows exactly where each is spent.

    `himm` is stated as "settled from wherever the publishing write is" because
    the floor is existentially bound inside `pubProto.knows`, and that phrasing
    is also the accurate statement of the discipline: the descriptor becomes
    immutable when it is published, not before. -/
theorem pub_deref_pins (d : Address) (v : Val) (root : Address)
    (deps depsD : List TVal) {s₀ r s₁ r' s}
    (hroot : Governs (pubProto d v) root s₀)
    (hload : LoadPost root deps s₀ r s₁)
    (hptr : r.val = Val.loc d 0) (hdep : r ∈ depsD)
    (himm : ∀ (t₀ : Ts) (m₀ : Msg), s₁.mem[t₀]? = some m₀ → m₀.loc = d →
      m₀.val = v → GovernsFrom (immProto v) d t₀ s₁)
    (hderef : LoadPost d depsD s₁ r' s) :
    s.stuck = true ∨ r'.val = v := by
  rcases proto_of_load (pubProto d v) root deps (pubProto_stable d v) hroot hload
    with hstuck | hu | ⟨_, hk⟩
  -- `stuck` is sticky across a load, which is exactly what `LoadPost.stuck`
  -- claims; the first load's failure has to be carried through the second.
  · exact Or.inl (hderef.stuck hstuck)
  · rw [hptr] at hu; simp at hu
  · obtain ⟨t₀, m₀, hm₀, hloc₀, hval₀, hle⟩ := hk hptr
    exact deref_pins d v depsD hm₀ hloc₀
      (Nat.le_trans hle (le_loadBound_of_mem s₁ d depsD r hdep))
      (himm t₀ m₀ hm₀ hloc₀ hval₀) hderef

/-! ### The controls

Three, because the section makes three claims that could each be empty.

The first claim is that the **existential phrasing of `knows` was necessary**,
not merely sufficient.  A reader could reasonably suspect it of being a
convenience that made one proof shorter.  It is not: the universal phrasing is
refutably unstable, and `badProto_not_stable` is that refutation, at compile
time rather than by demonstration.

The second claim is that the **write-exclusion in the interference lemmas is
load-bearing**.  All three of them differ only in how they discharge
`governs_mono`'s `hnew`, so one may reasonably ask whether `hnew` follows from
`Extends` anyway.  `governs_not_free_of_extends` says it does not.

The third claim is that `Governs` is **not vacuously establishable**.
`pubProto`'s `knows` is decidable on a concrete state, so the publication
program can be run both ways and the clause checked.  It holds with the
writer's `dmb ishst` and fails without it -- so the protocol's knowledge is
exactly what the fence buys, which is the claim §6.5 makes in prose. -/

/-- The tempting phrasing: *everything you can see at `d` is initialised.*

    This is what one writes first, and it is what `Governs` would need if the
    protocol were to pin the dereferenced value rather than merely bound it. -/
def badProto (d : Address) (v : Val) : Proto where
  wf _ := True
  knows _ t s := ∀ (t' : Ts) (m : Msg), s.mem[t']? = some m → m.loc = d →
    t' ≤ t → m.val = v

/-- **And it is not stable.**  Someone writes garbage at `d`, and the knowledge
    a reader already had becomes false retroactively.

    The witness is as small as it can be: empty memory, where the clause holds
    vacuously, extended by one bad message.  No fence, ordering, or view is
    involved, which is the point -- this is not an ordering bug and no ordering
    fixes it.  It is the same unstable universal, arrived at from a third
    direction. -/
theorem badProto_not_stable :
    ¬ Stable (badProto ⟨0, 0⟩ (Val.num 1)) := by
  intro hS
  -- `oracle` has no default, so the two witness states name it explicitly.
  have hext : Extends { mem := #[], oracle := [] }
      { mem := #[⟨⟨0, 0⟩, Val.num 2, 0⟩], oracle := [] } :=
    ⟨by simp, by intro t ht; simp at ht⟩
  -- Vacuously true of empty memory, and false one append later.
  have hk : (badProto ⟨0, 0⟩ (Val.num 1)).knows Val.undef 0
      { mem := #[], oracle := [] } := by
    intro t' m hm _ _
    simp at hm
  have := hS Val.undef 0 _ _ hext hk 0 ⟨⟨0, 0⟩, Val.num 2, 0⟩ rfl rfl (Nat.le_refl _)
  simp at this

/-- **`Governs` is not free from `Extends`**, so the write-exclusion in
    `governs_of_env_unreachable` and `governs_of_env_disowned` is carrying the
    argument rather than decorating it.

    The witness is a genuinely *stable* protocol governing a location
    vacuously, losing `Governs` to a single append.  That matters: it rules out
    the repair that suggests itself first, which is to strengthen `Stable`.
    Strengthening it cannot help, because the message that breaks the protocol
    never carried the knowledge in the first place -- there is nothing for a
    stability condition to preserve.  The obligation genuinely belongs to
    whoever appended. -/
theorem governs_not_free_of_extends :
    ¬ ∀ (P : Proto) (a : Address) (s₀ s : Machine), Stable P → Governs P a s₀ →
        Extends s₀ s → Governs P a s := by
  intro h
  have hext : Extends { mem := #[], oracle := [] }
      { mem := #[⟨⟨0, 0⟩, Val.num 1, 0⟩], oracle := [] } :=
    ⟨by simp, by intro t ht; simp at ht⟩
  -- Vacuous on empty memory, for any protocol at all.
  have hg : Governs (pubProto ⟨1, 0⟩ (Val.num 7)) ⟨0, 0⟩
      { mem := #[], oracle := [] } := by
    intro t m hm _; simp at hm
  have hbad := h _ _ _ _ (pubProto_stable ⟨1, 0⟩ (Val.num 7)) hg hext 0
    ⟨⟨0, 0⟩, Val.num 1, 0⟩ rfl rfl
  -- `num 1` is neither null nor the descriptor pointer, so `wf` already fails;
  -- the appended message did not have to attack `knows` to break the protocol.
  have hw : Val.num 1 = Val.num 0 ∨ Val.num 1 = Val.loc ⟨1, 0⟩ 0 := hbad.1
  rcases hw with h1 | h1 <;> simp at h1

/-! ### The executable half -/

/-- `pubProto.knows` as a `Bool`, for the scenario below.  Decidable because
    `mem` is finite: search it for an initialising write at or below `t`. -/
def pubKnowsAt (d : Address) (v : Val) (s : Machine) (t : Ts) : Bool :=
  (List.range s.mem.size).any fun t' =>
    (s.mem[t']?.elim false fun m => decide (m.loc = d) && decide (m.val = v)) &&
    decide (t' ≤ t)

/-- Publish with and without the writer's store-store fence, and check the
    protocol's knowledge clause at the view the root's message actually
    carries.

    Same program as `publicationScenario` (§8); what differs is that this one
    interrogates the *protocol* rather than what Remote managed to read. -/
def protoScenario (fenced : Bool) : String :=
  let root : Address := ⟨0, 0⟩
  let data : Address := ⟨1, 0⟩
  let v := Val.num 7
  let s0 : Machine :=
    { mem := #[⟨data, Val.undef, 0⟩, ⟨root, Val.num 0, 0⟩],
      sizes := [1, 1], roots := [root], rknow := [⟨root, 0⟩], oracle := [] }
  let (_, s) := (publishVia root data v fenced).run s0
  -- The root's newest message is the published pointer; read its view off the
  -- final memory rather than assuming which timestamp it landed at.
  let rootTs := (List.range s.mem.size).filter fun t =>
    s.mem[t]?.elim false fun m => decide (m.loc = root)
  let tv := (rootTs.reverse.head?).bind (fun t => s.mem[t]?) |>.elim 0 (·.view)
  let initTs := (List.range s.mem.size).filter fun t =>
    s.mem[t]?.elim false fun m => decide (m.loc = data) && decide (m.val = v)
  s!"fenced={fenced}: root-msg-view={tv}, init-write-at={initTs}, " ++
  s!"knows-holds={pubKnowsAt data v s tv}"

def protoDemo : String :=
  "  " ++ protoScenario false ++ "\n  " ++ protoScenario true

/-- `Governs (pubProto d v) root` as a `Bool`.  The image of the `Prop`, clause
    for clause: every message at `root` is null or the pointer, and if it is
    the pointer then the initialising write sits at or below its view. -/
def pubGovernsB (d : Address) (v : Val) (root : Address) (s : Machine) : Bool :=
  (List.range s.mem.size).all fun t =>
    s.mem[t]?.elim true fun m =>
      !decide (m.loc = root) ||
        ((decide (m.val = Val.num 0) || decide (m.val = Val.loc d 0)) &&
          (!decide (m.val = Val.loc d 0) || pubKnowsAt d v s m.view))

/-- `pub_load_under_env`, run.

    The fenced publication, then one environment step, with the oracle told to
    take the most damaging option available: write at the root, and write a
    pointer rather than null -- because null would satisfy `wf` and prove
    nothing.

    `owned=true` puts the root's label in `rdisowned`, so `rstoreStep` drops the
    write and the protocol survives.  `owned=false` is the same run without
    that, and it is there because the first row on its own is consistent with
    Remote having been harmless: the environment must be shown able to break
    the protocol when the hypothesis is removed, or the hypothesis is not what
    is doing the work. -/
def protoEnvScenario (owned : Bool) : String :=
  let root : Address := ⟨0, 0⟩
  let data : Address := ⟨1, 0⟩
  let v := Val.num 7
  let s0 : Machine :=
    { mem := #[⟨data, Val.undef, 0⟩, ⟨root, Val.num 0, 0⟩],
      sizes := [1, 1], roots := [root], rknow := [⟨root, 0⟩],
      rdisowned := if owned then [root.label] else [],
      -- store, store, then: address 0 (the root), action 2 (write), value 1
      -- (the pointer out of `rknow`, not null).
      oracle := [0, 0, 0, 2, 1] }
  let (_, s) := (do publishVia root data v true; renv : M Unit).run s0
  s!"owned={owned}: mem={s.mem.size}, governs={pubGovernsB data v root s}"

def protoEnvDemo : String :=
  "  " ++ protoEnvScenario false ++ "\n  " ++ protoEnvScenario true

/-- `GovernsFrom (immProto v) d t₀` as a `Bool`, with `t₀` taken to be the
    earliest write of `v` at `d` -- i.e. the floor the composed theorem would
    get out of `pubProto.knows`. `false` if there is no such write at all. -/
def settledFromB (d : Address) (v : Val) (s : Machine) : Bool :=
  match (List.range s.mem.size).filter fun t =>
      s.mem[t]?.elim false fun m => decide (m.loc = d) && decide (m.val = v) with
  | [] => false
  | t₀ :: _ =>
      (List.range s.mem.size).all fun t =>
        !decide (t₀ ≤ t) ||
          (s.mem[t]?.elim true fun m => !decide (m.loc = d) || decide (m.val = v))

/-- `pub_deref_pins`, run, and the control for it.

    Publish with the fence, then dereference the root carrying the dependency.
    The second row overwrites the descriptor *after* publishing, which is the
    one thing the composed theorem forbids.

    Both the hypothesis and the conclusion are printed, and the point of the
    control is that they fail **together**: `settled=false` is `himm` failing,
    `deref=99` is the pin failing. A control that only showed the conclusion
    breaking would not establish that this hypothesis is the one responsible. -/
def pinScenario (immutable : Bool) : String :=
  let root : Address := ⟨0, 0⟩
  let data : Address := ⟨1, 0⟩
  let v := Val.num 7
  let s0 : Machine :=
    { mem := #[⟨data, Val.undef, 0⟩, ⟨root, Val.num 0, 0⟩],
      sizes := [1, 1], roots := [root], rknow := [⟨root, 0⟩],
      oracle := [0, 0, 0, 0, 0, 0] }
  let (res, s) :=
    (do publishVia root data v true
        if immutable then pure () else mstore data (Val.num 99)
        let p ← mload root []
        mload data [p] : M TVal).run s0
  s!"immutable={immutable}: settled={settledFromB data v s}, " ++
  s!"deref={repr res.val}, stuck={s.stuck}"

def pinDemo : String :=
  "  " ++ pinScenario true ++ "\n  " ++ pinScenario false



/-! ## 15. Architecture refinement: the relation, and the lemma it rests on

§4.1 checks `behaviours arm ⊇ behaviours tso` by running 89<!--@suite--> shapes under both
rule sets and finding 0 escapes.  That is a gate, not a theorem, and this
section is the first half of replacing it with one.  **It deliberately stops
before the simulation**: the point is to fix the relation and discharge the
lemma everything else will rest on, so that if the relation is wrong we find out
here rather than fifty proofs later.

**Why the obvious argument fails.**  One would like to say: every TSO
transition is an ARM transition, so containment is immediate.  It is false.
There are nine architecture-sensitive points in this file, now all findable by
`sed -n '/\.tso/{=;p}'`, and eight of them are a `max` that makes a *bound*
larger under `tso` -- a restriction, which behaves.  The ninth is `lockFence`:
a TSO read-modify-write performs an extra `stepFence .sy` that the ARM one does
not.  So the TSO post-state is **not** a state the corresponding ARM step
produces, and there is no lockstep simulation with identity on states.
`fence_moves_the_state` below is the one-line refutation, so that this is
recorded as checked rather than believed.

**The relation.**  Carry the two runs side by side with ARM's views *below*
TSO's: memory equal on `loc` and `val` with ARM's per-message `view` ≤ TSO's,
registers equal on `val` and `rts` with `view` ≤, programs and promise sets
equal, and every component of `VState` pointwise ≤.

**Why that works, in one sentence per direction.**  Lowering a bound never
removes a transition -- `hiddenFrom` is monotone in `bound`, so a smaller bound
hides fewer writes and ARM's readable set *contains* TSO's (`readable_antitone`,
and `arm_reads_what_tso_reads` for the form the simulation wants); and a store's
guard is `ob < t`, which only gets easier as `ob` shrinks
(`arm_fulfils_what_tso_fulfils`).  `lockFence` is then not a problem but an
instance of the relation doing its job: a fence only ever *raises* views
(`VLe_stepFence`), so TSO taking one while ARM does not preserves ARM ≤ TSO
(`ThreadLe_of_fence_right`).

**One worry discharged by inspection.**  If a
counterexample existed it would be at `mstoreView` -- a *stronger* publication
rule under `tso` could make an outcome reachable that `arm` cannot produce.  It
cannot happen here, and the reason is visible in the signature rather than in a
proof: `storeMview` takes no `Arch` argument, and neither does the `mview` inside
`stepRmw` or the `M` layer's `mstoreView`.  Publication is architecture-blind in
this model; the architecture only ever moves *bounds*.  That is worth stating
precisely because it was the predicted failure and it is not one. -/

/-! ### The lemma

Everything else in this section is bookkeeping around these two. -/

/-- A smaller bound hides no more than a larger one.  Immediate from the shape
    of `hiddenFrom`: the witness it searches for lives in `range (bound+1)`, and
    that list only grows. -/
theorem hiddenFrom_antitone {mem : Memory} {a : Address} {t b b' : Ts}
    (hb : b' ≤ b) (h : hiddenFrom mem a t b' = true) :
    hiddenFrom mem a t b = true := by
  unfold hiddenFrom at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨t', hmem, hp⟩ := h
  refine ⟨t', ?_, hp⟩
  simp only [List.mem_range] at hmem ⊢
  exact Nat.lt_of_lt_of_le hmem (Nat.succ_le_succ hb)

/-- **Lowering a bound never removes a transition.**  This is the lemma the
    whole containment argument rests on, and it is true for a structural reason
    rather than by luck: `readable` is `written && !hidden`, the written half
    does not mention the bound at all, and the hidden half is monotone. -/
theorem readable_antitone {mem : Memory} {a : Address} {t b b' : Ts}
    (hb : b' ≤ b) (h : readable mem a t b = true) : readable mem a t b' = true := by
  unfold readable at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  obtain ⟨hw, hh⟩ := h
  refine ⟨hw, ?_⟩
  cases hcase : hiddenFrom mem a t b' with
  | false => simp
  | true => rw [hiddenFrom_antitone hb hcase] at hh; simp at hh

/-! ### The relation -/

/-- Two forwarding lists (`WeakMem.VState.fwd`): the same timestamps in the
    same order, the left views lower. -/
inductive FwdLe : List (Ts × Ts) → List (Ts × Ts) → Prop
  | nil : FwdLe [] []
  | cons {t f g : Ts} {l1 l2 : List (Ts × Ts)} : f ≤ g → FwdLe l1 l2 → FwdLe ((t, f) :: l1) ((t, g) :: l2)

theorem FwdLe.refl : ∀ l : List (Ts × Ts), FwdLe l l
  | [] => FwdLe.nil
  | _ :: l => FwdLe.cons (Nat.le_refl _) (FwdLe.refl l)

theorem FwdLe.trans {l1 l2 l3 : List (Ts × Ts)} (h₁ : FwdLe l1 l2) (h₂ : FwdLe l2 l3) :
    FwdLe l1 l3 := by
  induction h₁ generalizing l3 with
  | nil => cases h₂; exact FwdLe.nil
  | cons hfg _ ih =>
      cases h₂ with
      | cons hgh h₂' => exact FwdLe.cons (Nat.le_trans hfg hgh) (ih h₂')

theorem FwdLe.find {l1 l2 : List (Ts × Ts)} (h : FwdLe l1 l2) (t : Ts) :
    (l1.find? (fun p => p.1 == t) = none ∧ l2.find? (fun p => p.1 == t) = none) ∨
    ∃ p q, l1.find? (fun p => p.1 == t) = some p ∧ l2.find? (fun p => p.1 == t) = some q ∧
      p.2 ≤ q.2 := by
  induction h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons t' f g l1 l2 hfg _ ih =>
      by_cases hp : t' = t
      · exact Or.inr ⟨(t', f), (t', g), by simp [hp], by simp [hp], hfg⟩
      · have hb : (t' == t) = false := by simp [hp]
        simp only [List.find?_cons, hb]
        exact ih

/-- `VState` pointwise.  Six fields, six inequalities, no cleverness. -/
structure VLe (v w : VState) : Prop where
  coh : ∀ a, v.coh a ≤ w.coh a
  vRd : v.vRd ≤ w.vRd
  vWr : v.vWr ≤ w.vWr
  vCtrl : v.vCtrl ≤ w.vCtrl
  vPreBase : v.vPreBase ≤ w.vPreBase
  vRelSt : v.vRelSt ≤ w.vRelSt
  /-- Both runs pick the same timestamps, so they own the same writes. -/
  mine : v.mine = w.mine
  /-- The same forwarding entries, at the same timestamps; ARM's views lower,
      since they are joins of register views and timestamps (`fwdOf`). -/
  fwd : FwdLe v.fwd w.fwd

theorem VLe.refl (v : VState) : VLe v v :=
  ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
   Nat.le_refl _, Nat.le_refl _, rfl, FwdLe.refl _⟩

theorem VLe.trans {u v w : VState} (h₁ : VLe u v) (h₂ : VLe v w) : VLe u w :=
  ⟨fun a => Nat.le_trans (h₁.coh a) (h₂.coh a),
   Nat.le_trans h₁.vRd h₂.vRd, Nat.le_trans h₁.vWr h₂.vWr,
   Nat.le_trans h₁.vCtrl h₂.vCtrl, Nat.le_trans h₁.vPreBase h₂.vPreBase,
   Nat.le_trans h₁.vRelSt h₂.vRelSt, h₁.mine.trans h₂.mine, h₁.fwd.trans h₂.fwd⟩

/-- A related pair of states agrees on *whether* a read is of an own plain
    write, and the ARM forwarding view is the lower. -/
theorem VLe.ownFwd {v w : VState} (h : VLe v w) (t : Ts) :
    (ownFwd v t = none ∧ ownFwd w t = none) ∨
    ∃ f g, ownFwd v t = some f ∧ ownFwd w t = some g ∧ f ≤ g := by
  unfold WeakMem.ownFwd
  rw [h.mine]
  split
  · rcases h.fwd.find t with ⟨h1, h2⟩ | ⟨p, q, h1, h2, hle⟩
    · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2]
      exact ⟨_, _, rfl, rfl, Nat.le_min.2 ⟨Nat.min_le_left _ _, Nat.le_trans (Nat.min_le_right _ _) hle⟩⟩
  · left; exact ⟨rfl, rfl⟩

theorem VLe.rdV {v w : VState} (h : VLe v w) (pairs : List Ts) (t : Ts) {mv mv' : Ts}
    (hm : mv ≤ mv') : rdV v pairs t mv ≤ rdV w pairs t mv' := by
  unfold Promises.rdV
  rcases h.ownFwd t with ⟨h1, h2⟩ | ⟨f, g, h1, h2, hle⟩
  · rw [h1, h2]; exact Nat.max_le.2 ⟨Nat.le_trans (Nat.le_refl _) (Nat.le_max_left _ _), Nat.le_trans hm (Nat.le_max_right _ _)⟩
  · rw [h1, h2]; exact hle

theorem VLe.acqV {v w : VState} (h : VLe v w) (pairs : List Ts) (t : Ts) {mv mv' : Ts}
    (hm : mv ≤ mv') : acqV v pairs t mv ≤ acqV w pairs t mv' := by
  unfold Promises.acqV
  rcases h.ownFwd t with ⟨h1, h2⟩ | ⟨f, g, h1, h2, hle⟩
  · rw [h1, h2]
    exact Nat.max_le.2 ⟨Nat.le_trans hm (Nat.le_max_left _ _),
      Nat.le_trans (Nat.le_of_eq (by unfold extTs; rw [h.mine])) (Nat.le_max_right _ _)⟩
  · rw [h1, h2]; exact hle

/-- A register.  `val` and `rts` are **equal**, not related: the two runs pick
    the same timestamps, so what was read and from where are the same; only the
    *view* inherited from the message can differ, and only downward. -/
structure TValLe (x y : TVal) : Prop where
  val : x.val = y.val
  rts : x.rts = y.rts
  view : x.view ≤ y.view

structure ThreadLe (ta tt : Thread) : Prop where
  prog : ta.prog = tt.prog
  promises : ta.promises = tt.promises
  regs : ∀ r, TValLe (ta.regs r) (tt.regs r)
  vs : VLe ta.vs tt.vs

theorem ThreadLe.refl (th : Thread) : ThreadLe th th :=
  ⟨rfl, rfl, fun _ => ⟨rfl, rfl, Nat.le_refl _⟩, VLe.refl _⟩

/-- Memory: same length, same addresses, same values, ARM's views lower.

    Same *addresses* is what keeps `readable` comparable at all -- it depends on
    memory only through `m.loc` -- and same *values* is what makes the final
    register outcomes comparable, which is what the containment statement is
    actually about. -/
def MemLe (ma mt : Memory) : Prop :=
  ma.size = mt.size ∧
  ∀ (t : Ts) (m n : Msg), ma[t]? = some m → mt[t]? = some n →
    m.loc = n.loc ∧ m.val = n.val ∧ m.view ≤ n.view

structure ConfigLe (ca ct : Config) : Prop where
  mem : MemLe ca.mem ct.mem
  pairs : ca.pairs = ct.pairs
  size : ca.ths.size = ct.ths.size
  ths : ∀ (i : Nat) (ta tt : Thread), ca.ths[i]? = some ta → ct.ths[i]? = some tt →
    ThreadLe ta tt

/-! ### A fence only raises views

This is what absorbs `lockFence`, the one point where the two architectures do
not take the same step. -/

/-- Every `stepFence` is increasing on `VState`.  All three cases are `max`
    against the current value. -/
theorem VLe_stepFence (th : Thread) (f : Fence) : VLe th.vs (stepFence th f).vs := by
  cases f
  · exact ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      Nat.le_max_left _ _, Nat.le_refl _, rfl, FwdLe.refl _⟩
  · exact ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      Nat.le_refl _, Nat.le_max_left _ _, rfl, FwdLe.refl _⟩
  · exact ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      Nat.le_max_left _ _, Nat.le_max_left _ _, rfl, FwdLe.refl _⟩

/-- **TSO may fence where ARM does not, and the relation survives.**

    This is `lockFence` discharged: it is the one point
    with no lockstep counterpart and it is, but the refinement does not need a
    counterpart -- it needs the TSO side to stay *above*, and a fence can only
    push it further up. -/
theorem ThreadLe_of_fence_right {ta tt : Thread} (h : ThreadLe ta tt) (f : Fence) :
    ThreadLe ta (stepFence tt f) := by
  refine ⟨?_, ?_, ?_, VLe.trans h.vs (VLe_stepFence tt f)⟩
  · cases f <;> exact h.prog
  · cases f <;> exact h.promises
  · cases f <;> exact h.regs

/-- **The control**: the fence genuinely moves the state, so \"identity on
    states\" was never available and the refinement is not ceremony.

    One `VState` with a read recorded and no fence yet; `dmb sy` raises
    `vPreBase` from 0 to 1. -/
theorem fence_moves_the_state :
    ∃ (th : Thread) (f : Fence), (stepFence th f).vs ≠ th.vs := by
  refine ⟨{ prog := [], regs := fun _ => TVal.mk0 (Val.num 0),
            vs := { VState.init with vRd := 1 }, promises := [] }, .sy, ?_⟩
  intro hcon
  have h := congrArg VState.vPreBase hcon
  simp [stepFence, VState.init] at h

/-! ### The dependency joins

Two `foldl`s, and they are consumed asymmetrically: `depView` only has to be
monotone, `depRts` has to be *equal*, because a store's ordering bound reads
timestamps and the two runs agree on those exactly.

> One tooling note, because it cost real time and will cost it again.  **`omega`
> does not see through `max` when the implicit type argument is `Ts`.**  It
> handles `max` at a literal `Nat` perfectly well, but `Ts` is an `abbrev` and
> `omega`'s recogniser does not unfold it, so a goal like
> `max a b ≤ max c d` at `Ts` reports "No usable constraints found" -- not a
> failed proof search, a *refusal to look*.  Neither `show ... : Nat` nor
> `simp only [Nat.max_def]` repairs it.  Everything in §15 is therefore built
> from `le_max_le` below rather than from `omega`, which is also faster and
> gives better errors. -/

/-- Pointwise monotonicity of `max`.  The workhorse of §15. -/
private theorem le_max_le {a b c d : Ts} (h₁ : a ≤ c) (h₂ : b ≤ d) :
    max a b ≤ max c d :=
  Nat.max_le.2 ⟨Nat.le_trans h₁ (Nat.le_max_left _ _),
                Nat.le_trans h₂ (Nat.le_max_right _ _)⟩

private theorem foldl_max_mono {α : Type} (f g : α → Ts) (hfg : ∀ x, f x ≤ g x) :
    ∀ (l : List α) (acc acc' : Ts), acc ≤ acc' →
      l.foldl (fun a x => max a (f x)) acc ≤ l.foldl (fun a x => max a (g x)) acc' := by
  intro l
  induction l with
  | nil => intro acc acc' h; exact h
  | cons x xs ih =>
      intro acc acc' h
      exact ih _ _ (le_max_le h (hfg x))


theorem depView_mono {ra rt : Reg → TVal} (h : ∀ r, (ra r).view ≤ (rt r).view)
    (deps : List Reg) : depView ra deps ≤ depView rt deps :=
  foldl_max_mono _ _ h deps 0 0 (Nat.le_refl _)

theorem depRts_congr {ra rt : Reg → TVal} (h : ∀ r, (ra r).rts = (rt r).rts)
    (deps : List Reg) : depRts ra deps = depRts rt deps :=
  Nat.le_antisymm
    (foldl_max_mono _ _ (fun r => Nat.le_of_eq (h r)) deps 0 0 (Nat.le_refl _))
    (foldl_max_mono _ _ (fun r => Nat.le_of_eq (h r).symm) deps 0 0 (Nat.le_refl _))

/-- A load's bound is monotone for the same reason a store's is, and it needs
    *both* of the previous two lemmas: `TValLe` relaxes `view` and pins `rts`,
    and `depBound` joins them, so the join is monotone. -/
theorem depBound_mono {ra rt : Reg → TVal} (hv : ∀ r, (ra r).view ≤ (rt r).view)
    (hr : ∀ r, (ra r).rts = (rt r).rts) (deps : List Reg) :
    depBound ra deps ≤ depBound rt deps :=
  le_max_le (depView_mono hv deps) (Nat.le_of_eq (depRts_congr hr deps))

/-! ### The architecture-sensitive quantities are monotone

One lemma per arch-taking `def`.  Together these are the statement that the
architecture only ever moves bounds, and only ever upward under `tso`.

Each of the three definitions is unfolded once, by `rfl`, into a shape `omega`
can chew on.  That is deliberate: `simp only [readBoundOf]` leaves the
`if Arch.arm = Arch.tso` unreduced and `omega` then sees an opaque atom, and
full `simp` would silently reassociate the `max`es.  Unfolding by `rfl` is both
cheaper and immune to simp-set drift. -/

/-- `readBoundOf` at `arm`: the `ordered` term is `0`.  By `rfl`, because
    `Arch` has decidable equality by `deriving` and the discriminant is a
    literal constructor. -/
private theorem readBoundOf_arm (vs : VState) (dv : Ts) (a : Address) :
    readBoundOf .arm vs dv a = max (max (max vs.vPreBase dv) (vs.coh a)) 0 := rfl

/-- `readBoundOf` at `tso`: the `ordered` term is `vRd`. -/
private theorem readBoundOf_tso (vs : VState) (dv : Ts) (a : Address) :
    readBoundOf .tso vs dv a = max (max (max vs.vPreBase dv) (vs.coh a)) vs.vRd := rfl

/-- At the *same* state, ARM's read bound is the smaller.  This is the
    architecture in isolation, with the refinement held fixed. -/
theorem readBoundOf_arm_le (vs : VState) (dv : Ts) (a : Address) :
    readBoundOf .arm vs dv a ≤ readBoundOf .tso vs dv a := by
  rw [readBoundOf_arm, readBoundOf_tso]
  exact le_max_le (Nat.le_refl _) (Nat.zero_le _)

/-- And at related states, with a smaller dependency join, it is still smaller.
    This is the form the simulation needs. -/
theorem readBoundOf_arm_le_tso {v w : VState} (hv : VLe v w) {dv dv' : Ts}
    (hd : dv ≤ dv') (a : Address) :
    readBoundOf .arm v dv a ≤ readBoundOf .tso w dv' a := by
  rw [readBoundOf_arm, readBoundOf_tso]
  exact le_max_le (le_max_le (le_max_le hv.vPreBase hd) (hv.coh a)) (Nat.zero_le _)

/-- **Every timestamp TSO may read, ARM may read.**

    `readable_antitone` plus the bound comparison, in the shape a simulation
    step wants: the candidate list `stepLoad` filters on is *larger* under ARM,
    so every TSO successor has an ARM counterpart at the same timestamp. -/
theorem arm_reads_what_tso_reads {v w : VState} (hv : VLe v w) {dv dv' : Ts}
    (hd : dv ≤ dv') {mem : Memory} {a : Address} {t : Ts}
    (h : readable mem a t (readBoundOf .tso w dv' a) = true) :
    readable mem a t (readBoundOf .arm v dv a) = true :=
  readable_antitone (readBoundOf_arm_le_tso hv hd a) h

/-- The dependency join a store contributes to its own ordering bound.  Named
    so that the `Knobs` branch can be discharged once instead of inside every
    `storeOb` proof. -/
private def storeDepOf (k : Knobs) (th : Thread) (e : Expr) (deps : List Reg) : Ts :=
  if k.storeDepRts then
    depRts th.regs (deps ++ (match e with | .const _ => [] | .reg r => [r]))
  else
    depView th.regs (deps ++ (match e with | .const _ => [] | .reg r => [r]))

/-- **Where the asymmetry of §15's relation is paid for.**

    On the `rts` branch the two runs must agree *exactly* -- a store's bound
    reads timestamps, and `TValLe` pins those -- while on the `view` branch mere
    monotonicity is enough.  Both branches land in `≤`, but for different
    reasons, and that is why `TValLe` could not have been "`≤` on all three
    fields". -/
private theorem storeDepOf_mono (k : Knobs) {ta tt : Thread} (h : ThreadLe ta tt)
    (e : Expr) (deps : List Reg) : storeDepOf k ta e deps ≤ storeDepOf k tt e deps := by
  unfold storeDepOf
  cases hk : k.storeDepRts
  · exact depView_mono (fun r => (h.regs r).view) _
  · exact Nat.le_of_eq (depRts_congr (fun r => (h.regs r).rts) _)

/-- `storeOb` at `arm`: the guard is `false && _`, so the extra `max` against
    `vRd`/`vWr` is gone by `rfl`, whatever the knob says. -/
private theorem storeOb_arm (k : Knobs) (th : Thread) (a : Address) (e : Expr)
    (deps : List Reg) :
    storeOb k .arm th a e deps =
      max (max th.vs.vPreBase (storeDepOf k th e deps))
          (max th.vs.vCtrl (th.vs.coh a)) := rfl

/-- At `tso` the guard still depends on `k.tsoStoreOrder`, so this direction is
    an inequality rather than an equation -- which is all the refinement needs,
    and is in fact the stronger statement: it holds for *either* setting of the
    knob. -/
private theorem storeOb_base_le (k : Knobs) (arch : Arch) (th : Thread) (a : Address)
    (e : Expr) (deps : List Reg) :
    max (max th.vs.vPreBase (storeDepOf k th e deps))
        (max th.vs.vCtrl (th.vs.coh a))
      ≤ storeOb k arch th a e deps := by
  dsimp only [storeOb]
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_refl _

/-- The store side.  `storeOb` differs by a `max` against `vRd`/`vWr` under
    TSO, so ARM's is smaller; the dependency terms move the right way because
    `rts` is equal and `view` is monotone. -/
theorem storeOb_arm_le_tso (k : Knobs) {ta tt : Thread} (h : ThreadLe ta tt)
    (a : Address) (e : Expr) (deps : List Reg) :
    storeOb k .arm ta a e deps ≤ storeOb k .tso tt a e deps := by
  refine Nat.le_trans ?_ (storeOb_base_le k .tso tt a e deps)
  rw [storeOb_arm]
  exact le_max_le (le_max_le h.vs.vPreBase (storeDepOf_mono k h e deps))
                  (le_max_le h.vs.vCtrl (h.vs.coh a))

/-- The data view a store publishes, named for the same reason as
    `storeDepOf`. -/
private def dataViewOf (th : Thread) (e : Expr) : Ts :=
  match e with
  | .const _ => 0
  | .reg r => (th.regs r).view

private theorem dataViewOf_mono {ta tt : Thread} (h : ThreadLe ta tt) (e : Expr) :
    dataViewOf ta e ≤ dataViewOf tt e := by
  cases e with
  | const _ => exact Nat.le_refl _
  | reg r => exact (h.regs r).view

private theorem storeMview_rel (th : Thread) (e : Expr) (deps : List Reg) :
    storeMview th e deps true =
      max (max th.vs.vRelSt (max th.vs.vRd th.vs.vWr))
          (max (depView th.regs deps) (dataViewOf th e)) := rfl

private theorem storeMview_plain (th : Thread) (e : Expr) (deps : List Reg) :
    storeMview th e deps false =
      max th.vs.vRelSt (max (depView th.regs deps) (dataViewOf th e)) := rfl

/-- And publication is architecture-blind, so this one is pure monotonicity --
    there is no `arm`/`tso` to compare, only two related states.

    If a counterexample to the refinement existed it would be here, in a
    publication rule that is stronger under `tso`.  It cannot be: `storeMview`
    **takes no `Arch` argument at all**.  The architecture only ever moves
    bounds. -/
theorem storeMview_mono {ta tt : Thread} (h : ThreadLe ta tt) (e : Expr)
    (deps : List Reg) (rel : Bool) :
    storeMview ta e deps rel ≤ storeMview tt e deps rel := by
  have hdv := depView_mono (fun r => (h.regs r).view) deps
  have hdata := dataViewOf_mono h e
  cases rel
  · rw [storeMview_plain, storeMview_plain]
    exact le_max_le h.vs.vRelSt (le_max_le hdv hdata)
  · rw [storeMview_rel, storeMview_rel]
    exact le_max_le (le_max_le h.vs.vRelSt (le_max_le h.vs.vRd h.vs.vWr))
                    (le_max_le hdv hdata)

/-- **Every promise TSO may fulfil, ARM may fulfil** -- as far as the ordering
    guard is concerned.  `ob < tw` is the side condition, and `ob` only
    shrinks; stated with `≤`, which gives the strict form by
    `Nat.lt_of_le_of_lt`. -/
theorem arm_fulfils_what_tso_fulfils (k : Knobs) {ta tt : Thread}
    (h : ThreadLe ta tt) {a : Address} {e : Expr} {deps : List Reg} {tw : Ts}
    (hob : storeOb k .tso tt a e deps ≤ tw) : storeOb k .arm ta a e deps ≤ tw :=
  Nat.le_trans (storeOb_arm_le_tso k h a e deps) hob

/-! ### The executable half

Two controls, in the spirit of the rest of the file.  A monotonicity lemma is
worth nothing if the inequality is an equality everywhere -- then `arm` and
`tso` would be the same rules and there would be nothing to prove -- so the
first control exhibits a state where the read bound is **strictly** smaller
under `arm`.  The second exhibits a `VState` a fence genuinely changes, which is
the executable form of `fence_moves_the_state`: it is what rules out the
simpler refinement, identity on states, that one reaches for first. -/

private def refineVs : VState := { VState.init with vRd := 3, vPreBase := 1 }

private def refineTh : Thread :=
  { prog := [], regs := fun _ => TVal.mk0 (Val.num 0), vs := refineVs, promises := [] }

def refineDemo : String :=
  let a : Address := ⟨0, 0⟩
  let ba := readBoundOf .arm refineVs 0 a
  let bt := readBoundOf .tso refineVs 0 a
  let before := refineTh.vs.vPreBase
  let after := (stepFence refineTh .sy).vs.vPreBase
  s!"readBound arm={ba}, tso={bt}, strict={decide (ba < bt)}\n" ++
  s!"fence vPreBase before={before}, after={after}, moved={decide (before != after)}"


/-! ## 16. The simulation: every TSO outcome is an ARM outcome

§4.1 runs both machines over the suite and reports that the TSO outcome set is
contained in the ARM one on every test.  This section proves it for *every*
program, by forward simulation: for each TSO run there is an ARM run, taking
structurally the same steps with the same chosen timestamps, whose final
configuration is `ConfigLe`-related to the TSO one -- and `ConfigLe` is enough
to pin the observed registers, so the outcomes are equal, not merely related.

Only two things differ between the two runs.

1. The architecture-sensitive *bounds* -- `readBoundOf` and `storeOb` -- are
   larger under TSO.  A larger bound only removes candidate timestamps, so the
   ARM machine can always take the step the TSO machine took.  That is §15's
   `arm_reads_what_tso_reads` and `arm_fulfils_what_tso_fulfils`.
2. A TSO read-modify-write performs an extra `stepFence _ .sy` (`lockFence`).
   The ARM side does not, and does not need to: a fence only raises views on
   the *right* of the relation, which `ThreadLe_of_fence_right` absorbs.

### The finding: `ConfigLe` is not inductive

The obvious statement -- "`ConfigLe` is preserved by every rule" -- is false as
stated, and the case that breaks it is store *fulfilment*.  Writing to an
already-promised timestamp `t` requires the writer's `mview` to be below the
view recorded in the message at `t`; on the ARM side that obligation mentions
the ARM memory, and `MemLe` only offers `view_arm ≤ view_tso`, which is the
wrong direction to discharge it.

The repair is not a weaker relation but an extra invariant.  A promised message
is created by `promiseSteps`, which picks its view `w` from `List.range
c.mem.size` -- the *same* list in both runs, because `MemLe` pins the size.  So
at an outstanding promised timestamp the two memories do not merely refine one
another, they agree exactly, and the fulfilment obligation transports as an
equality.  Hence `Sim`, which is `ConfigLe` plus that agreement.  The bound
`t < ca.mem.size` has to be bundled into the invariant rather than derived,
because the *appending* case has no other way to rule out `t = mem.size`.

Maintaining the agreement needs two facts about each rule that have nothing to
do with the architecture -- memory only ever grows at the end (`MemExt`), and a
step never invents a promise -- which is why the `*_ext` family below is stated
for an arbitrary `arch` and applied to both runs.

`Sim` is added *beside* `ConfigLe` rather than replacing it, so §15 stays
true as written: `ConfigLe` is still the refinement relation, and `Sim` is the
inductive strengthening a proof by simulation happens to need. -/

namespace Sim

/-! ### Memory congruences

`MemLe` pins `loc`, `val` and the size, and every predicate the machine uses to
filter timestamps looks at memory only through those.  So all four are
*congruences*, not inequalities. -/

/-- The one shape all four predicates are built from. -/
theorem locAt_congr {ma mt : Memory} (h : MemLe ma mt) (a : Address) (t : Ts) :
    (ma[t]?.elim false fun m => decide (m.loc = a))
      = (mt[t]?.elim false fun m => decide (m.loc = a)) := by
  cases hma : ma[t]? with
  | none =>
      cases hmt : mt[t]? with
      | none => rfl
      | some n =>
          exfalso
          have h1 : ma.size ≤ t := Array.getElem?_eq_none_iff.1 hma
          rw [h.1] at h1
          rw [Array.getElem?_eq_none_iff.2 h1] at hmt
          simp at hmt
  | some m =>
      cases hmt : mt[t]? with
      | none =>
          exfalso
          have h1 : mt.size ≤ t := Array.getElem?_eq_none_iff.1 hmt
          rw [← h.1] at h1
          rw [Array.getElem?_eq_none_iff.2 h1] at hma
          simp at hma
      | some n =>
          have := (h.2 t m n hma hmt).1
          simp [this]

theorem hiddenFrom_congr {ma mt : Memory} (h : MemLe ma mt) (a : Address) (t b : Ts) :
    hiddenFrom ma a t b = hiddenFrom mt a t b := by
  have hf : (fun t' => decide (t < t') && (ma[t']?.elim false fun m => decide (m.loc = a)))
          = (fun t' => decide (t < t') && (mt[t']?.elim false fun m => decide (m.loc = a))) := by
    funext t'; rw [locAt_congr h a t']
  unfold hiddenFrom
  rw [hf]

theorem readable_congr {ma mt : Memory} (h : MemLe ma mt) (a : Address) (t b : Ts) :
    readable ma a t b = readable mt a t b := by
  unfold readable
  rw [locAt_congr h a t, hiddenFrom_congr h a t b]

theorem betweenAt_congr {ma mt : Memory} (h : MemLe ma mt) (a : Address) (tr tw : Ts) :
    betweenAt ma a tr tw = betweenAt mt a tr tw := by
  have hf : (fun t' => decide (tr < t') && decide (t' < tw) &&
                (ma[t']?.elim false fun m => decide (m.loc = a)))
          = (fun t' => decide (tr < t') && decide (t' < tw) &&
                (mt[t']?.elim false fun m => decide (m.loc = a))) := by
    funext t'; rw [locAt_congr h a t']
  unfold betweenAt
  rw [hf, h.1]

theorem rmwAdjacent_congr {ma mt : Memory} (h : MemLe ma mt) (a : Address) (tr tw : Ts) :
    rmwAdjacent ma a tr tw = rmwAdjacent mt a tr tw := by
  unfold rmwAdjacent
  rw [betweenAt_congr h a tr tw]

theorem pairStraddles_congr {ma mt : Memory} (h : MemLe ma mt) (ps : List Ts)
    (a0 : Address) (t0 t1 : Ts) :
    pairStraddles ma ps a0 t0 t1 = pairStraddles mt ps a0 t0 t1 := by
  have hf : (fun p => (ma[p]?.elim false fun m => decide (m.loc = a0)) &&
                (ma[p + 1]?.elim false fun m => decide (m.loc = a0.next)) &&
                (decide (p ≤ t0) != decide (p + 1 ≤ t1)))
          = (fun p => (mt[p]?.elim false fun m => decide (m.loc = a0)) &&
                (mt[p + 1]?.elim false fun m => decide (m.loc = a0.next)) &&
                (decide (p ≤ t0) != decide (p + 1 ≤ t1))) := by
    funext p; rw [locAt_congr h a0 p, locAt_congr h a0.next (p + 1)]
  unfold pairStraddles
  rw [hf]

/-! ### The load -/

/-- `MemLe` in the `[t]!` form the step functions actually use. -/
theorem memLe_bang {ma mt : Memory} (h : MemLe ma mt) {t : Ts} (ht : t < mt.size) :
    (ma[t]!).loc = (mt[t]!).loc ∧ (ma[t]!).val = (mt[t]!).val ∧
      (ma[t]!).view ≤ (mt[t]!).view := by
  have hta : t < ma.size := by rw [h.1]; exact ht
  have ea : ma[t]? = some ma[t]! := by
    rw [getElem!_pos ma t hta, Array.getElem?_eq_getElem hta]
  have et : mt[t]? = some mt[t]! := by
    rw [getElem!_pos mt t ht, Array.getElem?_eq_getElem ht]
  exact h.2 t _ _ ea et

theorem stepLoad_sim {ma mt : Memory} (hm : MemLe ma mt) {ta tt : Thread}
    (h : ThreadLe ta tt) (pairs : List Ts)
    (dst : Reg) (a : Address) (deps : List Reg) (acq : Bool)
    {tt' : Thread} (hin : tt' ∈ stepLoad .tso mt pairs tt dst a deps acq) :
    ∃ ta' ∈ stepLoad .arm ma pairs ta dst a deps acq, ThreadLe ta' tt' := by
  simp only [stepLoad, List.mem_map, List.mem_filter, List.mem_range] at hin
  obtain ⟨t, ⟨htlt, hrd⟩, rfl⟩ := hin
  have hbnd : readBoundOf .arm ta.vs (depBound ta.regs deps) a
            ≤ readBoundOf .tso tt.vs (depBound tt.regs deps) a :=
    readBoundOf_arm_le_tso h.vs
      (depBound_mono (fun r => (h.regs r).view) (fun r => (h.regs r).rts) deps) a
  have htlt' : t < ma.size := by rw [hm.1]; exact htlt
  have hrd' : readable ma a t (readBoundOf .arm ta.vs (depBound ta.regs deps) a) = true := by
    refine readable_antitone hbnd ?_
    rw [readable_congr hm]; exact hrd
  obtain ⟨hloc, hval, hview⟩ := memLe_bang hm htlt
  refine ⟨{ ta with
              regs := fun r => if r = dst then ⟨ma[t]!.val, ma[t]!.view, t⟩ else ta.regs r
              vs := { ta.vs with
                      coh := fun b => if b = a then max (ta.vs.coh a) t else ta.vs.coh b
                      vRd := max ta.vs.vRd (rdV ta.vs pairs t ma[t]!.view)
                      vPreBase :=
                        if acq then max ta.vs.vPreBase (acqV ta.vs pairs t ma[t]!.view)
                        else ta.vs.vPreBase } },
           ?_, ?_⟩
  · simp only [stepLoad, List.mem_map, List.mem_filter, List.mem_range]
    exact ⟨t, ⟨htlt', hrd'⟩, rfl⟩
  · refine ⟨h.prog, h.promises, ?_, ?_⟩
    · intro r
      by_cases hr : r = dst
      · simp only [hr, ite_true]
        exact ⟨hval, rfl, hview⟩
      · simp only [hr, ite_false]
        exact h.regs r
    · refine ⟨?_, ?_, h.vs.vWr, h.vs.vCtrl, ?_, h.vs.vRelSt, (by first | exact h.vs.mine | simp [h.vs.mine] | simp_all), h.vs.fwd⟩
      · intro b
        by_cases hb : b = a
        · simp only [hb, ite_true]
          exact le_max_le (h.vs.coh a) (Nat.le_refl _)
        · simp only [hb, ite_false]
          exact h.vs.coh b
      · exact le_max_le h.vs.vRd (h.vs.rdV pairs t hview)
      · cases acq
        · exact h.vs.vPreBase
        · exact le_max_le h.vs.vPreBase (h.vs.acqV pairs t hview)

/-! ### The store -/

theorem MemLe.refl (m : Memory) : MemLe m m := by
  refine ⟨rfl, ?_⟩
  intro t x y hx hy
  rw [hx] at hy
  cases hy
  exact ⟨rfl, rfl, Nat.le_refl _⟩

theorem MemLe.push {ma mt : Memory} (h : MemLe ma mt) {x y : Msg}
    (hloc : x.loc = y.loc) (hval : x.val = y.val) (hview : x.view ≤ y.view) :
    MemLe (ma.push x) (mt.push y) := by
  refine ⟨by simp [h.1], ?_⟩
  intro t m n hm hn
  rw [Array.getElem?_push] at hm hn
  by_cases ht : t = ma.size
  · rw [ite_eq_left ht] at hm
    rw [h.1] at ht
    rw [ite_eq_left ht] at hn
    cases hm; cases hn
    exact ⟨hloc, hval, hview⟩
  · rw [ite_eq_right ht] at hm
    have ht' : ¬ t = mt.size := by rw [← h.1]; exact ht
    rw [ite_eq_right ht'] at hn
    exact h.2 t m n hm hn

/-- The value a store writes.  Named rather than written inline: an inline
    `match e with` inside a `have` gets generalised over every hypothesis that
    mentions `e`, and the resulting motive does not match the machine's. -/
def storeValOf (th : Thread) (e : Expr) : Val :=
  match e with
  | .const c => c
  | .reg r => (th.regs r).val

/-- The value a store writes is the same in both runs: `TValLe` pins `val`. -/
theorem storeValOf_congr {ta tt : Thread} (h : ThreadLe ta tt) (e : Expr) :
    storeValOf ta e = storeValOf tt e := by
  cases e with
  | const c => rfl
  | reg r => exact (h.regs r).val

/-- Both halves of the store rule commit through the same shape. -/
theorem commitTh_le {ta tt : Thread} (h : ThreadLe ta tt) (a : Address) (t : Ts)
    {pa pt : List Ts} (hprom : pa = pt) :
    ThreadLe
      { ta with vs := { ta.vs with coh := fun b => if b = a then t else ta.vs.coh b
                                   vWr := max ta.vs.vWr t, mine := t :: ta.vs.mine }
                promises := pa }
      { tt with vs := { tt.vs with coh := fun b => if b = a then t else tt.vs.coh b
                                   vWr := max tt.vs.vWr t, mine := t :: tt.vs.mine }
                promises := pt } := by
  refine ⟨h.prog, hprom, h.regs, ?_, ?_, ?_, h.vs.vCtrl, h.vs.vPreBase, h.vs.vRelSt, (by first | exact h.vs.mine | simp [h.vs.mine] | simp_all), h.vs.fwd⟩
  · intro b
    by_cases hb : b = a
    · simp only [hb, ite_true]
      exact Nat.le_refl _
    · simp only [hb, ite_false]
      exact h.vs.coh b
  · exact h.vs.vRd
  · exact le_max_le h.vs.vWr (Nat.le_refl _)

/-- A store's forwarding entry relates: `fwdOf` is `depBound`, monotone in
    the registers. -/
theorem fwdOf_mono {ta tt : Thread} (h : ThreadLe ta tt) (e : Expr) (deps : List Reg) :
    fwdOf ta.regs e deps <= fwdOf tt.regs e deps :=
  depBound_mono (fun r => (h.regs r).view) (fun r => (h.regs r).rts) _

/-- `commitTh_le` with the store's forwarding entry (`Knobs.fwdView`). -/
theorem storeCommitTh_le (k : Knobs) {ta tt : Thread} (h : ThreadLe ta tt) (a : Address) (t : Ts)
    (e : Expr) (deps : List Reg) {pa pt : List Ts} (hprom : pa = pt) :
    ThreadLe
      { ta with vs := { ta.vs with coh := fun b => if b = a then t else ta.vs.coh b
                                   vWr := max ta.vs.vWr t, mine := t :: ta.vs.mine
                                   fwd := if k.fwdView then (t, fwdOf ta.regs e deps) :: ta.vs.fwd
                                          else ta.vs.fwd }
                promises := pa }
      { tt with vs := { tt.vs with coh := fun b => if b = a then t else tt.vs.coh b
                                   vWr := max tt.vs.vWr t, mine := t :: tt.vs.mine
                                   fwd := if k.fwdView then (t, fwdOf tt.regs e deps) :: tt.vs.fwd
                                          else tt.vs.fwd }
                promises := pt } := by
  have hc := commitTh_le h a t hprom
  refine ⟨hc.prog, hc.promises, hc.regs, ⟨hc.vs.coh, hc.vs.vRd, hc.vs.vWr, hc.vs.vCtrl, hc.vs.vPreBase,
    hc.vs.vRelSt, hc.vs.mine, ?_⟩⟩
  dsimp only
  split
  · exact FwdLe.cons (fwdOf_mono h e deps) h.vs.fwd
  · exact h.vs.fwd

/-- Inverting a guarded `some`.  Used instead of `split at`, which would pick
    the `match e with` *inside* the guard rather than the guard itself -- the
    machine writes the stored value as an inline match, and `split` has no way
    to know that is not the interesting scrutinee. -/
theorem of_ite_some {alpha : Type} {c : Prop} [Decidable c] {x z : alpha}
    (h : (if c then some x else none) = some z) : c /\ x = z := by
  by_cases hc : c
  . rw [ite_eq_left hc] at h
    cases h
    exact ⟨hc, rfl⟩
  . rw [ite_eq_right hc] at h
    simp at h

theorem stepStore_sim (k : Knobs) {ma mt : Memory} (hm : MemLe ma mt) {ta tt : Thread}
    (h : ThreadLe ta tt) (hp : ∀ t ∈ tt.promises, ma[t]? = mt[t]?)
    (a : Address) (e : Expr) (deps : List Reg) (rel : Bool)
    {mt' : Memory} {tt' : Thread} (hin : (mt', tt') ∈ stepStore k .tso mt tt a e deps rel) :
    ∃ q ∈ stepStore k .arm ma ta a e deps rel, MemLe q.1 mt' ∧ ThreadLe q.2 tt' := by
  have hv := storeValOf_congr h e
  have hmv := storeMview_mono h e deps rel
  have hob := storeOb_arm_le_tso k h a e deps
  simp only [stepStore, List.mem_append, List.mem_singleton] at hin
  rcases hin with happ | hful
  · cases happ
    have hmem :
        ((ma.push ⟨a, storeValOf ta e, storeMview ta e deps rel⟩),
         ({ ta with
            vs := { ta.vs with
                    coh := fun b => if b = a then ma.size else ta.vs.coh b
                    vWr := max ta.vs.vWr ma.size, mine := ma.size :: ta.vs.mine
                    fwd := if k.fwdView then (ma.size, fwdOf ta.regs e deps) :: ta.vs.fwd
                           else ta.vs.fwd }
            promises := ta.promises } : Thread))
          ∈ stepStore k .arm ma ta a e deps rel := by
      simp only [stepStore, List.mem_append, List.mem_singleton]
      exact Or.inl rfl
    refine ⟨_, hmem, MemLe.push hm rfl hv hmv, ?_⟩
    rw [hm.1]
    exact storeCommitTh_le k h a mt.size e deps h.promises
  · obtain ⟨t, htp, hft⟩ := List.mem_filterMap.1 hful
    have hsame : ma[t]? = mt[t]? := hp t htp
    split at hft
    · simp at hft
    · next m hmt =>
        have hma : ma[t]? = some m := hsame.trans hmt
        obtain ⟨hguard, hpair⟩ := of_ite_some hft
        cases hpair
        · have hguard' :
              ((m.loc == a) && (m.val == storeValOf ta e) &&
                decide (storeMview ta e deps rel <= m.view) &&
                decide (storeOb k .arm ta a e deps < t)) = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hguard ⊢
            obtain ⟨⟨⟨hl, hval⟩, hmview⟩, hobt⟩ := hguard
            exact ⟨⟨⟨hl, by rw [hv]; exact hval⟩, Nat.le_trans hmv hmview⟩,
                   Nat.lt_of_le_of_lt hob hobt⟩
          have hmem :
              ((ma : Memory),
               ({ ta with
                  vs := { ta.vs with
                          coh := fun b => if b = a then t else ta.vs.coh b
                          vWr := max ta.vs.vWr t, mine := t :: ta.vs.mine
                          fwd := if k.fwdView then (t, fwdOf ta.regs e deps) :: ta.vs.fwd
                                 else ta.vs.fwd }
                  promises := ta.promises.erase t } : Thread))
                ∈ stepStore k .arm ma ta a e deps rel := by
            simp only [stepStore, List.mem_append, List.mem_singleton]
            refine Or.inr (List.mem_filterMap.2 ⟨t, ?_, ?_⟩)
            · rw [h.promises]; exact htp
            · rw [hma]
              exact ite_eq_left hguard'
          exact ⟨_, hmem, hm, storeCommitTh_le k h a t e deps (by rw [h.promises])⟩

/-! ### The read half, shared by the load and the RMW -/

/-- Reading is the same construction in `stepLoad` and `stepRmw`, so it relates
    for the same reason.  `w` is the message view, which is the only thing that
    differs between the two runs.

    `t` and `tv` are separated because they are no longer the same quantity:
    coherence moves to the timestamp actually read, while `vRd` moves to
    `pairTop` of it, the top of the atomic write that timestamp belongs to.
    Nothing here cares which is which -- both runs pass the same pair, so the
    two sides get the same `tv` -- but the statement has to let them differ. -/
theorem readVs_le {va vt : VState} (h : VLe va vt) (a : Address) (t : Ts)
    {wa wt : Ts} (hw : wa <= wt) {ea et : Ts} (he : ea <= et) (acq : Bool) :
    VLe { va with coh := fun b => if b = a then max (va.coh a) t else va.coh b
                  vRd := max va.vRd wa
                  vPreBase := if acq then max va.vPreBase ea else va.vPreBase }
        { vt with coh := fun b => if b = a then max (vt.coh a) t else vt.coh b
                  vRd := max vt.vRd wt
                  vPreBase := if acq then max vt.vPreBase et else vt.vPreBase } := by
  refine ⟨?_, ?_, h.vWr, h.vCtrl, ?_, h.vRelSt, (by first | exact h.mine | simp [h.mine] | simp_all), h.fwd⟩
  · intro b
    by_cases hb : b = a
    · simp only [hb, ite_true]
      exact le_max_le (h.coh a) (Nat.le_refl _)
    · simp only [hb, ite_false]
      exact h.coh b
  · exact le_max_le h.vRd hw
  · cases acq
    · exact h.vPreBase
    · exact le_max_le h.vPreBase he

theorem readTh_le {ta tt : Thread} (h : ThreadLe ta tt) (dst : Reg) (a : Address)
    (t : Ts) {xa xt : TVal} (hx : TValLe xa xt) {wa wt : Ts} (hw : wa <= wt) {ea et : Ts} (he : ea <= et)
    (acq : Bool) :
    ThreadLe
      { ta with regs := fun r => if r = dst then xa else ta.regs r
                vs := { ta.vs with
                        coh := fun b => if b = a then max (ta.vs.coh a) t else ta.vs.coh b
                        vRd := max ta.vs.vRd wa
                        vPreBase := if acq then max ta.vs.vPreBase ea else ta.vs.vPreBase } }
      { tt with regs := fun r => if r = dst then xt else tt.regs r
                vs := { tt.vs with
                        coh := fun b => if b = a then max (tt.vs.coh a) t else tt.vs.coh b
                        vRd := max tt.vs.vRd wt
                        vPreBase := if acq then max tt.vs.vPreBase et else tt.vs.vPreBase } } := by
  refine ⟨h.prog, h.promises, ?_, readVs_le h.vs a t hw he acq⟩
  intro r
  by_cases hr : r = dst
  · simp only [hr, ite_true]
    exact hx
  · simp only [hr, ite_false]
    exact h.regs r

/-- The two things `rmwDst` can be: the read's register, or -- after a
    successful non-acquire `CAS` -- the value with no dependency at all. -/
theorem rmwDst_cases (kind : RmwKind) (acq : Bool) (m : Msg) (t : Ts) :
    rmwDst kind acq m t = ⟨m.val, m.view, t⟩ ∨
      (acq = false ∧ (∃ c, kind = .cas c) ∧ rmwDst kind acq m t = ⟨m.val, 0, 0⟩) := by
  cases kind with
  | cas c =>
      cases acq
      · by_cases hs : rmwSucceeds (.cas c) m.val = true
        · exact Or.inr ⟨rfl, ⟨c, rfl⟩, by simp [rmwDst, hs]⟩
        · exact Or.inl (by simp [rmwDst, hs])
      · exact Or.inl (by simp [rmwDst])
  | _ => exact Or.inl rfl

/-- What an RMW leaves in its destination register relates across the two
    runs: both read the same timestamp, so both take the same branch. -/
theorem rmwDst_le (kind : RmwKind) (acq : Bool)
    {ma mt : Msg} (hval : ma.val = mt.val) (hview : ma.view <= mt.view) (t : Ts) :
    TValLe (rmwDst kind acq ma t) (rmwDst kind acq mt t) := by
  unfold rmwDst
  cases kind with
  | cas c =>
      simp only [hval]
      split
      · exact ⟨rfl, rfl, Nat.le_refl _⟩
      · exact ⟨rfl, rfl, hview⟩
  | _ => exact ⟨hval, rfl, hview⟩

/-! ### The RMW -/

theorem rmwMview_mono {va vt : VState} (hv : VLe va vt) {da dt : Ts} (hd : da <= dt)
    {ra rt : Ts} (hr : ra <= rt) (rel : Bool) :
    (if rel then max (max (max va.vRelSt ra) (max va.vRd va.vWr)) da
     else max (max va.vRelSt ra) da)
      <= (if rel then max (max (max vt.vRelSt rt) (max vt.vRd vt.vWr)) dt
          else max (max vt.vRelSt rt) dt) := by
  cases rel
  · exact le_max_le (le_max_le hv.vRelSt hr) hd
  · exact le_max_le (le_max_le (le_max_le hv.vRelSt hr) (le_max_le hv.vRd hv.vWr)) hd

theorem rmwBase_mono {va vt : VState} (hv : VLe va vt) {da dt : Ts} (hd : da <= dt)
    (a : Address) :
    max (max va.vPreBase da) (max va.vCtrl (va.coh a))
      <= max (max vt.vPreBase dt) (max vt.vCtrl (vt.coh a)) :=
  le_max_le (le_max_le hv.vPreBase hd) (le_max_le hv.vCtrl (hv.coh a))

theorem le_guarded_max (c : Bool) (base x : Ts) : base <= if c then max base x else base := by
  cases c
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

theorem rmwDTs_mono (k : Knobs) {ta tt : Thread} (h : ThreadLe ta tt) (deps : List Reg) :
    (if k.storeDepRts then depRts ta.regs deps else depView ta.regs deps)
      <= (if k.storeDepRts then depRts tt.regs deps else depView tt.regs deps) := by
  cases hk : k.storeDepRts
  · exact depView_mono (fun r => (h.regs r).view) deps
  · exact Nat.le_of_eq (depRts_congr (fun r => (h.regs r).rts) deps)

/-- Related threads store the same value: `TValLe` keeps register values equal. -/
theorem rmwNewVal_congr {ta tt : Thread} (h : ThreadLe ta tt) (e : Expr) :
    rmwNewVal ta.regs e = rmwNewVal tt.regs e := by
  cases e with
  | const c => rfl
  | reg r => exact (h.regs r).val

/-! #### Naming the two thread shapes the rules build

Both are definitionally what the machine writes inline.  Naming them keeps the
witnesses in the simulation proofs to one line each instead of fifteen, and
`exact` still sees through to the machine's form. -/

def readThOf (th : Thread) (pairs : List Ts) (dst : Reg) (a : Address) (t : Ts)
    (x : TVal) (w : Ts) (acq : Bool) : Thread :=
  { th with
    regs := fun r => if r = dst then x else th.regs r
    vs := { th.vs with
            coh := fun b => if b = a then max (th.vs.coh a) t else th.vs.coh b
            vRd := max th.vs.vRd (rdV th.vs pairs t w)
            vPreBase := if acq then max th.vs.vPreBase (acqV th.vs pairs t w)
                        else th.vs.vPreBase } }

def commitThOf (th : Thread) (a : Address) (tw : Ts) (prom : List Ts) : Thread :=
  { th with
    vs := { th.vs with coh := fun b => if b = a then tw else th.vs.coh b
                       vWr := max th.vs.vWr tw, mine := tw :: th.vs.mine }
    promises := prom }

theorem readThOf_le {ta tt : Thread} (h : ThreadLe ta tt) (pairs : List Ts)
    (dst : Reg) (a : Address)
    (t : Ts) {xa xt : TVal} (hx : TValLe xa xt) {wa wt : Ts} (hw : wa <= wt) (acq : Bool) :
    ThreadLe (readThOf ta pairs dst a t xa wa acq) (readThOf tt pairs dst a t xt wt acq) :=
  readTh_le h dst a t hx (h.vs.rdV pairs t hw) (h.vs.acqV pairs t hw) acq

theorem commitThOf_le {ta tt : Thread} (h : ThreadLe ta tt) (a : Address) (t : Ts)
    {pa pt : List Ts} (hprom : pa = pt) :
    ThreadLe (commitThOf ta a t pa) (commitThOf tt a t pt) :=
  commitTh_le h a t hprom

/-! #### The two architecture-sensitive quantities of the write half

These are stated over the *scalars* rather than over a `VState`, because the
machine's `readVs.coh a` is `if a = a then max (vs.coh a) t else vs.coh a`, and
`a` is a variable, so that `if` is stuck for `whnf` while `simp` reduces it on
sight.  Naming the scalars means both runs present the same normal form. -/

/-- The view an RMW's write carries.  Same shape as `storeMview` plus the read
    half's view `rv`; `dv` is the view of the write's dependencies,
    `newv.writeDeps deps`. -/
def rmwMviewAt (relSt rd wr dv rv : Ts) (rel : Bool) : Ts :=
  if rel then max (max (max relSt rv) (max rd wr)) dv else max (max relSt rv) dv

theorem rmwMviewAt_mono {s1 s2 r1 r2 w1 w2 d1 d2 v1 v2 : Ts} (hs : s1 <= s2) (hr : r1 <= r2)
    (hw : w1 <= w2) (hd : d1 <= d2) (hv : v1 <= v2) (rel : Bool) :
    rmwMviewAt s1 r1 w1 d1 v1 rel <= rmwMviewAt s2 r2 w2 d2 v2 rel := by
  cases rel
  . exact le_max_le (le_max_le hs hv) hd
  . exact le_max_le (le_max_le (le_max_le hs hv) (le_max_le hr hw)) hd

/-- The part of an RMW's `ob` both architectures agree on. -/
def rmwBaseAt (preBase dTs ctrl cohA : Ts) : Ts := max (max preBase dTs) (max ctrl cohA)

theorem rmwBaseAt_mono {p1 p2 d1 d2 c1 c2 h1 h2 : Ts} (hp : p1 <= p2) (hd : d1 <= d2)
    (hc : c1 <= c2) (hh : h1 <= h2) : rmwBaseAt p1 d1 c1 h1 <= rmwBaseAt p2 d2 c2 h2 :=
  le_max_le (le_max_le hp hd) (le_max_le hc hh)

/-- TSO's `ob` is the base joined with the read and write views when
    `k.tsoStoreOrder` is on; ARM's *is* the base, because `arch = .tso` is
    definitionally `false` there.  Either way the base is below it.

    The condition is taken as an arbitrary `Prop`: `simp` rewrites the machine's
    `(decide (arch = .tso) && k.tsoStoreOrder) = true` into `True ∧ ... = true`
    on the TSO side, so a `Bool`-shaped statement would not match. -/
theorem rmwBaseAt_le_ite (p d c hh x : Ts) (P : Prop) [Decidable P] :
    rmwBaseAt p d c hh <= if P then max (rmwBaseAt p d c hh) x else rmwBaseAt p d c hh := by
  split
  . exact Nat.le_max_left _ _
  . exact Nat.le_refl _

/-! #### The simulation

Three branches: a failed compare-and-swap, which is a load; a write appended at
`mem.size`; and a write that fulfils an outstanding promise.  The third is the
one that needs `hp`: at a promised timestamp the two runs hold the *same*
message, which is more than `MemLe` gives. -/

theorem stepRmwAt_sim (k : Knobs) {ma mt : Memory} (hm : MemLe ma mt) {ta tt : Thread}
    (h : ThreadLe ta tt) (hp : forall t, t ∈ tt.promises -> ma[t]? = mt[t]?)
    (pairs : List Ts)
    (dst : Reg) (a : Address) (kind : RmwKind) (newv : Expr) (deps : List Reg)
    (acq rel : Bool) {mt' : Memory} {tt' : Thread}
    (hin : (mt', tt') ∈ stepRmwAt k .tso mt pairs tt dst a kind newv deps acq rel) :
    ∃ q ∈ stepRmwAt k .arm ma pairs ta dst a kind newv deps acq rel,
      MemLe q.1 mt' ∧ ThreadLe q.2 tt' := by
  simp only [stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range, ite_true] at hin
  obtain ⟨t, ⟨htlt, hrd⟩, hbody⟩ := hin
  have htlt' : t < ma.size := by rw [hm.1]; exact htlt
  obtain ⟨hloc, hval, hview⟩ := memLe_bang hm htlt
  have hrd' : readable ma a t (readBoundOf .arm ta.vs (depBound ta.regs deps) a) = true := by
    refine readable_antitone
      (readBoundOf_arm_le_tso h.vs
        (depBound_mono (fun r => (h.regs r).view) (fun r => (h.regs r).rts) deps) a) ?_
    rw [readable_congr hm]; exact hrd
  -- The read half, related once and reused by all three branches.
  have hrth := readThOf_le h pairs dst a t (rmwDst_le kind acq hval hview t) hview acq
  have hwv : kind.apply ma[t]!.val (rmwNewVal ta.regs newv)
      = kind.apply mt[t]!.val (rmwNewVal tt.regs newv) := by
    rw [hval, rmwNewVal_congr h newv]
  have hmview :
      rmwMviewAt ta.vs.vRelSt (max ta.vs.vRd (rdV ta.vs pairs t ma[t]!.view)) ta.vs.vWr
          (depView ta.regs (newv.writeDeps deps)) (max (pairTop pairs t) ma[t]!.view) rel
        <= rmwMviewAt tt.vs.vRelSt (max tt.vs.vRd (rdV tt.vs pairs t mt[t]!.view)) tt.vs.vWr
          (depView tt.regs (newv.writeDeps deps)) (max (pairTop pairs t) mt[t]!.view) rel :=
    rmwMviewAt_mono h.vs.vRelSt
      (le_max_le h.vs.vRd (h.vs.rdV pairs t hview))
      h.vs.vWr (depView_mono (fun r => (h.regs r).view) (newv.writeDeps deps))
      (le_max_le (Nat.le_refl (pairTop pairs t)) hview) rel
  have hbase :
      rmwBaseAt (if acq then max ta.vs.vPreBase (acqV ta.vs pairs t ma[t]!.view) else ta.vs.vPreBase)
          (if k.storeDepRts then depRts ta.regs (newv.writeDeps deps) else depView ta.regs (newv.writeDeps deps))
          ta.vs.vCtrl (max (ta.vs.coh a) t)
        <= rmwBaseAt (if acq then max tt.vs.vPreBase (acqV tt.vs pairs t mt[t]!.view) else tt.vs.vPreBase)
          (if k.storeDepRts then depRts tt.regs (newv.writeDeps deps) else depView tt.regs (newv.writeDeps deps))
          tt.vs.vCtrl (max (tt.vs.coh a) t) :=
    rmwBaseAt_mono hrth.vs.vPreBase (rmwDTs_mono k h (newv.writeDeps deps)) h.vs.vCtrl
      (le_max_le (h.vs.coh a) (Nat.le_refl t))
  split at hbody
  . -- The compare-and-swap failed: this is a load, and it fulfils nothing.
    next hfail =>
      have hfail' : (!rmwSucceeds kind ma[t]!.val) = true := by rw [hval]; exact hfail
      rw [List.mem_singleton] at hbody
      cases hbody
      have hmem : ((ma : Memory), readThOf ta pairs dst a t (rmwDst kind acq ma[t]! t) ma[t]!.view acq)
          ∈ stepRmwAt k .arm ma pairs ta dst a kind newv deps acq rel := by
        simp only [stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range]
        refine ⟨t, ⟨htlt', hrd'⟩, ?_⟩
        rw [ite_eq_left hfail', List.mem_singleton]
        rfl
      exact ⟨_, hmem, hm, ThreadLe_of_fence_right hrth .sy⟩
  . next hsucc =>
      have hsucc' : ¬ ((!rmwSucceeds kind ma[t]!.val) = true) := by rw [hval]; exact hsucc
      rw [List.mem_append] at hbody
      rcases hbody with happ | hful
      . -- The write is appended at the end of memory.
        split at happ
        . next hadj =>
            have hadj' : rmwAdjacent ma a t ma.size = true := by
              rw [rmwAdjacent_congr hm, hm.1]; exact hadj
            rw [List.mem_singleton] at happ
            cases happ
            have hmem :
                ((ma.push ⟨a, kind.apply ma[t]!.val (rmwNewVal ta.regs newv),
                    rmwMviewAt ta.vs.vRelSt
                      (max ta.vs.vRd (rdV ta.vs pairs t ma[t]!.view)) ta.vs.vWr
                      (depView ta.regs (newv.writeDeps deps)) (max (pairTop pairs t) ma[t]!.view) rel⟩),
                 commitThOf (readThOf ta pairs dst a t (rmwDst kind acq ma[t]! t) ma[t]!.view acq) a ma.size
                   ta.promises)
                  ∈ stepRmwAt k .arm ma pairs ta dst a kind newv deps acq rel := by
              simp only [stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range]
              refine ⟨t, ⟨htlt', hrd'⟩, ?_⟩
              rw [ite_eq_right hsucc']
              refine List.mem_append.2 (Or.inl ?_)
              rw [ite_eq_left hadj', List.mem_singleton]
              rfl
            refine ⟨_, hmem, MemLe.push hm rfl hwv hmview, ?_⟩
            rw [hm.1]
            exact ThreadLe_of_fence_right (commitThOf_le hrth a mt.size h.promises) .sy
        . simp at happ
      . -- The write fulfils an outstanding promise.
        obtain ⟨tw, htp, hft⟩ := List.mem_filterMap.1 hful
        have hsame : ma[tw]? = mt[tw]? := hp tw htp
        split at hft
        . simp at hft
        . next pm hmt =>
            have hma : ma[tw]? = some pm := hsame.trans hmt
            obtain ⟨hguard, hpair⟩ := of_ite_some hft
            cases hpair
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hguard
            obtain ⟨⟨⟨⟨hl, hvl⟩, hmv⟩, hob⟩, hadj⟩ := hguard
            have hguard' :
                ((pm.loc == a) && (pm.val == kind.apply ma[t]!.val (rmwNewVal ta.regs newv)) &&
                  decide (rmwMviewAt ta.vs.vRelSt
                    (max ta.vs.vRd (rdV ta.vs pairs t ma[t]!.view))
                    ta.vs.vWr (depView ta.regs (newv.writeDeps deps))
                    (max (pairTop pairs t) ma[t]!.view) rel <= pm.view) &&
                  decide (rmwBaseAt
                      (if acq then max ta.vs.vPreBase (acqV ta.vs pairs t ma[t]!.view) else ta.vs.vPreBase)
                      (if k.storeDepRts then depRts ta.regs (newv.writeDeps deps) else depView ta.regs (newv.writeDeps deps))
                      ta.vs.vCtrl (max (ta.vs.coh a) t) < tw) &&
                  rmwAdjacent ma a t tw) = true := by
              simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
              refine ⟨⟨⟨⟨hl, hvl.trans hwv.symm⟩, Nat.le_trans hmview hmv⟩, ?_⟩, ?_⟩
              . exact Nat.lt_of_le_of_lt hbase
                  (Nat.lt_of_le_of_lt (rmwBaseAt_le_ite _ _ _ _ _ _) hob)
              . rw [rmwAdjacent_congr hm]; exact hadj
            have hmem :
                ((ma : Memory),
                 commitThOf (readThOf ta pairs dst a t (rmwDst kind acq ma[t]! t) ma[t]!.view acq) a tw
                   (ta.promises.erase tw))
                  ∈ stepRmwAt k .arm ma pairs ta dst a kind newv deps acq rel := by
              simp only [stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range]
              refine ⟨t, ⟨htlt', hrd'⟩, ?_⟩
              rw [ite_eq_right hsucc']
              refine List.mem_append.2 (Or.inr (List.mem_filterMap.2 ⟨tw, ?_, ?_⟩))
              . rw [h.promises]; exact htp
              . rw [hma]
                exact ite_eq_left hguard'
            exact ⟨_, hmem, hm,
              ThreadLe_of_fence_right
                (commitThOf_le hrth a tw (by rw [h.promises])) .sy⟩

/-- `stepRmw_sim` for the rule proper: the TSO run's leading `lockFence`
    only raises views on the right, which `ThreadLe_of_fence_right` absorbs. -/
theorem stepRmw_sim (k : Knobs) {ma mt : Memory} (hm : MemLe ma mt) {ta tt : Thread}
    (h : ThreadLe ta tt) (hp : forall t, t ∈ tt.promises -> ma[t]? = mt[t]?)
    (pairs : List Ts)
    (dst : Reg) (a : Address) (kind : RmwKind) (newv : Expr) (deps : List Reg)
    (acq rel : Bool) {mt' : Memory} {tt' : Thread}
    (hin : (mt', tt') ∈ stepRmw k .tso mt pairs tt dst a kind newv deps acq rel) :
    ∃ q ∈ stepRmw k .arm ma pairs ta dst a kind newv deps acq rel,
      MemLe q.1 mt' ∧ ThreadLe q.2 tt' :=
  stepRmwAt_sim k hm (ThreadLe_of_fence_right h .sy) (fun t ht => hp t ht)
    pairs dst a kind newv deps acq rel hin

/-! ### The pair RMW -/

def readThOf2 (th : Thread) (pairs : List Ts) (dst0 dst1 : Reg) (a : Address)
    (t0 t1 : Ts)
    (v0 v1 : Val) (w0 w1 : Ts) (acq : Bool) : Thread :=
  { th with
    regs := fun r =>
      if r = dst0 then ⟨v0, w0, t0⟩ else if r = dst1 then ⟨v1, w1, t1⟩ else th.regs r
    vs := { th.vs with
            coh := fun b =>
              if b = a then max (th.vs.coh a) t0
              else if b = a.next then max (th.vs.coh a.next) t1
              else th.vs.coh b
            vRd := max th.vs.vRd (max (rdV th.vs pairs t0 w0) (rdV th.vs pairs t1 w1))
            vPreBase := if acq then max th.vs.vPreBase
                          (max (acqV th.vs pairs t0 w0) (acqV th.vs pairs t1 w1))
                        else th.vs.vPreBase } }

def commitThOf2 (th : Thread) (a : Address) (tw0 tw1 : Ts) (prom : List Ts) : Thread :=
  { th with
    vs := { th.vs with
            coh := fun b => if b = a then tw0 else if b = a.next then tw1 else th.vs.coh b
            vWr := max th.vs.vWr tw1, mine := (tw1 - 1) :: tw1 :: th.vs.mine }
    promises := prom }

/-- `commitThOf2` plus the wide store's forwarding entries (`pairFwdOf`); a
    pair RMW's write records none. -/
def storeThOf2 (th : Thread) (a : Address) (fw tw0 tw1 : Ts) (prom : List Ts) : Thread :=
  { th with
    vs := { th.vs with
            coh := fun b => if b = a then tw0 else if b = a.next then tw1 else th.vs.coh b
            vWr := max th.vs.vWr tw1, mine := (tw1 - 1) :: tw1 :: th.vs.mine
            fwd := (tw1 - 1, fw) :: (tw1, fw) :: th.vs.fwd }
    promises := prom }

theorem readThOf2_le {ta tt : Thread} (h : ThreadLe ta tt) (pairs : List Ts)
    (dst0 dst1 : Reg) (a : Address)
    (t0 t1 : Ts) {v0a v0t v1a v1t : Val} (h0 : v0a = v0t) (h1 : v1a = v1t)
    {w0a w0t w1a w1t : Ts} (hw0 : w0a <= w0t) (hw1 : w1a <= w1t) (acq : Bool) :
    ThreadLe (readThOf2 ta pairs dst0 dst1 a t0 t1 v0a v1a w0a w1a acq)
             (readThOf2 tt pairs dst0 dst1 a t0 t1 v0t v1t w0t w1t acq) := by
  unfold readThOf2
  refine ⟨h.prog, h.promises, ?_, ?_, ?_, h.vs.vWr, h.vs.vCtrl, ?_, h.vs.vRelSt, (by first | exact h.vs.mine | simp [h.vs.mine] | simp_all), h.vs.fwd⟩
  . intro r
    by_cases hr0 : r = dst0
    . simp only [hr0, ite_true]
      exact ⟨h0, rfl, hw0⟩
    . simp only [hr0, ite_false]
      by_cases hr1 : r = dst1
      . simp only [hr1, ite_true]
        exact ⟨h1, rfl, hw1⟩
      . simp only [hr1, ite_false]
        exact h.regs r
  . intro b
    by_cases hb0 : b = a
    . simp only [hb0, ite_true]
      exact le_max_le (h.vs.coh a) (Nat.le_refl _)
    . simp only [hb0, ite_false]
      by_cases hb1 : b = a.next
      . simp only [hb1, ite_true]
        exact le_max_le (h.vs.coh a.next) (Nat.le_refl _)
      . simp only [hb1, ite_false]
        exact h.vs.coh b
  . exact le_max_le h.vs.vRd (le_max_le (h.vs.rdV pairs t0 hw0) (h.vs.rdV pairs t1 hw1))
  . cases acq
    . exact h.vs.vPreBase
    . exact le_max_le h.vs.vPreBase (le_max_le (h.vs.acqV pairs t0 hw0) (h.vs.acqV pairs t1 hw1))

theorem commitThOf2_le {ta tt : Thread} (h : ThreadLe ta tt) (a : Address) (tw0 tw1 : Ts)
    {pa pt : List Ts} (hprom : pa = pt) :
    ThreadLe (commitThOf2 ta a tw0 tw1 pa) (commitThOf2 tt a tw0 tw1 pt) := by
  unfold commitThOf2
  refine ⟨h.prog, hprom, h.regs, ?_, h.vs.vRd, ?_, h.vs.vCtrl, h.vs.vPreBase, h.vs.vRelSt, (by first | exact h.vs.mine | simp [h.vs.mine] | simp_all), h.vs.fwd⟩
  . intro b
    by_cases hb0 : b = a
    . simp only [hb0, ite_true]
      exact Nat.le_refl _
    . simp only [hb0, ite_false]
      by_cases hb1 : b = a.next
      . simp only [hb1, ite_true]
        exact Nat.le_refl _
      . simp only [hb1, ite_false]
        exact h.vs.coh b
  . exact le_max_le h.vs.vWr (Nat.le_refl _)

theorem storeThOf2_le {ta tt : Thread} (h : ThreadLe ta tt) (a : Address) {fa ft : Ts} (hf : fa <= ft)
    (tw0 tw1 : Ts) {pa pt : List Ts} (hprom : pa = pt) :
    ThreadLe (storeThOf2 ta a fa tw0 tw1 pa) (storeThOf2 tt a ft tw0 tw1 pt) := by
  have hc := commitThOf2_le h a tw0 tw1 hprom
  exact ⟨hc.prog, hc.promises, hc.regs, ⟨hc.vs.coh, hc.vs.vRd, hc.vs.vWr, hc.vs.vCtrl, hc.vs.vPreBase,
    hc.vs.vRelSt, hc.vs.mine, FwdLe.cons hf (FwdLe.cons hf h.vs.fwd)⟩⟩

/-- Two pushes at once.  Stated as its own lemma rather than nesting
    `MemLe.push`: as a nested *argument* the `rfl`s are elaborated before the
    result type is known, and they then unify the two messages with each other. -/
theorem MemLe.push2 {ma mt : Memory} (h : MemLe ma mt) {x0 y0 x1 y1 : Msg}
    (hl0 : x0.loc = y0.loc) (hv0 : x0.val = y0.val) (hw0 : x0.view <= y0.view)
    (hl1 : x1.loc = y1.loc) (hv1 : x1.val = y1.val) (hw1 : x1.view <= y1.view) :
    MemLe ((ma.push x0).push x1) ((mt.push y0).push y1) :=
  MemLe.push (MemLe.push h hl0 hv0 hw0) hl1 hv1 hw1

theorem stepRmwPairAt_sim {ma mt : Memory} (hm : MemLe ma mt) {ta tt : Thread}
    (h : ThreadLe ta tt) (hp : forall t, t ∈ tt.promises -> ma[t]? = mt[t]?)
    (pairs : List Ts) (dst0 dst1 : Reg) (a : Address) (cmp0 cmp1 : Val) (new0 new1 : Expr)
    (deps : List Reg) (acq rel : Bool) {mt' : Memory} {pt' : List Ts} {tt' : Thread}
    (hin : (mt', pt', tt') ∈
      stepRmwPairAt .tso mt pairs tt dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    ∃ q ∈ stepRmwPairAt .arm ma pairs ta dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel,
      MemLe q.1 mt' ∧ q.2.1 = pt' ∧ ThreadLe q.2.2 tt' := by
  simp only [stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range, ite_true] at hin
  obtain ⟨t0, ⟨ht0, hrd0⟩, t1, ⟨ht1, hrd1⟩, hbody⟩ := hin
  have ht0' : t0 < ma.size := by rw [hm.1]; exact ht0
  have ht1' : t1 < ma.size := by rw [hm.1]; exact ht1
  obtain ⟨hloc0, hval0, hview0⟩ := memLe_bang hm ht0
  obtain ⟨hloc1, hval1, hview1⟩ := memLe_bang hm ht1
  -- Both quantities are needed here, for the two sides of the pair RMW.
  have hdv := depBound_mono (fun r => (h.regs r).view) (fun r => (h.regs r).rts) deps
  have hdvv := depView_mono (fun r => (h.regs r).view) (new1.writeDeps (new0.writeDeps deps))
  have hwv0 : rmwNewVal ta.regs new0 = rmwNewVal tt.regs new0 := rmwNewVal_congr h new0
  have hwv1 : rmwNewVal ta.regs new1 = rmwNewVal tt.regs new1 := rmwNewVal_congr h new1
  have hrd0' : readable ma a t0 (readBoundOf .arm ta.vs (depBound ta.regs deps) a) = true := by
    refine readable_antitone (readBoundOf_arm_le_tso h.vs hdv a) ?_
    rw [readable_congr hm]; exact hrd0
  have hrd1' :
      readable ma a.next t1 (readBoundOf .arm ta.vs (depBound ta.regs deps) a.next) = true := by
    refine readable_antitone (readBoundOf_arm_le_tso h.vs hdv a.next) ?_
    rw [readable_congr hm]; exact hrd1
  have hrth := readThOf2_le h pairs dst0 dst1 a t0 t1 hval0 hval1 hview0 hview1 acq
  have hmview :
      rmwMviewAt ta.vs.vRelSt
          (max ta.vs.vRd (max (rdV ta.vs pairs t0 ma[t0]!.view) (rdV ta.vs pairs t1 ma[t1]!.view)))
          ta.vs.vWr (depView ta.regs (new1.writeDeps (new0.writeDeps deps)))
          (max (max (pairTop pairs t0) ma[t0]!.view) (max (pairTop pairs t1) ma[t1]!.view)) rel
        <= rmwMviewAt tt.vs.vRelSt
          (max tt.vs.vRd (max (rdV tt.vs pairs t0 mt[t0]!.view) (rdV tt.vs pairs t1 mt[t1]!.view)))
          tt.vs.vWr (depView tt.regs (new1.writeDeps (new0.writeDeps deps)))
          (max (max (pairTop pairs t0) mt[t0]!.view) (max (pairTop pairs t1) mt[t1]!.view)) rel :=
    rmwMviewAt_mono h.vs.vRelSt
      (le_max_le h.vs.vRd (le_max_le (h.vs.rdV pairs t0 hview0) (h.vs.rdV pairs t1 hview1))) h.vs.vWr hdvv
      (le_max_le (le_max_le (Nat.le_refl (pairTop pairs t0)) hview0)
        (le_max_le (Nat.le_refl (pairTop pairs t1)) hview1)) rel
  have hbase :
      rmwBaseAt
          (if acq then max ta.vs.vPreBase (max (acqV ta.vs pairs t0 ma[t0]!.view) (acqV ta.vs pairs t1 ma[t1]!.view)) else ta.vs.vPreBase)
          (depRts ta.regs (new1.writeDeps (new0.writeDeps deps))) ta.vs.vCtrl (max (ta.vs.coh a) t0)
        <= rmwBaseAt
          (if acq then max tt.vs.vPreBase (max (acqV tt.vs pairs t0 mt[t0]!.view) (acqV tt.vs pairs t1 mt[t1]!.view)) else tt.vs.vPreBase)
          (depRts tt.regs (new1.writeDeps (new0.writeDeps deps))) tt.vs.vCtrl (max (tt.vs.coh a) t0) :=
    rmwBaseAt_mono hrth.vs.vPreBase
      (Nat.le_of_eq (depRts_congr (fun r => (h.regs r).rts) (new1.writeDeps (new0.writeDeps deps)))) h.vs.vCtrl
      (le_max_le (h.vs.coh a) (Nat.le_refl t0))
  split at hbody
  . simp at hbody
  . next hns =>
      have hns' : ¬ (pairStraddles ma pairs a t0 t1 = true) := by
        rw [pairStraddles_congr hm]; exact hns
      split at hbody
      . -- The compare failed: two loads.
        next hfail =>
          have hfail' :
              (!(decide (ma[t0]!.val = cmp0) && decide (ma[t1]!.val = cmp1))) = true := by
            rw [hval0, hval1]; exact hfail
          rw [List.mem_singleton] at hbody
          cases hbody
          have hmem : ((ma : Memory), pairs,
              readThOf2 ta pairs dst0 dst1 a t0 t1 ma[t0]!.val ma[t1]!.val ma[t0]!.view
                ma[t1]!.view acq)
              ∈ stepRmwPairAt .arm ma pairs ta dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel := by
            simp only [stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range]
            refine ⟨t0, ⟨ht0', hrd0'⟩, t1, ⟨ht1', hrd1'⟩, ?_⟩
            rw [ite_eq_right hns', ite_eq_left hfail', List.mem_singleton]
            rfl
          exact ⟨_, hmem, hm, rfl, ThreadLe_of_fence_right hrth .sy⟩
      . next hsucc =>
          have hsucc' :
              ¬ ((!(decide (ma[t0]!.val = cmp0) && decide (ma[t1]!.val = cmp1))) = true) := by
            rw [hval0, hval1]; exact hsucc
          rw [List.mem_append] at hbody
          rcases hbody with happ | hful
          . -- Both writes are appended at the end of memory.
            split at happ
            . next hadj =>
                have hadj' :
                    (rmwAdjacent ma a t0 ma.size &&
                      rmwAdjacent ma a.next t1 (ma.size + 1)) = true := by
                  rw [rmwAdjacent_congr hm, rmwAdjacent_congr hm, hm.1]; exact hadj
                rw [List.mem_singleton] at happ
                cases happ
                have hmem :
                    (((ma.push ⟨a, rmwNewVal ta.regs new0, rmwMviewAt ta.vs.vRelSt
                          (max ta.vs.vRd (max (rdV ta.vs pairs t0 ma[t0]!.view) (rdV ta.vs pairs t1 ma[t1]!.view)))
                          ta.vs.vWr (depView ta.regs (new1.writeDeps (new0.writeDeps deps)))
                          (max (max (pairTop pairs t0) ma[t0]!.view) (max (pairTop pairs t1) ma[t1]!.view)) rel⟩).push
                        ⟨a.next, rmwNewVal ta.regs new1, rmwMviewAt ta.vs.vRelSt
                          (max ta.vs.vRd (max (rdV ta.vs pairs t0 ma[t0]!.view) (rdV ta.vs pairs t1 ma[t1]!.view)))
                          ta.vs.vWr (depView ta.regs (new1.writeDeps (new0.writeDeps deps)))
                          (max (max (pairTop pairs t0) ma[t0]!.view) (max (pairTop pairs t1) ma[t1]!.view)) rel⟩),
                     pairs ++ [ma.size],
                     commitThOf2 (readThOf2 ta pairs dst0 dst1 a t0 t1 ma[t0]!.val ma[t1]!.val
                       ma[t0]!.view ma[t1]!.view acq) a ma.size (ma.size + 1) ta.promises)
                    ∈ stepRmwPairAt .arm ma pairs ta dst0 dst1 a cmp0 cmp1 new0 new1 deps
                        acq rel := by
                  simp only [stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range]
                  refine ⟨t0, ⟨ht0', hrd0'⟩, t1, ⟨ht1', hrd1'⟩, ?_⟩
                  rw [ite_eq_right hns', ite_eq_right hsucc']
                  refine List.mem_append.2 (Or.inl ?_)
                  rw [ite_eq_left hadj', List.mem_singleton]
                  rfl
                refine ⟨_, hmem, MemLe.push2 hm rfl hwv0 hmview rfl hwv1 hmview, ?_, ?_⟩
                . rw [hm.1]
                . rw [hm.1]
                  exact ThreadLe_of_fence_right
                    (commitThOf2_le hrth a mt.size (mt.size + 1) h.promises) .sy
            . simp at happ
          . -- Both writes fulfil outstanding promises.
            obtain ⟨tw0, htp, hft⟩ := List.mem_filterMap.1 hful
            split at hft
            . next pm0 pm1 hmt0 hmt1 =>
                obtain ⟨hguard, htriple⟩ := of_ite_some hft
                cases htriple
                simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hguard
                obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpc, hc⟩, hl0⟩, hv0⟩, hm0⟩, hl1⟩, hv1⟩, hm1⟩, hob⟩, hadj0⟩, hadj1⟩ :=
                  hguard
                have htp1 : (tw0 + 1) ∈ tt.promises := List.mem_of_elem_eq_true hc
                have hma0 : ma[tw0]? = some pm0 := (hp tw0 htp).trans hmt0
                have hma1 : ma[tw0 + 1]? = some pm1 := (hp (tw0 + 1) htp1).trans hmt1
                have hguard' :
                    (pairs.contains tw0 && ta.promises.contains (tw0 + 1) && (pm0.loc == a) && (pm0.val == rmwNewVal ta.regs new0) &&
                      decide (rmwMviewAt ta.vs.vRelSt
                        (max ta.vs.vRd (max (rdV ta.vs pairs t0 ma[t0]!.view) (rdV ta.vs pairs t1 ma[t1]!.view)))
                        ta.vs.vWr (depView ta.regs (new1.writeDeps (new0.writeDeps deps)))
                        (max (max (pairTop pairs t0) ma[t0]!.view) (max (pairTop pairs t1) ma[t1]!.view)) rel <= pm0.view) &&
                      (pm1.loc == a.next) && (pm1.val == rmwNewVal ta.regs new1) &&
                      decide (rmwMviewAt ta.vs.vRelSt
                        (max ta.vs.vRd (max (rdV ta.vs pairs t0 ma[t0]!.view) (rdV ta.vs pairs t1 ma[t1]!.view)))
                        ta.vs.vWr (depView ta.regs (new1.writeDeps (new0.writeDeps deps)))
                        (max (max (pairTop pairs t0) ma[t0]!.view) (max (pairTop pairs t1) ma[t1]!.view)) rel <= pm1.view) &&
                      decide (rmwBaseAt
                        (if acq then max ta.vs.vPreBase (max (acqV ta.vs pairs t0 ma[t0]!.view) (acqV ta.vs pairs t1 ma[t1]!.view))
                         else ta.vs.vPreBase)
                        (depRts ta.regs (new1.writeDeps (new0.writeDeps deps))) ta.vs.vCtrl (max (ta.vs.coh a) t0) < tw0) &&
                      rmwAdjacent ma a t0 tw0 &&
                      rmwAdjacent ma a.next t1 (tw0 + 1)) = true := by
                  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
                  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpc, ?_⟩, hl0⟩, hv0.trans hwv0.symm⟩, Nat.le_trans hmview hm0⟩, hl1⟩, hv1.trans hwv1.symm⟩,
                    Nat.le_trans hmview hm1⟩, ?_⟩, ?_⟩, ?_⟩
                  . rw [h.promises]; exact hc
                  . exact Nat.lt_of_le_of_lt hbase (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hob)
                  . rw [rmwAdjacent_congr hm]; exact hadj0
                  . rw [rmwAdjacent_congr hm]; exact hadj1
                have hmem : ((ma : Memory), pairs,
                    commitThOf2 (readThOf2 ta pairs dst0 dst1 a t0 t1 ma[t0]!.val ma[t1]!.val
                      ma[t0]!.view ma[t1]!.view acq) a tw0 (tw0 + 1)
                      ((ta.promises.erase tw0).erase (tw0 + 1)))
                    ∈ stepRmwPairAt .arm ma pairs ta dst0 dst1 a cmp0 cmp1 new0 new1 deps
                        acq rel := by
                  simp only [stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range]
                  refine ⟨t0, ⟨ht0', hrd0'⟩, t1, ⟨ht1', hrd1'⟩, ?_⟩
                  rw [ite_eq_right hns', ite_eq_right hsucc']
                  refine List.mem_append.2 (Or.inr (List.mem_filterMap.2 ⟨tw0, ?_, ?_⟩))
                  . rw [h.promises]; exact htp
                  . rw [hma0, hma1]
                    exact ite_eq_left hguard'
                exact ⟨_, hmem, hm, rfl, ThreadLe_of_fence_right
                  (commitThOf2_le hrth a tw0 (tw0 + 1) (by rw [h.promises])) .sy⟩
            . simp at hft

/-! ### The wide access

Neither rule contains anything the pair RMW did not already have, and the two
simulations say so by being shorter than the ones above rather than longer.

`stepLoadPair` is `stepRmwPair`'s failed-compare branch with the compare
deleted: same two reads, same `pairStraddles` filter, same `readThOf2` shape, so
the same lemmas discharge it.

`stepStorePair` is append-only (see §2), and that is what makes its simulation
*shorter* than `stepStore`'s.  `stepStore_sim` needs `hp` -- at a promised
timestamp the two runs hold the same message -- solely to relate the fulfilment
branch.  A wide store has no fulfilment branch, so there is no promised
timestamp to relate, and the lemma below takes no such hypothesis.  It is also
the reason it needs no `∃`: the rule is a function, not a list. -/

/-- What a wide store publishes: the join of what its two words would publish on
    their own.  Named for the reason `rmwMviewAt` is named -- both runs then
    present the same normal form, instead of two `max`-of-`let` trees that
    `simp` and `whnf` disagree about. -/
def storePairMview (th : Thread) (e0 e1 : Expr) (deps : List Reg) (rel : Bool) : Ts :=
  max (storeMview th e0 deps rel) (storeMview th e1 deps rel)

theorem storePairMview_mono {ta tt : Thread} (h : ThreadLe ta tt) (e0 e1 : Expr)
    (deps : List Reg) (rel : Bool) :
    storePairMview ta e0 e1 deps rel <= storePairMview tt e0 e1 deps rel :=
  le_max_le (storeMview_mono h e0 deps rel) (storeMview_mono h e1 deps rel)

/-- `stepStorePair` with its `let`-chain spelled out.  The proof is `rfl`; the
    shape it reduces to is the content.  A wide store commits through
    `storeThOf2` -- the pair RMW's `commitThOf2` plus the forwarding entries. -/
theorem stepStorePair_eq (mem : Memory) (pairs : List Ts) (th : Thread) (a : Address)
    (e0 e1 : Expr) (deps : List Reg) (rel : Bool) :
    stepStorePair mem pairs th a e0 e1 deps rel =
      ((mem.push ⟨a, storeValOf th e0, storePairMview th e0 e1 deps rel⟩).push
         ⟨a.next, storeValOf th e1, storePairMview th e0 e1 deps rel⟩,
       pairs ++ [mem.size],
       storeThOf2 th a (pairFwdOf th.regs e0 e1 deps) mem.size (mem.size + 1) th.promises) := rfl

/-- `stepRmwPair_sim` for the rule proper; see `stepRmw_sim`. -/
theorem stepRmwPair_sim {ma mt : Memory} (hm : MemLe ma mt) {ta tt : Thread}
    (h : ThreadLe ta tt) (hp : forall t, t ∈ tt.promises -> ma[t]? = mt[t]?)
    (pairs : List Ts) (dst0 dst1 : Reg) (a : Address) (cmp0 cmp1 : Val) (new0 new1 : Expr)
    (deps : List Reg) (acq rel : Bool) {mt' : Memory} {pt' : List Ts} {tt' : Thread}
    (hin : (mt', pt', tt') ∈
      stepRmwPair .tso mt pairs tt dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    ∃ q ∈ stepRmwPair .arm ma pairs ta dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel,
      MemLe q.1 mt' ∧ q.2.1 = pt' ∧ ThreadLe q.2.2 tt' :=
  stepRmwPairAt_sim hm (ThreadLe_of_fence_right h .sy) (fun t ht => hp t ht)
    pairs dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel hin

theorem stepStorePair_sim {ma mt : Memory} (hm : MemLe ma mt) {ta tt : Thread}
    (h : ThreadLe ta tt) (a : Address) (e0 e1 : Expr) (deps : List Reg) (rel : Bool) :
    MemLe
        ((ma.push ⟨a, storeValOf ta e0, storePairMview ta e0 e1 deps rel⟩).push
          ⟨a.next, storeValOf ta e1, storePairMview ta e0 e1 deps rel⟩)
        ((mt.push ⟨a, storeValOf tt e0, storePairMview tt e0 e1 deps rel⟩).push
          ⟨a.next, storeValOf tt e1, storePairMview tt e0 e1 deps rel⟩)
      ∧ ThreadLe (storeThOf2 ta a (pairFwdOf ta.regs e0 e1 deps) ma.size (ma.size + 1) ta.promises)
                 (storeThOf2 tt a (pairFwdOf tt.regs e0 e1 deps) mt.size (mt.size + 1) tt.promises) := by
  have hmv := storePairMview_mono h e0 e1 deps rel
  refine ⟨MemLe.push2 hm rfl (storeValOf_congr h e0) hmv rfl (storeValOf_congr h e1) hmv, ?_⟩
  rw [hm.1]
  exact storeThOf2_le h a (fwdOf_mono h e0 _) mt.size (mt.size + 1) h.promises

theorem stepLoadPair_sim {ma mt : Memory} (hm : MemLe ma mt) {ta tt : Thread}
    (h : ThreadLe ta tt) (pairs : List Ts) (dst0 dst1 : Reg) (a : Address)
    (deps : List Reg) (acq : Bool)
    {tt' : Thread} (hin : tt' ∈ stepLoadPair .tso mt pairs tt dst0 dst1 a deps acq) :
    ∃ ta' ∈ stepLoadPair .arm ma pairs ta dst0 dst1 a deps acq, ThreadLe ta' tt' := by
  simp only [stepLoadPair, List.mem_flatMap, List.mem_filter, List.mem_range,
    List.mem_filterMap] at hin
  obtain ⟨t0, ⟨ht0, hrd0⟩, t1, ⟨ht1, hrd1⟩, hbody⟩ := hin
  have ht0' : t0 < ma.size := by rw [hm.1]; exact ht0
  have ht1' : t1 < ma.size := by rw [hm.1]; exact ht1
  obtain ⟨hloc0, hval0, hview0⟩ := memLe_bang hm ht0
  obtain ⟨hloc1, hval1, hview1⟩ := memLe_bang hm ht1
  have hdv := depBound_mono (fun r => (h.regs r).view) (fun r => (h.regs r).rts) deps
  have hrd0' : readable ma a t0 (readBoundOf .arm ta.vs (depBound ta.regs deps) a) = true := by
    refine readable_antitone (readBoundOf_arm_le_tso h.vs hdv a) ?_
    rw [readable_congr hm]; exact hrd0
  have hrd1' :
      readable ma a.next t1 (readBoundOf .arm ta.vs (depBound ta.regs deps) a.next) = true := by
    refine readable_antitone (readBoundOf_arm_le_tso h.vs hdv a.next) ?_
    rw [readable_congr hm]; exact hrd1
  split at hbody
  . simp at hbody
  . next hns =>
      have hns' : ¬ (pairStraddles ma pairs a t0 t1 = true) := by
        rw [pairStraddles_congr hm]; exact hns
      obtain rfl := Option.some.inj hbody
      refine ⟨readThOf2 ta pairs dst0 dst1 a t0 t1 ma[t0]!.val ma[t1]!.val
          ma[t0]!.view ma[t1]!.view acq, ?_,
        readThOf2_le h pairs dst0 dst1 a t0 t1 hval0 hval1 hview0 hview1 acq⟩
      simp only [stepLoadPair, List.mem_flatMap, List.mem_filter, List.mem_range,
        List.mem_filterMap]
      exact ⟨t0, ⟨ht0', hrd0'⟩, t1, ⟨ht1', hrd1'⟩, ite_eq_right hns'⟩

/-! ### What a step does to memory and to the promise list

The simulation invariant has a second half -- at an outstanding promised
timestamp the two runs hold the *same* message -- and to carry it across a step
one needs two facts about *one* run: memory only grows at the end, and a step
never invents a promise.  Both are architecture-generic, so each is proved once
and used on both sides. -/

structure MemExt (m m' : Memory) : Prop where
  size : m.size <= m'.size
  get : forall (t : Nat), t < m.size -> m'[t]? = m[t]?

theorem MemExt.refl (m : Memory) : MemExt m m := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem MemExt.trans {m m' m'' : Memory} (h : MemExt m m') (h' : MemExt m' m'') :
    MemExt m m'' :=
  ⟨Nat.le_trans h.size h'.size,
   fun t ht => (h'.get t (Nat.lt_of_lt_of_le ht h.size)).trans (h.get t ht)⟩

theorem MemExt.push (m : Memory) (x : Msg) : MemExt m (m.push x) := by
  refine ⟨?_, ?_⟩
  . rw [Array.size_push]; exact Nat.le_succ _
  . intro t ht
    rw [Array.getElem?_push, ite_eq_right (Nat.ne_of_lt ht)]

/-- A fence leaves the promise list alone, and so does the `lockFence` wrapper
    the RMW rules put around their result. -/
theorem lockFence_promises (arch : Arch) (th : Thread) :
    (if arch = .tso then stepFence th .sy else th).promises = th.promises := by
  split <;> rfl

theorem stepLoad_ext (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst : Reg) (a : Address)
    (deps : List Reg) (acq : Bool) {th' : Thread}
    (hin : th' ∈ stepLoad arch mem pairs th dst a deps acq) :
    forall t, t ∈ th'.promises -> t ∈ th.promises := by
  simp only [stepLoad, List.mem_map, List.mem_filter, List.mem_range] at hin
  obtain ⟨t, _, rfl⟩ := hin
  exact fun _ ht => ht

theorem stepStore_ext (k : Knobs) (arch : Arch) (mem : Memory) (th : Thread) (a : Address)
    (e : Expr) (deps : List Reg) (rel : Bool) {mem' : Memory} {th' : Thread}
    (hin : (mem', th') ∈ stepStore k arch mem th a e deps rel) :
    MemExt mem mem' ∧ forall t, t ∈ th'.promises -> t ∈ th.promises := by
  simp only [stepStore, List.mem_append, List.mem_singleton] at hin
  rcases hin with happ | hful
  . cases happ
    exact ⟨MemExt.push mem _, fun _ ht => ht⟩
  . obtain ⟨tw, _, hft⟩ := List.mem_filterMap.1 hful
    split at hft
    . simp at hft
    . obtain ⟨_, hpair⟩ := of_ite_some hft
      cases hpair
      exact ⟨MemExt.refl mem, fun _ ht => List.mem_of_mem_erase ht⟩

theorem stepRmwAt_ext (k : Knobs) (arch : Arch) (mem : Memory) (pairs : List Ts)
    (th : Thread) (dst : Reg)
    (a : Address) (kind : RmwKind) (newv : Expr) (deps : List Reg) (acq rel : Bool)
    {mem' : Memory} {th' : Thread}
    (hin : (mem', th') ∈ stepRmwAt k arch mem pairs th dst a kind newv deps acq rel) :
    MemExt mem mem' ∧ forall t, t ∈ th'.promises -> t ∈ th.promises := by
  simp only [stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at hin
  obtain ⟨t, _, hbody⟩ := hin
  split at hbody
  . rw [List.mem_singleton] at hbody
    cases hbody
    refine ⟨MemExt.refl mem, ?_⟩
    intro t' ht'
    rw [lockFence_promises] at ht'
    exact ht'
  . rw [List.mem_append] at hbody
    rcases hbody with happ | hful
    . split at happ
      . rw [List.mem_singleton] at happ
        cases happ
        refine ⟨MemExt.push mem _, ?_⟩
        intro t' ht'
        rw [lockFence_promises] at ht'
        exact ht'
      . simp at happ
    . obtain ⟨tw, _, hft⟩ := List.mem_filterMap.1 hful
      split at hft
      . simp at hft
      . obtain ⟨_, hpair⟩ := of_ite_some hft
        cases hpair
        refine ⟨MemExt.refl mem, ?_⟩
        intro t' ht'
        rw [lockFence_promises] at ht'
        exact List.mem_of_mem_erase ht'

theorem stepRmwPairAt_ext (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst0 dst1 : Reg) (a : Address) (cmp0 cmp1 : Val) (new0 new1 : Expr) (deps : List Reg)
    (acq rel : Bool) {mem' : Memory} {pairs' : List Ts} {th' : Thread}
    (hin : (mem', pairs', th') ∈
      stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    MemExt mem mem' ∧ forall t, t ∈ th'.promises -> t ∈ th.promises := by
  simp only [stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at hin
  obtain ⟨t0, _, t1, _, hbody⟩ := hin
  split at hbody
  . simp at hbody
  . split at hbody
    . rw [List.mem_singleton] at hbody
      cases hbody
      refine ⟨MemExt.refl mem, ?_⟩
      intro t' ht'
      rw [lockFence_promises] at ht'
      exact ht'
    . rw [List.mem_append] at hbody
      rcases hbody with happ | hful
      . split at happ
        . rw [List.mem_singleton] at happ
          cases happ
          refine ⟨MemExt.trans (MemExt.push mem _) (MemExt.push _ _), ?_⟩
          intro t' ht'
          rw [lockFence_promises] at ht'
          exact ht'
        . simp at happ
      . obtain ⟨tw0, _, hft⟩ := List.mem_filterMap.1 hful
        split at hft
        . obtain ⟨_, htriple⟩ := of_ite_some hft
          cases htriple
          refine ⟨MemExt.refl mem, ?_⟩
          intro t' ht'
          rw [lockFence_promises] at ht'
          exact List.mem_of_mem_erase (List.mem_of_mem_erase ht')
        . simp at hft

/-- `stepRmw` is `stepRmwAt` after a fence, and a fence keeps the promises. -/
theorem stepRmw_ext (k : Knobs) (arch : Arch) (mem : Memory) (pairs : List Ts)
    (th : Thread) (dst : Reg)
    (a : Address) (kind : RmwKind) (newv : Expr) (deps : List Reg) (acq rel : Bool)
    {mem' : Memory} {th' : Thread}
    (hin : (mem', th') ∈ stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    MemExt mem mem' ∧ forall t, t ∈ th'.promises -> t ∈ th.promises := by
  have h := stepRmwAt_ext k arch mem pairs _ dst a kind newv deps acq rel hin
  exact ⟨h.1, fun t ht => by have h2 := h.2 t ht; rwa [lockFence_promises] at h2⟩

theorem stepRmwPair_ext (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst0 dst1 : Reg) (a : Address) (cmp0 cmp1 : Val) (new0 new1 : Expr) (deps : List Reg)
    (acq rel : Bool) {mem' : Memory} {pairs' : List Ts} {th' : Thread}
    (hin : (mem', pairs', th') ∈
      stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    MemExt mem mem' ∧ forall t, t ∈ th'.promises -> t ∈ th.promises := by
  have h := stepRmwPairAt_ext arch mem pairs _ dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel hin
  exact ⟨h.1, fun t ht => by have h2 := h.2 t ht; rwa [lockFence_promises] at h2⟩

/-- The wide store's half.  Two things are stronger here than in the lemmas
    above, and both are the absence of a fulfilment branch: memory grows by
    exactly two, and the promise list is not merely preserved up to `erase` --
    it is untouched. -/
theorem stepStorePair_ext (mem : Memory) (pairs : List Ts) (th : Thread) (a : Address)
    (e0 e1 : Expr) (deps : List Reg) (rel : Bool) :
    MemExt mem (stepStorePair mem pairs th a e0 e1 deps rel).1
      ∧ forall t, t ∈ (stepStorePair mem pairs th a e0 e1 deps rel).2.2.promises ->
          t ∈ th.promises := by
  rw [stepStorePair_eq]
  exact ⟨MemExt.trans (MemExt.push mem _) (MemExt.push _ _), fun _ ht => ht⟩

/-- The wide load's half.  It writes nothing, so there is no `MemExt` to state. -/
theorem stepLoadPair_ext (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst0 dst1 : Reg) (a : Address) (deps : List Reg) (acq : Bool) {th' : Thread}
    (hin : th' ∈ stepLoadPair arch mem pairs th dst0 dst1 a deps acq) :
    forall t, t ∈ th'.promises -> t ∈ th.promises := by
  simp only [stepLoadPair, List.mem_flatMap, List.mem_filter, List.mem_range,
    List.mem_filterMap] at hin
  obtain ⟨t0, _, t1, _, hbody⟩ := hin
  split at hbody
  . simp at hbody
  . obtain rfl := Option.some.inj hbody
    exact fun _ ht => ht

/-! ### The configuration invariant

`ConfigLe` alone is *not* inductive.  The store and RMW fulfilment cases need
`mview_arm ≤ (the message at the promised timestamp).view` on the ARM side, and
`MemLe` gives the inequality the wrong way round.  What rescues it is that a
promised message is created by `promiseSteps` with an explicit view `w` drawn
from the same list in both runs: at an outstanding promised timestamp the two
memories agree *exactly*.  That is the second field. -/

structure Sim (ca ct : Config) : Prop where
  le : ConfigLe ca ct
  prom : forall (i : Nat) (tt : Thread), ct.ths[i]? = some tt ->
    forall t, t ∈ tt.promises -> t < ca.mem.size ∧ ca.mem[t]? = ct.mem[t]?

/-- The two runs have the same number of threads, so a thread on one side is a
    thread on the other. -/
theorem ths_some {ca ct : Config} (h : ConfigLe ca ct) {i : Nat} {tt : Thread}
    (hi : ct.ths[i]? = some tt) : ∃ ta, ca.ths[i]? = some ta ∧ ThreadLe ta tt := by
  cases hca : ca.ths[i]? with
  | none =>
      exfalso
      have h1 : ca.ths.size <= i := Array.getElem?_eq_none_iff.1 hca
      rw [h.size] at h1
      rw [Array.getElem?_eq_none_iff.2 h1] at hi
      simp at hi
  | some ta => exact ⟨ta, rfl, h.ths i ta tt hca hi⟩

/-- Updating the same slot of both thread arrays with related threads. -/
theorem ths_set_le {A B : Array Thread} {tha tht : Thread} (i : Nat)
    (hold : forall (j : Nat) (x y : Thread), A[j]? = some x -> B[j]? = some y -> ThreadLe x y)
    (hnew : ThreadLe tha tht) :
    forall (j : Nat) (x y : Thread),
      (A.set! i tha)[j]? = some x -> (B.set! i tht)[j]? = some y -> ThreadLe x y := by
  intro j x y hx hy
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hx hy
  by_cases hij : i = j
  . rw [ite_eq_left hij] at hx hy
    split at hx
    . split at hy
      . cases hx; cases hy; exact hnew
      . simp at hy
    . simp at hx
  . rw [ite_eq_right hij] at hx hy
    exact hold j x y hx hy

/-- Reading a slot of an updated thread array: either it is the new thread, or
    it was there before. -/
theorem ths_set_cases {A : Array Thread} {th' : Thread} (i j : Nat) {x : Thread}
    (hx : (A.set! i th')[j]? = some x) : x = th' ∨ A[j]? = some x := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hx
  by_cases hij : i = j
  . rw [ite_eq_left hij] at hx
    split at hx
    . cases hx; exact Or.inl rfl
    . simp at hx
  . rw [ite_eq_right hij] at hx
    exact Or.inr hx

/-- Pushing onto both memories keeps a timestamp below the old size agreeing. -/
theorem prom_push {ma mt : Memory} (hsz : ma.size = mt.size) {t : Ts} (ht : t < ma.size)
    (heq : ma[t]? = mt[t]?) (x y : Msg) :
    t < (ma.push x).size ∧ (ma.push x)[t]? = (mt.push y)[t]? := by
  refine ⟨Nat.lt_of_lt_of_le ht (MemExt.push ma x).size, ?_⟩
  rw [(MemExt.push ma x).get t ht,
      (MemExt.push mt y).get t (by rw [← hsz]; exact ht)]
  exact heq

/-! ### The promise step

`promiseCands` looks at memory only through `loc` and `val`, which `MemLe`
pins, and at the thread only through `prog` and `promises`, which `ThreadLe`
pins.  So the candidate lists are *equal*, both runs choose the same view `w`,
and the two pushed messages are identical. -/

theorem locValAt_congr {ma mt : Memory} (h : MemLe ma mt) (a : Address) (v : Val) (t : Ts) :
    (ma[t]?.elim false fun m => m.loc == a && m.val == v)
      = (mt[t]?.elim false fun m => m.loc == a && m.val == v) := by
  cases hma : ma[t]? with
  | none =>
      cases hmt : mt[t]? with
      | none => rfl
      | some n =>
          exfalso
          have h1 : ma.size <= t := Array.getElem?_eq_none_iff.1 hma
          rw [h.1] at h1
          rw [Array.getElem?_eq_none_iff.2 h1] at hmt
          simp at hmt
  | some m =>
      cases hmt : mt[t]? with
      | none =>
          exfalso
          have h1 : mt.size <= t := Array.getElem?_eq_none_iff.1 hmt
          rw [← h.1] at h1
          rw [Array.getElem?_eq_none_iff.2 h1] at hma
          simp at hma
      | some n =>
          obtain ⟨hl, hv, _⟩ := h.2 t m n hma hmt
          simp [hl, hv]

theorem locVal_congr {ma mt : Memory} (h : MemLe ma mt) (t : Ts) : locVal ma t = locVal mt t := by
  unfold locVal
  cases hma : ma[t]? with
  | none =>
      cases hmt : mt[t]? with
      | none => rfl
      | some n =>
          exfalso
          have h1 : ma.size <= t := Array.getElem?_eq_none_iff.1 hma
          rw [h.1] at h1
          rw [Array.getElem?_eq_none_iff.2 h1] at hmt
          simp at hmt
  | some m =>
      cases hmt : mt[t]? with
      | none =>
          exfalso
          have h1 : mt.size <= t := Array.getElem?_eq_none_iff.1 hmt
          rw [← h.1] at h1
          rw [Array.getElem?_eq_none_iff.2 h1] at hma
          simp at hma
      | some n =>
          obtain ⟨hl, hv, _⟩ := h.2 t m n hma hmt
          simp [hl, hv]

theorem latestVal_congr {ma mt : Memory} (h : MemLe ma mt) (a : Address) :
    latestVal ma a = latestVal mt a := by
  unfold latestVal
  rw [h.1]
  congr 1
  funext t
  rw [locVal_congr h t]

theorem constStores_congr {ma mt : Memory} (h : MemLe ma mt) (prog : List Instr) :
    constStores ma prog = constStores mt prog := by
  induction prog with
  | nil => rfl
  | cons i rest ih =>
      cases i with
      | rmw dst a kind nv deps acq rel =>
          cases nv with
          | const v => simp only [constStores, latestVal_congr h a, ih]
          | reg r => simp only [constStores, ih]
      | store a e deps rel =>
          cases e with
          | const v => simp only [constStores, ih]
          | reg r => simp only [constStores, ih]
      | _ => simp only [constStores, ih]

theorem promiseCands_congr (k : Knobs) {ta tt : Thread} (h : ThreadLe ta tt)
    {ma mt : Memory} (hm : MemLe ma mt) : promiseCands k ta ma = promiseCands k tt mt := by
  unfold promiseCands
  simp only [h.prog, h.promises, locValAt_congr hm, constStores_congr hm, locVal_congr hm]

theorem pairPromiseCands_congr (k : Knobs) {ta tt : Thread} (h : ThreadLe ta tt)
    {ma mt : Memory} (hm : MemLe ma mt) :
    pairPromiseCands k ta ma = pairPromiseCands k tt mt := by
  unfold pairPromiseCands
  simp only [h.prog, h.promises, locValAt_congr hm]

theorem push_self (m : Memory) (x : Msg) : (m.push x)[m.size]? = some x := by
  rw [Array.getElem?_push, ite_eq_left rfl]

/-- Both runs push the *same* message, so exact agreement extends -- and it
    extends to the new timestamp too, which is what makes the promise step the
    only place agreement can be created. -/
theorem push_agree {ma mt : Memory} (hsz : ma.size = mt.size) (x : Msg) {t : Ts}
    (hle : t <= ma.size) (hold : t < ma.size -> ma[t]? = mt[t]?) :
    t < (ma.push x).size ∧ (ma.push x)[t]? = (mt.push x)[t]? := by
  rcases Nat.lt_or_ge t ma.size with hlt | hge
  . refine ⟨Nat.lt_of_lt_of_le hlt (MemExt.push ma x).size, ?_⟩
    rw [(MemExt.push ma x).get t hlt, (MemExt.push mt x).get t (by rw [← hsz]; exact hlt)]
    exact hold hlt
  . have ht : t = ma.size := Nat.le_antisymm hle hge
    subst ht
    refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, ?_⟩
    rw [push_self ma x, hsz, push_self mt x]

theorem push2_agree {ma mt : Memory} (hsz : ma.size = mt.size) (x y : Msg) {t : Ts}
    (hle : t <= ma.size + 1) (hold : t < ma.size -> ma[t]? = mt[t]?) :
    t < ((ma.push x).push y).size ∧
      ((ma.push x).push y)[t]? = ((mt.push x).push y)[t]? := by
  refine push_agree ?_ y ?_ ?_
  . rw [Array.size_push, Array.size_push, hsz]
  . rw [Array.size_push]; exact hle
  . intro h1
    rw [Array.size_push] at h1
    exact (push_agree hsz x (Nat.le_of_lt_succ h1) hold).2

theorem promiseTh_le {ta tt : Thread} (h : ThreadLe ta tt) {pa pt : List Ts} (hp : pa = pt) :
    ThreadLe { ta with promises := pa } { tt with promises := pt } :=
  ⟨h.prog, hp, h.regs, h.vs⟩

theorem promiseSteps_sim (k : Knobs) {ca ct : Config} (hs : Sim ca ct) (i : Nat)
    {ct' : Config} (hin : ct' ∈ promiseSteps k ct i) :
    ∃ ca' ∈ promiseSteps k ca i, Sim ca' ct' := by
  have hsz : ca.mem.size = ct.mem.size := hs.le.mem.1
  unfold promiseSteps at hin
  split at hin
  . simp at hin
  . next hk =>
      split at hin
      . simp at hin
      . next tt htt =>
          obtain ⟨ta, hta, hth⟩ := ths_some hs.le htt
          simp only [List.mem_append, List.mem_flatMap, List.mem_map] at hin
          rcases hin with ⟨⟨a, v⟩, hcand, w, hw, hcfg⟩ | ⟨⟨a, v0, v1⟩, hcand, w, hw, hcfg⟩
          . -- A single-word promise.
            cases hcfg
            have hcand' : (a, v) ∈ promiseCands k ta ca.mem := by
              rw [promiseCands_congr k hth hs.le.mem]; exact hcand
            have hw' : w ∈ (if k.promiseViews then List.range ca.mem.size else [0]) := by
              rw [hsz]; exact hw
            have hmem :
                ({ ca with
                    mem := ca.mem.push ⟨a, v, w⟩
                    ths := ca.ths.set! i
                             { ta with promises := ta.promises ++ [ca.mem.size] } } : Config)
                  ∈ promiseSteps k ca i := by
              unfold promiseSteps
              rw [ite_eq_right hk, hta]
              refine List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨(a, v), hcand', ?_⟩))
              exact List.mem_map.2 ⟨w, hw', rfl⟩
            refine ⟨_, hmem, ⟨⟨MemLe.push hs.le.mem rfl rfl (Nat.le_refl w),
              hs.le.pairs, ?_, ?_⟩, ?_⟩⟩
            . rw [Array.size_set!, Array.size_set!]; exact hs.le.size
            . exact ths_set_le i hs.le.ths
                (promiseTh_le hth (by rw [hth.promises, hsz]))
            . intro j y hj t htp
              rcases ths_set_cases i j hj with rfl | hold
              . rcases List.mem_append.1 htp with hin1 | hin2
                . have hoo := hs.prom i tt htt t hin1
                  exact push_agree hsz _ (Nat.le_of_lt hoo.1) (fun _ => hoo.2)
                . rw [List.mem_singleton] at hin2
                  subst hin2
                  exact push_agree hsz _ (Nat.le_of_eq hsz.symm)
                    (fun h1 => absurd h1 (by rw [hsz]; exact Nat.lt_irrefl _))
              . have hoo := hs.prom j y hold t htp
                exact push_agree hsz _ (Nat.le_of_lt hoo.1) (fun _ => hoo.2)
          . -- A pair promise: two words, one step.
            cases hcfg
            have hcand' : (a, v0, v1) ∈ pairPromiseCands k ta ca.mem := by
              rw [pairPromiseCands_congr k hth hs.le.mem]; exact hcand
            have hw' : w ∈ (if k.promiseViews then List.range ca.mem.size else [0]) := by
              rw [hsz]; exact hw
            have hmem :
                ({ ca with
                    mem := (ca.mem.push ⟨a, v0, w⟩).push ⟨a.next, v1, w⟩
                    pairs := ca.pairs ++ [ca.mem.size]
                    ths := ca.ths.set! i
                             { ta with
                               promises :=
                                 ta.promises ++ [ca.mem.size, ca.mem.size + 1] } } : Config)
                  ∈ promiseSteps k ca i := by
              unfold promiseSteps
              rw [ite_eq_right hk, hta]
              refine List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨(a, v0, v1), hcand', ?_⟩))
              exact List.mem_map.2 ⟨w, hw', rfl⟩
            refine ⟨_, hmem, ⟨⟨MemLe.push2 hs.le.mem rfl rfl (Nat.le_refl w) rfl rfl
              (Nat.le_refl w), ?_, ?_, ?_⟩, ?_⟩⟩
            . rw [hs.le.pairs, hsz]
            . rw [Array.size_set!, Array.size_set!]; exact hs.le.size
            . exact ths_set_le i hs.le.ths
                (promiseTh_le hth (by rw [hth.promises, hsz]))
            . intro j y hj t htp
              rcases ths_set_cases i j hj with rfl | hold
              . rcases List.mem_append.1 htp with hin1 | hin2
                . have hoo := hs.prom i tt htt t hin1
                  exact push2_agree hsz _ _
                    (Nat.le_trans (Nat.le_of_lt hoo.1) (Nat.le_succ _)) (fun _ => hoo.2)
                . have hle : t <= ca.mem.size + 1 := by
                    rcases List.mem_cons.1 hin2 with rfl | hin3
                    . rw [hsz]; exact Nat.le_succ _
                    . rw [List.mem_singleton] at hin3
                      subst hin3
                      rw [hsz]
                      exact Nat.le_refl _
                  exact push2_agree hsz _ _ hle
                    (fun h1 => absurd h1 (by
                      rcases List.mem_cons.1 hin2 with rfl | hin3
                      . rw [hsz]; exact Nat.lt_irrefl _
                      . rw [List.mem_singleton] at hin3
                        subst hin3
                        rw [hsz]
                        exact Nat.not_lt.2 (Nat.le_succ _)))
              . have hoo := hs.prom j y hold t htp
                exact push2_agree hsz _ _
                  (Nat.le_trans (Nat.le_of_lt hoo.1) (Nat.le_succ _)) (fun _ => hoo.2)

/-! ### The thread step -/

theorem fence_promises (th : Thread) (f : Fence) : (stepFence th f).promises = th.promises := by
  cases f <;> rfl

theorem fence_le {ta tt : Thread} (h : ThreadLe ta tt) (f : Fence) :
    ThreadLe (stepFence ta f) (stepFence tt f) := by
  cases f
  . exact ⟨h.prog, h.promises, h.regs, h.vs.coh, h.vs.vRd, h.vs.vWr, h.vs.vCtrl,
      le_max_le h.vs.vPreBase h.vs.vRd, h.vs.vRelSt, (by first | exact h.vs.mine | simp [h.vs.mine] | simp_all), h.vs.fwd⟩
  . exact ⟨h.prog, h.promises, h.regs, h.vs.coh, h.vs.vRd, h.vs.vWr, h.vs.vCtrl,
      h.vs.vPreBase, le_max_le h.vs.vRelSt h.vs.vWr, h.vs.mine, h.vs.fwd⟩
  . exact ⟨h.prog, h.promises, h.regs, h.vs.coh, h.vs.vRd, h.vs.vWr, h.vs.vCtrl,
      le_max_le h.vs.vPreBase (le_max_le h.vs.vRd h.vs.vWr),
      le_max_le h.vs.vRelSt (le_max_le h.vs.vRd h.vs.vWr), h.vs.mine, h.vs.fwd⟩

/-- Every rule commits through the same configuration shape, so the invariant
    is re-established once rather than seven times.  `hsub` is the only thing
    the promise half needs: a step never invents a promise. -/
theorem setTh_sim {ca ct : Config} (hs : Sim ca ct) (i : Nat) (rest : List Instr)
    {ma mt : Memory} (hm : MemLe ma mt) (hea : MemExt ca.mem ma) (het : MemExt ct.mem mt)
    {tha tht : Thread} (hth : ThreadLe tha tht)
    {th0 : Thread} (ht0 : ct.ths[i]? = some th0)
    (hsub : forall t, t ∈ tht.promises -> t ∈ th0.promises)
    {pa pt : List Ts} (hpairs : pa = pt) :
    Sim { mem := ma, ths := ca.ths.set! i { tha with prog := rest }, pairs := pa }
        { mem := mt, ths := ct.ths.set! i { tht with prog := rest }, pairs := pt } := by
  refine ⟨⟨hm, hpairs, ?_, ?_⟩, ?_⟩
  . rw [Array.size_set!, Array.size_set!]; exact hs.le.size
  . exact ths_set_le i hs.le.ths ⟨rfl, hth.promises, hth.regs, hth.vs⟩
  . intro j y hj t htp
    have hold : t < ca.mem.size ∧ ca.mem[t]? = ct.mem[t]? := by
      rcases ths_set_cases i j hj with rfl | hj'
      . exact hs.prom i th0 ht0 t (hsub t htp)
      . exact hs.prom j y hj' t htp
    refine ⟨Nat.lt_of_lt_of_le hold.1 hea.size, ?_⟩
    rw [hea.get t hold.1, het.get t (by rw [← hs.le.mem.1]; exact hold.1)]
    exact hold.2

theorem stepThread_sim (k : Knobs) {ca ct : Config} (hs : Sim ca ct) (i : Nat)
    {ct' : Config} (hin : ct' ∈ stepThread k .tso ct i) :
    ∃ ca' ∈ stepThread k .arm ca i, Sim ca' ct' := by
  unfold stepThread at hin
  split at hin
  . simp at hin
  . next tt htt =>
      obtain ⟨ta, hta, hth⟩ := ths_some hs.le htt
      have hprom : forall t, t ∈ tt.promises -> ca.mem[t]? = ct.mem[t]? :=
        fun t htp => (hs.prom i tt htt t htp).2
      split at hin
      . simp at hin
      . next ins rest hprog =>
          have hproga : ta.prog = ins :: rest := by rw [hth.prog]; exact hprog
          split at hin
          . -- load
            next dst a deps acq =>
              simp only [List.mem_map] at hin
              obtain ⟨tht, hstep, hcfg⟩ := hin
              cases hcfg
              obtain ⟨tha, hstepa, hthle⟩ :=
                stepLoad_sim hs.le.mem hth ca.pairs dst a deps acq
                  (by rw [hs.le.pairs]; exact hstep)
              have hmem :
                  ({ mem := ca.mem, ths := ca.ths.set! i { tha with prog := rest },
                     pairs := ca.pairs } : Config) ∈ stepThread k .arm ca i := by
                simp only [stepThread, hta, hproga, List.mem_map]
                exact ⟨tha, hstepa, rfl⟩
              exact ⟨_, hmem, setTh_sim hs i rest hs.le.mem (MemExt.refl _) (MemExt.refl _)
                hthle htt (stepLoad_ext .tso ct.mem ct.pairs tt dst a deps acq hstep)
                hs.le.pairs⟩
          . -- store
            next a e deps rel =>
              simp only [List.mem_map] at hin
              obtain ⟨⟨mt', tht⟩, hstep, hcfg⟩ := hin
              cases hcfg
              obtain ⟨⟨ma', tha⟩, hstepa, hmle, hthle⟩ :=
                stepStore_sim k hs.le.mem hth hprom a e deps rel hstep
              have hmem :
                  ({ mem := ma', ths := ca.ths.set! i { tha with prog := rest },
                     pairs := ca.pairs } : Config) ∈ stepThread k .arm ca i := by
                simp only [stepThread, hta, hproga, List.mem_map]
                exact ⟨(ma', tha), hstepa, rfl⟩
              exact ⟨_, hmem, setTh_sim hs i rest hmle
                (stepStore_ext k .arm ca.mem ta a e deps rel hstepa).1
                (stepStore_ext k .tso ct.mem tt a e deps rel hstep).1
                hthle htt (stepStore_ext k .tso ct.mem tt a e deps rel hstep).2 hs.le.pairs⟩
          . -- fence
            next f =>
              rw [List.mem_singleton] at hin
              cases hin
              have hmem :
                  ({ mem := ca.mem,
                     ths := ca.ths.set! i { stepFence ta f with prog := rest },
                     pairs := ca.pairs } : Config) ∈ stepThread k .arm ca i := by
                simp only [stepThread, hta, hproga, List.mem_singleton]
              exact ⟨_, hmem, setTh_sim hs i rest hs.le.mem (MemExt.refl _) (MemExt.refl _)
                (fence_le hth f) htt (fun t htp => by
                  rw [fence_promises] at htp; exact htp) hs.le.pairs⟩
          . -- branch
            next r =>
              rw [List.mem_singleton] at hin
              cases hin
              have hmem :
                  ({ mem := ca.mem,
                     ths := ca.ths.set! i
                              { ta with
                                vs := { ta.vs with
                                        vCtrl := max ta.vs.vCtrl
                                          (if k.ctrlRts then (ta.regs r).rts
                                           else (ta.regs r).view) }
                                prog := rest },
                     pairs := ca.pairs } : Config) ∈ stepThread k .arm ca i := by
                simp only [stepThread, hta, hproga, List.mem_singleton]
              have hbr :
                  ThreadLe
                    { ta with
                      vs := { ta.vs with
                              vCtrl := max ta.vs.vCtrl
                                (if k.ctrlRts then (ta.regs r).rts else (ta.regs r).view) } }
                    { tt with
                      vs := { tt.vs with
                              vCtrl := max tt.vs.vCtrl
                                (if k.ctrlRts then (tt.regs r).rts else (tt.regs r).view) } } := by
                refine ⟨hth.prog, hth.promises, hth.regs, hth.vs.coh, hth.vs.vRd,
                  hth.vs.vWr, ?_, hth.vs.vPreBase, hth.vs.vRelSt, (by first | exact hth.vs.mine | simp [hth.vs.mine] | simp_all), hth.vs.fwd⟩
                refine le_max_le hth.vs.vCtrl ?_
                cases hk : k.ctrlRts
                . exact (hth.regs r).view
                . exact Nat.le_of_eq (hth.regs r).rts
              exact ⟨_, hmem, setTh_sim hs i rest hs.le.mem (MemExt.refl _) (MemExt.refl _)
                hbr htt (fun t htp => htp) hs.le.pairs⟩
          . -- isb
            rw [List.mem_singleton] at hin
            cases hin
            have hmem :
                ({ mem := ca.mem,
                   ths := ca.ths.set! i
                            { ta with
                              vs := { ta.vs with
                                      vPreBase := max ta.vs.vPreBase ta.vs.vCtrl }
                              prog := rest },
                   pairs := ca.pairs } : Config) ∈ stepThread k .arm ca i := by
              simp only [stepThread, hta, hproga, List.mem_singleton]
            have hisb :
                ThreadLe
                  { ta with vs := { ta.vs with
                                    vPreBase := max ta.vs.vPreBase ta.vs.vCtrl } }
                  { tt with vs := { tt.vs with
                                    vPreBase := max tt.vs.vPreBase tt.vs.vCtrl } } :=
              ⟨hth.prog, hth.promises, hth.regs, hth.vs.coh, hth.vs.vRd, hth.vs.vWr,
               hth.vs.vCtrl, le_max_le hth.vs.vPreBase hth.vs.vCtrl, hth.vs.vRelSt, (by first | exact hth.vs.mine | simp [hth.vs.mine] | simp_all), hth.vs.fwd⟩
            exact ⟨_, hmem, setTh_sim hs i rest hs.le.mem (MemExt.refl _) (MemExt.refl _)
              hisb htt (fun t htp => htp) hs.le.pairs⟩
          . -- rmw
            next dst a cmp newv deps acq rel =>
              simp only [List.mem_map] at hin
              obtain ⟨⟨mt', tht⟩, hstep, hcfg⟩ := hin
              cases hcfg
              obtain ⟨⟨ma', tha⟩, hstepa, hmle, hthle⟩ :=
                stepRmw_sim k hs.le.mem hth hprom ca.pairs dst a cmp newv deps acq rel
                  (by rw [hs.le.pairs]; exact hstep)
              have hmem :
                  ({ mem := ma', ths := ca.ths.set! i { tha with prog := rest },
                     pairs := ca.pairs } : Config) ∈ stepThread k .arm ca i := by
                simp only [stepThread, hta, hproga, List.mem_map]
                exact ⟨(ma', tha), hstepa, rfl⟩
              exact ⟨_, hmem, setTh_sim hs i rest hmle
                (stepRmw_ext k .arm ca.mem ca.pairs ta dst a cmp newv deps acq rel hstepa).1
                (stepRmw_ext k .tso ct.mem ct.pairs tt dst a cmp newv deps acq rel hstep).1
                hthle htt
                (stepRmw_ext k .tso ct.mem ct.pairs tt dst a cmp newv deps acq rel hstep).2
                hs.le.pairs⟩
          . -- pair rmw
            next d0 d1 a cmp0 cmp1 new0 new1 deps acq rel =>
              simp only [List.mem_map] at hin
              obtain ⟨⟨mt', pt', tht⟩, hstep, hcfg⟩ := hin
              cases hcfg
              obtain ⟨⟨ma', pa', tha⟩, hstepa, hmle, hple, hthle⟩ :=
                stepRmwPair_sim hs.le.mem hth hprom ca.pairs d0 d1 a cmp0 cmp1 new0 new1
                  deps acq rel (by rw [hs.le.pairs]; exact hstep)
              have hmem :
                  ({ mem := ma', ths := ca.ths.set! i { tha with prog := rest },
                     pairs := pa' } : Config) ∈ stepThread k .arm ca i := by
                simp only [stepThread, hta, hproga, List.mem_map]
                exact ⟨(ma', pa', tha), hstepa, rfl⟩
              exact ⟨_, hmem, setTh_sim hs i rest hmle
                (stepRmwPair_ext .arm ca.mem ca.pairs ta d0 d1 a cmp0 cmp1 new0 new1
                  deps acq rel hstepa).1
                (stepRmwPair_ext .tso ct.mem ct.pairs tt d0 d1 a cmp0 cmp1 new0 new1
                  deps acq rel hstep).1
                hthle htt
                (stepRmwPair_ext .tso ct.mem ct.pairs tt d0 d1 a cmp0 cmp1 new0 new1
                  deps acq rel hstep).2
                hple⟩
          . -- pair store
            -- The only arm whose rule is a *function*: there is one successor,
            -- not a list of them, so there is nothing to pick and `hin` is an
            -- equation rather than a membership.  `stepStorePair_eq` is what
            -- lets the `let`-pattern in `stepThread` reduce.
            next a e0 e1 deps rel =>
              rw [stepStorePair_eq] at hin
              simp only [List.mem_singleton] at hin
              cases hin
              obtain ⟨hmle, hthle⟩ := stepStorePair_sim hs.le.mem hth a e0 e1 deps rel
              have hmem :
                  ({ mem := (ca.mem.push
                               ⟨a, storeValOf ta e0, storePairMview ta e0 e1 deps rel⟩).push
                               ⟨a.next, storeValOf ta e1, storePairMview ta e0 e1 deps rel⟩,
                     ths := ca.ths.set! i
                              { storeThOf2 ta a (pairFwdOf ta.regs e0 e1 deps) ca.mem.size
                                  (ca.mem.size + 1) ta.promises with prog := rest },
                     pairs := ca.pairs ++ [ca.mem.size] } : Config)
                    ∈ stepThread k .arm ca i := by
                simp only [stepThread, hta, hproga, stepStorePair_eq, List.mem_singleton]
              exact ⟨_, hmem, setTh_sim hs i rest hmle
                (stepStorePair_ext ca.mem ca.pairs ta a e0 e1 deps rel).1
                (stepStorePair_ext ct.mem ct.pairs tt a e0 e1 deps rel).1
                hthle htt
                (stepStorePair_ext ct.mem ct.pairs tt a e0 e1 deps rel).2
                (by rw [hs.le.pairs, hs.le.mem.1])⟩
          . -- pair load
            next d0 d1 a deps acq =>
              simp only [List.mem_map] at hin
              obtain ⟨tht, hstep, hcfg⟩ := hin
              cases hcfg
              obtain ⟨tha, hstepa, hthle⟩ :=
                stepLoadPair_sim hs.le.mem hth ca.pairs d0 d1 a deps acq
                  (by rw [hs.le.pairs]; exact hstep)
              have hmem :
                  ({ mem := ca.mem, ths := ca.ths.set! i { tha with prog := rest },
                     pairs := ca.pairs } : Config) ∈ stepThread k .arm ca i := by
                simp only [stepThread, hta, hproga, List.mem_map]
                exact ⟨tha, hstepa, rfl⟩
              exact ⟨_, hmem, setTh_sim hs i rest hs.le.mem (MemExt.refl _) (MemExt.refl _)
                hthle htt
                (stepLoadPair_ext .tso ct.mem ct.pairs tt d0 d1 a deps acq hstep)
                hs.le.pairs⟩

/-! ### The whole run

`Config.done` looks at `prog` and `promises`, both of which `ThreadLe` pins, so
it is a congruence; the rest is induction on fuel. -/

theorem done_congr {ca ct : Config} (h : ConfigLe ca ct) : ca.done = ct.done := by
  refine Bool.coe_iff_coe.mp ⟨?_, ?_⟩
  . intro hx
    unfold Config.done at hx ⊢
    rw [Array.all_eq_true] at hx ⊢
    intro i hi
    have hia : i < ca.ths.size := by rw [h.size]; exact hi
    have hle := h.ths i ca.ths[i] ct.ths[i]
      (Array.getElem?_eq_getElem hia) (Array.getElem?_eq_getElem hi)
    have hx' := hx i hia
    rw [hle.prog, hle.promises] at hx'
    exact hx'
  . intro hy
    unfold Config.done at hy ⊢
    rw [Array.all_eq_true] at hy ⊢
    intro i hi
    have hit : i < ct.ths.size := by rw [← h.size]; exact hi
    have hle := h.ths i ca.ths[i] ct.ths[i]
      (Array.getElem?_eq_getElem hi) (Array.getElem?_eq_getElem hit)
    have hy' := hy i hit
    rw [← hle.prog, ← hle.promises] at hy'
    exact hy'

theorem finals_sim (k : Knobs) (fuel : Nat) : forall {ca ct : Config}, Sim ca ct ->
    forall {ct' : Config}, ct' ∈ finals k .tso fuel ct ->
      ∃ ca' ∈ finals k .arm fuel ca, Sim ca' ct' := by
  induction fuel with
  | zero => intro ca ct hs ct' hin; simp [finals] at hin
  | succ n ih =>
      intro ca ct hs ct' hin
      rw [finals] at hin
      split at hin
      . next hdone =>
          rw [List.mem_singleton] at hin
          cases hin
          refine ⟨ca, ?_, hs⟩
          rw [finals, ite_eq_left (by rw [done_congr hs.le]; exact hdone)]
          exact List.mem_singleton.2 rfl
      . next hdone =>
          simp only [List.mem_flatMap, List.mem_range, List.mem_append] at hin
          obtain ⟨i, hi, c2, hstep, hrec⟩ := hin
          have hgoal : forall (c2a : Config), c2a ∈ stepThread k .arm ca i ++ promiseSteps k ca i ->
              forall (ca' : Config), ca' ∈ finals k .arm n c2a -> ca' ∈ finals k .arm (n + 1) ca := by
            intro c2a hc2a ca' hca'
            rw [finals, ite_eq_right (by rw [done_congr hs.le]; exact hdone)]
            refine List.mem_flatMap.2 ⟨i, List.mem_range.2 ?_, ?_⟩
            . rw [hs.le.size]; exact hi
            . exact List.mem_flatMap.2 ⟨c2a, hc2a, hca'⟩
          rcases hstep with hst | hpr
          . obtain ⟨c2a, hmem2, hs2⟩ := stepThread_sim k hs i hst
            obtain ⟨ca', hmema, hsa⟩ := ih hs2 hrec
            exact ⟨ca', hgoal c2a (List.mem_append.2 (Or.inl hmem2)) ca' hmema, hsa⟩
          . obtain ⟨c2a, hmem2, hs2⟩ := promiseSteps_sim k hs i hpr
            obtain ⟨ca', hmema, hsa⟩ := ih hs2 hrec
            exact ⟨ca', hgoal c2a (List.mem_append.2 (Or.inr hmem2)) ca' hmema, hsa⟩

/-! ### The outcome

`Litmus.obs` reads registers and locations.  `TValLe` pins register *values*
and `MemLe` pins memory values, so related final configurations produce the
same observation either way.  That turns the executable containment table of
§4.1 into a theorem.

The memory half is the one that was not designed for: `MemLe`'s "same values"
clause was written because it is what makes the *register* outcomes
comparable — a load reads a message's `val` — and it turns out to say exactly
what `memNat` needs without being touched.  That is the payoff for having
stated the relation on memory rather than on what the threads ended up
holding. -/

theorem regNat_congr {ca ct : Config} (h : ConfigLe ca ct) (i : Nat) (r : Reg) :
    regNat ca.ths[i]! r = regNat ct.ths[i]! r := by
  rcases Nat.lt_or_ge i ct.ths.size with hi | hi
  . have hia : i < ca.ths.size := by rw [h.size]; exact hi
    have hle := h.ths i ca.ths[i] ct.ths[i]
      (Array.getElem?_eq_getElem hia) (Array.getElem?_eq_getElem hi)
    rw [getElem!_pos ca.ths i hia, getElem!_pos ct.ths i hi]
    unfold regNat
    rw [(hle.regs r).val]
  . have hia : ¬ (i < ca.ths.size) := by rw [h.size]; exact Nat.not_lt.2 hi
    rw [getElem!_neg ca.ths i hia, getElem!_neg ct.ths i (Nat.not_lt.2 hi)]

/-- The fold inside `memNat`, on two lists that agree on `loc` and `val`
    position by position.  Stated over lists rather than arrays because that is
    the shape induction wants, and generalised over the accumulator because the
    step case changes it. -/
theorem memNat_fold_congr (a : Address) : ∀ (la lt : List Msg),
    la.length = lt.length →
    (∀ (i : Nat) (m n : Msg), la[i]? = some m → lt[i]? = some n →
      m.loc = n.loc ∧ m.val = n.val) →
    ∀ (acc : Option Val),
      la.foldl (fun acc m => if m.loc = a then some m.val else acc) acc =
      lt.foldl (fun acc m => if m.loc = a then some m.val else acc) acc
  | [], [], _, _, _ => rfl
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | m :: la, n :: lt, hlen, hpt, acc => by
      have hhd : m.loc = n.loc ∧ m.val = n.val := hpt 0 m n rfl rfl
      have hlen' : la.length = lt.length := by simpa using hlen
      have hpt' : ∀ (i : Nat) (p q : Msg), la[i]? = some p → lt[i]? = some q →
          p.loc = q.loc ∧ p.val = q.val := by
        intro i p q hp hq
        exact hpt (i + 1) p q (by simpa using hp) (by simpa using hq)
      simp only [List.foldl_cons, hhd.1, hhd.2]
      exact memNat_fold_congr a la lt hlen' hpt' _

theorem memNat_congr {ca ct : Config} (h : ConfigLe ca ct) (a : Address) :
    memNat ca.mem a = memNat ct.mem a := by
  obtain ⟨hsize, hpt⟩ := h.mem
  have hlen : ca.mem.toList.length = ct.mem.toList.length := by
    simpa using hsize
  have hpt' : ∀ (i : Nat) (m n : Msg),
      ca.mem.toList[i]? = some m → ct.mem.toList[i]? = some n →
      m.loc = n.loc ∧ m.val = n.val := by
    intro i m n hm hn
    obtain ⟨hl, hv, _⟩ := hpt i m n (by simpa using hm) (by simpa using hn)
    exact ⟨hl, hv⟩
  have key :
      ca.mem.foldl (fun (acc : Option Val) (m : Msg) =>
                      if m.loc = a then some m.val else acc) none =
      ct.mem.foldl (fun (acc : Option Val) (m : Msg) =>
                      if m.loc = a then some m.val else acc) none := by
    rw [← Array.foldl_toList, ← Array.foldl_toList]
    exact memNat_fold_congr a _ _ hlen hpt' none
  simp only [memNat, key]

theorem obsNat_congr {ca ct : Config} (h : ConfigLe ca ct) (q : Obs) :
    obsNat ca q = obsNat ct q := by
  cases q with
  | reg i r => exact regNat_congr h i r
  | mem a => exact memNat_congr h a

theorem sim_start (L : Litmus) : Sim (start L) (start L) := by
  refine ⟨⟨MemLe.refl _, rfl, rfl, ?_⟩, ?_⟩
  . intro i ta tt h1 h2
    rw [h1] at h2
    cases h2
    exact ThreadLe.refl ta
  . intro i tt hi t htp
    exfalso
    have hmem := Array.mem_of_getElem? hi
    simp only [start, List.mem_toArray, List.mem_map] at hmem
    obtain ⟨q, _, hq⟩ := hmem
    rw [← hq] at htp
    simp [Thread.mk'] at htp

/-- Membership in the deduplicating fold is membership in the list. -/
theorem mem_dedup {alpha : Type} [BEq alpha] [LawfulBEq alpha] (x : alpha) :
    forall (l acc : List alpha),
      (x ∈ l.foldl (fun acc y => if acc.contains y then acc else acc ++ [y]) acc)
        ↔ (x ∈ acc ∨ x ∈ l) := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons y ys ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hc : acc.contains y = true
      . rw [ite_eq_left hc]
        constructor
        . intro h
          rcases h with h | h
          . exact Or.inl h
          . exact Or.inr (List.mem_cons.2 (Or.inr h))
        . intro h
          rcases h with h | h
          . exact Or.inl h
          . rcases List.mem_cons.1 h with rfl | h'
            . exact Or.inl (List.mem_of_elem_eq_true hc)
            . exact Or.inr h'
      . rw [ite_eq_right hc]
        constructor
        . intro h
          rcases h with h | h
          . rcases List.mem_append.1 h with h' | h'
            . exact Or.inl h'
            . rw [List.mem_singleton] at h'
              exact Or.inr (List.mem_cons.2 (Or.inl h'))
          . exact Or.inr (List.mem_cons.2 (Or.inr h))
        . intro h
          rcases h with h | h
          . exact Or.inl (List.mem_append.2 (Or.inl h))
          . rcases List.mem_cons.1 h with rfl | h'
            . exact Or.inl (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))
            . exact Or.inr h'

/-- **Every TSO outcome is an ARM outcome.**  §4.1 checks this by running both
    machines over the suite; this proves it for every program. -/
theorem tso_outcomes_subset_arm (k : Knobs) (L : Litmus) {o : List Nat}
    (ho : o ∈ outcomesOf k { L with arch := .tso }) :
    o ∈ outcomesOf k { L with arch := .arm } := by
  simp only [outcomesOf] at ho ⊢
  rw [mem_dedup] at ho ⊢
  rcases ho with h | ho
  . simp at h
  refine Or.inr ?_
  simp only [List.mem_map] at ho ⊢
  obtain ⟨ct', hct', hobs⟩ := ho
  obtain ⟨ca', hca', hsim⟩ := finals_sim k 64 (sim_start { L with arch := .tso }) hct'
  refine ⟨ca', hca', ?_⟩
  rw [← hobs]
  refine List.map_congr_left ?_
  intro q _
  exact obsNat_congr hsim.le q

end Sim

-- The gate reads the line this prints: the simulation must rest on Lean's own
-- axioms and on nothing else, in particular not on `sorryAx`.
#print axioms Sim.tso_outcomes_subset_arm


/-! ## 17. The synchronised cell (`Sync`): what "must be derived" costs

> **Renamed**.  This section called the structure
> `Loc` and the object a *locative*.
> The language then gave "locative" its reference-flavour meaning
> (allocation + offset, `CoreLang.Ty.loc`), so the lock-word-plus-payload cell
> here is `Sync`, as in the language, and its predicates and theorems are
> `Sync*` / `sync_*`.

§6's ladder has three rows.  One word is a primitive, two adjacent words are a
primitive (`casPair`, §6.11, after the detour that section records), and three
or more "must be derived".  This section builds the third row and then measures
what the derivation costs, because the cost is not visible in the table and is
the only part of the ladder that is not obvious.

### The layout

A `Sync` cell is one allocation holding a lock word and `width` payload words,
with the lock at offset 0.  Putting the lock *inside* the object rather than
beside it is not tidiness.  `lock_protects_data` (§11.2) needs the protected
address to differ from the lock word, and takes `a ≠ lk` as a hypothesis for
the caller to discharge; here the same fact is `Sync.word_ne_lock`, a theorem
about offsets.  The companion `Sync.word_inj` says distinct indices are distinct
cells.  Those two lemmas are the whole of the layout.

### The theorem

`sync_write_is_atomic` is the first **width-generic** protection result in
this file: for any `width`, a writer that takes the lock installs every word,
and afterwards every word still holds what it wrote.  The environment runs
*between every pair of stores* -- uncontrolled, as in §6.8's `copy`, which is
why the adversary is part of the program rather than wrapped around it -- and
the conclusion is `LatestIs` at each word, which is coherence-latest and so
rules out a remote write landing after ours rather than merely alongside it.
It concludes two further things, `SyncFrozen` and `SyncReleased`, which name the
*timestamps* rather than only the values; they are there for the reader, and
"The protocol, as two statements about memory" below says what they are.

Three things about it.

**It needed nothing about allocation.**  No bounds hypothesis, no `allocated`:
`LatestIs` is a statement about memory, and a store appends whether or not it
is in bounds (it sets `stuck`, which this theorem does not mention).  A
`Sync` cell whose payload runs off the end of its allocation is still updated
atomically; it is just also broken, and the two are kept separate.

**It needed one new clause in §11.2**, and the reason generalises.  Every store
in the critical section wants `StorePost.append`, whose hypothesis is that the
promise list is empty, so the loop invariant has to carry `promises = []`
*through the environment step*.  `LockedEnvPost` said nothing about promises
and neither did `RcasPost`, so the induction died at the first iteration.  Both
gained a `promises` clause, both `rfl`.  This is the same shape of gap as
`LoadPost.rd` in §11.3: a `*Post` is only as strong as the first client that
needed each clause, and a loop is a client that needs everything to compose
with itself.

**It needed no `Nodup` argument**, which is worth recording because the obvious
proof does.  Preserving "every word written so far still holds its value"
across one more store looks like it requires knowing the new index differs from
the old ones.  It does not: case on whether the two *addresses* are equal, and
if they are, the message just pushed is the one the goal is asking for.  The
uniqueness of loop indices never enters.

### What the derivation costs

The ladder says 3+ words must be derived.  `syncLadderDemo` shows what that
buys and what it does not, in three rows that differ only in how the update is
made and who is watching:

  * the naive lock-free attempt -- `casPair` on two words, `cas` on the third --
    exposes the intermediate `(1,1,7)` to an observer reading in between;
  * the derived version exposes **the same tuple** to an observer that ignores
    the lock;
  * and excludes only the observer that runs the protocol.

The middle row is the point, and printing the identical tuple is what makes it
land.  A primitive is atomic against *everybody*, including an observer that
has never heard of it; a lock is atomic only against *participants*.  That
asymmetry is the real content of the ladder's third row, and the table does not
show it.

`syncSnapshotDemo` is the same claim from the reader's side: a reader
holding the lock sees `(7,7,7)` while the environment is trying to write, and
the same reader without the lock sees `(7,0,0)`.

That reader side is now proved as well, by `sync_read_is_a_snapshot` below,
so the demo is that theorem's *control* rather than a substitute for it: the
unlocked row is what shows the protection is not coming from somewhere else.
And the two theorems compose, with one exception: what the writer concludes
about the state it leaves is character for character what the reader assumes
about memory, which is `sync_snapshot_after_write`.  The exception is that the
reader also assumes `hfwd : s₀.vs.fwd = []`, a forwarding-free state, which is
false after any plain `mstore` by that agent, `lwrite` included (every plain
store records a forwarding entry).  So for a same-agent round trip the writer's
conclusion no longer meets the reader's hypotheses as stated; generalising
`hfwd` to "no `fwd` entry at `L`'s words" is future work. -/

/-- A synchronised cell: one allocation holding a lock word and `width` payload words. -/
structure Sync where
  base  : Address
  width : Nat
  deriving Repr, DecidableEq, Inhabited

def Sync.lock (L : Sync) : Address := L.base

def Sync.word (L : Sync) (i : Nat) : Address :=
  ⟨L.base.label, L.base.offset + i + 1⟩

/-- **The lock cannot be mistaken for payload.**  `lock_protects_data` took
    `a ≠ lk` as a hypothesis; putting the lock inside the object turns it into
    arithmetic on offsets.

    `omega` is no use here -- `Offset` is an `abbrev` for `Nat`, and §7 records
    that `omega` cannot see atoms declared at an abbrev. -/
theorem Sync.word_ne_lock (L : Sync) (i : Nat) : L.word i ≠ L.lock := by
  intro h
  have h2 : L.base.offset + i + 1 = L.base.offset := congrArg Address.offset h
  have hlt : L.base.offset < L.base.offset + i + 1 :=
    Nat.lt_succ_of_le (Nat.le_add_right _ _)
  rw [h2] at hlt
  exact Nat.lt_irrefl _ hlt

/-- And distinct indices are distinct cells. -/
theorem Sync.word_inj (L : Sync) {i j : Nat} (h : L.word i = L.word j) : i = j := by
  have h2 : L.base.offset + i + 1 = L.base.offset + j + 1 := congrArg Address.offset h
  exact Nat.add_left_cancel (Nat.add_right_cancel h2)

/-! ### The protocol, as two statements about memory

Before either side of the lock is written down, here is what the lock *means*.
Both predicates are about the memory array alone: no thread, no view state, no
program.  That is deliberate, and it is what lets the writer's conclusion be
the reader's hypothesis without either theorem mentioning the other's code. -/

/-- The memory-side half of a snapshot: word `i` holds `v i` at timestamp
    `N i`, and nothing above `N i` is at that word. -/
structure SyncFrozen (s : Machine) (L : Sync) (v : Nat → Val) (N : Nat → Ts) :
    Prop where
  msg  : ∀ i, i < L.width → ∃ mv, s.mem[N i]? = some ⟨L.word i, v i, mv⟩
  froz : ∀ i, i < L.width → ∀ (t' : Ts) (m' : Msg),
           s.mem[t']? = some m' → m'.loc = L.word i → t' ≤ N i

/-- **The previous holder released after writing.**  The coherence-latest
    message at the lock word carries a view covering every payload timestamp.

    A statement about memory only: it mentions no thread and no view state, so
    a reader can be handed it by whoever last released, and the reader's own
    `vPreBase` does not appear. -/
def SyncReleased (s : Machine) (L : Sync) (N : Nat → Ts) : Prop :=
  ∀ (t : Ts) (m : Msg), s.mem[t]? = some m → m.loc = L.lock →
    betweenAt s.mem L.lock t s.mem.size = false →
    ∀ i, i < L.width → N i ≤ m.view

/-- `SyncFrozen`'s two fields are `LatestIs`, unfolded: a message at `N`, and
    nothing at that address above it.  Naming the timestamp is strictly more
    information, which is why the writer's invariant carries `N` and recovers
    `LatestIs` here rather than the other way round. -/
theorem latestIs_of_frozen {mem : Memory} {a : Address} {w : Val} {N : Ts}
    {m : Msg} (hN : mem[N]? = some m) (hloc : m.loc = a) (hval : m.val = w)
    (hfroz : ∀ (t' : Ts) (m' : Msg), mem[t']? = some m' → m'.loc = a → t' ≤ N) :
    LatestIs mem a w := by
  refine ⟨N, m, hN, hloc, hval, ?_⟩
  rw [betweenAt, List.any_eq_false]
  intro t' _
  rcases hm' : mem[t']? with _ | m'
  · simp
  · by_cases hla : m'.loc = a
    · have hle := hfroz t' m' hm' hla
      simp [hla, Nat.not_lt.2 hle]
    · simp [hla]

/-- **A releasing store publishes everything this thread has written.**  This
    is the one arithmetic fact behind `SyncReleased`: `mstoreView … true` takes
    the max with `vWr`, so the view it leaves at the lock word is above every
    timestamp this thread wrote.  The plain store's view (`rel := false`) is
    not, which is the whole difference between `STR` and `STLR`. -/
theorem mstoreView_ge_vWr (s : Machine) (deps : List TVal) :
    s.vs.vWr ≤ mstoreView s deps true := by
  show s.vs.vWr ≤ max (max s.vs.vRelSt (max s.vs.vRd s.vs.vWr)) (tvView deps)
  exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (Nat.le_max_left _ _)

/-- Update the whole cell under its own lock, with a protocol-respecting
    environment running between every pair of stores.

    The adversary is *in* the program, as in §6.8's `copy`, and for the same
    reason: an interleaving written around the operation only tests the states
    the caller chose to expose.  Its store index varies with the iteration, so
    it attempts a different write each time round. -/
def lwrite (L : Sync) (v : Nat → Val) (lkra ra : RAddr) : M Bool := do
  let got ← acquire L.lock
  if got then
    for i in List.range L.width do
      mstore (L.word i) (v i)
      renvLocked lkra ra i
    release L.lock
  pure got

/-- **A multi-word update is atomic, for any width, and it publishes.**  If the
    lock was taken, every word of the cell holds what this critical section
    wrote -- no remote write landed after any of them -- even though the
    environment ran between every pair of stores.

    The last two conjuncts are what make this the reader's theorem too.
    `SyncFrozen` names the timestamps `LatestIs` only quantifies over, and
    `SyncReleased` says the message the release left at the lock word carries a
    view above all of them.  Together they are, verbatim, the memory
    hypotheses of `sync_read_is_a_snapshot`; that theorem also needs
    `hfwd : s₀.vs.fwd = []`, which is false after any plain `mstore` by the
    same agent, `lwrite` included.

    Carrying them costs one strengthened loop invariant and nothing else.  The
    invariant holds an `N j` for each word written so far, plus the
    *arithmetic* fact `mem.size ≤ vWr + 1` -- one store's worth of slack,
    because `StorePost.append` gives `s₀.mem.size ≤ s.vs.vWr` after the push
    rather than a monotonicity clause for `vWr`.  That slack is exactly enough:
    at the release every payload timestamp is below `mem.size`, hence at most
    `vWr`, and `mstoreView … true` dominates `vWr`. -/
theorem sync_write_is_atomic (L : Sync) (v : Nat → Val) (lkra ra : RAddr)
    (s₀ : Machine) (hlk : lkra.addr = L.lock) (hp : s₀.promises = []) :
    ⦃fun s => ⌜s = s₀⌝⦄
    lwrite L v lkra ra
    ⦃⇓ got s => ⌜got = true →
        (∀ i, i < L.width → LatestIs s.mem (L.word i) (v i)) ∧
        s.promises = [] ∧
        ∃ N, SyncFrozen s L v N ∧ SyncReleased s L N⌝⦄ := by
  mvcgen [lwrite, acquire, release]
  case inv1 =>
    exact ⇓ ⟨c, _⟩ s => ⌜∃ N : Nat → Ts,
      s.promises = [] ∧
      LatestIs s.mem L.lock (Val.num 1) ∧
      s.mem.size ≤ s.vs.vWr + 1 ∧
      ∀ j ∈ c.«prefix»,
        (∃ mv, s.mem[N j]? = some ⟨L.word j, v j, mv⟩) ∧
        (∀ (t' : Ts) (m' : Msg), s.mem[t']? = some m' → m'.loc = L.word j →
           t' ≤ N j)⌝
  -- One iteration: the protected store, then an uncontrolled environment step.
  · rename_i sA hA r sB hcas jp hgot pref cur suff hsplit b s1 hinv u1 s2 hstore u2 s3 henv
    obtain ⟨N, hprom, hlock, hvw, hwords⟩ := hinv
    obtain ⟨hmem, _, hprom2, hvw2⟩ := hstore.append hprom
    have hlock2 : LatestIs s2.mem L.lock (Val.num 1) := by
      rw [hmem]; exact latestIs_push_ne _ (L.word_ne_lock cur) hlock
    -- **The environment did nothing at all**, because it cannot take the lock.
    have hm3 : s3.mem = s2.mem := henv.quiet (by rw [hlk]; exact hlock2)
    have hsz : s2.mem.size = s1.mem.size + 1 := by rw [hmem]; simp
    -- The word just written gets the slot the store appended to; the rest keep
    -- the timestamps they already had.
    refine ⟨fun j => if j = cur then s1.mem.size else N j, ?_, ?_, ?_, ?_⟩
    · rw [henv.promises]; exact hprom2
    · rw [hm3]; exact hlock2
    · rw [hm3, henv.vs, hsz]; omega
    · intro j hj
      dsimp only
      -- No `Nodup` argument is needed, and that is not an accident: if `j` were
      -- somehow `cur`, the message just pushed is the one the goal asks for.
      by_cases he : j = cur
      · subst he
        rw [ite_eq_left rfl]
        refine ⟨⟨mstoreView s1 [] false, ?_⟩, ?_⟩
        · rw [hm3, hmem]; simp
        · intro t' m' hm' hloc'
          rw [hm3, hmem] at hm'
          have hlt := lt_size_of_getElem? hm'
          rw [Array.size_push] at hlt
          exact Nat.lt_succ_iff.mp hlt
      · have hjp : j ∈ pref := by
          rcases List.mem_append.1 hj with h | h
          · exact h
          · exact absurd (List.mem_singleton.1 h) he
        obtain ⟨⟨mv, hj1⟩, hj2⟩ := hwords j hjp
        have hNlt : N j < s1.mem.size := lt_size_of_getElem? hj1
        rw [ite_eq_right he]
        refine ⟨⟨mv, ?_⟩, ?_⟩
        · rw [hm3, hmem, Array.getElem?_push, ite_eq_right (Nat.ne_of_lt hNlt)]
          exact hj1
        · intro t' m' hm' hloc'
          rw [hm3, hmem, Array.getElem?_push] at hm'
          split at hm'
          · exfalso
            have hm'' : m' = ⟨L.word cur, v cur, mstoreView s1 [] false⟩ :=
              (Option.some.inj hm').symm
            rw [hm''] at hloc'
            exact he (L.word_inj (by simpa using hloc')).symm
          · exact hj2 t' m' hm' hloc'
  -- Entry: the acquire appended `1` to the lock word, and nothing is written yet.
  · rename_i sA hA r sB hcas jp hgot
    subst hA
    obtain ⟨⟨mv, hmem⟩, _, hprom, hvw, _⟩ := hcas.append hgot hp
    refine ⟨fun _ => 0, hprom, by rw [hmem]; exact latestIs_push _ _ _ _, ?_, ?_⟩
    · rw [hmem]; simp only [Array.size_push]; omega
    · intro j hj; simp at hj
  -- Exit: the release is a store to the lock, and the lock is not a payload
  -- word, so every word still holds what the critical section put there -- and
  -- the message the release pushes is the one `SyncReleased` talks about.
  · rename_i sA hA r sB hcas jp hgot b s1 hinv u s2 hrel
    obtain ⟨N, hprom, _, hvw, hwords⟩ := hinv
    intro _
    obtain ⟨hmemF, _, hpromF, _⟩ := hrel.append hprom
    have hword : ∀ i, i < L.width →
        (∃ mv, s2.mem[N i]? = some ⟨L.word i, v i, mv⟩) ∧
        (∀ (t' : Ts) (m' : Msg), s2.mem[t']? = some m' → m'.loc = L.word i →
           t' ≤ N i) := by
      intro i hi
      obtain ⟨⟨mv, h1⟩, h2⟩ := hwords i (List.mem_range.2 hi)
      have hNlt : N i < s1.mem.size := lt_size_of_getElem? h1
      refine ⟨⟨mv, ?_⟩, ?_⟩
      · rw [hmemF, Array.getElem?_push, ite_eq_right (Nat.ne_of_lt hNlt)]; exact h1
      · intro t' m' hm' hloc'
        rw [hmemF, Array.getElem?_push] at hm'
        split at hm'
        · exfalso
          have hm'' : m' = ⟨L.lock, Val.num 0, mstoreView s1 [] true⟩ :=
            (Option.some.inj hm').symm
          rw [hm''] at hloc'
          exact absurd (by simpa using hloc'.symm) (L.word_ne_lock i)
        · exact h2 t' m' hm' hloc'
    refine ⟨?_, hpromF, N, ⟨fun i hi => (hword i hi).1, fun i hi => (hword i hi).2⟩, ?_⟩
    · intro i hi
      obtain ⟨⟨mv, h1⟩, h2⟩ := hword i hi
      exact latestIs_of_frozen h1 rfl rfl h2
    · -- Coherence-latest at the lock word is *unique*, so whatever message a
      -- consumer of `SyncReleased` produces is the one the release just pushed.
      intro t m hm hloc hbet i hi
      have hm0 : s2.mem[s1.mem.size]? =
          some ⟨L.lock, Val.num 0, mstoreView s1 [] true⟩ := by
        rw [hmemF]; simp
      have hb0 : betweenAt s2.mem L.lock s1.mem.size s2.mem.size = false := by
        rw [hmemF]; exact betweenAt_push_top _ _ _
      have ht : s1.mem.size = t := latest_unique hm0 rfl hb0 hm hloc hbet
      rw [← ht] at hm
      have hmv : m = ⟨L.lock, Val.num 0, mstoreView s1 [] true⟩ :=
        (Option.some.inj (hm0.symm.trans hm)).symm
      obtain ⟨⟨mv, h1⟩, _⟩ := hwords i (List.mem_range.2 hi)
      have hNlt : N i < s1.mem.size := lt_size_of_getElem? h1
      have h3 : N i ≤ s1.vs.vWr := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hNlt hvw)
      rw [hmv]
      exact Nat.le_trans h3 (mstoreView_ge_vWr s1 [])
  -- The acquire failed: the conclusion is guarded by `got = true`.
  · rename_i sA hA r sB hcas jp hnot
    intro h
    exact absurd h hnot

/-! ### The reader

The writer's theorem says nobody else's write landed after ours.  That is not
the same as saying a reader sees a consistent snapshot, and the two need
different arguments: exclusion is about *memory*, and a snapshot is about the
reader's *bound*.  A reader that holds the lock still has to explain why its
loads may not take an older message at each word, and coherence alone does not
supply that -- a fresh thread's views are all zero.

### The two hypotheses, and why they are the right two

`SyncFrozen` is the memory-side half: each word `i` holds `v i` at timestamp
`N i`, and nothing above `N i` is at that word.  This is what "the writer has
finished and nobody else may write" looks like as a statement about memory, and
it is the direct generalisation of §8's `publication_chain.top`.

`SyncReleased` is the ordering half, and it is the interesting one.  It says the
*coherence-latest message at the lock word* carries a view that covers every
`N i`.  That is exactly what a releasing store leaves behind -- `mstoreView`
with `rel := true` is `max (max vRelSt (max vRd vWr)) …`, and `StorePost.append`
puts every payload timestamp under `vWr` -- so the hypothesis is not an
assumption about the reader at all.  It is a statement about what the previous
holder did before it let go.

Stating it that way is what keeps the theorem honest.  The tempting alternative
is to assume `N i ≤ s.vs.vPreBase` directly, which is also enough; but that
assumes the reader *already had* the barrier, and then the acquire does no work
and the theorem proves nothing about locks.  Here the reader starts with
`vPreBase` wherever it happened to be -- zero, for a thread that has done
nothing -- and `CasPost.acqv` is what moves it.

### What the loop carries

The invariant is one disjunction:

    s.stuck = true ∨ (the lock is held ∧ SyncSnapshot ∧ acc = prefix.map v)

`SyncSnapshot` is `SyncFrozen` plus `N i ≤ s.vs.vPreBase`: the memory half
survives because the environment cannot write, and the bound half survives
because `LoadPost.pre` and `LockedEnvPost.vs` cannot lower `vPreBase`.  The
accumulator is stated as `acc = c.prefix.map v` rather than as a length plus a
pointwise claim, which is what avoids having to prove `cur = pref.length` from
the loop's `range = pref ++ cur :: suff`.

The `stuck` disjunct is not decoration.  `CasPost.read` and `LoadPost.read`
both begin with "…or the run is stuck", and an oracle that picked a nonexistent
successor has not exhibited a behaviour of the program; the disjunct is how
that excuse is inherited, and `RcasPost.stuck`, `LockedEnvPost.stuck` and
`LoadPost.stuck` are what let it survive a whole iteration.

### Where the two hypotheses come from

From the writer.  `sync_write_is_atomic` concludes `∃ N, SyncFrozen ∧
SyncReleased` about the state it leaves behind, which is exactly what this
theorem assumes about memory in the state it starts in, and
`sync_snapshot_after_write` below is that composition written out.  So those
hypotheses are not this theorem's price: they are the previous holder's
receipt.

The third hypothesis, `hfwd : s₀.vs.fwd = []`, is not: it says the reader's
agent has no plain write of its own to be forwarded, and it is false after any
plain `mstore` by that agent, `lwrite` included.  So the writer's
postcondition is no longer literally the reader's precondition for a
same-agent round trip; generalising `hfwd` to "no `fwd` entry at `L`'s words"
is future work. -/

/-- What the reader carries through its loop: the memory half, plus the bound
    that the acquire bought. -/
structure SyncSnapshot (s : Machine) (L : Sync) (v : Nat → Val) (N : Nat → Ts) :
    Prop extends SyncFrozen s L v N where
  cover : ∀ i, i < L.width → N i ≤ s.vs.vPreBase

/-- Read the whole cell under its own lock, with the same
    protocol-respecting environment `lwrite` runs against, between every pair
    of loads. -/
def lread (L : Sync) (lkra ra : RAddr) : M (Bool × List Val) := do
  let got ← acquire L.lock
  if got then
    let mut acc : List Val := []
    for i in List.range L.width do
      let r ← mload (L.word i)
      acc := acc ++ [r.val]
      renvLocked lkra ra i
    release L.lock
    pure (got, acc)
  else
    pure (got, [])

/-- **A multi-word read under the lock is a snapshot, for any width.**  If the
    lock was taken, the reader returns exactly the `width` values the previous
    holder left -- no tearing, no word read from an older message -- even
    though the environment ran between every pair of loads.

    The reader-side companion to `sync_write_is_atomic`, and the clause
    that does the work is `CasPost.acqv`: without it the reader's bound never
    reaches the payload and the second disjunct of `LoadPost.read` cannot be
    ruled out. -/
theorem sync_read_is_a_snapshot (L : Sync) (v : Nat → Val) (N : Nat → Ts)
    (lkra ra : RAddr) (s₀ : Machine)
    (hlk : lkra.addr = L.lock) (hp : s₀.promises = [])
    (hfwd : s₀.vs.fwd = [])
    (hfrz : SyncFrozen s₀ L v N) (hrel : SyncReleased s₀ L N) :
    ⦃fun s => ⌜s = s₀⌝⦄
    lread L lkra ra
    ⦃⇓ res s => ⌜res.1 = true → s.stuck = true ∨
        (res.2.length = L.width ∧ ∀ i, i < L.width → res.2[i]! = v i)⌝⦄ := by
  mvcgen [lread, acquire, release]
  case inv1 =>
    exact ⇓ ⟨c, acc⟩ s => ⌜s.stuck = true ∨
      (LatestIs s.mem L.lock (Val.num 1) ∧ SyncSnapshot s L v N ∧
       acc = c.«prefix».map v)⌝
  -- One iteration: the protected load, then an uncontrolled environment step.
  · rename_i pref cur suff hsplit b s2 hinv r1 accL s1 hload u s3 henv
    simp +zetaDelta only []
    rcases hinv with hst | ⟨hlock, hsn, hb⟩
    · exact Or.inl (by rw [henv.stuck]; exact hload.stuck hst)
    have hcurlt : cur < L.width :=
      List.mem_range.1 (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_self ..))
    -- **The environment did nothing at all**, because it cannot take the lock.
    have hlock1 : LatestIs s1.mem L.lock (Val.num 1) := by rw [hload.mem]; exact hlock
    have hmem3 : s3.mem = s2.mem := by
      rw [henv.quiet (by rw [hlk]; exact hlock1), hload.mem]
    obtain ⟨mv, hN⟩ := hsn.msg cur hcurlt
    have hfr := hsn.froz cur hcurlt
    rcases hload.read with hstuck | ⟨_, hnone⟩ | ⟨hmsg, hr⟩
    · exact Or.inl (by rw [henv.stuck]; exact hstuck)
    · -- The word is frozen at a live message, so something *is* readable and
      -- the load's "nothing to read" case cannot have happened.  This is what
      -- `readable_top_of_frozen` exists for.
      exfalso
      have hcontra := hnone (N cur)
      rw [readable_top_of_frozen hN rfl hfr] at hcontra
      simp at hcontra
    · right
      -- And the bound reaches `N cur`, so it is the *only* readable timestamp.
      have hb2 : N cur ≤ loadBound s2 (L.word cur) [] :=
        Nat.le_trans (hsn.cover cur hcurlt) (vPreBase_le_loadBound _ _ _)
      have ht := readable_eq_of_frozen hN rfl hb2 hfr hr
      rw [ht, hN] at hmsg
      simp only [Option.some.injEq, Msg.mk.injEq] at hmsg
      refine ⟨by rw [hmem3]; exact hlock, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [hmem3]; exact hsn.msg
      · rw [hmem3]; exact hsn.froz
      · intro i hi
        rw [henv.vs]
        exact Nat.le_trans (hsn.cover i hi) hload.pre
      · rw [hb, List.map_append, ← hmsg.2.1]
        rfl
  -- Entry: the acquire appended `1` to the lock word, and -- the point of the
  -- whole section -- inherited the view the previous holder released with.
  · rename_i sA hA r sB hcas hgot accL
    subst hA
    obtain ⟨⟨mv, hmem⟩, _, _, _, hbet⟩ := hcas.append hgot hp
    -- The reader has no plain write of its own to be forwarded (`hfwd`), so
    -- the acquire takes the view of the message it read.
    have hnf : ownFwd sA.vs r.1.rts = none := by simp [ownFwd, hfwd]
    rcases hcas.read with hstuck | ⟨_, hfalse, _⟩ | ⟨_, hna⟩ | ⟨hmsg, _⟩
    · exact Or.inl hstuck
    · exfalso; rw [hfalse] at hgot; simp at hgot
    · exact absurd hna (by decide)
    · right
      refine ⟨by rw [hmem]; exact latestIs_push _ _ _ _, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
      · intro i hi
        obtain ⟨mv', h⟩ := hfrz.msg i hi
        refine ⟨mv', ?_⟩
        rw [hmem, Array.getElem?_push,
          ite_eq_right (Nat.ne_of_lt (lt_size_of_getElem? h))]
        exact h
      · intro i hi t' m' hm' hloc'
        rw [hmem, Array.getElem?_push] at hm'
        split at hm'
        · -- The message just pushed is the lock word, which is never payload.
          have hm'' : m' = ⟨L.lock, Val.num 1, mv⟩ := (Option.some.inj hm').symm
          rw [hm''] at hloc'
          exact absurd (by simpa using hloc'.symm) (L.word_ne_lock i)
        · exact hfrz.froz i hi t' m' hm' hloc'
      · -- `SyncReleased` names the view; `CasPost.acqv` is what puts it into
        -- this thread's `vPreBase`.  `CasPost.append` supplies the missing
        -- link: what a successful RMW read was coherence-latest.
        intro i hi
        exact Nat.le_trans (hrel r.1.rts _ hmsg rfl (hbet rfl) i hi) (hcas.acqv rfl hnf)
  -- Exit: the release is a store, and the only thing it can do to the answer
  -- is get stuck.
  · rename_i racc s1 hinv u s2 hstore
    intro _
    rcases hinv with hst | ⟨_, _, hb⟩
    · exact Or.inl (by rw [hstore.stuck, hst]; rfl)
    · right
      subst hb
      exact ⟨by simp, fun i hi => by simp [hi]⟩
  -- The acquire failed: the conclusion is guarded by `got = true`.
  · rename_i hnot
    intro h
    exact absurd h hnot

/-- **The writer's postcondition is the reader's precondition.**  Nothing is
    proved here that was not proved above; the content is that the hypothesis
    is the `∃ N, SyncFrozen ∧ SyncReleased` conjunct of `sync_write_is_atomic`
    copied out character for character.

    That is what it means for the link to be closed.  Neither theorem mentions
    the other's program, and neither mentions a thread: the writer leaves a
    fact about *memory* behind, the reader picks it up, and the lock word is
    the only channel between them.  A second cell, or a second writer, or
    a reader on a machine that has never run `lwrite`, all compose the same
    way -- which they would not if the link were a claim about one particular
    run.

    What is still not one *program* is the round trip: chaining these under
    `mvcgen` as a single `do` block would need the intermediate `N` as a ghost,
    and `@[spec]` matching leaves it an unconstrained metavariable.  See §0.4. -/
theorem sync_snapshot_after_write (L : Sync) (v : Nat → Val) (lkra ra : RAddr)
    (s₀ : Machine) (hlk : lkra.addr = L.lock) (hp : s₀.promises = [])
    (hfwd : s₀.vs.fwd = [])
    (hpub : ∃ N, SyncFrozen s₀ L v N ∧ SyncReleased s₀ L N) :
    ⦃fun s => ⌜s = s₀⌝⦄
    lread L lkra ra
    ⦃⇓ res s => ⌜res.1 = true → s.stuck = true ∨
        (res.2.length = L.width ∧ ∀ i, i < L.width → res.2[i]! = v i)⌝⦄ := by
  obtain ⟨N, hfrz, hrel⟩ := hpub
  exact sync_read_is_a_snapshot L v N lkra ra s₀ hlk hp hfwd hfrz hrel

-- Read the compiler, not the report.  §16 explains the reasoning: a `sorry` is
-- not a runtime behaviour, so nothing the measurements print could reveal one,
-- and these are the only lines that can.  `check-promises.sh` item 25 asserts
-- both that they appear and that `sorryAx` is not in them.
#print axioms sync_write_is_atomic
#print axioms sync_read_is_a_snapshot

/-! ### The measurements -/

/-- A remote agent that runs the protocol and then updates every word.  §11.2's
    `renvLocked` writes one address; a torn *read* needs an adversary that
    writes more than one. -/
def renvLockedAll (lk : RAddr) (ras : List RAddr) : M Unit := do
  let got ← rcas lk (Val.num 0) (Val.num 1)
  if got then
    for ra in ras do
      rstore ra 0

def syncBase : Address := ⟨0, 0⟩

/-- Three payload words: past the pair primitive, which is the point. -/
def sync3 : Sync := ⟨syncBase, 3⟩

def locStart (oracle : List Nat) : Machine :=
  { mem := #[⟨sync3.lock, Val.num 0, 0⟩,
             ⟨sync3.word 0, Val.num 7, 0⟩,
             ⟨sync3.word 1, Val.num 7, 0⟩,
             ⟨sync3.word 2, Val.num 7, 0⟩],
    sizes := [4],
    roots := [syncBase],
    rknow := [⟨sync3.lock, 0⟩, ⟨sync3.word 0, 0⟩, ⟨sync3.word 1, 0⟩, ⟨sync3.word 2, 0⟩],
    oracle := oracle }

def locShowVals (l : List Val) : String :=
  "(" ++ String.intercalate "," (l.map fun v => match v with
    | .num n => toString n
    | .undef => "undef"
    | .null => "null"
    | .loc a _ => s!"&{a.label}.{a.offset}") ++ ")"

/-- The reader's side.  The remote agent takes the lock and rewrites all three
    words in the middle of the local read. -/
def syncSnapshotScenario (readerLocks : Bool) : String :=
  let s0 := locStart [0, 9, 0, 9, 9, 9]
  let prog : M (Bool × List Val) := do
    let got ← if readerLocks then acquire sync3.lock
              else do let _ ← mload sync3.lock; pure true
    let a ← mload (sync3.word 0)
    renvLockedAll ⟨sync3.lock, 0⟩ [⟨sync3.word 0, 0⟩, ⟨sync3.word 1, 0⟩, ⟨sync3.word 2, 0⟩]
    let b ← mload (sync3.word 1)
    let c ← mload (sync3.word 2)
    pure (got, [a.val, b.val, c.val])
  let ((got, vs), s) := prog.run s0
  s!"reader-locks={readerLocks}: acquired={got}, read={locShowVals vs}, stuck={s.stuck}"

def syncSnapshotDemo : String :=
  "  " ++ syncSnapshotScenario false ++ "\n  " ++ syncSnapshotScenario true

/-- How a three-word update is made, and who is watching. -/
inductive SyncWay where
  /-- The naive lock-free attempt: `CASP` on two words, `CAS` on the third. -/
  | pairThenCas
  /-- The derived version, with an observer that ignores the lock. -/
  | lockUnaware
  /-- The derived version, with an observer that runs the protocol. -/
  | lockAware
  deriving Repr, DecidableEq

def SyncWay.str : SyncWay → String
  | .pairThenCas => "casPair+cas  "
  | .lockUnaware => "lock, unaware"
  | .lockAware   => "lock, aware  "

/-- Local updates all three words from 7 to 1; the observer reads all three in
    the middle.  `casPair` covers words 0 and 1, so the naive version's window
    is between the pair and the single. -/
def syncLadderScenario (w : SyncWay) : String :=
  let s0 := locStart [0, 9, 9, 9, 9, 9, 9, 9, 9]
  let obs : M (List Val) := do
    let m0 ← rload ⟨sync3.word 0, 0⟩
    let m1 ← rload ⟨sync3.word 1, 0⟩
    let m2 ← rload ⟨sync3.word 2, 0⟩
    pure [(m0.map Msg.val).getD .undef, (m1.map Msg.val).getD .undef,
          (m2.map Msg.val).getD .undef]
  let prog : M (String × List Val) := do
    match w with
    | .pairThenCas => do
        let _ ← mcasPair (sync3.word 0) (Val.num 7) (Val.num 7) (Val.num 1) (Val.num 1)
        let seen ← obs
        let _ ← mcas (sync3.word 2) (Val.num 7) (Val.num 1)
        pure ("read", seen)
    | .lockUnaware => do
        let _ ← acquire sync3.lock
        mstore (sync3.word 0) (Val.num 1)
        mstore (sync3.word 1) (Val.num 1)
        let seen ← obs
        mstore (sync3.word 2) (Val.num 1)
        release sync3.lock
        pure ("read", seen)
    | .lockAware => do
        let _ ← acquire sync3.lock
        mstore (sync3.word 0) (Val.num 1)
        mstore (sync3.word 1) (Val.num 1)
        let got ← rcas ⟨sync3.lock, 0⟩ (Val.num 0) (Val.num 1)
        let seen ← if got then obs else pure []
        mstore (sync3.word 2) (Val.num 1)
        release sync3.lock
        pure (if got then "read" else "blocked", seen)
  let ((how, vs), _) := prog.run s0
  s!"{w.str}: observer {how}" ++ (if how = "read" then s!" {locShowVals vs}" else "")

def syncLadderDemo : String :=
  "  " ++ syncLadderScenario .pairThenCas ++
  "\n  " ++ syncLadderScenario .lockUnaware ++
  "\n  " ++ syncLadderScenario .lockAware

/-! ## 18. Null, and why it is not an address

It was settled that the language has a nullable pointer `Ptr? μ τ`,
and left the model an obligation it could not discharge.  `null` has to be a
value; `Val` had three constructors and it could be none of them.  `num 0` is
the tempting one and is exactly the one that must not be used: if `null` is
`num 0` then `Int → Ptr` exists by the back door, and the guarantee that a
pointer can only come from an allocation -- the thing the whole type system is
being built to say -- is gone before it is stated.

§6.3 recommended trying a **reserved `AllocLabel`** first, on the grounds that a
fourth `Val` constructor would be disruptive because `Val` is matched on in both
model files.  That estimate was checkable in one command and was wrong.  The
development contains **six** exhaustive `Val` case splits: three one-liners in
proofs and three display helpers.  Every other match already ends in a wildcard,
and every one of those wildcards wants the null case to go the way it already
goes.

The six is worth more than the four the one command reported, and not because
the number is bigger.  The sweep looked at the two *model* files, which is what
§6.3's objection was about, and so it missed `valStr` here and `valStr` in
`Tutorial.lean` -- the second of which only surfaced when `check-promises.sh`
got past `Promises.lean` and reached the tutorial.  So the estimate was
corrected twice, both times by the exhaustiveness checker rather than by
re-reading.  That is the actual argument for the constructor: a missed site is
a **compile error**, where a missed site under the reserved-label design is a
`Val.loc` that quietly flows into `Reaches`.  The cost of being wrong about the
count is bounded by the type checker, and the cost of being wrong about the
merits is not.

The reserved label is also worse on the merits, and that is the part worth
keeping.  It would make `null` a `Val.loc`, and then every site that asks "is
this a pointer?" would have to ask a second question:

* `Reaches.ptr` would follow it, so the reachable set would contain a label
  nothing allocated, and `fresh_unreachable` would need an exception;
* `rlearnedOf` would hand the reader a dereferenceable `RAddr`, so a null chase
  would take a step and *then* get stuck, rather than stopping;
* `reaches_push_nonptr`'s hypothesis `∀ b g, v ≠ Val.loc b g` would stop holding of
  a value that points nowhere, which is backwards.

A constructor gets all three right by construction.  The general form, which is
worth carrying into `CoreLang.lean`: **a sentinel placed inside a datatype must
be excluded again at every use of that datatype; a sentinel placed beside them
is excluded once, by the type.**

The other thing `null` must not be is `undef`, and that one is not obvious --
both are non-pointers, both stop a chase, and a language could plausibly spell
the empty optional with the poison value.  It cannot, and `nullPublishDemo`
below is why: `undef` is the value §5's headline theorem forbids a thread from
observing, and a program that publishes an empty optional has to be allowed to
publish it.  Collapsing the two would make `published_read_is_initialised`
false of a correct program. -/

/-- The point of the constructor, three times over.  Trivial by
    `noConfusion` -- which is the argument for the constructor: at a reserved
    address none of these three would be provable, and the second one would be
    *false*. -/
theorem null_ne_num (n : Nat) : Val.null ≠ Val.num n := fun h => Val.noConfusion h

theorem null_ne_loc (a : Address) (g : Nat) : Val.null ≠ Val.loc a g := fun h => Val.noConfusion h

theorem null_ne_undef : Val.null ≠ Val.undef := fun h => Val.noConfusion h

/-- **Publishing null exposes nothing.**  A corollary of `reaches_push_nonptr`
    with the hypothesis discharged rather than assumed, which is the whole
    saving: at a reserved address this statement would need the label to be
    excluded from `Reaches` by hand, and here it needs nothing.

    This is the model-side content of the language's claim that nulling a
    popped slot is safe: the slot stops pointing at the popped element without
    the store making anything newly reachable. -/
theorem reaches_push_null {s s' : Machine} {a : Address} {w : Ts}
    (hroots : s'.roots = s.roots) (hmem : s'.mem = s.mem.push ⟨a, Val.null, w⟩)
    {l : AllocLabel} (h : Reaches s' l) : Reaches s l :=
  reaches_push_nonptr hroots hmem (fun _ _ hb => Val.noConfusion hb) h

/-- **A chase through null stops**, and stops without taking a step.  `rlearnedOf`
    is the single rule both the ordering theorems (§12) and the knowledge
    theorems (§7) go through, so this one equation is what keeps a null link out
    of both. -/
theorem no_deref_through_null (ra : RAddr) (m : Msg) (h : m.val = Val.null) :
    rlearnedOf ra m = none := by
  unfold rlearnedOf; rw [h]

/-- **Writing null initialises the cell.**  An instance of
    `load_reads_own_write`, and it needs no proof at all because that theorem
    quantifies over `Val`: the spec layer never looks inside a value, so a new
    constructor costs it nothing.  Stated anyway, because the language
    leans on it -- `Vec.pop` nulls the vacated slot and must leave `init`
    where it was. -/
theorem null_store_is_a_store (a : Address) :
    ⦃fun s => ⌜s.promises = [] ∧ s.stuck = false⌝⦄
    (do mstore a Val.null; mload a : M TVal)
    ⦃⇓ r s => ⌜s.stuck = true ∨ r.val = Val.null⌝⦄ :=
  load_reads_own_write a Val.null

/-! ### The measurements -/

/-- One link, four things the root could hold.  The machine literal is §8's,
    with the payload already in place and the *root* varied instead; the
    mechanism is shared rather than copied, since the chase goes through the
    same `rderefChain`. -/
def nullChaseScenario (link : Val) : String :=
  let root : Address := ⟨0, 0⟩
  let data : Address := ⟨1, 0⟩
  let s0 : Machine :=
    { mem := #[⟨data, Val.num 7, 0⟩, ⟨root, link, 0⟩],
      sizes := [1, 1],
      roots := [root], rknow := [⟨root, 0⟩],
      oracle := [0, 0, 0, 0] }
  let (r, s) := (rderefChain ⟨root, 0⟩).run s0
  let derefd := match r with | some m => valStr m.val | none => "stopped"
  s!"root holds {valStr link}: deref {derefd}, stuck={s.stuck}"

def nullChaseDemo : String :=
  "  " ++ nullChaseScenario (Val.loc ⟨1, 0⟩ 0) ++
  "\n  " ++ nullChaseScenario Val.null ++
  "\n  " ++ nullChaseScenario (Val.num 0) ++
  "\n  " ++ nullChaseScenario Val.undef

/-- §8's publication scenario with a **null payload**.  Same program, same
    oracle, same adversary; only the value being published differs from the
    `num 7` row §8 prints. -/
def nullPublishScenario (fenced : Bool) : String :=
  let root : Address := ⟨0, 0⟩
  let data : Address := ⟨1, 0⟩
  let s0 : Machine :=
    { mem := #[⟨data, Val.undef, 0⟩, ⟨root, Val.num 0, 0⟩],
      sizes := [1, 1],
      roots := [root], rknow := [⟨root, 0⟩],
      oracle := [0, 0, 1, 0] }
  let (r, s) :=
    (do publishVia root data Val.null fenced
        rderefChain ⟨root, 0⟩ : M (Option Msg)).run s0
  let derefd := match r with | some m => valStr m.val | none => "nothing"
  let sawUndef := s.rreads.any fun v => match v with | .undef => true | _ => false
  s!"fenced={fenced}: deref-read={derefd}, saw-undef={sawUndef}"

def nullPublishDemo : String :=
  "  " ++ nullPublishScenario false ++ "\n  " ++ nullPublishScenario true

/-- Printed section by section, and timed.

    State-space exploration dominates the runtime here and the sections differ
    by two orders of magnitude, so a single `#eval` of one big `String` is
    indistinguishable from a hang while it works, and a regression has nowhere
    to show up but the total.

    Lean is lazy, so each clock is read *after* the `println` that consumes the
    section rather than after the `let` that names it: binding a section costs
    nothing, and timing the binding reports 0 ms for work that takes minutes. -/
def reportIO : IO Unit := do
  let emit (label : String) (f : Unit → String) : IO Unit := do
    let t0 ← IO.monoMsNow
    IO.println s!"\n=== {label} ==="
    IO.println (f ())
    let t1 ← IO.monoMsNow
    IO.println s!"    [{t1 - t0} ms]"
  let t0 ← IO.monoMsNow
  let base := pass {}
  let (body, bad) := suiteReport base
  IO.println "=== promise machine: in-order issue + early writes ===\n"
  IO.println body
  IO.println s!"\n{suite.length} tests, {bad} failing"
  let t1 ← IO.monoMsNow
  IO.println s!"    [{t1 - t0} ms]"
  emit "ablations (each must break something)" (fun _ => ablation)
  emit "generality checks (each must change nothing)" (fun _ => generality base)
  emit "tso ⊆ arm (§4.1: none may escape, and not all may agree)"
    (fun _ => containmentReport)
  emit ("certification (§4.2: must change no state set, must prune, " ++
        "must leave nothing stuck)")
    (fun _ => certReport base)
  emit "promise candidate exactness" (fun _ => regStoreReport)
  emit "do-notation front-end (§5) + spec layer (§6)" (fun _ => "  " ++ coherenceDemo ++
    "\n  mstore_spec / mload_spec / mfence_spec : proved (compile-time)" ++
    "\n  load_reads_own_write : proved from specs, nothing unfolded" ++
    "\n  publish_orders_data_before_flag : 3 ops chained, nothing unfolded")
  emit "Remote (§7)" (fun _ => remoteDemo ++
    "\n  renv_spec : proved (compile-time)" ++
    "\n  private_stays_private / private_unreachable : proved across 2 env steps")
  emit "safe publication (§8)" (fun _ => publicationDemo ++
    "\n  the unfenced row is the counterexample: same memory, same oracle," ++
    "\n  same reader -- only the dmb ishst differs, and without it Remote" ++
    "\n  dereferences the published pointer and reads undef." ++
    "\n  published_read_is_initialised : proved (compile-time), fenced case")
  emit "ownership transfer (§9, prototype)" (fun _ => ownershipDemo ++
    "\n  the unowned row is the counterexample: Remote overwrites the" ++
    "\n  address between the store and the load, so the load is not" ++
    "\n  deterministic.  rdisowned is an ASSUMPTION, not a mechanism." ++
    "\n  owned_load_reads_own_write : proved (compile-time), across 2 renv steps")
  emit "ownership transfer, composed (§9.1)" (fun _ => transferDemo ++
    "\n  the unowned row is the counterexample: the same published object," ++
    "\n  the same acquiring read, the same oracle -- and Remote clobbers it" ++
    "\n  between the receiver's two reads." ++
    "\n  transferred_read_is_stable : proved (compile-time); publication (§8)" ++
    "\n  and ownership (§9) composed over one program, with 2 uncontrolled" ++
    "\n  environment steps after the handoff")
  emit "allocation and a loop (§10)" (fun _ => allocDemo ++
    "\n  undef is a value: an allocated cell nobody wrote reads as undef and" ++
    "\n  does not get stuck; only a load outside every allocation does." ++
    "\n  unwritten_of_no_readable : proved -- an empty candidate list means the" ++
    "\n  cell was never written by anyone, at every bound, which is why the" ++
    "\n  undef result may carry view 0 and timestamp 0" ++
    "\n" ++ storeBoundsDemo ++
    "\n  the store checks bounds unconditionally, because it has no branch on" ++
    "\n  which nothing happens -- so the bad write is recorded as well as" ++
    "\n  flagged.  row 3 is why that is sound: reading back the cell the bad" ++
    "\n  store created takes the load's unchecked branch, and the run is still" ++
    "\n  stuck, because stuck is sticky." ++
    "\n" ++ copyDemo ++
    "\n  the published row is the counterexample: same oracle, same adversary," ++
    "\n  same copy -- only the destination differs, and Remote finds the one" ++
    "\n  the root points at." ++
    "\n  fresh_unreachable : proved; label freshness is a theorem, not an axiom" ++
    "\n  copy_stays_private : proved (compile-time) -- a for-loop with an" ++
    "\n  invariant, and an uncontrolled environment step in the body" ++
    "\n" ++ copyValuesDemo ++
    "\n  both rows copy the same buffer; they differ in the source's history." ++
    "\n  row 2 clobbers src[0] after it has been read, so two messages with" ++
    "\n  different values sit at that cell and no v describes the memory --" ++
    "\n  which is exactly the frozen-source hypothesis failing." ++
    "\n  copy_copies_something : proved (compile-time) -- unconditional; every" ++
    "\n  word of the buffer was at the address it came from when it was read" ++
    "\n  copy_is_exact : proved -- a 10-line corollary, not a second induction;" ++
    "\n  §9's rdisowned and §11.2's lock are the two ways to buy its antecedent")
  emit "read-modify-write (§11)" (fun _ => casDemo ++
    "\n  the plain row is the counterexample: the same memory and the same" ++
    "\n  oracle, and load-check-store takes a lock somebody else is holding." ++
    "\n  the stale timestamp is still readable to the CAS -- it just yields no" ++
    "\n  outcome, because a write after it would not be adjacent." ++
    "\n  casOutcomes_nil : proved -- an RMW never runs out of write slots," ++
    "\n  so an empty outcome list really does mean nothing was readable" ++
    "\n  mcas_spec : proved (compile-time); CasPost.append carries atomicity" ++
    "\n  in the form an exclusion argument needs it")
  emit "a lock, derived (§11.1)" (fun _ => lockDemo ++
    "\n  the free row is the control: Remote's first attempt succeeds, so the" ++
    "\n  exclusion theorem is not satisfied by a CAS that never takes anything." ++
    "\n  its second attempt fails, so exclusion is a property of the operation" ++
    "\n  and not a privilege of the local agent." ++
    "\n  lock_is_exclusive : proved (compile-time) -- once the local acquire" ++
    "\n  succeeds, both remote attempts fail, and nothing is assumed about the" ++
    "\n  environment except that it runs the same protocol.  This is what" ++
    "\n  §9's rdisowned was standing in for.")
  emit "what the lock protects (§11.2)" (fun _ => protectDemo ++
    "\n  the first row is the counterexample, and it is a one-instruction" ++
    "\n  difference: local reads the lock instead of winning it.  Same" ++
    "\n  environment, same oracle, same store -- and Remote takes the lock and" ++
    "\n  clobbers the data between the store and the load." ++
    "\n  lock_protects_data : proved (compile-time) -- owned_load_reads_own_write" ++
    "\n  with the assumption discharged.  rdisowned does not appear: the" ++
    "\n  environment is stopped because it cannot take the lock, which is a" ++
    "\n  theorem, not a rely condition.")
  emit "the seqlock (§11.3)" (fun _ => seqlockDemo ++
    "\n  no exclusion anywhere: the writer takes nothing the reader respects" ++
    "\n  and the reader takes nothing at all, so the guarantee is detection." ++
    "\n  both fences are load-bearing, and each row drops exactly one." ++
    "\n  row 1: without the reader's dmb ishld it accepts a counter it read" ++
    "\n  from before the transaction opened, while holding data from inside." ++
    "\n  row 2: without the writer's dmb ishst the data word carries no view," ++
    "\n  so the reader's load absorbs nothing, its fence has nothing to" ++
    "\n  promote, and its validating read is free to take the stale counter." ++
    "\n  seqlock_validation_detects : proved (compile-time) -- writer = Local" ++
    "\n  because only Local's stores are subject to promises, which is what" ++
    "\n  makes its store-store fence something the model may claim" ++
    "\n" ++ seqlockPromiseDemo ++
    "\n  the writer's data store, promised: landing before the counter store" ++
    "\n  with nothing executed out of order.  the two rows read the same" ++
    "\n  message on the same oracle and tear identically -- the fence changes" ++
    "\n  nothing a reader can see.  what it changes is whether the promise can" ++
    "\n  be kept: after dmb ishst the store publishes more than the promise" ++
    "\n  did, so it cannot take that timestamp (no_fulfil_after_release_fence)," ++
    "\n  appends instead, and leaves the promise outstanding.  rule 3 of §2.3" ++
    "\n  then discards the run, which is the whole of the fence's effect and is" ++
    "\n  invisible without the behaviour column." ++
    "\n  fenced_writer_cannot_discharge : proved (compile-time) -- the row" ++
    "\n  above is one oracle and two addresses; the theorem is every oracle," ++
    "\n  any two distinct addresses and any value.  it needed StorePost.keep," ++
    "\n  which is what lets a proof say a promise *survived* a store, and" ++
    "\n  PromisePost, without which a promise could only appear in an #eval.")
  emit "the two-word compare-and-swap (§11.4)" (fun _ => casPairDemo ++
    "\n  the plain row is the counterexample, and it is the one a lock cannot" ++
    "\n  fix by being atomic harder: two single-word CASes are each atomic and" ++
    "\n  the pair still tears, because neither says anything about the other." ++
    "\n  both rows fail their compare on purpose -- a *winning* CAS cannot read" ++
    "\n  stale, so tearing is only visible on the failing path, which is also" ++
    "\n  where herd7's C-read-tear probe found it." ++
    "\n  row 2 lists every snapshot the pair CAS admits rather than running it" ++
    "\n  once, so the claim is that the torn pair is unavailable and not merely" ++
    "\n  that the oracle passed it over." ++
    "\n  pairStraddles_latest : proved -- the two coherence-latest messages are" ++
    "\n  never a torn snapshot, which is what makes the next one true" ++
    "\n  casPairOutcomes_nil : proved -- neither the straddle filter nor the" ++
    "\n  doubled adjacency test can empty the outcome list on its own" ++
    "\n  mcasPair_spec : proved (compile-time); CasPairPost.append carries" ++
    "\n  atomicity at both words, and registers the pair so later readers are" ++
    "\n  held to the snapshot it created")
  emit "pointer chasing (§12)" (fun _ => chaseDemo ++
    "\n  rows 1 and 2 are the writer's fence: with it the reader walks all" ++
    "\n  three links and reads the payload; without it it gets the right" ++
    "\n  pointer out of the root and then undef from the very first node." ++
    "\n  rows 2 and 3 are why a reader-side barrier is not an alternative:" ++
    "\n  dmb ishld before every load changes nothing, because without the" ++
    "\n  writer's fence the messages carry no view and there is nothing to" ++
    "\n  promote.  rows 1 and 4 are the claim: the reader's barrier is" ++
    "\n  redundant when the writer did its job, because the address" ++
    "\n  dependency already supplied the ordering it would have supplied." ++
    "\n  one writer fence covers the whole structure, not one per node." ++
    "\n  chased_reads_are_published : proved (compile-time) -- any depth, no" ++
    "\n  reader barrier; the third conclusion says the traversal stops only" ++
    "\n  at a real end of list, so the safety property is not vacuous" ++
    "\n  chase_after_publication : proved -- one line; PubTop.addr and" ++
    "\n  PubTop.view are already exactly what the traversal wants")
  emit "a growable array (§13)" (fun _ => vecDemo ++
    "\n  rows 1-3 are the live prefix: the values survived two reallocations" ++
    "\n  and two copies, starting from a vector with no capacity at all." ++
    "\n  rows 4 and 5 are the capacity/length split, and nothing tells them" ++
    "\n  apart but the allocation table: inside the buffer and unwritten reads" ++
    "\n  undef and is fine, one word further on is stuck.  §6.8 said an" ++
    "\n  allocation rule without bounds could not distinguish these." ++
    "\n  rows 6 and 7 are the control: the same loop with vpush's growth test" ++
    "\n  deleted, and the third push into a capacity-2 buffer gets stuck --" ++
    "\n  so the store's bounds check does bite." ++
    "\n  vpushes_never_stick : proved (compile-time) -- any list of pushes" ++
    "\n  from a fresh vector; and len = xs.length, so it is not satisfied by" ++
    "\n  a push that discards its argument" ++
    "\n  copy_stays_clean : proved -- §10's copy given the bounds theorem it" ++
    "\n  was missing; LoadPost.clean and the new sizes clauses are what it" ++
    "\n  needed, and EnvPost.sizes is where the allocator is declared local")
  emit "per-location protocols (§14)" (fun _ => protoDemo ++
    "\n  the two rows are the same publication program, and what is being" ++
    "\n  checked is the *protocol's* knowledge clause rather than what Remote" ++
    "\n  read: `knows` says the descriptor's initialising write sits at or" ++
    "\n  below the view the root's message carries.  Without the writer's" ++
    "\n  dmb ishst the root's message carries view 0 and the init write is at" ++
    "\n  timestamp 2, so the clause is false -- the fence is exactly what the" ++
    "\n  protocol is buying, which is what §6.5 claims in prose" ++
    "\n  proto_of_load : proved -- reading a governed location yields the" ++
    "\n  protocol's knowledge; not tagged @[spec], so it competes with" ++
    "\n  nothing at mload's ~40 call sites" ++
    "\n  governs_mono / governs_of_store_other / governs_of_store_at : proved" ++
    "\n  -- preservation, split into old messages (Stable) and new ones (the" ++
    "\n  writer's obligation).  Publishing is proving." ++
    "\n  pubProto_stable, pub_hides_stale, pub_load : proved -- RCU as a" ++
    "\n  Proto; coherence turns the lower bound into an exclusion" ++
    "\n  badProto_not_stable : proved -- the *universal* phrasing of knows is" ++
    "\n  refutably unstable, so the existential form was necessary and not" ++
    "\n  merely convenient.  Two-message witness, no ordering involved." ++
    "\n\n  the protocol under interference:\n" ++ protoEnvDemo ++
    "\n  same publication, then one environment step, with the oracle taking" ++
    "\n  the worst option available to it: write at the root, and write a" ++
    "\n  pointer rather than null.  With the root disowned the write is" ++
    "\n  dropped and the protocol survives; without it Remote lands `loc root`" ++
    "\n  at the root and even `wf` fails.  So ownership is what the first row" ++
    "\n  is resting on, not luck." ++
    "\n  governs_of_env_rely / _other / _unreachable / _disowned : proved --" ++
    "\n  a protocol survives an arbitrary Remote step by any of three routes," ++
    "\n  two of them free from clauses EnvPost already carries.  No rely" ++
    "\n  parameterisation of Stable was needed: what an environment step" ++
    "\n  threatens is new messages, not knowledge already carried." ++
    "\n  governs_not_free_of_extends : proved -- and the write-exclusion is" ++
    "\n  load-bearing; Extends alone does not preserve Governs, even for a" ++
    "\n  protocol that is stable." ++
    "\n  pub_load_under_env : proved -- the RCU reader keeps its ordering" ++
    "\n  across arbitrary interference, with no hypothesis about the" ++
    "\n  descriptor at all" ++
    "\n\n  composing two protocols, to pin rather than bound:\n" ++ pinDemo ++
    "\n  the root protocol supplies ordering, a second protocol at the" ++
    "\n  descriptor supplies exclusion, and the dereference returns the" ++
    "\n  published value.  the second row overwrites the descriptor after" ++
    "\n  publishing, and hypothesis and conclusion fail together -- settled" ++
    "\n  is himm, deref is the pin -- which is what makes it this" ++
    "\n  hypothesis and not some other that is responsible." ++
    "\n  the naive descriptor protocol, plain immutability at every" ++
    "\n  timestamp, is *not* what works: it is false wherever the" ++
    "\n  pre-initialisation message exists, which is exactly the state RCU" ++
    "\n  is hard in, so it assumes the bug away.  hence GovernsFrom and a" ++
    "\n  floor at the publishing write." ++
    "\n  deref_pins / pub_deref_pins : proved -- the three LoadPost cases" ++
    "\n  are discharged by different hypotheses, and the undef case needs" ++
    "\n  only *existence* of the write, not ordering; the ordering is spent" ++
    "\n  entirely on excluding the stale message" ++
    "\n  governsFrom_of_env_disowned : proved -- the floor-indexed form" ++
    "\n  survives interference too, so the composition inherits it")
  emit "architecture refinement (§15)" (fun _ => refineDemo ++
    "\n  the first row is why there is anything to prove: at a state that has" ++
    "\n  already read, tso's read bound is strictly larger, so the two rule" ++
    "\n  sets genuinely differ and the monotonicity lemmas are not identities." ++
    "\n  the second row is why the refinement cannot be identity on states:" ++
    "\n  a fence moves vPreBase, and lockFence gives a tso RMW a fence the arm" ++
    "\n  one does not take.  ThreadLe_of_fence_right absorbs it -- tso only has" ++
    "\n  to stay above, not to be matched step for step." ++
    "\n  hiddenFrom_antitone / readable_antitone : proved -- the one lemma" ++
    "\n  everything rests on; a smaller bound hides fewer writes, so arm's" ++
    "\n  readable set contains tso's" ++
    "\n  readBoundOf_arm_le_tso / storeOb_arm_le_tso / storeMview_mono :" ++
    "\n  proved -- one per architecture-taking def, plus the two the" ++
    "\n  simulation will cite: arm_reads_what_tso_reads and" ++
    "\n  arm_fulfils_what_tso_fulfils" ++
    "\n  storeMview takes no Arch argument at all, which discharges the" ++
    "\n  counterexample the design note flagged: publication is" ++
    "\n  architecture-blind, and the architecture only ever moves bounds" ++
    "\n  the simulation itself (step 3) is §16, and it is proved: see the" ++
    "\n  '#print axioms' line the build emits for tso_outcomes_subset_arm." ++
    "\n  that check reads the compiler rather than this report, because a" ++
    "\n  sorry is not a runtime behaviour and nothing printed here could" ++
    "\n  reveal one (check-promises.sh item 22)")
  emit "the synchronised cell (§17)" (fun _ => syncLadderDemo ++
    "\n  the first two rows print the same tuple, and that is the finding:" ++
    "\n  to an observer that is not running the protocol, the derived" ++
    "\n  three-word update is worth exactly as much as the naive one.  a" ++
    "\n  primitive is atomic against everybody; a lock is atomic only" ++
    "\n  against participants, which is what the ladder's third row costs" ++
    "\n  and what its table does not show." ++
    "\n" ++ syncSnapshotDemo ++
    "\n  the reader's side of the same point: holding the lock is what" ++
    "\n  turns three loads into a snapshot." ++
    "\n  sync_write_is_atomic : proved -- for any width, with the" ++
    "\n  environment running between every pair of stores.  it concludes" ++
    "\n  SyncFrozen and SyncReleased, which are verbatim the memory" ++
    "\n  hypotheses of" ++
    "\n  sync_read_is_a_snapshot : proved -- likewise for the reader," ++
    "\n  and the demo above is now its control rather than its substitute." ++
    "\n  sync_snapshot_after_write is that composition, spelled out, with" ++
    "\n  one more hypothesis: hfwd (the reader's fwd list is empty), which" ++
    "\n  is false after any plain mstore by that agent, lwrite included;" ++
    "\n  so the writer's postcondition is no longer literally the reader's" ++
    "\n  precondition for a same-agent round trip; generalising hfwd to" ++
    "\n  no fwd entry at the cell's words is future work." ++
    "\n  what carries the ordering is CasPost.acqv: the acquiring CAS pulls" ++
    "\n  the view the previous holder released with into vPreBase, which is" ++
    "\n  what puts the payload timestamps under the reader's load bound.")
  emit "null (§18)" (fun _ => nullChaseDemo ++
    "\n  row 1 is the only one that dereferences.  the other three are the" ++
    "\n  claim that a fourth constructor added no fourth way to move a view:" ++
    "\n  null stops the chase exactly where a number or an undef stops it," ++
    "\n  and stops it in rlearnedOf, before a step is taken." ++
    "\n  null_ne_num / null_ne_loc / null_ne_undef : proved -- by noConfusion," ++
    "\n  which is the argument for the constructor rather than a reserved" ++
    "\n  address: at a reserved AllocLabel the second of the three is *false*." ++
    "\n  reaches_push_null : proved -- publishing null exposes nothing, with" ++
    "\n  reaches_push_nonptr's hypothesis discharged instead of assumed" ++
    "\n  no_deref_through_null : proved -- one equation, and it is the equation" ++
    "\n  both §7's knowledge theorems and §12's ordering theorems go through" ++
    "\n  null_store_is_a_store : proved, by instantiation and nothing else --" ++
    "\n  load_reads_own_write quantifies over Val, so the spec layer never" ++
    "\n  looked inside a value and a new constructor costs it nothing" ++
    "\n" ++ nullPublishDemo ++
    "\n  the rows above are §8's publication with a null payload, and they are" ++
    "\n  the control for the decision that null is not undef.  the fenced row" ++
    "\n  reads null and saw-undef=false: a program may publish an empty" ++
    "\n  optional and its reader observes a value, not poison.  the unfenced" ++
    "\n  row reads undef, which is the same counterexample §8 prints." ++
    "\n  spell null as undef and those two rows collapse -- and with them" ++
    "\n  published_read_is_initialised, which would become false of a correct" ++
    "\n  program rather than a theorem about an incorrect one.")

end Promises

/- The driver lives in `Report.lean` so that this file can be compiled to an
   olean once and then queried a table at a time.  `#eval` isolates stdout until
   the command finishes, so a single all-sections eval is indistinguishable from
   a hang; splitting the driver out is what makes a slow section attributable. -/

