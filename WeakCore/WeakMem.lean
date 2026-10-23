/-
Weak memory, stage 1: executable core model + litmus harness.

Targets: ARMv8-A and x86-TSO, both other-multi-copy-atomic.  One rule set,
selected by `Arch`; TSO is ARM with three orderings put back (see `Arch`).

The model is view-based, in the style of Promising-ARM/RISC-V (Pulte,
Pichon-Pharabod, Kang, Lee, Hur; PLDI 2019).  Memory is a single global
append-only array of messages; the array index *is* the timestamp, and
per-location coherence order is timestamp order restricted to that location.

Relaxed behaviour comes from two places, and it is worth keeping them straight:

  * the *reader* side -- per-location coherence views plus views inherited from
    messages -- which is what makes fences, dependencies and acquire/release do
    their work; and
  * *out-of-order issue*, which lets an agent execute an access before an
    earlier independent one.  This is what LB needs and the views cannot
    provide.

Nothing here is a program-logic proof.  The point of stage 1 is to get the
transition rules litmus-validated before building anything on top of them; the
single `theorem` in this file, `Address.next_ne`, is there only because every
pair rule needs it to simplify.  All 102<!--@suite--> tests currently agree with the
architecture, and the 12 `tso ⊆ arm` containment checks pass.

This file is the single description of each litmus test.  The assembly herd7
checks is *generated* from the `Instr` lists below (§9), and the verdicts herd7
is compared against are generated from the same `archAllows` / `states` fields
the model is tested against.  Nothing under `litmus/` is hand-written; editing
it is pointless, as `check-herd.sh` regenerates it before every run.

  lean --run WeakMem.lean              -- run the model, print the report
  lean --run WeakMem.lean emit DIR     -- write DIR/{aarch64,x86_64,aarch64-pair,
                                          aarch64-wide}/*.litmus
  ./check-herd.sh                      -- emit, run herd7, compare, exit 1 on
                                          any disagreement
  ./ablate.sh                          -- show which TSO rules are load-bearing

The reference verdicts come from herd7 master (7.58+1, rev ad8e24e, 2026-10-02,
built from github.com/herd/herdtools7); release 7.58 agrees with it on every
verdict and state count below.  Only the `aarch64` suite runs
against a bundled herdtools7 model (`aarch64.cat`) unchanged.  The other two do
not, and the reason is this: neither bundled
x86 model orders read-modify-writes, and the bundled aarch64 model treats
`CASP` as two independent single-word RMWs.  Those suites run against
`cats/x86tso-mixed-rmw.cat` and `cats/aarch64-pair.cat`, which are the bundled
models with our axioms added -- each axiom carries the witness that forced it.

Both the verdict *and* the number of distinct final states are checked; the
state count is the stronger test and is what caught `LB+data` being vacuous.

Full citations for Promising-ARM/RISC-V, herdtools7 and the ARMv8 and x86-TSO
models are in `Promises.lean`'s header.
None of the three is ours.

CAVEATS, since being *stronger* than the architecture is the unsound direction:

  * The reorder rule (`mayReorder`) is a hand-written approximation of ARM's
    ordered-before relation, not a transcription of it.  It is validated only
    by the suite below.  Anything the suite does not cover is unverified.
  * Accesses are single-word, or a naturally-aligned pair of adjacent words
    (`rmwPair`, and under FEAT_LSE2 `storePair`/`loadPair`).  No sub-word, no
    unaligned, and no genuinely overlapping mixed-size access.
  * The wide access assumes FEAT_LSE2 and is ARM-only: `wellFormed` rejects
    `storePair`/`loadPair` under `tso`, because whether herd7 models a 16-byte
    x86 access usefully is unmeasured.
  * `plain` vs `once` (compiler-visible) access kinds are not yet modelled;
    every access here behaves as `once`.
  * `tso ⊆ arm` is *tested* on twelve shapes (§8), not proved.  It **is** proved
    for the successor machine -- `Promises.lean` §16, `tso_outcomes_subset_arm`,
    for every program -- but that theorem is about that machine, and the
    out-of-order scheduler here is exactly what it does not have.  So a result
    established against *this* file still does not transfer from ARM to x86 by
    citation.

SCOPE.  What is validated here is the *memory subsystem*, not the model the
design is ultimately about.  `Val.undef` and `Val.loc` are never constructed by
any test; allocation labels and offsets are used only through `DecidableEq`;
and the harness interleaves N explicit threads rather than the two agents
(local and `Remote`) of `Promises.lean`.  Most importantly, half the relaxed behaviour lives in the
harness's scheduler (`issuable`), not in the transition rules — force in-order
issue and `LB` and `MP+po+dmb.ld` both become wrongly forbidden.  A program
logic that executes in program order therefore does *not* inherit this
validation from these rules alone.

RESOLVED, see `Promises.lean`: an in-order machine *does* reproduce all 102<!--@suite--> tests
(with the same state sets) once stores may fulfill earlier **promises**.  That
file is the front-end this one could not be; the scheduler here stays as it is,
because it is the thing `Promises.lean` is validated against.
-/

namespace WeakMem

/-! ## 1. Basic types -/

abbrev AllocLabel := Nat
abbrev Offset := Nat

/-- Global timestamp.  Also the index into `Memory`. -/
abbrev Ts := Nat

structure Address where
  label : AllocLabel
  offset : Offset
  deriving Repr, DecidableEq, Inhabited

/-- The second word of a pair access.  Single-word accesses are always aligned
    (a settled design decision), so "the next word" is unambiguous. -/
def Address.next (a : Address) : Address := { a with offset := a.offset + 1 }

/-- The two words of a pair are different addresses.

    Obvious, and needed constantly: every pair rule updates `coh` with a chain
    `if b = a then ... else if b = a.next then ...`, and reading the second
    branch off it requires knowing the first does not fire. -/
theorem Address.next_ne (a : Address) : a.next ≠ a := by
  intro h
  -- `Nat.succ_ne_self` rather than `omega`: `Offset` is an `abbrev`, and
  -- `omega` does not see through it to find a `Nat` to reason about.
  exact absurd (congrArg Address.offset h) (Nat.succ_ne_self a.offset)

/-- `undef` is a *value*, not a separate state tag: a fresh allocation really
    does contain it, and "no thread observes an uninitialised object" becomes
    "no load reads-from an `undef` write".

    `null` is the other value that is not a number and not a pointer, and it is
    a **fourth constructor rather than a reserved address** for two reasons,
    only one of which was anticipated.

    The anticipated one: it must not be `num 0`, because
    then `Int → Ptr` exists by the back door and the type system's guarantee
    that a pointer can only come from an allocation is gone.

    The one that decided it: a reserved `AllocLabel` would make `null` a
    `Val.loc`, and *every* site that asks "is this a pointer?" would then need
    to ask a second question.  `Reaches.ptr` would follow it, `rlearnedOf` would
    hand back a dereferenceable `RAddr`, and `reaches_push_nonptr`'s hypothesis
    `∀ b g, v ≠ Val.loc b g` would stop holding of a value that points nowhere.
    A constructor gets the right answer at all of them by construction — and
    at most of them it costs nothing at all, because those matches already end
    in a wildcard.

    The plan was to try the reserved label *first*, on the
    grounds that a new constructor would be disruptive.  That estimate was
    checkable in one command and was wrong: the development contains six
    exhaustive `Val` case splits, three of them one line each in proofs and
    three of them display helpers.  The command said four, because it looked at
    the two model files -- which is what §6.3's objection was about -- and the
    other two were found by the exhaustiveness checker, the last of them only
    once the gate reached `Tutorial.lean`.  Which is the argument restated: a
    site missed here is a compile error, and a site missed under the reserved
    label is a `Val.loc` flowing quietly into `Reaches`.

    `null` is distinct from `undef`, and the distinction is the point.  `undef`
    is "nobody has written here"; `null` is "somebody wrote here, deliberately,
    and what they wrote is not a pointer".  The language's growable array depends on
    telling them apart: nulling a popped slot leaves it *initialised*.

    **`loc` carries a tag**.  A tier-1 sum with two
    or more pointer arms is one word whose low bits say which arm it is
    (pointers may be low-bit tagged), and a model
    `Val` has to be able to hold that word or the sum cannot be stored with the
    single-copy atomicity §3.5 promises.  The tag is not part of the address:
    a load or store goes through `a`, and a tagged pointer must be untagged
    (by the program) before it is dereferenced.  `Reaches` follows a tagged
    pointer exactly as an untagged one, which is what the collector contract
    needs (§1.3 R7).

    The field is **required**, with no default, and that is deliberate.  With
    `tag : Nat := 0` Lean elaborates the *pattern* `.loc a` as `.loc a 0`, so
    every existing "is this a pointer?" match would have silently stopped
    matching tagged pointers -- the reserved-label failure above, reintroduced
    by a convenience.  Without a default every site is a compile error until
    someone decides what it means. -/
inductive Val where
  | undef
  | num (n : Nat)
  | loc (a : Address) (tag : Nat)
  | null
  deriving Repr, DecidableEq, Inhabited

/-- A value in a register, carrying the memory events its computation depends
    on.  Views propagate only through explicitly dependency-preserving
    combinators (`deps` on an instruction); ordinary arithmetic would drop the
    view to 0, conservatively modelling a compiler that breaks the dependency.

    The two timestamps are consumed **asymmetrically**, and conflating them is
    a real bug rather than a tidiness question -- see `depBound`.  `view` is
    what the *writer* published and is what a store re-publishes; `rts` is what
    the *reader* did and is what a dependency orders against. -/
structure TVal where
  val : Val
  /-- Inherited from the message.  What the *writer* published. -/
  view : Ts
  /-- The timestamp this value was read from.  What the *reader* did. -/
  rts : Ts
  deriving Repr, Inhabited

def TVal.mk0 (v : Val) : TVal := ⟨v, 0, 0⟩

/-! ## 2. Memory -/

/-- A write event.  `view` is what a reader of this message inherits: it is how
    the writer publishes its earlier accesses.  A plain store publishes only
    what preceding fences put into `vRelSt`. -/
structure Msg where
  loc : Address
  val : Val
  view : Ts
  deriving Repr, Inhabited

abbrev Memory := Array Msg

/-- Is there a write to `a` strictly after `t` and at or before `bound`?
    If so, `t` has been superseded by something the reader is already ordered
    after, and reading `t` would violate coherence/ordering. -/
def hiddenFrom (mem : Memory) (a : Address) (t bound : Ts) : Bool :=
  (List.range (bound + 1)).any fun t' =>
    decide (t < t') && (mem[t']?.elim false fun m => decide (m.loc = a))

/-- May a reader whose ordering bound is `bound` read `a` from timestamp `t`? -/
def readable (mem : Memory) (a : Address) (t bound : Ts) : Bool :=
  (mem[t]?.elim false fun m => decide (m.loc = a)) && !hiddenFrom mem a t bound

/-! ## 3. Per-agent view state -/

structure VState where
  /-- Per-location coherence view: reads of `a` are bounded below by `coh a`. -/
  coh : Address → Ts
  /-- Join of the timestamps loads read from, and of the views they inherit.
      Consulted by `dmb ld`.  Including the load's *own* timestamp is what
      makes IRIW+dmb.sy forbidden, i.e. what expresses multi-copy atomicity;
      it is only sound because store→store reordering is modelled separately,
      by letting an agent append its stores out of order. -/
  vRd : Ts
  /-- Join of timestamps this agent has stored.  Consulted by `dmb st`. -/
  vWr : Ts
  /-- Join of views of branch conditions.  Consulted by `isb`. -/
  vCtrl : Ts
  /-- Joined into the ordering bound of every subsequent access. -/
  vPreBase : Ts
  /-- What a subsequent plain store publishes in its message view. -/
  vRelSt : Ts
  /-- Timestamps of this agent's own writes.  A read of one of them is `rfi`,
      which ARM does not order (`obs` has `rfe` only); a read of any other is
      `rfe`, and an acquire is then ordered after the write it read.  See
      `extTs`. -/
  mine : List Ts := []
  /-- Forwarding views (Pulte et al.'s forwarding bank): for each of this
      agent's own *plain* writes, the join of its address and data
      dependencies.  A read of that write contributes this, not the write's
      timestamp or message view: `rfi` is not in `ob`, but `(addr|data);rfi`
      is (`dob`).  `SB+rfi-pos`, `SB+rfi-dmb.ld` and
      `SB+dmb.st-rfi-ldar+dmb.sy` are the tests; `MP+dmb.sy+data-rfi-ldar` is
      the control that says the dependencies must stay.  An RMW's write gets
      no entry, so `aob` (`MP+stlr+swp-rfi-ldar`) is untouched.  See `ownFwd`. -/
  fwd : List (Ts × Ts) := []
  deriving Inhabited

def VState.init : VState :=
  { coh := fun _ => 0, vRd := 0, vWr := 0, vCtrl := 0, vPreBase := 0, vRelSt := 0 }

inductive Fence where
  | ld   -- dmb ld
  | st   -- dmb st
  | sy   -- dmb sy
  deriving Repr, DecidableEq, Inhabited

/-! ### Architectures

The same rules describe both targets; TSO is ARM with things taken away.
Writing it this way (rather than as a separate model) is deliberate: it makes
`arm` visibly the weaker of the two, which is the direction proofs need to
transfer in.  Two differences suffice, both below in §5:

1. A load's ordering bound always includes `vRd` (load→load is ordered).
2. `mayReorder` admits only one relaxation: a load hoisting past a store to a
   different address.  Store→load is TSO's *only* reordering.

Both are load-bearing, and the suite says exactly how.  Drop 1 and `MP`/`IRIW`
become allowed; drop 2 and `MP`/`LB`/`IRIW` become allowed.

A third difference is tempting and is **deliberately absent**: TSO also orders
store→store and load→store, which would suggest making every TSO store publish
`vRd`/`vWr` like an `STLR`.  That is redundant here — see the comment in
`stepStore` — and adding it changes no test.  Getting this wrong in the other
direction is the real hazard: "TSO = ARM with a stricter `mayReorder`" is
*false*, and the ablation above is the proof.  With difference 2 in place but 1
removed, `MP` is still allowed: no amount of forbidden reordering bounds the
reader's second load.

On x86 `MFENCE` is `Fence.sy`; there is no `Fence.ld`/`Fence.st` and no
acquire/release form of an ordinary access, so those cases are simply never
exercised by a `tso` litmus test. -/
inductive Arch where
  | arm
  | tso
  deriving Repr, DecidableEq, Inhabited

/-! ## 4. Instruction language

This is the litmus front-end, not the program logic front-end.

It was originally noted here that stage 2 would "drive the same rules from a
`do`-notation monad with a single Local agent".  That is not accurate, and the
inaccuracy matters: a `do`-notation front-end runs in program order, and so
would drive `stepLoad`/`stepStore`/`stepFence` but *not* `issuable`.  Forcing
in-order issue here wrongly forbids `LB` and `MP+po+dmb.ld` — so the stage-1
validation does not transfer to such a front-end.

`deps` lists the registers that an access's address (and, for a store, its
data) syntactically depends on, in a way the compiler is required to preserve.
This is `keepDep` made syntactic.
-/

abbrev Reg := Nat

inductive Expr where
  | const (v : Val)
  | reg (r : Reg)
  deriving Repr, Inhabited

/-- The value an `Expr` denotes in a register file. -/
def Expr.valIn (regs : Reg → TVal) : Expr → Val
  | .const c => c
  | .reg r => (regs r).val

/-- The registers a write that stores `e` depends on: the address dependencies
    `deps`, plus `e`'s own register if it is one (a *data* dependency).

    The constant case returns `deps` itself rather than `deps ++ []`, so that
    for a constant this is `deps` by definition and an RMW with a constant new
    value is literally the rule it was before the operand became an `Expr`. -/
def Expr.writeDeps (e : Expr) (deps : List Reg) : List Reg :=
  match e with
  | .const _ => deps
  | .reg r => deps ++ [r]

/-- What a read-modify-write does with the value it read.

    `swap` writes the operand unconditionally (`SWP`, x86 `XCHG`); `cas v`
    writes it only if the value read is `v` (`CAS`, `LOCK CMPXCHG`); the
    fetch-ops combine the value read with the operand (`LDADD`, `LDSET`,
    `LDCLR`, `LDEOR`; x86 `LOCK XADD`, and `LOCK OR/AND/XOR` when the old value
    is unused).  One instruction rather than six because the memory-model
    content is identical: the kind decides a pure test on the value read and a
    pure function of it, and neither touches ordering or atomicity.  The
    write's view already carries the read's (`stepRmw`'s `rv`), which is all a
    data dependency on the RMW's own read would add. -/
inductive RmwKind where
  | swap | cas (v : Val) | add | or | and | xor
  deriving Repr, DecidableEq, Inhabited

/-- Does the value read make the write happen?  Only a `cas` can fail. -/
def RmwKind.succeeds : RmwKind → Val → Bool
  | .cas e, v => decide (v = e)
  | _, _ => true

/-- The value written, from the value read and the operand.  Fetch-ops on
    anything but a number are undefined, as the arithmetic would be. -/
def RmwKind.apply : RmwKind → Val → Val → Val
  | .swap, _, o | .cas _, _, o => o
  | .add, .num n, .num k => .num (n + k)
  | .or, .num n, .num k => .num (n ||| k)
  | .and, .num n, .num k => .num (n &&& k)
  | .xor, .num n, .num k => .num (n ^^^ k)
  | _, _, _ => .undef

/-- A fetch-op: the kinds whose write depends on the value read. -/
def RmwKind.isFetch : RmwKind → Bool
  | .swap | .cas _ => false
  | _ => true

inductive Instr where
  | load (dst : Reg) (a : Address) (deps : List Reg) (acq : Bool)
  | store (a : Address) (e : Expr) (deps : List Reg) (rel : Bool)
  /-- A read-modify-write.  `dst` receives the value read, whether or not the
      write happens, which is how a program tells success from failure.

      `kind` says what is done with the value read: an unconditional swap
      (`SWP`, x86 `XCHG`), a compare-and-swap (`CAS`), which writes only if the
      value read is `v`, or a fetch-op (`LDADD` and friends), which writes a
      function of it.  One constructor for all of them because the memory-model
      content is identical -- see `RmwKind`.

      `acq`/`rel` select `CASA`/`CASL`/`CASAL`, and mean exactly what they mean
      on a load and a store respectively.

      `newv` is an `Expr`, exactly as a store's value is: `CAS Ws,Wt,[Xn]`,
      `SWP Ws,Wt,[Xn]` and `LDADD Ws,Wt,[Xn]` take the new value or operand
      from a register, and a register that came from a load carries a data
      dependency into the write.  The write half therefore publishes that
      register's view, as `stepStore` does.  The comparison value stays a
      constant: it feeds only the success test, never memory. -/
  | rmw (dst : Reg) (a : Address) (kind : RmwKind) (newv : Expr)
        (deps : List Reg) (acq rel : Bool)
  /-- A two-word compare-and-swap: ARM `CASP` (FEAT_LSE), x86 `LOCK
      CMPXCHG16B`.  Operates on `a` and the word immediately after it.

      Unlike `rmw` the comparison is not optional.  An unconditional pair swap
      has no lock content, and `CASP` is the form both architectures actually
      provide as the primitive worth modelling (a settled design decision).

      Both words are compared before either is written, and the two writes land
      in consecutive slots, which is what makes this atomic rather than two
      `rmw`s.  See `stepRmwPair`.

      `new0`/`new1` are `Expr`s for the reason `rmw`'s `newv` is: `CASP`
      takes the new pair from registers `Xt,X(t+1)`, and a register that came
      from a load is a data dependency of both writes, so the pair publishes
      its view, as `stepStorePair` does.  The compare values stay constants. -/
  | rmwPair (dst0 dst1 : Reg) (a : Address) (cmp0 cmp1 : Val) (new0 new1 : Expr)
            (deps : List Reg) (acq rel : Bool)
  /-- A two-word *plain* store: ARM `STP`, over `a` and the word after it.

      This is the FEAT_LSE2 instruction, and it is the whole content of
      the language's tier 2: a 16-byte aligned access that is
      single-copy atomic without being a read-modify-write.

      The model change it needs is the same one `cats/aarch64-lse2.cat` makes,
      and that correspondence is the argument that the two mean the same
      thing.  The cat file widens `pair-atomic`'s write side from
      `range(rmw) * range(rmw)` to `W * W` -- all writes, not just RMW writes.
      Here, `Config.pairs` was extended only by `stepRmwPair`; `stepStorePair`
      extends it too.  Nothing else moves, because `pairStraddles` and
      `pairTop` were already written against `pairs` rather than against
      `rmwPair`.

      Baseline Armv8 does *not* give this, which is why these tests are a
      separate group with a separate reference model, exactly as
      `cats/aarch64-pair.cat` and `cats/aarch64-lse2.cat` are separate
      files. -/
  | storePair (a : Address) (e0 e1 : Expr) (deps : List Reg) (rel : Bool)
  /-- A two-word *plain* load: ARM `LDP`.  The read half of the above.

      Note what it does and does not buy.  Against a wide store it is a
      snapshot; against two ordinary stores it must still tear, because a wide
      *load* cannot make non-atomic writes atomic.  `WidePlainPairRead` is the
      control that holds this to account. -/
  | loadPair (dst0 dst1 : Reg) (a : Address) (deps : List Reg) (acq : Bool)
  | fence (f : Fence)
  /-- Register a control dependency on `r`.  Note that on ARM a control
      dependency orders load→store but NOT load→load. -/
  | branch (r : Reg)
  | isb
  deriving Repr, Inhabited

structure Thread where
  prog : List Instr
  regs : Reg → TVal
  vs : VState
  deriving Inhabited

def Thread.mk' (prog : List Instr) : Thread :=
  { prog := prog, regs := fun _ => TVal.mk0 (Val.num 0), vs := VState.init }

structure Config where
  mem : Memory
  ths : Array Thread
  /-- Timestamps `p` such that `mem[p]` and `mem[p+1]` were written together by
      one atomic pair RMW.

      This cannot be read off `mem`.  Two ordinary stores to adjacent words
      produce exactly the same two messages, and a pair read *is* allowed to
      tear across those -- our `cats/aarch64-pair.cat` restricts its write side
      to `range(rmw)` for precisely this reason, so the model has to draw the
      same distinction.  Marking the message itself would mean a fourth field
      on `Msg`, which anonymous-constructor sites (including ones inside proof
      statements) would all have to grow; `Config` is built with record syntax
      in both of its two literals, so a defaulted field here is free. -/
  pairs : List Ts := []
  deriving Inhabited

/-! ## 5. Transition rules -/

def depView (regs : Reg → TVal) (deps : List Reg) : Ts :=
  deps.foldl (fun acc r => max acc (regs r).view) 0

def depRts (regs : Reg → TVal) (deps : List Reg) : Ts :=
  deps.foldl (fun acc r => max acc (regs r).rts) 0

/-- **The dependency bound a load must respect**, joining the view a dependency
    inherited with the timestamp it was read from.

    The `rts` half is not optional and was missing until §10's generated suite
    found it.  ARM has `ob ⊇ obs; dob`: a read that reads-from an external write
    is ordered after that write, and a dependency-ordered access is ordered
    after the read.  In a timestamp model "ordered after the write at `t`" is
    exactly "bound ≥ t", and only `rts` carries `t`.  Using `view` alone models
    the *writer's* release path and silently drops the `rf` edge.

    The symptom was that the model got every *fence*-ordered shape right and
    every *dependency*-ordered one wrong from three threads up -- `WRC+addrs`,
    `WRC+data+addr`, `WRC+ctrl+ctrlisb`, `IRIW+addrs` and four siblings all came
    out `allowed` against herd7's `forbidden`, while `WRC+X+dmb.ld` was right.
    That asymmetry is the fingerprint: `vRd` already joined `pairTop t`, and the
    register did not.  No two-thread test can see it, which is why a hand-picked
    suite missed it for eight stages.

    It does **not** forbid `MP+po+addr`.  `hiddenFrom` hides `t` only if another
    write to the same address lands in `(t, bound]`, and there the writer may
    publish `y` before `x`, so the reader's bound never reaches the write of
    `x`.  The freedom comes from `issuable` here and from promising in
    `Promises.lean`; the opposite was once claimed, and that claim
    predates both.

    Note what does **not** change: `stepStore`'s `dv`, which is what a store
    *publishes*.  That is a different rule with a different justification, and
    conflating the two is what the separate field exists to prevent. -/
def depBound (regs : Reg → TVal) (deps : List Reg) : Ts :=
  max (depView regs deps) (depRts regs deps)

/-- **Single-copy atomicity, reader side.**  The extent of the atomic write a
    read at `t` observed: `t + 1` if `t` is the first word of a pair RMW's
    write, and `t` otherwise.

    Observing *either* word of a pair RMW's write means observing the whole of
    it, so the reader's read view must cover both.  Without this the model is
    asymmetric in a way no atomicity property can be: a scratch probe measured
    it, with an observer doing `LDR` ; `DMB SY` ; `LDR` over the two words.
    Reading the second word first happens to drag `vRd` past `t + 1` anyway, so
    that direction came out forbidden; reading the first word first did not, so
    that direction came out allowed.  The two differ only in word order.

    `vRd` is the right carrier, and it is the only one that is right:

    * It is consumed only as *ordering* -- TSO's load→load bound, and
      `stepFence .ld`'s `vPreBase ⊔= vRd`.  So an unordered pair of loads may
      still tear, which is correct: without a barrier the second load may have
      been satisfied first.
    * Raising it from `t` to `t + 1` can hide exactly one further message, the
      pair's own second word, because timestamps are unique.

    The tempting alternative -- give the first word's *message* a view of
    `t + 1`, which needs no new parameter -- is wrong.  `Msg.view` is a view
    over **all** locations, so an acquire reader would take `vPreBase ≥ t + 1`,
    the maximum timestamp in memory, and a plain `CASP` would become a full
    barrier. -/
def pairTop (pairs : List Ts) (t : Ts) : Ts :=
  if pairs.contains t then t + 1 else t

/-- **What an acquire read at `t` is ordered after, beyond the message's view.**
    ARM has `ob ⊇ obs ⊇ rfe` and `bob ⊇ [A]; po`: an `LDAR` that reads an
    *external* write at `t` orders every later access after that write, so the
    later accesses' bound is at least `t` (`pairTop`, for a pair's second
    word).  Reading an agent's *own* write is `rfi`, which is not in `ob`, and
    contributes nothing.

    Missing until the readers–writer lock found it: with only `m.view`, an
    acquire of a *plain* write that is coherence-after a release got nothing,
    so `WRC+rel+st+acq` -- `W x; STLR w` ∥ `STR w` (co-after) ∥ `LDAR w; LDR x`
    -- was allowed against herd7's `Never`, and so was every `CAS`/`LDR;STR`
    variant.  The `rfi` controls `SB+rfi-acq+dmb` and `MP+dmb+rfi-acq` are
    herd7-allowed and stay allowed, which is why this is not simply `t`. -/
def extTs (vs : VState) (pairs : List Ts) (t : Ts) : Ts :=
  if vs.mine.contains t then 0 else pairTop pairs t

/-- The forwarding view of a read of `t`, if `t` is one of this agent's own
    plain writes (`VState.fwd`).  Clamped to `t`: the dependencies of a write
    are below its ordering bound and so below `t` whenever a store's bound
    counts `rts` (`storeDepRts`), and the clamp makes every bound that held for
    `t` hold for the forwarding view without that hypothesis. -/
def ownFwd (vs : VState) (t : Ts) : Option Ts :=
  if vs.mine.contains t then (vs.fwd.find? (fun p => p.1 == t)).map (fun p => min t p.2) else none

/-- What a read of `t` carrying message view `mv` adds to `vRd`: the forwarding
    view for an own plain write, else the timestamp (`pairTop`) and the view. -/
def fwdRd (vs : VState) (pairs : List Ts) (t mv : Ts) : Ts :=
  (ownFwd vs t).getD (max (pairTop pairs t) mv)

/-- What an acquire read of `t` adds to `vPreBase`: the forwarding view for an
    own plain write, else the message view and `extTs`. -/
def fwdAcq (vs : VState) (pairs : List Ts) (t mv : Ts) : Ts :=
  (ownFwd vs t).getD (max mv (extTs vs pairs t))

/-- The forwarding view a plain store records: the join of its address and
    data registers' views and read timestamps (`depBound`). -/
def storeFwdW (regs : Reg → TVal) (e : Expr) (deps : List Reg) : Ts :=
  depBound regs (deps ++ match e with | .const _ => [] | .reg r => [r])

/-- A load is nondeterministic: it returns one successor per readable
    timestamp. -/
def stepLoad (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst : Reg) (a : Address) (deps : List Reg) (acq : Bool) : List Thread :=
  let vs := th.vs
  -- Ordering bound: fences, dependencies, and coherence.  Under TSO every
  -- earlier load joins in too, which is load→load ordering.
  let ordered := if arch = .tso then vs.vRd else 0
  let bound :=
    max (max (max vs.vPreBase (depBound th.regs deps)) (vs.coh a)) ordered
  let cands := (List.range mem.size).filter fun t => readable mem a t bound
  cands.map fun t =>
    let m := mem[t]!
    let tv : TVal := ⟨m.val, m.view, t⟩
    let vs' : VState :=
      { vs with
        coh := fun b => if b = a then max (vs.coh a) t else vs.coh b
        vRd := max vs.vRd (fwdRd vs pairs t m.view)
        -- LDAR: this load is ordered before every subsequent access.
        vPreBase := if acq then max vs.vPreBase (fwdAcq vs pairs t m.view) else vs.vPreBase }
    { th with
      regs := fun r => if r = dst then tv else th.regs r
      vs := vs' }

/-- Stores are the same on both architectures; see the `mview` comment. -/
def stepStore (mem : Memory) (th : Thread) (a : Address) (e : Expr)
    (deps : List Reg) (rel : Bool) : Memory × Thread :=
  let vs := th.vs
  let v := match e with
    | .const c => c
    | .reg r => (th.regs r).val
  let dataView := match e with
    | .const _ => 0
    | .reg r => (th.regs r).view
  let dv := max (depView th.regs deps) dataView
  -- What this store publishes.  STLR additionally publishes all prior accesses.
  --
  -- There is deliberately no TSO case here, though TSO does order store→store
  -- and load→store.  Publishing `vRd`/`vWr` for every TSO store is *redundant*:
  -- a store pushed at timestamp `t` can only have been preceded by accesses at
  -- timestamps `< t`, since the array only grows, so `mview < t`; and a reader
  -- of that message gets `vRd ≥ t` from the TSO load rule, which dominates.
  -- Ablating it changes no test.  Since an unjustified *strengthening* is the
  -- direction that makes a proof unsound with respect to real hardware, the
  -- redundant rule is left out rather than left in.
  let mview :=
    if rel then max (max vs.vRelSt (max vs.vRd vs.vWr)) dv
    else max vs.vRelSt dv
  let t := mem.size
  let mem' := mem.push ⟨a, v, mview⟩
  let vs' : VState :=
    { vs with
      coh := fun b => if b = a then t else vs.coh b
      vWr := max vs.vWr t
      mine := t :: vs.mine
      fwd := (t, storeFwdW th.regs e deps) :: vs.fwd }
  (mem', { th with vs := vs' })

def stepFence (th : Thread) (f : Fence) : Thread :=
  let vs := th.vs
  let vs' := match f with
    | .ld => { vs with vPreBase := max vs.vPreBase vs.vRd }
    | .st => { vs with vRelSt := max vs.vRelSt vs.vWr }
    | .sy => { vs with
                 vPreBase := max vs.vPreBase (max vs.vRd vs.vWr)
                 vRelSt := max vs.vRelSt (max vs.vRd vs.vWr) }
  { th with vs := vs' }

/-! ### Read-modify-write

The atomicity of an RMW is the one memory-model property that is not about
ordering, and it is the reason locks can be built at all.  Everything else in
this file constrains *which* write a read may see; this constrains whether a
read and a write may have anything **between** them.

The architectural statement is that the RMW's read and its write are adjacent
in the modification order of the location.  Here the array index *is* the
modification order (restricted to the location), so that becomes:

> no message at `a` has a timestamp strictly between the read's and the
> write's.

`rmwAdjacent` is exactly that, and it is the whole of atomicity.  Two things
follow that are worth naming, because both were checked against herd7 rather
than assumed:

* For a plain appending RMW the write lands at `mem.size`, so the condition
  says the read must be from the **coherence-latest** write to `a`.  An RMW
  therefore cannot read stale, no matter how far behind the thread's views
  are.  That is not an extra rule -- it falls out.
* The coherence-latest message at `a` is never hidden, so it is readable
  whatever the ordering bound is.  A successful RMW consequently has exactly
  one read candidate, which is why adding RMW costs the state space almost
  nothing.

A *failed* CAS is a plain read: it writes nothing, so there is nothing for
atomicity to constrain, and it may read stale like any other load.  herd7
agrees -- this is why `SB+cas` has four states and not two. -/

/-- Is there a message at `a` strictly between `tr` and `tw`? -/
def betweenAt (mem : Memory) (a : Address) (tr tw : Ts) : Bool :=
  (List.range mem.size).any fun t' =>
    decide (tr < t') && decide (t' < tw) &&
      (mem[t']?.elim false fun m => decide (m.loc = a))

/-- The atomicity side condition: the read at `tr` and the write at `tw` are
    adjacent in the modification order of `a`. -/
def rmwAdjacent (mem : Memory) (a : Address) (tr tw : Ts) : Bool :=
  decide (tr < tw) && !betweenAt mem a tr tw

/-- Does the value read make the write happen? -/
def rmwSucceeds (kind : RmwKind) (v : Val) : Bool := kind.succeeds v

/-- One RMW, returning one successor per readable timestamp that is consistent
    with atomicity.  The read half is `stepLoad`'s rule and the write half is
    `stepStore`'s; the only new content is `rmwAdjacent`. -/
def stepRmw (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst : Reg) (a : Address)
    (kind : RmwKind) (newv : Expr) (deps : List Reg) (acq rel : Bool) :
    List (Memory × Thread) :=
  -- On x86 a locked read-modify-write is a full barrier, so an RMW there
  -- carries `MFENCE`'s view update in addition to its own.  ARM's `CAS`/`SWP`
  -- carry only what `acq`/`rel` ask for, which is why `SB+cas` is `Sometimes`
  -- on ARM and forbidden on x86 -- see the two tests of that name.
  --
  -- This applies to a *failed* CAS too: `LOCK CMPXCHG` asserts the lock and
  -- performs the read-modify-write cycle whether or not the comparison
  -- succeeds, so the barrier is not conditional on the write happening.  And
  -- it is a barrier on *both* sides: the read is ordered after every earlier
  -- access, which is why the fence is applied before the read bound is taken
  -- as well as after the write (`SB+cmpxchg-fails`).
  let lockFence (t : Thread) : Thread :=
    if arch = .tso then stepFence t .sy else t
  let th := lockFence th
  let vs := th.vs
  let ordered := if arch = .tso then vs.vRd else 0
  let bound :=
    max (max (max vs.vPreBase (depBound th.regs deps)) (vs.coh a)) ordered
  let cands := (List.range mem.size).filter fun t => readable mem a t bound
  cands.filterMap fun t =>
    let m := mem[t]!
    -- The read half, identical to `stepLoad`, `pairTop` included.
    let readVs : VState :=
      { vs with
        coh := fun b => if b = a then max (vs.coh a) t else vs.coh b
        vRd := max vs.vRd (fwdRd vs pairs t m.view)
        vPreBase := if acq then max vs.vPreBase (fwdAcq vs pairs t m.view) else vs.vPreBase }
    -- A successful non-acquire `CAS` returns the value read with no
    -- dependency at all (herd7's `aarch64_cas_ok`): a later access addressed
    -- through it is ordered neither after the read nor after whatever the
    -- comparand register depended on before -- herd7 allows
    -- `MP+dmb.sy+ldr-cas-addrRs`, where that register was loaded first, and
    -- forbids the same shape with no `CAS`.  `MP+dmb.sy+cas-addrRs` is the
    -- test here; `CASA`/`CASAL` are the controls.
    let dstV : TVal := match kind with
      | .cas _ => if rmwSucceeds kind m.val && !acq then ⟨m.val, 0, 0⟩
                  else ⟨m.val, m.view, t⟩
      | _ => ⟨m.val, m.view, t⟩
    let readTh : Thread :=
      { th with
        regs := fun r => if r = dst then dstV else th.regs r
        vs := readVs }
    if !rmwSucceeds kind m.val then
      -- Failed CAS: an ordinary load, no write, no atomicity obligation.
      some (mem, lockFence readTh)
    else
      let tw := mem.size
      if !rmwAdjacent mem a t tw then none
      else
        -- The write half, identical to `stepStore`, but computed against the
        -- views the read already updated -- the write of an RMW follows its
        -- own read.
        --
        -- The new value and its data dependency come from the registers
        -- *before* the read: `dst` may name the same register, and the value
        -- read is not an input to the write.  The data register joins `dv`
        -- only; it is not an address dependency, so it does not bound the read.
        let dv := depView th.regs (newv.writeDeps deps)
        -- `rv` is the view of the read half.  ARM's `aob` (via `rmw` then
        -- `lrs`) says: an acquire that reads an RMW's write is
        -- ordered after the RMW's *read* (not just its write), and since
        -- `rmw` itself is in `aob`, so is everyone else ordered after the
        -- write.  Carrying `rv` in the message is what delivers that to an
        -- own-thread acquire, which `extTs` otherwise lets through (`rfi`).
        -- `MP+stlr+swp-rfi-ldar` is the test.  A release RMW already has it,
        -- inside `vRd`.
        -- The write is computed against `wvs`: the read's views with `rv`
        -- joined into `vRelSt`, so that it is *literally* a store's write
        -- from that state (`TermStep.stepRmw_split` leans on this); the
        -- thread keeps `readVs.vRelSt`, since later stores are not ordered
        -- after the RMW's read.
        let rv := max (pairTop pairs t) m.view
        let wvs := { readVs with vRelSt := max readVs.vRelSt rv }
        let mview :=
          if rel then max (max wvs.vRelSt (max wvs.vRd wvs.vWr)) dv
          else max wvs.vRelSt dv
        some (mem.push ⟨a, kind.apply m.val (newv.valIn th.regs), mview⟩,
          lockFence
            { readTh with
              vs := { readVs with
                      coh := fun b => if b = a then tw else readVs.coh b
                      vWr := max readVs.vWr tw
                      mine := tw :: readVs.mine } })

/-! ### Pair atomicity

A `CASP` is not two `CAS`es.  Two things have to hold that per-location
adjacency does not give on its own.

**The writes must land together.**  Handled by construction: both messages are
pushed in one step, at `mem.size` and `mem.size + 1`.  Per-location adjacency
then does the rest, and it is worth seeing why it suffices.  Suppose pair A
lands at `(n, n+1)` and pair B reads `t0 = n` -- it saw A's first word -- but
`t1 < n+1` at the second.  For B to *succeed* its write to the second word must
be adjacent to `t1`; but A's write at `n+1` is a write to that location lying
between, so adjacency fails and B contributes no successor.  A partially
committed pair is therefore not expressible, which is exactly the property
herd7's stock model lacked.

**The reads must be a consistent snapshot.**  This one does *not* fall out.  A
*failing* pair CAS writes nothing, so adjacency constrains nothing, and its two
reads would otherwise be free to come from either side of somebody else's pair
write -- a torn read.  `cats/aarch64-pair.cat`'s probe `C-read-tear` says
`Never`, so the model must forbid it too, and `pairStraddles` is that rule.

Note the asymmetry with plain stores.  A pair read may tear across two
*ordinary* adjacent stores, and must, because they are not atomic.  That is why
`Config.pairs` exists rather than the condition being read off memory, and it
is the same distinction the cat file draws by restricting its write side to
`range(rmw)`. -/

/-- Would a pair read at `(t0, t1)` straddle an atomic pair write?

    `pairs` holds the timestamps `p` at which some pair RMW wrote its first
    word, its second being at `p + 1`.  Reading at or after `p` in the first
    word while reading before `p + 1` in the second (or vice versa) means the
    two words came from different sides of one atomic update.

    Both words are checked, not just the first.  Every way of extending `pairs`
    does write `a0` at `p` and `a0.next` at `p + 1`, so the second conjunct is
    never false in a reachable state and adding it changes no outcome -- the
    litmus suite says so.  What it buys is that the predicate no longer depends
    on that being true.  The argument that a pair CAS always has *some* outcome
    turns on the coherence-latest message at each word never straddling, and
    that step needs to know where the second word is; with the conjunct the
    fact is read off the predicate instead of carried as an invariant on the
    machine. -/
def pairStraddles (mem : Memory) (pairs : List Ts) (a0 : Address)
    (t0 t1 : Ts) : Bool :=
  pairs.any fun p =>
    (mem[p]?.elim false fun m => decide (m.loc = a0)) &&
    (mem[p + 1]?.elim false fun m => decide (m.loc = a0.next)) &&
    (decide (p ≤ t0) != decide (p + 1 ≤ t1))

/-- One two-word compare-and-swap.  Returns the successors, each carrying the
    new memory, the new pair-start list, and the new thread.

    The shape follows `stepRmw` throughout; everything that is genuinely new is
    the `pairStraddles` filter and the fact that two messages are pushed. -/
def stepRmwPair (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst0 dst1 : Reg) (a : Address) (cmp0 cmp1 : Val) (new0 new1 : Expr)
    (deps : List Reg) (acq rel : Bool) :
    List (Memory × List Ts × Thread) :=
  let a0 := a
  let a1 := a.next
  -- `lockFence` first as well as last on x86: see `stepRmw`.
  let lockFence (t : Thread) : Thread :=
    if arch = .tso then stepFence t .sy else t
  let th := lockFence th
  let vs := th.vs
  let ordered := if arch = .tso then vs.vRd else 0
  -- Two different dependency quantities, and they must not be conflated: the
  -- *read* side joins `rts` (`depBound`), the *publication* view below does
  -- not.  See `depBound`.
  --
  -- The new values' registers, if any, are data dependencies of both writes
  -- (one shared `mview`, as in `stepStorePair`); they join `dv` only, never
  -- the read's bound.  Values are taken before the read, as in `stepRmw`.
  let dv := depView th.regs (new1.writeDeps (new0.writeDeps deps))
  let bnd := fun (b : Address) =>
    max (max (max vs.vPreBase (depBound th.regs deps)) (vs.coh b)) ordered
  let c0 := (List.range mem.size).filter fun t => readable mem a0 t (bnd a0)
  let c1 := (List.range mem.size).filter fun t => readable mem a1 t (bnd a1)
  c0.flatMap fun t0 => c1.filterMap fun t1 =>
    if pairStraddles mem pairs a0 t0 t1 then none
    else
      let m0 := mem[t0]!
      let m1 := mem[t1]!
      -- The read half, `stepLoad`'s rule applied to both words at once.
      let readVs : VState :=
        { vs with
          coh := fun b =>
            if b = a0 then max (vs.coh a0) t0
            else if b = a1 then max (vs.coh a1) t1
            else vs.coh b
          vRd := max vs.vRd (max (fwdRd vs pairs t0 m0.view) (fwdRd vs pairs t1 m1.view))
          vPreBase :=
            if acq then max vs.vPreBase (max (fwdAcq vs pairs t0 m0.view) (fwdAcq vs pairs t1 m1.view))
            else vs.vPreBase }
      let readTh : Thread :=
        { th with
          regs := fun r =>
            if r = dst0 then ⟨m0.val, m0.view, t0⟩
            else if r = dst1 then ⟨m1.val, m1.view, t1⟩
            else th.regs r
          vs := readVs }
      if !(decide (m0.val = cmp0) && decide (m1.val = cmp1)) then
        -- Failed compare: two ordinary loads.  No write, no atomicity
        -- obligation beyond the snapshot condition already applied above.
        some (mem, pairs, lockFence readTh)
      else
        let tw0 := mem.size
        let tw1 := mem.size + 1
        if !(rmwAdjacent mem a0 t0 tw0 && rmwAdjacent mem a1 t1 tw1) then none
        else
          -- `rv`: see the single-word RMW.
          let rv := max (max (pairTop pairs t0) m0.view) (max (pairTop pairs t1) m1.view)
          let wvs := { readVs with vRelSt := max readVs.vRelSt rv }
          let mview :=
            if rel then max (max wvs.vRelSt (max wvs.vRd wvs.vWr)) dv
            else max wvs.vRelSt dv
          some ((mem.push ⟨a0, new0.valIn th.regs, mview⟩).push ⟨a1, new1.valIn th.regs, mview⟩,
            pairs ++ [tw0],
            lockFence
              { readTh with
                vs := { readVs with
                        coh := fun b =>
                          if b = a0 then tw0
                          else if b = a1 then tw1
                          else readVs.coh b
                        vWr := max readVs.vWr tw1
                        mine := tw0 :: tw1 :: readVs.mine } })


/-! ### The wide access (FEAT_LSE2)

`stepRmwPair` above already makes a two-word access single-copy atomic, and
`pairStraddles`/`pairTop` already state that atomicity over `Config.pairs`
rather than over the instruction that created the entry.  So the two rules
below are short, and their shortness is the result rather than a convenience:
**taking FEAT_LSE2 is the same edit here as it is in the reference model.**
`cats/aarch64-lse2.cat` widens `pair-atomic`'s write side from
`range(rmw) * range(rmw)` to `W * W`; `stepStorePair` widens the set of
timestamps in `pairs` from pair-RMW writes to all wide writes.  Neither change
touches anything else.

What must *not* happen is the rule becoming a blanket prohibition on adjacent
writes.  Two ordinary `stepStore`s do not extend `pairs`, so a reader may still
tear across them, and `WidePlainOrderedRead` is the control that says so. -/

/-- A two-word plain store.  `stepStore` twice, in one step, plus the `pairs`
    entry -- and the `pairs` entry is the whole of FEAT_LSE2.

    The two messages land at `mem.size` and `mem.size + 1`, which is what makes
    them a pair as far as `pairStraddles` is concerned; the same construction
    `stepRmwPair` uses, and the same reason it works. -/
def stepStorePair (mem : Memory) (pairs : List Ts) (th : Thread) (a : Address)
    (e0 e1 : Expr) (deps : List Reg) (rel : Bool) :
    Memory × List Ts × Thread :=
  let vs := th.vs
  let valOf : Expr → Val := fun e =>
    match e with | .const c => c | .reg r => (th.regs r).val
  let viewOf : Expr → Ts := fun e =>
    match e with | .const _ => 0 | .reg r => (th.regs r).view
  let dv := max (depView th.regs deps) (max (viewOf e0) (viewOf e1))
  -- Identical to `stepStore`'s `mview`, including the absence of a TSO case;
  -- the argument there applies here unchanged.
  let mview :=
    if rel then max (max vs.vRelSt (max vs.vRd vs.vWr)) dv
    else max vs.vRelSt dv
  let a0 := a
  let a1 := a.next
  let t0 := mem.size
  let t1 := mem.size + 1
  let mem' := (mem.push ⟨a0, valOf e0, mview⟩).push ⟨a1, valOf e1, mview⟩
  let vs' : VState :=
    { vs with
      coh := fun b => if b = a0 then t0 else if b = a1 then t1 else vs.coh b
      vWr := max vs.vWr t1
      mine := t0 :: t1 :: vs.mine
      fwd := (t0, storeFwdW th.regs e0 (deps ++ (match e1 with | .const _ => [] | .reg r => [r])))
             :: (t1, storeFwdW th.regs e0 (deps ++ (match e1 with | .const _ => [] | .reg r => [r])))
             :: vs.fwd }
  (mem', pairs ++ [t0], { th with vs := vs' })

/-- A two-word plain load.  Exactly `stepRmwPair`'s read half, with the compare
    and the write deleted -- including `pairStraddles`, which is what stops the
    two words coming from either side of somebody else's wide write.

    It buys a snapshot only against writes that were themselves atomic.  Against
    two ordinary stores `pairs` is empty, the filter never fires, and all four
    combinations survive. -/
def stepLoadPair (arch : Arch) (mem : Memory) (pairs : List Ts) (th : Thread)
    (dst0 dst1 : Reg) (a : Address) (deps : List Reg) (acq : Bool) :
    List Thread :=
  let a0 := a
  let a1 := a.next
  let vs := th.vs
  let ordered := if arch = .tso then vs.vRd else 0
  let bnd := fun (b : Address) =>
    max (max (max vs.vPreBase (depBound th.regs deps)) (vs.coh b)) ordered
  let c0 := (List.range mem.size).filter fun t => readable mem a0 t (bnd a0)
  let c1 := (List.range mem.size).filter fun t => readable mem a1 t (bnd a1)
  c0.flatMap fun t0 => c1.filterMap fun t1 =>
    if pairStraddles mem pairs a0 t0 t1 then none
    else
      let m0 := mem[t0]!
      let m1 := mem[t1]!
      let vs' : VState :=
        { vs with
          coh := fun b =>
            if b = a0 then max (vs.coh a0) t0
            else if b = a1 then max (vs.coh a1) t1
            else vs.coh b
          vRd := max vs.vRd (max (fwdRd vs pairs t0 m0.view) (fwdRd vs pairs t1 m1.view))
          vPreBase :=
            if acq then max vs.vPreBase (max (fwdAcq vs pairs t0 m0.view) (fwdAcq vs pairs t1 m1.view))
            else vs.vPreBase }
      some
        { th with
          regs := fun r =>
            if r = dst0 then ⟨m0.val, m0.view, t0⟩
            else if r = dst1 then ⟨m1.val, m1.view, t1⟩
            else th.regs r
          vs := vs' }


/-! ### Out-of-order issue

The view machinery above expresses relaxed behaviour on the *reader* side, which
covers load→load and store→store reordering as observed by other agents.  It
does not by itself cover an agent executing a store *before* a preceding
independent load — the reordering LB needs.  For that we let an agent issue any
instruction from its pending program, provided everything still ahead of it is a
load that cannot order it.

Only reordering past *loads* is modelled here.  Reordering past stores would be
architecturally permitted too, but the view rules already generate those
observable behaviours (SB, MP+po), so admitting it here would only duplicate
them.  Restricting to loads keeps the reorder rule small enough to audit. -/

def instrAddr : Instr → Option Address
  | .load _ a _ _ => some a
  | .store a _ _ _ => some a
  | .rmw _ a _ _ _ _ _ => some a
  -- The *base* only.  The emitter wants one address register per access, and a
  -- pair access needs exactly one; `instrAddrs` is what ordering questions use.
  | .rmwPair _ _ a _ _ _ _ _ _ _ => some a
  | .storePair a _ _ _ _ => some a
  | .loadPair _ _ a _ _ => some a
  | _ => none

/-- Every address an instruction touches.  A pair access touches two, and
    ordering questions -- "do these two instructions hit the same location?" --
    have to see both, or a same-location access to the second word could be
    reordered past it. -/
def instrAddrs : Instr → List Address
  | .load _ a _ _ => [a]
  | .store a _ _ _ => [a]
  | .rmw _ a _ _ _ _ _ => [a]
  | .rmwPair _ _ a _ _ _ _ _ _ _ => [a, a.next]
  | .storePair a _ _ _ _ => [a, a.next]
  | .loadPair _ _ a _ _ => [a, a.next]
  | _ => []

/-- The registers an instruction writes.  A pair access writes two. -/
def instrDefs : Instr → List Reg
  | .load d _ _ _ => [d]
  | .rmw d _ _ _ _ _ _ => [d]
  | .rmwPair d0 d1 _ _ _ _ _ _ _ _ => [d0, d1]
  | .loadPair d0 d1 _ _ _ => [d0, d1]
  | _ => []

/-- Do these two instructions touch disjoint sets of locations? -/
def addrsDisjoint (i j : Instr) : Bool :=
  (instrAddrs i).all fun a => !(instrAddrs j).any fun b => decide (b = a)

def instrDeps : Instr → List Reg
  | .load _ _ d _ => d
  | .store _ e d _ => d ++ (match e with | .reg r => [r] | _ => [])
  | .rmw _ _ _ e d _ _ => e.writeDeps d
  | .rmwPair _ _ _ _ _ n0 n1 d _ _ => n1.writeDeps (n0.writeDeps d)
  -- Both stored values are data dependencies, for the same reason the
  -- single-word store's is.
  | .storePair _ e0 e1 d _ =>
      d ++ (match e0 with | .reg r => [r] | _ => []) ++
           (match e1 with | .reg r => [r] | _ => [])
  | .loadPair _ _ _ d _ => d
  | .branch r => [r]
  | _ => []

/-- Only memory accesses are ever issued early.  Fences, `ISB` and branches
    must stay where the program put them: hoisting a fence above the access it
    was meant to order is exactly how this rule goes wrong.  An `STLR` is
    likewise pinned — refusing to issue it early *is* its release semantics.
    An `LDAR` may still issue early; it constrains what comes after it, which
    is handled by `mayReorder` below.

    A plain `CAS` is hoistable, which is *not* the obvious answer — it performs
    a write, and one might expect the atomicity requirement to pin it. herd7
    says otherwise: `LB+cas` is `Sometimes`, and it is only reachable if the
    CAS can be issued while an earlier independent load is still pending.  A
    `CASL` is pinned, for the same reason an `STLR` is.

    A `CASP` is hoistable on the same grounds.  Pair atomicity says the two
    words move together; it says nothing about when the pair issues, and
    `LB+casp` is the test that holds this to account.

    An `STP` and an `LDP` are exactly their single-word counterparts here.
    Single-copy atomicity is a statement about what an *observer* can see
    between the two words, and says nothing at all about issue order; treating
    a wide access as pinned would silently strengthen the model, which is the
    unsound direction. -/
def hoistable : Instr → Bool
  | .load _ _ _ _ => true
  | .store _ _ _ rel => !rel
  | .rmw _ _ _ _ _ _ rel => !rel
  | .rmwPair _ _ _ _ _ _ _ _ _ rel => !rel
  | .storePair _ _ _ _ rel => !rel
  | .loadPair _ _ _ _ _ => true
  | _ => false

/-- Does an instruction read memory? -/
def Instr.readsMem : Instr → Bool
  | .load .. | .loadPair .. | .rmw .. | .rmwPair .. => true
  | _ => false

/-- Does an instruction write memory? -/
def Instr.writesMem : Instr → Bool
  | .store .. | .storePair .. | .rmw .. | .rmwPair .. => true
  | _ => false

/-- A memory access that is neither acquire nor release. -/
def Instr.plainAcc : Instr → Bool
  | .load _ _ _ acq => !acq
  | .loadPair _ _ _ _ acq => !acq
  | .store _ _ _ rel => !rel
  | .storePair _ _ _ _ rel => !rel
  | .rmw _ _ _ _ _ acq rel => !acq && !rel
  | .rmwPair _ _ _ _ _ _ _ _ acq rel => !acq && !rel
  | _ => false

/-- (A0) **A barrier may be issued ahead of a pending plain access it does not
    order** (ARM); `none` when `ins` is not a barrier.  `DMB LD` orders the reads before it,
    `DMB ST` the writes before it, and `ISB` acts only through `vCtrl`, which only a `branch`
    raises (and a branch pins what follows it).  Without this, every barrier pinned everything
    behind it, so `W; DMB LD; W` -- which no barrier orders -- could not reorder, and
    `MP+str-dmb.ld-str+dmb.sy` came out forbidden against herd7's `Sometimes` (single words as
    well as pairs).  Issuing `DMB LD` early is exact (a store never reads `vPreBase`), and so is
    `DMB ST` (a load never reads `vRelSt`).  `DMB SY` still pins. -/
def barrierMayIssue (earlier ins : Instr) : Option Bool :=
  match ins with
  | .fence .ld => some (earlier.plainAcc && !earlier.readsMem)
  | .fence .st => some (earlier.plainAcc && !earlier.writesMem)
  | .isb => some earlier.plainAcc
  | _ => none

/-- May `ins` be issued while `earlier` is still pending ahead of it? -/
def mayReorder (arch : Arch) (earlier ins : Instr) : Bool :=
  match arch with
  | .tso =>
      -- Store→load is TSO's only relaxation: the store sits in the store
      -- buffer while the load goes to memory.  Nothing else moves.  An RMW is
      -- a locked operation and never moves in either role; no TSO test
      -- exercises this, and `wellFormed` rejects RMW on x86 (see there).
      (match ins with | .load _ _ _ _ => true | _ => false) &&
      (match earlier with
       | .store a _ _ rel =>
           !rel && (instrAddr ins).elim true fun b => decide (a ≠ b)
       | _ => false)
  | .arm =>
    (barrierMayIssue earlier ins).getD <|
    hoistable ins &&
    -- Two side conditions recur in every case below, so they are named once.
    -- `noDep`: no register dependency (address, data, or control) from what
    -- `earlier` writes into what `ins` reads.  `disj`: never reorder two
    -- accesses to the same location (SC per location).  A pair access can
    -- supply two registers to the first and two locations to the second, which
    -- is the only reason these are lists.
    (let noDep := (instrDefs earlier).all fun d => !(instrDeps ins).contains d
     let disj := addrsDisjoint earlier ins
     match earlier with
     | .load _ _ _ acq =>
         -- LDAR orders everything after it.
         !acq && noDep && disj
     | .store _ _ _ rel =>
         -- STLR orders everything after it.  A store defines no register, so
         -- `noDep` is vacuous here and is left off.
         !rel && disj
     | .rmw _ _ _ _ _ acq rel =>
         -- An RMW in the *earlier* position is both a load and a store, so it
         -- has to satisfy both of the above: an acquire or a release pins what
         -- follows, a register dependency on its result pins what follows, and
         -- same-location accesses never move past each other.
         !acq && !rel && noDep && disj
     | .rmwPair _ _ _ _ _ _ _ _ acq rel =>
         -- Identical, with two result registers and two locations.
         !acq && !rel && noDep && disj
     | .storePair _ _ _ _ rel =>
         -- A wide store is a store: `disj` now compares two locations against
         -- two, which `instrAddrs` already supplies.
         !rel && disj
     | .loadPair _ _ _ _ acq =>
         -- A wide load is a load, with two result registers.
         !acq && noDep && disj
     -- Fences, branches and ISB pin what follows them.
     | _ => false)

/-- Every instruction the agent may issue now, paired with the program that
    remains afterwards. -/
def issuable (arch : Arch) (prog : List Instr) : List (Instr × List Instr) :=
  (List.range prog.length).filterMap fun k =>
    match prog[k]? with
    | none => none
    | some ins =>
        if (prog.take k).all (fun e => mayReorder arch e ins) then
          some (ins, prog.take k ++ prog.drop (k + 1))
        else none

/-- Issue one instruction of agent `i`, returning all successors. -/
def stepThread (arch : Arch) (c : Config) (i : Nat) : List Config :=
  match c.ths[i]? with
  | none => []
  | some th =>
    (issuable arch th.prog).flatMap fun (ins, rest) =>
      -- `{ c with ... }` rather than a fresh literal, so that `pairs` survives
      -- every step that is not itself a pair write.
      let setTh (mem : Memory) (th' : Thread) : Config :=
        { c with mem := mem, ths := c.ths.set! i { th' with prog := rest } }
      match ins with
      | .load dst a deps acq =>
          (stepLoad arch c.mem c.pairs th dst a deps acq).map (setTh c.mem)
      | .store a e deps rel =>
          let (mem', th') := stepStore c.mem th a e deps rel
          [setTh mem' th']
      | .rmw dst a kind newv deps acq rel =>
          (stepRmw arch c.mem c.pairs th dst a kind newv deps acq rel).map
            fun (mem', th') => setTh mem' th'
      | .rmwPair d0 d1 a c0 c1 n0 n1 deps acq rel =>
          (stepRmwPair arch c.mem c.pairs th d0 d1 a c0 c1 n0 n1 deps acq rel).map
            fun (mem', pairs', th') =>
              { c with
                mem := mem'
                pairs := pairs'
                ths := c.ths.set! i { th' with prog := rest } }
      | .storePair a e0 e1 deps rel =>
          -- The only rule besides `stepRmwPair` that extends `pairs`, and the
          -- only line of this file that takes FEAT_LSE2.
          let (mem', pairs', th') :=
            stepStorePair c.mem c.pairs th a e0 e1 deps rel
          [{ c with
             mem := mem'
             pairs := pairs'
             ths := c.ths.set! i { th' with prog := rest } }]
      | .loadPair d0 d1 a deps acq =>
          (stepLoadPair arch c.mem c.pairs th d0 d1 a deps acq).map (setTh c.mem)
      | .fence f => [setTh c.mem (stepFence th f)]
      | .branch r =>
          -- Joins `rts` as well as `view`, for exactly `depBound`'s reason: a
          -- branch is ordered after the *read* it tests, not merely after what
          -- that read's writer published.  `Promises.lean` has done this since
          -- promising arrived (its `ctrlRts` knob); here it was missed, and
          -- `WRC+ctrl+ctrlisb` and its two siblings were the symptom.
          let vs := th.vs
          let w := max (th.regs r).view (th.regs r).rts
          [setTh c.mem { th with vs := { vs with vCtrl := max vs.vCtrl w } }]
      | .isb =>
          let vs := th.vs
          [setTh c.mem { th with vs := { vs with vPreBase := max vs.vPreBase vs.vCtrl } }]

def Config.done (c : Config) : Bool := c.ths.all fun th => th.prog.isEmpty

/-- Exhaustively explore every interleaving and every read resolution. -/
def finals (arch : Arch) (fuel : Nat) (c : Config) : List Config :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if c.done then [c]
    else
      (List.range c.ths.size).flatMap fun i =>
        (stepThread arch c i).flatMap (finals arch fuel)


/-! ## 6. Litmus harness -/

def regNat (th : Thread) (r : Reg) : Nat :=
  match (th.regs r).val with
  | .num n => n
  | _ => 999

/-- The value a finished run leaves at `a`: the value of the coherence-latest
    write to it.

    Coherence order *is* timestamp order here — `hiddenFrom` says a read is
    ordered after any later write to the same address, so same-address writes
    are totally ordered by index — which makes "coherence-latest" simply the
    last message in the array whose `loc` is `a`.  `Litmus.initMem` seeds every
    location, so the search cannot come up empty for a location the test
    declares.

    `999` for an unwritten or non-numeric location, matching `regNat`'s
    convention: a sentinel that no litmus test uses as a value, so it shows up
    as an obviously-wrong outcome rather than silently reading as zero. -/
def memNat (mem : Memory) (a : Address) : Nat :=
  match mem.foldl (fun (acc : Option Val) (m : Msg) =>
                     if m.loc = a then some m.val else acc) none with
  | some (.num n) => n
  | _ => 999

/-- What a litmus test's final condition may name.

    Registers only, until the `diy7` differential suite
    needed more: every generated cycle whose last edge is a write ends in a
    condition like `[x]=2`, and there are whole families -- coherence, `2+2W`,
    anything built from `Coe`/`Wse` -- that cannot be stated without one.
    `Parse.parseCond` used to refuse these by name rather than drop them, which
    is how the restriction stayed visible until it could be lifted. -/
inductive Obs where
  /-- `t:Xr` -- register `r` of thread `t`. -/
  | reg (t : Nat) (r : Reg)
  /-- `[x]` -- the coherence-last value at a location. -/
  | mem (a : Address)
  deriving Repr, DecidableEq, Inhabited

structure Litmus where
  name : String
  /-- Which architecture's rules to run, and which `.litmus` subdirectory the
      reference numbers below came from. -/
  arch : Arch := .arm
  /-- One program per agent. -/
  threads : List (List Instr)
  /-- Locations to seed with an initial `num 0` write. -/
  locs : List Address
  /-- The outcome of interest: what to read out of a finished run. -/
  obs : List Obs
  /-- The values making up the outcome of interest. -/
  target : List Nat
  /-- Is `target` architecturally allowed?  Cross-checked against `herd7` with
      the bundled `aarch64.cat` / `x86tso.cat`; see `litmus/`. -/
  archAllows : Bool
  /-- Number of distinct final states herd7 reports.  Checking the whole state
      *set* rather than just `target` is a much stronger test: it is what
      caught `LB+data` being vacuous. -/
  states : Option Nat := none
  /-- Set when we already know the model disagrees with the architecture. -/
  xfail : Bool := false

def Litmus.initMem (L : Litmus) : Memory :=
  (L.locs.map fun a => (⟨a, Val.num 0, 0⟩ : Msg)).toArray

def Litmus.start (L : Litmus) : Config :=
  { mem := L.initMem, ths := (L.threads.map Thread.mk').toArray }

/-- Read one observation out of a finished configuration. -/
def Obs.read (c : Config) : Obs → Nat
  | .reg i r => regNat c.ths[i]! r
  | .mem a   => memNat c.mem a

def Litmus.outcomes (L : Litmus) : List (List Nat) :=
  let fuel := 64
  let fs := finals L.arch fuel L.start
  let raw := fs.map fun c => L.obs.map (Obs.read c)
  raw.foldl (fun acc o => if acc.contains o then acc else acc ++ [o]) []

structure Result where
  name : String
  arch : Arch
  observed : List (List Nat)
  modelAllows : Bool
  archAllows : Bool
  states : Option Nat
  xfail : Bool

def Litmus.run (L : Litmus) : Result :=
  let os := L.outcomes
  { name := L.name, arch := L.arch, observed := os, modelAllows := os.contains L.target,
    archAllows := L.archAllows, states := L.states, xfail := L.xfail }


def Result.statesOk (r : Result) : Bool :=
  match r.states with
  | none => true
  | some n => r.observed.length == n

def Result.agrees (r : Result) : Bool :=
  (r.modelAllows == r.archAllows) && r.statesOk

def Result.status (r : Result) : String :=
  if r.agrees then (if r.xfail then "XPASS" else "ok   ")
  else if r.xfail then "xfail"
  else "FAIL "

def Result.render (r : Result) : String :=
  let say (b : Bool) := if b then "allowed" else "forbidden"
  let a := match r.arch with | .arm => "arm" | .tso => "tso"
  s!"{r.status} | [{a}] {r.name}\n" ++
  s!"        model: {say r.modelAllows}   arch: {say r.archAllows}\n" ++
  s!"        outcomes: {repr r.observed}"

/-! ## 7. The tests -/

def x : Address := ⟨0, 0⟩
def y : Address := ⟨1, 0⟩

def two : List Address := [x, y]

def one : Val := Val.num 1

/-- Writer side of MP: `x := 1; dmb ishst; y := 1`. -/
def mpWriter : List Instr :=
  [ .store x (.const one) [] false
  , .fence .st
  , .store y (.const one) [] false ]

/-- Writer side of MP with no barrier at all. -/
def mpWriterPo : List Instr :=
  [ .store x (.const one) [] false
  , .store y (.const one) [] false ]

/-- Every MP variant here has herd7 state count 4 when the outcome is allowed
    and 3 when it is forbidden -- the forbidden one is exactly the missing
    state. -/
def mpLitmus (nm : String) (w : List Instr) (reader : List Instr)
    (archAllows : Bool) : Litmus :=
  { name := nm, threads := [w, reader], locs := two
    obs := [.reg 1 0, .reg 1 1], target := [1, 0], archAllows := archAllows
    states := some (if archAllows then 4 else 3) }

/-- No reader-side ordering: allowed. -/
def mp_po : Litmus :=
  mpLitmus "MP+dmb.st+po" mpWriter
    [ .load 0 y [] false, .load 1 x [] false ] true

/-- Address dependency orders load→load on ARM: forbidden. -/
def mp_addr : Litmus :=
  mpLitmus "MP+dmb.st+addr" mpWriter
    [ .load 0 y [] false, .load 1 x [0] false ] false

/-- Control dependency does NOT order load→load (speculation): allowed.
    This is the single most important test in the suite -- it is what makes
    the "check length then compute address" slice protocol unsafe. -/
def mp_ctrl : Litmus :=
  mpLitmus "MP+dmb.st+ctrl" mpWriter
    [ .load 0 y [] false, .branch 0, .load 1 x [] false ] true

/-- ...but ctrl+isb does: forbidden. -/
def mp_ctrlisb : Litmus :=
  mpLitmus "MP+dmb.st+ctrlisb" mpWriter
    [ .load 0 y [] false, .branch 0, .isb, .load 1 x [] false ] false

/-- Reader-side dmb ishld: forbidden. -/
def mp_dmbld : Litmus :=
  mpLitmus "MP+dmb.st+dmb.ld" mpWriter
    [ .load 0 y [] false, .fence .ld, .load 1 x [] false ] false

/-- No writer-side barrier: a reader-side dependency is not enough. -/
def mp_po_addr : Litmus :=
  mpLitmus "MP+po+addr" mpWriterPo
    [ .load 0 y [] false, .load 1 x [0] false ] true

/-- Same, with a reader-side fence: still allowed, the writer is unordered. -/
def mp_po_dmbld : Litmus :=
  mpLitmus "MP+po+dmb.ld" mpWriterPo
    [ .load 0 y [] false, .fence .ld, .load 1 x [] false ] true

/-- STLR/LDAR: forbidden. -/
def mp_rel_acq : Litmus :=
  { name := "MP+stlr+ldar"
    threads :=
      [ [ .store x (.const one) [] false, .store y (.const one) [] true ]
      , [ .load 0 y [] true, .load 1 x [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 1], target := [1, 0], archAllows := false
    states := some 3 }

/-- Coherence of read-read: forbidden (SC per location). -/
def corr : Litmus :=
  { name := "CoRR"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 0 x [] false, .load 1 x [] false ] ]
    locs := [x], obs := [.reg 1 0, .reg 1 1], target := [1, 0], archAllows := false
    states := some 3 }

/-- Coherence of read-write: forbidden.  A load cannot read its own thread's
    po-later store.  This test caught a real bug: the promise machine let the
    load read the thread's own *promise* of that store, and the fulfil guard
    (`ob ≤ t`, now `ob < t`) then accepted it.  See `Promises.stepStore`. -/
def corw1 : Litmus :=
  { name := "CoRW1"
    threads := [ [ .load 0 x [] false, .store x (.const one) [] false ] ]
    locs := [x], obs := [.reg 0 0], target := [1], archAllows := false
    states := some 1 }

/-- CoRW1 with a second writer, so the final value of `x` is observed too.
    The same bug admitted `(1,2)` and `(1,1)`. -/
def corw1b : Litmus :=
  { name := "CoRW1b"
    threads :=
      [ [ .load 0 x [] false, .store x (.const one) [] false ]
      , [ .store x (.const (.num 2)) [] false ] ]
    locs := [x], obs := [.reg 0 0, .mem x], target := [1, 1], archAllows := false
    states := some 3 }

/-- Store buffering: allowed. -/
def sb : Litmus :=
  { name := "SB"
    threads :=
      [ [ .store x (.const one) [] false, .load 0 y [] false ]
      , [ .store y (.const one) [] false, .load 0 x [] false ] ]
    locs := two, obs := [.reg 0 0, .reg 1 0], target := [0, 0], archAllows := true
    states := some 4 }

/-- Store buffering with full fences: forbidden. -/
def sb_dmb : Litmus :=
  { name := "SB+dmb.sy"
    threads :=
      [ [ .store x (.const one) [] false, .fence .sy, .load 0 y [] false ]
      , [ .store y (.const one) [] false, .fence .sy, .load 0 x [] false ] ]
    locs := two, obs := [.reg 0 0, .reg 1 0], target := [0, 0], archAllows := false
    states := some 3 }

/-- Load buffering: allowed.  Requires an agent to issue its store before a
    preceding independent load. -/
def lb : Litmus :=
  { name := "LB"
    threads :=
      [ [ .load 0 y [] false, .store x (.const one) [] false ]
      , [ .load 0 x [] false, .store y (.const one) [] false ] ]
    locs := two, obs := [.reg 0 0, .reg 1 0], target := [1, 1], archAllows := true
    states := some 4 }

/-- A control dependency DOES order load→store: forbidden.  This is the
    direction the slice protocol's length check actually gets right. -/
def lb_ctrl : Litmus :=
  { name := "LB+ctrl"
    threads :=
      [ [ .load 0 y [] false, .branch 0, .store x (.const one) [] false ]
      , [ .load 0 x [] false, .branch 0, .store y (.const one) [] false ] ]
    locs := two, obs := [.reg 0 0, .reg 1 0], target := [1, 1], archAllows := false
    states := some 3 }

/-- Data dependency orders load→store: forbidden.

    The store writes a *constant* `1` carrying a preserved dependency on the
    loaded register -- i.e. the `EOR W2,W0,W0; ADD W2,W2,#1` idiom, which is
    what the herd7 `LB+data` test does.  Writing `.reg 0` instead would store
    whatever was loaded, so a `1` could never propagate and the test would pass
    vacuously; the herd7 state-count cross-check is what exposed that. -/
def lb_data : Litmus :=
  { name := "LB+data"
    threads :=
      [ [ .load 0 y [] false, .store x (.const one) [0] false ]
      , [ .load 0 x [] false, .store y (.const one) [0] false ] ]
    locs := two, obs := [.reg 0 0, .reg 1 0], target := [1, 1], archAllows := false
    states := some 3 }

/-- IRIW with no barriers: allowed, because each observer may reorder its own
    two loads. -/
def iriw : Litmus :=
  { name := "IRIW"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .store y (.const one) [] false ]
      , [ .load 0 x [] false, .load 1 y [] false ]
      , [ .load 0 y [] false, .load 1 x [] false ] ]
    locs := two, obs := [.reg 2 0, .reg 2 1, .reg 3 0, .reg 3 1]
    target := [1, 0, 1, 0], archAllows := true, states := some 16 }

/-- IRIW with full fences between the reads: FORBIDDEN on ARMv8 and x86, but
    ALLOWED on POWER.  This is the litmus test that distinguishes a
    multi-copy-atomic architecture from a non-multi-copy-atomic one, and hence
    the test that licenses collapsing all remote threads into one agent. -/
def iriw_dmb : Litmus :=
  { name := "IRIW+dmb.sy"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .store y (.const one) [] false ]
      , [ .load 0 x [] false, .fence .sy, .load 1 y [] false ]
      , [ .load 0 y [] false, .fence .sy, .load 1 x [] false ] ]
    locs := two, obs := [.reg 2 0, .reg 2 1, .reg 3 0, .reg 3 1]
    target := [1, 0, 1, 0], archAllows := false, states := some 15 }

/-! ### Read-modify-write

Six tests here (the fetch-ops have their own section below), and the
reference verdicts were taken from herd7 *before* `stepRmw` was written — the point of this file is that the rules follow the
architecture rather than the other way round, and RMW is the case where
reconstructing from intuition is most dangerous.

The set is chosen so that each test can only pass for one reason:

* `CASAtomic` / `SWPAtomic` — atomicity itself, in both flavours.  Two agents
  race to take the same location from 0; both succeeding is forbidden, and the
  two states are the two serialisations.  Everything a lock needs is here.
* `SB+cas`, `MP+cas+po` — a plain `CAS` orders *nothing*.  Atomicity is not
  fencing, and a model that conflated them would forbid these.
* `MP+casl+ldar` — and the release/acquire forms do order, so the ordering
  machinery still reaches an RMW.
* `LB+cas` — a plain `CAS` may be issued early.  This is the one that
  contradicts the obvious guess. -/

/-- CAS 0→1 at `a`, leaving the value read in register `d`. -/
def casTake (d : Reg) (a : Address) (v : Nat) (acq rel : Bool := false) : Instr :=
  .rmw d a (.cas (Val.num 0)) (.const (Val.num v)) [] acq rel

/-- Unconditional swap of `v` into `a`, leaving the value read in `d`. -/
def swapIn (d : Reg) (a : Address) (v : Nat) : Instr :=
  .rmw d a .swap (.const (Val.num v)) [] false false

/-- **The atomicity test.**  Two agents CAS the same location from 0.  Both
    reading 0 would mean both succeeded, which is exactly what an RMW forbids
    and exactly what makes a lock a lock. -/
def cas_atomic : Litmus :=
  { name := "CASAtomic"
    threads := [ [ casTake 0 x 1 ], [ casTake 0 x 2 ] ]
    locs := [x], obs := [.reg 0 0, .reg 1 0], target := [0, 0], archAllows := false
    states := some 2 }

/-- The same, with unconditional swaps.  Worth having separately: `SWP` always
    writes, so it exercises the atomicity condition without the value
    comparison being able to mask a bug in it. -/
def swp_atomic : Litmus :=
  { name := "SWPAtomic"
    threads := [ [ swapIn 0 x 1 ], [ swapIn 0 x 2 ] ]
    locs := [x], obs := [.reg 0 0, .reg 1 0], target := [0, 0], archAllows := false
    states := some 2 }

/-- A plain CAS is not a fence: store buffering survives it. -/
def sb_cas : Litmus :=
  { name := "SB+cas"
    threads :=
      [ [ casTake 0 x 1, .load 4 y [] false ]
      , [ casTake 0 y 1, .load 4 x [] false ] ]
    locs := two, obs := [.reg 0 4, .reg 1 4], target := [0, 0], archAllows := true
    states := some 4 }

/-- Nor does it order a preceding store: message passing still leaks.  Contrast
    `MP+dmb.st+po`, which is the same test with a real fence. -/
def mp_cas : Litmus :=
  { name := "MP+cas+po"
    threads :=
      [ [ .store x (.const one) [] false, casTake 0 y 1 ]
      , [ .load 0 y [] false, .load 4 x [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 4], target := [1, 0], archAllows := true
    states := some 4 }

/-- But `CASL` publishes and `LDAR` acquires, so the release/acquire pair works
    through an RMW exactly as it does through a plain store. -/
def mp_casl_ldar : Litmus :=
  { name := "MP+casl+ldar"
    threads :=
      [ [ .store x (.const one) [] false, casTake 0 y 1 false true ]
      , [ .load 0 y [] true, .load 4 x [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 4], target := [1, 0], archAllows := false
    states := some 3 }

/-! #### `aob`: an acquire reading an RMW's write is ordered after the RMW's read

ARM's `aob` (herd7 `aarch64hwreqs.cat`, via `rmw` then `lrs`): the *read*
of an RMW is ordered before a Load-Acquire that reads the RMW's write, own
thread included.  The 2018 model Promising-ARM was validated against had the
stronger clause ordering the RMW's *write* before the acquire --
which `SB+swp-rfi-ldar+dmb.sy` would have forbidden; ARM has since relaxed it,
and that test is allowed.  `MP+stlr+swp-rfi-ldar` is what the current clause
forbids, and what the read view `rv` in `stepRmw`'s message delivers; the
`ldr-str` control shows it is the RMW that does it. -/

def sb_swp_rfi_ldar : Litmus :=
  { name := "SB+swp-rfi-ldar+dmb.sy"
    threads :=
      [ [ swapIn 0 x 1, .load 1 x [] true, .load 2 y [] false ]
      , [ .store y (.const one) [] false, .fence .sy, .load 0 x [] false ] ]
    locs := two, obs := [.reg 0 1, .reg 0 2, .reg 1 0], target := [1, 0, 0]
    archAllows := true, states := some 4 }

def mp_stlr_swp_rfi_ldar : Litmus :=
  { name := "MP+stlr+swp-rfi-ldar"
    threads :=
      [ [ .store y (.const one) [] false, .store x (.const one) [] true ]
      , [ swapIn 0 x 2, .load 1 x [] true, .load 2 y [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 1, .reg 1 2], target := [1, 2, 0]
    archAllows := false, states := some 4 }

def mp_stlr_str_rfi_ldar : Litmus :=
  { name := "MP+stlr+ldr-str-rfi-ldar"
    threads :=
      [ [ .store y (.const one) [] false, .store x (.const one) [] true ]
      , [ .load 0 x [] false, .store x (.const (Val.num 2)) [] false
        , .load 1 x [] true, .load 2 y [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 1, .reg 1 2], target := [1, 2, 0]
    archAllows := true, states := some 5 }

def wrc_stlr_swp_ldar : Litmus :=
  { name := "WRC+stlr+swp+ldar"
    threads :=
      [ [ .store y (.const one) [] false, .store x (.const one) [] true ]
      , [ swapIn 0 x 2 ]
      , [ .load 0 x [] true, .load 1 y [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 2 0, .reg 2 1], target := [1, 2, 0]
    archAllows := false, states := some 9 }

/-- **The counter-intuitive one.**  A plain CAS may be issued while an earlier
    independent load is still outstanding, so load buffering survives it.  The
    natural guess is that atomicity pins the RMW in place; herd7 says it does
    not, and this test is what keeps the model honest about that. -/
def lb_cas : Litmus :=
  { name := "LB+cas"
    threads :=
      [ [ .load 4 x [] false, casTake 0 y 1 ]
      , [ .load 4 y [] false, casTake 0 x 1 ] ]
    locs := two, obs := [.reg 0 4, .reg 1 4], target := [1, 1], archAllows := true
    states := some 4 }

/-! ### Fetch-ops

The LSE fetch-ops (`LDADD`, `LDSET`, `LDCLR`, `LDEOR`) are `SWP` with a computed
new value, and the tests are the `SWP`/`CAS` set re-run on `LDADD`, with
`XADDValue` and `BitOpsValue` added for what is new: the value written.  The
verdicts are herd7 master's (`ad8e24e`); Promising-ARM does not model these
instructions (its caveats say so), and the exclusive pair is the analogue.

`LB+xadd` is the one that exercises the promise machine's `latestVal`: the
fetch-add's write is promised before its own read happens, with the value the
read will return already decided by `rmwAdjacent`. -/

/-- Fetch-add `v` at `a`, leaving the value read in register `d`. -/
def xaddBy (d : Reg) (a : Address) (v : Nat) (acq rel : Bool := false) : Instr :=
  .rmw d a .add (.const (Val.num v)) [] acq rel

/-- Two fetch-adds of 1 from 0: both reading 0 is forbidden. -/
def xadd_atomic : Litmus :=
  { name := "XADDAtomic"
    threads := [ [ xaddBy 0 x 1 ], [ xaddBy 0 x 1 ] ]
    locs := [x], obs := [.reg 0 0, .reg 1 0], target := [0, 0], archAllows := false
    states := some 2 }

/-- The value written is `old + v`: after a `+1` and a `+2` the location holds
    3, never 1 (a lost update) -- which a swap would produce. -/
def xadd_value : Litmus :=
  { name := "XADDValue"
    threads := [ [ xaddBy 0 x 1 ], [ xaddBy 0 x 2 ] ]
    locs := [x], obs := [.mem x], target := [1], archAllows := false
    states := some 1 }

/-- `LDSET 6` then `LDCLR ~3` (the emission of `and 3`) leaves `6 &&& 3 = 2`;
    the other order leaves 6.  Checks the `and`-as-`LDCLR` spelling. -/
def bitops_value : Litmus :=
  { name := "BitOpsValue"
    threads :=
      [ [ .rmw 0 x .or (.const (Val.num 6)) [] false false ]
      , [ .rmw 0 x .and (.const (Val.num 3)) [] false false ] ]
    locs := [x], obs := [.mem x], target := [2], archAllows := true
    states := some 2 }

/-- A plain `LDADD` is not a fence, as a plain `CAS` is not. -/
def sb_xadd : Litmus :=
  { name := "SB+xadd"
    threads :=
      [ [ xaddBy 0 x 1, .load 4 y [] false ]
      , [ xaddBy 0 y 1, .load 4 x [] false ] ]
    locs := two, obs := [.reg 0 4, .reg 1 4], target := [0, 0], archAllows := true
    states := some 4 }

def mp_xadd : Litmus :=
  { name := "MP+xadd+po"
    threads :=
      [ [ .store x (.const one) [] false, xaddBy 0 y 1 ]
      , [ .load 0 y [] false, .load 4 x [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 4], target := [1, 0], archAllows := true
    states := some 4 }

/-- `LDADDL` publishes and `LDAR` acquires. -/
def mp_xaddl_ldar : Litmus :=
  { name := "MP+xaddl+ldar"
    threads :=
      [ [ .store x (.const one) [] false, xaddBy 0 y 1 false true ]
      , [ .load 0 y [] true, .load 4 x [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 4], target := [1, 0], archAllows := false
    states := some 3 }

/-- A plain `LDADD` may be issued early, as a plain `CAS` may. -/
def lb_xadd : Litmus :=
  { name := "LB+xadd"
    threads :=
      [ [ .load 4 x [] false, xaddBy 0 y 1 ]
      , [ .load 4 y [] false, xaddBy 0 x 1 ] ]
    locs := two, obs := [.reg 0 4, .reg 1 4], target := [1, 1], archAllows := true
    states := some 4 }

/-- A register operand is a data dependency of the write, as `WRC+casdata+addr`
    has it for a `CAS`. -/
def wrc_xadddata_addr : Litmus :=
  { name := "WRC+xadddata+addr"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 4 x [] false, .rmw 2 y .add (.reg 4) [] false false ]
      , [ .load 0 y [] false, .load 1 x [0] false ] ]
    locs := two, obs := [.reg 1 4, .reg 2 0, .reg 2 1], target := [1, 1, 0]
    archAllows := false, states := some 5 }

/-! ### Pair RMW

These run against `cats/aarch64-pair.cat`, not the bundled model, and with
`-variant mixed`.  Stock `aarch64.cat` decomposes a `CASP` into independent
per-word events and lets a *successful* one partially commit; the custom file
adds two axioms that stop it.  The probe runs behind those axioms were scratch
and are not checked in; every axiom in the cat file carries its witness inline.

They live in their own suite and their own directory because of those two
flags: running the other 22 tests under `-variant mixed` would be a different
experiment, and mixing them would hide which model said what.

One trap governs the choice of outcomes.  A `CASP` writes the loaded pair back
into its compare registers **whether or not it succeeded**, so "both threads
report the expected value" does not mean "both succeeded".  That confound is
what made the original investigation nearly conclude the opposite of the truth.
`CASPAtomic` is stated in the form where the two coincide -- a thread that read
`(0,0)` when `(0,0)` is what it was comparing against did succeed -- and the
genuinely discriminating test is `CASPReadTear`, which is about the *read*. -/

/-- The second word of each pair. -/
def xn : Address := x.next
def yn : Address := y.next

def pairTwo : List Address := [x, xn]

/-- `CASP` of `(0,0)` → `(v,v)` at the pair based at `a`, reading into the
    register pair `d, d+1`. -/
def caspTake (d : Reg) (a : Address) (v : Nat) (acq rel : Bool := false) :
    Instr :=
  .rmwPair d (d + 1) a (Val.num 0) (Val.num 0) (.const (Val.num v)) (.const (Val.num v)) []
    acq rel

/-- Non-vacuity: an uncontended `CASP` succeeds and reports the pair it
    compared against.  Without this the two forbidden tests below could be
    passing because nothing happens at all. -/
def casp_solo : Litmus :=
  { name := "CASPSolo"
    threads := [ [ caspTake 2 x 1 ] ]
    locs := pairTwo, obs := [.reg 0 2, .reg 0 3], target := [0, 0]
    archAllows := true
    states := some 1 }

/-- **Pair exclusion.**  Two agents `CASP` the same pair from `(0,0)`.  Both
    reporting `(0,0)` means both compared equal, hence both succeeded, which
    atomicity forbids.

    Note this one is `Never` even under *stock* herd7, because per-location
    adjacency at the first word is already enough to forbid it.  It is here for
    the state set, not because it discriminates. -/
def casp_atomic : Litmus :=
  { name := "CASPAtomic"
    threads := [ [ caspTake 2 x 1 ], [ caspTake 2 x 2 ] ]
    locs := pairTwo, obs := [.reg 0 2, .reg 0 3, .reg 1 2, .reg 1 3]
    target := [0, 0, 0, 0]
    archAllows := false
    states := some 2 }

/-- **The discriminating test.**  `P0` reports the *old* first word and the
    *new* second word -- a torn read, one half of `P1`'s atomic update.

    Stock herd7 says `Sometimes`.  The repaired model says `Never`, and so does
    this model: `stepRmwPair`'s `pairStraddles` filter is what rules it out, and
    deleting that filter makes this state reachable.  A failing pair CAS is
    otherwise just two ordinary loads, which would be free to tear. -/
def casp_read_tear : Litmus :=
  { name := "CASPReadTear"
    threads := [ [ caspTake 2 x 1 ], [ caspTake 2 x 2 ] ]
    locs := pairTwo, obs := [.reg 0 2, .reg 0 3], target := [0, 2]
    archAllows := false
    states := some 2 }

/-- A plain `CASP` is hoistable, exactly as a plain `CAS` is: pair atomicity
    says the two words move together, not that the pair cannot issue early.
    This is `LB+cas` with both RMWs widened, and it is the test that would
    catch `hoistable` being made conservative for pairs. -/
def lb_casp : Litmus :=
  { name := "LB+casp"
    threads :=
      [ [ .load 6 x [] false, caspTake 2 y 1 ]
      , [ .load 7 y [] false, caspTake 2 x 1 ] ]
    locs := [x, xn, y, yn], obs := [.reg 0 6, .reg 1 7], target := [1, 1]
    archAllows := true
    states := some 4 }

/-- `WRC+casdata+addr` with the RMW widened: `P1`'s `CASP` takes its new pair
    from the register its load of `x` filled, so both writes carry a data
    dependency on that load, and an observer that sees the pair and then reads
    `x` through an address dependency must see `x = 1`.  Forbidden.

    This is what `new0`/`new1` being `Expr`s is for.  With constants the
    write would be unordered after the load and the outcome allowed, as the
    control below shows. -/
def wrc_caspdata_addr : Litmus :=
  { name := "WRC+caspdata+addr"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 4 x [] false
        , .rmwPair 2 3 y (Val.num 0) (Val.num 0) (.reg 4) (.reg 4) [] false false ]
      , [ .load 0 y [] false, .load 1 x [0] false ] ]
    locs := [x, y, yn], obs := [.reg 1 4, .reg 2 0, .reg 2 1], target := [1, 1, 0]
    archAllows := false, states := some 5 }

/-- The control: the same with no ordering on the observer is allowed, so the
    test above is forbidden by the pair's data dependency and not by something
    blunter. -/
def wrc_caspdata_po : Litmus :=
  { name := "WRC+caspdata+po"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 4 x [] false
        , .rmwPair 2 3 y (Val.num 0) (Val.num 0) (.reg 4) (.reg 4) [] false false ]
      , [ .load 0 y [] false, .load 1 x [] false ] ]
    locs := [x, y, yn], obs := [.reg 1 4, .reg 2 0, .reg 2 1], target := [1, 1, 0]
    archAllows := true, states := some 6 }

/-! #### Single-copy atomicity against a reader that is not a pair

The three above ask whether a pair RMW tears against *another pair access*.
These two ask the harder question: whether an observer using two ordinary,
separately-issued loads can catch a pair RMW half-done.  Architecturally it
cannot -- a `CASP` on an aligned 16-byte quantity is single-copy atomic, so
having observed either word you have observed both -- and the two tests differ
only in which word the observer reads first.

They are a **pair of tests and must be read as one**.  Before `pairTop`, this
model reported `Never` for `CASPOrderedRead` and `Sometimes` for
`CASPOrderedReadSwapped`; the `Never` was an artifact of the pair's two
messages sitting at adjacent timestamps `t`, `t+1`, so that reading the second
word drags `vRd` past both and reading the first word does not.  Either one
alone is therefore worthless as evidence: the first passes for the wrong
reason, and only the second detects the bug.

Stock herd7 says `Sometimes` to both, because it decomposes `CASP` into two
writes that are not in one `sca-class`; `cats/aarch64-pair.cat`'s
`pair-external` axiom is what repairs that.  So these are also the two tests
that justify the second axiom in that file. -/

/-- Read the pair's *second* word, full barrier, read its first.  Seeing the
    new second word and the old first word is a torn observation. -/
def casp_ordered_read : Litmus :=
  { name := "CASPOrderedRead"
    threads :=
      [ [ caspTake 2 x 1 ]
      , [ .load 6 xn [] false, .fence .sy, .load 7 x [] false ] ]
    locs := pairTwo, obs := [.reg 1 6, .reg 1 7], target := [1, 0]
    archAllows := false
    states := some 3 }

/-- The same with the words swapped, which is the one that had to be written
    down for the previous test to mean anything. -/
def casp_ordered_read_swapped : Litmus :=
  { name := "CASPOrderedReadSwapped"
    threads :=
      [ [ caspTake 2 x 1 ]
      , [ .load 6 x [] false, .fence .sy, .load 7 xn [] false ] ]
    locs := pairTwo, obs := [.reg 1 6, .reg 1 7], target := [1, 0]
    archAllows := false
    states := some 3 }

/-- **A pair RMW may only fulfil a *pair* promise.**  `P0`'s later plain
    stores of `1` to `x` and `xn` make two *single* promises available at
    adjacent timestamps, with exactly the values the `CASP` writes.  If the
    `CASP` could discharge them, its write would be a pair `pairTop` does not
    know about, and the observer -- the `CASPOrderedReadSwapped` reader --
    could read the new `x` from it and still the initial `xn`.  Herd forbids
    that: reading `x` from the `CASP` is ruled out by pair atomicity and
    reading it from the later store by the writer's `DMB`.  (Stock herd7
    says `Sometimes`, for the `CASPOrderedReadSwapped` reason: only
    `cats/aarch64-pair.cat` forbids the first way.)

    Found by reading `Promises.stepRmwPair`, not by a failing test: the
    promise machine reached `[0, 0, 1, 0]` here until its fulfil branch
    required the first timestamp to be in `pairs`; the stage-1 machine, which
    has no promises, never did. -/
def casp_fulfil_singles : Litmus :=
  { name := "CASPFulfilSingles"
    threads :=
      [ [ caspTake 2 x 1, .fence .sy, .store x (.const one) [] false
        , .store xn (.const one) [] false ]
      , [ .load 6 x [] false, .fence .sy, .load 7 xn [] false ] ]
    locs := pairTwo, obs := [.reg 0 2, .reg 0 3, .reg 1 6, .reg 1 7]
    target := [0, 0, 1, 0]
    archAllows := false
    states := some 3 }

/-! #### What the pair RMW leaves behind

The five tests above all ask what some *thread* saw.  That was not a choice:
until `Litmus.obs` grew a `.mem` case (§6 `Obs`), a final condition could only
name registers, so "is the pair torn **in memory** afterwards?" was a question
this harness could not put.  These three put it.

The question is not a restatement of the read-side ones.  A torn *read* is one
agent's view of a pair that is whole everywhere else; torn *memory* is a pair
that no subsequent reader can ever see whole again, however it reads.  Stock
herd7 permits the second, and it takes a location-valued condition to say so.

They are also the third instance of §6.12's lesson, now on the write side: of
the two contention probes, the one that looks like the obvious statement of
atomicity is the one that proves nothing. -/

/-- Non-vacuity for the two below, and the only direct test of `memNat`:
    an uncontended `CASP` leaves *both* words written.  If the coherence-latest
    lookup were wrong this is where it shows, because the two forbidden tests
    would then be passing on a misread rather than on atomicity. -/
def casp_write_solo : Litmus :=
  { name := "CASPWriteSolo"
    threads := [ [ caspTake 2 x 1 ] ]
    locs := pairTwo, obs := [.mem x, .mem xn], target := [1, 1]
    archAllows := true
    states := some 1 }

/-- **The probe that proves nothing by itself.**  Two `CASP`s contend; the
    condition asks for `P0`'s first word beside `P1`'s second.

    Stock herd7 also says `Never` here -- per-location coherence is already
    enough to forbid that particular cross -- so the *verdict* does not
    discriminate at all.  The state count does, and by a wide margin: stock
    reports six final states, of which four are torn, and the repaired model
    reports two.  Written alone this test would have read as confirmation; it
    is here as the control for the next one, and as the concrete case that
    justifies `Litmus.states` existing at all. -/
def casp_write_tear : Litmus :=
  { name := "CASPWriteTear"
    threads := [ [ caspTake 2 x 1 ], [ caspTake 2 x 2 ] ]
    locs := pairTwo, obs := [.mem x, .mem xn], target := [1, 2]
    archAllows := false
    states := some 2 }

/-- **The discriminating test.**  The same two `CASP`s, asking for `P0`'s first
    word beside an *unwritten* second word -- one half of an update that
    succeeded.

    Stock herd7 says `Sometimes`.  `cats/aarch64-pair.cat` says `Never`, and so
    does this model, though for a reason worth stating plainly: `stepRmwPair`
    pushes both messages in a single step, so write-side tearing is impossible
    *by construction* here rather than by a rule that could be ablated away.
    The test therefore carries no evidence about a rule; what it pins is the
    representation, and the disagreement with stock herd7. -/
def casp_write_partial : Litmus :=
  { name := "CASPWritePartial"
    threads := [ [ caspTake 2 x 1 ], [ caspTake 2 x 2 ] ]
    locs := pairTwo, obs := [.mem x, .mem xn], target := [1, 0]
    archAllows := false
    states := some 2 }

/-! ### x86-TSO

The same shapes again, under `Arch.tso`.  Reference numbers come from
`litmus/x86_64/` via herd7, using `cats/x86tso-mixed-rmw.cat` rather than a
bundled model -- see the RMW block below for why.  The whole
point of this first block is that exactly one of them is `Sometimes`: TSO's
only relaxation is store→load, so `SB` is allowed and everything else is
forbidden.

Note the tests are *not* re-encoded — they are the same `Instr` lists as the
ARM versions, minus the dependency/`ISB` variants, which have no x86 analogue
(x86 has no notion of dependency ordering, and does not need one because the
orderings those variants buy are already guaranteed). -/

/-- Message passing needs no barriers at all on x86: forbidden. -/
def x86_mp : Litmus :=
  { name := "MP", arch := .tso
    threads := [ mpWriterPo, [ .load 0 y [] false, .load 1 x [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 1], target := [1, 0], archAllows := false
    states := some 3 }

/-- Store buffering: allowed.  The one relaxation TSO has. -/
def x86_sb : Litmus :=
  { name := "SB", arch := .tso
    threads :=
      [ [ .store x (.const one) [] false, .load 0 y [] false ]
      , [ .store y (.const one) [] false, .load 0 x [] false ] ]
    locs := two, obs := [.reg 0 0, .reg 1 0], target := [0, 0], archAllows := true
    states := some 4 }

/-- ...and `MFENCE` is what takes it away: forbidden. -/
def x86_sb_mfence : Litmus :=
  { name := "SB+mfence", arch := .tso
    threads :=
      [ [ .store x (.const one) [] false, .fence .sy, .load 0 y [] false ]
      , [ .store y (.const one) [] false, .fence .sy, .load 0 x [] false ] ]
    locs := two, obs := [.reg 0 0, .reg 1 0], target := [0, 0], archAllows := false
    states := some 3 }

/-- Load buffering: forbidden, with no dependency needed.  Contrast `LB` on
    ARM, where it takes a `ctrl` or `data` dependency to forbid this. -/
def x86_lb : Litmus :=
  { name := "LB", arch := .tso
    threads :=
      [ [ .load 0 y [] false, .store x (.const one) [] false ]
      , [ .load 0 x [] false, .store y (.const one) [] false ] ]
    locs := two, obs := [.reg 0 0, .reg 1 0], target := [1, 1], archAllows := false
    states := some 3 }

/-- Coherence of read-read: forbidden. -/
def x86_corr : Litmus :=
  { name := "CoRR", arch := .tso
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 0 x [] false, .load 1 x [] false ] ]
    locs := [x], obs := [.reg 1 0, .reg 1 1], target := [1, 0], archAllows := false
    states := some 3 }

/-- IRIW: forbidden even with no fences, because TSO never reorders load→load.
    On ARM this needs `dmb.sy` between the reads; the bare version is allowed
    there.  x86 is (like ARMv8) multi-copy atomic, so the two-agent abstraction
    is sound on both targets. -/
def x86_iriw : Litmus :=
  { name := "IRIW", arch := .tso
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .store y (.const one) [] false ]
      , [ .load 0 x [] false, .load 1 y [] false ]
      , [ .load 0 y [] false, .load 1 x [] false ] ]
    locs := two, obs := [.reg 2 0, .reg 2 1, .reg 3 0, .reg 3 1]
    target := [1, 0, 1, 0], archAllows := false, states := some 15 }

/-- IRIW with `MFENCE`: forbidden, and the fences buy nothing -- same 15 states
    as the unfenced version.  Included precisely to pin that down. -/
def x86_iriw_mfence : Litmus :=
  { name := "IRIW+mfence", arch := .tso
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .store y (.const one) [] false ]
      , [ .load 0 x [] false, .fence .sy, .load 1 y [] false ]
      , [ .load 0 y [] false, .fence .sy, .load 1 x [] false ] ]
    locs := two, obs := [.reg 2 0, .reg 2 1, .reg 3 0, .reg 3 1]
    target := [1, 0, 1, 0], archAllows := false, states := some 15 }

/-! #### Read-modify-write on x86

The same shapes as the ARM RMW block, and the interesting thing is how many of
the verdicts *differ*.  Atomicity is identical on the two architectures --
`CASAtomic` and `SWPAtomic` give 2 states on both.  The ordering an RMW
carries with it is not: on ARM a plain `CAS` orders nothing, so `SB+cas`,
`MP+cas+po` and `LB+cas` are all `Sometimes`; on x86 a locked
read-modify-write is a full barrier, so all three are forbidden.  Keeping both
sets is what stops "atomic" and "ordering" being quietly conflated.

There is no x86 analogue of `MP+casl+ldar`: TSO has no weaker RMW to contrast
a release one against.

`SB+cas`, `MP+cas+po` and `LB+cas` are *character-for-character* the same
`Litmus` values as their ARM counterparts apart from `arch`, `archAllows` and
`states` -- same threads, same registers, same observations.  That is the
point: the inputs are identical, so the differing verdicts can only be the
architecture talking.  (This is why `x86Reg` carries eight registers rather
than four; at four, these tests had to be renumbered and the comparison was
muddier than it needed to be.)

Reference numbers come from herd7 via `cats/x86tso-mixed-rmw.cat`, which is
the bundled mixed-size model with `rmw` added to `lob`.  The bundled x86
models are *not* usable as an oracle here -- both of them allow a third state
in `SWPAtomic` in which each swap reads the other's value.  See the header
comment in that file. -/

/-- Atomicity, via `LOCK CMPXCHG`.  Both agents reading 0 would mean both took
    the location; forbidden, and the two states are the two serialisations. -/
def x86_cas_atomic : Litmus :=
  { name := "CASAtomic", arch := .tso
    threads := [ [ casTake 0 x 1 ], [ casTake 0 x 2 ] ]
    locs := [x], obs := [.reg 0 0, .reg 1 0], target := [0, 0], archAllows := false
    states := some 2 }

/-- Atomicity again, unconditionally, via `XCHG`.  This is precisely the test
    herd7's bundled x86 models get wrong, so it is the one that justifies
    shipping a corrected `.cat` at all. -/
def x86_swp_atomic : Litmus :=
  { name := "SWPAtomic", arch := .tso
    threads := [ [ swapIn 0 x 1 ], [ swapIn 0 x 2 ] ]
    locs := [x], obs := [.reg 0 0, .reg 1 0], target := [0, 0], archAllows := false
    states := some 2 }

/-- **Differs from ARM.**  `SB+cas` is `Sometimes` on ARM -- a plain `CAS` is
    not a fence there.  On x86 the lock is a fence, so store buffering does
    not survive it. -/
def x86_sb_cas : Litmus :=
  { name := "SB+cas", arch := .tso
    threads :=
      [ [ casTake 0 x 1, .load 4 y [] false ]
      , [ casTake 0 y 1, .load 4 x [] false ] ]
    locs := two, obs := [.reg 0 4, .reg 1 4], target := [0, 0], archAllows := false
    states := some 3 }

/-- **Differs from ARM** for the same reason, though x86 forbids this shape
    even without the CAS (`MP`).  It earns its place by pinning the state
    count: adding a locked RMW must not add states. -/
def x86_mp_cas : Litmus :=
  { name := "MP+cas+po", arch := .tso
    threads :=
      [ [ .store x (.const one) [] false, casTake 0 y 1 ]
      , [ .load 0 y [] false, .load 4 x [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 4], target := [1, 0], archAllows := false
    states := some 3 }

/-- **Differs from ARM, and this is the sharpest of the three.**  `LB+cas` is
    the ARM test that contradicts the obvious guess: there, a plain `CAS` may
    be issued while an earlier independent load is still outstanding.  On x86
    it may not.  A model that made `hoistable` architecture-independent would
    fail exactly one of these two tests. -/
def x86_lb_cas : Litmus :=
  { name := "LB+cas", arch := .tso
    threads :=
      [ [ .load 4 x [] false, casTake 0 y 1 ]
      , [ .load 4 y [] false, casTake 0 x 1 ] ]
    locs := two, obs := [.reg 0 4, .reg 1 4], target := [1, 1], archAllows := false
    states := some 3 }

/-! #### Fetch-ops on x86

herd7's x86 has no `xadd` (see `x86Thread`), so these are checked through
`lock addq`, and none observes the RMW's result register.  `XADDValue` is the
atomicity test in the only form herd7 can state: the final value.  A locked
RMW is a full barrier, so the three ordering tests are forbidden, as the `cas`
ones are. -/

def x86_xadd_value : Litmus :=
  { name := "XADDValue", arch := .tso
    threads := [ [ xaddBy 0 x 1 ], [ xaddBy 0 x 2 ] ]
    locs := [x], obs := [.mem x], target := [1], archAllows := false
    states := some 1 }

def x86_sb_xadd : Litmus :=
  { name := "SB+xadd", arch := .tso
    threads :=
      [ [ xaddBy 0 x 1, .load 4 y [] false ]
      , [ xaddBy 0 y 1, .load 4 x [] false ] ]
    locs := two, obs := [.reg 0 4, .reg 1 4], target := [0, 0], archAllows := false
    states := some 3 }

def x86_mp_xadd : Litmus :=
  { name := "MP+xadd+po", arch := .tso
    threads :=
      [ [ .store x (.const one) [] false, xaddBy 0 y 1 ]
      , [ .load 0 y [] false, .load 4 x [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 4], target := [1, 0], archAllows := false
    states := some 3 }

def x86_lb_xadd : Litmus :=
  { name := "LB+xadd", arch := .tso
    threads :=
      [ [ .load 4 x [] false, xaddBy 0 y 1 ]
      , [ .load 4 y [] false, xaddBy 0 x 1 ] ]
    locs := two, obs := [.reg 0 4, .reg 1 4], target := [1, 1], archAllows := false
    states := some 3 }

/-- `WRC` with an `xchgq` relay whose new value is the value it loaded.  The
    register is both the new value and the destination, which is how `xchgq`
    is written; the observer seeing `y = 1` is the evidence the value flowed.
    Forbidden, as every `WRC` is on x86. -/
def x86_wrc_xchgdata : Litmus :=
  { name := "WRC+xchgdata", arch := .tso
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 0 x [] false, .rmw 0 y .swap (.reg 0) [] false false ]
      , [ .load 0 y [] false, .load 1 x [] false ] ]
    locs := two, obs := [.reg 2 0, .reg 2 1], target := [1, 0]
    archAllows := false, states := some 3 }

/-- The same with `lock cmpxchgq`, whose source operand is the loaded register.
    Forbidden. -/
def x86_wrc_cmpxchgdata : Litmus :=
  { name := "WRC+cmpxchgdata", arch := .tso
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 1 x [] false, .rmw 0 y (.cas (Val.num 0)) (.reg 1) [] false false ]
      , [ .load 0 y [] false, .load 1 x [] false ] ]
    locs := two, obs := [.reg 1 1, .reg 2 0, .reg 2 1], target := [1, 1, 0]
    archAllows := false, states := some 5 }

/-! ### Three threads, and why two are not enough

`WRC` is the shape that found `depBound`, and both variants are in the suite for
that reason.  With only two threads a dependency that orders against *the write
it observed* and one that orders only against *what that write published* are
indistinguishable, because there is one writer and the two coincide.  A relay
thread separates them: `P1`'s plain store of `y` publishes nothing, so a `P2`
ordered only by publication is free to miss `P0`'s write of `x`.

Eight generated shapes in this family were wrong before the fix (§10); these
two are the hand-written witnesses, one per corrected rule. -/

/-- Write-to-read causality, data dependency on the relay and address
    dependency on the observer: forbidden.  The witness for `depBound`. -/
def wrc_data_addr : Litmus :=
  { name := "WRC+data+addr"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 0 x [] false, .store y (.const one) [0] false ]
      , [ .load 0 y [] false, .load 1 x [0] false ] ]
    locs := two, obs := [.reg 1 0, .reg 2 0, .reg 2 1], target := [1, 1, 0]
    archAllows := false, states := some 7 }

/-- The same with control dependencies, the observer's reinforced by `ISB`:
    forbidden.  The witness for `branch` joining `rts`. -/
def wrc_ctrl_ctrlisb : Litmus :=
  { name := "WRC+ctrl+ctrlisb"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 0 x [] false, .branch 0, .store y (.const one) [] false ]
      , [ .load 0 y [] false, .branch 0, .isb, .load 1 x [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 2 0, .reg 2 1], target := [1, 1, 0]
    archAllows := false, states := some 7 }

/-- The control on both: with no ordering at all on the observer the outcome is
    architecturally *allowed*, so the two above are not forbidden for some
    blunter reason. -/
def wrc_ctrl_po : Litmus :=
  { name := "WRC+ctrl+po"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 0 x [] false, .branch 0, .store y (.const one) [] false ]
      , [ .load 0 y [] false, .load 1 x [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 2 0, .reg 2 1], target := [1, 1, 0]
    archAllows := true, states := some 8 }

/-! ### A register as an RMW's new value

`CAS Ws,Wt,[Xn]` and `SWP Ws,Wt,[Xn]` take the new value from a register, and
when that register was loaded the write has a genuine data dependency on the
load: the value read is the value stored, with no `EOR`/`ADD` idiom.  These are
the `WRC` relay again with the relay's store replaced by such an RMW, so that
the write half's data operand (`Instr.rmw`'s `newv : Expr`) is checked against
herd7 rather than assumed.  The observer reading `y = 1` already proves the
value flowed, since nothing else writes 1 to `y`. -/

/-- The relay swaps the value it read into `y`: forbidden, like
    `WRC+data+addr`. -/
def wrc_swpdata_addr : Litmus :=
  { name := "WRC+swpdata+addr"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 0 x [] false, .rmw 1 y .swap (.reg 0) [] false false ]
      , [ .load 0 y [] false, .load 1 x [0] false ] ]
    locs := two, obs := [.reg 1 0, .reg 2 0, .reg 2 1], target := [1, 1, 0]
    archAllows := false, states := some 5 }

/-- The same through a compare-and-swap from 0, which always succeeds here:
    forbidden. -/
def wrc_casdata_addr : Litmus :=
  { name := "WRC+casdata+addr"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 0 x [] false, .rmw 1 y (.cas (Val.num 0)) (.reg 0) [] false false ]
      , [ .load 0 y [] false, .load 1 x [0] false ] ]
    locs := two, obs := [.reg 1 0, .reg 2 0, .reg 2 1], target := [1, 1, 0]
    archAllows := false, states := some 5 }

/-- The control: with no ordering on the observer the outcome is allowed, so
    the two above are forbidden by the data dependency and not by something
    blunter. -/
def wrc_swpdata_po : Litmus :=
  { name := "WRC+swpdata+po"
    threads :=
      [ [ .store x (.const one) [] false ]
      , [ .load 0 x [] false, .rmw 1 y .swap (.reg 0) [] false false ]
      , [ .load 0 y [] false, .load 1 x [] false ] ]
    locs := two, obs := [.reg 1 0, .reg 2 0, .reg 2 1], target := [1, 1, 0]
    archAllows := true, states := some 6 }

/-! ### The wide access (FEAT_LSE2)

`litmus/aarch64-lse2/` already holds four hand-written probes whose subject is
the *cat file*.  These are the other half, and the difference is what they are
about: these are emitted from the `Instr` lists the model runs, so they check
**our machine** against `cats/aarch64-lse2.cat` rather than that cat file
against stock herd7.  §7 item 6.

Three of the six correspond to a hand-written probe and one does not.
`WideOrderedReadSwapped` is new: the hand-written set has a swapped twin
for the `LDP` reader (`I-ldp-stp-swapped`) and **none for the separate-`LDR`
reader** (`K-ldp-stp-sep`), which is the very shape §6.12's asymmetry showed up
in.  Written alone, the unswapped one would be the probe that proves nothing.

The controls are load-bearing in both directions.  `WidePlainPairRead` says a
wide *load* does not make two ordinary stores atomic; without it the rule could
be a blanket prohibition on adjacent writes and every other test here would
still pass. -/

/-- Store `1` to both words of `x` in one instruction. -/
def stpOnes : Instr := .storePair x (.const one) (.const one) [] false

/-- Non-vacuity, and the analogue of `casp_write_solo`: an uncontended wide
    store leaves *both* words written.  Without this the forbidden tests below
    could be passing because nothing was ever written. -/
def wide_store_solo : Litmus :=
  { name := "WideStoreSolo"
    threads := [ [ stpOnes ] ]
    locs := pairTwo, obs := [.mem x, .mem xn], target := [1, 1]
    archAllows := true
    states := some 1 }

/-- `STP` against `LDP`: the reader sees the whole store or none of it.  The
    generated counterpart of `I-ldp-stp`. -/
def wide_pair_read : Litmus :=
  { name := "WidePairRead"
    threads := [ [ stpOnes ], [ .loadPair 4 5 x [] false ] ]
    locs := pairTwo, obs := [.reg 1 4, .reg 1 5], target := [1, 0]
    archAllows := false
    states := some 2 }

/-- The same with the condition swapped.  Both orientations must flip together,
    which is the standing requirement §6.12 left behind. -/
def wide_pair_read_swapped : Litmus :=
  { name := "WidePairReadSwapped"
    threads := [ [ stpOnes ], [ .loadPair 4 5 x [] false ] ]
    locs := pairTwo, obs := [.reg 1 4, .reg 1 5], target := [0, 1]
    archAllows := false
    states := some 2 }

/-- The mixed-size case, and the one the model has to get right by a different
    route: the reader is two *ordinary* loads ordered by a full barrier, so
    nothing about it is a pair.  What forbids tearing here is `pairTop`, not
    `pairStraddles`.  The generated counterpart of `K-ldp-stp-sep`. -/
def wide_ordered_read : Litmus :=
  { name := "WideOrderedRead"
    threads :=
      [ [ stpOnes ]
      , [ .load 6 xn [] false, .fence .sy, .load 7 x [] false ] ]
    locs := pairTwo, obs := [.reg 1 6, .reg 1 7], target := [1, 0]
    archAllows := false
    states := some 3 }

/-- **The probe the hand-written set is missing.**  The same two ordinary loads
    in the other order.  `pairTop` raises `vRd` past the pair's *second* word
    when the *first* is read, so the two directions are forbidden by visibly
    different arithmetic, and only writing both says the rule is not an
    artifact of word order. -/
def wide_ordered_read_swapped : Litmus :=
  { name := "WideOrderedReadSwapped"
    threads :=
      [ [ stpOnes ]
      , [ .load 6 x [] false, .fence .sy, .load 7 xn [] false ] ]
    locs := pairTwo, obs := [.reg 1 6, .reg 1 7], target := [1, 0]
    archAllows := false
    states := some 3 }

/-- **Control: two ordinary stores still tear.**  Same reader as
    `WidePairRead`, and the writer is the only thing that changed.  A model that
    forbade adjacent writes outright would pass every test above and fail this
    one, which is the whole reason it is here.  The generated counterpart of
    `J-plain-str-tear`. -/
def wide_plain_pair_read : Litmus :=
  { name := "WidePlainPairRead"
    threads :=
      [ [ .store x (.const one) [] false, .store xn (.const one) [] false ]
      , [ .loadPair 4 5 x [] false ] ]
    locs := pairTwo, obs := [.reg 1 4, .reg 1 5], target := [0, 1]
    archAllows := true
    states := some 4 }

/-! ### Store forwarding, and what a successful `CAS` returns

Three permissions a model without them gets wrong in the strict direction, and
controls that keep each from becoming a licence.

**A read of the thread's own plain write is forwarded** (`VState.fwd`,
`ownFwd`).  It contributes the write's forwarding view -- what the store's
address and data depended on -- rather than its timestamp, so it orders
nothing the store did not: herd7's `rfi` is not in `ob`.  `SB+rfi-pos`,
`SB+rfi-dmb.ld` and `SB+dmb.st-rfi-ldar+dmb.sy` are `Sometimes`; a model that
joined the timestamp forbids all three.  The two `data-rfi` controls are why
the view is the *forwarding* view and not nothing: the forwarded value still
carries the store's data dependency, and through it the earlier read.

**A successful non-acquire `CAS` returns the value with no dependency**
(herd7's `aarch64_cas_ok`), so an address dependency on it is no dependency
on the read: `MP+dmb.sy+cas-addrRs` and `MP+dmb.sy+casl-addrRs` are
`Sometimes`.  `CASA`/`CASAL` and a plain `LDR` are the controls.

Not in the suite, and herd7-only evidence for the same rule: the
`MP+dmb.sy+ldr-{cas,casl,casa,casal}-addrRs` set, where the comparand register
is *loaded* (`LDR W0,[y]; CAS W0,W2,[z]` with `z=1`) and the later read is
addressed through it.  herd7 7.58 (stock, `aarch64-pair.cat` and
`aarch64-lse2.cat` alike) says `Sometimes` for `cas`, `casl` and `casa` and
`Never` for `casal` and for the no-`CAS` control `MP+dmb.sy+ldr-addr-ctl` --
so a successful non-acquire `CAS` drops the comparand's *old* dependency too,
which is why the register is zeroed rather than kept.  They cannot be written
here: `Instr`'s `CAS` compares against a constant, so a loaded comparand is
not expressible (§9 would emit a `MOV` over it, and §10 rejects a `CAS` whose
compare register has no known value), and `Litmus` seeds every location with
0, not 1.

**`lock cmpxchg` is a barrier before its read too**, failed or not:
`SB+cmpxchg-fails` is forbidden on x86. -/

/-- A third location, for the shapes that need one.  Not `z`: a global of that
    name would capture an auto-bound implicit in every file that opens this
    namespace. -/
def locZ : Address := ⟨2, 0⟩

def locsXYZ : List Address := [x, y, locZ]

/-- **Allowed.**  Each thread reads its own write, then the other location,
    with only a `DMB LD` between.  The `DMB LD` orders the second read after
    the first, but the first is forwarded, so neither is ordered after the
    store. -/
def sb_rfi_dmbld : Litmus :=
  { name := "SB+rfi-dmb.ld"
    threads :=
      [ [ .store x (.const one) [] false, .load 2 x [] false, .fence .ld
        , .load 4 y [] false ]
      , [ .store y (.const one) [] false, .load 2 y [] false, .fence .ld
        , .load 4 x [] false ] ]
    locs := two, obs := [.reg 0 2, .reg 0 4, .reg 1 2, .reg 1 4]
    target := [1, 0, 1, 0], archAllows := true, states := some 4 }

/-- **Allowed.**  An acquire read of the thread's own write orders the later
    read after the acquire, but the acquire is forwarded, so not after the
    store it read -- and the `DMB ST` before that store orders stores only. -/
def sb_dmbst_rfi_ldar : Litmus :=
  { name := "SB+dmb.st-rfi-ldar+dmb.sy"
    threads :=
      [ [ .store x (.const one) [] false, .fence .st, .store y (.const one) [] false
        , .load 2 y [] true, .load 4 locZ [] false ]
      , [ .store locZ (.const one) [] false, .fence .sy, .load 2 x [] false ] ]
    locs := locsXYZ, obs := [.reg 0 2, .reg 0 4, .reg 1 2]
    target := [1, 0, 0], archAllows := true, states := some 4 }

/-- **Control, forbidden.**  The forwarded value carries the store's data
    dependency on the first read, so the acquire is ordered after it.  The
    dependency is `LB+data`'s (a constant with the read's register in `deps`,
    `EOR`+`ADD` in the litmus file), not a register store: promise candidates
    are exact only for constant stores (`Promises.regStoreReport`). -/
def mp_dmbsy_data_rfi_ldar : Litmus :=
  { name := "MP+dmb.sy+data-rfi-ldar"
    threads :=
      [ [ .store x (.const one) [] false, .fence .sy, .store y (.const one) [] false ]
      , [ .load 0 y [] false, .store locZ (.const one) [0] false, .load 7 locZ [] true
        , .load 5 x [] false ] ]
    locs := locsXYZ, obs := [.reg 1 0, .reg 1 7, .reg 1 5]
    target := [1, 1, 0], archAllows := false, states := some 3 }

/-- **Control, forbidden.**  The same with a plain read and a `DMB LD`. -/
def mp_dmbsy_data_rfi_ldr : Litmus :=
  { name := "MP+dmb.sy+data-rfi-ldr"
    threads :=
      [ [ .store x (.const one) [] false, .fence .sy, .store y (.const one) [] false ]
      , [ .load 0 y [] false, .store locZ (.const one) [0] false, .load 7 locZ [] false
        , .fence .ld, .load 5 x [] false ] ]
    locs := locsXYZ, obs := [.reg 1 0, .reg 1 7, .reg 1 5]
    target := [1, 1, 0], archAllows := false, states := some 3 }

/-- The reader of the `CAS` comparand tests: a `CAS` of `y` from 1 to 2, then
    a read of `x` addressed through the comparand register. -/
def casAddrRs (nm : String) (acq rel : Bool) (allowed : Bool) : Litmus :=
  { name := nm
    threads :=
      [ [ .store x (.const one) [] false, .fence .sy, .store y (.const one) [] false ]
      , [ .rmw 0 y (.cas (Val.num 1)) (.const (Val.num 2)) [] acq rel
        , .load 5 x [0] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 5], target := [1, 0]
    archAllows := allowed, states := some (if allowed then 4 else 3) }

/-- **Allowed.**  A successful non-acquire `CAS` returns the value read with
    no dependency (herd7's `aarch64_cas_ok`), so the address dependency
    through `W0` orders nothing. -/
def mp_dmbsy_cas_addrRs : Litmus := casAddrRs "MP+dmb.sy+cas-addrRs" false false true

/-- **Allowed.**  A release orders earlier accesses, not later ones. -/
def mp_dmbsy_casl_addrRs : Litmus := casAddrRs "MP+dmb.sy+casl-addrRs" false true true

/-- **Control, forbidden.**  An acquire `CAS` writes the value read. -/
def mp_dmbsy_casa_addrRs : Litmus := casAddrRs "MP+dmb.sy+casa-addrRs" true false false

/-- **Control, forbidden.** -/
def mp_dmbsy_casal_addrRs : Litmus := casAddrRs "MP+dmb.sy+casal-addrRs" true true false

/-- **Control, forbidden.**  A plain read in place of the `CAS`. -/
def mp_dmbsy_ldr_addr : Litmus :=
  { name := "MP+dmb.sy+ldr-addr"
    threads :=
      [ [ .store x (.const one) [] false, .fence .sy, .store y (.const one) [] false ]
      , [ .load 0 y [] false, .load 5 x [0] false ] ]
    locs := two, obs := [.reg 1 0, .reg 1 5], target := [1, 0]
    archAllows := false, states := some 3 }

/-- **Allowed on x86.**  TSO orders read→read, but a read of the thread's own
    buffered store is satisfied from the buffer, before the store is visible,
    so the later read can still miss the other thread's store. -/
def x86_sb_rfi_pos : Litmus :=
  { name := "SB+rfi-pos", arch := .tso
    threads :=
      [ [ .store x (.const one) [] false, .load 0 x [] false, .load 4 y [] false ]
      , [ .store y (.const one) [] false, .load 0 y [] false, .load 4 x [] false ] ]
    locs := two, obs := [.reg 0 0, .reg 0 4, .reg 1 0, .reg 1 4]
    target := [1, 0, 1, 0], archAllows := true, states := some 4 }

/-- **Forbidden on x86.**  Both compares fail, so neither writes; the lock
    still drains the buffer before the read. -/
def x86_sb_cmpxchg_fails : Litmus :=
  { name := "SB+cmpxchg-fails", arch := .tso
    threads :=
      [ [ .store x (.const one) [] false
        , .rmw 0 y (.cas (Val.num 5)) (.const (Val.num 2)) [] false false ]
      , [ .store y (.const one) [] false
        , .rmw 0 x (.cas (Val.num 5)) (.const (Val.num 2)) [] false false ] ]
    locs := two, obs := [.reg 0 0, .reg 1 0], target := [0, 0]
    archAllows := false, states := some 3 }

def armSuite : List Litmus :=
  [ mp_po, mp_addr, mp_ctrl, mp_ctrlisb, mp_dmbld, mp_po_addr, mp_po_dmbld
  , mp_rel_acq, corr, corw1, corw1b, sb, sb_dmb, lb, lb_ctrl, lb_data, iriw, iriw_dmb
  , wrc_data_addr, wrc_ctrl_ctrlisb, wrc_ctrl_po
  , cas_atomic, swp_atomic, sb_cas, mp_cas, mp_casl_ldar, lb_cas
  , wrc_swpdata_addr, wrc_casdata_addr, wrc_swpdata_po
  , sb_swp_rfi_ldar, mp_stlr_swp_rfi_ldar, mp_stlr_str_rfi_ldar, wrc_stlr_swp_ldar
  , xadd_atomic, xadd_value, bitops_value, sb_xadd, mp_xadd, mp_xaddl_ldar, lb_xadd
  , wrc_xadddata_addr
  , sb_rfi_dmbld, sb_dmbst_rfi_ldar, mp_dmbsy_data_rfi_ldar, mp_dmbsy_data_rfi_ldr
  , mp_dmbsy_cas_addrRs, mp_dmbsy_casl_addrRs, mp_dmbsy_casa_addrRs
  , mp_dmbsy_casal_addrRs, mp_dmbsy_ldr_addr ]

def tsoSuite : List Litmus :=
  [ x86_mp, x86_sb, x86_sb_mfence, x86_lb, x86_corr, x86_iriw
  , x86_iriw_mfence
  , x86_cas_atomic, x86_swp_atomic, x86_sb_cas, x86_mp_cas, x86_lb_cas
  , x86_wrc_xchgdata, x86_wrc_cmpxchgdata
  , x86_xadd_value, x86_sb_xadd, x86_mp_xadd, x86_lb_xadd
  , x86_sb_rfi_pos, x86_sb_cmpxchg_fails ]

/-- Validated against `cats/aarch64-pair.cat` under `-variant mixed`, so these
    are emitted to their own directory and checked separately.  They are still
    `Arch.arm` tests and still run in `suite`; it is only the *reference* that
    differs. -/
def pairSuite : List Litmus :=
  [ casp_solo, casp_atomic, casp_read_tear, lb_casp
  , wrc_caspdata_addr, wrc_caspdata_po
  , casp_ordered_read, casp_ordered_read_swapped, casp_fulfil_singles
  , casp_write_solo, casp_write_tear, casp_write_partial ]

/-! ### Promised wide writes (B4)

A plain `STP` may be promised and fulfilled, both words at once, exactly as a `CASP` may.  Until
B4 `Promises.stepStorePair` was append-only and `LB` with `STP` writers came out forbidden there
while herd7 (lse2, pair and stock cats) says `Sometimes`; none of the tests above promised a wide
write, so item 1 never saw it.  The `MP` tests are the stage-1 half (A0, `barrierMayIssue`): a
`DMB LD` between two writes orders neither, single words or pairs.  The last two are
`refGap`: see there. -/

def b4StpX : Instr := .storePair x (.const one) (.const one) [] false
def b4StpY : Instr := .storePair y (.const one) (.const one) [] false
def b4Pairs : List Address := [x, xn, y, yn]
def b4MpRd : List Instr := [ .loadPair 6 7 y [] false, .fence .sy, .load 5 x [] false ]
def b4MpRdS : List Instr := [ .load 6 y [] false, .fence .sy, .load 5 x [] false ]

/-- LB, `LDP` readers, `STP` writers (Kraken's `LB+ldp-stp`). -/
def lb_ldp_stp : Litmus :=
  { name := "LBldpstp"
    threads := [ [ .loadPair 6 7 x [] false, b4StpY ], [ .loadPair 6 7 y [] false, b4StpX ] ]
    locs := b4Pairs, obs := [.reg 0 6, .reg 1 6], target := [1, 1]
    archAllows := true, states := some 4 }

/-- LB, `LDR` readers, `STP` writers. -/
def lb_ldr_stp : Litmus :=
  { name := "LBldrstp"
    threads := [ [ .load 6 x [] false, b4StpY ], [ .load 7 y [] false, b4StpX ] ]
    locs := b4Pairs, obs := [.reg 0 6, .reg 1 7], target := [1, 1]
    archAllows := true, states := some 4 }

/-- LB, one side `STP`, the other a plain `STR`. -/
def lb_ldr_stp_str : Litmus :=
  { name := "LBldrstpstr"
    threads := [ [ .load 6 x [] false, b4StpY ], [ .load 7 y [] false, .store x (.const one) [] false ] ]
    locs := b4Pairs, obs := [.reg 0 6, .reg 1 7], target := [1, 1]
    archAllows := true, states := some 4 }

/-- The control: `DMB LD` before both pair stores orders each read before its write. -/
def lb_dmbld_stp : Litmus :=
  { name := "LBdmbldstp"
    threads := [ [ .loadPair 6 7 x [] false, .fence .ld, b4StpY ], [ .loadPair 6 7 y [] false, .fence .ld, b4StpX ] ]
    locs := b4Pairs, obs := [.reg 0 6, .reg 1 6], target := [1, 1]
    archAllows := false, states := some 3 }

/-- One-sided: only `P0` fenced. -/
def lb_dmbld_stp_one : Litmus :=
  { name := "LBdmbldstpone"
    threads := [ [ .loadPair 6 7 x [] false, .fence .ld, b4StpY ], [ .loadPair 6 7 y [] false, b4StpX ] ]
    locs := b4Pairs, obs := [.reg 0 6, .reg 1 6], target := [1, 1]
    archAllows := true, states := some 4 }

/-- One-sided: `P0` fenced `STP`, `P1` unfenced plain `STR`. -/
def lb_dmbld_stp_str : Litmus :=
  { name := "LBdmbldstpstr"
    threads := [ [ .loadPair 6 7 x [] false, .fence .ld, b4StpY ], [ .load 7 y [] false, .store x (.const one) [] false ] ]
    locs := b4Pairs, obs := [.reg 0 6, .reg 1 7], target := [1, 1]
    archAllows := true, states := some 4 }

/-- MP, `STR; STP` writer: the `STP` must be promised (stage 2) or issued early (stage 1). -/
def mp_str_stp : Litmus :=
  { name := "MPstrstp"
    threads := [ [ .store x (.const one) [] false, b4StpY ], b4MpRd ]
    locs := b4Pairs, obs := [.reg 1 6, .reg 1 5], target := [1, 0]
    archAllows := true, states := some 4 }

/-- A `DMB LD` between the two writes orders neither (A0). -/
def mp_str_dmbld_stp : Litmus :=
  { name := "MPstrdmbldstp"
    threads := [ [ .store x (.const one) [] false, .fence .ld, b4StpY ], b4MpRd ]
    locs := b4Pairs, obs := [.reg 1 6, .reg 1 5], target := [1, 0]
    archAllows := true, states := some 4 }

/-- The same with single words: the stage-1 gap was never about pairs. -/
def mp_str_dmbld_str : Litmus :=
  { name := "MPstrdmbldstr"
    threads := [ [ .store x (.const one) [] false, .fence .ld, .store y (.const one) [] false ], b4MpRdS ]
    locs := b4Pairs, obs := [.reg 1 6, .reg 1 5], target := [1, 0]
    archAllows := true, states := some 4 }

/-- And with an `ISB`, which without a control dependency orders nothing. -/
def mp_str_isb_str : Litmus :=
  { name := "MPstrisbstr"
    threads := [ [ .store x (.const one) [] false, .isb, .store y (.const one) [] false ], b4MpRdS ]
    locs := b4Pairs, obs := [.reg 1 6, .reg 1 5], target := [1, 0]
    archAllows := true, states := some 4 }

/-- `refGap`: the `CASP`'s read is ordered before the `STP`, its write is not. -/
def mp_casp_dmbld_stp : Litmus :=
  { name := "MPcaspdmbldstp"
    threads := [ [ caspTake 2 x 1, .fence .ld, b4StpY ], b4MpRd ]
    locs := b4Pairs, obs := [.reg 1 6, .reg 1 5], target := [1, 0]
    archAllows := true, states := some 4, xfail := true }

/-- `refGap`, single words: `SWP; DMB LD; STR`. -/
def mp_swp_dmbld_str : Litmus :=
  { name := "MPswpdmbldstr"
    threads := [ [ .rmw 2 x .swap (.const one) [] false false, .fence .ld, .store y (.const one) [] false ], b4MpRdS ]
    locs := b4Pairs, obs := [.reg 1 6, .reg 1 5], target := [1, 0]
    archAllows := true, states := some 4, xfail := true }

/-- Pair guard: a plain `STR` matching word 0 of a promised `CASP` must not discharge it. -/
def g1_casp_single : Litmus :=
  { name := "GOneCaspSingle"
    threads := [ [ .load 6 y [] false, .store x (.const one) [] false, caspTake 2 x 1 ],
                 [ .loadPair 6 7 x [] false, .store y (.const one) [] false ] ]
    locs := b4Pairs, obs := [.reg 0 6, .reg 1 6, .reg 1 7], target := [1, 1, 0]
    archAllows := true, states := some 4 }

def b4Tests : List Litmus :=
  [ lb_ldp_stp, lb_ldr_stp, lb_ldr_stp_str, lb_dmbld_stp, lb_dmbld_stp_one, lb_dmbld_stp_str
  , mp_str_stp, mp_str_dmbld_stp, mp_str_dmbld_str, mp_str_isb_str
  , mp_casp_dmbld_stp, mp_swp_dmbld_str, g1_casp_single ]

/-- Validated against `cats/aarch64-lse2.cat`, and **only** against it: these
    are the tests that assume FEAT_LSE2, so running them against
    `cats/aarch64-pair.cat` would report tearing and be right to.  That is not a
    weakness of the group, it is what it is for -- the separation is the same
    one the two cat files draw, for the same reason (§6.16).

    Still `Arch.arm`, and still in `suite`, so `containment` and the report
    cover them like everything else.  Only the reference differs. -/
def wideSuite : List Litmus :=
  [ wide_store_solo
  , wide_pair_read, wide_pair_read_swapped
  , wide_ordered_read, wide_ordered_read_swapped
  , wide_plain_pair_read ] ++ b4Tests

def suite : List Litmus := armSuite ++ tsoSuite ++ pairSuite ++ wideSuite

/-- (A0) **Where this machine knowingly over-forbids** (the `xfail` tests): an `RMW` (`SWP`, `CAS`,
    `CASP`), then `DMB LD`, then a write.  The barrier orders the RMW's read before the write but
    not its write, and an RMW here is one atomic step, so the write cannot be split off and issued
    early; doing that safely needs promises (`Promises.lean` gets these right).  `Promises`'s
    item 1 compares these against herd7's state counts instead of against this machine. -/
def refGap : List String := ["MPcaspdmbldstp", "MPswpdmbldstr"]

#guard refGap.all fun n => suite.any fun L => L.name == n && L.xfail
#guard suite.all fun L => !L.xfail || refGap.contains L.name
#guard refGap.all fun n => suite.all fun L => L.name != n || !L.run.agrees

/-! ## 8. TSO ⊆ ARM

The reason to have both architectures in one model is so that a proof done
against `arm` is also a proof about x86.  That needs `behaviours arm ⊇
behaviours tso`, which is *not* automatic from "TSO has fewer reorderings".
Two things get in the way.  The rule sets differ in the message views stores
publish, and a stronger publication rule could in principle make some outcome
reachable under `tso` that `arm` cannot produce.  And TSO's locked RMW performs
a `.sy` fence that ARM's does not, so it is an *extra* step rather than a
restricted one -- a TSO post-state is not in general a state the corresponding
ARM step produces, which rules out matching the runs step for step.

This is the testable shadow of that claim: run each `tso` test's programs under
the `arm` rules too, and report any outcome `tso` admits that `arm` does not.
A real theorem (a view-refinement simulation, not a lockstep one) is a later
stage; until then this at least fails loudly if the containment breaks on a
shape we care about. -/

structure Containment where
  name : String
  /-- Outcomes reachable under TSO but not under ARM.  Must be empty. -/
  escapes : List (List Nat)

def Litmus.containment (L : Litmus) : Containment :=
  let underTso := ({ L with arch := .tso } : Litmus).outcomes
  let underArm := ({ L with arch := .arm } : Litmus).outcomes
  { name := L.name, escapes := underTso.filter fun o => !underArm.contains o }

def Containment.ok (c : Containment) : Bool := c.escapes.isEmpty

def Containment.render (c : Containment) : String :=
  if c.ok then s!"ok    | tso ⊆ arm: {c.name}"
  else s!"FAIL  | tso ⊆ arm: {c.name}  escapes: {repr c.escapes}"

def report : String :=
  let rs := suite.map Litmus.run
  let body := String.intercalate "\n" (rs.map Result.render)
  let bad := rs.filter fun r => !r.agrees && !r.xfail
  let gaps := rs.filter fun r => !r.agrees && r.xfail
  let cs := tsoSuite.map Litmus.containment
  let cbody := String.intercalate "\n" (cs.map Containment.render)
  let cbad := cs.filter fun c => !c.ok
  body ++ "\n\n" ++ cbody ++
  s!"\n\n{rs.length} tests, {bad.length} failing, {gaps.length} known gaps" ++
  s!"\n{cs.length} containment checks, {cbad.length} failing"

/-! ## 9. Emitting `.litmus` files

Until now every test existed *twice*: as an `Instr` list here, and as assembly
in `litmus/`.  Nothing connected them, so the two could drift — and they did.
`LB+data` passed vacuously for exactly that reason: the Lean version stored the
loaded value while the assembly stored a constant carrying a dependency, so the
Lean test could not have observed the outcome it claimed to be checking.  The
state-count comparison caught it, but only by luck; the two descriptions were
never required to be the same test.

So the assembly is generated from the `Instr` lists.  There is now one
description of each test, `check-herd.sh` runs herd7 on what this emitter
produces, and drift is impossible rather than merely unlikely.

Register allocation is fixed and dumb:

  * Lean register `r` → `W{r}` / `X{r}`, so the `exists` clause names exactly
    the registers the model's `obs` field names.  Caps Lean registers at 8.
  * `W8`, `W9` → scratch for dependency idioms.
  * `X10` → scratch for a computed address.
  * `X14`… → one per location per thread, holding that location's address.

`Litmus.wellFormed` rejects anything that would overflow this scheme, so a test
that cannot be faithfully emitted is a hard error rather than a quietly wrong
`.litmus` file. -/

def addrBase : Nat := 14

/-- Base addresses accessed as a *pair*, by any instruction.  These are declared
    as two-element arrays rather than scalars, because a pair access covers two
    *contiguous* words and herd7 gives no adjacency guarantee between two
    separately declared locations.  This is also why pair tests need
    `-variant mixed`.

    `STP`/`LDP` are here for exactly the same reason `CASP` is.  Note the
    consequence for the wide group's *control*: a test whose writer uses two
    ordinary `STR`s still needs the array declaration, because its reader is an
    `LDP` -- and if only the writer were consulted the two words would be
    unrelated scalars and the control would not be testing adjacency at all. -/
def Litmus.pairBases (L : Litmus) : List Address :=
  L.threads.foldl
    (fun acc p => p.foldl
      (fun acc ins =>
        match ins with
        | .rmwPair _ _ a _ _ _ _ _ _ _
        | .storePair a _ _ _ _
        | .loadPair _ _ a _ _ =>
            if acc.any (fun b => decide (b = a)) then acc else acc ++ [a]
        | _ => acc)
      acc)
    []

/-- Locations that get a name of their own.  The second word of a pair is named
    as a subscript of its base, so it must not also consume a slot in the
    `x`/`y`/`z`/`w` pool -- otherwise a test's second real location ends up
    called `z`, which is correct but unreadable. -/
def Litmus.nameableLocs (L : Litmus) : List Address :=
  L.locs.filter fun a => !L.pairBases.any fun b => decide (b.next = a)

/-- The bare identifier for a location, by position among the nameable ones. -/
def Litmus.baseName (L : Litmus) (a : Address) : String :=
  match L.nameableLocs.findIdx? (fun b => decide (b = a)) with
  | some i => (["x", "y", "z", "w"]).getD i s!"v{i}"
  | none => "UNKNOWN_LOC"

/-- How a location is *named* in the test body.  Words belonging to a pair are
    subscripts of their base; everything else keeps its bare name. -/
def Litmus.locName (L : Litmus) (a : Address) : String :=
  if L.pairBases.any (fun b => decide (b = a)) then s!"{L.baseName a}[0]"
  else
    match L.pairBases.find? (fun b => decide (b.next = a)) with
    | some b => s!"{L.baseName b}[1]"
    | none => L.baseName a

/-- How a location is *addressed*: an array decays to its base identifier, so
    an address register for a pair is loaded with `x`, not `x[0]`.

    The *second* word of a pair decays the same way, and is then reached with
    the offset `addrOffset` supplies.  herd7's init block has no syntax for the
    address of an array element -- `1:X14=x[1]` is rejected with "out-of-bound
    access on x" and `1:X14=&x[1]` with "unexpected '&'" -- so `[X14,#8]` in the
    body is the only way to name it. -/
def Litmus.addrName (L : Litmus) (a : Address) : String :=
  if L.pairBases.any (fun b => decide (b = a)) then L.baseName a
  else match L.pairBases.find? (fun b => decide (b.next = a)) with
    | some b => L.baseName b
    | none => L.locName a

/-- The addressing-mode offset that goes with `addrName`: one 64-bit word for
    the second half of a pair, nothing otherwise.  Appended *inside* the
    brackets, so it composes with the computed-address register `X10` that a
    dependency-carrying access uses. -/
def Litmus.addrOffset (L : Litmus) (a : Address) : String :=
  if L.pairBases.any (fun b => decide (b.next = a)) then ",#8" else ""

/-- The distinct locations a thread touches, in first-use order. -/
def threadLocs (prog : List Instr) : List Address :=
  prog.foldl
    (fun acc ins =>
      match instrAddr ins with
      | some a => if acc.any (fun b => decide (b = a)) then acc else acc ++ [a]
      | none => acc)
    []

/-- Code computing `W8 = 0` while carrying a preserved dependency on every
    register in `deps`.  This is the `EOR Wt,Wd,Wd` idiom herd7's own tests use;
    a compiler is not permitted to see through it. -/
def zeroDep : List Reg → List String
  | [] => ["MOV W8,#0"]
  | d :: rest =>
      s!"EOR W8,W{d},W{d}" ::
      rest.flatMap fun d' => [s!"EOR W9,W{d'},W{d'}", "ORR W8,W8,W9"]

/-- Returns this thread's init-block entries and its assembly lines. -/
def Litmus.armThread (L : Litmus) (tid : Nat) (prog : List Instr) :
    List String × List String :=
  let locs := threadLocs prog
  let areg : Address → Nat := fun a =>
    addrBase + ((locs.findIdx? (fun b => decide (b = a))).getD 0)
  -- The offset half of the addressing mode; see `Litmus.addrOffset`.
  let aoff : Address → String := fun a => L.addrOffset a
  let init := locs.mapIdx fun i a => s!"{tid}:X{addrBase + i}={L.addrName a};"
  let step : (List String × Nat) → Instr → (List String × Nat) :=
    fun (acc, lbl) ins =>
      match ins with
      | .load dst a deps acq =>
          let op := if acq then "LDAR" else "LDR"
          if deps.isEmpty then
            (acc ++ [s!"{op} W{dst},[X{areg a}{aoff a}]"], lbl)
          else
            -- Address dependency: the loaded address is computed from `deps`.
            (acc ++ zeroDep deps ++
               [s!"ADD X10,X{areg a},W8,SXTW", s!"{op} W{dst},[X10{aoff a}]"], lbl)
      | .store a e deps rel =>
          let op := if rel then "STLR" else "STR"
          match e, deps.isEmpty with
          | .const (.num n), true =>
              (acc ++ [s!"MOV W8,#{n}", s!"{op} W8,[X{areg a}{aoff a}]"], lbl)
          | .const (.num n), false =>
              -- Data dependency: the stored value is computed from `deps`.
              (acc ++ zeroDep deps ++
                 [s!"ADD W8,W8,#{n}", s!"{op} W8,[X{areg a}{aoff a}]"], lbl)
          | .reg r, true =>
              (acc ++ [s!"{op} W{r},[X{areg a}{aoff a}]"], lbl)
          | .reg r, false =>
              (acc ++ zeroDep deps ++
                 [s!"ADD X10,X{areg a},W8,SXTW", s!"{op} W{r},[X10{aoff a}]"], lbl)
          | _, _ => (acc ++ ["UNSUPPORTED_STORE_VALUE"], lbl)
      | .rmw dst a kind newv deps acq rel =>
          -- `CAS Ws,Wt,[Xn]`: compare `Ws` with memory, store `Wt` if equal,
          -- and leave the old value in `Ws`.  `SWP Ws,Wt,[Xn]` stores `Ws` and
          -- leaves the old value in `Wt` -- note the operands are the other way
          -- round, which is an easy thing to get silently wrong.  The fetch-ops
          -- `LDADD/LDSET/LDCLR/LDEOR Ws,Wt,[Xn]` follow `SWP`: operand in `Ws`,
          -- old value to `Wt`.  `LDCLR` clears the operand's bits, so `and`
          -- complements the operand first (`MVN`), which keeps a register
          -- operand's dependency.
          --
          -- W11 rather than W8 for the new value: W8 and W9 belong to
          -- `zeroDep`, and a dependency-carrying RMW needs both live at once.
          let sfx := (if acq then "A" else "") ++ (if rel then "L" else "")
          let n := match newv with | .const (.num k) => k | _ => 0
          let pre := if deps.isEmpty then [] else zeroDep deps
          let fix := if deps.isEmpty then []
                     else [s!"ADD X10,X{areg a},W8,SXTW"]
          let addr :=
            if deps.isEmpty then s!"X{areg a}{aoff a}" else s!"X10{aoff a}"
          --
          -- A register new value is used in place, with no staging `MOV`;
          -- `wellFormed` keeps it distinct from a CAS's `dst`, which the
          -- compare value's `MOV` overwrites.
          let fetchMn : RmwKind → Option String
            | .add => some "LDADD" | .or => some "LDSET" | .and => some "LDCLR"
            | .xor => some "LDEOR" | _ => none
          match kind, newv with
          | .cas (.num e), .reg r =>
              (acc ++ pre ++ fix ++
                 [s!"MOV W{dst},#{e}", s!"CAS{sfx} W{dst},W{r},[{addr}]"], lbl)
          | .cas (.num e), _ =>
              (acc ++ pre ++ fix ++
                 [s!"MOV W{dst},#{e}", s!"MOV W11,#{n}",
                  s!"CAS{sfx} W{dst},W11,[{addr}]"], lbl)
          | .swap, .reg r =>
              (acc ++ pre ++ fix ++ [s!"SWP{sfx} W{r},W{dst},[{addr}]"], lbl)
          | .swap, _ =>
              (acc ++ pre ++ fix ++
                 [s!"MOV W11,#{n}", s!"SWP{sfx} W11,W{dst},[{addr}]"], lbl)
          | .and, .reg r =>
              (acc ++ pre ++ fix ++
                 [s!"MVN W11,W{r}", s!"LDCLR{sfx} W11,W{dst},[{addr}]"], lbl)
          | .and, _ =>
              (acc ++ pre ++ fix ++
                 [s!"MOV W11,#{n}", "MVN W11,W11", s!"LDCLR{sfx} W11,W{dst},[{addr}]"], lbl)
          | k, .reg r =>
              match fetchMn k with
              | some mn => (acc ++ pre ++ fix ++ [s!"{mn}{sfx} W{r},W{dst},[{addr}]"], lbl)
              | none => (acc ++ ["UNSUPPORTED_RMW_COMPARE"], lbl)
          | k, _ =>
              match fetchMn k with
              | some mn =>
                  (acc ++ pre ++ fix ++
                     [s!"MOV W11,#{n}", s!"{mn}{sfx} W11,W{dst},[{addr}]"], lbl)
              | none => (acc ++ ["UNSUPPORTED_RMW_COMPARE"], lbl)
      | .rmwPair d0 d1 a c0 c1 n0 n1 deps acq rel =>
          -- `CASP <Xs>,<X(s+1)>,<Xt>,<X(t+1)>,[<Xn>]`: compare the pair held in
          -- `Xs,Xs+1` against the two words at `[Xn]`, store `Xt,Xt+1` if both
          -- match, and leave the loaded pair in `Xs,Xs+1` whether or not it
          -- matched.  That last part is the CAS-vs-SWP confound in pair form --
          -- a thread reporting the expected value in `Xs` has *not* thereby
          -- succeeded.
          --
          -- Both register pairs must be consecutive and start even.
          -- `wellFormed` enforces that for `d0,d1`; `X12,X13` is the fixed
          -- new-value pair, chosen because `X10` is the computed-address
          -- scratch and `X11` belongs to single-word RMW emission.
          --
          -- X-form rather than W-form: the operands are 64-bit, and the
          -- `exists` clause names `X` registers anyway.
          let sfx := (if acq then "A" else "") ++ (if rel then "L" else "")
          let num := fun (v : Val) => match v with | .num k => k | _ => 0
          -- A register new value is copied into the fixed pair with a register
          -- `MOV`, which herd7 follows as data flow, so the dependency reaches
          -- the write; `wellFormed` keeps it off `d0,d1`, which the compare
          -- `MOV`s overwrite first.
          let movN := fun (x : String) (e : Expr) => match e with
            | .reg r => s!"MOV {x},X{r}"
            | .const v => s!"MOV {x},#{num v}"
          let pre := if deps.isEmpty then [] else zeroDep deps
          let fix := if deps.isEmpty then []
                     else [s!"ADD X10,X{areg a},W8,SXTW"]
          let addr :=
            if deps.isEmpty then s!"X{areg a}{aoff a}" else s!"X10{aoff a}"
          (acc ++ pre ++ fix ++
             [s!"MOV X{d0},#{num c0}", s!"MOV X{d1},#{num c1}",
              movN "X12" n0, movN "X13" n1,
              s!"CASP{sfx} X{d0},X{d1},X12,X13,[{addr}]"], lbl)
      | .storePair a e0 e1 deps _ =>
          -- `STP <Xt1>,<Xt2>,[<Xn>]`.  X-form is forced, not chosen: the
          -- locations are `uint64_t`, and `STP W..,W..` would write two 4-byte
          -- slots, i.e. half of the first location and none of the second.
          --
          -- X12/X13 are the scratch pair, the same two `CASP` uses for its new
          -- value, and for the same reason: X8/X9 belong to `zeroDep`, X10 is
          -- the computed-address scratch and X11 belongs to single-word RMW.
          let pre := if deps.isEmpty then [] else zeroDep deps
          let fix := if deps.isEmpty then []
                     else [s!"ADD X10,X{areg a},W8,SXTW"]
          let addr :=
            if deps.isEmpty then s!"X{areg a}{aoff a}" else s!"X10{aoff a}"
          -- Constants need a scratch register each; registers are used as-is.
          let (r0, movs0) := match e0 with
            | .reg r => (s!"X{r}", [])
            | .const (.num n) => ("X12", [s!"MOV X12,#{n}"])
            | .const _ => ("X12", ["UNSUPPORTED_STORE_VALUE"])
          let (r1, movs1) := match e1 with
            | .reg r => (s!"X{r}", [])
            | .const (.num n) => ("X13", [s!"MOV X13,#{n}"])
            | .const _ => ("X13", ["UNSUPPORTED_STORE_VALUE"])
          (acc ++ pre ++ fix ++ movs0 ++ movs1 ++
             [s!"STP {r0},{r1},[{addr}]"], lbl)
      | .loadPair d0 d1 a deps _ =>
          -- `LDP <Xt1>,<Xt2>,[<Xn>]`, X-form for the reason above.  The
          -- `exists` clause names `X` registers anyway, so no conversion is
          -- needed at the observation end.
          let pre := if deps.isEmpty then [] else zeroDep deps
          let fix := if deps.isEmpty then []
                     else [s!"ADD X10,X{areg a},W8,SXTW"]
          let addr :=
            if deps.isEmpty then s!"X{areg a}{aoff a}" else s!"X10{aoff a}"
          (acc ++ pre ++ fix ++ [s!"LDP X{d0},X{d1},[{addr}]"], lbl)
      | .fence f =>
          let m := match f with
            -- `DMB LD`/`DMB ST`, not `ISHLD`/`ISHST`: herd7 master's
            -- aarch64fences.cat flags a shareability argument on `DMB` as
            -- deprecated (same semantics; `dmb.ld` contains both).
            | .ld => "DMB LD"
            | .st => "DMB ST"
            | .sy => "DMB SY"
          (acc ++ [m], lbl)
      | .branch r =>
          let nm := s!"L{tid}{lbl}"
          (acc ++ [s!"CBNZ W{r},{nm}", nm ++ ":"], lbl + 1)
      | .isb => (acc ++ ["ISB"], lbl)
  (init, (prog.foldl step ([], 0)).1)

def padTo (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (w - s.length) ' ')

/-- Lay the per-thread columns out side by side, herd7 style. -/
def renderCols (hdr : List String) (cols : List (List String)) : List String :=
  let h := cols.foldl (fun m c => max m c.length) 0
  let cols := cols.map fun c => c ++ List.replicate (h - c.length) ""
  let w := (List.zip hdr cols).map fun (hd, c) =>
    c.foldl (fun m s => max m s.length) hd.length
  let row (cells : List String) : String :=
    " " ++ String.intercalate " | "
      ((List.zip cells w).map fun (s, k) => padTo s k) ++ " ;"
  row hdr :: (List.range h).map fun r => row (cols.map fun c => c.getD r "")

/-- The final condition.  `regName` is per-architecture (`X1` vs `rax`); a
    location renders the same on both, so only the register case needs it.

    A scalar is written `[x]` and an array element `x[1]`: herd7's syntax puts
    the brackets in different places, and `locName` already knows which a
    location is, so the test is "did it come back subscripted". -/
def Litmus.existsClause (L : Litmus) (regName : Nat → String) : String :=
  let conds := (List.zip L.obs L.target).map fun (o, v) =>
    match o with
    | .reg t r => s!"{t}:{regName r}={v}"
    | .mem a =>
        let nm := L.locName a
        if nm.any (· == '[') then s!"{nm}={v}" else s!"[{nm}]={v}"
  "exists (" ++ String.intercalate " /\\ " conds ++ ")"

def Litmus.toArm (L : Litmus) : String :=
  let per := L.threads.mapIdx fun i p => L.armThread i p
  let inits := (per.map Prod.fst).filter (fun i => !i.isEmpty)
  -- A pair base must be declared as a two-element array, or its two words are
  -- unrelated scalars and `CASP` writes whichever location herd7 happened to
  -- lay down after the base.
  let decls := L.pairBases.map fun b => s!"uint64_t {L.baseName b}[2];"
  let hdr := (List.range L.threads.length).map fun i => s!"P{i}"
  let body := renderCols hdr (per.map Prod.snd)
  s!"AArch64 {L.name}\n" ++ "{\n" ++
  String.intercalate "\n" (decls ++ inits.map fun i => String.intercalate " " i) ++
  "\n}\n" ++
  String.intercalate "\n" body ++ "\n" ++
  L.existsClause (fun r => s!"X{r}") ++ "\n"

/-- x86-64 register names, eight of them to match AArch64's limit so that the
    two architectures' versions of a test can use the *same* register numbers
    rather than differing for no reason.

    `rax` is first deliberately: `CMPXCHG` hard-wires it as the
    compare-and-old-value operand, so `wellFormed` requires a conditional RMW
    to target register 0.

    `r11` is deliberately absent -- RMW emission uses it as a scratch for the
    new value, so it must not be nameable by a test. -/
def x86Reg (r : Nat) : String :=
  (["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "r8", "r9"]).getD r "rbad"

/-- One instruction may emit several lines, hence `flatMap` rather than `map`.

    This targets herd7's `X86_64` front end, not its 32-bit `X86` one.  The
    reason is `CMPXCHG`: `X86` does not implement it (`I_CMPXCHG not
    implemented`), so conditional RMW would be inexpressible.  `X86_64` has
    both `cmpxchgq` and `xchgq`, which gives x86 the same RMW coverage as
    AArch64.  The seven pre-existing tests were checked to produce identical
    verdicts and state counts before and after the move. -/
def Litmus.x86Thread (L : Litmus) (prog : List Instr) : List String :=
  prog.flatMap fun ins =>
    match ins with
    | .load dst a _ _ => [s!"movq ({L.locName a}), %{x86Reg dst}"]
    | .store a (.const (.num n)) _ _ => [s!"movq ${n}, ({L.locName a})"]
    | .store a (.reg r) _ _ => [s!"movq %{x86Reg r}, ({L.locName a})"]
    | .store _ _ _ _ => ["UNSUPPORTED_STORE_VALUE"]
    | .rmwPair _ _ _ _ _ _ _ _ _ _ =>
        -- Unreachable: `wellFormed` rejects a pair RMW on x86 before emission.
        -- It is rejected rather than approximated because herd7 (7.58, and
        -- master at `ad8e24e`) has no `CMPXCHG16B` at all -- `X86_64Lexer.mll` knows only `cmpxchg{,b,w,l,q}`
        -- -- so there is nothing faithful to emit.
        ["UNSUPPORTED_PAIR_RMW_ON_X86"]
    | .rmw dst a kind newv _ _ _ =>
        -- `acq`/`rel` are deliberately dropped.  A locked read-modify-write on
        -- x86 is already a full barrier, so there is no weaker variant to
        -- emit and nothing for the flags to select.
        let n := match newv with | .const (.num k) => k | _ => 0
        match kind with
        -- herd7 (master at `ad8e24e`) has no `xadd`: `X86_64Lexer.mll` knows
        -- `lock add|xor|inc|dec`, `xchg` and `lock cmpxchg`, and rejects `lock
        -- or`/`lock and`.  So a fetch-add or fetch-xor is checked through
        -- `lock addq`/`lock xorq`, whose lock semantics are `xadd`'s but which
        -- leave no old value in a register: `wellFormed` therefore requires the
        -- test not to observe `dst`, and rejects `or`/`and` on x86 outright.
        | .add => [s!"lock addq ${n}, ({L.locName a})"]
        | .xor => [s!"lock xorq ${n}, ({L.locName a})"]
        | .or | .and => ["UNSUPPORTED_X86_FETCH_OP"]
        | .cas (.num e) =>
            -- `lock cmpxchgq (m), %src` compares RAX with memory, stores
            -- `%src` if equal, and leaves the old value in RAX either way.
            -- Note herd7 writes the operands (memory, source) -- the other way
            -- round from AT&T, and an easy thing to get silently wrong.
            --
            -- RAX is not a choice; the instruction hard-wires it.  `wellFormed`
            -- therefore requires `dst = 0` rather than emitting a fixup `mov`,
            -- which would clobber a register the test may be observing.
            --
            -- %r11 carries the new value: it is outside the four registers a
            -- litmus test may name, so it cannot collide with one.
            --
            -- A register new value is the source operand directly; `wellFormed`
            -- keeps it off RAX.
            match newv with
            | .reg r =>
                [s!"movq ${e}, %rax", s!"lock cmpxchgq ({L.locName a}), %{x86Reg r}"]
            | _ =>
                [s!"movq ${e}, %rax", s!"movq ${n}, %r11",
                 s!"lock cmpxchgq ({L.locName a}), %r11"]
        | .swap =>
            -- `xchgq %r, (m)` swaps, so staging the new value in `dst` leaves
            -- the old value in `dst` -- precisely the RMW result, with no
            -- scratch register needed.
            --
            -- No `lock` prefix, and that is not an omission: XCHG with a memory
            -- operand is the one x86 instruction that locks implicitly.  Intel
            -- SDM, XCHG: the processor's locking protocol is applied "for the
            -- duration of the exchange operation, regardless of the presence or
            -- absence of the LOCK prefix".  herd7 agrees -- it generates the
            -- `rmw` relation for a bare `xchgq`.
            --
            -- A register new value must be `dst` itself (`wellFormed`): the
            -- swap then needs no staging at all.
            match newv with
            | .reg _ => [s!"xchgq %{x86Reg dst}, ({L.locName a})"]
            | _ => [s!"movq ${n}, %{x86Reg dst}", s!"xchgq %{x86Reg dst}, ({L.locName a})"]
        | .cas _ => ["UNSUPPORTED_RMW_COMPARE"]
    | .fence _ => ["mfence"]
    -- Rejected by `wellFormed`; x86 has no dependency ordering to express.
    | .branch _ => ["UNSUPPORTED_BRANCH"]
    | .isb => ["UNSUPPORTED_ISB"]
    -- Also rejected by `wellFormed`, and for a reason worth keeping visible:
    -- the x86 half of the language's tier 2 is AVX `MOVDQA`, which is
    -- not validated.  The placeholder is named rather than a
    -- bare catch-all so that a test reaching here is legible in the output.
    | .storePair _ _ _ _ _ => ["UNSUPPORTED_WIDE_STORE"]
    | .loadPair _ _ _ _ _ => ["UNSUPPORTED_WIDE_LOAD"]

def Litmus.toX86 (L : Litmus) : String :=
  let hdr := (List.range L.threads.length).map fun i => s!"P{i}"
  let body := renderCols hdr (L.threads.map L.x86Thread)
  s!"X86_64 {L.name}\n" ++
  "{ " ++
  String.intercalate " " (L.locs.map fun a => s!"uint64_t {L.locName a} = 0;") ++
  " }\n" ++
  String.intercalate "\n" body ++ "\n" ++
  L.existsClause x86Reg ++ "\n"


def Litmus.render (L : Litmus) : String :=
  match L.arch with | .arm => L.toArm | .tso => L.toX86

/-- Directory name, and also the argument `check-herd.sh` takes.  `x86_64`
    rather than `x86` because the emitted tests are herd7 `X86_64`, not its
    32-bit `X86`; see `x86Thread`.

    Defined on `Arch` rather than `Litmus` so that `main`'s emission and this
    can not drift apart -- they were two separate string literals once. -/
def Arch.subdir : Arch → String
  | .arm => "aarch64"
  | .tso => "x86_64"

def Litmus.subdir (L : Litmus) : String := L.arch.subdir

/-- Reasons this test cannot be faithfully emitted.  Emission refuses rather
    than producing a `.litmus` file that is quietly a different test. -/
def Litmus.wellFormed (L : Litmus) : Option String :=
  -- Eight on both architectures: `x86Reg` and the `W`/`X` register names each
  -- supply that many, so a test can use one register numbering for both.
  let maxReg := 8
  let allRegs := L.threads.flatMap fun p => p.flatMap fun i =>
    (match i with
     | .load d _ _ _ => [d]
     | .rmw d _ _ _ _ _ _ => [d]
     | .rmwPair d0 d1 _ _ _ _ _ _ _ _ => [d0, d1]
     | .loadPair d0 d1 _ _ _ => [d0, d1]
     | _ => []) ++ instrDeps i
  let obsRegs := L.obs.filterMap fun o =>
    match o with | .reg _ r => some r | .mem _ => none
  let obsAddrs := L.obs.filterMap fun o =>
    match o with | .reg _ _ => none | .mem a => some a
  let allAddrs := L.threads.flatMap (fun p => p.flatMap instrAddrs) ++ obsAddrs
  if L.locs.length > 4 then some "more than 4 locations"
  else if L.threads.length > 4 then some "more than 4 threads"
  else if (allRegs ++ obsRegs).any (fun r => decide (r ≥ maxReg)) then
    some s!"register >= {maxReg}"
  else if allAddrs.any (fun a => L.locName a == "UNKNOWN_LOC") then
    some "accesses a location missing from `locs`"
  else if L.obs.length != L.target.length then
    some "obs and target have different lengths"
  else if L.arch = .tso &&
      L.threads.any (fun p => p.any fun i =>
        match i with | .branch _ => true | .isb => true | _ => false) then
    some "branch/isb in an x86 test: x86 has no dependency ordering"
  -- `CMPXCHG` hard-wires RAX as both the compare operand and where the old
  -- value lands, so a conditional RMW on x86 must read into register 0.  The
  -- alternative -- emitting a fixup `mov` into the intended register -- would
  -- clobber RAX, which the test may itself be observing, so this is rejected
  -- rather than papered over.  An unconditional swap has no such constraint:
  -- `xchgq` works with any register.
  else if L.arch = .tso &&
      L.threads.any (fun p => p.any fun i =>
        match i with
        | .rmw d _ (.cas _) _ _ _ _ => decide (d != 0)
        | _ => false) then
    some "conditional RMW on x86 must target register 0 (rax); CMPXCHG fixes it"
  -- A CAS's compare value is staged in `dst` before the instruction, so a new
  -- value held in the same register would be overwritten by it and the
  -- emitted test would store the compare value, not the model's new value.
  else if L.threads.any (fun p => p.any fun i =>
        match i with
        | .rmw d _ (.cas _) (.reg r) _ _ _ => decide (r = d)
        | _ => false) then
    some "CAS new-value register is its destination; the compare MOV clobbers it"
  -- `xchgq %r,(m)` stores `%r` and loads into `%r`, so on x86 a register new
  -- value is emitted in place and must be the destination.  Staging it with a
  -- register-to-register `movq` would need the §10 parser to track register
  -- copies, which it does not.
  else if L.arch = .tso &&
      L.threads.any (fun p => p.any fun i =>
        match i with
        | .rmw d _ .swap (.reg r) _ _ _ => decide (r ≠ d)
        | _ => false) then
    some "x86 swap: a register new value must be the destination register"
  -- herd7's x86 has no `xadd` (see `x86Thread`): a fetch-op is emitted as
  -- `lock addq`/`lock xorq`, which does not write `dst`, so the test must not
  -- look at `dst` -- neither in `obs` nor through a later dependency -- and
  -- the operand must be a constant.  `or`/`and` have no x86 spelling at all.
  else if L.arch = .tso &&
      (List.range L.threads.length).any (fun i =>
        let p := L.threads.getD i []
        let obsI := L.obs.filterMap fun o =>
          match o with | .reg j r => if j = i then some r else none | .mem _ => none
        (List.range p.length).any fun k =>
          match p.getD k .isb with
          | .rmw d _ kind nv _ _ _ =>
              kind.isFetch &&
                (kind = .or || kind = .and ||
                 (match nv with | .reg _ => true | _ => false) ||
                 obsI.contains d ||
                 (p.drop (k + 1)).any fun j => (instrDeps j).contains d)
          | _ => false) then
    some "x86 fetch-op: herd7 has only `lock add`/`lock xor`, which leave no old value; the test may not use `dst`"
  -- herd7 (7.58, and master at `ad8e24e`) has no `CMPXCHG16B` -- `X86_64Lexer.mll` knows only
  -- `cmpxchg{,b,w,l,q}` -- so an x86 pair test cannot be emitted at all, let
  -- alone validated.  Rejected rather than approximated.
  else if L.arch = .tso &&
      L.threads.any (fun p => p.any fun i =>
        match i with | .rmwPair _ _ _ _ _ _ _ _ _ _ => true | _ => false) then
    some "pair RMW on x86: herd7 has no CMPXCHG16B"
  -- `CASP <Xs>,<X(s+1)>,...` requires the destination pair to be consecutive
  -- and to start at an even register.  Emitting a fixup would defeat the
  -- purpose, since the test observes those very registers.
  else if L.threads.any (fun p => p.any fun i =>
      match i with
      | .rmwPair d0 d1 _ _ _ _ _ _ _ _ => decide (d1 != d0 + 1 || d0 % 2 != 0)
      | _ => false) then
    some "CASP needs dst1 = dst0 + 1 with dst0 even"
  -- The compare `MOV`s write `d0,d1` before the new pair is staged, so a
  -- register new value there would be clobbered.
  else if L.threads.any (fun p => p.any fun i =>
      match i with
      | .rmwPair d0 d1 _ _ _ n0 n1 _ _ _ =>
          [n0, n1].any fun e => match e with
            | .reg r => decide (r = d0) || decide (r = d1)
            | .const _ => false
      | _ => false) then
    some "CASP: a register new value must not be a destination register"
  -- Both words of a pair must be seeded, or the second reads as a location
  -- that never existed.  Every pair access, not just the RMW: a wide load of
  -- an unseeded second word would read `undef` and the test would be measuring
  -- the allocation table instead of atomicity.
  else if L.threads.any (fun p => p.any fun i =>
      match i with
      | .rmwPair _ _ a _ _ _ _ _ _ _
      | .storePair a _ _ _ _
      | .loadPair _ _ a _ _ =>
          !L.locs.any fun b => decide (b = a.next)
      | _ => false) then
    some "pair access: the second word is missing from `locs`"
  -- herd7's X86_64 front end has no 16-byte plain pair access, and AVX
  -- `MOVDQA` is unvalidated rather than something this emitter can
  -- reach.  Rejected rather than approximated, as with `CMPXCHG16B` above.
  else if L.arch = .tso &&
      L.threads.any (fun p => p.any fun i =>
        match i with
        | .storePair _ _ _ _ _ | .loadPair _ _ _ _ _ => true
        | _ => false) then
    some "wide access on x86: not emittable (16-byte x86 access is unvalidated)"
  -- Base ARMv8 has no acquire `LDP` or release `STP` -- `LDAR`/`STLR` are
  -- single-register, and FEAT_LSE2 widens atomicity, not ordering.  The step
  -- rules accept the flags because every other access here does; emission
  -- refuses, so no test can depend on an instruction that does not exist.
  else if L.threads.any (fun p => p.any fun i =>
      match i with
      | .storePair _ _ _ _ rel => rel
      | .loadPair _ _ _ _ acq => acq
      | _ => false) then
    some "acquire LDP / release STP: no such instruction"
  else none

/-! ## 10. Reading `.litmus` files back

§9 writes tests out.  This reads them in, and the point is differential testing
against a *generator*.

§9 closed one loop — the assembly herd7 checks is generated from the `Instr`
lists the model runs — but left another open: **who chooses the tests?**  We
did, by hand, and a hand-picked suite can only find bugs someone thought to look
for.  It found none for eight stages, which is weaker evidence than it looks.

So the flow inverts.  `diycross7` enumerates every cycle in a family of
relaxations, herd7 is the oracle, and the `.litmus` file is the *source*:

```text
  diycross7  --->  litmus/gen/aarch64/*.litmus  --herd7-->  oracle.txt
                             |
                             +--parsed here--> the model --> compared
```

Neither side is written by hand, so "the model agrees with the architecture" is
checked on tests nobody chose.  The first run of this found **eight** wrong
verdicts, all in three- and four-thread shapes, and all one bug: see `depBound`.

The reader's hard part is not lexing.  It is that `Instr.deps` names **load
destination registers** — the registers that carry a view — while assembly
threads a dependency through scratch registers (`EOR W8,W0,W0`).  So `Env`
tracks, per register, the transitive set of loads its value depends on, plus
enough constant propagation to turn `MOV W0,#1 ; STR W0,[X1]` back into a store
of a *constant* rather than of a register.

It reads both dialects — `diy7`'s and §9's own — which is what makes the round
trip over `litmus/aarch64/` a test of the reader: those 25 files have
herd7-validated expectations, so reconstructing them exactly is a real
obligation.  Anything it cannot express is a hard error rather than a skip. -/

namespace Parse

/-! ### Lexing

Lean's `String.trim`, `String.drop` and `String.dropEnd` return a
`String.Slice`.  The reader stores and compares these fragments, so it wants
`String` throughout; three wrappers keep the conversions in one place. -/

def trimS (s : String) : String := s.trimAscii.toString
def dropS (s : String) (n : Nat) : String := (s.drop n).toString
def dropEndS (s : String) (n : Nat) : String := (s.dropEnd n).toString

/-- Registers are written `W3` or `X3`; both name register 3.  Width is a
    property of the access, not of the register file, and the model has no
    notion of width at all (a settled design decision). -/
def regOf? (s : String) : Option Reg :=
  if s.length ≥ 2 then
    match s.front with
    | 'W' | 'X' | 'w' | 'x' => (dropS s 1).toNat?
    | _ => none
  else none

def immOf? (s : String) : Option Nat :=
  if s.startsWith "#" then (dropS s 1).toNat? else none

/-- `LDR W3,[X4,W2,SXTW]` → `("LDR", ["W3","X4","W2","SXTW"])`.

    Brackets carry no information once the mnemonic is known — a `LDR`'s second
    operand is an address whether or not it is written `[X4]` — so they are
    deleted, and everything after the mnemonic becomes one comma-separated
    operand list.  Splitting on spaces and re-joining with commas makes
    `LDR W3, [X4]` and `LDR W3,[X4]` the same input. -/
def splitInstr (line : String) : String × List String :=
  let line := (line.replace "[" "").replace "]" ""
  match ((trimS line).splitOn " ").filter (fun s => !s.isEmpty) with
  | [] => ("", [])
  | m :: rest =>
      let ops := ((String.intercalate "," rest).splitOn ",").map trimS
      (m.toUpper, ops.filter (fun s => !s.isEmpty))

/-! ### The per-thread environment -/

structure Env where
  /-- From the init block: which location a register points at. -/
  addrs : List (Reg × Address) := []
  /-- Known constant contents, so a store of `1` comes back as a constant. -/
  consts : List (Reg × Nat) := []
  /-- The loads a register's value depends on.  Present (possibly empty)
      exactly for registers this thread has written: the difference between
      "written, no dependency" and "never written" matters, because reading the
      latter as "no dependency" would make a test vacuous in the one direction
      it exists to rule out. -/
  deps : List (Reg × List Reg) := []
  /-- Registers written by `MVN`, with the operand they complement: `LDCLR`
      of such a register is `and` with that operand.  §9 spells `and n` as
      `MOV W11,#n; MVN W11,W11; LDCLR W11,...`, since there is no `LDAND`. -/
  invs : List (Reg × Expr) := []
  deriving Inhabited

def Env.dep (e : Env) (r : Reg) : List Reg := (e.deps.lookup r).getD []
def Env.written (e : Env) (r : Reg) : Bool := (e.deps.lookup r).isSome
def Env.cst (e : Env) (r : Reg) : Option Nat := e.consts.lookup r
def Env.addr? (e : Env) (r : Reg) : Option Address := e.addrs.lookup r

def dedup (l : List Reg) : List Reg :=
  l.foldl (fun a x => if a.contains x then a else a ++ [x]) []

def Env.setReg (e : Env) (r : Reg) (c : Option Nat) (d : List Reg) : Env :=
  { e with
    consts := (e.consts.filter fun p => p.1 != r) ++ c.toList.map (fun n => (r, n)),
    deps := (e.deps.filter fun p => p.1 != r) ++ [(r, dedup d)],
    invs := e.invs.filter fun p => p.1 != r }

def Env.setAddr (e : Env) (r : Reg) (a : Address) (d : List Reg) : Env :=
  { e.setReg r none d with
    addrs := (e.addrs.filter fun p => p.1 != r) ++ [(r, a)] }

/-! ### Instructions -/

def needReg (s : String) : Except String Reg :=
  match regOf? s with
  | some r => .ok r
  | none => .error s!"expected a register, got `{s}`"

def Env.needAddr (e : Env) (s : String) : Except String Address := do
  let r ← needReg s
  match e.addr? r with
  | some a => .ok a
  | none => .error s!"`{s}` does not hold an address"

/-- The address operand of a load, store or RMW: `Xa`, or `Xa,Wb,SXTW` for an
    address dependency carried by the zero in `Wb`.

    Both dialects appear.  `diy7` writes the dependency into the addressing
    mode; §9 emits `ADD X10,Xa,W8,SXTW` and then uses `[X10]`, which arrives
    here as the one-operand case with the dependency already on `X10`. -/
def Env.addrOps (e : Env) (ops : List String) : Except String (Address × List Reg) := do
  match ops with
  | [a] =>
      let r ← needReg a
      let ad ← e.needAddr a
      return (ad, e.dep r)
  | [a, b, _] =>
      let ad ← e.needAddr a
      let rb ← needReg b
      if e.cst rb != some 0 then
        throw s!"address offset register `{b}` is not a known zero"
      return (ad, e.dep rb)
  | _ => throw "unsupported addressing mode"

def binOp (mn : String) (x y : Option Nat) : Option Nat :=
  match x, y with
  | some a, some b =>
      match mn with
      | "ADD" => some (a + b)
      | "SUB" => some (a - b)
      | "ORR" => some (a ||| b)
      | "EOR" => some (a ^^^ b)
      | _ => none
  | _, _ => none

def fenceOf? (s : String) : Option Fence :=
  match s.toUpper with
  | "SY" | "ISH" => some .sy
  | "ST" | "ISHST" => some .st
  | "LD" | "ISHLD" => some .ld
  | _ => none

/-- `acq`/`rel` from a `CAS`/`SWP` suffix. -/
def sfxOf? (s : String) : Option (Bool × Bool) :=
  match s.toUpper with
  | "" => some (false, false)
  | "A" => some (true, false)
  | "L" => some (false, true)
  | "AL" => some (true, true)
  | _ => none

/-- One assembly line to zero or one `Instr`, plus the updated environment.

    Most lines produce no instruction: `MOV`, the ALU ops and labels exist only
    to set up the registers a real access will use. -/
def step (e : Env) (line : String) : Except String (Env × List Instr) := do
  let (mn, ops) := splitInstr line
  if mn.isEmpty || mn.endsWith ":" || mn == "NOP" then return (e, [])
  match mn, ops with
  | "MOV", [d, s] => do
      let rd ← needReg d
      match immOf? s with
      | some n => return (e.setReg rd (some n) [], [])
      | none =>
          let rs ← needReg s
          match e.addr? rs with
          | some a => return (e.setAddr rd a (e.dep rs), [])
          | none => return (e.setReg rd (e.cst rs) (e.dep rs), [])
  -- A computed address: `ADD Xd,Xa,Wb,SXTW` with `Xa` an address and `Wb` a
  -- dependency-carrying zero.  This is §9's own idiom.
  | "ADD", [d, a, b, _] => do
      let rd ← needReg d
      let ad ← e.needAddr a
      let rb ← needReg b
      if e.cst rb != some 0 then
        throw s!"computed address: `{b}` is not a known zero"
      return (e.setAddr rd ad (e.dep rb), [])
  | "ADD", [d, a, b] | "SUB", [d, a, b] | "ORR", [d, a, b] | "EOR", [d, a, b] => do
      let rd ← needReg d
      let ra ← needReg a
      if !e.written ra then throw s!"{mn}: `{a}` was never written"
      let (cb, db) ←
        match immOf? b with
        | some n => pure (some n, ([] : List Reg))
        | none => do
            let rb ← needReg b
            if !e.written rb then throw s!"{mn}: `{b}` was never written"
            pure (e.cst rb, e.dep rb)
      -- `EOR Wd,Wa,Wa` is zero whatever `Wa` holds; that is the point of the
      -- idiom, and the only case where the value is known despite an unknown
      -- operand.
      let c := if mn == "EOR" && regOf? b == some ra then some 0
               else binOp mn (e.cst ra) cb
      return (e.setReg rd c (e.dep ra ++ db), [])
  | "MVN", [d, s] => do
      let rd ← needReg d
      let rs ← needReg s
      if !e.written rs then throw s!"MVN: `{s}` was never written"
      let src := match e.cst rs with
        | some n => Expr.const (.num n)
        | none => Expr.reg rs
      let e' := e.setReg rd none (e.dep rs)
      return ({ e' with invs := e'.invs ++ [(rd, src)] }, [])
  | "LDR", d :: rest | "LDAR", d :: rest => do
      let rd ← needReg d
      let (a, deps) ← e.addrOps rest
      return (e.setReg rd none [rd], [.load rd a deps (mn == "LDAR")])
  | "STR", s :: rest | "STLR", s :: rest => do
      let rs ← needReg s
      if !e.written rs then throw s!"{mn}: `{s}` was never written"
      let (a, adeps) ← e.addrOps rest
      let ev := match e.cst rs with
        | some n => Expr.const (.num n)
        | none => Expr.reg rs
      return (e, [.store a ev (dedup (e.dep rs ++ adeps)) (mn == "STLR")])
  | "DMB", [k] => do
      match fenceOf? k with
      | some f => return (e, [.fence f])
      | none => throw s!"unknown fence `{mn} {k}`"
  | "ISB", [] => return (e, [.isb])
  | "CBNZ", [r, _] | "CBZ", [r, _] => do
      let rr ← needReg r
      if e.dep rr != [rr] then
        throw s!"branch on `{r}`, which is not a load destination"
      return (e, [.branch rr])
  | _, _ =>
      -- CAS and SWP, whose suffixes make the mnemonic table open-ended.
      if mn.startsWith "CASP" then
        throw "CASP: pair RMW is not read back (§9 is the source for those)"
      else if mn.startsWith "CAS" then
        match sfxOf? (dropS mn 3), ops with
        | some (acq, rel), s :: t :: rest => do
            let rs ← needReg s
            let rt ← needReg t
            let cmp ← match e.cst rs with
              | some n => pure n
              | none => throw s!"CAS: compare register `{s}` has no known value"
            -- A new value with no known constant is a register operand, as
            -- for `STR`.
            if !e.written rt then throw s!"CAS: new-value register `{t}` was never written"
            let nv := match e.cst rt with
              | some n => Expr.const (.num n)
              | none => Expr.reg rt
            let (a, deps) ← e.addrOps rest
            return (e.setReg rs none [rs],
                    [.rmw rs a (.cas (.num cmp)) nv deps acq rel])
        | _, _ => throw s!"cannot read `{line}`"
      else if mn.startsWith "LDADD" || mn.startsWith "LDSET" ||
              mn.startsWith "LDEOR" || mn.startsWith "LDCLR" then
        -- The LSE fetch-ops: `LDADD Ws,Wt,[Xn]` and friends take the operand in
        -- `Ws` and leave the old value in `Wt`, as `SWP` does.  `LDCLR` clears
        -- the operand's bits, so it reads back as `and` only through the
        -- complement `MVN` left in `Ws`.
        let kind : RmwKind :=
          if mn.startsWith "LDADD" then .add else if mn.startsWith "LDSET" then .or
          else if mn.startsWith "LDEOR" then .xor else .and
        match sfxOf? (dropS mn 5), ops with
        | some (acq, rel), s :: t :: rest => do
            let rs ← needReg s
            let rt ← needReg t
            if !e.written rs then throw s!"{mn}: operand register `{s}` was never written"
            let nv ←
              if mn.startsWith "LDCLR" then
                match e.invs.lookup rs with
                | some x => pure x
                | none => throw s!"LDCLR: operand `{s}` is not a known complement (`MVN`)"
              else
                pure (match e.cst rs with
                  | some n => Expr.const (.num n)
                  | none => Expr.reg rs)
            let (a, deps) ← e.addrOps rest
            return (e.setReg rt none [rt], [.rmw rt a kind nv deps acq rel])
        | _, _ => throw s!"cannot read `{line}`"
      else if mn.startsWith "SWP" then
        -- `SWP Ws,Wt,[Xn]` stores `Ws` and leaves the old value in `Wt` — the
        -- operands are the other way round from `CAS`.
        match sfxOf? (dropS mn 3), ops with
        | some (acq, rel), s :: t :: rest => do
            let rs ← needReg s
            let rt ← needReg t
            if !e.written rs then throw s!"SWP: new-value register `{s}` was never written"
            let nv := match e.cst rs with
              | some n => Expr.const (.num n)
              | none => Expr.reg rs
            let (a, deps) ← e.addrOps rest
            return (e.setReg rt none [rt], [.rmw rt a .swap nv deps acq rel])
        | _, _ => throw s!"cannot read `{line}`"
      else throw s!"cannot read `{line}`"

/-! ### x86-64

Everything above reads AArch64.  `diy7 -arch X86_64` and §9's own emitter speak
two dialects of AT&T syntax, and this reader has to take both: the generated
suite is the point, but reading back what we emit is what checks the reader
itself, exactly as the AArch64 round trip does.  They differ in every surface
detail and in none of the substance.

| | §9's emitter | `diy7` |
|---|---|---|
| width suffix | `movq` | `movl` |
| register | `%rax`, `%r11` | `%eax`, `%ebx` |
| init block | `{ uint64_t x = 0; }` | **empty** |
| address | `(x)` | `(x)` |
| `xchg` operands | `xchgq %rax,(x)` | `xchgl (x),%eax` |

The register spelling is the one that matters.  `diy7` writes `%eax` in the
program and `0:rax` in the *condition*, so a reader that treated the two as
different registers would turn every generated test into one that observes a
register nothing ever wrote — and would then disagree with herd7 about almost
everything, which at least fails loudly.  Width is not modelled here at all
(a settled design decision), so both spellings name the same `Reg`.

The empty init block is the other structural difference, and it moves where
location names come from: for AArch64 the init block says which register points
where, and for x86 the address is written into the instruction, so the program
text is the only source. -/

/-- x86-64 general-purpose registers, in **encoding** order — the only
    numbering with a claim to being canonical.  `rax`/`eax` are one register,
    and so are `r8`/`r8d`; the leading `%` is optional because a final
    condition omits it. -/
def x86Reg? (s : String) : Option Reg :=
  let s := (if s.startsWith "%" then dropS s 1 else s).toLower
  if s.length < 2 then none
  else
    let wide := s.front == 'r'
    let body := dropS s 1
    match ["ax", "cx", "dx", "bx", "sp", "bp", "si", "di"].findIdx?
            (fun n => n == body) with
    | some i => if wide || s.front == 'e' then some i else none
    | none =>
        -- `r8`..`r15`, with or without the `d` that names their low half.
        if !wide then none
        else
          let body := if body.endsWith "d" then dropEndS body 1 else body
          match body.toNat? with
          | some n => if 8 ≤ n && n ≤ 15 then some n else none
          | none => none

def x86NeedReg (s : String) : Except String Reg :=
  match x86Reg? s with
  | some r => .ok r
  | none => .error s!"expected an x86 register, got `{s}`"

/-- `(x)` → `x`.  The only addressing mode either dialect uses: a settled
    design decision says accesses are single-word and aligned, so there is no
    displacement, index or scale to read, and anything else must fail rather
    than be approximated. -/
def x86Loc? (s : String) : Option String :=
  if s.startsWith "(" && s.endsWith ")" then
    let n := trimS (dropEndS (dropS s 1) 1)
    if n.isEmpty then none else some n
  else none

def x86Imm? (s : String) : Option Nat :=
  if s.startsWith "$" then (dropS s 1).toNat? else none

/-- One line to `(locked, mnemonic, operands)`.

    Not `splitInstr`: that one deletes brackets, which here would destroy the
    address, and it has no notion of a prefix.  `lock` is a separate word
    rather than part of the mnemonic. -/
def splitX86 (line : String) : Bool × String × List String :=
  let ws := ((trimS line).splitOn " ").filter (fun s => !s.isEmpty)
  let (lck, ws) := match ws with
    | w :: rest => if w.toLower == "lock" then (true, rest) else (false, ws)
    | [] => (false, ws)
  match ws with
  | [] => (lck, "", [])
  | m :: rest =>
      let ops := ((String.intercalate "," rest).splitOn ",").map trimS
      (lck, m.toLower, ops.filter (fun s => !s.isEmpty))

/-- One x86-64 line to zero or one `Instr`.

    `addrOf` rather than an `Env` lookup, because the address is a name in the
    instruction rather than a register set up by the init block.

    The width suffix is dropped: `movl` and `movq` differ only in access width,
    which this model does not have.  `lock` is *not* consulted — on this model's
    x86 an RMW is ordered by `Instr.rmw` itself, and an unlocked `xchg` is
    locked implicitly on real hardware anyway — but it is parsed rather than
    ignored so that a stray prefix cannot silently become part of a mnemonic. -/
def stepX86 (addrOf : String → Address) (e : Env) (line : String) :
    Except String (Env × List Instr) := do
  let (_, mn0, ops) := splitX86 line
  if mn0.isEmpty || mn0.endsWith ":" || mn0 == "nop" then return (e, [])
  let mn := if mn0.endsWith "q" || mn0.endsWith "l" then dropEndS mn0 1 else mn0
  match mn, ops with
  | "mfence", [] => return (e, [.fence .sy])
  | "mov", [src, dst] =>
      match x86Loc? dst, x86Loc? src with
      | some _, some _ => throw s!"memory-to-memory move `{line}`"
      | some d, none => do
          -- A store, of an immediate or of a register.
          match x86Imm? src with
          | some n => return (e, [.store (addrOf d) (.const (.num n)) [] false])
          | none =>
              let rs ← x86NeedReg src
              if !e.written rs then throw s!"store of `{src}`, which was never written"
              let ev := match e.cst rs with
                | some n => Expr.const (.num n)
                | none => Expr.reg rs
              return (e, [.store (addrOf d) ev (e.dep rs) false])
      | none, some a => do
          let rd ← x86NeedReg dst
          return (e.setReg rd none [rd], [.load rd (addrOf a) [] false])
      | none, none => do
          -- Register setup; produces no memory event.
          let rd ← x86NeedReg dst
          match x86Imm? src with
          | some n => return (e.setReg rd (some n) [], [])
          | none =>
              let rs ← x86NeedReg src
              return (e.setReg rd (e.cst rs) (e.dep rs), [])
  -- `xchg %rax,(x)` stores `%rax` and leaves the old value in `%rax`, so the
  -- one register is both the new value and the destination.
  --
  -- Either operand order.  `xchg` is symmetric in the instruction set and the
  -- assembler accepts both spellings, so the two dialects unsurprisingly differ:
  -- §9 emits `xchgq %rax,(x)` and `diy7` writes `xchgl (x),%eax`.  The address
  -- is whichever operand is one; requiring a fixed order would reject half the
  -- valid programs for no reason the model can point at.
  | "xchg", [p, q] => do
      let (s, a) ← match x86Loc? p, x86Loc? q with
        | none, some a => pure (p, a)
        | some a, none => pure (q, a)
        | some _, some _ => throw s!"xchg: two memory operands in `{line}`"
        | none, none => throw s!"xchg: no memory operand in `{line}`"
      let rs ← x86NeedReg s
      if !e.written rs then throw s!"xchg: `{s}` was never written"
      let nv := match e.cst rs with
        | some n => Expr.const (.num n)
        | none => Expr.reg rs
      return (e.setReg rs none [rs], [.rmw rs (addrOf a) .swap nv [] false false])
  -- `lock cmpxchg (x),%r11` compares against `%rax`, stores `%r11` on success,
  -- and leaves what it read in `%rax` either way.  The accumulator is implicit,
  -- which is the one place this dialect hides an operand.
  | "cmpxchg", [d, t] => do
      let some a := x86Loc? d | throw s!"cmpxchg: `{d}` is not an address"
      let rt ← x86NeedReg t
      let rax := 0
      let cmp ← match e.cst rax with
        | some n => pure n
        | none => throw "cmpxchg: %rax has no known value to compare against"
      if !e.written rt then throw s!"cmpxchg: new-value register `{t}` was never written"
      let nv := match e.cst rt with
        | some n => Expr.const (.num n)
        | none => Expr.reg rt
      return (e.setReg rax none [rax],
              [.rmw rax (addrOf a) (.cas (.num cmp)) nv [] false false])
  -- `lock addq $n,(x)` / `lock xorq $n,(x)`: a fetch-op whose old value goes
  -- nowhere (herd7's x86 has no `xadd`, see `x86Thread`).  The model's `rmw`
  -- needs a destination, so it gets `%r11`, the scratch register §9 never
  -- observes; `wellFormed` has already refused any test that would look.
  | "add", [src, dst] | "xor", [src, dst] => do
      let some a := x86Loc? dst | throw s!"{mn}: `{dst}` is not an address"
      let some n := x86Imm? src | throw s!"{mn}: operand `{src}` is not an immediate"
      let r11 := 11
      return (e.setReg r11 none [r11],
              [.rmw r11 (addrOf a) (if mn == "add" then .add else .xor)
                 (.const (.num n)) [] false false])
  | _, _ => throw s!"cannot read `{line}`"

/-- Location names in first-use order, read off the program text because
    `diy7`'s x86 init block is empty. -/
def x86Names (cols : List (List String)) : List String :=
  cols.foldl (fun (acc : List String) col =>
    col.foldl (fun (acc : List String) line =>
      let (_, _, ops) := splitX86 line
      ops.foldl (fun (acc : List String) o =>
        match x86Loc? o with
        | some n => if acc.contains n then acc else acc ++ [n]
        | none => acc) acc) acc) []

/-! ### Whole files -/


def isCond (l : String) : Bool :=
  l.startsWith "exists" || l.startsWith "forall" || l.startsWith "~exists"

/-- ` P0          | P1          ;` → `["P0", "P1"]`. -/
def splitRow (l : String) : List String :=
  let l := trimS l
  let l := if l.endsWith ";" then trimS (dropEndS l 1) else l
  (l.splitOn "|").map trimS

structure Raw where
  name : String
  /-- From the header line.  `AArch64` and `X86_64` are the two herd7 writes
      for the two architectures this model has. -/
  arch : Arch
  init : List String
  cols : List (List String)
  cond : String

/-- Header, init block, program table, final condition.  `diy7`'s metadata
    lines (`Cycle=`, `Generator=`, `Prefetch=`, …) sit between the header and
    the `{`, and are skipped by looking for the `{` rather than counting.

    Both brace styles are accepted.  `diy7` puts `{` on a line of its own; a
    hand-written test usually opens with `{ uint64_t x[2];` and closes with
    `... }` on the last entry's line.  Only reading the first style would mean
    this parser could read nothing but its own generator's output, which is
    most of the value gone -- the pair probes are hand-written. -/
def splitFile (src : String) : Except String Raw := do
  let lines := ((src.splitOn "\n").map trimS).filter (fun l => !l.isEmpty)
  let (hdr, rest) ← match lines with
    | [] => throw "empty file"
    | h :: r => pure (h, r)
  let (arch, name) ← match (hdr.splitOn " ").filter (fun s => !s.isEmpty) with
    | [a, n] =>
        if a == "AArch64" then pure (Arch.arm, n)
        else if a == "X86_64" then pure (Arch.tso, n)
        else throw s!"unsupported architecture `{a}`"
    | _ => throw s!"bad header `{hdr}`"

  let body ← match rest.dropWhile (fun l => !l.startsWith "{") with
    | [] => throw "no init block"
    | o :: b => pure (trimS (dropS o 1) :: b)
  let body := body.filter fun l => !l.isEmpty
  let closes := fun (l : String) => l.endsWith "}"
  let init := (body.takeWhile (fun l => !closes l)) ++
    (match body.find? closes with
     | some l => [trimS (dropEndS l 1)]
     | none => [])
  let prog := (body.dropWhile (fun l => !closes l)).drop 1
  let (hdrRow, rows) ← match prog with
    | [] => throw "no program"
    | h :: r => pure (h, r)
  let n := (splitRow hdrRow).length
  let bodyRows := (rows.takeWhile (fun l => !isCond l)).map splitRow
  let cond ← match rows.dropWhile (fun l => !isCond l) with
    | [] => throw "no final condition"
    | c :: _ => pure c
  let cols := (List.range n).map fun i => bodyRows.map fun r => r.getD i ""
  return { name := name, arch := arch, init := init, cols := cols, cond := cond }

/-- Init-block entries, as `(thread, register, location name)`.  Anything that
    is not a per-thread address binding is either a declaration (skipped) or an
    initial value, and a nonzero initial value is refused rather than ignored:
    `Litmus.initMem` seeds every location with `num 0`. -/
def parseInit (entries : List String) : Except String (List (Nat × Reg × String)) := do
  let toks := ((String.intercalate " " entries).splitOn ";").map trimS
  let mut out := []
  for t in toks do
    if t.isEmpty || t.startsWith "uint64_t" || t.startsWith "int" then continue
    match t.splitOn "=" with
    | [lhs, rhs] =>
        let lhs := trimS lhs
        let rhs := trimS rhs
        match lhs.splitOn ":" with
        | [tid, r] =>
            let some i := (trimS tid).toNat? | throw s!"bad init entry `{t}`"
            let rr ← needReg (trimS r)
            out := out ++ [(i, rr, rhs)]
        | _ => if rhs != "0" then throw s!"nonzero initial value in `{t}`"
    | _ => throw s!"bad init entry `{t}`"
  return out

/-- The left-hand side of one conjunct of a final condition, still unresolved:
    a location is a *name* here, because the name-to-`Address` mapping is built
    from the whole file and the condition may be the first place a location is
    mentioned.

    `idx` is the array subscript.  A scalar is index 0, and so is `x[0]`, which
    is exactly right: `Litmus.locName` names a pair's base word `x[0]` and its
    base `Address` has offset 0. -/
inductive CondLhs where
  | reg (t : Nat) (r : Reg)
  | mem (name : String) (idx : Nat)
  deriving Repr, Inhabited

/-- `exists (1:X1=1 /\ [x]=2)` → `[(reg 1 1, 1), (mem "x" 0, 2)]`.

    `regOf` is the architecture's register naming — `needReg` for AArch64,
    `x86NeedReg` for x86 — and is the only part of a final condition that
    differs between the two.

    All three forms herd7 accepts on the left of a location condition are
    taken: `[x]=2`, the bare `x=2` it also prints, and `x[1]=2` for an element
    of a declared array -- which is what a `CASP` test's final state looks
    like, and the reason the memory-observing pair probes could not be
    `Litmus` values. Anything else is refused loudly rather than dropped: a
    silently discarded conjunct would make a test pass by observing less than
    it claims. -/
def parseCond (regOf : String → Except String Reg) (s : String) :
    Except String (List (CondLhs × Nat)) := do
  if !s.startsWith "exists" then
    throw s!"only `exists` conditions are read, got `{s}`"
  let s := trimS (dropS s 6)
  let s := if s.startsWith "(" then dropS s 1 else s
  let s := if s.endsWith ")" then dropEndS s 1 else s
  let parts := (s.splitOn "/\\").map trimS
  let mut out := []
  for p in parts do
    match p.splitOn "=" with
    | [lhs, rhs] =>
        let some v := (trimS rhs).toNat? | throw s!"bad condition `{p}`"
        let lhs := trimS lhs
        match lhs.splitOn ":" with
        | [tid, r] =>
            let some i := (trimS tid).toNat? | throw s!"bad condition `{p}`"
            let rr ← regOf (trimS r)
            out := out ++ [(CondLhs.reg i rr, v)]
        | [nm] =>
            let nm := trimS nm
            -- `[x]` -- the dereference form.
            let nm := if nm.startsWith "[" && nm.endsWith "]" then
                        trimS (dropEndS (dropS nm 1) 1) else nm
            -- `x[1]` -- an element of a declared array.
            let (base, idx) ←
              if nm.endsWith "]" then
                match (dropEndS nm 1).splitOn "[" with
                | [b, i] =>
                    let some k := (trimS i).toNat? | throw s!"bad subscript in `{p}`"
                    pure (trimS b, k)
                | _ => throw s!"bad condition `{p}`"
              else pure (nm, 0)
            if base.isEmpty then throw s!"bad condition `{p}`"
            out := out ++ [(CondLhs.mem base idx, v)]
        | _ => throw s!"bad condition `{p}`"
    | _ => throw s!"bad condition `{p}`"
  return out

def parseLitmus (src : String) : Except String Litmus := do
  let raw ← splitFile src
  let inits ← parseInit raw.init
  let conds ← parseCond (match raw.arch with
                         | .arm => needReg
                         | .tso => x86NeedReg) raw.cond
  -- One allocation per location name, in first-use order.  The condition is
  -- folded in after the program, so a location that is only ever *observed*
  -- still gets an allocation and an initial `num 0` -- without which
  -- `Litmus.initMem` would leave it empty and `memNat` would read the 999
  -- sentinel rather than 0.
  --
  -- Where the program's own names come from is the one place the two
  -- architectures differ structurally: AArch64 binds an address to a register
  -- in the init block, x86 writes it into the instruction.
  let names : List String := match raw.arch with
    | .arm => inits.foldl
        (fun (acc : List String) (e : Nat × Reg × String) =>
          if acc.contains e.2.2 then acc else acc ++ [e.2.2]) []
    | .tso => x86Names raw.cols
  let names := conds.foldl
    (fun acc (c : CondLhs × Nat) =>
      match c.1 with
      | .mem n _ => if acc.contains n then acc else acc ++ [n]
      | .reg _ _ => acc) names
  let addrOf : String → Address := fun n =>
    ⟨(names.findIdx? (fun m => m == n)).getD 0, 0⟩
  -- `x[1]` is the base's `Address` with the offset bumped, which is exactly
  -- `Address.next` iterated -- the same convention `Litmus.locName` inverts.
  let elemOf : String → Nat → Address := fun n i => ⟨(addrOf n).label, i⟩
  -- A subscripted word is a location in its own right: `initMem` seeds `locs`,
  -- and an unseeded location reads as `memNat`'s 999 sentinel rather than 0.
  let extraLocs := conds.filterMap fun (c : CondLhs × Nat) =>
    match c.1 with
    | .mem n i => if i == 0 then none else some (elemOf n i)
    | .reg _ _ => none
  let mut threads := []
  for (i, col) in raw.cols.mapIdx (fun i c => (i, c)) do
    let mut e : Env := {}
    for b in inits do
      if b.1 == i then e := e.setAddr b.2.1 (addrOf b.2.2) []
    let mut prog := []
    for line in col do
      let r := match raw.arch with
        | .arm => step e line
        | .tso => stepX86 addrOf e line
      match r with
      | .ok (e', is) => e := e'; prog := prog ++ is
      | .error m => throw s!"P{i}: {m}"
    threads := threads ++ [prog]
  let locs := (names.map addrOf) ++
    extraLocs.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
  return { name := raw.name, arch := raw.arch, threads := threads,
           locs := locs,
           obs := conds.map fun c =>
             match c.1 with
             | .reg t r  => Obs.reg t r
             | .mem n i  => Obs.mem (elemOf n i),
           target := conds.map Prod.snd,
           -- Not declared here: for a generated test herd7 is the oracle and
           -- the comparison happens outside Lean.  `archAllows` would be a
           -- claim this file has no basis for.
           archAllows := false }

/-- What the model says about a test read off disk, in the same
    `NAME verdict states` form `check-herd.sh` reduces herd7's output to. -/
def genLine (L : Litmus) : String :=
  let os := L.outcomes
  let verdict := if os.contains L.target then "allowed" else "forbidden"
  s!"{L.name} {verdict} {os.length}"

/-- Run every `.litmus` file in `dir`.  A file that cannot be read is a
    failure, not a skip -- a generated shape the parser does not understand is
    exactly the case this harness exists to find, and skipping it would turn a
    gap in the model into a smaller-looking test run.

    Output is sorted, because `readDir` order is filesystem-dependent and the
    caller diffs this against a checked-in oracle. -/
def runDir (dir : String) : IO UInt32 := do
  let entries ← System.FilePath.readDir (System.FilePath.mk dir)
  let files := ((entries.toList.map (fun e => e.path.toString)).filter
    (fun f => f.endsWith ".litmus")).mergeSort (· ≤ ·)
  let mut bad := 0
  let mut lines := []
  for f in files do
    let src ← IO.FS.readFile (System.FilePath.mk f)
    match parseLitmus src with
    | .ok L => lines := lines ++ [genLine L]
    | .error m => IO.eprintln s!"{f}: {m}"; bad := bad + 1
  for l in lines.mergeSort (· ≤ ·) do IO.println l
  return if bad == 0 then 0 else 1

end Parse

/-- Write one architecture's tests, plus the verdicts `check-herd.sh` compares
    herd7's output against.  Deriving `expected.txt` from the same `Litmus`
    values the model runs is the point: it makes "the model agrees with herd7"
    and "the model agrees with its own declared expectations" the same claim. -/
def emitArch (root sub : String) (ls : List Litmus) : IO Unit := do
  let dir := root ++ "/" ++ sub
  IO.FS.createDirAll (System.FilePath.mk dir)
  for L in ls do
    IO.FS.writeFile (System.FilePath.mk (dir ++ "/" ++ L.name ++ ".litmus")) L.render
  let expected := ls.map fun L =>
    let verdict := if L.archAllows then "allowed" else "forbidden"
    let n := L.states.elim "?" toString
    s!"{L.name} {verdict} {n}"
  IO.FS.writeFile (System.FilePath.mk (dir ++ "/expected.txt"))
    (String.intercalate "\n" expected ++ "\n")

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      let errs := suite.filterMap fun L =>
        L.wellFormed.map fun e => s!"{L.name}: {e}"
      if !errs.isEmpty then
        for e in errs do IO.eprintln s!"cannot emit {e}"
        return 1
      emitArch dir Arch.arm.subdir armSuite
      emitArch dir Arch.tso.subdir tsoSuite
      -- Separate directory: these need `-model cats/aarch64-pair.cat` and
      -- `-variant mixed`, which the other two groups must not get.
      emitArch dir "aarch64-pair" pairSuite
      -- And separate again: these need `cats/aarch64-lse2.cat`, which the pair
      -- group must not get either -- under it, `WidePlainPairRead` would be the
      -- only honest test in the directory.  §6.16 is the argument for why the
      -- two cat files stay two files, and this is the same argument one level
      -- up.
      emitArch dir "aarch64-wide" wideSuite
      IO.println s!"wrote {suite.length} tests to {dir}/"
      return 0
  | ["run", dir] =>
      -- §10, the other direction: read `.litmus` files nobody here wrote and
      -- say what the model does with them.  Used by gate item 30 on the
      -- `diy7`-generated suite, where herd7 is the oracle and
      -- `litmus/gen/expected.txt` is its recorded answer.
      Parse.runDir dir
  | [] =>
      IO.println report
      return 0
  | _ =>
      IO.eprintln "usage: lean --run WeakMem.lean [emit DIR | run DIR]"
      return 1

end WeakMem

def main (args : List String) : IO UInt32 := WeakMem.main args

