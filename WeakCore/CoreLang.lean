/-
# CoreLang — the type layer

This file mechanises §2 (kinds) and §3
(types) and nothing else: the grammar, well-formedness, and the three functions
every typing rule will consult —

  * `width`     — §2's width table, i.e. the kind `sized i`;
  * `zeroable`  — §3.6's `Zeroable`, the GC and pre-zeroing condition;
  * `sensitive` — §3.8's view-sensitivity, which decides when a store or load
                  must carry `rel`/`acq`/`deps`.

plus one structural check the note describes but never names, `coupledOK`
(§3.5: *a coupled representation must be single-copy atomic*).

and, since §7 row 21, `tear` (§5a): the torn form of a type, which is what a
reader that holds nothing may see (the seqlock).

No terms here: the term layer's checker is `CoreTerm.lean`, which imports this
file.  No semantics, and deliberately **no import of the memory model yet**:
nothing at this layer needs it.  (§7 row 12a renamed
the model's synchronised cell to `Promises.Sync`, so the import will not clash.)

Every table row that these functions compute is pinned by a
`#guard` in §6.  Where a function disagrees with the note, the guard states
what the *function* computes and §7 says why the note is the one that is wrong.
A failing `#guard` is an elaboration error, so a regression in either direction
is caught by the build.

Build:  LEAN_PATH=build lean CoreLang.lean
-/

namespace CoreLang

/-! ## §1. Modes, index terms, constraints -/

/-- Index terms: linear arithmetic over ℕ.  De Bruijn — `var 0` is the nearest
enclosing index binder (`∀a` or `∃a`).  `smul` multiplies by a *literal* only;
that restriction is what keeps the pure constraint language Presburger. -/
inductive Idx
  | lit  (n : Nat)
  | var  (k : Nat)
  | add  (i j : Idx)
  | sub  (i j : Idx)
  | smul (n : Nat) (i : Idx)
  deriving DecidableEq, Repr

namespace Idx

/-- The value of a variable-free term. -/
def closed : Idx → Option Nat
  | lit n    => some n
  | var _    => none
  | add i j  => return (← i.closed) + (← j.closed)
  | sub i j  => return (← i.closed) - (← j.closed)
  | smul n i => return n * (← i.closed)

def mentions (k : Nat) : Idx → Bool
  | lit _    => false
  | var k'   => k' == k
  | add i j  => i.mentions k || j.mentions k
  | sub i j  => i.mentions k || j.mentions k
  | smul _ i => i.mentions k

def inScope (n : Nat) : Idx → Bool
  | lit _    => true
  | var k    => k < n
  | add i j  => i.inScope n && j.inScope n
  | sub i j  => i.inScope n && j.inScope n
  | smul _ i => i.inScope n

/-- Make room for a new binder at depth `c`. -/
def shift (c : Nat) : Idx → Idx
  | lit n    => lit n
  | var k    => if k ≥ c then var (k + 1) else var k
  | add i j  => add (i.shift c) (j.shift c)
  | sub i j  => sub (i.shift c) (j.shift c)
  | smul n i => smul n (i.shift c)

/-- Remove binder `c`; only meaningful when `¬ mentions c`. -/
def lower (c : Nat) : Idx → Idx
  | lit n    => lit n
  | var k    => if k > c then var (k - 1) else var k
  | add i j  => add (i.lower c) (j.lower c)
  | sub i j  => sub (i.lower c) (j.lower c)
  | smul n i => smul n (i.lower c)

/-- `i * w`, if it is still linear: one factor must be closed.  This is the
whole of §3.7 cost 1 — and see §7 finding 4 for the case it rules out. -/
def mul (i w : Idx) : Option Idx :=
  match w.closed, i.closed with
  | some n, _      => some (smul n i)
  | none,   some m => some (smul m w)
  | none,   none   => none

end Idx

/-- Who may touch what a reference reaches.  `own`: this thread, and nobody else
can reach it (§4).  `pub`: published, any thread (§4.1).  `rgn r`: whoever
holds the token for region `r` (§7 row 20).  A region is an index variable,
so `∃r` is the ordinary index existential and needs no binder sort of its own;
regions are only ever compared for equality. -/
inductive Mode
  | own
  | pub
  | rgn (r : Idx)
  deriving DecidableEq, Repr

namespace Mode
def shift (c : Nat) : Mode → Mode
  | rgn r => rgn (r.shift c)
  | μ     => μ
def lower (c : Nat) : Mode → Mode
  | rgn r => rgn (r.lower c)
  | μ     => μ
def mentions (k : Nat) : Mode → Bool
  | rgn r => r.mentions k
  | _     => false
def inScope (n : Nat) : Mode → Bool
  | rgn r => r.inScope n
  | _     => true
end Mode

/-- A **capability** for region `r` (`Ty.cap`): zero width, copyable, never
conjured from zeros.  Strongest first: `pub ≤ bor ≤ rd`.
* `pub` — the region is published memory (`openPub`); first-class.
* `bor` — a token lent for a scope (`borrow`); pub discipline on `rgn r`:
  loads, stores and cell `cas`, with `acq`/`rel` on view-sensitive types.
  Second-class: never stored, returned, or made a type argument.
* `rd`  — a token or read share lent for a scope; loads only. Second-class. -/
inductive Cap
  | pub
  | bor
  | rd
  /-- A frozen region: made by `freeze` from a fresh token, so no protocol word
  was ever born for it and no one can write it again.  First-class and
  copyable, read-only; a load under it is a plain load. -/
  | frz
  deriving DecidableEq, Repr

namespace Cap
/-- `s` grants at least what `t` does.  `pub` does not grant `frz`: a `pub`
region may still be written by others, and `frz` promises it never is. -/
def le : Cap → Cap → Bool
  | .pub, .pub | .pub, .bor | .pub, .rd => true
  | .bor, .bor | .bor, .rd => true
  | .rd, .rd => true
  | .frz, .frz | .frz, .rd => true
  | _, _ => false
def second : Cap → Bool
  | .pub | .frz => false
  | _ => true
def writes : Cap → Bool
  | .rd | .frz => false
  | _ => true
end Cap

/-- Refinement predicates `ψ`.  Everything except `ini` is a pure constraint
`φ`, decided by Presburger; `ini i` is the knowledge atom `ini ν ≥ i`, decided
by §3.8's publication discipline instead. -/
inductive Pred
  | tt
  | le  (i j : Idx)
  | eq  (i j : Idx)
  | and (p q : Pred)
  | ini (i : Idx)
  deriving DecidableEq, Repr

namespace Pred

def hasIni : Pred → Bool
  | ini _   => true
  | and p q => p.hasIni || q.hasIni
  | _       => false

def isTrue : Pred → Bool
  | tt => true
  | _  => false

def mentions (k : Nat) : Pred → Bool
  | tt      => false
  | le i j  => i.mentions k || j.mentions k
  | eq i j  => i.mentions k || j.mentions k
  | and p q => p.mentions k || q.mentions k
  | ini i   => i.mentions k

def inScope (n : Nat) : Pred → Bool
  | tt      => true
  | le i j  => i.inScope n && j.inScope n
  | eq i j  => i.inScope n && j.inScope n
  | and p q => p.inScope n && q.inScope n
  | ini i   => i.inScope n

def shift (c : Nat) : Pred → Pred
  | tt      => tt
  | le i j  => le (i.shift c) (j.shift c)
  | eq i j  => eq (i.shift c) (j.shift c)
  | and p q => and (p.shift c) (q.shift c)
  | ini i   => ini (i.shift c)

end Pred

/-! ## §1a. Kinds of type variables

What a typing rule may assume about a type variable.  **Width and tier are not
here**: no typing rule consumes them, and prenex `∀` is monomorphised, so they
are settled per instance.  Each field is *one-sided*: it asserts a good
property, and its absence means "assume the worst".  So the empty record is the
top kind, and subkinding is pointwise implication. -/

/-- Which atomic accesses (`cas`, `ldar`, `stlr`) are licensed at the variable.
`word`: its width is exactly 1.  `pair`: its width is 1 or 2 — 16-byte `CASP`
and LSE2 pairs, matching §3.5's tier 2.  `word` asserts more than `pair`. -/
inductive Atom
  | none
  | word
  | pair
  deriving DecidableEq, Repr

def Atom.holds : Atom → Option Nat → Bool
  | .none, _ => true
  | .word, w => w == some 1
  | .pair, w => w == some 1 || w == some 2

structure Kind where
  /-- `Zeroable` (§3.6): allocation without initialisation; `ini` for free. -/
  zero   : Bool := false
  /-- not view-sensitive (§3.8): plain loads and stores are enough. -/
  insens : Bool := false
  /-- passes `coupledOK` (row 16): may be the target of a `pub` reference. -/
  share  : Bool := false
  /-- reaches no `own` reference (§4.2): may be stored into `pub` memory. -/
  noOwn  : Bool := false
  atom   : Atom := .none
  /-- not affine (§7 row 20): a value may be duplicated, so it may be loaded
  from memory and used twice.  `noOwn` does not imply it: a token or a
  protocol word reaches no `own` reference and is still affine. -/
  copy   : Bool := false
  /-- never a protocol word (`wordFree`): a plain store or `xchg` may write a
  cell of this type.  A word cell takes only token-checked stores, and a
  generic store must not reach one through an instance. -/
  noWord : Bool := false
  deriving DecidableEq, Repr

def Kind.top : Kind := {}

/-- What a closure's hidden environment must satisfy.  A `pub` closure's
environment sits behind `Ptr pub α`, so it must be shareable and reach nothing
`own`; an `own` closure's environment is unconstrained. -/
def Kind.closure : Mode → Kind
  | .own   => {}
  | .pub   => { share := true, noOwn := true }
  | .rgn _ => {}

/-- The kind of each type variable, innermost first.  `none` marks a variable
bound by `μ`, which is answered coinductively (or, for `Zeroable`, not at all:
a zero word is finite). -/
abbrev KEnv := List (Option Kind)

/-! ## §1b. Word protocols

A protocol word is a word whose value is always in one of a few *state
families* `scale·k + off` (`k ≥ 0`), each either **holding** the word's region
or not.  Transitions `(from, to, dk)` take family `from` at parameter `k` to
family `to` at `k + dk`, where `dk` may be negative, and wild moves `(from, to)`
take any parameter to any parameter.  A state that holds the region is *shared*: anyone
may `cas` out of it, and doing so takes the region.  A state that does not is
*held*: only the thread holding the region's token may leave it, which is how
`unlock` knows the lock's value without reading it.

One region per word.  That covers every lock, seqlock and flag in the note;
ticket locks and condition variables need two words and are protocols over a
pair, which is later. -/

structure Clause where
  scale : Nat
  off   : Nat
  holds : Bool
  deriving DecidableEq, Repr

structure Proto where
  clauses : List Clause
  /-- `(from, to, dk)`: family `from` at `k` to family `to` at `k + dk`.  A
  negative `dk` counts down (a reader leaving a readers–writer lock). -/
  trans   : List (Nat × Nat × Int)
  /-- A **ghost** protocol has no runtime word: width 0, no loads, no `cas`,
  and stores are erased.  It is typestate — the state lives in the token. -/
  ghost   : Bool := false
  /-- The **lending** clauses: holding states in which each reader has an
  affine `share r`, and the parameter counts them (`k + 1` outstanding). -/
  lends   : List Nat := []
  /-- The **counting-down** lending clauses: holding states whose parameter
  counts *free* permits.  Lending a share steps `k + 1 → k`, so the transition
  itself proves a permit was free; giving one back steps `k → k + 1`.  No `cas`
  enters or leaves such a family, so the capacity is the value the word was
  created with, and the region is never taken back. -/
  lendsDown : List Nat := []
  /-- The **wild** moves `(from, to)`: family `from` at *any* parameter to
  family `to` at *any* parameter.  A move out of a parameterless family into a
  family chooses the parameter (`0 → busy(k)` for the `k` the code supplies);
  a move back forgets it.  The operation still names both values (`cas`'s
  expected and new value, a store's token and value), so the states are known;
  only the equation `k' = k + dk` is dropped.  Written `a->b*`. -/
  wild : List (Nat × Nat) := []
  /-- A **local** protocol (opt-in; see `Robust.lean`): its tokens never leave
  the block that took them.  While a block holds one it makes no call and
  does not end, and the token is consumed only by a `store` on its own word
  (or restructured: paired, split, borrowed).  So the held states are
  *windows*: straight-line code between a `cas` and a `store`, which is what a
  crash-recovery argument can be scoped to.  Nothing changes for a protocol
  without the flag. -/
  isLocal : Bool := false
  /-- A **robust** protocol *claims* to have no held state: no participant's
  stopping can leave the word in a state only it may leave.  `pwf` checks the
  claim, so a program whose protocol claims it falsely is refused at
  `mkWord`.  (`local` is the weaker, windowed discipline.) -/
  robust : Bool := false
  /-- A **norepeat** protocol *claims* that no shared state is re-entered at a
  value it had, so a `cas` out of one is never fooled (ABA).  Checked by
  `pwf` (`CoreTerm.noRepeat`). -/
  norepeat : Bool := false
  /-- An **epoch** protocol (opt-in; design (b) of a worked locking-scheme example, not included): the
  word is a counter nobody holds (`pwf` requires the one clause `k!` and the one
  move `0->0(+1)`), and a `cas` from `e` to `e + 1` on it yields an **epoch
  token** `Tok[r, P, e + 1]` (`Ty.tokE`) rather than the region.  Epoch tokens
  are *affine* — dropping one is exactly what a stopped handler does — and
  grant one thing: the epoch-fenced write `casp` on an `EPair[r, P]`
  (`Ty.epair`), a payload pair `(epoch, value)` whose new epoch must be the
  token's.  A later `cas` on the counter revokes every earlier token: its
  fenced writes still name a stale epoch and any reader, or the next holder's
  re-stamp, sees it.  The protocol has no held state, so it is crash-free.
  Nothing changes for a protocol without the flag. -/
  epoch : Bool := false
  /-- A **ticket** protocol (opt-in): the owner word of a ticket lock, a held
  counter `<k ; 0->0+1>` that nobody is born holding.  `mkTicket` makes it
  beside a dispenser (an `epoch` counter) in one region; the holder of ticket
  `n + 1` (the dispenser's token `Tok[r, N, n + 1]`) obtains the owner's token
  `Tok[r, P, n]` by `claim` once it has observed the owner at `n` (acquisition
  by observation), and its releasing `store rel` of `n + 1` hands the lock on
  instead of keeping a token.  Nothing changes for a protocol without the flag. -/
  ticket : Bool := false
  /-- The declared **recovery targets** (opt-in): `(h, s)` says that once the
  thread holding the word in held family `h` has stopped for good, the word may
  be moved to shared family `s`, at a parameter the recovering step chooses,
  without the token.  No term of the core language makes this move: it is the
  move of the trusted reclaim step, gated by an oracle for "the holder is
  dead", which the liveness argument models; the field fixes what that step may write, so the theorem does not
  depend on the trusted code's choice.  `pwf` checks that `h` is held, `s` is
  shared and lends nothing, and each `h` has at most one target.  Written
  `recover(2->0)`.  Nothing changes for a protocol without one. -/
  recover : List (Nat × Nat) := []
  deriving DecidableEq, Repr

/-! ### Pair protocols  (two words, one 16-byte access)

A **pair protocol** is a protocol over two adjacent words read, written and
compared-and-swapped as one single-copy-atomic 16-byte access (`ldp`/`stp`
under FEAT_LSE2, `casp` under FEAT_LSE; `cmpxchg16b` and an aligned 16-byte
move on x86-64).  Its state families have two patterns, one per half, with an
optional relation between the two parameters: `(0, k)` is "first word 0,
second anything", `(2k, k | k1 = k0 + 1)` ties the halves.  A transition
moves each parameter by a delta or forgets it (`none`: that half is wild —
an epoch counter next to a value the move chooses freely).  Everything
else — holding, taking by `casp`, giving back by `stp` — is as for one word.
A pair is a granule-sized leaf, so §3.5's tier-2 alignment obligation applies:
it starts on a 16-byte boundary. -/

/-- How the second half's parameter is tied to the first's: `k₁ ⋈ k₀ + d`. -/
inductive Rel2
  | free
  | eq (d : Int)
  | le (d : Int)   -- `k₁ ≤ k₀ + d`
  | ge (d : Int)   -- `k₁ ≥ k₀ + d`
  deriving DecidableEq, Repr

/-- A pair state family: half `h` is `s_h·k_h + o_h`, with `rel` between the parameters. -/
structure Clause2 where
  s0    : Nat
  o0    : Nat
  s1    : Nat
  o1    : Nat
  rel   : Rel2 := .free
  holds : Bool
  deriving DecidableEq, Repr

structure Proto2 where
  clauses : List Clause2
  /-- `(from, to, d0, d1)`: family `from` at `(k₀, k₁)` to family `to` at
  `(k₀ + d0, k₁ + d1)`; a `none` delta forgets that half's parameter. -/
  trans   : List (Nat × Nat × Option Int × Option Int)
  /-- The claim that no state is held (`Proto.robust`), checked by `pwf2`. -/
  robust  : Bool := false
  /-- An **epoch pair** (opt-in; the `(e, busy)` refinement of `Proto.epoch`):
  half 0 is an epoch counter that only ever grows, half 1 whatever the
  protocol says.  `pwf2` requires every state shared and half 0 the bare
  parameter `k` in every clause, and every move to change half 0 by `0` or
  `+1` (never wild).  A `casp acq` whose move bumps the epoch yields the epoch
  token `Tok[r, P, e + 1]` (`Ty.tokE`, affine); the other moves bind `Unit` as
  before.  So an acquire `(e, 0) -> (e+1, 1)` and a reclaim `(e, 1) -> (e+1, 1)`
  both issue the new epoch's token and revoke the old one, a release
  `(e, 1) -> (e, 0)` issues nothing, and the busy flag is under the same
  checks as the counter.  Nothing changes for a pair without the flag. -/
  epoch   : Bool := false
  deriving DecidableEq, Repr

/-- The counter an epoch token, or an epoch pair, belongs to: a single-word
`epoch` protocol or an `epoch` pair protocol. -/
inductive ECounter
  | word (P : Proto)
  | pair (P : Proto2)
  deriving DecidableEq, Repr

namespace ECounter
/-- The flag that makes the protocol a counter at all. -/
def isEpoch : ECounter → Bool
  | .word P => P.epoch
  | .pair P => P.epoch
end ECounter

/-! ## §2. Types

Two variable sorts, both de Bruijn and kept apart: **type** variables (`tvar`,
bound by `mu` and `tex`) and **index** variables (`Idx.var`, bound by `iall`,
`iex`).  That separation is §3's first NOTE — `∃a` and `∃α` are different
existentials — made structural.

There is no arrow.  §3.9 removed `→` as a former; `arrow` in §5 is the
desugaring `∃α. Code (σ × Ptr μ α) τ × Ptr μ α`. -/

/-- A fixed-width integer's width. -/
inductive Wd
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr

namespace Wd
def bits : Wd → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64
/-- Lanes of this width in one 64-bit word. -/
def lanes (w : Wd) : Nat := 64 / w.bits
def name : Wd → String
  | .w8 => "8" | .w16 => "16" | .w32 => "32" | .w64 => "64"
theorem bits_pos (w : Wd) : 0 < w.bits := by cases w <;> decide
theorem lanes_pos (w : Wd) : 0 < w.lanes := by cases w <;> decide
end Wd

inductive RegAcc | ro | wo | rw deriving DecidableEq, Repr       -- register access (`Acc` is taken: TermRun.Acc, core Acc)
inductive Mo  | plain | rel | acq deriving DecidableEq, Repr      -- ordering mode of a register access
/-- A sealed one-word value (`Val.num`): a register, a register block with its already-split indices, a bus address, an
interrupt line. No introduction form in the language: only the start argument and `regAt` introduce them. -/
inductive Opq
  | reg (w : Wd) (acc : RegAcc)
  | blk (n : Nat) (w : Wd) (acc : RegAcc) (stride : Nat) (taken : List Nat)   -- `n` registers of width `w`, one every
                                                                             -- `stride` bytes (`Wd.bits w / 8 ≤ stride`)
  | bus
  | irq
  deriving DecidableEq, Repr
/-- Read-pure registers are copyable; everything else is affine (exclusive rights). -/
def Opq.copyable : Opq → Bool
  | .reg _ .ro => true
  | _ => false
def RegAcc.canRead  : RegAcc → Bool | .ro | .rw => true | .wo => false
def RegAcc.canWrite : RegAcc → Bool | .wo | .rw => true | .ro => false
/-- The kind flag of a `code` value: plain, or restricted with its fuel and stack budgets (decision E). -/
inductive CodeKind | plain | restricted (fuel stack : Nat) deriving DecidableEq, Repr

inductive Ty
  | unit
  | void                              -- §7 row 13: no introduction form
  | int
  | intS   (i : Idx)                  -- the singleton `Int(i)`
  | fix    (sg : Bool) (w : Wd)       -- a `w`-bit integer, signed if `sg`: its two's-complement bits, `< 2^w`
  | lanes  (sg : Bool) (w : Wd)       -- one 64-bit word of `64/w` lanes of `fix sg w`, little-endian
  | prod   (σ τ : Ty)
  | sum    (σ τ : Ty)
  | code   (σ τ : Ty) (k : CodeKind)   -- bare code pointer, captures nothing; `k`: restricted budgets. NO default: a
                                        -- defaulted field is silently matched as its default in patterns; every
                                        -- site is edited explicitly (`_` in patterns, `.plain` in terms)
  | array  (i : Idx) (τ : Ty)
  | ptr    (μ : Mode) (τ : Ty)        -- base of an allocation
  | ptrOpt (μ : Mode) (τ : Ty)        -- nullable
  | loc    (μ : Mode) (τ : Ty)        -- the locative: allocation + offset
  | share  (r : Idx)                  -- a read share of region r, lent by a word: width 0, affine
  | cap    (s : Cap) (r : Idx)        -- a capability for region r: width 0, copyable
  | word   (r : Idx) (P : Proto)      -- §7 row 20: a protocol word over region r
  | tok    (r : Idx) (st : Option (Proto × Idx)) -- §7 row 20: holding region r, in state st.2 of
                                        -- protocol st.1 (none: a fresh region, no word yet); width 0.
                                        -- Affine; linear when the state has a move out (CoreTerm's noDrop).
                                      -- `some i`: taken from the word at value i
  | word2  (r : Idx) (P : Proto2)     -- a protocol pair over region r: two words, one granule
  | tok2   (r : Idx) (P : Proto2) (i0 i1 : Idx) -- holding region r, the pair at value (i0, i1); width 0
  | epair  (r : Idx) (P : ECounter)   -- an epoch-fenced payload pair (epoch, value) under the counter P of r
  | tokE   (r : Idx) (P : ECounter) (e : Idx) -- an epoch token: writer of epoch e in region r; width 0, affine
  | tvar   (k : Nat)
  | mu     (τ : Ty)                   -- iso-recursive, binds a type variable
  | iall   (τ : Ty)                   -- ∀a. τ, binds an index variable
  | iex    (τ : Ty)                   -- ∃a. τ, binds an index variable
  | tex    (κ : Kind) (τ : Ty)        -- ∃(α : κ). τ, binds a type variable
  | refine (τ : Ty) (ψ : Pred)        -- { ν : τ | ψ }
  | tid                              -- (E1) `ThreadId`: a sealed thread reference, one word (`Val.num` of the
                                     -- thread's index); no introduction form (only `spawn` and `current`),
                                     -- copyable, not Zeroable, compared by `ifeq`; a reference for the GC
  | opq    (o : Opq)                              -- a sealed one-word value; see `Opq`
  deriving DecidableEq, Repr

namespace Ty

/-- Shift type variables at or above `c`. -/
def shiftT (c : Nat) : Ty → Ty
  | tvar k       => if k ≥ c then tvar (k + 1) else tvar k
  | prod a b     => prod (a.shiftT c) (b.shiftT c)
  | sum a b      => sum (a.shiftT c) (b.shiftT c)
  | code a b k   => code (a.shiftT c) (b.shiftT c) k
  | array i t    => array i (t.shiftT c)
  | ptr μ t      => ptr μ (t.shiftT c)
  | ptrOpt μ t   => ptrOpt μ (t.shiftT c)
  | loc μ t      => loc μ (t.shiftT c)
  | mu t         => mu (t.shiftT (c + 1))
  | tex κ t      => tex κ (t.shiftT (c + 1))
  | iall t       => iall (t.shiftT c)
  | iex t        => iex (t.shiftT c)
  | refine t ψ   => refine (t.shiftT c) ψ
  | t            => t

/-- Shift index variables at or above `c`. -/
def shiftI (c : Nat) : Ty → Ty
  | intS i       => intS (i.shift c)
  | prod a b     => prod (a.shiftI c) (b.shiftI c)
  | sum a b      => sum (a.shiftI c) (b.shiftI c)
  | code a b k   => code (a.shiftI c) (b.shiftI c) k
  | array i t    => array (i.shift c) (t.shiftI c)
  | ptr μ t      => ptr (μ.shift c) (t.shiftI c)
  | ptrOpt μ t   => ptrOpt (μ.shift c) (t.shiftI c)
  | loc μ t      => loc (μ.shift c) (t.shiftI c)
  | word r P     => word (r.shift c) P
  | tok r st     => tok (r.shift c) (st.map fun (P, i) => (P, i.shift c))
  | word2 r P    => word2 (r.shift c) P
  | tok2 r P i j => tok2 (r.shift c) P (i.shift c) (j.shift c)
  | epair r P    => epair (r.shift c) P
  | tokE r P e   => tokE (r.shift c) P (e.shift c)
  | share r      => share (r.shift c)
  | cap s r      => cap s (r.shift c)
  | mu t         => mu (t.shiftI c)
  | tex κ t      => tex κ (t.shiftI c)
  | iall t       => iall (t.shiftI (c + 1))
  | iex t        => iex (t.shiftI (c + 1))
  | refine t ψ   => refine (t.shiftI c) (ψ.shift c)
  | t            => t

def idxMentions (k : Nat) : Ty → Bool
  | intS i       => i.mentions k
  | prod a b     => a.idxMentions k || b.idxMentions k
  | sum a b      => a.idxMentions k || b.idxMentions k
  | code a b _   => a.idxMentions k || b.idxMentions k
  | array i t    => i.mentions k || t.idxMentions k
  | ptr μ t      => μ.mentions k || t.idxMentions k
  | ptrOpt μ t   => μ.mentions k || t.idxMentions k
  | loc μ t      => μ.mentions k || t.idxMentions k
  | word r _     => r.mentions k
  | tok r st     => r.mentions k || st.any (·.2.mentions k)
  | word2 r _    => r.mentions k
  | tok2 r _ i j => r.mentions k || i.mentions k || j.mentions k
  | epair r _    => r.mentions k
  | tokE r _ e   => r.mentions k || e.mentions k
  | share r      => r.mentions k
  | cap _ r      => r.mentions k
  | mu t         => t.idxMentions k
  | tex _ t      => t.idxMentions k
  | iall t       => t.idxMentions (k + 1)
  | iex t        => t.idxMentions (k + 1)
  | refine t ψ   => t.idxMentions k || ψ.mentions k
  | _            => false

def tyMentions (k : Nat) : Ty → Bool
  | tvar k'      => k' == k
  | prod a b     => a.tyMentions k || b.tyMentions k
  | sum a b      => a.tyMentions k || b.tyMentions k
  | code a b _   => a.tyMentions k || b.tyMentions k
  | array _ t    => t.tyMentions k
  | ptr _ t      => t.tyMentions k
  | ptrOpt _ t   => t.tyMentions k
  | loc _ t      => t.tyMentions k
  | mu t         => t.tyMentions (k + 1)
  | tex _ t      => t.tyMentions (k + 1)
  | iall t       => t.tyMentions k
  | iex t        => t.tyMentions k
  | refine t _   => t.tyMentions k
  | _            => false

/-- Does type variable `d` occur somewhere **not** under a one-word former?

This is §2's guard for `μα.τ`, reused verbatim by §3.9 for `∃α.τ`.  The
one-word formers are the four reference types **and `Code`**: a code pointer is
one word whatever its domain and codomain are.  §3.9 lists only
`Ptr`/`Ptr?`/`Loc`, and under that reading its own closure encoding is
ill-formed — see §7 finding 3. -/
def unguarded (d : Nat) : Ty → Bool
  | tvar k       => k == d
  | ptr _ _      => false
  | ptrOpt _ _   => false
  | loc _ _      => false
  | code _ _ _   => false
  | prod a b     => a.unguarded d || b.unguarded d
  | sum a b      => a.unguarded d || b.unguarded d
  | array _ t    => t.unguarded d
  | iall t       => t.unguarded d
  | iex t        => t.unguarded d
  | refine t _   => t.unguarded d
  | mu t         => t.unguarded (d + 1)
  | tex _ t      => t.unguarded (d + 1)
  | _            => false

/-- Well-formedness under `nt` type variables and `ni` index variables: every
variable is in scope, and every `μ`/`∃α` body is guarded. -/
def wf (nt ni : Nat) : Ty → Bool
  | tvar k       => k < nt
  | intS i       => i.inScope ni
  | prod a b     => a.wf nt ni && b.wf nt ni
  | sum a b      => a.wf nt ni && b.wf nt ni
  | code a b _   => a.wf nt ni && b.wf nt ni
  | array i t    => i.inScope ni && t.wf nt ni
  | ptr μ t      => μ.inScope ni && t.wf nt ni
  | ptrOpt μ t   => μ.inScope ni && t.wf nt ni
  | loc μ t      => μ.inScope ni && t.wf nt ni
  | word r _     => r.inScope ni
  | tok r st     => r.inScope ni && st.all (·.2.inScope ni)
  | word2 r _    => r.inScope ni
  | tok2 r _ i j => r.inScope ni && i.inScope ni && j.inScope ni
  | epair r _    => r.inScope ni
  | tokE r _ e   => r.inScope ni && e.inScope ni
  | share r      => r.inScope ni
  | cap _ r      => r.inScope ni
  | mu t         => !t.unguarded 0 && t.wf (nt + 1) ni
  | tex _ t      => !t.unguarded 0 && t.wf (nt + 1) ni
  | iall t       => t.wf nt (ni + 1)
  | iex t        => t.wf nt (ni + 1)
  | refine t ψ   => ψ.inScope ni && t.wf nt ni
  | _            => true

end Ty

/-! ## §3. Width and sum tiers

Computed together because they are not independent: a sum's width depends on
its tier, and the tier depends on the widths of its arms.

**Sums are flattened.**  The tier is decided over the *list* of arms of a nest
of `+`, not pairwise.  §2's table states the tier-2 test for a binary `σ + τ`;
applied pairwise it would box `Int + (Int + Int)` (the inner sum is two words)
but not `(Int + Int) + Int` ... also two words.  Flattening makes the width
independent of how the arms are associated, which is the only reading under
which `σ + τ` means "a sum".

**The arm summary.**  For each arm: a pointer spends one tag slot (§3.5's
budget); a payload-free arm (width 0) shares one slot with all the others;
anything else is *wide* and rules out the niche.  `Ptr?` is both a pointer arm
and a payload-free one (its null).  `Void` contributes no arm at all. -/

structure Arms where
  ptrs   : Nat
  units  : Nat
  wide   : Nat
  /-- the largest arm width, if every arm's width is a closed number -/
  maxW   : Option Nat
  deriving DecidableEq, Repr

namespace Arms

def empty : Arms := ⟨0, 0, 0, some 0⟩

def combine (a b : Arms) : Arms :=
  ⟨a.ptrs + b.ptrs, a.units + b.units, a.wide + b.wide,
   (do let x ← a.maxW; let y ← b.maxW; pure (max x y))⟩

/-- Tag slots spent: one per pointer arm, plus one for the payload-free arms
(and a `Ptr?` arm's null), reserved even when there are none.  Reserving it
keeps the tier stable under subsumption: `Ptr <: Ptr?` inside a sum adds a
payload-free case, and must not push eight pointer arms over the budget and
turn a one-word sum into a two-word one. -/
def slots (a : Arms) : Nat := a.ptrs + 1

/-- A lone non-sum type seen as a one-arm sum. -/
def leaf (w : Option Idx) : Arms :=
  match w.bind Idx.closed with
  | some 0 => ⟨0, 1, 0, some 0⟩
  | c      => ⟨0, 0, 1, c⟩

def ptrArm : Arms := ⟨1, 0, 0, some 1⟩
def optArm : Arms := ⟨1, 1, 0, some 1⟩

end Arms

/-- §3.5's three tiers. -/
inductive Tier
  | niche   -- one word, the arm is recovered from the word alone
  | wide    -- (tag, payload), two words, one 16-byte single-copy-atomic access
  | boxed   -- one word, a reference to a born-frozen (tag, payload) block
  deriving DecidableEq, Repr

/-- Eight tag slots: 8-byte alignment leaves three low bits (§3.5). -/
def tagSlots : Nat := 8

def Arms.tier (a : Arms) : Tier :=
  if a.wide = 0 ∧ a.slots ≤ tagSlots then .niche
  else if a.maxW.any (· ≤ 1) then .wide
  else .boxed

structure Info where
  width : Option Idx
  arms  : Arms
  deriving DecidableEq, Repr

/-- What each free type variable is taken to be as wide as.  At top level every
variable is abstract (`none`); §4's theorem is that for a guarded body the
choice does not matter. -/
def Ctx := Nat → Option Idx

def Ctx.cons (o : Option Idx) (ρ : Ctx) : Ctx
  | 0     => o
  | n + 1 => ρ n

def Ctx.shiftI (ρ : Ctx) : Ctx := fun n => (ρ n).map (Idx.shift 0)

def Info.leaf (w : Option Idx) : Info := ⟨w, Arms.leaf w⟩

/-- Remove index binder 0 from a width.  Fails if the width *mentions* it —
that is `unsized`, resurrected, and §2 says no type may be. -/
def lowerW (w : Option Idx) : Option Idx :=
  w.bind fun w => if w.mentions 0 then none else some (w.lower 0)

open Ty in
def info (ρ : Ctx) : Ty → Info
  | unit       => Info.leaf (some (.lit 0))
  | void       => ⟨some (.lit 0), Arms.empty⟩
  | int        => Info.leaf (some (.lit 1))
  | intS _     => Info.leaf (some (.lit 1))
  | fix _ _    => Info.leaf (some (.lit 1))
  | lanes _ _  => Info.leaf (some (.lit 1))
  | prod a b   =>
      Info.leaf (do pure (.add (← (info ρ a).width) (← (info ρ b).width)))
  | sum a b    =>
      let arms := (info ρ a).arms.combine (info ρ b).arms
      -- An arm of unknown width (a type variable, say) leaves the tier open:
      -- instantiation may make the sum niche, wide or boxed.  So the width is
      -- unknown too, like the variable's own; guessing `1` (boxed) let an
      -- admitted instance break every width-based check.
      if arms.maxW.isNone then ⟨none, arms⟩ else
      match arms.tier with
      | .wide => ⟨some (.lit 2), arms⟩
      | _     => ⟨some (.lit 1), arms⟩
  | code _ _ _ => Info.leaf (some (.lit 1))
  | tid        => Info.leaf (some (.lit 1))   -- (E1) one word, a leaf (not a sum niche)
  | opq _      => Info.leaf (some (.lit 1))   -- (M1) one word, a leaf
  -- An inline array has no static width, even at a literal extent: indices
  -- are erased at runtime, so a width that depended on one would let an index
  -- instantiation change a layout the machine cannot see change.
  -- Nothing loads or stores an inline array by value anyway.
  | array _ _  => Info.leaf none
  | ptr _ _    => ⟨some (.lit 1), Arms.ptrArm⟩
  | ptrOpt _ _ => ⟨some (.lit 1), Arms.optArm⟩
  -- A `Loc` may be null (§7 row 15 (c): to a zero-length region), so as a sum
  -- arm it is `Ptr?`-shaped: its null takes the payload-free slot, which `slots`
  -- already reserves, so no tier moves.  Every `Loc`, not only `Loc (Array …)`,
  -- so that instantiating the pointee cannot change an arm's kind
  -- (otherwise a null `Loc` could not be injected into a niche sum).
  | loc _ _    => ⟨some (.lit 1), Arms.optArm⟩
  | word _ P   => Info.leaf (some (.lit (if P.ghost then 0 else 1)))
  | tok _ _    => Info.leaf (some (.lit 0))
  | word2 _ _  => Info.leaf (some (.lit 2))   -- one granule: §3.5 tier 2's alignment
  | tok2 _ _ _ _ => Info.leaf (some (.lit 0))
  | epair _ _  => Info.leaf (some (.lit 2))
  | tokE _ _ _ => Info.leaf (some (.lit 0))
  | share _    => Info.leaf (some (.lit 0))
  | cap _ _    => Info.leaf (some (.lit 0))
  | tvar k     => Info.leaf (ρ k)
  | mu t       => info (ρ.cons none) t
  | tex _ t    => info (ρ.cons none) t
  | iall t     => let it := info ρ.shiftI t; ⟨lowerW it.width, it.arms⟩
  | iex t      => let it := info ρ.shiftI t; ⟨lowerW it.width, it.arms⟩
  | refine t _ => info ρ t

namespace Ty

def top : Ctx := fun _ => none

/-- §2's width, in machine words, as an index term. -/
def width (τ : Ty) : Option Idx := (info top τ).width

/-- The sum tier, for a type whose head is `+`. -/
def tier (τ : Ty) : Tier := (info top τ).arms.tier

end Ty

/-! ## §3a. `Zeroable`

Is the all-zeros representation a legal inhabitant?  Separate from `info`
because the answer depends on **index values**, which width does not: since
row 15, the null word inhabits `Loc μ (Array n τ)` exactly when `n = 0`.

So `zeroableIn` carries what is known about each index variable.  An `∃n`
contributes `n = 0` — the zero word's `Int(n)` fields read 0, so 0 is the only
witness worth trying, and trying one witness is sound (zeroable ⇒ some witness
works).  A `∀n` contributes nothing, so anything that depends on `n` fails.

That is exactly what makes the empty slice and the empty vector free: at the
witness `0`, the base is a `Loc` to a zero-length array (null is legal), the
length is `Int(0)` (zero is legal), and `ini ν ≥ 0` holds of anything. -/

/-- Known values of index variables, innermost first. -/
abbrev IEnv := List (Option Nat)

def Idx.evalIn (env : IEnv) : Idx → Option Nat
  | .lit n    => some n
  | .var k    => env[k]?.join
  | .add i j  => return (← i.evalIn env) + (← j.evalIn env)
  | .sub i j  => return (← i.evalIn env) - (← j.evalIn env)
  | .smul n i => return n * (← i.evalIn env)

/-- Does a refinement hold of the zero word, given `env`?  Pure constraints
are evaluated when their indices are known.  `ini ν ≥ i` holds of *any*
reference when `i = 0`, and is otherwise not known to hold of null. -/
def Pred.zeroHolds (env : IEnv) : Pred → Bool
  | .tt      => true
  | .le i j  => (do pure (decide ((← i.evalIn env) ≤ (← j.evalIn env)))) == some true
  | .eq i j  => (do pure (decide ((← i.evalIn env) = (← j.evalIn env)))) == some true
  | .and p q => p.zeroHolds env && q.zeroHolds env
  | .ini i   => i.evalIn env == some 0

/-- A property of type variable `k`: from its kind if it has one, `onRec` if it
is bound by `μ`, and `false` (the worst case) if it is free. -/
def KEnv.ask (ke : KEnv) (k : Nat) (onRec : Bool) (f : Kind → Bool) : Bool :=
  match ke[k]? with
  | some (some κ) => f κ
  | some none     => onRec
  | none          => false

/-- Can this (non-sum) arm of a niche sum be payload-free — a zero-width arm,
or a `Ptr?`-shaped one (its null)?  TermRun's `armK` is `nil` or `opt`. -/
def Ty.payloadFree (t : Ty) : Bool :=
  let a := (info Ty.top t).arms
  a == Arms.optArm || (a.wide == 0 && a.ptrs == 0)

mutual
/-- `Zeroable`, under known index values and type-variable kinds. -/
def zeroableIn (env : IEnv) (ke : KEnv) : Ty → Bool
  | .unit       => true
  | .void       => false
  | .int        => true
  | .intS i     => i.evalIn env == some 0
  | .fix _ _    => true
  | .lanes _ _  => true
  | .prod a b   => zeroableIn env ke a && zeroableIn env ke b
  -- A sum is `Zeroable` iff its *zero arm* is: the arm the all-zeros word
  -- decodes to.  Niche: the first payload-free arm (the payload-free arms share
  -- slot 0, and the first of them is the zero word).  Wide: tag 0, the leftmost
  -- inhabited arm, with a zero payload.  Boxed: none (a null box is not a sum).
  -- Arms are flattened as the runtime flattens them (`TermRun.armsOf`).
  | .sum a b    =>
      match (Ty.sum a b).tier with
      | .niche => (zeroArmP Ty.payloadFree env ke a <|> zeroArmP Ty.payloadFree env ke b) == some true
      | .wide  => (zeroArmP (fun _ => true) env ke a <|> zeroArmP (fun _ => true) env ke b) == some true
      | .boxed => false
  | .code _ _ _ => false
  | .tid        => false   -- (E1) sealed: `zero[ThreadId]` would forge thread 0
  | .opq _      => false   -- (M1) sealed: `zero[Reg]` would forge register 0
  | .array _ t  => zeroableIn env ke t
  | .ptr _ _    => false
  | .ptrOpt _ _ => true
  -- §7 row 15: null is a `Loc` only to a zero-length region, which no access
  -- can reach — every access needs `k < n` — so there is no null check.
  | .loc _ (.array i _) => i.evalIn env == some 0
  | .loc _ _    => false
  -- §3.11: a kinded variable is `Zeroable` if its kind says so.  A `μ`-bound
  -- one is not: the zero word is finite, so it cannot rely on the recursion.
  -- §7 row 20: a zeroed protocol word would be in a state nobody entered, and a
  -- zero-width token conjured by allocation would be a region from nowhere.
  | .word _ _   => false
  | .tok _ _    => false
  | .word2 _ _  => false
  | .tok2 _ _ _ _ => false
  | .epair _ _  => false
  | .tokE _ _ _ => false
  | .share _    => false
  | .cap _ _    => false
  | .tvar k     => ke.ask k false (·.zero)
  | .mu t       => zeroableIn env (none :: ke) t
  | .tex _ _    => false
  | .iall t     => zeroableIn (none :: env) ke t
  | .iex t      => zeroableIn (some 0 :: env) ke t
  | .refine t ψ => zeroableIn env ke t && ψ.zeroHolds env

/-- The zeroability of the first arm of a nest of `+` that `sel` picks
(flattened through wrappers, as `TermRun.armsOf`); `none` if it picks none.
The zero arm: `sel = fun _ => true` (tier 2, tag 0, the leftmost inhabited
arm) or `Ty.payloadFree` (tier 1, the first payload-free arm). -/
def zeroArmP (sel : Ty → Bool) (env : IEnv) (ke : KEnv) : Ty → Option Bool
  | .sum a b     => zeroArmP sel env ke a <|> zeroArmP sel env ke b
  | .void        => none
  | .refine t ψ  => (zeroArmP sel env ke t).map (· && ψ.zeroHolds env)
  | .iall t      => zeroArmP sel (none :: env) ke t
  | .iex t       => zeroArmP sel (some 0 :: env) ke t
  | .mu t        => zeroArmP sel env (none :: ke) t
  | .tex _ t     => (zeroArmP sel env (none :: ke) t).map fun _ => false
  | t            => if sel t then some (zeroableIn env ke t) else none
end

namespace Ty

/-- §3.6's `Zeroable` for a closed type. -/
def zeroable (τ : Ty) : Bool := zeroableIn [] [] τ

/-! ## §3.8's view-sensitivity -/

/-- `ini` on a reference to `Zeroable` elements holds at every view, because
pre-zeroed pages are below every view (§3.6, §3.8's `Zeroable` row). -/
def pointeeZeroableIn (ke : KEnv) : Ty → Bool
  | ptr _ (array _ e)    => zeroableIn [] ke e
  | loc _ (array _ e)    => zeroableIn [] ke e
  | ptrOpt _ (array _ e) => zeroableIn [] ke e
  | ptr _ e              => zeroableIn [] ke e
  | loc _ e              => zeroableIn [] ke e
  | ptrOpt _ e           => zeroableIn [] ke e
  | _                    => false

/-- Can this type's refinement fail at some view?  Structural, and does not
look under references: a reference's target is re-checked at the dereference,
which is where §3.8's load rules force the reader to pay.

`tex κ` is sensitive unless its kind says the witness is not (§3.11).  With the
top kind that is `true`, which is §3.9's rule and 10b's repair: the witness is
hidden, and a closure's call dereferences it without the caller seeing its
type.  A kinded `tvar` answers from its kind; a `μ`-bound one conservatively
`true`, though under the guard this function never reaches it. -/
def sensitiveIn (ke : KEnv) : Ty → Bool
  | prod a b   => sensitiveIn ke a || sensitiveIn ke b
  | sum a b    => sensitiveIn ke a || sensitiveIn ke b
  | array _ t  => sensitiveIn ke t
  | mu t       => sensitiveIn (none :: ke) t
  | iall t     => sensitiveIn ke t
  | iex t      => sensitiveIn ke t
  | tex κ t    => !κ.insens || sensitiveIn (some κ :: ke) t
  | tvar k     => !ke.ask k false (·.insens)
  | refine t ψ => sensitiveIn ke t || (ψ.hasIni && !pointeeZeroableIn ke t)
  -- A frozen handle licenses plain loads of the region, so whoever gets one
  -- must have seen the stores that initialised it: it travels by rel/acq.
  | cap .frz _ => true
  | _          => false

def sensitive (τ : Ty) : Bool := sensitiveIn [] τ

/-! ## §3.5's representation rule, for packages

§3.5 names three coupled types — sums, slices, closures — and gives sums three
tiers.  It gives *packages* none.  A package is coupled when the variable it
binds is mentioned by two or more of its words (or by a word and its
constraint): then one word says how to read another, which is §3.5's
definition.  The rule is that such a package must fit a granule. -/

/-- How many of the words of `τ`'s flattened product mention type variable
`k` (see `countI`, which uses this for `μ` variables). -/
def countT (k : Nat) : Ty → Nat
  | prod a b   => a.countT k + b.countT k
  | refine t _ => t.countT k
  | iall t     => t.countT k
  | iex t      => t.countT k
  | tex _ t    => t.countT (k + 1)
  | mu t       => t.countT (k + 1) + (if t.tyMentions (k + 1) then t.countT 0 else 0)
  | t          => if t.tyMentions k then 1 else 0

/-- How many of the words of `τ`'s flattened product, plus its refinement
predicates, mention index variable `k`.  (T3c-5c) `μ` and type packages are
looked through: their layout is their body's, word by word (`accs`), so a
torn read can mix their words.  A `μ`'s own variable stands for the whole `μ`
type, so where the body mentions `k`, each word mentioning the `μ` variable
(a reference to the recursive type) mentions `k` too. -/
def countI (k : Nat) : Ty → Nat
  | prod a b   => a.countI k + b.countI k
  | refine t ψ => t.countI k + (if ψ.mentions k then 1 else 0)
  | iall t     => t.countI (k + 1)
  | iex t      => t.countI (k + 1)
  | mu t       => t.countI k + (if t.idxMentions k then t.countT 0 else 0)
  | tex _ t    => t.countI k
  | t          => if t.idxMentions k then 1 else 0

def fitsGranule (τ : Ty) : Bool := (τ.width.bind Idx.closed).any (· ≤ 2)

/-- Every coupled package in `τ` (not looking under references) fits in one
16-byte single-copy-atomic access.  Sums need no check: tiering makes every
sum atomic by construction.  A kinded `tvar` passes iff its kind says `share`
(§3.11); a `μ`-bound one passes, since the body it stands for is checked. -/
def coupledOKIn (ke : KEnv) : Ty → Bool
  | prod a b   => coupledOKIn ke a && coupledOKIn ke b
  | sum a b    => coupledOKIn ke a && coupledOKIn ke b
  | array _ t  => coupledOKIn ke t
  | mu t       => coupledOKIn (none :: ke) t
  | iall t     => coupledOKIn ke t
  | refine t _ => coupledOKIn ke t
  | iex t      => coupledOKIn ke t && (decide (t.countI 0 < 2) || (iex t).fitsGranule)
  | tex κ t    => coupledOKIn (some κ :: ke) t &&
                    (decide (t.countT 0 < 2) || (tex κ t).fitsGranule)
  | tvar k     => ke.ask k true (·.share)
  | _          => true

def coupledOK (τ : Ty) : Bool := coupledOKIn [] τ

/-- **§3.11's `noOwn`.**  No `own` reference is reachable from a value of this
type.  Looks *through* `pub` references (what they reach is reachable too) and
stops at `own` ones, which are the violation; `Code` reaches nothing, since its
domain and codomain are argument types, not data. -/
def noOwnIn (ke : KEnv) : Ty → Bool
  | ptr .own _    => false
  | ptrOpt .own _ => false
  | loc .own _    => false
  | ptr .pub t    => noOwnIn ke t
  | ptrOpt .pub t => noOwnIn ke t
  | loc .pub t    => noOwnIn ke t
  -- §7 row 20: what a region holds is the region's, not this thread's, so an
  -- `own` reference inside it is not an escape.  This is row 17, relaxed.
  | ptr (.rgn _) _    => true
  | ptrOpt (.rgn _) _ => true
  | loc (.rgn _) _    => true
  | prod a b      => noOwnIn ke a && noOwnIn ke b
  | sum a b       => noOwnIn ke a && noOwnIn ke b
  | array _ t     => noOwnIn ke t
  | mu t          => noOwnIn (none :: ke) t
  | tex κ t       => κ.noOwn && noOwnIn (some κ :: ke) t
  | iall t        => noOwnIn ke t
  | iex t         => noOwnIn ke t
  | refine t _    => noOwnIn ke t
  | tvar k        => ke.ask k true (·.noOwn)
  | _             => true

def noOwn (τ : Ty) : Bool := noOwnIn [] τ

/-- **Not a protocol word** at the head (through refinements): a cell of this
type may take a plain store or `xchg`.  A type variable answers from its kind:
`noWord`, or `copy` (a word is affine, so a `copy` kind admits none); a
`μ`-bound one stands for a recursive type, never a word. -/
def wordFreeIn (ke : KEnv) : Ty → Bool
  | word _ _   => false
  | word2 _ _  => false
  | epair _ _  => false
  | refine t _ => wordFreeIn ke t
  | tvar k     => ke.ask k true (fun κ => κ.noWord || κ.copy)
  | _          => true

def wordFree (τ : Ty) : Bool := wordFreeIn [] τ

/-- **No inline array** outside references (T3c-5, D1'): an array has no value
layout (width table, `Array` row), so it lives only behind a `Loc`.
A value of a type with an unguarded array could never be built or accessed.
Type variables are array-free because `admitsIn` refuses arrays as arguments. -/
def arrFree : Ty → Bool
  | array _ _  => false
  | prod a b   => arrFree a && arrFree b
  | sum a b    => arrFree a && arrFree b
  | mu t       => arrFree t
  | iall t     => arrFree t
  | iex t      => arrFree t
  | tex _ t    => arrFree t
  | refine t _ => arrFree t
  | _          => true

/-- **The term layer's affinity** (§7 row 20): may a value of this type be used
at most once?  Tokens and protocol-word values carry a region; `own`
references are the §4 invariant.  Stops at references: what is *in* memory is
not in the context.  A kinded variable is affine unless its kind says `copy`;
a `μ`-bound one answers from the body it stands for. -/
def affineIn (ke : KEnv) : Ty → Bool
  | tok _ _       => true
  | share _       => true
  | word _ _      => true
  | word2 _ _     => true
  | tok2 _ _ _ _  => true
  | epair _ _     => true
  | tokE _ _ _    => true
  | ptr .own _    => true
  | ptrOpt .own _ => true
  | loc .own _    => true
  | prod a b      => affineIn ke a || affineIn ke b
  | sum a b       => affineIn ke a || affineIn ke b
  | array _ t     => affineIn ke t
  | iex t         => affineIn ke t
  | iall t        => affineIn ke t
  | tex κ t       => affineIn (some κ :: ke) t
  | refine t _    => affineIn ke t
  | mu t          => affineIn (none :: ke) t
  | opq o         => !o.copyable
  | tvar k        => !ke.ask k true (·.copy)
  | _             => false

def affine (τ : Ty) : Bool := affineIn [] τ

/-- Does a value of this type carry a second-class capability (`bor`, `rd`)?
Structural and conservative: under binders too.  A code pointer carries none:
its *argument* may mention one, and a call must then be handed one, which is
passing it (so a closure may take a capability for its environment's region).
Its result stays conservative, though no block may return one anyway. -/
def secondClass : Ty → Bool
  | cap s _      => s.second
  | prod a b     => a.secondClass || b.secondClass
  | sum a b      => a.secondClass || b.secondClass
  | code _ b _   => b.secondClass
  | array _ t    => t.secondClass
  | ptr _ t      => t.secondClass
  | ptrOpt _ t   => t.secondClass
  | loc _ t      => t.secondClass
  | mu t         => t.secondClass
  | iall t       => t.secondClass
  | iex t        => t.secondClass
  | tex _ t      => t.secondClass
  | refine t _   => t.secondClass
  | _            => false

/-- Second-class capabilities only where a value may hold them: at top level,
through products, sums, refinements and index and type existentials — never
behind a reference or inside code.  (A package is a value like a pair: opening
it binds its body, which is then second-class in turn; `new` and `endBorrow`
see through it, since `secondClass` does.) -/
def scTop : Ty → Bool
  | cap _ _      => true
  | prod a b     => a.scTop && b.scTop
  | sum a b      => a.scTop && b.scTop
  | refine t _   => t.scTop
  | iex t        => t.scTop
  | iall t       => t.scTop
  | tex _ t      => t.scTop
  | t            => !t.secondClass

/-- **§7 row 16, decided: (b)**, and **row 17's `own`-under-`pub` rule.**

Row 16: a coupled package that does not fit a granule may be shared only
where one holder writes it.  So the target of every `pub` reference — `Ptr
pub`, `Ptr? pub`, `Loc pub` — must pass `coupledOK`.  An `own` reference is
exempt, since no other thread can reach it (§4), and so is a region reference
`Ptr (rgn r)` (row 20), since only the holder of `r`'s token may write it.  Row 16
originally said "only inside `Sync`"; the former is gone, and a mutex is now
library code (§5).

Row 17: nothing reachable through a `pub` reference may be an `own` reference.
Row 20 relaxes this at a region boundary: behind `Ptr (rgn r)`, an `own`
reference belongs to the region, and the holder reads it out *as* `Ptr (rgn r)`
(`CoreTerm.lean`'s `adapt`), so it cannot escape as `own`.

A hidden witness is checked through its kind: `∃(α : κ). … Ptr pub α` passes
only if `κ` asserts `share` and `noOwn`, and `pack` checks that the witness has
them (`Kind.admits`).  That replaces row 16's ad-hoc re-check at `pack`. -/
def sharedOKIn (ke : KEnv) : Ty → Bool
  | ptr .pub t    => coupledOKIn ke t && noOwnIn ke t && sharedOKIn ke t
  | ptrOpt .pub t => coupledOKIn ke t && noOwnIn ke t && sharedOKIn ke t
  | loc .pub t    => coupledOKIn ke t && noOwnIn ke t && sharedOKIn ke t
  | ptr .own t    => sharedOKIn ke t
  | ptrOpt .own t => sharedOKIn ke t
  | loc .own t    => sharedOKIn ke t
  | ptr (.rgn _) t    => sharedOKIn ke t
  | ptrOpt (.rgn _) t => sharedOKIn ke t
  | loc (.rgn _) t    => sharedOKIn ke t
  | prod a b      => sharedOKIn ke a && sharedOKIn ke b
  | sum a b       => sharedOKIn ke a && sharedOKIn ke b
  | code a b _    => sharedOKIn ke a && sharedOKIn ke b
  | array _ t     => sharedOKIn ke t
  | mu t          => sharedOKIn (none :: ke) t
  | tex κ t       => sharedOKIn (some κ :: ke) t
  | iall t        => sharedOKIn ke t
  | iex t         => sharedOKIn ke t
  | refine t _    => sharedOKIn ke t
  | _             => true

def sharedOK (τ : Ty) : Bool := sharedOKIn [] τ

/-- The kind `sized i` of a type under `ni` index variables: defined exactly
when the type is well-formed, respects the sharing rule, and its width is
nameable. -/
def kindIn (ni : Nat) (τ : Ty) : Option Idx :=
  if τ.wf 0 ni && τ.sharedOK then τ.width else none

def kind : Ty → Option Idx := kindIn 0

/-- The width of a closed type as a number — what the `#guard`s compare. -/
def words (τ : Ty) : Option Nat := τ.kind.bind Idx.closed

end Ty

/-- **§3.11: `σ` may instantiate a variable of kind `κ`** — at a `pack` of
`∃(α : κ)`, and (once there are terms) at each use of a prenex `∀(α : κ)`.
`σ` must itself be a type, and have every property `κ` asserts.  Stated for
closed `σ`; the open version threads `KEnv` and is the term layer's. -/
def Kind.admits (κ : Kind) (σ : Ty) : Bool :=
  σ.kind.isSome &&
  (!κ.zero   || σ.zeroable) &&
  (!κ.insens || !σ.sensitive) &&
  (!κ.share  || σ.coupledOK) &&
  (!κ.noOwn  || σ.noOwn) &&
  (!κ.copy   || !σ.affine) &&
  (!κ.noWord || σ.wordFree) &&
  κ.atom.holds σ.words

/-- Subkinding: `κ ≤ κ'` when `κ` asserts at least what `κ'` does. -/
def Atom.implies : Atom → Atom → Bool
  | _,     .none => true
  | .word, .word => true
  | .word, .pair => true
  | .pair, .pair => true
  | _,     _     => false

def Kind.le (κ κ' : Kind) : Bool :=
  (!κ'.zero || κ.zero) && (!κ'.insens || κ.insens) && (!κ'.share || κ.share) &&
  (!κ'.noOwn || κ.noOwn) && (!κ'.copy || κ.copy) && (!κ'.noWord || κ.noWord) &&
  κ.atom.implies κ'.atom

/-! ## §4. The guard does what §3.9 says it does

§3.9's claim: under the guard, `width (∃α. τ) = width τ` "with no case analysis
on the witness", and the same for `μα. τ`.  Stated here as: if type variable
`d` is guarded in `τ`, then what `d` is taken to be as wide as cannot change
anything `info` computes — width, tier, or zeroability.  The `mu` and `tex`
clauses of `info` bind their variable to `none` (abstract); this theorem is what
licenses that, since binding it to the width of the unfolding, or of the
witness, would give the same answer. -/

theorem info_irrel (τ : Ty) :
    ∀ (d : Nat) (ρ ρ' : Ctx), τ.unguarded d = false →
      (∀ n, n ≠ d → ρ n = ρ' n) → info ρ τ = info ρ' τ := by
  induction τ with
  | tvar k =>
      intro d ρ ρ' hg h
      have hk : k ≠ d := by simpa [Ty.unguarded] using hg
      simp [info, h k hk]
  | prod a b iha ihb =>
      intro d ρ ρ' hg h
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      simp only [info, iha d ρ ρ' hg.1 h, ihb d ρ ρ' hg.2 h]
  | sum a b iha ihb =>
      intro d ρ ρ' hg h
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      simp only [info, iha d ρ ρ' hg.1 h, ihb d ρ ρ' hg.2 h]
  | array i t ih =>
      intro d ρ ρ' hg h
      simp only [Ty.unguarded] at hg
      simp only [info, ih d ρ ρ' hg h]
  | refine t ψ ih =>
      intro d ρ ρ' hg h
      simp only [Ty.unguarded] at hg
      simp only [info, ih d ρ ρ' hg h]
  | mu t ih =>
      intro d ρ ρ' hg h
      simp only [Ty.unguarded] at hg
      simp only [info]
      apply ih (d + 1) _ _ hg
      intro n hn
      cases n with
      | zero => rfl
      | succ m => exact h m (by omega)
  | tex κ t ih =>
      intro d ρ ρ' hg h
      simp only [Ty.unguarded] at hg
      have := ih (d + 1) (ρ.cons none) (ρ'.cons none) hg (by
        intro n hn
        cases n with
        | zero => rfl
        | succ m => exact h m (by omega))
      simp only [info, this]
  | iall t ih =>
      intro d ρ ρ' hg h
      simp only [Ty.unguarded] at hg
      have := ih d ρ.shiftI ρ'.shiftI hg (by
        intro n hn; simp [Ctx.shiftI, h n hn])
      simp only [info, this]
  | iex t ih =>
      intro d ρ ρ' hg h
      simp only [Ty.unguarded] at hg
      have := ih d ρ.shiftI ρ'.shiftI hg (by
        intro n hn; simp [Ctx.shiftI, h n hn])
      simp only [info, this]
  | _ => intros; rfl

/-- §3.9's sentence, as a theorem: the width of a guarded `∃α. τ` or `μα. τ`
body does not depend on the width of `α`. -/
theorem width_witness_irrelevant (t : Ty) (ρ : Ctx) (w : Option Idx)
    (hg : t.unguarded 0 = false) :
    (info (ρ.cons w) t).width = (info (ρ.cons none) t).width := by
  rw [info_irrel t 0 (ρ.cons w) (ρ.cons none) hg]
  intro n hn
  cases n with
  | zero => exact absurd rfl hn
  | succ m => rfl

/-! ## §5. The library types

None of these is a former.  Each is something a user could have written, which
is the constraint you placed on `Buf`. -/

open Ty Idx

/-- §7 row 14: `Bool ≙ 1 + 1`. -/
def bool : Ty := .sum .unit .unit

/-- §3.9: `σ →[μ] τ  ≙  ∃(α : closure μ). Code (σ × Ptr μ α) τ × Ptr μ α`.  The
kind is §3.11's: a `pub` closure's environment must be shareable and reach
nothing `own`, or `Ptr pub α` would not be a type.  The code receives the
environment *pointer* (24f), not the environment by value: a call copies one
word whatever the environment holds, a closure can keep state in it from call
to call, and `α` occurs only under `Ptr`, which the term layer's `guardT`
requires of a package it will open. -/
def arrow (μ : Mode) (σ τ : Ty) : Ty :=
  .tex (Kind.closure μ)
    (.prod (.code (.prod (σ.shiftT 0) (.ptr μ (.tvar 0))) (τ.shiftT 0) .plain) (.ptr μ (.tvar 0)))

/-- §3.9's "non-capturing case `α = 1`": the arrow's body with the witness
instantiated to `1`. -/
def arrowNoCapture (μ : Mode) (σ τ : Ty) : Ty :=
  .prod (.code (.prod σ (.ptr μ .unit)) τ .plain) (.ptr μ .unit)

/-- The **region arrow**, for an environment in some region, lent with a
capability `s`:

  `σ →[s] τ  ≙  ∃α. ∃r. (Code (∃q. (σ × Cap s q) × Ptr[q] α) τ × Ptr[r] α) × Cap s r`

The package holds the code, the environment pointer, and the capability for the
environment's region (zero width: still two coupled words).  A call packs the
region back into the argument, so the code block is written once for every
region (`fnptr` needs a monomorphic block) and receives the capability with the
environment.  One library serves every holder (`Caps.lean`): an own environment
is a region lent with `borrow bor t`, and a published one is opened with
`openPub`, whose `Cap pub r` subsumes `bor` and `rd`.  Nothing needs publishing.
With `s = pub` the closure is first-class; with `bor`/`rd` it is second-class,
like the capability it holds, and `endBorrow` drops it.  The region is bound in
the type (package targets are closed in indices).  The kind is
`closure (rgn _)`, which asks nothing: the region's rules govern the accesses. -/
def arrowRgn (s : Cap) (σ τ : Ty) : Ty :=
  .tex (Kind.closure (.rgn (.var 0)))
    (.iex (.prod
      (.prod (.code (.iex (.prod (.prod ((σ.shiftT 0).shiftI 0 |>.shiftI 0) (.cap s (.var 0)))
                                 (.ptr (.rgn (.var 0)) (.tvar 0))))
                    ((τ.shiftT 0).shiftI 0) .plain)
             (.ptr (.rgn (.var 0)) (.tvar 0)))
      (.cap s (.var 0))))

/-- §3.7: `Buf μ τ cap init ≙ { ν : Loc μ (Array cap τ) | ini ν ≥ init }`. -/
def buf (μ : Mode) (τ : Ty) (cap init : Idx) : Ty :=
  .refine (.loc μ (.array cap τ)) (.ini init)

/-- §3.7: `Slice μ τ ≙ ∃n. Buf μ τ n n × Int(n)`. -/
def slice (μ : Mode) (τ : Ty) : Ty :=
  .iex (.prod (buf μ (τ.shiftI 0) (.var 0) (.var 0)) (.intS (.var 0)))

/-- §3.7: `Vec μ τ ≙ ∃ cap init len. Buf μ τ cap init × Int(cap) × Int(len)
with len ≤ init ≤ cap`.  De Bruijn: `len = 0`, `init = 1`, `cap = 2`.

Mode-parametric since §7 row 17.  It used to be `Buf own` only, and then
`Sync pub (Vec τ)` — row 16's one way to share a vector — put an `own`
reference behind a `pub` one.  Since row 20 a locked vector can be
`mutex (Vec own τ)` again; `Vec pub τ` is for sharing outside a region, and for
seqlock payloads, which `validate` duplicates. -/
def vec (μ : Mode) (τ : Ty) : Ty :=
  .iex (.iex (.iex (.refine
    (.prod (buf μ (((τ.shiftI 0).shiftI 0).shiftI 0) (.var 2) (.var 1))
           (.prod (.intS (.var 2)) (.intS (.var 0))))
    (.and (.le (.var 0) (.var 1)) (.le (.var 1) (.var 2))))))

/-- §3.5: `List τ ≙ μα. Ptr? μ (τ × α)`. -/
def list (μ : Mode) (τ : Ty) : Ty :=
  .mu (.ptrOpt μ (.prod (τ.shiftT 0) (.tvar 0)))

/-- `n` pointer arms, and `u` payload-free ones, as a right-nested sum. -/
def ptrSum : Nat → Nat → Ty
  | 0,     0     => .void
  | 0,     1     => .unit
  | 0,     u + 1 => .sum .unit (ptrSum 0 u)
  | 1,     0     => .ptr .own .int
  | n + 1, u     => .sum (.ptr .own .int) (ptrSum n u)

/-! ### Synchronisation, derived  (§7 row 20)

There is no lock former.  A mutex is a protocol word next to a pointer into
the region it guards, and `lock`/`unlock` are ordinary code (`CoreTerm.lean`).
The seqlock is the same shape with a different protocol. -/

/-- `0 ↦ r` (free: the word holds the region), `1 ↦ ∅` (held).  Taking is
`cas 0 1`; giving back is `store 1 → 0`.  Not monotone: it returns to `0`, which
is why a mutex has no optimistic readers. -/
def mutexP : Proto := ⟨[⟨0, 0, true⟩, ⟨0, 1, false⟩], [(0, 1, 0), (1, 0, 0)], false, [], [], [], false, false, false, false, false, []⟩

/-- `2k ↦ r` (readable), `2k+1 ↦ ∅` (a writer holds it); `2k → 2k+1` takes,
`2k+1 → 2(k+1)` gives.  Strictly increasing, so a state once left never comes
back — the version measure §4.4 rule 6 needs. -/
def seqP : Proto := ⟨[⟨2, 0, true⟩, ⟨2, 1, false⟩], [(0, 1, 0), (1, 0, 1)], false, [], [], [], false, false, false, false, false, []⟩

/-- `∃r. Ptr pub (Word[r, P] × Ptr r τ)`: a protocol word and the region it
governs. -/
def guardedBy (P : Proto) (τ : Ty) : Ty :=
  .iex (.ptr .pub (.prod (.word (.var 0) P) (.ptr (.rgn (.var 0)) (τ.shiftI 0))))

def mutex (τ : Ty) : Ty := guardedBy mutexP τ
def seqLock (τ : Ty) : Ty := guardedBy seqP τ

/-! ## §5a. Torn representations

What a reader that holds nothing may see: a seqlock reader, racing a writer
that updates the payload one access at a time.  `tear τ` is the type of such a
read.  It is **not** a new value former: it has the same width as `τ`, and it is
built from `τ`'s own pieces.

The pieces are `τ`'s **single-copy-atomic units**, not its words.  §3.5 makes
every coupled representation atomic: a sum is atomic by tier, and a coupled
package that fits a granule is one pair access.  Those never tear.  What tears
is an uncoupled product, and a coupled package too wide for a granule (`Vec`),
which is only legal where one holder writes it (row 16).

Tearing erases coupling.  Every binder (`∃n`, `∃α`, `∀n`) is pushed down onto
each unit that mentions it, so **each unit gets its own witness**.  A refinement
that spans units is dropped, and one on a single unit (`Buf`'s `ini`) is kept.
`μ` is unfolded once when its body splits.  The unfolding's recursive
occurrences sit under references, which are units and are left alone, because a
torn read tears the words it reads, not what they point to.

Soundness of that last clause is not free, and it is not claimed here.  A
pointer word read torn may point to data the reader has not been ordered after,
so a torn value is **opaque** in the term layer.  It cannot be dereferenced,
stored or passed on, and its only elimination is `validate` (§4.4). -/

namespace Pred

/-- Remove index binder `c`; only meaningful when `¬ mentions c`. -/
def lower (c : Nat) : Pred → Pred
  | tt      => tt
  | le i j  => le (i.lower c) (j.lower c)
  | eq i j  => eq (i.lower c) (j.lower c)
  | and p q => and (p.lower c) (q.lower c)
  | ini i   => ini (i.lower c)

end Pred

namespace Ty

/-- Remove index binder `c`; only meaningful when `¬ idxMentions c`. -/
def lowerI (c : Nat) : Ty → Ty
  | intS i       => intS (i.lower c)
  | prod a b     => prod (a.lowerI c) (b.lowerI c)
  | sum a b      => sum (a.lowerI c) (b.lowerI c)
  | code a b k   => code (a.lowerI c) (b.lowerI c) k
  | array i t    => array (i.lower c) (t.lowerI c)
  | ptr μ t      => ptr (μ.lower c) (t.lowerI c)
  | ptrOpt μ t   => ptrOpt (μ.lower c) (t.lowerI c)
  | loc μ t      => loc (μ.lower c) (t.lowerI c)
  | word r P     => word (r.lower c) P
  | tok r st     => tok (r.lower c) (st.map fun (P, i) => (P, i.lower c))
  | word2 r P    => word2 (r.lower c) P
  | tok2 r P i j => tok2 (r.lower c) P (i.lower c) (j.lower c)
  | epair r P    => epair (r.lower c) P
  | tokE r P e   => tokE (r.lower c) P (e.lower c)
  | share r      => share (r.lower c)
  | cap s r      => cap s (r.lower c)
  | mu t         => mu (t.lowerI c)
  | tex κ t      => tex κ (t.lowerI c)
  | iall t       => iall (t.lowerI (c + 1))
  | iex t        => iex (t.lowerI (c + 1))
  | refine t ψ   => refine (t.lowerI c) (ψ.lower c)
  | t            => t

/-- Remove type binder `c`; only meaningful when `¬ tyMentions c`. -/
def lowerT (c : Nat) : Ty → Ty
  | tvar k       => if k > c then tvar (k - 1) else tvar k
  | prod a b     => prod (a.lowerT c) (b.lowerT c)
  | sum a b      => sum (a.lowerT c) (b.lowerT c)
  | code a b k   => code (a.lowerT c) (b.lowerT c) k
  | array i t    => array i (t.lowerT c)
  | ptr μ t      => ptr μ (t.lowerT c)
  | ptrOpt μ t   => ptrOpt μ (t.lowerT c)
  | loc μ t      => loc μ (t.lowerT c)
  | mu t         => mu (t.lowerT (c + 1))
  | tex κ t      => tex κ (t.lowerT (c + 1))
  | iall t       => iall (t.lowerT c)
  | iex t        => iex (t.lowerT c)
  | refine t ψ   => refine (t.lowerT c) ψ
  | t            => t

/-- Substitute `s` for type variable `j`, removing the binder. -/
def substT (j : Nat) (s : Ty) : Ty → Ty
  | tvar k       => if k == j then s else if k > j then tvar (k - 1) else tvar k
  | prod a b     => prod (substT j s a) (substT j s b)
  | sum a b      => sum (substT j s a) (substT j s b)
  | code a b k   => code (substT j s a) (substT j s b) k
  | array i t    => array i (substT j s t)
  | ptr μ t      => ptr μ (substT j s t)
  | ptrOpt μ t   => ptrOpt μ (substT j s t)
  | loc μ t      => loc μ (substT j s t)
  | mu t         => mu (substT (j + 1) (s.shiftT 0) t)
  | tex κ t      => tex κ (substT (j + 1) (s.shiftT 0) t)
  | iall t       => iall (substT j (s.shiftI 0) t)
  | iex t        => iex (substT j (s.shiftI 0) t)
  | refine t ψ   => refine (substT j s t) ψ
  | t            => t

/-- Did tearing split this type into several units?  A torn type is a tree of
`prod` and `array` nodes whose leaves are units, and no unit has either at its
head. -/
def split : Ty → Bool
  | prod _ _  => true
  | array _ _ => true
  | _         => false

/-- Push index binder 0 down onto every unit that mentions it, wrapping with
`mk` (`iex` or `iall`); lower it out of the rest.  Fails on an inline array
whose *length* is the bound index: that type has no width (§7 finding 2), so it
is not a type to begin with. -/
def bindI (mk : Ty → Ty) : Ty → Option Ty
  | prod a b  => do pure (prod (← bindI mk a) (← bindI mk b))
  | array i e => if i.mentions 0 then none else do pure (array (i.lower 0) (← bindI mk e))
  | u         => some (if u.idxMentions 0 then mk u else u.lowerI 0)

/-- The same for a type binder `∃(α : κ)`. -/
def bindT (κ : Kind) : Ty → Ty
  | prod a b  => prod (bindT κ a) (bindT κ b)
  | array i e => array i (bindT κ e)
  | u         => if u.tyMentions 0 then tex κ u else u.lowerT 0

/-- A package that §3.5 stores in one access: its variable couples two or more
units, and it fits a granule. -/
def atomicI (t : Ty) : Bool := decide (t.countI 0 ≥ 2) && (iex t).fitsGranule
def atomicT (κ : Kind) (t : Ty) : Bool := decide (t.countT 0 ≥ 2) && (tex κ t).fitsGranule

/-- **The torn form of `τ`**: what a load of `τ` can return when each atomic
unit may come from a different write. -/
def tear : Ty → Option Ty
  | prod a b   => do pure (prod (← tear a) (← tear b))
  | array i t  => do pure (array i (← tear t))
  | iex t      => if atomicI t then some (iex t) else (tear t).bind (bindI iex)
  -- `∀` needs no erasure: a value is in every instance or it is not, word by
  -- word.  It is distributed only to keep the tree shape for outer binders.
  | iall t     => (tear t).bind (bindI iall)
  | tex κ t    => if atomicT κ t then some (tex κ t) else (tear t).map (bindT κ)
  | refine t ψ => (tear t).map fun t' => if t'.split then t' else refine t' ψ
  | mu t       => (tear t).map fun t' => if t'.split then substT 0 (mu t) t' else mu t
  | t          => some t

/-- Width as a number, without `kind`'s sharing check: `Vec` is not shareable,
and that is the point of tearing it. -/
def rawWords (τ : Ty) : Option Nat := τ.width.bind Idx.closed

end Ty

/-- `(∃cap init. Buf pub Int cap init) × (∃cap. Int(cap)) × (∃len. Int(len))`:
three independent witnesses, and `len ≤ init ≤ cap` gone. -/
def tornVecInt : Ty :=
  .prod (.iex (.iex (.refine (.loc .pub (.array (.var 1) .int)) (.ini (.var 0)))))
        (.prod (.iex (.intS (.var 0))) (.iex (.intS (.var 0))))

-- The package that motivated it: a `Vec` tears into three units, each with its
-- own witness, and the result is shareable where `Vec` itself is not (row 16).
#guard Ty.tear (vec .pub .int) == some tornVecInt
#guard !(vec .pub .int).coupledOK
#guard tornVecInt.coupledOK
#guard (Ty.ptr .pub tornVecInt).sharedOK
#guard !(Ty.ptr .pub (vec .pub .int)).sharedOK

-- (T3c-5c) Coupling is counted through `μ` and `∃α`, whose words are laid out
-- one by one: `∃n. μα. Int(n) × Int × Int(n)` (three units) is not shareable.
#guard !(Ty.ptr .pub (.iex (.mu (.prod (.intS (.var 0)) (.prod .int (.intS (.var 0))))))).sharedOK
#guard !(Ty.ptr .pub (.iex (.tex { share := true, noOwn := true }
    (.prod (.intS (.var 0)) (.prod .int (.intS (.var 0))))))).sharedOK
#guard !(Ty.ptr .pub (.tex { share := true, noOwn := true }
    (.mu (.prod (.ptr .pub (.tvar 1)) (.prod .int (.ptr .pub (.tvar 1))))))).sharedOK
-- and the `μ` variable counts as mentioning what the `μ` mentions:
-- `∃n. μβ. Int(n) × Int × Ptr pub β` (three units) is coupled across its
-- first and last words.
#guard !(Ty.ptr .pub (.iex (.mu (.prod (.intS (.var 0)) (.prod .int (.ptr .pub (.tvar 0))))))).sharedOK

-- What never tears: a slice (coupled, fits a granule, one pair access), a
-- closure (the same, through `∃α`), every sum tier, and a `μ` whose body is a
-- single reference.
#guard Ty.tear (slice .pub .int) == some (slice .pub .int)
#guard Ty.tear (arrow .pub .int .int) == some (arrow .pub .int .int)
#guard Ty.tear (.sum .int .int) == some (.sum .int .int)
#guard Ty.tear (ptrSum 2 1) == some (ptrSum 2 1)
#guard Ty.tear (list .pub .int) == some (list .pub .int)

-- An uncoupled package tears, and its witness goes to the one word that uses it.
#guard Ty.tear (.iex (.prod .int (.intS (.var 0)))) == some (.prod .int (.iex (.intS (.var 0))))

-- A `μ` whose body splits is unfolded once; the recursion stays under the pointer.
#guard let body : Ty := .prod .int (.ptrOpt .pub (.tvar 0))
       Ty.tear (.mu body) == some (.prod .int (.ptrOpt .pub (.mu body)))

-- Tearing goes inside inline arrays, element by element.
#guard Ty.tear (.array (.lit 4) (vec .pub .int)) == some (.array (.lit 4) tornVecInt)

-- The one refusal is a type that has no width anyway (§7 finding 2).
#guard let bad : Ty := .iex (.prod (.array (.var 0) .int) (.intS (.var 0)))
       Ty.tear bad == none && bad.width == none

/-- The types the next two guards range over. -/
def tearSamples : List Ty :=
  [.int, .prod .int .int, slice .pub .int, vec .pub .int, vec .own (.ptr .own .int),
   arrow .pub .int .int, arrow .own (vec .own .int) .int, list .pub .int,
   ptrSum 1 1, ptrSum 2 1, .sum .int .int, .array (.lit 4) (.prod .int .int),
   .prod .int (slice .pub .int), .mu (.prod .int (.ptrOpt .pub (.tvar 0))),
   .array (.lit 3) (vec .pub .int)]

-- A torn value occupies exactly the words the value did: tearing changes what
-- a reader may assume, never the layout.
#guard tearSamples.all fun τ => (Ty.tear τ).bind Ty.rawWords == τ.rawWords
-- Tearing is idempotent: a torn type has nothing left to erase.
#guard tearSamples.all fun τ => ((Ty.tear τ).bind Ty.tear) == Ty.tear τ
-- And everything it produces passes `coupledOK`, even from types that do not.
#guard tearSamples.all fun τ => ((Ty.tear τ).map Ty.coupledOK) == some true
#guard !tearSamples.all Ty.coupledOK

/-! ## §6. The note's tables, pinned

Each block pins one specification table.  A row that was revised during mechanisation
is marked `-- §7 finding N` and states what the function computes. -/

-- §2's width table
#guard unit.words = some 0
#guard void.words = some 0                                  -- §7 row 13
#guard int.words = some 1
#guard (intS (lit 7)).words = some 1
#guard (prod int int).words = some 2
#guard (code int int .plain).words = some 1
#guard (array (lit 4) (prod int int)).words = none          -- F4: an inline array has no width
#guard (ptr .own (prod int int)).words = some 1
#guard (ptrOpt .own int).words = some 1
#guard (loc .pub int).words = some 1
#guard (mutex (prod int int)).words = some 1
#guard (tok (lit 0) none).words = some 0
#guard (word (lit 0) mutexP).words = some 1
#guard (refine int (.le (lit 0) (lit 1))).words = some 1
#guard bool.words = some 1                                  -- §7 row 14
#guard (buf .own int (lit 4) (lit 2)).words = some 1
#guard (slice .own int).words = some 2
#guard (vec .own int).words = some 3
#guard (list .pub int).words = some 1
#guard (arrow .own int int).words = some 2
#guard (arrowNoCapture .own int int).words = some 2         -- §7 finding 1
-- The region arrow: two coupled words, like the others (the capability is zero
-- width).  Its code argument mentions a capability, but a code pointer carries
-- none; the package's own capability is what makes a `bor` closure second-class.
#guard (arrowRgn .bor int int).words = some 2
#guard (arrowRgn .bor int int).wf 0 0                  -- closed: a package target
#guard (arrowRgn .bor int int).secondClass             -- holds a `bor`: passed, never kept
#guard (arrowRgn .bor int int).scTop                   -- so it may be an argument
#guard !(arrowRgn .pub int int).secondClass            -- a `pub` one is first-class
#guard !(Ty.code (arrowRgn .bor int int) int .plain).secondClass   -- taking one holds none
-- What stays second-class: a capability as a value, anywhere it could be kept.
#guard (cap .bor (lit 0)).secondClass
#guard (prod int (cap .rd (lit 0))).secondClass
#guard (ptr .own (cap .bor (lit 0))).secondClass
#guard !(ptr .own (cap .bor (lit 0))).scTop
#guard (code int (cap .bor (lit 0)) .plain).secondClass              -- a result stays conservative
#guard !(cap .pub (lit 0)).secondClass                        -- `pub` is first-class

-- §2: index quantification is erased, but only when the width does not
-- mention the bound variable.  `∃n. Array n Int` is `unsized`, and is refused.
#guard (iex (array (var 0) int)).kind = none                -- §7 finding 2
#guard (iex (ptr .own (array (var 0) int))).words = some 1
-- ...and a two-dimensional array with both extents variable has no linear width.
#guard (array (var 0) (array (var 1) int)).kindIn 2 = none  -- §7 finding 4
#guard (array (var 0) (array (lit 3) int)).kindIn 1 = none  -- F4

-- §3.5's tier table
#guard bool.tier = .niche
#guard (ptrOpt .own int).words = some 1
#guard (sum (ptr .own int) (ptr .own unit)).tier = .niche
#guard (ptrSum 7 0).tier = .niche
#guard (ptrSum 8 0).tier = .wide       -- F3: the payload-free slot is always reserved
#guard (ptrSum 7 3).tier = .niche
#guard (ptrSum 8 1).tier = .wide       -- 9 slots: over budget, but every arm is one word
-- F3: turning one pointer arm into `Ptr?` (a subtype step) keeps the tier.
#guard [1, 6, 7, 8].all fun n =>
  (ptrSum n 0).tier = (sum (ptrOpt .own int) (ptrSum (n - 1) 0)).tier
#guard (ptrSum 9 0).tier = .wide
#guard (sum int (ptr .own int)).tier = .wide
#guard (sum int (ptr .own int)).words = some 2
#guard (sum int int).tier = .wide
#guard (sum (prod int int) int).tier = .boxed
#guard (sum (prod int int) int).words = some 1
-- flattening: association does not change the width
#guard (sum int (sum int int)).words = (sum (sum int int) int).words
#guard (sum int (sum int int)).words = some 2
-- `Void` arms cost nothing
#guard (sum void (ptr .own int)).tier = .niche

-- §3.6's `Zeroable` table
#guard unit.zeroable
#guard int.zeroable
#guard (ptrOpt .own int).zeroable
#guard !(ptr .own int).zeroable
#guard (prod int (ptrOpt .own int)).zeroable
#guard (array (lit 3) int).zeroable
#guard bool.zeroable                                   -- `false` is the zero word
#guard !(sum (ptr .own int) (ptr .own unit)).zeroable  -- slot 0 is a pointer
#guard !(arrow .own int int).zeroable
#guard !void.zeroable
-- The zero arm: a niche sum's is its first payload-free arm.
#guard !(sum (tok (lit 0) none) (ptr .pub int)).zeroable  -- a token arm is not
#guard !(sum (loc .own int) (ptr .pub int)).zeroable      -- null `Loc`, not Zeroable
#guard (sum (ptr .pub int) unit).zeroable                 -- `unit` takes slot 0
#guard (mu (sum unit (ptr .own (prod int (tvar 0))))).zeroable  -- the empty list
-- §7 row 15, decided (c): null is a `Loc` only to a zero-length region.
#guard (loc .own (array (lit 0) int)).zeroable
#guard !(loc .own (array (lit 3) int)).zeroable
#guard !(loc .own int).zeroable
#guard (buf .own (ptr .own int) (lit 0) (lit 0)).zeroable     -- even of non-`Zeroable` τ
#guard !(buf .own int (lit 4) (lit 0)).zeroable
#guard (slice .own int).zeroable                        -- `(null, 0)`, the empty slice
#guard (vec .own int).zeroable                               -- ...and the empty vector
-- `(null, n)` with `n > 0` has no type: pin the length and null is refused.
#guard !(prod (buf .own int (lit 5) (lit 5)) (intS (lit 5))).zeroable
-- Under `∀n` nothing is known about `n`, so nothing depending on it is zero.
#guard !(iall (loc .own (array (var 0) int))).zeroable

-- §3.8's view-sensitivity table
#guard !int.sensitive
#guard !(code int int .plain).sensitive
#guard !(ptr .own (buf .own (ptr .own int) (lit 4) (lit 2))).sensitive
#guard !(buf .own int (lit 4) (lit 2)).sensitive              -- `Zeroable` elements
#guard (buf .own (ptr .own int) (lit 4) (lit 2)).sensitive    -- otherwise
#guard !(slice .own int).sensitive
#guard (slice .own (ptr .own int)).sensitive
#guard (prod int (buf .own (ptr .own int) (lit 4) (lit 2))).sensitive
#guard (arrow .own int int).sensitive                        -- §3.9, derived
#guard !(list .pub int).sensitive

-- §3.9: the arrow is well-formed.  (Before 24f the code took `σ × α`, and it was
-- well-formed only because `Code` counts as a guard; now `α` is under `Ptr`.)
#guard (arrow .own int int).kind.isSome
#guard (code (prod int (tvar 0)) int .plain).tyMentions 0          -- §7 finding 3

-- §3.5's representation rule, applied to packages
#guard (slice .own int).coupledOK
#guard (arrow .own int int).coupledOK
#guard !(vec .own int).coupledOK                                  -- §7 finding 6
-- ...and row 16's decision: shared only where one holder writes it — an `own`
-- reference, or a region (row 20, which replaced the `Sync` former).
#guard (ptr .own (vec .own int)).kind.isSome
#guard (ptr .pub (vec .pub int)).kind = none
#guard (loc .pub (prod int (vec .pub int))).kind = none
#guard (mutex (vec .pub int)).kind.isSome
#guard (mutex (vec .own int)).kind.isSome                    -- row 20: region-held `own`
#guard (seqLock (vec .pub int)).kind.isSome
#guard !(word (lit 0) mutexP).zeroable                        -- a state nobody entered
#guard !(tok (lit 0) none).zeroable
#guard (ptr .pub (slice .pub int)).kind.isSome               -- two words: fits

-- §7 row 17: nothing reachable through `pub` is `own`, except through a region.
#guard (ptr .pub (ptr .own int)).kind = none
#guard (mutex (ptr .own int)).kind.isSome                   -- row 20 relaxes row 17
#guard (ptr .pub (ptr .pub (ptr .own int))).kind = none       -- two hops
#guard (ptr .pub (list .own int)).kind = none
#guard (ptr .pub (list .pub int)).kind.isSome
#guard (ptr .own (ptr .own int)).kind.isSome
#guard (ptr .own (ptr .pub int)).kind.isSome
-- A region is not a way round row 17: `own` directly behind `pub` is still out.
#guard (ptr .pub (prod (word (lit 0) mutexP) (ptr .own int))).kind = none
#guard (ptr .pub (code (ptr .own int) int .plain)).kind.isSome      -- code reaches no data
-- ...so an `own` closure cannot be shared, and a `pub` one can.
#guard (ptr .pub (arrow .own int int)).kind = none
#guard (ptr .pub (arrow .pub int int)).kind.isSome
#guard (arrow .pub int int).kind.isSome

-- §3.11: kinds on `∃`.  `Ptr pub α` is a type only if `α`'s kind says so —
-- row 16's hidden-witness residue, now closed in the kind, not at `pack`.
#guard (tex {} (ptr .pub (tvar 0))).kind = none
#guard (tex { noOwn := true } (ptr .pub (tvar 0))).kind = none
#guard (tex { share := true } (ptr .pub (tvar 0))).kind = none
#guard (tex { share := true, noOwn := true } (ptr .pub (tvar 0))).kind.isSome
#guard (tex {} (ptr .own (tvar 0))).kind.isSome
-- Sensitivity reads the kind; the top kind keeps §3.9 / 10b's `true`.
#guard (arrow .pub int int).sensitive
#guard (tex {} (ptr .own (tvar 0))).sensitive
#guard !(tex { insens := true } (ptr .own (tvar 0))).sensitive
-- ...and `ini` over a kinded element type asks the kind whether it is `Zeroable`.
#guard (tex { insens := true } (buf .own (tvar 0) (lit 4) (lit 2))).sensitive
#guard !(tex { insens := true, zero := true } (buf .own (tvar 0) (lit 4) (lit 2))).sensitive

-- §3.11: `Kind.admits`, the instantiation check.
#guard Kind.top.admits (vec .pub int)
#guard !(Kind.closure .pub).admits (vec .pub int)                 -- row 16: not shareable
#guard (Kind.closure .pub).admits (slice .pub int)
#guard !(Kind.closure .pub).admits (ptr .own int)            -- row 17: reaches `own`
#guard !Kind.top.admits (ptr .pub (ptr .own int))            -- not a type at all
#guard !({ zero := true } : Kind).admits (ptr .own int)
#guard ({ insens := true } : Kind).admits (slice .own int)
#guard !({ insens := true } : Kind).admits (slice .own (ptr .own int))
#guard ({ atom := .word } : Kind).admits int
#guard !({ atom := .word } : Kind).admits (prod int int)
#guard ({ atom := .pair } : Kind).admits (prod int int)
#guard ({ atom := .pair } : Kind).admits (sum int (ptr .own int))   -- tier 2
#guard !({ atom := .pair } : Kind).admits (vec .pub int)
#guard !({ atom := .word } : Kind).admits unit
-- Every kind is inhabited: `Int` has every property a kind can assert.
#guard ({ zero := true, insens := true, share := true, noOwn := true,
          atom := .word } : Kind).admits int
-- Subkinding is pointwise implication; the top kind is the greatest.
#guard (Kind.closure .pub).le Kind.top
#guard !Kind.top.le (Kind.closure .pub)
#guard ({ atom := .word } : Kind).le { atom := .pair }
#guard !({ atom := .pair } : Kind).le { atom := .word }

/-! ## §7. What mechanising the type layer found

Seven disagreements.  Each guard above states what the function computes; this
is why the function, not the note, is taken to be right.  None needs a design
decision to fix except 5, 6 and 7.

1. **A non-capturing closure is two words, not one.**  §2's table and §3 both
   say `σ →[μ] τ` has width 1 "when `α = 1`", as `1 + 0`.  But the
   desugaring's second component is `Ptr μ α`, and a pointer to `1` is still a
   pointer.  Instantiating the witness does not delete a word.  Only a bare
   `Code σ τ` is one word; a function *value* is always two.

2. **Index erasure has a side condition §2 does not state.**  "`∃a. τ` has
   `width τ`" is ill-scoped when `width τ` mentions `a`: `∃n. Array n Int` is
   precisely `unsized`, resurrected by the index existential rather than the
   type one.  `Slice` escapes only because its array sits under `Loc`.

3. **§3.9's guard, read literally, rejects §3.9's own closure.**  It confines
   `α` to "`Ptr`/`Ptr?`/`Loc`", and says the encoding is guarded because "`α`
   appears only under `Ptr μ α`".  It also appears in `Code (σ × α) τ`.  The
   fix is the obvious one and is what `unguarded` does: `Code` is a one-word
   former and guards like a reference.

4. **Array widths are not always linear.**  §3.7 cost 1 says `width τ` "is a
   constant for any fixed `τ` — so array widths stay linear".  Not when `τ` is
   itself an array of variable extent: `Array a (Array b Int)` has width
   `a * b`, and has no kind.  A 2-D array with both extents variable must be an
   array of references.

5. **`Slice` was not `Zeroable` as derived.**  §3.6 said the all-zeros slice is
   `(null, 0)`, the empty slice.  But §3.7 *derives* `Slice` from `Buf`, and
   `Buf` is a refined `Loc` — which, like `Ptr`, had no null.  **Decided (row
   15 (c)):** null inhabits `Loc μ (Array n τ)` exactly when `n = 0`.  No
   access can reach a zero-length region — every one needs `k < n` — so the
   bounds proof subsumes the null check and none is ever emitted; and
   `(null, n)` with `n > 0` is ill-typed, not checked.  `zeroableIn` tracks
   index values to decide it, and the empty `Vec` comes out zero too.  A
   `Loc?` was the rejected alternative: nullness independent of `n` would admit
   `(null, 5)` unless a new `ν ≠ null` atom tied the two back together.

6. **`Vec` is a three-word coupled package, and §3.5 has no tier for it.**
   `cap` is mentioned by the `Buf` and by `Int(cap)`, so one word says how to
   read another — §3.5's definition of coupled — and three words do not fit a
   granule.  A torn `Vec` pairs a new buffer with an old capacity, and `push`
   writes past the allocation: a `stuck` state, the progress failure §2's
   IMPORTANT note already describes for slices.  §3.5's tier 3 is defined only
   for sums.  **Decided (row 16 (b)):** such a package may be shared only
   inside `Sync` — since row 20, inside a region, `Sync` being gone.  `sharedOK` enforces it in the kind.  The one place it could
   not look, a hidden existential witness, is now covered by §3.11's kinds:
   `∃(α : κ). … Ptr pub α` is a type only if `κ` asserts `share`.

7. **`own` could sit behind `pub`.**  `sharedOK` accepted `Ptr pub (Ptr own
   τ)`, and so did every check before it: a shared cell holding a pointer that
   §4.2 promises no other thread can reach.  Found while deciding what a type
   variable's kind must say (§3.11's `noOwn`).  **Decided (row 17):** nothing
   reachable through a `pub` reference is `own`, `Sync pub` included.  It
   broke one earlier decision — `Sync pub (Vec τ)`, row 16's way to share a
   vector, has an `own` buffer — so `Vec` became mode-parametric.

Settled as byproducts, as §7 of the note predicted: **row 13** (`Void`: width 0,
not `Zeroable`, no arm in a sum, no introduction form) and the easy half of
**row 14** (`Bool ≙ 1 + 1`: tier 1, one word, `Zeroable` with `false` as the
zero word).  Row 14's hard half — refined booleans from comparisons — is a
question about terms and is untouched here. -/

-- Read by check-promises.sh: a `sorry` is only a warning, so the gate greps
-- this output for `sorryAx`.
#print axioms info_irrel
#print axioms width_witness_irrelevant

/-! ## §8. Row 18's lemma, sampled: a generic check covers every admitted instance

A polymorphic code block is checked once, with each type parameter answering
from its kind, and then monomorphised.  That is sound only if every property
the checker concludes of a generic type also holds of each instance at an
admitted type.  The directions that matter are one-way: generic `sharedOK`,
`coupledOK` and `noOwn` imply the instance's, and generic *not* view-sensitive
and *not* affine imply the instance's.  Checked over every kind with `atom =
none`, a spread of bodies mentioning `α` = `tvar 0`, and instances that
include the adversarial ones (a token, a protocol word, an `own` reference).
Proved for every kind, body and instance as `KindSound.coversInstances_true`
(T3b-2e), with the general form for the term checker's simultaneous `substTs`
as `KindSound.row18_kinds`; the samples stay as a quick smoke test. -/

def allKinds : List Kind :=
  [false, true].flatMap fun z => [false, true].flatMap fun i => [false, true].flatMap fun s =>
  [false, true].flatMap fun o => [false, true].map fun c =>
    { zero := z, insens := i, share := s, noOwn := o, copy := c }

def genericBodies : List Ty :=
  [.tvar 0, .ptr .pub (.tvar 0), .prod (.tvar 0) .int, .sum (.tvar 0) .unit,
   .ptr .pub (.prod (.tvar 0) (.tvar 0)),
   .mu (.prod (.tvar 1) (.ptrOpt .pub (.tvar 0))),
   .ptr .pub (.mu (.prod (.tvar 1) (.ptrOpt .pub (.tvar 0)))),
   .ptr (.rgn (.lit 0)) (.tvar 0),
   .iex (.prod (.tvar 0) (.intS (.var 0))),
   -- F1: a coupled package with a sum over `α` inside.  Its width must not be
   -- guessed from `α`'s absence: at `α := Int` the sum is wide.
   .iex (.prod (.sum (.tvar 0) (.intS (.var 0))) (.intS (.var 0))),
   .ptr .pub (.iex (.prod (.sum (.tvar 0) (.intS (.var 0))) (.intS (.var 0))))]

def instanceSamples : List Ty :=
  [.int, .unit, .ptr .pub .int, .ptr .own .int, .prod .int .int, .sum .int .unit,
   .tok (.lit 0) none, .word (.lit 0) ⟨[⟨0, 0, true⟩, ⟨0, 1, false⟩], [(0, 1, 0), (1, 0, 0)], false, [], [], [], false, false, false, false, false, []⟩,
   .ptr .pub (.ptr .own .int)]

def coversInstances (κ : Kind) (b σ : Ty) : Bool :=
  let ke : KEnv := [some κ]
  let t := Ty.substT 0 σ b
  !κ.admits σ ||
  ((!b.sharedOKIn ke  || t.sharedOK) &&
   (!b.coupledOKIn ke || t.coupledOK) &&
   (!b.noOwnIn ke     || t.noOwn) &&
   (b.sensitiveIn ke  || !t.sensitive) &&
   (b.affineIn ke     || !t.affine))

#guard allKinds.all fun κ => genericBodies.all fun b => instanceSamples.all (coversInstances κ b)
-- `copy` is what keeps a token or a word out: `noOwn` alone admits both.
#guard ({ noOwn := true } : Kind).admits (.tok (.lit 0) none)
#guard !({ noOwn := true, copy := true } : Kind).admits (.tok (.lit 0) none)
-- `noWord` keeps a protocol word out (and only that): a token is still admitted.
#guard ({ noOwn := true } : Kind).admits (.word (.lit 0) ⟨[⟨0, 0, true⟩], [], false, [], [], [], false, false, false, false, false, []⟩)
#guard !({ noOwn := true, noWord := true } : Kind).admits (.word (.lit 0) ⟨[⟨0, 0, true⟩], [], false, [], [], [], false, false, false, false, false, []⟩)
#guard ({ noOwn := true, noWord := true } : Kind).admits (.tok (.lit 0) none)
-- Row 18 for `wordFree`, sampled: a generic body word-free at its kind is word-free at every
-- admitted instance.  Proved for every kind, body and instance as `KindSound.wordFree_covers`.
#guard allKinds.all fun κ => [Kind.top, { noWord := true }].all fun κ' =>
  let κ := { κ with noWord := κ'.noWord }
  genericBodies.all fun b => instanceSamples.all fun σ =>
    !κ.admits σ || !b.wordFreeIn [some κ] || (Ty.substT 0 σ b).wordFree

/-- Any bit pattern is a value: what a device may write into a cell (decision H). -/
def bitsIn : Ty → Bool
  | .unit => true
  | .fix _ _ => true
  | .lanes _ _ => true
  | .prod a b => bitsIn a && bitsIn b
  | .array _ t => bitsIn t
  | _ => false

end CoreLang
