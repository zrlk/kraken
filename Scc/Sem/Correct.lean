/-
The `scc` correctness statement.

`Correct T S Λ B asm` says that the lowered program `asm`, loaded under the
layout `Λ` into the extended target machine of `T`, is simulated by the
source machine `S` (a WeakCore program with its start configurations), up
to the resource budget `B`. It is the existence of a `Sim`: a relation `R`
between target and source configurations with five properties.

1. **Start** (`Sim.start`). The loader yields a target start configuration
   that `R` relates to a source start configuration. This is unconditional
   (the heap-bytes fallback, which ships first: the image is empty). Route S
   (`RouteS`: the static image of `Λ` is the memory of some start
   configuration of the source, i.e. of some complete run of the setup
   block) is defined but not yet part of `Correct`; once Route S exists it
   becomes a conjunct of `Correct`, not a hypothesis of `start` (as a
   hypothesis, a false `RouteS` made `start` vacuous, and with a loader that
   refuses, everything).
2. **Progress** (`Sim.progress`). Every reachable target configuration has
   no fault and has terminated or has a live thread and lets every live
   thread step; every shared location it has written is inside `Λ`'s shared
   regions (`InLayout`). Resource exhaustion is not stuck: the target then
   runs its abort routine, whose exit is the `abort` outcome.
3. **Simulation** (`Sim.sim`). Every reachable target configuration is
   `R`-related to a reachable source configuration, and the target's trace
   (less its `writeErr`, `cloneErr` and `abort` events, `obs`) is a prefix of that source
   run's trace.
4. **Abort only when justified** (`Sim.abort`). A step of target thread
   `tid` that emits `abort k` after the target trace `tr` is taken from a
   configuration related to a source configuration `s` reachable with trace
   exactly `obs tr` (so the target has produced all the output the source
   produced before the justifying step: no early abort), whose thread `i` is
   mapped to `tid` by the witness of `R`, and the abort of kind `k` is
   justified there
   (`AbortJustified`): for `overflow`, `heap`, `stack` and `threads`, some
   step of thread `i` from `s` leaves the corresponding part of the budget;
   for `threads` also a refused `clone` earlier (the target trace contains
   `Ev.cloneErr`); for `writeErr`, the kernel refused an earlier `write`
   (the target trace contains `Ev.writeErr`). Without this clause a compiler that aborts at
   once would be correct.
5. **`R` is explicit** (`Sim.explicit`). Every `R`-related pair has a
   `Witness` satisfying `Components`: the thread map, the layout injection
   of source labels into address ranges, the value representation (on
   memory messages, timestamp by timestamp, and on register environments),
   and the stack-map clause. The register-environment clauses exempt a
   frame running the output extern's uncompiled model (`ExternFrame`),
   whose locals `scc_rt_print` does not keep. `R` may say more (views, promise sets, runtime
   invariants); these are what every user of the statement can rely on.

Usable consequences: `Sim.transfer` (an invariant of every reachable source
configuration holds of a source configuration related to each reachable
target configuration), `Sim.transfer_stepsG` and `Sim.transfer_stepsX` (the
same for a property proved along WeakCore's `StepsG … Sp` runs, the form of
its token-soundness theorems).

Sanity: `correct_trivial` (the empty program and the empty assembly satisfy
the statement, with every component of `R` checked), and two incorrect
targets that it rejects: one that prints a byte the source does not
(`not_correct_spurious_output`), and one that aborts at once
(`not_correct_spurious_abort`).

**Which targets.** `Target` and `ExtMachine` are records of free fields
(`runs`, `atSys`, `live`, `exited`, `fault`, `stackRange`, `regVal`,
`privLoad`, `pc`, the extension steps, the loader), and an arbitrary instance
can trivialise the statement (`fault := fun _ => False` hides faults).
`Correct` is meaningful only for the canonical `Target` of each ISA, defined
once and part of the trusted base (`Scc/DESIGN.md` §4); a certificate must
state `Correct (targetOf arch) …` for that canonical target, never for a
`Target` supplied by `scc`.
On the canonical targets the certification of promises is the solo
projection of the kernel step (`Kernel.certSem`; `Scc/DESIGN.md` §3.1 lists
where it differs).

**Which budget.** `B` is chosen by whoever produces the certificate, and a
small `B` justifies many aborts. The guarantee reads: correct for every run
whose source stays within `B`; so `scc` prints `B` with each program.

`Scc/DESIGN.md` §1 explains each clause.
-/
import Scc.Sem.Ext
import Scc.Sem.SrcExt
import Scc.PrintModel

namespace Scc.Sem

/-! ## The layout `Λ` -/

/-- **A layout**: where the program's regions are. All addresses are natural
numbers below `2^64`. Thread control blocks live in their own region,
`pinned` (a `ThreadId` is the address of its block), apart from the heap
arena; the stacks come from the shared stack pool.
The pool region holds stack ranges only: the pool's own shared metadata (free
list, cursor) lives in `heap` or `data`, so its writes are shared writes in
`shared` (`InLayout`), and the pool region is only ever accessed as private
stack memory (`stack_private`). -/
structure Layout where
  /-- The text. -/
  code : Range
  /-- The writable static image (`.data`). -/
  data : Range
  /-- The read-only static image (`.rodata`), mapped read-only. Its contents
  are not part of the layout: the canonical loaders lay the text's `.rodata`
  section out from `rodata.lo` (`Scc/Sem/Target.lean`, `rodataWords`) and
  resolve its labels from that image. Not one of `regions` (so `WF` does not
  constrain it); the loaders check that a non-empty image fits it, in the
  address space and clear of `regions` (`rodataFits`). Empty by default. -/
  rodata : Range := ⟨0, 0⟩
  /-- The heap arena (bump allocator for source objects). -/
  heap : Range
  /-- The shared pool that stack ranges are taken from. -/
  stackPool : Range
  /-- **The pinned region** (`scc_rt_pinned`): the thread control blocks,
  each at a fixed address for its thread's life, apart from the heap arena.
  Shared memory: other threads read and write a block's fields (the futex
  permit, `exited`). -/
  pinned : Range
  /-- Where each label allocated before the run (by the setup block) is
  placed in `data` (Route S); `none` for every label with the fallback. -/
  static : WeakMem.AllocLabel → Option Nat
  /-- The initial words of `data`: (address, value). -/
  image : List (Nat × Nat)
  /-- The address of each data symbol the text refers to (the `.data` and
  `.bss` labels: static data, the heap arena, the stack pool, the runtime's
  words), as the linker placed them. `static` places source labels; this
  places assembler names (the compiler names each static label's symbol), so
  that the loader can resolve the text's references. -/
  symbols : List (String × Nat)
  /-- The assembler label of the `exit_group` system call of the abort stub
  of each kind: the extended machine reports an exit issued there as
  `abort k`, not `exit 101`. A label, not an address: the loader resolves it
  in the text it loads, so the classification does not depend on the model
  giving instructions their assembled sizes. -/
  abortLbl : AbortKind → String
  /-- **The colour bits** of a reference word: the reserved metadata bits a
  collector may rewrite in a live slot with no source step (a heal,
  `ColourOnly`). `0` with no collector: then no write is colour-only. -/
  colourMask : Nat := 0
  /-- Whether the runtime may move live objects (a copying collector): only
  then may a witness start a label's placement epoch after its allocation
  in source time (`Witness.since`, `Components.epoch_fixed`). `false` with
  no collector. Without relocation the target-time bound `Witness.tsFrom`
  still marks where a label's placement begins: target messages to its range
  at or before it are earlier writes to recycled memory, constrained by
  `Components.pre_alloc`. -/
  relocates : Bool := false
  /-- **The immediate table** (live immediate constants): the source words
  the code keeps as constants folded into its instructions, at no place.
  Keyed by a frame's remaining term (its control point), a variable and a
  word index, it gives the constant; a witness may place a word at an
  immediate (`WordPlace.imm`) only as the table says (`Components.env_imm`).
  Fixed per program (`scc` emits it from the lowering's placement data), not
  chosen per state. Empty by default: then no word is at an immediate. -/
  imms : CoreTerm.Expr → String → Nat → Option Nat := fun _ _ _ => none

namespace Layout

/-- The five regions. -/
def regions (Λ : Layout) : List Range := [Λ.code, Λ.data, Λ.heap, Λ.stackPool, Λ.pinned]

/-- An address of the data regions, where a data symbol may lie: the static
image, the heap arena, the stack pool or the pinned region. -/
def dataRegion (Λ : Layout) (a : Nat) : Prop :=
  Λ.data.contains a ∨ Λ.heap.contains a ∨ Λ.stackPool.contains a ∨ Λ.pinned.contains a

/-- **Well-formed layout**: regions in the address space, 16-aligned and
pairwise disjoint, above address `0`; the abort stubs at distinct labels;
the image in `data`, word-aligned, of 64-bit values; each data symbol in a
data region, outside the code (below or above it), under its own name. `Λ` has no code address: the abort sites are
labels, which the target resolves (as are the transfer sites, whose labels
are fixed, `XferKind.label`). -/
structure WF (Λ : Layout) : Prop where
  inSpace : ∀ r ∈ Λ.regions, r.InSpace
  aligned : ∀ r ∈ Λ.regions, r.Aligned 16
  disjoint : Λ.code.Disjoint Λ.data ∧ Λ.code.Disjoint Λ.heap ∧ Λ.code.Disjoint Λ.stackPool ∧
    Λ.data.Disjoint Λ.heap ∧ Λ.data.Disjoint Λ.stackPool ∧ Λ.heap.Disjoint Λ.stackPool ∧
    Λ.code.Disjoint Λ.pinned ∧ Λ.data.Disjoint Λ.pinned ∧ Λ.heap.Disjoint Λ.pinned ∧
    Λ.stackPool.Disjoint Λ.pinned
  abortInj : ∀ k k', Λ.abortLbl k = Λ.abortLbl k' → k = k'
  image : ∀ p ∈ Λ.image, Λ.data.contains p.1 ∧ p.1 % 8 = 0 ∧ p.2 < 2 ^ 64
  /-- Every data symbol lies in a data region (`dataRegion`) ... -/
  symIn : ∀ p ∈ Λ.symbols, Λ.dataRegion p.2
  /-- ... outside the code, below or above it (the loaders lay the label
  cells of the symbols below the code out before it and of the others after
  it, and refuse one inside it, `symsAbove`; so no symbol is in `code`,
  `WF.sym_not_code`) ... -/
  symAbove : ∀ p ∈ Λ.symbols, p.2 < Λ.code.lo ∨ Λ.code.lo + Λ.code.size ≤ p.2
  /-- ... and symbol names are distinct (the loader resolves a reference by
  name). -/
  symNodup : (Λ.symbols.map Prod.fst).Nodup
  /-- Every region starts above address `0`, so a placed label's base, and
  hence a location's word, is never the null word `0`. -/
  pos : ∀ r ∈ Λ.regions, 0 < r.lo

/-- No data symbol lies in the code. -/
theorem WF.sym_not_code {Λ : Layout} (h : Λ.WF) {p : String × Nat} (hp : p ∈ Λ.symbols) :
    ¬ Λ.code.contains p.2 := fun hc => by
  have := h.symAbove p hp; simp only [Range.contains] at hc; omega

/-- **A range in the heap or the static image starts above `0`.** -/
theorem WF.lo_pos {Λ : Layout} (h : Λ.WF) {r : Range} (hr : r.Sub Λ.heap ∨ r.Sub Λ.data) : 0 < r.lo := by
  rcases hr with hr | hr
  · have := h.pos Λ.heap (by simp [regions]); exact Nat.lt_of_lt_of_le this hr.1
  · have := h.pos Λ.data (by simp [regions]); exact Nat.lt_of_lt_of_le this hr.1

/-- An address of the shared regions (static image, heap, or the pinned
region of thread control blocks). -/
def shared (Λ : Layout) (a : Nat) : Prop := Λ.data.contains a ∨ Λ.heap.contains a ∨ Λ.pinned.contains a

end Layout

/-! ## The value representation -/

/-- The target address of a source word address, under a label placement
`lbl` (label ↦ base address): `base + 8 · offset`.

This is the linear reading of `Scc/LAYOUT.md` §2 for objects with no trace
words: scalar word `i` of an object at base `b` is at `b + 8i`. Objects with
trace words (references, locative bases, `ThreadId`s in memory) lay those
out below the base, at `b − traceBias − 8j`, which this map does not
describe; M1 is scoped to scalar-only labels (`Scc/DESIGN.md` §8), and the
general map (`Obj.slots`) is M2's. -/
def wordAddr (lbl : WeakMem.AllocLabel → Option Nat) (a : WeakMem.Address) : Option Nat :=
  (lbl a.label).map (· + 8 * a.offset)

/-- **The value representation**: target word `v` represents source value
`x` under the label placement `lbl`.

* `undef`: any word.
* `num n`: the word `n`, which must be below `2^64` (a larger source `Int`
  has no representation: the target aborts first).
* `loc a tag`: the mapped address of `a` plus the tag (a pointer's low bits;
  `tag < 8`, words being 8-aligned).
* `null`: `0`. -/
def ValRep (lbl : WeakMem.AllocLabel → Option Nat) : WeakMem.Val → Nat → Prop
  | .undef, _ => True
  | .num n, v => n < 2 ^ 64 ∧ v = n
  | .loc a tag, v => tag < 8 ∧ ∃ x, wordAddr lbl a = some x ∧ v = x + tag
  | .null, v => v = 0

/-- The 8-byte Kraken location of a target word address. -/
def wordLoc (a : Nat) : Kraken.Promising.Loc := ⟨BitVec.ofNat 64 a, 8⟩

/-- **The 8 bytes at word address `a` of target message `k'`** (of the
initial write when `k' = 0`), if that message's location covers them: the
8-byte location at `a` (`Memory.read?`), else the low half of a 16-byte
location at `a` or the high half of one at `a - 8` (little-endian; a
single-copy-atomic 16-byte access, `casp` or a declared pair). At timestamp
0 it is the initial value of the 8-byte location at `a`. -/
def wordAt (mem : Kraken.Promising.Memory) (a k' : Nat) : Option Nat :=
  match mem.read? (wordLoc a) k' with
  | some v => some v.toNat
  | none =>
    match mem.read? ⟨BitVec.ofNat 64 a, 16⟩ k' with
    | some v => some (v.toNat % 2 ^ 64)
    | none => if 8 ≤ a then (mem.read? ⟨BitVec.ofNat 64 (a - 8), 16⟩ k').map (·.toNat / 2 ^ 64) else none

/-- On an 8-byte message `wordAt` is `Memory.read?`: proofs about 8-byte
accesses only are unchanged. -/
theorem wordAt_of_read {mem : Kraken.Promising.Memory} {a k' : Nat} {v : Kraken.Promising.Val}
    (h : mem.read? (wordLoc a) k' = some v) : wordAt mem a k' = some v.toNat := by
  simp [wordAt, h]

-- A 16-byte message at 64 holds the word 3 at 64 (low half) and 5 at 72
-- (high half), nothing at 80; an 8-byte message is read as itself.
#guard wordAt { init := [], msgs := #[⟨⟨64, 16⟩, BitVec.ofNat 128 (5 * 2 ^ 64 + 3), 0⟩] } 64 1 == some 3 &&
  wordAt { init := [], msgs := #[⟨⟨64, 16⟩, BitVec.ofNat 128 (5 * 2 ^ 64 + 3), 0⟩] } 72 1 == some 5 &&
  wordAt { init := [], msgs := #[⟨⟨64, 16⟩, BitVec.ofNat 128 (5 * 2 ^ 64 + 3), 0⟩] } 80 1 == none &&
  wordAt { init := [], msgs := #[⟨wordLoc 64, 7, 0⟩] } 64 1 == some 7

/-! ## The budget `B` -/

/-- **A resource budget**, in source terms. The target's limits (arena size,
thread slots, per-thread stack cap) are chosen so that a source run within
the budget never exhausts them; that is a fact about `Λ`, not part of the
statement. -/
structure Budget where
  /-- Heap words: distinct source cell addresses in memory. -/
  cells : Nat
  /-- Threads ever created. -/
  threads : Nat
  /-- Per-thread call depth (frames on the source stack). -/
  frames : Nat

/-- The number of distinct cell addresses in a source configuration's memory.
Every allocation (`TermRun.alloc` for `new` and boxed sums, `allocBuf` for
`newBuf`) pushes one first message per word it allocates, `undef` or the
zero of the type, so this is the number of words allocated so far, as long
as later stores and promises are to allocated cells (which the checker
ensures for accepted programs). -/
def cellCount (s : TermRun.Cfg) : Nat := (s.mem.toList.map (·.loc)).eraseDups.length

/-- The number of allocations made so far: the sum of the threads'
allocation counters (`nalloc`, one per `new`, boxed sum or `newBuf`,
including zero-word ones). -/
def allocCount (s : TermRun.Cfg) : Nat := (s.ths.toList.map (·.nalloc)).sum

/-- **Heap use** in words: the words allocated plus one header word per
allocation (the target allocator's header, which a zero-word allocation also
takes). -/
def heapUse (s : TermRun.Cfg) : Nat := cellCount s + allocCount s

/-! ### The heap part under `gc none`: the stand-in and its margin

The heap part of the budget is meant to be target-sized: the bytes of the
objects of the labels counted (all labels with no collector, the live ones
under a collector), each object `8 · (1 + len · (n + m))` bytes in the
bipartite layout (`Scc/LAYOUT.md`) plus any alignment filler. Until WeakCore
exports a per-label closed type, `heapUse` (words plus one header word per
allocation) stands in for it under `gc none`. The margin: the arena bytes the
runtime can consume for allocations whose source sizes are counted by
`heapUse` is at most `16 · heapUse` (`arena_margin`, `arena_covers`), so an
arena of `16 · B.cells` bytes is never exhausted while the heap part holds. -/

/-- **The arena bytes of one allocation** under `gc none`: a header word and
`t` target words, `8 · (1 + t)`, plus `fill` bytes of alignment filler before
it (at most 8: an 8-byte filler when the cursor is misaligned). -/
def objBytes (t fill : Nat) : Nat := 8 * (1 + t) + fill

/-- **The margin of the stand-in**: for allocations given as (source words
`w`, target words `t`, filler `f`), with at most three target words for two
source words (a mixed unit: tag or scalar and a reference in two regions)
and at most 8 filler bytes, the arena bytes are at most 16 per word or
header counted by the source. -/
theorem arena_margin (as : List (Nat × Nat × Nat)) (ht : ∀ a ∈ as, 2 * a.2.1 ≤ 3 * a.1)
    (hf : ∀ a ∈ as, a.2.2 ≤ 8) :
    (as.map fun a => objBytes a.2.1 a.2.2).sum ≤ 16 * ((as.map (·.1)).sum + as.length) := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have h1 := ht a (by simp)
    have h2 := hf a (by simp)
    have := ih (fun b hb => ht b (by simp [hb])) (fun b hb => hf b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, objBytes] at this ⊢
    omega

/-- **The arena covers the heap part**: if the allocations of a source
configuration `s` (as `arena_margin` takes them) account for its words and
its allocation count (`cellCount`, `allocCount`: every allocation pushes one
first message per word to its fresh label, and later stores are to allocated
cells), then within the heap part of `B` they take at most `16 · B.cells`
arena bytes. -/
theorem arena_covers {s : TermRun.Cfg} {B : Budget} (as : List (Nat × Nat × Nat))
    (ht : ∀ a ∈ as, 2 * a.2.1 ≤ 3 * a.1) (hf : ∀ a ∈ as, a.2.2 ≤ 8)
    (hw : (as.map (·.1)).sum = cellCount s) (hn : as.length = allocCount s) (hB : heapUse s ≤ B.cells) :
    (as.map fun a => objBytes a.2.1 a.2.2).sum ≤ 16 * B.cells := by
  have := arena_margin as ht hf
  rw [hw, hn] at this
  unfold heapUse at hB
  omega

-- One word and one header: 16 bytes; three source words of which two form a
-- mixed unit (four target words) after an 8-byte filler: 48 bytes, under
-- 16 · (3 + 1).
#guard objBytes 1 0 == 16 && objBytes 4 8 == 48

/-! ## Free variables of source code -/

/-- The variable an atom reads, if any. -/
def atVars : CoreTerm.At → List String
  | .var x => [x]
  | _ => []

/-- The atoms an operation reads. -/
def opAts : CoreTerm.Op → List CoreTerm.At
  | .atom a | .inl _ a | .inr _ a | .new a | .fold a _ | .publish a | .intoRgn _ a | .newBuf a _
  | .fld _ a | .load _ a | .pack a _ _ | .packT a _ _ | .call _ _ a _ | .borrow _ a | .endBorrow a
  | .nameI a | .bit1 _ a | .freeze a | .cvt _ _ a | .toInt a | .asLanes _ _ a | .fop1 _ a
  | .ldp _ a _ _ | .spawn _ a _ _ | .ext _ a => [a]
  | .pair a b | .add a b | .sub a b | .idx a b | .xchg a b | .callc a b | .rem a b | .loadAt a b
  | .bits _ a b | .band a b | .loadAtF a b _ | .fop _ a b | .fcmp _ a b | .lane a b | .ldl a b
  | .mkWord _ _ a b | .claim a b | .fetch _ _ _ a b | .mkEPair _ _ a b | .mkTicket _ _ _ a b => [a, b]
  | .bufInit a b c | .xchgAt a b c | .vmatch a b c | .xchgAtF a b _ c | .setLane a b c | .stl a b c
  | .ldlw a b c | .mkWord2 _ _ a b c => [a, b, c]
  | .stlw a b c d | .stp _ a b c d => [a, b, c, d]
  | .store _ a v tok => [a, v] ++ tok.toList
  | .null _ _ | .fence _ | .validate _ | .fnptr _ | .zero _ => []

/-- The variables an operation reads: its atoms', and `validate`'s. -/
def opVars (op : CoreTerm.Op) : List String :=
  (opAts op).flatMap atVars ++ match op with
    | .validate y => [y]
    | _ => []

/-- **The free variables of a term**: the variables it reads before binding
them. A construct's name is removed exactly in the scope where the runtime
pushes it on the environment (`TermRun.tstep`), as in WeakCore's
`TermScope.freeB` (`Scc/Sem/Scope.lean`, `mem_exprFv`): `unpack`'s index, the region of
`region`/`openPub` and `parity`'s `k` bind no variable, and `cas`/`casp`
bind `t` in `ok` only. -/
def exprFv : CoreTerm.Expr → List String
  | .let_ x op e => opVars op ++ (exprFv e).filter (· != x)
  | .split a x y e => atVars a ++ (exprFv e).filter (fun z => z != x && z != y)
  | .unpack a _ x e => atVars a ++ (exprFv e).filter (· != x)
  | .unpackT a _ x e => atVars a ++ (exprFv e).filter (· != x)
  | .region a _ p t e => atVars a ++ (exprFv e).filter (fun z => z != p && z != t)
  | .openPub a _ p c e => atVars a ++ (exprFv e).filter (fun z => z != p && z != c)
  | .case a x e₁ y e₂ => atVars a ++ (exprFv e₁).filter (· != x) ++ (exprFv e₂).filter (· != y)
  | .ifnull a e₁ x e₂ => atVars a ++ exprFv e₁ ++ (exprFv e₂).filter (· != x)
  | .parity a _ e₁ e₂ => atVars a ++ exprFv e₁ ++ exprFv e₂
  | .ifeq a b e₁ e₂ => atVars a ++ atVars b ++ exprFv e₁ ++ exprFv e₂
  | .cas _ _ w e v t ok fail => atVars w ++ atVars e ++ atVars v ++ (exprFv ok).filter (· != t) ++ exprFv fail
  | .casp _ _ w e0 e1 v0 v1 t ok fail =>
    atVars w ++ atVars e0 ++ atVars e1 ++ atVars v0 ++ atVars v1 ++ (exprFv ok).filter (· != t) ++ exprFv fail
  | .ret a => atVars a
  | .tail _ _ a _ => atVars a

/-- The environments of a source thread: the current frame's, then each
suspended frame's, innermost first. -/
def frameEnvs (th : TermRun.TTh) : List TermRun.Env := th.env :: th.stack.map (·.env)

/-- The remaining terms of a source thread's frames, in the order of
`frameEnvs`: the current term, then each suspended frame's continuation. A
frame's control point, the key of the immediate table (`Layout.imms`). -/
def frameTerms (th : TermRun.TTh) : List CoreTerm.Expr := th.term :: th.stack.map (·.body)

/-- The variables each frame of a source thread still reads, in the order of
`frameEnvs`: the current term's free variables, then each suspended frame's
continuation's, less the variable the callee's result is bound to. -/
def frameFv (th : TermRun.TTh) : List (List String) :=
  exprFv th.term :: th.stack.map fun f => (exprFv f.body).filter (· != f.x)

/-- A term followed down through `let`, `split` and both arms of `ifeq`:
the term itself and every term a thread running it reaches without a call
or a return (`TermRun.tstep` continues a `let` and a `split` with the body,
an `ifeq` with one arm). Any other constructor is a leaf, but a `ret` leaf is
left out: the models return only `()`, which reads no variable (`env_total`
asks nothing of it), and a `ret ()` is not the extern's own (any block may
return `()`). Used only on the two bodies of `externModelTerms`, built from
these constructors, `ret` and `tail`. -/
def modelTerms : CoreTerm.Expr → List CoreTerm.Expr
  | e@(.let_ _ _ b) => e :: modelTerms b
  | e@(.split _ _ _ b) => e :: modelTerms b
  | e@(.ifeq _ _ y n) => e :: (modelTerms y ++ modelTerms n)
  | .ret _ => []
  | e => [e]

/-- **The output extern's model terms**: exactly the terms of the two model
bodies, `Scc.Frontend.printBody` (`print{m}`) and `Scc.Frontend.printLBody`
(its loop `printL{i, d}`, which `Frontend.externOf` fixes textually,
`declIs`), less their `ret ()` leaves. A thread running the extern is at
one of these terms until it returns: a `tail` to `printL` enters
`printLBody`, the `emit` step continues with the `let`'s body, and neither
body calls. The list is closed: another extern's model is
not on it until it is added here. -/
def externModelTerms : List CoreTerm.Expr :=
  modelTerms Scc.Frontend.printBody ++ modelTerms Scc.Frontend.printLBody

/-- **Frame `d` of `th` runs the output extern's model**: it is the current
frame (`d = 0`; the model bodies make no call, so no suspended frame is one
of theirs) and its term is one of `externModelTerms`. scc does not compile
the model: the runtime's `scc_rt_print` stands for it, emitting a slice with
multi-byte `write`s, and the model's locals (byte and word counters, the
loaded word) have no target counterpart while such a `write` is under way.
`Components` therefore exempts these frames from `env_rep` and `env_total`
only; every other clause, `env_imm` included, holds for them as for any
frame. -/
def ExternFrame (th : TermRun.TTh) (d : Nat) : Prop :=
  d = 0 ∧ th.term ∈ externModelTerms

/-- Every number in the register environments of thread `i` (every frame)
fits in 64 bits. A `+` on plain `Int` whose result does not is the
`Int`-overflow abort. -/
def NoBigNumT (i : Nat) (s : TermRun.Cfg) : Prop :=
  ∀ th, s.ths[i]? = some th → ∀ e ∈ frameEnvs th, ∀ b ∈ e, ∀ w ∈ b.2.2, ∀ n, w.val = .num n → n < 2 ^ 64

/-- **One part of the budget**, the one abort kind `k` is about, as seen by
thread `i`: heap use within `B.cells`; thread `i`'s call depth within
`B.frames`; thread count within `B.threads`; thread `i`'s numbers within 64
bits. The `writeErr` kind has no budget part (`True`). -/
def Budget.Part (B : Budget) : AbortKind → Nat → TermRun.Cfg → Prop
  | .overflow, i, s => NoBigNumT i s
  | .heap, _, s => heapUse s ≤ B.cells
  | .stack, i, s => ∀ th, s.ths[i]? = some th → th.stack.length ≤ B.frames
  | .threads, _, s => s.ths.size ≤ B.threads
  | .writeErr, _, _ => True

/-- **The source configuration is within the budget**: every part, for
every thread. -/
def Budget.Within (B : Budget) (s : TermRun.Cfg) : Prop := ∀ k i, B.Part k i s

/-! ## The components of `R` -/

/-- Where a target word lives: a register, or the 8 bytes at an address of
the thread's private memory (a stack slot). -/
inductive Place (Reg : Type) where
  | reg (r : Reg)
  | slot (a : Nat)

/-- The value at a place of a thread state, if mapped. -/
def placeVal (M : ExtMachine) (st : M.I.State) : Place M.I.RegId → Option Nat
  | .reg r => some (M.regVal st r).toNat
  | .slot a => (M.privLoad st (BitVec.ofNat 64 a)).map (·.toNat)

/-- Where a locative's offset word lives: at a place, or nowhere, as a
constant the code has folded into the displacements of its accesses (an
immediate; `newBuf`'s `(base, 0)`, a constant `fld` or index). Only the
offset half of a locative may be an immediate: every other word a frame
still reads is at a place. -/
inductive OffPlace (Reg : Type) where
  | at (pl : Place Reg)
  | imm (n : Nat)

/-- The value of an offset word: at its place, or the immediate. -/
def offVal (M : ExtMachine) (st : M.I.State) : OffPlace M.I.RegId → Option Nat
  | .at pl => placeVal M st pl
  | .imm n => some n

/-- **Where a source word lives on the target**: one target word, or, for a
locative, two (`Scc/LAYOUT.md` §4): the object's base and the offset word.
The lowering keeps a locative as the pair `(base, offset)` everywhere, so a
source word `.loc a tag` is not one target word. A word may also be at no
place, a constant `n` the code has folded into its instructions (`imm`), at
the control points the layout's immediate table names (`Layout.imms`,
`Components.env_imm`). -/
inductive WordPlace (Reg : Type) where
  | one (pl : Place Reg)
  | loc (base : Place Reg) (off : OffPlace Reg)
  | imm (n : Nat)

/-- The target places of a word place (an immediate, or an immediate
offset, has none). -/
def WordPlace.places {Reg : Type} : WordPlace Reg → List (Place Reg)
  | .one pl => [pl]
  | .loc b (.at o) => [b, o]
  | .loc b (.imm _) => [b]
  | .imm _ => []

/-- **The locative representation**: target words `vb` (base) and `vo`
(offset word) represent source value `x`.

* `undef`: any pair.
* `loc a 0`: `vb` is the base of `a`'s label (its scalar word 0, `Witness.lbl`)
  and `vo` is the byte offset of `a`'s word, `8 · a.offset`: the scalar half
  of `Obj.offWord`, the trace half being 0 in the scalar-only scope of
  `wordAddr`.
* Every other value is not represented by a pair: a locative with a
  non-zero tag (a locative carries no tag bits), and `num`, `null`. -/
def LocRep (lbl : WeakMem.AllocLabel → Option Nat) : WeakMem.Val → Nat → Nat → Prop
  | .undef, _, _ => True
  | .loc a tag, vb, vo => tag = 0 ∧ lbl a.label = some vb ∧ vo = 8 * a.offset
  | .num _, _, _ => False
  | .null, _, _ => False

/-- **The word representation at a word place**: a single place holds a
word `ValRep` relates; a pair holds a base and offset word `LocRep` relates;
an immediate `n` is a word `ValRep` relates (for a number: the number is
`n`). -/
def WordPlaceRep (M : ExtMachine) (lbl : WeakMem.AllocLabel → Option Nat) (st : M.I.State) :
    WordPlace M.I.RegId → WeakMem.Val → Prop
  | .one pl, x => ∃ v, placeVal M st pl = some v ∧ ValRep lbl x v
  | .loc pb po, x => ∃ vb vo, placeVal M st pb = some vb ∧ offVal M st po = some vo ∧ LocRep lbl x vb vo
  | .imm n, x => ValRep lbl x n

/-- **The data `R` is witnessed by.** -/
structure Witness (M : ExtMachine) where
  /-- Source thread index ↦ target thread index. -/
  thr : Nat → Option Nat
  /-- Source label ↦ base address (the layout injection). The base is the
  address of the object's scalar word 0, the address `scc_rt_alloc`
  returns (`Scc/LAYOUT.md` §2); the header word at `base − 8` is outside the
  label's range (`labelRange`), so the allocator's header store is a
  runtime write. -/
  lbl : WeakMem.AllocLabel → Option Nat
  /-- Source label ↦ its size in words. -/
  lsize : WeakMem.AllocLabel → Nat
  /-- Source timestamp ↦ target timestamp (`0`: the target's initial write). -/
  ts : Nat → Option Nat
  /-- The register-environment map: source thread, frame depth (`0` is the
  current frame), variable, word index ↦ target word place (one place, or
  two for a locative). Partial: a dead variable need not be kept. -/
  env : Nat → Nat → String → Nat → Option (WordPlace M.I.RegId)
  /-- The stack map: the places of each target thread that hold pointers
  into its stack. -/
  marked : Nat → Place M.I.RegId → Prop
  /-- **The placement epoch of each label, in source time**: the current
  placement (`lbl`) represents the label's messages from this source
  timestamp on, and for each address the latest earlier message (the value
  a move copied, `Witness.InEpoch`). `0` unless `Λ.relocates`. -/
  since : WeakMem.AllocLabel → Nat
  /-- **The placement epoch of each label, in target time**: target writes
  inside the label's current range after this target timestamp are the
  label's (`mem_onto`); earlier ones belong to whatever occupied the range
  before (a dead object, a from-space copy). Unless `Λ.relocates`, the
  earlier ones are images or outstanding promises (`pre_alloc`). -/
  tsFrom : WeakMem.AllocLabel → Nat

/-- The address range of a placed label. -/
def labelRange {M : ExtMachine} (w : Witness M) (l : WeakMem.AllocLabel) (b : Nat) : Range :=
  ⟨b, 8 * w.lsize l⟩

/-- **Reachability from a set of root labels** `R` through the references
stored in any message to a reachable label (cells and boxes alike; every
message, not only the latest, since a thread may read an older one). -/
inductive Reach (s : TermRun.Cfg) (R : WeakMem.AllocLabel → Prop) : WeakMem.AllocLabel → Prop
  /-- A root. -/
  | root {l : WeakMem.AllocLabel} : R l → Reach s R l
  /-- A reference stored in a message to a reachable label. -/
  | cell {m : WeakMem.Msg} {a : WeakMem.Address} {g : Nat} :
      Reach s R m.loc.label → m ∈ s.mem.toList → m.val = .loc a g → Reach s R a.label

/-- **The root labels**: the labels referenced by a word of a variable some
frame of some thread still reads (`frameFv`, the roots of `env_total`; they
are also the values in flight, a source thread holding no word outside its
frames). A thread's control block has no source label (a `ThreadId` is not
yet a reference), so it is no root. -/
def RootLabel (s : TermRun.Cfg) (l : WeakMem.AllocLabel) : Prop :=
  ∃ (i : Nat) (th : TermRun.TTh) (d : Nat) (e : TermRun.Env) (xs : List String) (x : String) (ty : CoreLang.Ty)
    (ws : List TermRun.Word) (wd : TermRun.Word) (a : WeakMem.Address) (g : Nat), s.ths[i]? = some th ∧ (frameEnvs th)[d]? = some e ∧
    (frameFv th)[d]? = some xs ∧ x ∈ xs ∧ TermRun.lookupE e x = some (ty, ws) ∧ wd ∈ ws ∧
    wd.val = .loc a g ∧ a.label = l

/-- **The live labels of a source configuration** (`Live s l`): reachable
from the root labels. The memory clauses of `Components` cover the live
labels only: a dead label's cells are runtime-owned. -/
def Live (s : TermRun.Cfg) : WeakMem.AllocLabel → Prop := Reach s (RootLabel s)

/-- A label with no message in memory (not yet allocated, or allocated with
no words). -/
def Fresh (s : TermRun.Cfg) (l : WeakMem.AllocLabel) : Prop := ∀ m ∈ s.mem.toList, m.loc.label ≠ l

/-- With no thread there is no root, so no label is live. -/
theorem live_no_threads {s : TermRun.Cfg} (h : s.ths = #[]) {l : WeakMem.AllocLabel} : ¬ Live s l := by
  intro hl
  induction hl with
  | root hr =>
    obtain ⟨i, th, -, -, -, -, -, -, -, -, -, hth, -⟩ := hr
    simp [h] at hth
  | cell _ _ _ ih => exact ih

/-- **Reachability after a step**: if every message of `c'` is a message of
`c` or stores only references reachable in `c` (from `R`) or fresh, and so
is every root of `c'`, then every label reachable in `c'` was reachable in
`c` or is fresh. -/
theorem Reach.step {c c' : TermRun.Cfg} {R R' : WeakMem.AllocLabel → Prop}
    (hmem : ∀ m ∈ c'.mem.toList, m ∈ c.mem.toList ∨
      ∀ a g, m.val = .loc a g → Reach c R a.label ∨ Fresh c a.label)
    (hroot : ∀ l, R' l → Reach c R l ∨ Fresh c l) {l : WeakMem.AllocLabel} (h : Reach c' R' l) :
    Reach c R l ∨ Fresh c l := by
  induction h with
  | root hr => exact hroot _ hr
  | @cell m a g _ hm hv ih =>
    rcases hmem m hm with hold | hnew
    · rcases ih with r | f
      · exact .inl (.cell r hold hv)
      · exact absurd rfl (f m hold)
    · exact hnew a g hv

/-- **Dead stays dead**, in the form a step proof uses: under the hypotheses
of `Reach.step` (from the root labels), a label that is dead in `c` and not
fresh is dead in `c'`. The hypotheses are the per-step content: no step
forges a reference to a dead label, and new labels are fresh. -/
theorem dead_stays_dead {c c' : TermRun.Cfg}
    (hmem : ∀ m ∈ c'.mem.toList, m ∈ c.mem.toList ∨ ∀ a g, m.val = .loc a g → Live c a.label ∨ Fresh c a.label)
    (hroot : ∀ l, RootLabel c' l → Live c l ∨ Fresh c l) {l : WeakMem.AllocLabel}
    (hd : ¬ Live c l) (hf : ¬ Fresh c l) : ¬ Live c' l := fun h =>
  (Reach.step hmem hroot h).elim hd hf

/-- A source message is in the current placement epoch of its label (`w.since`):
at or after the epoch's start, or the latest message to its address before it
(the value the move copied). With `since = 0` every message is. -/
def Witness.InEpoch {M : ExtMachine} (w : Witness M) (s : TermRun.Cfg) (k : Nat) (m : WeakMem.Msg) : Prop :=
  w.since m.loc.label ≤ k ∨
    ∀ k2 m2, k < k2 → k2 < w.since m.loc.label → s.mem[k2]? = some m2 → m2.loc ≠ m.loc

/-- **A colour-only write** (a heal): target message `k'` rewrites the latest
earlier message to its location, changing some bits, all of them colour bits
(`Λ.colourMask`). With mask `0` no write is colour-only (`not_colourOnly_zero`). -/
def ColourOnly (Λ : Layout) (mem : Kraken.Promising.Memory) (k' : Nat) (m' : Kraken.Promising.Msg) : Prop :=
  ∃ k0 m0, k0 < k' ∧ mem.get? k0 = some m0 ∧ m0.loc = m'.loc ∧
    (∀ k2 m2, k0 < k2 → k2 < k' → mem.get? k2 = some m2 → m2.loc ≠ m'.loc) ∧
    m0.val.toNat ≠ m'.val.toNat ∧ (m0.val.toNat ^^^ m'.val.toNat) &&& Λ.colourMask = m0.val.toNat ^^^ m'.val.toNat

/-- With no colour bits, no write is colour-only. -/
theorem not_colourOnly_zero {Λ : Layout} (h : Λ.colourMask = 0) {mem : Kraken.Promising.Memory} {k' : Nat}
    {m' : Kraken.Promising.Msg} : ¬ ColourOnly Λ mem k' m' := by
  rintro ⟨k0, m0, -, -, -, -, hne, hx⟩
  rw [h, Nat.and_zero] at hx
  exact hne (Nat.eq_of_testBit_eq fun i => by
    have := congrArg (Nat.testBit · i) hx
    simp only [Nat.zero_testBit, Nat.testBit_xor] at this
    revert this; cases m0.val.toNat.testBit i <;> cases m'.val.toNat.testBit i <;> simp)

/-- **The components of `R`** at a target configuration `t` and a source
configuration `s`, witnessed by `w`. -/
structure Components (M : ExtMachine) (Λ : Layout) (w : Witness M) (t : M.Cfg) (s : TermRun.Cfg) :
    Prop where
  /-- Thread map: every source thread has a target thread ... -/
  thr_total : ∀ i, i < s.ths.size → ∃ j, w.thr i = some j ∧ j < t.1.threads.size
  /-- ... no two the same ... -/
  thr_inj : ∀ i i' j, w.thr i = some j → w.thr i' = some j → i = i'
  /-- ... and every running target thread is one of them (no runtime-only
  threads). -/
  thr_onto : ∀ j tt, M.runs t j → t.1.threads[j]? = some tt → ∃ i, i < s.ths.size ∧ w.thr i = some j
  /-- Layout injection: static labels are where `Λ` puts them ... -/
  lbl_static : ∀ l b, Λ.static l = some b → w.lbl l = some b
  /-- ... every placed label is a word-aligned range inside the heap or the
  static image ... -/
  lbl_range : ∀ l b, w.lbl l = some b → b % 8 = 0 ∧
    ((labelRange w l b).Sub Λ.heap ∨ (labelRange w l b).Sub Λ.data)
  /-- ... distinct live labels do not overlap (a dead label's range may be
  reused) ... -/
  lbl_disj : ∀ l l' b b', l ≠ l' → Live s l → Live s l' → w.lbl l = some b → w.lbl l' = some b' →
    (labelRange w l b).Disjoint (labelRange w l' b')
  /-- ... and every cell of a live label is placed, within its label. -/
  lbl_mem : ∀ m ∈ s.mem.toList, Live s m.loc.label →
    ∃ b, w.lbl m.loc.label = some b ∧ m.loc.offset < w.lsize m.loc.label
  /-- Placement epochs start at allocation unless the runtime relocates
  objects (in source time; for the target-time bound `w.tsFrom` without
  relocation see `pre_alloc`). -/
  epoch_fixed : Λ.relocates = false → ∀ l, w.since l = 0
  /-- Value representation on memory: each source message to a live label,
  in its placement epoch (`Witness.InEpoch`), is a target message (or the
  target's initial write) covering the mapped word (`wordAt`: an 8-byte
  message there, or half of a 16-byte one), with a representing value ... -/
  mem_rep : ∀ k m, s.mem[k]? = some m → Live s m.loc.label → w.InEpoch s k m →
    ∃ k' a v, w.ts k = some k' ∧ wordAddr w.lbl m.loc = some a ∧
      wordAt t.1.mem a k' = some v ∧ ValRep w.lbl m.val v
  /-- ... only the first message to a source address of a live label may be
  the target's initial write (timestamp 0: a fresh cell's `undef` or zero
  message, the zeroed arena), and only in the label's first epoch; a later
  message must be a target message (after a move, the first image at the new
  address is the copy's write) ... -/
  ts_first : ∀ k m, s.mem[k]? = some m → Live s m.loc.label → w.ts k = some 0 →
    w.since m.loc.label = 0 ∧ ∀ k2 m2, k2 < k → s.mem[k2]? = some m2 → m2.loc ≠ m.loc
  /-- ... in the same order **per location**: two messages to one address of
  a live label, from its epoch's start on (a move's copies are not ordered),
  map to target messages in their source order. Messages to distinct
  addresses are not ordered by the map: a promise the target made before an
  allocation and fulfils after it keeps its early timestamp, while the source
  message it represents is appended after the allocation (`Scc/DESIGN.md`
  §9.0, "Fresh allocation"). Order across locations is the view relation's
  business, not the memory map's ... -/
  ts_mono : ∀ k1 k2 k1' k2' m1 m2, s.mem[k1]? = some m1 → s.mem[k2]? = some m2 → m1.loc = m2.loc →
    Live s m1.loc.label → w.since m1.loc.label ≤ k1 →
    w.ts k1 = some k1' → w.ts k2 = some k2' → 0 < k1' → 0 < k2' → k1 < k2 → k1' < k2'
  /-- ... every target write inside a live label's current range, in
  its epoch (`w.tsFrom`), is the image of a source message or a colour-only
  write (`ColourOnly`, none without colour bits): the target writes nothing
  to the live image the source did not. Writes elsewhere (headers, the
  collector's metadata, from-space copies, dead objects, free slots) are
  runtime-owned and need no source step ... -/
  mem_onto : ∀ k' m', t.1.mem.get? k' = some m' →
    (∃ l b, Live s l ∧ w.lbl l = some b ∧ w.tsFrom l < k' ∧ (labelRange w l b).contains m'.loc.addr.toNat) →
    (∃ k, k < s.mem.size ∧ w.ts k = some k') ∨ ColourOnly Λ t.1.mem k' m'
  /-- ... and, unless the runtime relocates objects, a target write inside a
  live label's range at or before `w.tsFrom` is also the image of a source
  message, or else a promise its writing thread still has outstanding (in
  that thread's `prom`). The witness is chosen afresh at each related pair,
  so with `w.tsFrom l` at the target's last timestamp this exempts every
  outstanding promise, wherever it points: the source need not mirror a
  promise until the fulfilling store, which then appends the image (a
  promise to an address the allocator returns later has no label to be
  mirrored in before that). A fulfilled write is no longer exempt, and a
  write that never was a promise is not exempt at all. -/
  pre_alloc : Λ.relocates = false → ∀ k' m', t.1.mem.get? k' = some m' →
    (∃ l b, Live s l ∧ w.lbl l = some b ∧ k' ≤ w.tsFrom l ∧ (labelRange w l b).contains m'.loc.addr.toNat) →
    (∃ k, k < s.mem.size ∧ w.ts k = some k') ∨
      ∃ tt, t.1.threads[m'.tid]? = some tt ∧ k' ∈ tt.prom
  /-- Value representation on register environments: each placed word of
  each frame of each source thread is represented at its place in the
  related target thread, except in a frame running the output extern's
  uncompiled model (`ExternFrame`) ... -/
  env_rep : ∀ i th j tt, s.ths[i]? = some th → w.thr i = some j → t.1.threads[j]? = some tt →
    ∀ d e, (frameEnvs th)[d]? = some e → ∀ x ty ws, TermRun.lookupE e x = some (ty, ws) →
    ∀ k wd wp, ws[k]? = some wd → w.env i d x k = some wp → ¬ ExternFrame th d →
    WordPlaceRep M w.lbl tt.st wp wd.val
  /-- ... and every word of every variable a frame still reads (`frameFv`)
  is placed: `env` may drop only dead variables. A frame running the output
  extern's model (`ExternFrame`) is exempt from both: `scc_rt_print` stands
  for it, and during a multi-byte `write` the model's locals have no target
  counterpart. -/
  env_total : ∀ i th, s.ths[i]? = some th → ∀ d e xs, (frameEnvs th)[d]? = some e → (frameFv th)[d]? = some xs →
    ¬ ExternFrame th d → ∀ x ∈ xs, ∀ ty ws, TermRun.lookupE e x = some (ty, ws) →
    ∀ k < ws.length, ∃ pl, w.env i d x k = some pl
  /-- Stack map: each thread's current stack range is in the pool ... -/
  stack_pool : ∀ j rg, M.stackRange t j = some rg → rg.Sub Λ.stackPool
  /-- ... ranges of distinct threads are disjoint ... -/
  stack_disj : ∀ j j' rg rg', j ≠ j' → M.stackRange t j = some rg → M.stackRange t j' = some rg' →
    rg.Disjoint rg'
  /-- ... the range is mapped in its thread's private memory and in no other
  thread's (stack memory is never shared) ... -/
  stack_owned : ∀ j rg, M.stackRange t j = some rg → ∀ j' tt', t.1.threads[j']? = some tt' →
    ∀ a, a % 8 = 0 → rg.contains a → rg.contains (a + 7) →
    ((M.privLoad tt'.st (BitVec.ofNat 64 a)).isSome ↔ j' = j)
  /-- ... no shared write is to an address in a stack range ... -/
  stack_private : ∀ j rg, M.stackRange t j = some rg → ∀ m ∈ t.1.mem.msgs.toList,
    ¬ rg.contains m.loc.addr.toNat
  /-- ... every marked place points into its thread's current range ... -/
  stack_marked : ∀ j pl, w.marked j pl → ∃ tt rg v, t.1.threads[j]? = some tt ∧
    M.stackRange t j = some rg ∧ placeVal M tt.st pl = some v ∧ rg.contains v
  /-- ... and no place holding a source word is marked: words that represent
  source values are never stack pointers, so the marked places are the only
  words a stack copy must rewrite. -/
  stack_unmarked : ∀ i d x k wp pl j, w.env i d x k = some wp → pl ∈ wp.places → w.thr i = some j →
    ¬ w.marked j pl
  /-- **Immediates only as the layout's table says**: a word placed at an
  immediate `n` is one the immediate table gives `n` for, at its frame's
  control point (`frameTerms`). With the empty table no word is at an
  immediate. -/
  env_imm : ∀ i th d e x k n, s.ths[i]? = some th → (frameTerms th)[d]? = some e →
    w.env i d x k = some (.imm n) → Λ.imms e x k = some n

/-- **The unscoped components**: `Components` as it was before the memory
clauses were scoped to live labels and placement epochs, every clause over
every label. A relation proved in this form gives `Components` for a witness
with no epochs (`ComponentsAll.scoped`): the form for a target with no
collector, and how proofs of the earlier statement carry over. -/
structure ComponentsAll (M : ExtMachine) (Λ : Layout) (w : Witness M) (t : M.Cfg) (s : TermRun.Cfg) :
    Prop where
  /-- Thread map: every source thread has a target thread ... -/
  thr_total : ∀ i, i < s.ths.size → ∃ j, w.thr i = some j ∧ j < t.1.threads.size
  /-- ... no two the same ... -/
  thr_inj : ∀ i i' j, w.thr i = some j → w.thr i' = some j → i = i'
  /-- ... and every running target thread is one of them (no runtime-only
  threads). -/
  thr_onto : ∀ j tt, M.runs t j → t.1.threads[j]? = some tt → ∃ i, i < s.ths.size ∧ w.thr i = some j
  /-- Layout injection: static labels are where `Λ` puts them ... -/
  lbl_static : ∀ l b, Λ.static l = some b → w.lbl l = some b
  /-- ... every placed label is a word-aligned range inside the heap or the
  static image ... -/
  lbl_range : ∀ l b, w.lbl l = some b → b % 8 = 0 ∧
    ((labelRange w l b).Sub Λ.heap ∨ (labelRange w l b).Sub Λ.data)
  /-- ... distinct labels do not overlap ... -/
  lbl_disj : ∀ l l' b b', l ≠ l' → w.lbl l = some b → w.lbl l' = some b' →
    (labelRange w l b).Disjoint (labelRange w l' b')
  /-- ... and every cell in source memory is placed, within its label. -/
  lbl_mem : ∀ m ∈ s.mem.toList, ∃ b, w.lbl m.loc.label = some b ∧ m.loc.offset < w.lsize m.loc.label
  /-- Value representation on memory: each source message is a target
  message (or the target's initial write) covering the mapped word
  (`wordAt`: an 8-byte message there, or half of a 16-byte one), with a
  representing value ... -/
  mem_rep : ∀ k m, s.mem[k]? = some m → ∃ k' a v, w.ts k = some k' ∧ wordAddr w.lbl m.loc = some a ∧
    wordAt t.1.mem a k' = some v ∧ ValRep w.lbl m.val v
  /-- ... only the first message to a source address may be the target's
  initial write (timestamp 0: a fresh cell's `undef` or zero message, the
  zeroed arena); a later message must be a target message ... -/
  ts_first : ∀ k m, s.mem[k]? = some m → w.ts k = some 0 → ∀ k2 m2, k2 < k → s.mem[k2]? = some m2 →
    m2.loc ≠ m.loc
  /-- ... in the same order, except that the two halves of a source pair
  write (`k1 ∈ s.pairs`, messages `k1` and `k1 + 1`, at distinct source
  addresses) may share one 16-byte target message ... -/
  ts_mono : ∀ k1 k2 k1' k2', w.ts k1 = some k1' → w.ts k2 = some k2' → 0 < k1' → 0 < k2' → k1 < k2 →
    k1' < k2' ∨ (k1' = k2' ∧ k2 = k1 + 1 ∧ k1 ∈ s.pairs ∧
      ∀ m1 m2, s.mem[k1]? = some m1 → s.mem[k2]? = some m2 → m1.loc ≠ m2.loc)
  /-- ... and every target write inside a placed label is the image of a
  source message (the target writes nothing the source did not). -/
  mem_onto : ∀ k' m', t.1.mem.get? k' = some m' →
    (∃ l b, w.lbl l = some b ∧ (labelRange w l b).contains m'.loc.addr.toNat) →
    ∃ k, k < s.mem.size ∧ w.ts k = some k'
  /-- Value representation on register environments: each placed word of
  each frame of each source thread is represented at its place in the
  related target thread, except in a frame running the output extern's
  uncompiled model (`ExternFrame`) ... -/
  env_rep : ∀ i th j tt, s.ths[i]? = some th → w.thr i = some j → t.1.threads[j]? = some tt →
    ∀ d e, (frameEnvs th)[d]? = some e → ∀ x ty ws, TermRun.lookupE e x = some (ty, ws) →
    ∀ k wd wp, ws[k]? = some wd → w.env i d x k = some wp → ¬ ExternFrame th d →
    WordPlaceRep M w.lbl tt.st wp wd.val
  /-- ... and every word of every variable a frame still reads (`frameFv`)
  is placed: `env` may drop only dead variables. A frame running the output
  extern's model (`ExternFrame`) is exempt from both: `scc_rt_print` stands
  for it, and during a multi-byte `write` the model's locals have no target
  counterpart. -/
  env_total : ∀ i th, s.ths[i]? = some th → ∀ d e xs, (frameEnvs th)[d]? = some e → (frameFv th)[d]? = some xs →
    ¬ ExternFrame th d → ∀ x ∈ xs, ∀ ty ws, TermRun.lookupE e x = some (ty, ws) →
    ∀ k < ws.length, ∃ pl, w.env i d x k = some pl
  /-- Stack map: each thread's current stack range is in the pool ... -/
  stack_pool : ∀ j rg, M.stackRange t j = some rg → rg.Sub Λ.stackPool
  /-- ... ranges of distinct threads are disjoint ... -/
  stack_disj : ∀ j j' rg rg', j ≠ j' → M.stackRange t j = some rg → M.stackRange t j' = some rg' →
    rg.Disjoint rg'
  /-- ... the range is mapped in its thread's private memory and in no other
  thread's (stack memory is never shared) ... -/
  stack_owned : ∀ j rg, M.stackRange t j = some rg → ∀ j' tt', t.1.threads[j']? = some tt' →
    ∀ a, a % 8 = 0 → rg.contains a → rg.contains (a + 7) →
    ((M.privLoad tt'.st (BitVec.ofNat 64 a)).isSome ↔ j' = j)
  /-- ... no shared write is to an address in a stack range ... -/
  stack_private : ∀ j rg, M.stackRange t j = some rg → ∀ m ∈ t.1.mem.msgs.toList,
    ¬ rg.contains m.loc.addr.toNat
  /-- ... every marked place points into its thread's current range ... -/
  stack_marked : ∀ j pl, w.marked j pl → ∃ tt rg v, t.1.threads[j]? = some tt ∧
    M.stackRange t j = some rg ∧ placeVal M tt.st pl = some v ∧ rg.contains v
  /-- ... and no place holding a source word is marked: words that represent
  source values are never stack pointers, so the marked places are the only
  words a stack copy must rewrite. -/
  stack_unmarked : ∀ i d x k wp pl j, w.env i d x k = some wp → pl ∈ wp.places → w.thr i = some j →
    ¬ w.marked j pl
  /-- **Immediates only as the layout's table says**: a word placed at an
  immediate `n` is one the immediate table gives `n` for, at its frame's
  control point (`frameTerms`). With the empty table no word is at an
  immediate. -/
  env_imm : ∀ i th d e x k n, s.ths[i]? = some th → (frameTerms th)[d]? = some e →
    w.env i d x k = some (.imm n) → Λ.imms e x k = some n

/-- **Unscoped components give the scoped ones** for a witness whose epochs
all start at 0 (as `epoch_fixed` asks when `Λ.relocates` is false): every live
label is a label, every message is in its epoch, and the six memory clauses
only gain hypotheses. -/
theorem ComponentsAll.scoped {M : ExtMachine} {Λ : Layout} {w : Witness M} {t : M.Cfg} {s : TermRun.Cfg}
    (h : ComponentsAll M Λ w t s) (hs : ∀ l, w.since l = 0) (_ht : ∀ l, w.tsFrom l = 0) :
    Components M Λ w t s where
  thr_total := h.thr_total
  thr_inj := h.thr_inj
  thr_onto := h.thr_onto
  lbl_static := h.lbl_static
  lbl_range := h.lbl_range
  env_rep := h.env_rep
  env_total := h.env_total
  stack_pool := h.stack_pool
  stack_disj := h.stack_disj
  stack_owned := h.stack_owned
  stack_private := h.stack_private
  stack_marked := h.stack_marked
  stack_unmarked := h.stack_unmarked
  env_imm := h.env_imm
  lbl_disj l l' b b' hne _ _ := h.lbl_disj l l' b b' hne
  lbl_mem m hm _ := h.lbl_mem m hm
  epoch_fixed _ l := hs l
  mem_rep k m hm _ _ := h.mem_rep k m hm
  ts_first k m hm _ h0 := ⟨hs _, h.ts_first k m hm h0⟩
  ts_mono k1 k2 k1' k2' m1 m2 hm1 hm2 hloc _ _ h1 h2 p1 p2 hlt :=
    (h.ts_mono k1 k2 k1' k2' h1 h2 p1 p2 hlt).resolve_right fun ⟨_, _, _, hne⟩ => hne m1 m2 hm1 hm2 hloc
  mem_onto k' m' hm := fun ⟨l, b, _, hb, _, hc⟩ => .inl (h.mem_onto k' m' hm ⟨l, b, hb, hc⟩)
  pre_alloc _ k' m' hm := fun ⟨l, b, _, hb, _, hc⟩ => .inl (h.mem_onto k' m' hm ⟨l, b, hb, hc⟩)

/-- With `ts_first`, the timestamp map is strictly monotone on the messages
to one source address, the initial write (0) included: a later message to
the same address never maps to an earlier or equal target timestamp. -/
theorem Components.ts_mono_loc {M : ExtMachine} {Λ : Layout} {w : Witness M} {t : M.Cfg}
    {s : TermRun.Cfg} (h : Components M Λ w t s) {k1 k2 k1' k2' : Nat} {m1 m2 : WeakMem.Msg}
    (hm1 : s.mem[k1]? = some m1) (hm2 : s.mem[k2]? = some m2) (hloc : m1.loc = m2.loc)
    (hl : Live s m1.loc.label) (he : w.since m1.loc.label ≤ k1)
    (h1 : w.ts k1 = some k1') (h2 : w.ts k2 = some k2') (hlt : k1 < k2) : k1' < k2' := by
  rcases Nat.eq_zero_or_pos k2' with rfl | p2
  · exact absurd hloc ((h.ts_first k2 m2 hm2 (hloc ▸ hl) h2).2 k1 m1 hlt hm1)
  rcases Nat.eq_zero_or_pos k1' with rfl | p1
  · exact p2
  · exact h.ts_mono k1 k2 k1' k2' m1 m2 hm1 hm2 hloc hl he h1 h2 p1 p2 hlt

/-! ## Route S -/

/-- The latest message to a source address. -/
def lastMsg (mem : WeakMem.Memory) (a : WeakMem.Address) : Option WeakMem.Msg :=
  mem.toList.reverse.find? (·.loc = a)

/-- The static image of `Λ` is the memory of source configuration `s`: each
image word is the latest value of a static cell, and each static cell is in
the image. -/
def ImageMatches (Λ : Layout) (s : TermRun.Cfg) : Prop :=
  (∀ a v, (a, v) ∈ Λ.image → ∃ l off b m, Λ.static l = some b ∧ a = b + 8 * off ∧
    lastMsg s.mem ⟨l, off⟩ = some m ∧ ValRep Λ.static m.val v) ∧
  (∀ m ∈ s.mem.toList, ∀ b, Λ.static m.loc.label = some b →
    ∃ v, (b + 8 * m.loc.offset, v) ∈ Λ.image)

/-- **The Route S obligation**: the static image is the memory of some start
configuration of the source (some complete run of the setup block). It is
checked, not trusted: the certificate evaluates the setup block. -/
def RouteS (Λ : Layout) (S : SrcSem) : Prop := ∃ s, S.init s ∧ ImageMatches Λ (S.core s)

/-! ## The statement -/

/-- A target: the extended machine, the assembly type, the loader (the
trusted model of assembler, linker and loader realising `Λ`), and label
resolution: the code address, in the loaded program's layout, of a label of
the text. -/
structure Target where
  M : ExtMachine
  Asm : Type
  load : Asm → Layout → Option M.Cfg
  resolve : Asm → Layout → String → Option Nat

/-- **The code marks of `asm` loaded under `Λ`**, from the target's label
resolution: each range-transfer site at its fixed label (`XferKind.label`,
the only places a thread moves a stack-pool range into or out of its
private memory), and each abort site at its label. -/
def Target.marks (T : Target) (asm : T.Asm) (Λ : Layout) : Marks where
  site k := T.resolve asm Λ k.label
  abortAt k := T.resolve asm Λ (Λ.abortLbl k)

/-- Every shared location of the target configuration is in a shared region
of `Λ` (no access outside `Λ`): every message (write) is in `shared`, and
every initial word is in `shared` or in the read-only image `rodata`, where
the loaders lay the text's `.rodata` out (`rodataWords`). Being read-only,
`rodata` is never written: a message there is outside `Λ`. -/
def InLayout (Λ : Layout) {M : ExtMachine} (t : M.Cfg) : Prop :=
  (∀ m ∈ t.1.mem.msgs.toList, Λ.shared m.loc.addr.toNat) ∧
    (∀ p ∈ t.1.mem.init, Λ.shared p.1.addr.toNat ∨ Λ.rodata.contains p.1.addr.toNat)

/-- **An abort of kind `k` is justified** at the reachable source
configuration `s`, for source thread `i`, after the target trace `tr`:

* `overflow`, `heap`, `threads`: some step of thread `i` from `s`
  **crosses** the budget part of kind `k` (`Budget.Part`): the part holds at
  `s` and fails after the step. So a part already exceeded at `s` (say a
  big number in a dead variable of another thread) justifies nothing
  (`AbortJustified.part_before`); the overflow part looks only at thread
  `i`'s own frames.
* `stack`: some step of thread `i` from `s` leaves its depth above
  `B.frames`. Unlike the other kinds the abort need not happen at the
  crossing: the runtime has no depth counter, and aborts when a frame does
  not fit under the stack cap, which the layout places at or beyond
  `B.frames` frames (`AbortJustified.stack_part_after`).
* `threads` also: the kernel refused an earlier `clone`
  (`Ev.cloneErr ∈ tr`; the runtime aborts with `threads` when `clone`
  fails).
* `writeErr`: the kernel refused an earlier `write` (`Ev.writeErr ∈ tr`). -/
def AbortJustified (B : Budget) (S : SrcSem) (tr : List Ev) (s : S.Cfg) (i : Nat) : AbortKind → Prop
  | .writeErr => Ev.writeErr ∈ tr
  | .threads => Ev.cloneErr ∈ tr ∨
      ∃ es s', S.step i s es s' ∧ B.Part .threads i (S.core s) ∧ ¬ B.Part .threads i (S.core s')
  -- The stack abort is the grow routine's, at the byte cap; it may come
  -- later than the crossing of `B.frames`, so only the far side is required.
  | .stack => ∃ es s', S.step i s es s' ∧ ¬ B.Part .stack i (S.core s')
  | k => ∃ es s', S.step i s es s' ∧ B.Part k i (S.core s) ∧ ¬ B.Part k i (S.core s')

/-- An abort justified by the environment: a refused `write` for
`writeErr`, a refused `clone` for `threads`. -/
def EnvJustified (tr : List Ev) : AbortKind → Prop
  | .writeErr => Ev.writeErr ∈ tr
  | .threads => Ev.cloneErr ∈ tr
  | _ => False

/-- A budget abort other than `stack` not justified by the environment is
justified only by a step that crosses the part: the part holds before the
step and fails after it. -/
theorem AbortJustified.crossing {B : Budget} {S : SrcSem} {tr : List Ev} {s : S.Cfg} {i : Nat}
    {k : AbortKind} (hs : k ≠ .stack) (hk : ¬ EnvJustified tr k) (h : AbortJustified B S tr s i k) :
    ∃ es s', S.step i s es s' ∧ B.Part k i (S.core s) ∧ ¬ B.Part k i (S.core s') := by
  cases k with
  | writeErr => exact absurd h hk
  | threads => exact h.resolve_left hk
  | stack => exact absurd rfl hs
  | _ => exact h

/-- **A justified `stack` abort**: some step of thread `i` from `s` leaves
the stack part (its depth above `B.frames`), whether or not it held at
`s`. -/
theorem AbortJustified.stack_part_after {B : Budget} {S : SrcSem} {tr : List Ev} {s : S.Cfg} {i : Nat}
    (h : AbortJustified B S tr s i .stack) : ∃ es s', S.step i s es s' ∧ ¬ B.Part .stack i (S.core s') :=
  h

/-- **Justification is not inherited**: if the budget part of kind `k`
(not `stack`) already fails at `s`, no abort of kind `k` is justified at `s`
by the source. -/
theorem AbortJustified.part_before {B : Budget} {S : SrcSem} {tr : List Ev} {s : S.Cfg} {i : Nat}
    {k : AbortKind} (hs : k ≠ .stack) (hk : ¬ EnvJustified tr k) (h : AbortJustified B S tr s i k) :
    B.Part k i (S.core s) :=
  (h.crossing hs hk).choose_spec.choose_spec.2.1

/-- In particular, an abort of a budget kind other than `stack` is never
justified at a source configuration that is already outside the budget part
for that thread, unless the environment justifies it. -/
theorem AbortJustified.not_of_not_part {B : Budget} {S : SrcSem} {tr : List Ev} {s : S.Cfg} {i : Nat}
    {k : AbortKind} (hs : k ≠ .stack) (hk : ¬ EnvJustified tr k) (hp : ¬ B.Part k i (S.core s)) :
    ¬ AbortJustified B S tr s i k :=
  fun h => hp (h.part_before hs hk)

/-- **A refused `clone` justifies a `threads` abort**, whatever the source
does. -/
theorem AbortJustified.of_cloneErr {B : Budget} {S : SrcSem} {tr : List Ev} {s : S.Cfg} {i : Nat}
    (h : Ev.cloneErr ∈ tr) : AbortJustified B S tr s i .threads :=
  .inl h

/-- **A simulation witnessing correctness.** See the module docstring. -/
structure Sim (T : Target) (S : SrcSem) (Λ : Layout) (B : Budget) (asm : T.Asm) where
  /-- The relation. -/
  R : T.M.Cfg → S.Cfg → Prop
  /-- The layout is well formed. -/
  layout : Λ.WF
  /-- 1. Start (unconditional: the heap-bytes fallback, empty image). -/
  start : ∃ t0 s0, T.load asm Λ = some t0 ∧ S.init s0 ∧ R t0 s0
  /-- 2. Progress (fault freedom), and no access outside `Λ`. -/
  progress : ∀ t0 tr t, T.load asm Λ = some t0 → T.M.Run (T.marks asm Λ) t0 tr t → T.M.Progress (T.marks asm Λ) t ∧ InLayout Λ t
  /-- 3. Simulation with trace prefixes. -/
  sim : ∀ t0 tr t, T.load asm Λ = some t0 → T.M.Run (T.marks asm Λ) t0 tr t →
    ∃ tr' s, S.Reach tr' s ∧ R t s ∧ obs tr <+: tr'
  /-- 4. An abort of target thread `tid` is justified at a related source
  configuration whose trace is exactly the target's observable trace so far,
  for the source thread mapped to `tid`. -/
  abort : ∀ t0 tr t tid es t' k, T.load asm Λ = some t0 → T.M.Run (T.marks asm Λ) t0 tr t →
    T.M.Step (T.marks asm Λ) tid t es t' →
    Ev.abort k ∈ es → ∃ s w i, S.Reach (obs tr) s ∧ R t s ∧ Components T.M Λ w t (S.core s) ∧
      w.thr i = some tid ∧ AbortJustified B S tr s i k
  /-- 5. `R` is explicit. -/
  explicit : ∀ t s, R t s → ∃ w : Witness T.M, Components T.M Λ w t (S.core s)

/-- **`scc` correctness**: some simulation exists. -/
def Correct (T : Target) (S : SrcSem) (Λ : Layout) (B : Budget) (asm : T.Asm) : Prop :=
  Nonempty (Sim T S Λ B asm)

/-! ## Using the statement -/

namespace Sim

variable {T : Target} {S : SrcSem} {Λ : Layout} {B : Budget} {asm : T.Asm}

/-- **Invariant transfer**: an invariant of every reachable source
configuration holds of a source configuration `R`-related to each reachable
target configuration, together with the components of `R`. -/
theorem transfer (h : Sim T S Λ B asm) {Inv : S.Cfg → Prop} (hInv : ∀ tr s, S.Reach tr s → Inv s)
    {t0 t : T.M.Cfg} {tr : List Ev} (h0 : T.load asm Λ = some t0) (hr : T.M.Run (T.marks asm Λ) t0 tr t) :
    ∃ s, h.R t s ∧ Inv s ∧ ∃ w : Witness T.M, Components T.M Λ w t (S.core s) := by
  obtain ⟨tr', s, hs, hR, -⟩ := h.sim t0 tr t h0 hr
  exact ⟨s, hR, hInv tr' s hs, h.explicit t s hR⟩

/-- **Transfer of a WeakCore safety result**, for any extra source step `Sp`
(spawns, extern steps; `Sp i` taken by thread `i`): a property of every
configuration reachable along WeakCore's `StepsG` runs with extra step
`∃ i, Sp i` holds of a source configuration related
to each reachable target configuration. -/
theorem transfer_stepsG {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch}
    {Sp : Nat → TermRun.Cfg → TermRun.Cfg → Prop} {obsTrace : TermRun.Cfg → List Ev}
    {init : TermRun.Cfg → Prop} (h : Sim T (SrcSem.ofStepsG p k arch Sp obsTrace init) Λ B asm)
    {P : TermRun.Cfg → Prop}
    (hP : ∀ c0 c, init c0 → TermSpawnStep.StepsG p k arch (fun c c' => ∃ i, Sp i c c') c0 c → P c)
    {t0 t : T.M.Cfg} {tr : List Ev} (h0 : T.load asm Λ = some t0) (hr : T.M.Run (T.marks asm Λ) t0 tr t) :
    ∃ s, h.R t s ∧ P s ∧ ∃ w : Witness T.M, Components T.M Λ w t s :=
  h.transfer (Inv := P) (fun _ _ ⟨c0, hi, hrun⟩ => hP c0 _ hi (SrcSem.ofStepsG_run_stepsG hrun)) h0 hr

/-- **Transfer of a WeakCore safety result to the source instance**: a
property of every configuration reachable along WeakCore's `StepsG` runs with
extra step "a spawn or an extern step" holds of a source configuration
related to each reachable target configuration of a simulation with
`SrcSem.source P p` (whose steps are gated `StepsG` steps). -/
theorem transfer_source {P : SrcSem.SrcParams} {p : CoreTerm.Prog}
    (h : Sim T (SrcSem.source P p) Λ B asm) {Q : TermRun.Cfg → Prop}
    (hQ : ∀ c0 c, P.init c0 →
      TermSpawnStep.StepsG p P.k P.arch (fun c c' => ∃ i, SrcSem.SpawnBy P.cap i c c' ∨ P.hooks.ext i c c') c0 c →
        Q c)
    {t0 t : T.M.Cfg} {tr : List Ev} (h0 : T.load asm Λ = some t0) (hr : T.M.Run (T.marks asm Λ) t0 tr t) :
    ∃ s, h.R t s ∧ Q s ∧ ∃ w : Witness T.M, Components T.M Λ w t s :=
  h.transfer (Inv := Q) (fun _ _ ⟨c0, hi, hrun⟩ => hQ c0 _ hi (SrcSem.source_run_stepsG hrun)) h0 hr

/-- **Transfer of a WeakCore safety result**: a property of every
configuration reachable along `StepsX` (machine steps and spawns, the runs
WeakCore's token-soundness theorems quantify over) holds of a source
configuration related to each reachable target configuration. -/
theorem transfer_stepsX {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap : Nat}
    {init : TermRun.Cfg → Prop} (h : Sim T (SrcSem.ofSpawn p k arch cap init) Λ B asm)
    {P : TermRun.Cfg → Prop} (hP : ∀ c0 c, init c0 → TermSpawnStep.StepsX p k arch cap c0 c → P c)
    {t0 t : T.M.Cfg} {tr : List Ev} (h0 : T.load asm Λ = some t0) (hr : T.M.Run (T.marks asm Λ) t0 tr t) :
    ∃ s, h.R t s ∧ P s ∧ ∃ w : Witness T.M, Components T.M Λ w t s :=
  h.transfer (Inv := P) (fun _ _ ⟨c0, hi, hrun⟩ => hP c0 _ hi (SrcSem.ofSpawn_run_stepsX hrun)) h0 hr

end Sim

/-! ## Sanity: the statement is satisfiable, and not by everything -/

/-- The existing machine as a target: the assembly is the per-thread start
states and the initial memory (what Kraken's runners and kits start from),
loaded by `Config.init`. -/
def Target.ofBase (I : Kraken.Promising.ISA) (A : Kraken.Promising.Arch)
    (rv : I.State → I.RegId → BitVec 64) (pl : I.State → BitVec 64 → Option (BitVec 64)) : Target where
  M := ExtMachine.ofBase I A rv pl
  Asm := List I.State × List (Kraken.Promising.Loc × Kraken.Promising.Val)
  load asm _ := some (Kraken.Promising.Config.init asm.1 asm.2, ())
  resolve _ _ _ := none

/-- The source configuration with no threads and empty memory. -/
def emptyCfg : TermRun.Cfg := { mem := #[], ths := #[] }

/-- A small well-formed layout with no static data. -/
def trivLayout : Layout where
  code := ⟨16, 32⟩
  data := ⟨48, 16⟩
  heap := ⟨64, 16⟩
  stackPool := ⟨80, 16⟩
  pinned := ⟨96, 16⟩
  static _ := none
  image := []
  symbols := []
  abortLbl k := s!"scc_abort_{k.idx}"

theorem trivLayout_wf : trivLayout.WF where
  inSpace r hr := by
    simp only [Layout.regions, trivLayout, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Range.InSpace] <;> omega
  aligned r hr := by
    simp only [Layout.regions, trivLayout, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Range.Aligned]
  disjoint := by simp only [trivLayout, Range.Disjoint]; omega
  abortInj k k' h := by
    cases k <;> cases k' <;> first | rfl | simp [trivLayout, AbortKind.idx] at h
  image p hp := by simp [trivLayout] at hp
  symIn p hp := by simp [trivLayout] at hp
  symAbove p hp := by simp [trivLayout] at hp
  symNodup := by simp [trivLayout]
  pos r hr := by
    simp only [Layout.regions, trivLayout, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

section Trivial

variable {I : Kraken.Promising.ISA} {A : Kraken.Promising.Arch}

/-- The empty start configuration of the existing machine takes no step. -/
theorem init_nil_no_step {tid : Nat} {c' : Kraken.Promising.Config I} :
    ¬ Kraken.Promising.Live.Inf.StepSemInf A tid (Kraken.Promising.Config.init [] []) c' := by
  rintro (⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩) <;>
    simp [Kraken.Promising.Config.init] at ht

/-- The empty source configuration takes no step. -/
theorem emptyCfg_no_step {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c' : TermRun.Cfg} :
    ¬ TermRun.Step p k arch emptyCfg c' :=
  SrcSem.no_step_of_no_threads rfl

/-- The witness with empty maps. -/
def Witness.empty (M : ExtMachine) : Witness M :=
  ⟨fun _ => none, fun _ => none, fun _ => 0, fun _ => none, fun _ _ _ _ => none, fun _ _ => False,
    fun _ => 0, fun _ => 0⟩

/-- **The components of `R` are satisfiable**: they hold of any target
configuration with no threads, no shared writes and no stack ranges, and the
empty source configuration, under a layout with no static data. -/
theorem components_empty (M : ExtMachine) (Λ : Layout) (t : M.Cfg) (ht : t.1.threads = #[])
    (hm : t.1.mem.msgs = #[]) (hs : ∀ j, M.stackRange t j = none) (hst : ∀ l, Λ.static l = none) :
    Components M Λ (Witness.empty M) t emptyCfg := by
  constructor <;>
    simp [Witness.empty, emptyCfg, ht, hm, hs, hst, Kraken.Promising.Memory.get?]

/-- **Non-vacuity**: the empty assembly is a correct lowering of the empty
program, on the existing machine, for every budget. Every clause is
discharged, and every component of `R` holds of the start states with the
empty witness. -/
theorem correct_trivial (rv : I.State → I.RegId → BitVec 64) (pl : I.State → BitVec 64 → Option (BitVec 64))
    (p : CoreTerm.Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (B : Budget) :
    Correct (Target.ofBase I A rv pl) (SrcSem.ofStep p k arch (· = emptyCfg)) trivLayout B ([], []) := by
  let t0 : (Target.ofBase I A rv pl).M.Cfg := (Kraken.Promising.Config.init [] [], ())
  have stuck : ∀ tid es c', ¬ (Target.ofBase I A rv pl).M.Step ((Target.ofBase I A rv pl).marks ([], []) trivLayout) tid t0 es c' :=
    fun _ _ _ hs =>
    init_nil_no_step ((ExtMachine.ofBase_step_iff (fun _ => rfl)).mp hs).2
  have run0 : ∀ t0' tr t, (Target.ofBase I A rv pl).load ([], []) trivLayout = some t0' →
      (Target.ofBase I A rv pl).M.Run ((Target.ofBase I A rv pl).marks ([], []) trivLayout) t0' tr t → tr = [] ∧ t = t0 := by
    intro t0' tr t h0 hr
    cases h0
    exact LRun.eq_refl_of_stuck hr fun es c ⟨tid, hs⟩ => stuck tid es c hs
  refine ⟨{
    R := fun t s => t = t0 ∧ s = emptyCfg
    layout := trivLayout_wf
    start := ⟨t0, emptyCfg, rfl, rfl, rfl, rfl⟩
    progress := ?_
    sim := ?_
    abort := ?_
    explicit := ?_ }⟩
  · intro t0' tr t h0 hr
    obtain ⟨-, rfl⟩ := run0 t0' tr t h0 hr
    refine ⟨⟨?_, Or.inl ?_⟩, ?_, ?_⟩
    · rintro ⟨tid, m, outs, hs, -⟩
      have h : Kraken.Promising.stepThread A (Kraken.Promising.Config.init [] [] :
          Kraken.Promising.Config I) tid = none := by
        simp [Kraken.Promising.stepThread, Kraken.Promising.Config.init]
      exact absurd (h.symm.trans hs) (by simp)
    · simp [t0, Target.ofBase, Kraken.Promising.Config.final, Kraken.Promising.Config.init]
    · simp [t0, Kraken.Promising.Config.init]
    · simp [t0, Kraken.Promising.Config.init]
  · intro t0' tr t h0 hr
    obtain ⟨rfl, rfl⟩ := run0 t0' tr t h0 hr
    exact ⟨[], emptyCfg, ⟨emptyCfg, rfl, .refl _⟩, ⟨rfl, rfl⟩, List.prefix_refl _⟩
  · intro t0' tr t tid es t' _ h0 hr hs _
    obtain ⟨-, rfl⟩ := run0 t0' tr t h0 hr
    exact (stuck tid es t' hs).elim
  · rintro t s ⟨rfl, rfl⟩
    exact ⟨_, components_empty _ trivLayout t0 (by simp [t0, Kraken.Promising.Config.init])
      (by simp [t0, Kraken.Promising.Config.init]) (fun _ => rfl) (fun _ => rfl)⟩

end Trivial

section Rejected

variable (I : Kraken.Promising.ISA) (A : Kraken.Promising.Arch)

/-- A toy target with one thread in state `st`, always at a system call
(no instruction step), at pc 0, that runs until it emits `e` once, by a
system call. Every label resolves to 0, so an abort is at its site. -/
def oneShot (e : Ev) (st : I.State) : Target where
  M := {
    I := I, A := A, X := Bool
    runs := fun c tid => c.2 = false ∧ tid = 0
    atSys := fun _ _ => True
    spawn := fun _ _ _ _ => False
    sys := fun _ _ c es c' => c.2 = false ∧ es = [e] ∧ c' = (c.1, true)
    xfer := fun _ _ _ _ => False
    live := fun _ _ => False
    exited := fun _ => none
    fault := fun _ => False
    regVal := fun _ _ => 0
    privLoad := fun _ _ => none
    stackRange := fun _ _ => none
    pc := fun _ => 0 }
  Asm := Unit
  load _ _ := some (Kraken.Promising.Config.init [st] [], false)
  resolve _ _ _ := some 0

/-- `oneShot`'s thread is at every abort site. -/
theorem oneShot_abort_at (e : Ev) (st : I.State) {Λ : Layout} :
    ∀ k, Ev.abort k ∈ [e] → ∃ a, ((oneShot I A e st).marks () Λ).abortAt k = some a ∧
      (oneShot I A e st).M.AtAddr a (Kraken.Promising.Config.init [st] [], false) 0 :=
  fun _ _ => ⟨0, rfl, ⟨_, rfl, rfl⟩⟩

/-- The runs of the empty source are empty. -/
theorem emptyCfg_reach {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {tr : List Ev}
    {s : TermRun.Cfg} (h : (SrcSem.ofStep p k arch (· = emptyCfg)).Reach tr s) : tr = [] ∧ s = emptyCfg := by
  obtain ⟨s0, rfl, hr⟩ := h
  exact LRun.eq_refl_of_stuck hr fun _ _ ⟨_, hs⟩ =>
    hs.1.elim (fun h => emptyCfg_no_step h.step) id

/-- **Rejected: spurious output.** A target that prints a byte is not a
correct lowering of the empty program. -/
theorem not_correct_spurious_output (b : Fin 256) (st : I.State) (p : CoreTerm.Prog) (k : Promises.Knobs)
    (arch : WeakMem.Arch) (Λ : Layout) (B : Budget) :
    ¬ Correct (oneShot I A (.out b) st) (SrcSem.ofStep p k arch (· = emptyCfg)) Λ B () := by
  rintro ⟨h⟩
  have hr : (oneShot I A (.out b) st).M.Run ((oneShot I A (.out b) st).marks () Λ)
      (Kraken.Promising.Config.init [st] [], false) [.out b] (Kraken.Promising.Config.init [st] [], true) := by
    unfold ExtMachine.Run
    exact LRun.step (es := [.out b]) (tr := []) (c' := (Kraken.Promising.Config.init [st] [], true))
      ⟨0, .sys ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (by simp) (by simp) (by simp)⟩ (.refl _)
  obtain ⟨tr', s, hs, -, hp⟩ := h.sim _ _ _ rfl hr
  obtain ⟨rfl, -⟩ := emptyCfg_reach hs
  simp [obs, Ev.isObs] at hp

/-- **Rejected: unjustified abort.** A target that aborts at once, of any
kind, is not a correct lowering of the empty program: the empty program
takes no step, so it never leaves any budget, and no `write` came before. -/
theorem not_correct_spurious_abort (ak : AbortKind) (st : I.State) (p : CoreTerm.Prog) (k : Promises.Knobs)
    (arch : WeakMem.Arch) (Λ : Layout) (B : Budget) :
    ¬ Correct (oneShot I A (.abort ak) st) (SrcSem.ofStep p k arch (· = emptyCfg)) Λ B () := by
  rintro ⟨h⟩
  obtain ⟨s, w, i, hs, -, -, -, hj⟩ := h.abort _ [] _ 0 [.abort ak]
    (Kraken.Promising.Config.init [st] [], true) ak rfl (.refl _)
    (.sys ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (by simp) (oneShot_abort_at I A (.abort ak) st) (by simp)) (by simp)
  obtain ⟨-, rfl⟩ := emptyCfg_reach hs
  have nst : ∀ es s', ¬ (SrcSem.ofStep p k arch (· = emptyCfg)).step i emptyCfg es s' :=
    fun _ _ hst => hst.1.elim (fun h => emptyCfg_no_step h.step) id
  cases ak with
  | writeErr => simp [AbortJustified] at hj
  | threads =>
    rcases hj with hj | ⟨es, s', hst, -⟩
    · simp at hj
    · exact nst es s' hst
  | _ => obtain ⟨es, s', hst, -⟩ := hj; exact nst es s' hst

end Rejected

end Scc.Sem
