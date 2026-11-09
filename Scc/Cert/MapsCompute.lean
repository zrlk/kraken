import Scc.Cert.Maps

/-!
# Certificate tables computed from the text (ISA-neutral core)

The root maps and block successors of `Scc.Cert.Maps`, computed from the
emitted text, and a checker for a claimed table. The text arrives as a list of items (`Item`): a
label, or an instruction classified by what the analysis needs (`Ins`: its control flow and the
frame slots it reads, writes and takes the address of). The ISA front ends (`MapsX64`,
`MapsA64`) classify their instructions and supply the per-function tags (`FnTags`).

**Tags trusted from the IR, tied to the text only via the certificates' `reproduces` guard;
option B must discharge this.** The tags of the parameter, result and argument registers and of
the frame slots come from the IR function and its signature, not from the text. The text is
used for the addresses, the control flow and the slot liveness.

What is computed, per function, over its body (from `FnTags.bodyStart` up to `FnTags.bodyEnd`):

* **Leaders**: the body start, every branch target inside the body, and every instruction after
  a call or a conditional branch, except that a conditional branch followed by an unconditional
  one (`jcc; jmp`) is one terminator: the `jmp` is no leader unless it is a branch target. An
  instruction after a `jmp`, a `ret` or a block-ending instruction is a leader only if it is a
  branch target (fall-through does not reach it).
* **Slot liveness**: a slot is live before an instruction if the instruction reads it, or if it
  is live after it and the instruction does not write it; a slot whose address is taken
  anywhere in the body is live everywhere (it may be read through the pointer). Iterated to the
  fixpoint over the body's control flow.
* **Root maps**: at each prologue block entry (`FnTags.paramPts`), the parameter registers; at
  each leader, the tagged slots live there, and at a leader that is a call's return address
  also the call's result registers (`FnTags.callRes`); at each call, keyed at its return address,
  the roots live after the call in the caller: the slot entry of `scc_stackmap` for that return
  address (`FnTags.stackmap`; every call must have one and every entry must belong to a call,
  else the computation fails), then the call's result registers; at each `ret`, the result
  registers; at the grow stub's call of
  the trampoline (`FnTags.growStub`), keyed at its return address, its `scc_stackmap` entry: the
  save-area words of the tagged parameters live on entry.
* **Successors**: from each leader, the first safe point control reaches (the return address of
  the block's call, its `ret`, the leader a fall-through reaches) or the branch targets (both
  targets of a `jcc; jmp` terminator); from each prologue block entry and from the grow call's
  return address, the first safe points reached through the function's text (`outSuccs`: the
  body's start, the grow call's return address, the stack check it jumps back to).

Exemptions (no maps): the prologue instructions other than the block entries of `paramPts`,
the stubs from `bodyEnd` on (other than the grow stub's call; in particular no block-entry map at
that call's return address, only its call map, where the stub reloads the argument registers
and jumps back to the check: a documented gap), and the routines without tags (the runtime;
computed from the text and listed by the front ends). A conditional branch out of the body must
go to an abort stub (a trap path: the abort call, then a trap) or a child stub (a new thread's
entry, covered by the thread-start rule of the collector track, not by these tables), else the
computation fails (`stubsOk`, "The stubs a body branches to").

**The call map at the return address is local to the caller.** It lists what the caller itself
keeps live after the call: the slots of its `scc_stackmap` entry (the IR registers live after
the call, all spilled: no machine register is kept across a call), then the call's result
registers, tagged by the caller's own destination registers of that call (`FnTags.callRes`; a
result the caller drops is no root). Nothing depends on the callee's body or on the callers; in
particular no argument register is listed (they are dead at the return address). The grow
stub's call map is its `scc_stackmap` entry alone.

Untrusted: a failed check fails a certificate, it never makes one unsound.

**What `check_sound` says, and what it does not.** It says that a table the checker accepts is
the recomputed one (`compute`) and has the format's shape; it is not a correctness theorem. That
the computed maps are *correct* (every location that holds a root at a safe point is in its map,
and every location in a map holds a value of its tag or a harmless one) is not proved here.
TODO: state and prove it against the x64 / AArch64
semantics of the text.

**Over-approximated slots.** A slot whose address is taken is listed at every leader, and a slot
read before it is written on some path is listed where it is live, so a map can list a slot that
was never written on the path taken. Nothing zeroes frame slots in the prologue today. For a
`stack` slot this is harmless: the grow routine rewrites a listed word only if it lies in the old
stack range (`Scc/IR/StackMap.lean`, "Which slots are listed"), the same rule the `scc_stackmap`
entries rely on, which list address-taken slots at every call. For a `heap` slot it is harmless
only while no collector reads the maps (`Func.heapRegs`: "nothing reads them yet"); a moving
collector needs the prologue to zero the tagged slots that a map can list before their first
write (or a definite-assignment check that rules them out). Open item for the collector track.
-/

namespace Scc.Cert.Maps

/-- What an instruction does to control. -/
inductive Flow where
  /-- Falls through to the next instruction. -/
  | fall
  /-- Jumps to a label. -/
  | jmp (l : String)
  /-- Jumps to a label or falls through. -/
  | jcc (l : String)
  /-- Calls a symbol, then falls through. -/
  | call (g : String)
  /-- Returns. -/
  | ret
  /-- Leaves the function otherwise (a tail jump, a trap). -/
  | stop
  deriving Repr, BEq, DecidableEq, Inhabited

/-- **An instruction, classified**: its control flow and the frame slots (signed byte offsets
from the frame record) it reads, writes (the whole word) and takes the address of. -/
structure Ins where
  flow : Flow := .fall
  reads : List Int := []
  writes : List Int := []
  takes : List Int := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An item of the text, at its byte offset from the start of the text; an instruction with its
size in bytes. -/
inductive Item where
  | label (addr : Nat) (l : String)
  | ins (addr size : Nat) (i : Ins)
  deriving Repr, BEq, Inhabited

/-- **The tags of one function** (from the IR; see the module docstring). -/
structure FnTags where
  /-- The labels of the prologue's block entries (the function's entry, the stack check's
  continuation): each gets a map of the parameter registers. -/
  paramPts : List String
  /-- The label of the first body block. -/
  bodyStart : String
  /-- The first label after the body (its stubs), or `none`: the body runs to the next function. -/
  bodyEnd : Option String
  /-- The tagged parameter registers (the maps at `paramPts`). -/
  params : List (Loc × Tag)
  /-- The tagged result registers (each `ret`'s map). -/
  result : List (Loc × Tag)
  /-- The tagged frame slots. -/
  slots : List (Int × Tag)
  /-- The tagged result registers of each call of the body, in order: the caller's own tags of
  the call's destination registers (added to the call's map and to the block-entry map at its
  return address). One entry per call of the body, else the computation fails. -/
  callRes : List (List (Loc × Tag)) := []
  /-- The label of the grow stub (the failed stack check's path to the trampoline), or `none`:
  its first call gets a call map, its `scc_stackmap` entry (the save-area words). -/
  growStub : Option String := none
  /-- The `scc_stackmap` entries of the function: return address, stack slots, heap slots. -/
  stackmap : List (Nat × List Int × List Int) := []
  deriving Repr, Inhabited

/-! ## The body -/

/-- The items of the body: from the label `bodyStart` up to the label `bodyEnd` (exclusive). -/
def bodyOf (t : FnTags) (items : List Item) : List Item :=
  let rest := items.dropWhile fun | .label _ l => l != t.bodyStart | _ => true
  match t.bodyEnd with
  | some e => rest.takeWhile fun | .label _ l => l != e | _ => true
  | none => rest

/-- The instructions of a body, in order, with their addresses and sizes. -/
def insOf (body : List Item) : Array (Nat × Nat × Ins) :=
  (body.filterMap fun | .ins a z i => some (a, z, i) | _ => none).toArray

/-- The index of the first instruction at or after each label of the body. -/
def labelIdx (body : List Item) : List (String × Nat) :=
  (body.foldl (fun (acc : List (String × Nat) × Nat) it => match it with
    | .label _ l => ((l, acc.2) :: acc.1, acc.2)
    | .ins _ _ _ => (acc.1, acc.2 + 1)) ([], 0)).1.reverse

/-- The successor indices of instruction `k` (`n` instructions; a target outside the body has
none). -/
def succIdx (lix : List (String × Nat)) (n k : Nat) (i : Ins) : List Nat :=
  let nxt := if k + 1 < n then [k + 1] else []
  let tgt (l : String) := match lix.lookup l with | some j => if j < n then [j] else [] | none => []
  match i.flow with
  | .fall | .call _ => nxt
  | .jmp l => tgt l
  | .jcc l => tgt l ++ nxt
  | .ret | .stop => []

/-- `a ∪ b` on slot lists. -/
def unionI (a b : List Int) : List Int := b.foldl (fun acc o => if acc.contains o then acc else acc ++ [o]) a

/-- **Live slots before each instruction** (see the module docstring), by iteration to the
fixpoint; the slots whose address is taken are live everywhere. -/
def liveSlots (body : List Item) : Array (List Int) :=
  let is := insOf body
  let n := is.size
  let lix := labelIdx body
  let taken := is.toList.foldl (fun acc (_, _, i) => unionI acc i.takes) []
  let step (live : Array (List Int)) : Array (List Int) :=
    (Array.range n).map fun k =>
      let i := (is[k]!).2.2
      let out := (succIdx lix n k i).foldl (fun acc j => unionI acc (live[j]!)) []
      unionI (unionI taken i.reads) (out.filter fun o => !i.writes.contains o)
  let slotsN := is.toList.foldl (fun acc (_, _, i) => unionI acc (i.reads ++ i.writes ++ i.takes)) []
  let rec go : Nat → Array (List Int) → Array (List Int)
    | 0, m => m
    | f + 1, m =>
      let m' := step m
      if m'.map List.length == m.map List.length then m else go f m'
  go ((n + 1) * (slotsN.length + 1)) (Array.replicate n [])

/-- Insert `x` into `l` after every element `y` with `le y x` up to the first one without (into
a list sorted by `le`, after the elements equal to it). Structural, so the kernel reduces it. -/
def insertStable {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le y x then y :: insertStable le x ys else x :: y :: ys

/-- **Stable insertion sort** by a total preorder `le`: for such an `le` the same list as
`List.mergeSort` (the sorted permutation that keeps the order of equal elements is unique), but
structural (`List.mergeSort` is by well-founded recursion, which the kernel does not unfold), so
that `decide +kernel` can evaluate the tables. Quadratic; the tables have a few hundred
entries. -/
def sortStable {α : Type} (le : α → α → Bool) (l : List α) : List α :=
  l.foldl (fun acc x => insertStable le x acc) []

/-! ## Text tests the kernel reduces

The front ends read the emitter's assembler lines. Core's `String.startsWith`, `String.splitOn`
and `String.toNat?` do not reduce in the kernel (`decide +kernel` gets stuck on them), so the
front ends use these forms, on the UTF-8 bytes or the characters, with the same results (pinned
against the core functions by the tests below). -/

/-- `p` occurs in the byte list `l` (at some position). -/
def bytesInfix (p : List UInt8) : List UInt8 → Bool
  | [] => p.isEmpty
  | b :: bs => p.isPrefixOf (b :: bs) || bytesInfix p bs

/-- `s.startsWith p`, on the UTF-8 bytes (a byte prefix of a valid UTF-8 string is a character
prefix: the encoding is prefix-free). -/
def startsK (s p : String) : Bool := p.toUTF8.data.toList.isPrefixOf s.toUTF8.data.toList

/-- `p` occurs in `s`, on the UTF-8 bytes (an occurrence starts at a character boundary: no
encoded character starts with a continuation byte); `(s.splitOn p).length > 1` for non-empty
`p`. -/
def containsK (s p : String) : Bool := bytesInfix p.toUTF8.data.toList s.toUTF8.data.toList

/-- `l` split at the occurrences of `sep`, left to right, not overlapping; `[l]` for an empty
`sep` (`String.splitOn` on characters). -/
def splitList {α : Type} [BEq α] (sep : List α) (l : List α) : List (List α) :=
  let rec go : Nat → List α → List α → List (List α)
    | 0, cur, rest => [cur.reverse ++ rest]
    | f + 1, cur, rest =>
      if sep.isPrefixOf rest then cur.reverse :: go f [] (rest.drop sep.length)
      else match rest with
        | [] => [cur.reverse]
        | c :: cs => go f (c :: cur) cs
  if sep.isEmpty then [l] else go (l.length + 1) [] l

/-- `s.splitOn sep` (on the characters). -/
def splitK (s sep : String) : List String := (splitList sep.toList s.toList).map String.ofList

/-- `s.toNat?`: decimal digits, `_` between two digits allowed. -/
def toNatK? (s : String) : Option Nat :=
  let l := s.toList
  let ok := l.foldl (fun (st : Option Bool) c =>
    st.bind fun lastDigit =>
      if c = '_' then (if lastDigit then some false else none)
      else if c.isDigit then some true else none) (some false)
  if ok = some true then
    some (l.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0)
  else none

/-- `s.toInt?`: an optional `-`, then `toNatK?`. -/
def toIntK? (s : String) : Option Int :=
  match s.toList with
  | '-' :: rest => (toNatK? (String.ofList rest)).map Int.negOfNat
  | _ => (toNatK? s).map Int.ofNat

/-- The branch targets of a body (instruction indices), in the order of their branches. -/
def targets (body : List Item) : List Nat :=
  let is := insOf body
  let lix := labelIdx body
  (is.toList.filterMap fun (_, _, i) => match i.flow with
    | .jmp l | .jcc l => lix.lookup l | _ => none).filter (· < is.size)

/-- Instruction `k` is a conditional branch whose next instruction is an unconditional one that
is no branch target (`tg`): the two are one terminator (`jcc; jmp`). -/
def jccJmp (is : Array (Nat × Nat × Ins)) (tg : List Nat) (k : Nat) : Bool :=
  match (is[k]!).2.2.flow with
  | .jcc _ => k + 1 < is.size && !tg.contains (k + 1) &&
      (match (is[k + 1]!).2.2.flow with | .jmp _ => true | _ => false)
  | _ => false

/-- **The leaders** (instruction indices): the first instruction, every branch target in the
body, and every instruction after a call or a conditional branch, except the `jmp` of a
`jcc; jmp` terminator (`jccJmp`). Control reaches an instruction after a `jmp`, a `ret` or a
block end only through a branch, so it is a leader only as a branch target. -/
def leaders (body : List Item) : List Nat :=
  let is := insOf body
  let n := is.size
  let tg := targets body
  let after := ((List.range n).filter fun k => match (is[k]!).2.2.flow with
    | .call _ => true
    | .jcc _ => !jccJmp is tg k
    | _ => false).map (· + 1) |>.filter (· < n)
  sortStable (fun a b => decide (a ≤ b)) ((if n = 0 then [] else [0]) ++ tg ++ after).eraseDups

/-- The tagged slots of `t` among `live`, in `t.slots`' order. -/
def liveRoots (t : FnTags) (live : List Int) : List (Loc × Tag) :=
  t.slots.filterMap fun (o, g) => if live.contains o then some (.slot o, g) else none

/-- The slot part of a call's map: its `scc_stackmap` entry (keyed at return address `ra`);
an error if the function has none there. -/
def callRoots (t : FnTags) (ra : Nat) : Except String (List (Loc × Tag)) :=
  match t.stackmap.find? (·.1 == ra) with
  | some (_, st, hp) => .ok (st.map (fun o => (.slot o, .stack)) ++ hp.map (fun o => (.slot o, .heap)))
  | none => .error s!"{t.bodyStart}: no scc_stackmap entry at return address {ra}"

/-- The address of a label of the text. -/
def labelAddr (items : List Item) (l : String) : Option Nat :=
  items.findSome? fun | .label a l' => if l' == l then some a else none | _ => none

/-- The grow stub's call: the first call after label `l` (address, size, callee). -/
def growCall (items : List Item) (l : String) : Option (Nat × Nat × String) :=
  (items.dropWhile fun | .label _ l' => l' != l | _ => true).findSome? fun
    | .ins a z i => match i.flow with | .call g => some (a, z, g) | _ => none
    | _ => none

/-- **The result registers of the body's calls**, by return address: the `k`th call of the body
gets the `k`th entry of `FnTags.callRes`. An error if their numbers differ. -/
def siteRes (t : FnTags) (is : Array (Nat × Nat × Ins)) : Except String (List (Nat × List (Loc × Tag))) := do
  let ras := is.toList.filterMap fun (a, z, i) => match i.flow with | .call _ => some (a + z) | _ => none
  unless ras.length == t.callRes.length do
    throw s!"{t.bodyStart}: {ras.length} calls in the body, {t.callRes.length} in the IR"
  pure (ras.zip t.callRes)

/-- **The root maps of one function, from the slot liveness `live`** (indexed by the body's
instructions, as `liveSlots`): a parameter map at each of `paramPts`, over the body the
maps of its leaders, calls and `ret`s, and the map of the grow stub's call. A call's map is keyed
at its return address (where a thread stopped in the callee resumes) and lists the live slots of
its `scc_stackmap` entry, then the call's result registers (`siteRes`); at a return address that
is also a block entry, the call's map comes first, then the block entry's, which adds the call's
result registers to the live slots. An error if a call has no `scc_stackmap` entry, an entry of
the function is no call's return address (the call maps are the table's entries both ways), or
the body's calls do not match `FnTags.callRes`. `fnMaps` is this with the reference liveness;
the certificate's checker (`checkW`) uses it with a witness. -/
def fnMapsW (t : FnTags) (items : List Item) (live : Array (List Int)) :
    Except String (List RootMap) := do
  -- the function's entry (the first of `paramPts`) is frameless: the prologue has not set up
  -- the frame record yet
  let pre ← t.paramPts.zipIdx.mapM fun (l, j) => match labelAddr items l with
    | some a => pure { pt := ⟨.blockEntry, a⟩, roots := t.params, frameless := j == 0 }
    | none => throw s!"{t.bodyStart}: no label {l}"
  let body := bodyOf t items
  let is := insOf body
  let ls := leaders body
  let grow ← match t.growStub with
    | none => pure none
    | some l => match growCall items l with
      | some c => pure (some c)
      | none => throw s!"{t.bodyStart}: no call after the grow stub {l}"
  let rs ← siteRes t is
  let calls := rs.map (·.1) ++ (grow.map fun (a, z, _) => a + z).toList
  for (ra, _) in t.stackmap do
    unless calls.contains ra do throw s!"{t.bodyStart}: scc_stackmap entry at {ra} is no call's return address"
  let ms ← (List.range is.size).mapM fun k => do
    let (a, z, i) := is[k]!
    -- the call's result registers, if instruction `k` is a call's return address
    let res : List (Loc × Tag) := if k = 0 then [] else match (is[k - 1]!).2.2.flow with
      | .call _ => (rs.lookup a).getD []
      | _ => []
    let entry : List RootMap :=
      if ls.contains k then [{ pt := ⟨.blockEntry, a⟩, roots := res ++ liveRoots t (live[k]!) }]
      else []
    let own : List RootMap ← match i.flow with
      | .call _ => do
        let sl ← callRoots t (a + z)
        pure [{ pt := ⟨.call, a + z⟩, roots := sl ++ (rs.lookup (a + z)).getD [] }]
      -- frameless: the epilogue has torn the frame record down
      | .ret => pure [{ pt := ⟨.ret, a⟩, roots := t.result, frameless := true }]
      | _ => pure []
    pure (entry ++ own)
  let gm ← match grow with
    | some (a, z, _) => do
      let sl ← callRoots t (a + z)
      pure [{ pt := ⟨.call, a + z⟩, roots := sl : RootMap }]
    | none => pure []
  pure (pre ++ ms.flatten ++ gm)

/-- **The root maps of one function**: `fnMapsW` with the reference liveness (`liveSlots`). -/
def fnMaps (t : FnTags) (items : List Item) : Except String (List RootMap) :=
  fnMapsW t items (liveSlots (bodyOf t items))

/-- **The function symbols of `fns`**: each one's entry label (the first of `paramPts`). A tail
successor (`Succs.tail`) must be one of them (`Tables.tailsIn`, checked by `check`, `checkWWith`). -/
def fnNames (fns : List FnTags) : List String := fns.filterMap (·.paramPts.head?)

/-- **The successors of one function's blocks**: from each leader, the return address of the
call or the `ret` that ends its run, the leader a fall-through reaches, or the branch targets (of
a `jcc; jmp` terminator: the conditional branch's target, then the `jmp`'s); a `jmp` out of the
body (a tail jump), alone or the `jmp` of a `jcc; jmp` terminator, is succeeded by its target, by
name, whatever the target is (`Succs.tail`; a function's entry has the target's frameless
parameter map, and the jump arrives with the jumping function's frame torn down). That the target
is a function is not decided here but by the checkers (`Tables.tailsIn`: a `jmp` out of a body to
anything but a function symbol fails them). A conditional branch out of the body has no
successor here: it must go to a stub that never reaches a safe point, else `compute` and
`computeW` fail (`stubsOk`); so every branch out of a body is either a tail name or a stub. -/
def fnSuccs (t : FnTags) (items : List Item) : List Succs :=
  let body := bodyOf t items
  let is := insOf body
  let n := is.size
  let lix := labelIdx body
  let ls := leaders body
  let tg := targets body
  let addrOf (j : Nat) : Nat := (is[j]!).1
  let rec walk : Nat → Nat → List Nat × List String
    | 0, _ => ([], [])
    | f + 1, k =>
      if k ≥ n then ([], []) else
      let (a, z, i) := is[k]!
      match i.flow with
      | .call _ => ([a + z], [])
      | .ret => ([a], [])
      | .stop => ([], [])
      | .jcc l => if jccJmp is tg k then
            -- the terminator's `jmp m` out of the body is a tail jump, as a lone one is
            let j := (is[k + 1]!).2.2
            let tl := match j.flow with
              | .jmp m => if (succIdx lix n (k + 1) j).isEmpty then [m] else []
              | _ => []
            ((succIdx lix n k { i with flow := .jmp l } ++ succIdx lix n (k + 1) j).map addrOf, tl)
          else ((succIdx lix n k i).map addrOf, [])
      | .jmp l => match succIdx lix n k i with
        | [] => ([], [l])
        | js => (js.map addrOf, [])
      | .fall => if ls.contains (k + 1) then (if k + 1 < n then ([addrOf (k + 1)], []) else ([], []))
          else walk f (k + 1)
  ls.map fun k => let (nx, tl) := walk (n + 1) k; ⟨addrOf k, nx, tl⟩

/-- **The successors outside the body**: from each prologue block entry (`paramPts`) and from the
grow stub's return address (which has its call's map but no block-entry map, the documented
gap), the first safe points control reaches, following the text of the whole function (a stub's
jump back to the stack check included): `pts` are the addresses of the function's maps (a call's
at its return address); a call or `ret` without a map is passed over (an abort call is followed
by a trap, which leaves). So the scheduler can be led from every safe point outside the body,
and from the grow call's return, to the next one. -/
def outSuccs (t : FnTags) (items : List Item) (pts : List Nat) : Except String (List Succs) := do
  let is := insOf items
  let n := is.size
  let lix := labelIdx items
  let rec walk : Nat → Nat → List Nat
    | 0, _ => []
    | f + 1, k =>
      if k ≥ n then [] else
      let (a, _, i) := is[k]!
      if pts.contains a then [a] else
      match i.flow with
      | .stop | .ret => []
      | .fall | .call _ => walk f (k + 1)
      | .jmp l => match lix.lookup l with | some j => walk f j | none => []
      | .jcc l => (match lix.lookup l with | some j => walk f j | none => []) ++ walk f (k + 1)
  -- the successors of the instruction at index `k`, not counting `k` itself
  let nexts (k : Nat) : List Nat :=
    if k ≥ n then [] else
    let (_, _, i) := is[k]!
    let nx := walk n (k + 1)
    let tg (l : String) := match lix.lookup l with | some j => walk n j | none => []
    (match i.flow with
      | .stop | .ret => []
      | .fall | .call _ => nx
      | .jmp l => tg l
      | .jcc l => tg l ++ nx).eraseDups
  let pre ← t.paramPts.mapM fun l => match lix.lookup l, labelAddr items l with
    | some k, some a => pure ({ addr := a, next := nexts k } : Succs)
    | _, _ => throw s!"{t.bodyStart}: no label {l}"
  -- from the grow call's return address (instruction `k + 1`, itself in `pts`: the call's map);
  -- the call's index by one pass over the instructions (an indexed search, `is[k]!` for each
  -- `k`, is quadratic in the kernel)
  let grow : List Succs := match t.growStub.bind (growCall items ·) with
    | some (a, z, _) => match (is.toList.zipIdx.find? (·.1.1 == a)).map (·.2) with
      | some k => [{ addr := a + z, next := nexts (k + 1) }]
      | none => []
    | none => []
  pure (pre ++ grow)

/-! ## The stubs a body branches to

A conditional branch out of a body (`jcc l`, `l` no label of the body) is no safe point and gets
no successor (`succIdx`): control that takes it must never come back to a safe point of the
function. That holds for the two stubs scc emits there, which `stubsOk` recognises from the items
after `l` (decided; a branch out of a body to anything else fails `compute` and `computeW`, so
the certificates' kernel-checked `computeW` refuses it):

* **An abort stub** (`.L<f>.ovf` on x64, `.L<n>_<f>.abort_overflow` on AArch64): instructions that
  fall through (the abort kind into the argument register), a call of a symbol starting with
  `scc_rt_abort`, then a trap (`trapAt`). `scc_rt_abort` does not return; the trap is not reached.
* **A child stub** (`.L<f>.child.<entry>` on x64, `.L<n>_<f>.child<k>` on AArch64: the label
  contains `.child`): instructions that fall through (the argument moves, the frame pointer
  zeroed), the call of the thread's entry, which the front ends classify as leaving the function
  (`.stop`: the frame pointer is zeroed before it), then a trap. Not a trap path: the new thread
  starts here, with no frame record and no safe point before the entry's own; it is covered by
  the thread-start rule (collector track), not by these tables. The entry's name is not checked
  (the front ends drop it with the call's classification; `exemptions` lists those calls).

A trap is a block-ending instruction (`ud2`, `.stop`) or a label `L` followed by `jmp L` (the
AArch64 halt loop). -/

/-- **A trap**: a block-ending instruction, or a label `L` followed by `jmp L`. -/
def trapAt : List Item → Bool
  | .ins _ _ i :: _ => i.flow == .stop
  | .label _ l :: .ins _ _ i :: _ => i.flow == .jmp l
  | _ => false

/-- The items after the leading instructions that fall through. -/
def dropFalls : List Item → List Item
  | [] => []
  | .label a l :: r => .label a l :: r
  | .ins a z i :: r => if i.flow == .fall then dropFalls r else .ins a z i :: r

/-- **The items after `l` are an abort or a child stub** (see the section docstring). -/
def stubShape (l : String) (after : List Item) : Bool :=
  match dropFalls after with
  | .ins _ _ i :: r => match i.flow with
    | .call g => startsK g "scc_rt_abort" && trapAt r
    | .stop => containsK l ".child" && trapAt r
    | _ => false
  | _ => false

/-- **The first conditional branch of `t`'s body out of the body to no stub** (`stubShape` of
the items after its target's label; a target the items do not label is no stub): its address
and target, or `none`. -/
def badStub? (t : FnTags) (items : List Item) : Option (Nat × String) :=
  let body := bodyOf t items
  let is := insOf body
  let lix := labelIdx body
  is.toList.findSome? fun (a, _, i) => match i.flow with
    | .jcc l =>
      if (match lix.lookup l with | some j => decide (j < is.size) | none => false) then none
      else match items.dropWhile (fun | .label _ m => m != l | _ => true) with
        | _ :: after => if stubShape l after then none else some (a, l)
        | [] => some (a, l)
    | _ => none

/-- **Every conditional branch out of a tagged body goes to a stub** (`badStub?`), else an
error. Checked first by `compute` and `computeW`. -/
def stubsOk (fns : List FnTags) (items : List Item) : Except String Unit :=
  match fns.findSome? fun t => (badStub? t items).map fun p => (t.bodyStart, p) with
  | some (b, a, l) => .error s!"{b}: the conditional branch at {a} leaves the body to {l}, no abort or child stub"
  | none => .ok ()

/-- **The tables of a text**: the maps and successors of its tagged functions, sorted by
address (stably: the order of `fnMaps` at one address is kept). A tail successor is a name, so
the tables of a part of the text (a function's slice, a range) do not depend on where the target
is: the parts' tables merged in address order are the whole text's by construction. An error if
a conditional branch leaves a body to no stub (`stubsOk`). -/
def compute (fns : List FnTags) (items : List Item) : Except String Tables := do
  stubsOk fns items
  let ms ← fns.mapM fun t => fnMaps t items
  let os ← (fns.zip ms).mapM fun (t, m) => outSuccs t items (m.map (·.pt.addr))
  pure { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) ms.flatten,
         succs := sortStable (fun a b => decide (a.addr ≤ b.addr))
           (fns.flatMap (fun t => fnSuccs t items) ++ os.flatten) }

/-- **The checker**: a claimed table is the computed one, has the format's shape, and its tail
names are function symbols of `fns` (`fnNames`). -/
def check (fns : List FnTags) (items : List Item) (t : Tables) : Bool :=
  match compute fns items with
  | .ok c => decide (t = c) && t.g1Ok && t.tailsIn (fnNames fns)
  | .error _ => false

theorem check_sound {fns : List FnTags} {items : List Item} {t : Tables}
    (h : check fns items t = true) :
    compute fns items = .ok t ∧ t.g1Ok = true ∧ t.tailsIn (fnNames fns) = true := by
  unfold check at h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨by rw [hc, h.1.1], h.1.2, h.2⟩
  · simp at h

/-! ## The checker with a liveness witness (W3 option (b))

`liveSlots` is a fixpoint iteration the kernel cannot afford on real functions. The certificate
instead carries a **liveness witness** per tagged function (`w`, indexed like `liveSlots`), and the
kernel checks locally that it is a **post-fixpoint** of the same transfer function (`liveOk`), then
builds the maps from it (`fnMapsW`). Every post-fixpoint contains the reference liveness
(`liveSlots_le`), so the maps can only list extra slots, never miss one the reference lists. scc
emits the reference liveness (`witness`), so the tables equal `compute`'s (`computeW_witness`);
that equality is checked by scc (untrusted, W1), not by the certificate. -/

/-- `a ⊆ b` on slot lists. -/
def subI (a b : List Int) : Bool := a.all (b.contains ·)

/-- `liveOk`'s loop: instruction `k` (of `n`, with the label indices `lix`) and the rest `is`,
with the witness entries from `k` on (`ws`; `wl` the whole witness). The entry of the next
instruction is the head of the rest (`ws`), any other one is looked up in `wl`. -/
def liveOkGo (taken : List Int) (lix : List (String × Nat)) (n : Nat) (wl : List (List Int)) :
    List (Nat × Nat × Ins) → List (List Int) → Nat → Bool
  | [], [], _ => true
  | (_, _, i) :: is, wk :: ws, k =>
    subI taken wk && subI i.reads wk &&
      (succIdx lix n k i).all (fun j =>
        subI ((if j == k + 1 then ws.headD [] else wl.getD j []).filter
          fun o => !i.writes.contains o) wk) &&
      liveOkGo taken lix n wl is ws (k + 1)
  | _, _, _ => false

/-- **`w` is a post-fixpoint of slot liveness on `body`**: one entry per instruction, and before
each instruction `k` it contains the address-taken slots, the slots `k` reads, and every slot live
before a successor of `k` that `k` does not write (`liveSlots`' step, as inclusions; `liveOk_spec`).
Recursive over the instructions and the witness together, not indexed into arrays: the kernel
evaluates `Array` indexing with `get!` at a cost that dominates on large routines (`scc_rt_grow`:
2139 MB indexed, 455 MB recursive). -/
def liveOk (body : List Item) (w : Array (List Int)) : Bool :=
  let is := (insOf body).toList
  let taken := is.foldl (fun acc (_, _, i) => unionI acc i.takes) []
  liveOkGo taken (labelIdx body) is.length w.toList is w.toList 0

/-- **The tables from witnesses** `ws` (one per function of `fns`, in order): as `compute`, with
`fnMapsW` (the stubs checked first, `stubsOk`). -/
def computeW (fns : List FnTags) (items : List Item) (ws : List (Array (List Int))) :
    Except String Tables := do
  stubsOk fns items
  unless ws.length == fns.length do throw s!"{ws.length} liveness witnesses for {fns.length} functions"
  let ms ← (fns.zip ws).mapM fun (t, w) => fnMapsW t items w
  let os ← (fns.zip ms).mapM fun (t, m) => outSuccs t items (m.map (·.pt.addr))
  pure { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) ms.flatten,
         succs := sortStable (fun a b => decide (a.addr ≤ b.addr))
           (fns.flatMap (fun t => fnSuccs t items) ++ os.flatten) }

/-- **The witnesses scc emits**: the reference liveness of each function. -/
def witness (fns : List FnTags) (items : List Item) : List (Array (List Int)) :=
  fns.map fun t => liveSlots (bodyOf t items)

/-- **The checker with witnesses**, the function symbols `names`: every witness is a
post-fixpoint on its function's body, and the claimed table is the one built from them, with the
format's shape and its tail names among `names` (so a `jmp` out of a body, alone or after a
`jcc`, to anything but one of `names` fails it; a `jcc` out of a body to anything but a stub fails
`computeW`, `stubsOk`). -/
def checkWWith (names : List String) (fns : List FnTags) (items : List Item)
    (ws : List (Array (List Int))) (t : Tables) : Bool :=
  (fns.zip ws).all (fun (f, w) => liveOk (bodyOf f items) w) &&
  match computeW fns items ws with
  | .ok c => decide (t = c) && t.g1Ok && t.tailsIn names
  | .error _ => false

theorem checkWWith_sound {names : List String} {fns : List FnTags} {items : List Item}
    {ws : List (Array (List Int))} {t : Tables} (h : checkWWith names fns items ws t = true) :
    (∀ p ∈ fns.zip ws, liveOk (bodyOf p.1 items) p.2 = true) ∧
      computeW fns items ws = .ok t ∧ t.g1Ok = true ∧ t.tailsIn names = true := by
  unfold checkWWith at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hl, h⟩ := h
  refine ⟨fun p hp => hl p hp, ?_⟩
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨by rw [hc, h.1.1], h.1.2, h.2⟩
  · simp at h

/-- **The checker with witnesses**: `checkWWith`, the tail names among `fns`' symbols. -/
def checkW (fns : List FnTags) (items : List Item) (ws : List (Array (List Int))) (t : Tables) : Bool :=
  checkWWith (fnNames fns) fns items ws t

theorem checkW_sound {fns : List FnTags} {items : List Item} {ws : List (Array (List Int))}
    {t : Tables} (h : checkW fns items ws t = true) :
    (∀ p ∈ fns.zip ws, liveOk (bodyOf p.1 items) p.2 = true) ∧
      computeW fns items ws = .ok t ∧ t.g1Ok = true ∧ t.tailsIn (fnNames fns) = true :=
  checkWWith_sound h

/-- With scc's witnesses, `computeW` is `compute`. -/
theorem computeW_witness (fns : List FnTags) (items : List Item) :
    computeW fns items (witness fns items) = compute fns items := by
  have hz : ∀ l : List FnTags, (l.zip (l.map fun t => liveSlots (bodyOf t items))).mapM
      (fun (p : FnTags × Array (List Int)) => fnMapsW p.1 items p.2) =
      l.mapM fun t => fnMaps t items := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons, ih]; rfl
  simp only [computeW, compute, witness, List.length_map, beq_self_eq_true]
  simp only [hz]
  rfl

/-! ## The least fixpoint from a ranked witness

`liveOk` says a witness `w` is a *post-fixpoint* of slot liveness, so it contains the reference
liveness (`liveSlots_le`), maybe with more. A **rank witness** `r` (one natural number per slot of
`w`, in the same order) shows the converse: every slot of `w` is *justified*, read or
address-taken at its instruction, or live at a successor at a smaller rank and not written by
the instruction. By induction on the rank every justified slot is in the iteration's `r + 1`-th
step, so with `maxRank r < fuelOf body` (the iteration's fuel) a post-fixpoint with a rank
witness is the least fixpoint, as sets per instruction. scc computes the ranks by
Bellman–Ford (`ranksOf`, untrusted); the kernel checks them linearly (`justified`). -/

/-- Whether `o` has a rank below `r` in a witness entry `os` with ranks `rs` (in order). -/
def lowerIn (o : Int) (r : Nat) : List Int → List Nat → Bool
  | o' :: os, r' :: rs => (o' == o && decide (r' < r)) || lowerIn o r os rs
  | _, _ => false

/-- `justified`'s loop: instruction `k` (of `n`, with the label indices `lix`) and the rest `is`,
with the witness entries and their ranks from `k` on (`ws`, `rs`; `wl`, `rl` the whole lists).
The entry of the next instruction is the head of the rest; any other one is looked up. -/
def justGo (taken : List Int) (lix : List (String × Nat)) (n : Nat) (wl : List (List Int))
    (rl : List (List Nat)) : List (Nat × Nat × Ins) → List (List Int) → List (List Nat) → Nat → Bool
  | [], [], [], _ => true
  | (_, _, i) :: is, wk :: ws, rk :: rs, k =>
    Nat.beq wk.length rk.length &&
    (wk.zip rk).all (fun (o, r) => taken.contains o || i.reads.contains o ||
      (!i.writes.contains o && (succIdx lix n k i).any fun j =>
        if j == k + 1 then lowerIn o r (ws.headD []) (rs.headD [])
        else lowerIn o r (wl.getD j []) (rl.getD j []))) &&
    justGo taken lix n wl rl is ws rs (k + 1)
  | _, _, _, _ => false

/-- **Every slot of `w` is justified at its rank in `r`** on `body`: `r` has one entry per
instruction, as long as `w`'s, and each slot `o` of `w`'s entry `k`, at rank `x`, is
address-taken in the body, or read by instruction `k`, or not written by it and in the entry of
one of its successors (`succIdx`, `liveSlots`' successors) at a rank below `x`. Recursive over the
instructions and the lists together, as `liveOk`. -/
def justified (body : List Item) (w : Array (List Int)) (r : List (List Nat)) : Bool :=
  let is := (insOf body).toList
  let taken := is.foldl (fun acc (_, _, i) => unionI acc i.takes) []
  justGo taken (labelIdx body) is.length w.toList r is w.toList r 0

/-- **`liveSlots`' fuel** on `body`: its iteration's bound,
`(instructions + 1) * (slots + 1)`. -/
def fuelOf (body : List Item) : Nat :=
  let is := insOf body
  let slotsN := is.toList.foldl (fun acc (_, _, i) => unionI acc (i.reads ++ i.writes ++ i.takes)) []
  (is.size + 1) * (slotsN.length + 1)

/-- The largest rank of a rank witness (0 if none). -/
def maxRank (r : List (List Nat)) : Nat := r.foldl (fun m l => l.foldl max m) 0

/-- **The least-fixpoint check** of one function's witness `w` with ranks `r` on `body`: a
post-fixpoint (`liveOk`), every slot justified (`justified`), the ranks below the fuel. -/
def leastOk (body : List Item) (w : Array (List Int)) (r : List (List Nat)) : Bool :=
  liveOk body w && justified body w r && decide (maxRank r < fuelOf body)

/-- **The ranks scc emits** for the witness `w` on `body` (untrusted; `justified` checks them):
0 for a slot read or address-taken at its instruction, else one more than the least rank of the
slot at a successor that does not write it, by Bellman–Ford from the reads; a slot without a
justification keeps a rank above `fuelOf body`, which `leastOk` refuses. -/
def ranksOf (body : List Item) (w : Array (List Int)) : List (List Nat) :=
  let is := insOf body
  let n := is.size
  let lix := labelIdx body
  let taken := is.toList.foldl (fun acc (_, _, i) => unionI acc i.takes) []
  let inf := fuelOf body + 1
  let init : Array (List Nat) := (Array.range n).map fun k =>
    let i := (is[k]!).2.2
    (w[k]!).map fun o => if taken.contains o || i.reads.contains o then 0 else inf
  let step (rk : Array (List Nat)) : Array (List Nat) := (Array.range n).map fun k =>
    let i := (is[k]!).2.2
    ((w[k]!).zip (rk[k]!)).map fun (o, x) =>
      if i.writes.contains o then x else
      (succIdx lix n k i).foldl (fun m j =>
        match ((w[j]!).zip (rk[j]!)).find? (·.1 == o) with
        | some (_, x') => min m (x' + 1)
        | none => m) x
  let rec go : Nat → Array (List Nat) → Array (List Nat)
    | 0, m => m
    | f + 1, m => let m' := step m; if m' == m then m else go f m'
  (go (fuelOf body) init).toList

/-- **The witnesses with ranks scc emits**: per function, the reference liveness and its
ranks. -/
def witnessR (fns : List FnTags) (items : List Item) : List (Array (List Int) × List (List Nat)) :=
  fns.map fun t => let b := bodyOf t items; let w := liveSlots b; (w, ranksOf b w)

/-- **A GC-table witness of a program**: per IR function, in `p.funcs` order (the order of the
front ends' tags), its liveness witness and the witness's ranks (`witnessR`'s shape). -/
abbrev GcWit := List (Array (List Int) × List (List Nat))

/-- **The tables from a ranked witness** `gw` (one per function of `fns`, in order): every
function's witness is the least fixpoint on its body (`leastOk`), then the tables are
`computeW`'s from the witnesses. An error naming the first function whose witness fails, or if
`gw` has not one entry per function. -/
def computeWR (fns : List FnTags) (items : List Item) (gw : GcWit) : Except String Tables := do
  unless gw.length == fns.length do
    throw s!"gc tables: {gw.length} ranked witnesses for {fns.length} functions"
  match (fns.zip gw).zipIdx.find? (fun ((t, (w, r)), _) => !leastOk (bodyOf t items) w r) with
  | some ((t, _), k) =>
    throw s!"gc tables: the witness of function {k} ({(t.paramPts.head?).getD "?"}) is no least fixpoint"
  | none => computeW fns items (gw.map (·.1))

/-- With every witness the least fixpoint, `computeWR` is `computeW` on the witnesses. -/
theorem computeWR_eq {fns : List FnTags} {items : List Item} {gw : GcWit}
    (hl : gw.length = fns.length)
    (h : ∀ p ∈ fns.zip gw, leastOk (bodyOf p.1 items) p.2.1 p.2.2 = true) :
    computeWR fns items gw = computeW fns items (gw.map (·.1)) := by
  have hf : (fns.zip gw).zipIdx.find? (fun ((t, (w, r)), _) => !leastOk (bodyOf t items) w r) =
      none := by
    rw [List.find?_eq_none]
    intro x hx
    obtain ⟨⟨t, w, r⟩, k⟩ := x
    have := h (t, w, r) (List.fst_mem_of_mem_zipIdx hx)
    simp [this]
  simp only [computeWR, hl, beq_self_eq_true, hf]
  rfl

/-! ### `computeWR` in stages

A certificate checks `computeWR` in pieces, each its own kernel check on literals: each
function's least-fixpoint check (`leastFrom_cons`), the stubs, each function's maps and exit
successors (chained by `mapM`), and the sort (`computeW_of_stages`, `computeWR_of_least`). -/

/-- Every function's ranked witness is its least fixpoint (`leastOk`), the lists of one length. -/
def leastFrom (items : List Item) : List FnTags → GcWit → Bool
  | [], [] => true
  | t :: ts, (w, r) :: gs => leastOk (bodyOf t items) w r && leastFrom items ts gs
  | _, _ => false

theorem leastFrom_cons {items : List Item} {t : FnTags} {ts : List FnTags} {w : Array (List Int)}
    {r : List (List Nat)} {gs : GcWit} (h : leastOk (bodyOf t items) w r = true)
    (h' : leastFrom items ts gs = true) : leastFrom items (t :: ts) ((w, r) :: gs) = true := by
  simp only [leastFrom, h, h', Bool.and_self]

theorem leastFrom_spec {items : List Item} : ∀ {fns : List FnTags} {gw : GcWit},
    leastFrom items fns gw = true →
      gw.length = fns.length ∧ ∀ p ∈ fns.zip gw, leastOk (bodyOf p.1 items) p.2.1 p.2.2 = true
  | [], [], _ => ⟨rfl, by simp⟩
  | t :: ts, (w, r) :: gs, h => by
    simp only [leastFrom, Bool.and_eq_true] at h
    obtain ⟨hl, hr⟩ := leastFrom_spec h.2
    refine ⟨by simp [hl], ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact hr p hp
  | [], _ :: _, h => by simp [leastFrom] at h
  | _ :: _, [], h => by simp [leastFrom] at h

/-- **`computeWR` from the least-fixpoint checks and `computeW`.** -/
theorem computeWR_of_least {fns : List FnTags} {items : List Item} {gw : GcWit} {t : Tables}
    (h : leastFrom items fns gw = true) (hw : computeW fns items (gw.map (·.1)) = .ok t) :
    computeWR fns items gw = .ok t := by
  obtain ⟨hl, hall⟩ := leastFrom_spec h
  rw [computeWR_eq hl hall, hw]

/-- **`computeW` from its stages**: the stubs, the witnesses' count, each function's maps (`ms`)
and exit successors (`os`); the tables are the sort of them. -/
theorem computeW_of_stages {fns : List FnTags} {items : List Item} {ws : List (Array (List Int))}
    {ms : List (List RootMap)} {os : List (List Succs)}
    (hs : stubsOk fns items = .ok ()) (hl : ws.length = fns.length)
    (hm : (fns.zip ws).mapM (fun (t, w) => fnMapsW t items w) = .ok ms)
    (ho : (fns.zip ms).mapM (fun (p : FnTags × List RootMap) =>
      outSuccs p.1 items (p.2.map fun (m : RootMap) => m.pt.addr)) = .ok os) :
    computeW fns items ws = .ok
      { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) ms.flatten,
        succs := sortStable (fun a b => decide (a.addr ≤ b.addr))
          (fns.flatMap (fun t => fnSuccs t items) ++ os.flatten) } := by
  simp only [computeW, hs, hl, beq_self_eq_true, hm, bind, Except.bind, pure, Except.pure,
    ite_true]
  rw [ho]

/-- **`computeW` from its stages, the block successors staged too** (`fs`, each function's
`fnSuccs`): `computeW_of_stages` with the successors of the functions' blocks given, so that a
certificate checks them one function at a time. -/
theorem computeW_of_stagesF {fns : List FnTags} {items : List Item} {ws : List (Array (List Int))}
    {ms : List (List RootMap)} {os : List (List Succs)} {fs : List Succs}
    (hs : stubsOk fns items = .ok ()) (hl : ws.length = fns.length)
    (hm : (fns.zip ws).mapM (fun (t, w) => fnMapsW t items w) = .ok ms)
    (ho : (fns.zip ms).mapM (fun (p : FnTags × List RootMap) =>
      outSuccs p.1 items (p.2.map fun (m : RootMap) => m.pt.addr)) = .ok os)
    (hf : fns.flatMap (fun t => fnSuccs t items) = fs) :
    computeW fns items ws = .ok
      { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) ms.flatten,
        succs := sortStable (fun a b => decide (a.addr ≤ b.addr)) (fs ++ os.flatten) } := by
  rw [← hf]
  exact computeW_of_stages hs hl hm ho

theorem mem_unionI {x : Int} : ∀ {a b : List Int}, x ∈ unionI a b ↔ x ∈ a ∨ x ∈ b := by
  intro a b
  induction b generalizing a with
  | nil => simp [unionI]
  | cons y ys ih =>
    have h : unionI a (y :: ys) = unionI (if a.contains y then a else a ++ [y]) ys := rfl
    rw [h, ih]
    by_cases hy : a.contains y
    · simp only [hy, ite_true]
      simp only [List.contains_iff_mem] at hy
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl hy
          · exact Or.inr h
    · simp only [hy]
      simp [List.mem_append, List.mem_cons, or_assoc]

theorem mem_foldl_unionI {x : Int} {α : Type} (g : α → List Int) :
    ∀ (l : List α) (acc : List Int),
      x ∈ l.foldl (fun acc j => unionI acc (g j)) acc ↔ x ∈ acc ∨ ∃ j ∈ l, x ∈ g j := by
  intro l
  induction l with
  | nil => simp
  | cons y ys ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih, mem_unionI]
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

theorem subI_iff {a b : List Int} : subI a b = true ↔ ∀ x ∈ a, x ∈ b := by
  simp [subI]

/-- An invariant of every iterate is an invariant of `liveSlots.go`'s result. -/
theorem liveSlots_go_inv (P : Array (List Int) → Prop) (step : Array (List Int) → Array (List Int))
    (hs : ∀ m, P m → P (step m)) : ∀ f m, P m → P (liveSlots.go step f m) := by
  intro f
  induction f with
  | zero => intro m h; simpa [liveSlots.go] using h
  | succ f ih =>
    intro m h
    simp only [liveSlots.go]
    split
    · exact h
    · exact ih _ (hs _ h)

theorem getElem!_none {a : Array (List Int)} {k : Nat} (h : ¬ k < a.size) : a[k]! = [] := by
  simp [h]; rfl

theorem headD_drop {α : Type} (d : α) : ∀ (l : List α) (n : Nat), (l.drop n).headD d = l.getD n d
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | _ :: l, n + 1 => by simp only [List.drop_succ_cons, List.getD_cons_succ]; exact headD_drop d l n

theorem liveOkGo_spec (taken : List Int) (lix : List (String × Nat)) (n : Nat) (wl : List (List Int)) :
    ∀ (is : List (Nat × Nat × Ins)) (ws : List (List Int)) (k : Nat), ws = wl.drop k →
      liveOkGo taken lix n wl is ws k = true →
      ws.length = is.length ∧ ∀ m (hm : m < is.length),
        subI taken (wl.getD (k + m) []) = true ∧ subI (is[m].2.2.reads) (wl.getD (k + m) []) = true ∧
        ∀ j ∈ succIdx lix n (k + m) is[m].2.2,
          subI ((wl.getD j []).filter fun o => !is[m].2.2.writes.contains o) (wl.getD (k + m) []) = true
  | [], [], _, _, _ => ⟨rfl, fun m hm => absurd hm (Nat.not_lt_zero _)⟩
  | [], _ :: _, _, _, h => by simp [liveOkGo] at h
  | _ :: _, [], _, _, h => by simp [liveOkGo] at h
  | (a, z, i) :: is, wk :: ws, k, hws, h => by
    have hwk : wk = wl.getD k [] := by
      have := congrArg (fun l => l.headD []) hws
      simpa [headD_drop] using this
    have hws' : ws = wl.drop (k + 1) := by
      have := congrArg List.tail hws
      simpa [List.tail_drop] using this
    simp only [liveOkGo, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨⟨ht, hr⟩, hs⟩, hg⟩ := h
    obtain ⟨hlen, hall⟩ := liveOkGo_spec taken lix n wl is ws (k + 1) hws' hg
    refine ⟨by simp [hlen], ?_⟩
    intro m hm
    cases m with
    | zero =>
      subst hwk
      refine ⟨by simpa using ht, by simpa using hr, ?_⟩
      intro j hj
      have := hs j (by simpa using hj)
      by_cases hjk : j = k + 1
      · subst hjk
        simpa [hws', headD_drop] using this
      · simpa [hjk] using this
    | succ m =>
      have := hall m (by simpa using hm)
      simpa [Nat.add_assoc, Nat.add_comm 1 m] using this

theorem getElem!_eq_getD_toList (w : Array (List Int)) (k : Nat) : w[k]! = w.toList.getD k [] := by
  by_cases h : k < w.size
  · rw [getElem!_pos w k h]; simp [List.getD_eq_getElem?_getD, h]
  · rw [getElem!_none h]
    have : w.toList[k]? = none := by simp; omega
    simp [List.getD_eq_getElem?_getD, this]

/-- **What `liveOk` checks**, indexed: one witness entry per instruction, and before each
instruction `k` the address-taken slots, the slots `k` reads, and the slots live before each
successor of `k` that `k` does not write. -/
theorem liveOk_spec {body : List Item} {w : Array (List Int)} (h : liveOk body w = true) :
    w.size = (insOf body).size ∧ ∀ k (hk : k < (insOf body).size),
      subI ((insOf body).toList.foldl (fun acc (_, _, i) => unionI acc i.takes) []) w[k]! = true ∧
      subI ((insOf body)[k].2.2.reads) w[k]! = true ∧
      ∀ j ∈ succIdx (labelIdx body) (insOf body).size k (insOf body)[k].2.2,
        subI ((w[j]!).filter fun o => !(insOf body)[k].2.2.writes.contains o) w[k]! = true := by
  obtain ⟨hlen, hall⟩ := liveOkGo_spec _ _ _ w.toList _ _ 0 (by simp) h
  refine ⟨by simpa using hlen, ?_⟩
  intro k hk
  have := hall k (by simpa using hk)
  simp only [Nat.zero_add, Array.length_toList, Array.getElem_toList] at this
  simp only [getElem!_eq_getD_toList]
  exact this

/-- **The reference liveness is below every post-fixpoint**: if `liveOk body w`, every slot
`liveSlots body` lists before instruction `k` is in `w[k]`. Each iterate of `liveSlots`, from the
empty array, stays below `w`, because `w` is closed under the step; this holds whether or not the
iteration converged. So the maps `fnMapsW` builds from a checked witness list every slot the
reference maps list. -/
theorem liveSlots_le {body : List Item} {w : Array (List Int)} (h : liveOk body w = true) :
    ∀ (k : Nat) (x : Int), x ∈ (liveSlots body)[k]! → x ∈ w[k]! := by
  obtain ⟨_, hk⟩ := liveOk_spec h
  unfold liveSlots
  apply liveSlots_go_inv (fun (m : Array (List Int)) => ∀ (k : Nat) (x : Int), x ∈ m[k]! → x ∈ w[k]!)
  · intro m hm k x hx
    by_cases hkn : k < (insOf body).size
    · have hx' := hx
      rw [getElem!_pos _ _ (by simpa using hkn)] at hx'
      simp only [Array.getElem_map, Array.getElem_range] at hx'
      obtain ⟨ht, hr, hsu⟩ := hk k hkn
      rw [getElem!_pos (insOf body) k hkn] at hx'
      rw [subI_iff] at ht hr
      rcases mem_unionI.mp hx' with h1 | h1
      · rcases mem_unionI.mp h1 with h2 | h2
        · exact ht x h2
        · exact hr x h2
      · rw [List.mem_filter] at h1
        obtain ⟨h1, hw⟩ := h1
        rcases (mem_foldl_unionI _ _ _).mp h1 with h3 | ⟨j, hj, h3⟩
        · simp at h3
        · have := hsu j hj
          rw [subI_iff] at this
          exact this x (List.mem_filter.mpr ⟨hm j x h3, hw⟩)
    · rw [getElem!_none (by simpa using hkn)] at hx
      simp at hx
  · intro k x hx
    by_cases hkn : k < (Array.replicate (insOf body).size ([] : List Int)).size
    · rw [getElem!_pos (Array.replicate (insOf body).size ([] : List Int)) k hkn] at hx
      simp at hx
    · rw [getElem!_none hkn] at hx
      simp at hx

/-! ## Tests -/

/-- A toy function `f`: a prologue (`f`, `f.go`), a body that stores a heap slot, branches,
calls `g` on one arm, reads the slot after the call and returns (one instruction after the join
`f.b`, so the `ret` is no block entry, as in scc's epilogues), and a stub `f.stk`. -/
def toyItems : List Item :=
  [.label 0 "f", .ins 0 4 { flow := .jcc "f.stk" }, .label 4 "f.go", .ins 4 4 {},
   .label 8 "f.entry", .ins 8 4 { writes := [-8] }, .ins 12 4 { flow := .jcc "f.b" },
   .ins 16 4 { flow := .call "g" }, .ins 20 4 { reads := [-8] },
   .label 24 "f.b", .ins 24 4 {}, .ins 28 4 { flow := .ret }, .label 32 "f.stk",
   .ins 32 4 { flow := .jmp "f.go" }]

def toyTags : FnTags :=
  { paramPts := ["f", "f.go"], bodyStart := "f.entry", bodyEnd := some "f.stk",
    params := [(.reg 7, .heap)], result := [(.reg 0, .heap)], slots := [(-8, .heap)],
    callRes := [[(.reg 0, .heap)]],
    stackmap := [(20, [], [-8])] }

/-- info: [0, 2, 3, 4] -/
#guard_msgs in
#eval leaders (bodyOf toyTags toyItems)

-- `sortStable` keeps the order of equal keys, as `List.mergeSort` does.
#guard sortStable (fun a b => decide (a.1 ≤ b.1)) [(3, 0), (1, 0), (3, 1), (2, 0), (1, 1), (0, 0)] ==
  [(3, 0), (1, 0), (3, 1), (2, 0), (1, 1), (0, 0)].mergeSort (fun a b => decide (a.1 ≤ b.1))
#guard sortStable (fun a b => decide (a.1 ≤ b.1)) [(3, 0), (1, 0), (3, 1), (2, 0), (1, 1), (0, 0)] ==
  [(0, 0), (1, 0), (1, 1), (2, 0), (3, 0), (3, 1)]

/-- Lines and patterns of the front ends, and corner cases (empty, overlapping, repeated, at the
ends, not ASCII). -/
def textSamples : List String :=
  [".type f, %function", ".type wc_main, @function", ".size f, .-f", "\t.quad a, 1, 2", ".quad 3",
   ".quad -16", ".data", ".bss", ".section .rodata", ".section", ".text", ".p2align 4", ".p2align",
   ".globl _start", ".arch armv8.4-a", "x(%rbp)", "((%rbp", "(%rb(%rbp", "-8(%rbp,%rax,8)",
   "ldr x9, [sp, x16]", "str x0, [sp]", "[s[sp", "a,,b", "", ",", ", ", "ab", "aab", "abab", "aaa",
   "12", "1_000", "_1", "1_", "1__0", "-5", "--5", "-", "+5", "0x1f", "é,é", ".Lgw3", ".Lgc", "%function"]

def textPats : List String :=
  [", ", ",", " ", ".quad ", "(%rbp", "[sp", ".section", ".p2align ", ".type ", ".globl ", ".arch ",
   ".Lgw", "ab", "aa", "a", "", "é", "-"]

#guard textSamples.all fun s => textPats.all fun p =>
  startsK s p == s.startsWith p && splitK s p == s.splitOn p &&
    (p.isEmpty || containsK s p == decide ((s.splitOn p).length > 1))
#guard textSamples.all fun s => toNatK? s == s.toNat? && toIntK? s == s.toInt?

-- The kernel evaluates the text tests.
example : splitK ".type f, %function" ", " = [".type f", "%function"] ∧ startsK ".section x" ".section" ∧
    containsK "-8(%rbp)" "(%rbp" ∧ toIntK? "-16" = some (-16) ∧ toNatK? "1_0" = some 10 := by
  decide +kernel

-- The kernel evaluates the leaders (structural sort, no well-founded recursion).
example : leaders (bodyOf toyTags toyItems) = [0, 2, 3, 4] := by decide +kernel

/-- `(kind, address, roots)` of the computed maps. -/
def toyMaps : List (Kind × Nat × List (Loc × Tag)) :=
  match compute [toyTags] toyItems with
  | .ok t => t.maps.map fun m => (m.pt.kind, m.pt.addr, m.roots)
  | .error _ => []

-- The slot is dead at the body start (written first), live from the store to the read after
-- the call (at the call's map, keyed at its return address 20, through `scc_stackmap`), and
-- dead at `ret`; the call's map and the block entry at the return address add the call's
-- result register (the caller's tag of its destination), and no argument register.
#guard toyMaps ==
  [(.blockEntry, 0, [(.reg 7, .heap)]), (.blockEntry, 4, [(.reg 7, .heap)]),
   (.blockEntry, 8, []), (.blockEntry, 16, [(.slot (-8), .heap)]),
   (.call, 20, [(.slot (-8), .heap), (.reg 0, .heap)]),
   (.blockEntry, 20, [(.reg 0, .heap), (.slot (-8), .heap)]),
   (.blockEntry, 24, []), (.ret, 28, [(.reg 0, .heap)])]
-- The frame state: the function's entry `f` (the first of `paramPts`) and the `ret` are
-- frameless, every other map is not.
#guard (match compute [toyTags] toyItems with
  | .ok t => t.maps.map (·.frameless) | .error _ => []) ==
  [true, false, false, false, false, false, false, true]
#guard (match compute [toyTags] toyItems with
  | .ok t => t.succs.map (fun s => (s.addr, s.next))
  | .error _ => []) == [(0, [4]), (4, [8]), (8, [24, 16]), (16, [20]), (20, [24]), (24, [28])]
#guard (match compute [toyTags] toyItems with | .ok t => check [toyTags] toyItems t | .error _ => false)
-- The kernel evaluates the tables.
example : (match compute [toyTags] toyItems with
  | .ok t => t.succs.map (fun s => (s.addr, s.next))
  | .error _ => []) = [(0, [4]), (4, [8]), (8, [24, 16]), (16, [20]), (20, [24]), (24, [28])] := by
  decide +kernel

/-- A body with a `jcc; jmp` terminator, an instruction after the `jmp` and one after a `ret`,
neither a branch target. -/
def toyJItems : List Item :=
  [.label 0 "e", .ins 0 4 { flow := .jcc "b" }, .ins 4 4 { flow := .jmp "c" }, .ins 8 4 {},
   .label 12 "b", .ins 12 4 { flow := .ret }, .label 16 "c", .ins 16 4 { flow := .ret },
   .ins 20 4 {}]

def toyJTags : FnTags :=
  { paramPts := [], bodyStart := "e", bodyEnd := none, params := [], result := [], slots := [] }

-- One terminator: no leader at the `jmp`, none after it or after the `ret`; the block's
-- successors are both targets.
#guard leaders (bodyOf toyJTags toyJItems) == [0, 3, 4]
#guard (match compute [toyJTags] toyJItems with
  | .ok t => t.succs.map (fun s => (s.addr, s.next))
  | .error _ => []) == [(0, [12, 16]), (12, [12]), (16, [16])]
example : leaders (bodyOf toyJTags toyJItems) = [0, 3, 4] := by decide +kernel
-- A `jmp` that is a branch target is a leader of its own, entered from the `jcc`.
#guard (let its := toyJItems.take 2 ++ [.label 4 "j"] ++ (toyJItems.drop 2).take 6 ++
    [.ins 20 4 { flow := .jmp "j" }]
  leaders (bodyOf toyJTags its) == [0, 1, 3, 4] &&
  (match compute [toyJTags] its with
    | .ok t => t.succs.map (fun s => (s.addr, s.next))
    | .error _ => []) == [(0, [12, 4]), (4, [16]), (12, [12]), (16, [16])])
-- A tail jump out of the body (`jmp t`) is succeeded by its target `t`, by name, whatever `t`
-- is; the checker refuses it unless `t` is one of the functions' names (`fnNames`: the tagged
-- functions' entries; here only `e`). (The entry `e` is the body's start here, so it has two
-- successor entries: the prologue's and the body's.)
#guard (let its := toyJItems.take 5 ++ [.ins 12 4 { flow := .jmp "t" }] ++ toyJItems.drop 6
  let e : FnTags := { toyJTags with paramPts := ["e"] }
  let sc (r : Except String Tables) : List (Nat × List Nat × List String) := match r with
    | .ok r => r.succs.map (fun (s : Succs) => (s.addr, s.next, s.tail)) | .error _ => []
  sc (compute [e] its) == [(0, [12, 16], []), (0, [12, 16], []), (12, [], ["t"]), (16, [16], [])] &&
  (match compute [e] its with | .ok t => !check [e] its t | .error _ => false))
-- The `jmp` of a `jcc; jmp` terminator out of the body (`jcc b; jmp t`) is a tail jump too: the
-- block is succeeded by the branch target and by `t`, by name; the checkers refuse it unless `t`
-- is one of the names, and accept it when it is.
/-- A body whose `jcc; jmp` terminator's `jmp` leaves it (to `t`); the `ret` one instruction
after the join `b`, so its map does not share the block entry's address. -/
def toyPairItems : List Item :=
  [.label 0 "e", .ins 0 4 { flow := .jcc "b" }, .ins 4 4 { flow := .jmp "t" }, .label 8 "b",
   .ins 8 4 {}, .ins 12 4 { flow := .ret }]

/-- info: [(0, [8], ["t"]), (8, [12], [])] -/
#guard_msgs in
#eval (fnSuccs toyJTags toyPairItems).map fun (s : Succs) => (s.addr, s.next, s.tail)
-- (`toyJTags` has no function names: `fnNames` is empty.)
#guard (match compute [toyJTags] toyPairItems with
  | .ok t => !check [toyJTags] toyPairItems t &&
      !checkW [toyJTags] toyPairItems (witness [toyJTags] toyPairItems) t &&
      !checkWWith ["u"] [toyJTags] toyPairItems (witness [toyJTags] toyPairItems) t &&
      checkWWith ["t"] [toyJTags] toyPairItems (witness [toyJTags] toyPairItems) t
  | .error _ => false)
-- The `jcc` of a `jcc; jmp` terminator out of the body to no stub fails the computation.
#guard (compute [toyJTags] (toyJItems.modify 1 fun _ => .ins 0 4 { flow := .jcc "nowhere" })).toOption.isNone
#guard (computeW [toyJTags] (toyJItems.modify 1 fun _ => .ins 0 4 { flow := .jcc "nowhere" })
  [liveSlots (bodyOf toyJTags toyJItems)]).toOption.isNone
-- The call maps are the `scc_stackmap` entries both ways.
#guard (compute [{ toyTags with stackmap := [] }] toyItems).toOption.isNone
#guard (compute [{ toyTags with stackmap := [(20, [], [-8]), (28, [], [])] }] toyItems).toOption.isNone

/-- The toy with a grow stub: `f.stk` calls the trampoline `more`, whose `scc_stackmap` entry
(return address 36) lists the save word `-16` of the heap parameter. -/
def toyGrowItems : List Item :=
  toyItems.take 12 ++ [.label 32 "f.stk", .ins 32 4 { flow := .call "more" },
    .ins 36 4 { flow := .jmp "f.go" }]

def toyGrowTags : FnTags :=
  { toyTags with growStub := some "f.stk", stackmap := [(20, [], [-8]), (36, [], [-16])] }

-- One more map, the grow call's at its return address 36 (no block-entry map there); one more
-- successor entry, from that return address back through the stub's jump to the prologue's
-- `f.go`; the prologue entry `f` now reaches the grow call's return address as well.
#guard (match compute [toyGrowTags] toyGrowItems with
  | .ok t => (t.maps.map fun m => (m.pt.kind, m.pt.addr, m.roots)) == toyMaps ++
      [(.call, 36, [(.slot (-16), .heap)])] && check [toyGrowTags] toyGrowItems t &&
    (t.succs.map fun s => (s.addr, s.next)) ==
      [(0, [36, 4]), (4, [8]), (8, [24, 16]), (16, [20]), (20, [24]), (24, [28]), (36, [4])]
  | .error _ => false)
-- Without the grow stub, its entry is no call's return address; without the entry, its call
-- has no map.
#guard (compute [{ toyGrowTags with growStub := none }] toyGrowItems).toOption.isNone
#guard (compute [{ toyGrowTags with stackmap := [(20, [], [-8])] }] toyGrowItems).toOption.isNone
#guard (compute [{ toyGrowTags with growStub := some "f.nope" }] toyGrowItems).toOption.isNone

/-- The toy with conditional branches out of the body to stubs: an abort stub `f.ovf` (x64's
shape: the kind, the abort call, `ud2`) and a child stub `f.child.w` (AArch64's: the moves, the
entry's call classified `.stop`, the halt loop). -/
def toyStubItems : List Item :=
  toyItems.take 9 ++ [.label 24 "f.b", .ins 24 4 { flow := .jcc "f.ovf" },
    .ins 28 4 { flow := .jcc "f.child.w" }, .ins 32 4 { flow := .ret }, .label 36 "f.stk",
    .ins 36 4 { flow := .jmp "f.go" },
    .label 40 "f.ovf", .ins 40 4 {}, .ins 44 4 { flow := .call "scc_rt_abort" },
    .ins 48 4 { flow := .stop },
    .label 52 "f.child.w", .ins 52 4 {}, .ins 56 4 {}, .ins 60 4 { flow := .stop },
    .label 64 "f.child.w_halt", .ins 64 4 { flow := .jmp "f.child.w_halt" }]

/-- `toyStubItems` with stub `f.ovf` (its label and three instructions) replaced by `r`. -/
def toyStubWith (r : List Item) : List Item := toyStubItems.take 15 ++ r ++ toyStubItems.drop 19

#guard (stubsOk [toyTags] toyStubItems).toOption.isSome
-- A branch out of the body has no successor of its own: from 24 and 28 only the fall-through.
/-- info: [(0, [4]), (4, [8]), (8, [24, 16]), (16, [20]), (20, [24]), (24, [28]), (28, [32]), (32, [32])] -/
#guard_msgs in
#eval (match compute [toyTags] toyStubItems with
  | .ok t => t.succs.map fun (s : Succs) => (s.addr, s.next)
  | .error _ => [])
-- Refused: an abort stub without its trap, one calling something else, a stub of other
-- instructions, a branch to a label the text does not have, a `.stop` stub not labelled as a
-- child; `computeW` refuses them too.
#guard [toyStubWith [.label 40 "f.ovf", .ins 40 4 {}, .ins 44 4 { flow := .call "scc_rt_abort" },
      .ins 48 4 {}],
    toyStubWith [.label 40 "f.ovf", .ins 40 4 {}, .ins 44 4 { flow := .call "g" },
      .ins 48 4 { flow := .stop }],
    toyStubWith [.label 40 "f.ovf", .ins 40 4 { flow := .jmp "f.go" }],
    toyStubItems.map (fun | .label a "f.ovf" => .label a "f.ovg" | it => it),
    toyStubItems.map (fun | .label a "f.child.w" => .label a "f.thr.w" | it => it)].all fun its =>
  (compute [toyTags] its).toOption.isNone &&
    (computeW [toyTags] its [liveSlots (bodyOf toyTags its)]).toOption.isNone
-- The kernel evaluates the stub check.
example : (stubsOk [toyTags] toyStubItems).toOption.isSome = true := by decide +kernel

-- The checker with a witness: scc's witness is a post-fixpoint, and its tables are `compute`'s.
/-- info: #[[], [-8], [-8], [-8], [], []] -/
#guard_msgs in
#eval liveSlots (bodyOf toyTags toyItems)
#guard liveOk (bodyOf toyTags toyItems) (liveSlots (bodyOf toyTags toyItems))
#guard (match compute [toyTags] toyItems with
  | .ok t => checkW [toyTags] toyItems (witness [toyTags] toyItems) t | .error _ => false)
#guard (match compute [toyGrowTags] toyGrowItems with
  | .ok t => checkW [toyGrowTags] toyGrowItems (witness [toyGrowTags] toyGrowItems) t
  | .error _ => false)
-- A witness with a live slot dropped (before the read after the call) is refused, and so is
-- the table built from it.
#guard !liveOk (bodyOf toyTags toyItems) #[[], [-8], [-8], [], [], []]
#guard (match compute [toyTags] toyItems with
  | .ok t => !checkW [toyTags] toyItems [#[[], [-8], [-8], [], [], []]] t | .error _ => false)
#guard (match computeW [toyTags] toyItems [#[[], [-8], [-8], [], [], []]] with
  | .ok t => !checkW [toyTags] toyItems [#[[], [-8], [-8], [], [], []]] t | .error _ => false)
-- So is a witness of the wrong length, and a missing one.
#guard !liveOk (bodyOf toyTags toyItems) #[[], [-8], [-8], [-8], []]
#guard (computeW [toyTags] toyItems []).toOption.isNone
-- An over-approximating witness passes `liveOk`; its maps list the extra slot, so they differ
-- from `compute`'s (scc rejects that, the certificate does not).
#guard liveOk (bodyOf toyTags toyItems) #[[-8], [-8], [-8], [-8], [-8], [-8]]
#guard (match computeW [toyTags] toyItems [#[[-8], [-8], [-8], [-8], [-8], [-8]]],
    compute [toyTags] toyItems with
  | .ok a, .ok b => a != b && checkW [toyTags] toyItems [#[[-8], [-8], [-8], [-8], [-8], [-8]]] a
  | _, _ => false)
-- The kernel evaluates the checker.
example : (match compute [toyTags] toyItems with
  | .ok t => checkW [toyTags] toyItems [#[[], [-8], [-8], [-8], [], []]] t | .error _ => false) = true := by
  decide +kernel

-- The least-fixpoint check: scc's witness with its ranks passes; the over-approximating one has
-- no ranks that justify its extra slots; a corrupted rank, a dropped rank and ranks at the fuel
-- are refused.
/-- info: [[], [2], [1], [0], [], []] -/
#guard_msgs in
#eval ranksOf (bodyOf toyTags toyItems) (liveSlots (bodyOf toyTags toyItems))
#guard leastOk (bodyOf toyTags toyItems) (liveSlots (bodyOf toyTags toyItems))
  (ranksOf (bodyOf toyTags toyItems) (liveSlots (bodyOf toyTags toyItems)))
#guard witnessR [toyTags] toyItems ==
  [(liveSlots (bodyOf toyTags toyItems), ranksOf (bodyOf toyTags toyItems) (liveSlots (bodyOf toyTags toyItems)))]
#guard !leastOk (bodyOf toyTags toyItems) #[[-8], [-8], [-8], [-8], [-8], [-8]]
  (ranksOf (bodyOf toyTags toyItems) #[[-8], [-8], [-8], [-8], [-8], [-8]])
#guard !justified (bodyOf toyTags toyItems) #[[], [-8], [-8], [-8], [], []] [[], [1], [1], [0], [], []]
#guard !justified (bodyOf toyTags toyItems) #[[], [-8], [-8], [-8], [], []] [[], [], [0], [0], [], []]
#guard !leastOk (bodyOf toyTags toyItems) #[[], [-8], [-8], [-8], [], []]
  [[], [fuelOf (bodyOf toyTags toyItems) + 1], [fuelOf (bodyOf toyTags toyItems)], [0], [], []]
example : leastOk (bodyOf toyTags toyItems) #[[], [-8], [-8], [-8], [], []] [[], [2], [1], [0], [], []] = true := by
  decide +kernel
-- The tables from scc's ranked witness are `compute`'s; a corrupted rank, a dropped witness slot
-- and a missing or extra witness are refused.
#guard (computeWR [toyTags] toyItems (witnessR [toyTags] toyItems)).toOption ==
  (compute [toyTags] toyItems).toOption
#guard (computeWR [toyTags] toyItems (witnessR [toyTags] toyItems)).toOption.isSome
#guard (computeWR [toyTags] toyItems [(#[[], [-8], [-8], [-8], [], []], [[], [1], [1], [0], [], []])]).toOption.isNone
#guard (computeWR [toyTags] toyItems [(#[[], [-8], [], [-8], [], []], [[], [2], [], [0], [], []])]).toOption.isNone
#guard (computeWR [toyTags] toyItems []).toOption.isNone
#guard (computeWR [toyTags] toyItems (witnessR [toyTags, toyTags] toyItems)).toOption.isNone

/-- info: 'Scc.Cert.Maps.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_sound
/-- info: 'Scc.Cert.Maps.liveSlots_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms liveSlots_le

end Scc.Cert.Maps
