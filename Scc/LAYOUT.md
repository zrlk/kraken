# scc object layout

scc lays objects out as WeakCore's GC design decides: the **bipartite,
bidirectional** layout. No collector is built:
`--gc none` stays a bump allocator. The layout is fixed now, before more
proofs depend on the old one. `Scc/Lower/Obj.lean` implements it,
`Scc/Lower/Term.lean` and `Scc/Lower/Runtime.lean` use it, and
`Scc/Test/LayoutTest.lean` tests it.

## 1. Regions per type: `reg T = (n, m)`

Every closed type `T` has `n` **scalar** words and `m` **trace** words.
Trace words are references, locative bases and `ThreadId`s; a moving
collector would rewrite them and nothing else. `Obj.regE` computes
`(n, m, ext)` in a single recursion, where `ext` counts the
target words a value has beyond WeakCore's model width `wc`
(`Ty.rawWords`). So `n + m = wc + ext`.

Types in the accepted fragment:

| type | `(n, m)` | `ext` | note |
|---|---|---|---|
| `Unit`, `Void` | (0, 0) | 0 | erased |
| `Int`, `Int[i]`, `U8`…`I64` (`fix`), `LanesU8`… (`lanes`) | (1, 0) | 0 | |
| `Ptr μ τ` | (0, 1) | 0 | an object's base |
| `ThreadId` (stubbed as `Ptr pub Void`) | (0, 1) | 0 | the TCB's address, in the pinned region (§7) |
| `Loc μ τ` | **(1, 1)** | 1 | base (trace) + offset word (scalar), §4 |
| `σ × τ` | `(n_σ + n_τ, m_σ + m_τ)` | `e_σ + e_τ` | concatenated region by region |
| `{τ \| ψ}`, `∃i. τ`, `∃α. τ`, `∀i. τ`, `μα. τ` | that of `τ` | | erased wrappers |
| `Array[k] τ` (behind a `Loc`) | no value width | | an array object: §3 |

`regE` also covers types outside the fragment (sums among them),
so the width law can be tested where it has content (`LayoutTest`, all
ten cases of the width law):

- `word`: (1, 0), or (0, 0) if ghost.
- `word2`, `epair`: (2, 0).
- `code`: (1, 0).
- `Ptr?`: (0, 1).
- niche sum: `(max n_arm, 1)`.
- wide sum: `(1 + max n_arm, max m_arm)`.
- boxed sum: (0, 1).
- tokens, shares, caps: (0, 0).

None of these is lowered.

**In registers, frames and arguments** a value is its words in the model's
order. Products are concatenated, and every locative is expanded to two
words, `(base, offset)`. `Obj.slots T s r` is the layout map `φ_T`. It sends
each word, in that order, to `(region, index)`, starting at scalar index `s`
and trace index `r`.

Example: `Int × Ptr × Loc` has value words `[int, ptr, loc.base, loc.off]`.
They map to scalar 0, trace 0, trace 1, scalar 1.

`φ_T` is applied only where a value meets memory (`Term.cellAddrs`). A
store writes the words in value order, so the model's unit order is kept,
which matters for release stores of multi-word values. A component's words
are contiguous within each region, so a sub-object is a pair of ranges.

## 2. Objects: bidirectional, one header word

An object at base `b`, with `M = len·m` trace words and `N = len·n` scalar
words (`len = 1` except for arrays):

```
headerBeforeTrace = false (default)         headerBeforeTrace = true
  b − 8(M+1) … b − 16: trace words            b − 8(M+1): header
  b − 8: header                               b − 8M … b − 8: trace words
  b … b + 8N − 8: scalar words                b … b + 8N − 8: scalar words
```

- Scalar word `i` is at `b + 8i`.
- Trace word `j` is at `b − traceBias − 8j`, where `traceBias` is 16
  (header at `b − 8`, the default) or 8 (header before the trace region).

The trace region grows down from the base. Then a locative's addresses
depend only on its own offset word, never on the enclosing object's `m`.
Both regions are prefix-stable.

Where the header sits is configured by
`ObjLayout.headerBeforeTrace` in `Scc/Config.lean`:

- `false` (the default, the chosen placement): the header is at `b − 8`, so
  a reference reaches it in one load. The heap is not linearly parsable
  (that is not required) and there is no allocation-time object-start
  bitmap: a moving, evacuating collector never walks the heap linearly; it
  reaches objects from references, and liveness comes from its mark bitmap.
- `true`: a linear walk from low addresses would parse the heap from headers
  alone. Kept as a switch; the emitted code is correct under either value.

**Header word** (`Obj.header0`, `Obj.decode`; field widths in
`ObjLayout`), from bit 0:

| field | bits | meaning |
|---|---|---|
| `kind` | 3 | 0 object (`new`), 1 array (`newBuf`), 2 box (reserved: sums are not in the fragment), 3 pinned runtime block (TCB) |
| `gc` | 5 | reserved for the collector; 0 under `gc none` |
| `n` | 14 | scalar words of the object, or of the element for an array |
| `m` | 14 | trace words of the object, or of the element |
| `len` | 28 | element count; 1 for a non-array object |

An object takes `1 + len·(n + m)` words, so the header alone gives its size
and its map. `n` and `m` are the element's regions *with* their alignment
gaps (`Obj.counts`, the 16-byte pair layout of §9), so the size covers every
gap; a gap in the trace region is a trace word no unit uses, born null in
the zero-filled arena and never stored, so a scan of the trace region reads
it as null. On the accepted fragment there are no gaps (`counts = regOf`);
the lowering refuses a type on which they differ until it places pairs
(`Lower.countsOf`). The map is `objMap = replicate n false ++ replicate m true` per element.
No fragment type comes near 14 bits: that would take a
product of 16 384 components. The lowering rejects such a type with a
message. A buffer of `2^28` or more elements takes the `heap` abort outcome
(and could not fit the 64 MiB arena anyway).

**Allocation** (`scc_rt_alloc(h, k)`, `Runtime.allocF`):

- `h` is the header with `len = 0`, an immediate for objects and arrays alike.
- `k` is the element count: 1 for `new`, the length for `newBuf`.
- The allocator bumps the cursor by `8·(1 + k·(n + m))`, writes
  `h | k << 36` (`Obj.lenShift`) at the header's place, and returns the base.
- The arena is zero-filled `.bss` that is never reused, so scalars start at
  0 and every trace slot starts null.

## 3. Arrays

A buffer of `k` elements of type `τ = (n, m)` is one object with header
`(array, n, m, k)`:

- slot `j`'s scalar words start at scalar index `j·n`;
- slot `j`'s trace words start at trace index `j·m`.

The `idx` result is a locative whose offset word advances by one
**stride** per slot (§4).

Element types in the fragment are one model word: `Int`, `fix`, `lanes`,
`Ptr`, `Loc`. A `Loc` element is (1, 1): two target words.

`Ptr` and `Loc` are not zeroable, so a buffer of them can only be filled
slot by slot with `bufInit`. `bufInit` (a plain store to slot `ini`) is in
the accepted fragment for that reason.

## 4. Locatives: `(base, offset)`

A locative is two words everywhere (registers, frames, arguments, own
cells): the object's **base** (a trace word) and an **offset word** (a
scalar). The offset word packs the pointee's start in both regions as byte
offsets from the base:

```
offset = scalarByteOffset + 2^32 · traceByteOffset        (Obj.offWord)
```

The scalar word `i` of the pointee is at `base + lo32(offset) + 8i`. Its trace
word `j` is at `base − hi32(offset) − traceBias − 8j`.

**Why not the model offset.** WeakCore's model offset (for
arrays, the slot index) cannot be dereferenced: a `Loc μ τ` type names only
the pointee, not the enclosing object. Take `Loc pub Int` produced by `fld`
into `Int × Ptr × Int` and into `Ptr × Int × Int`: the two have the same
type but different scalar indices for the same model offset, and locatives
are passed between functions. The packed pair is the "pair" answer to Q10.

- **Both cases.** The pair is used for array slots as well as product
  fields.
- **Not observable.** It is a scalar word whose encoding no program can
  observe, and the collector ignores it.

Arithmetic:

- `fld 1` of a cell `c₁ × c₂` adds the constant `stride(n_c₁, m_c₁)`, where
  `stride(n, m) = 8n + 2^32·8m`.
- `fld 0` keeps the offset.
- `b[i]` adds `i · stride(n_τ, m_τ)`: one multiply by a constant, then one
  add.
- A `Ptr` has offset 0.
- A constant offset folds into the instructions' displacements, the usual
  case for `fld` on a `Ptr`.
- A variable offset costs a 32-bit zero-extension and a shift before the
  access.

**Bit budget.** Each half is 32 bits, so the scalar and the trace part of an
object must each stay below 4 GiB. An object never exceeds the arena
(64 MiB by default). `Layout.heapBytes` must stay below `2^32`: the lowering
refuses a larger arena. A `newBuf` of a literal length whose region would
take `2^32` bytes or more is refused by the frontend; a dynamic length is
bounded by the allocator (`2^lenBits` elements) and by the arena.

**Derived addresses.** `base + lo32(offset)` and `base − hi32(offset)` are
computed right before the loads and stores that use them. They are never
live across a call (a safepoint). Frames, registers at safepoints and the
heap only ever hold bases: there are no interior pointers and
no base/derived pairs in the stack maps.

## 5. Frames and stack maps

Every IR register lives in a frame slot. The stack map of a safepoint lists
two kinds of live register:

- **stack registers**: these hold stack addresses and are rewritten when a
  stack grows;
- **heap registers**: these hold **trace words**. A trace word is a
  reference, a locative's base, or a `ThreadId`.

A locative's offset word and every scalar are in neither list. The heap
lists are exact: `Term.markWords` marks every word of every typed value from
`Obj.traceMask`, one for one (a mismatch is a lowering error), trace words
into `Func.heapRegs` and the other words into `Func.scalarRegs`; the runtime
marks its own registers that live across a call (TCB addresses as trace
words, the grow routine's stack addresses and sizes as scalars). So a
frame's map is `reg` of each live binding's type, in value order. `Scc/Test/MapTest.lean` checks this on `hello.w`, `handoff.w`,
`spill.w` and `layout.w`: no register is in both lists (every heap-list
entry holds a trace word of its type), and every register live across a
safepoint (a call, or the prologue check for live parameters) has a kind (no
trace word is missing from a heap list).

`StackMap.check` is unchanged and still rejects every escaping stack
address: stored to memory, passed to a system call, `clone` or a site,
returned, or passed in a tail call. Two-word locatives add no stack
addresses: their base is a heap or pinned address.

Arguments and results are flattened to words, at most `maxArgs` = 32
arguments and `maxRets` = 6 results. A locative takes two of them.
Arguments past the target's registers (x64 six, AArch64 eight) go on the
stack, in the caller's **outgoing area** at the bottom of its frame
(`IR.Core`'s calling convention): argument `k + j` at `[sp + 8j]` at the
call, `sp` 16-byte aligned, so at `16 + 8j` above the callee's frame record.

- **Which map lists spilled trace words: the callee's.** The callee copies
  its stack arguments into its own frame slots in the prologue, right after
  the stack check; from then on its call maps list those slots like any
  other register, and the outgoing words are dead (no map lists them). The
  one safepoint where they are live in place is the callee's prologue check:
  its map (`StackMap.checkMap`) lists live stack parameters at `16 + 8j`
  from the frame record (register parameters stay at their save-area
  words).
- **Growable stacks.** The incoming words lie above the callee's frame
  record and below the caller's slots, inside the copied `[fp, stackTop)`,
  so the move copies them raw and the frame-record walk never touches them;
  a listed stack address among them is rewritten through the check's map.
  `spill.w` grows the stack 20000 frames deep through a nine-word block
  whose stack parameters include locative bases.
- **Tail calls: argument areas.** Every `tail` is a jump, whatever its
  argument count, so a tail loop runs in constant stack. Functions joined by
  `tail` edges (in either direction) share one incoming argument area
  (`StackMap.argAreas`): its size is the most stack words any member takes as
  parameters or passes in a tail call. Every `call` of a member reserves that
  area as outgoing space (`StackMap.callWords`), and a tail call writes its
  stack arguments over the current function's own incoming area, which is
  always large enough. A function entered without a caller (`start`, a
  `clone` or `switchTo` target) must have area 0; both emitters reject a
  program otherwise. Calls to functions outside wide tail components are
  unchanged. `tailwide.w` runs a three-block tail loop (4, 9 and 12 words)
  a million times under the default stack cap; `MapTest.areaIssues` checks
  that every call reserves its callee's area and every tail call fits.
- **Spawn.** Spawn arguments still travel in the TCB, at most
  `maxSpawnArgs` = 6 words (the pinned region reserves that much per
  thread); a spawned block with more is rejected with a message.

`hello.w`'s `worker` block takes 6 words (a slice locative, its length, a
count, a `Ptr` and a `ThreadId`): the spawn limit, not the call limit.

## 6. Mixed units do not race (O3, provisional `regionHomog`)

A **mixed unit** is a single-copy-atomic unit with both a scalar and a
trace word. In the fragment the only mixed unit is a
**locative**. Outside the fragment there are also:

- niche sums with a `Loc` arm;
- wide sums with a reference arm;
- coupled packages that mix the two kinds.

`Obj.inlineMixed` recognises all of them.

The halves of a mixed unit live in different regions, so no single access
covers them. Such a unit may live in a frame, an argument or an own cell.
It must not sit inline in a shared cell type, where a racing reader could
pair the base of one write with the offset of another.

`Scc.Frontend.regionHomog` provisionally rejects every such type, with a
message naming it. It covers:

- `Ptr pub τ` / `Loc pub τ` / `Ptr? pub τ` whose pointee holds a mixed unit
  inline (behind a further reference is fine);
- shared buffers of locatives.

It runs on every signature and on the type of every binding in the
checker's context. It is to be removed when WeakCore's checker has its
`regionHomog` rule. No existing test hits it. `hello.w`'s slice is only a
frame and argument value.

**Two-word units in one region** (`word2`, `epair`, scalar-only wide sums,
coupled packages of two scalars or of two references) stay one 16-byte
single-copy-atomic access in their region, at an aligned granule (§9).
None is in the fragment, and neither emitter has a pair access yet: A64
`ldp`/`stp` are outside `WCLowerable`.

## 7. Runtime blocks: the pinned region and TCBs

- **Pinned region.** TCBs live in their own `.bss` region
  (`scc_rt_pinned`, with its own bump cursor), not in the object arena, so
  "pinned" is a property of the address. The region holds
  `maxThreads + 1` TCBs with the largest argument (`Runtime.pinnedBytes`),
  so the thread cap (`scc_rt_thread_reserve`) is reached first. Its
  exhaustion check is kept anyway (abort `threads`).
- **A TCB is an object of kind `pinned`** with the same header and layout
  as any object.
  - Its fields are its first scalar words: `self` 0, `stackLimit` 8,
    `permit` 16, `exited` 24, `stackBase` 32, `stackTop` 40, **`badMask` 48**
    `index` 56 and **`depth`** 64 (`Tcb.size` = 72).
  - `badMask` is reserved for the loaded-value barrier's bad-bit mask. It is
    0 under `gc none` and nothing reads it.
  - `depth` is unused: it was the thread's stack depth counter, now removed.
    The only stack abort is the grow routine's, when a frame does not fit
    under `stackCapBytes`; `Lower.stackBudget` gives the depth (`B.frames`)
    within which that never happens. The word is kept this release so that
    `Tcb.size` and the pinned block do not move, and goes with the next
    layout change. Nothing accesses it; it is 0 because the pinned region is
    zero-filled and never reused.
- **Spawn arguments.** A spawned thread's argument words follow the fields
  by region: scalars from byte 72, trace words as the TCB's trace region
  (`Term.tcbLayout`). The child's trampoline reads them back from there.
- **ThreadId.** It is the TCB's address, both `main`'s argument and
  `spawn`'s result. The model value `num i` is related to it by type. The thread index is stored in the TCB (`index`, 0 for main). A
  trace slot never holds a small integer.

## 8. Niche tags and metadata bits

Every object base is 8-aligned, which leaves the three low bits of a
reference for WeakCore's niche encoding (`tagSlots = 8`).
Sums are not in the fragment, so scc emits no tagged reference yet.

`gc none` uses no metadata bits. A collector's metadata bits must lie above
bit 2. Its loaded-value barrier must mask them and preserve the
niche bits. The header's 5 `gc` bits and the TCB's `badMask` are reserved
for it.

## 9. Alignment

- The arena and the pinned region are 16-aligned.
- Every allocation is a whole number of words, so every header, every base
  and every word is 8-aligned.
- **16-byte pairs** (`Obj.place`, `Obj.strideOf`, `Obj.allocGap`). A pair
  (WeakCore's `Acc.two`: `word2`, `epair`, a scalar wide sum, a coupled
  package of two words) is one single-copy-atomic 16-byte access, so both
  its words lie in one region and form one aligned granule. A **scalar
  pair** has two scalar words. A **trace pair** has two references (a
  coupled package of two pointers, allowed in shared cells). A
  pair with one word of each kind is a mixed unit (§6) and has no layout.
  - An object holding a pair has a 16-aligned base. The allocator skips one
    word when the cursor would misalign it: the base lies `8·(M + 1)` bytes
    above the object's start under either header placement, so the gap is
    `allocGap c M ∈ {0, 1}` words. The skipped word is never read and needs
    no header and no filler kind, because nothing walks the heap linearly
    (R-c is dropped, §2). The header does not record whether an object
    holds a pair, so an evacuating collector keeps every copied object's
    `base mod 16` (at most one skipped word per copy).
  - Within the object, `place` starts a scalar pair at an even scalar index
    (`base + 8i`) and a trace pair at a trace index `j` with
    `traceBias/8 + j + 1` even (its granule starts at
    `base − traceBias − 8(j + 1)`): odd `j` with the header at `base − 8`,
    even `j` with the header before the trace region. When the next index
    does not qualify, `place` leaves a one-word gap in that region.
  - An array element's regions are rounded up to an even number of words in
    each region holding a pair (`strideOf`), so every element repeats the
    first element's alignment.
  - Types without pairs get no gap: `place` agrees with `slots` on them, so
    the layout of the accepted fragment is unchanged.
  - Status: no pair type is in the fragment and neither emitter has a pair
    access (A64 `ldp`/`stp` are outside `WCLowerable`). The lowering still
    uses `slots`, and `Runtime.allocF` does not align yet. `place`,
    `strideOf` and `allocGap` fix the layout those will use;
    `Scc/Test/LayoutTest.lean` checks that every pair of a cell, of the
    first four array elements and of a fresh object is one aligned granule,
    under both header placements.

## 10. Open items and provisional choices

| item | provisional choice | where |
|---|---|---|
| Header encoding | one word: `kind 3 · gc 5 · n 14 · m 14 · len 28`; arrays carry the element's `(n, m)` and the length in the same word | `ObjLayout` field widths |
| Header placement | decided: between the regions at `b − 8` (`headerBeforeTrace = false`), no object-start bitmap, no parsable heap required (§2). `true` (header before the trace region) stays a one-line switch in `Scc/Config.lean`; the emitted-size guards in `Scc/Emit/X64Test.lean` carry both expectations (`byPlacement`). Checked under each value: `false` run.sh 40/40 on x64 and 40/40 on arm, diff.sh -n 300 300/300 on both; `true` run.sh 40/40 on x64 and 40/40 on arm, diff.sh -n 300 300/300 on both (and `lake build Scc` succeeds under both) | `ObjLayout.headerBeforeTrace` |
| Locative offset word | packed pair of 32-bit byte offsets (scalar low, trace high), for products and arrays alike: §4. Accepted. | `Obj.offWord`, `Obj.stride` |
| Metadata bits | none under `gc none`; low 3 bits are niche tags; 5 header bits and the TCB's `badMask` reserved | §8 |
| 16-byte alignment | decided layout, not emitted: a scalar pair at an even scalar index, a trace pair at a trace index whose granule is 16-aligned, one-word gaps where needed, element strides even per region, and a 16-aligned base via one skipped word without a header (§9) | `Obj.place`, `Obj.strideOf`, `Obj.allocGap` |
| Boxes | header kind 2 reserved; boxed sums are not in the fragment | `HeaderKind.box` |
| `regionHomog` | provisional frontend check (§6); remove when WeakCore's checker has the rule | `Frontend.regionHomog` |
| Argument spilling | calls take up to 32 argument words, the ones past the registers on the stack (§5); results at most 6; spawn arguments at most 6 (the TCB area) | §5 |
| Stored `ThreadId` | a trace word to a pinned block; storing one in a cell is subject to WeakCore's store restriction until its cell-type map exists | §7 |
| Pairs (scalar or trace) | one aligned 16-byte access in their region (§9); no emitter support yet (A64 `ldp`/`stp` are outside `WCLowerable`) | §6, §9 |
| Spawn argument reload | a future barrier site: the thread trampoline (`Runtime.threadF`) reloads the spawn argument words from the TCB with plain loads; under a collector they must be loaded-value-barrier loads, because a phase flip can happen between the parent's store and the child's first instruction. No code change under `gc none` | `Runtime.threadF` |
| Heal stub | not built: the future `scc_rt_heal` is a register-preserving stub with the grow stub's calling convention (the per-function `stack_grow` stub of `Scc/Emit/A64.lean` and its x64 counterpart: it saves the argument registers, on AArch64 also the frame record, calls the runtime and restores them) | — |
