import Scc.Config
import Scc.Lower.Term
import Scc.IR.StackMap

/-!
# The scc runtime, written in the IR

The only runtime of an scc binary (`--host linux`, `--gc none`):

* `scc_rt_start` (entered from `_start`): sets `SIGPIPE` to ignored
  (`rt_sigaction`), allocates the main thread's TCB and stack, and switches to
  them (`Term.switchTo`), entering `scc_rt_main`.
* `scc_rt_main`: runs the setup block `rodata` if `main` takes its result (static
  data by the heap-bytes route), calls `main` with the main thread's
  `ThreadId` (its TCB's address), and exits the process with `main`'s result
  (`exit_group`; the kernel keeps `v mod 256`).
* `scc_rt_alloc(h, k, u)`: the bump allocator for objects (`allocF`): an
  atomic add on the arena cursor, never freed.  `h` is an object header with
  length 0 (`Scc.Obj.header0`) and `k` the element count; the allocation is
  the header word plus `k` times the element's scalar and trace words, laid
  out as in `Scc/LAYOUT.md`, and the result is the object's base.  With
  `k ≥ 2^lenBits`, the abort outcome (`AbortKind.heap`).  `u` is the
  allocation's size in source units (the object's words, `Frontend.words`,
  plus one, the lowerer's constant at `new` and `k·words + 1` at `newBuf`):
  an atomic add on the heap counter `scc_rt_heap_use` gives the units `old`
  allocated before; the allocation takes the abort outcome iff
  `old ≤ heapCells < old + u` (it crosses the limit), and spins for ever if
  `old > heapCells` (another thread crossed it and is exiting the process).
  The counter is also the arena's cursor, in 16-byte cells (`heapCells` is
  `heapBytes / 16`): the object is the `u` cells from `scc_rt_heap +
  16·old`, which hold it (an object takes at most 16 bytes per source unit),
  so the add both counts and places the allocation.
  The arena is `.bss`: zero-filled and never reused, so every allocation
  starts zeroed and every trace slot null.
* `scc_rt_thread_init(tcb)`: takes an initial stack range (`lay.stackBytes`)
  from the shared pool, initialises the TCB (`self`, `stackLimit`,
  `stackBase`, `stackTop`, `permit`, `exited`), and returns the range's top.
* `scc_rt_stack_take(size)` / `scc_rt_stack_release(base, size)`: the shared
  stack pool (size classes, free arrays under a spin lock, a bump cursor);
  an exhausted pool is the abort outcome (`AbortKind.stack`).  Every range a
  thread gets passes the take site and every range given back passes the
  release site (see "Sites" below).
* `scc_rt_grow(fp, need)`: the grow routine (`Growth.grow`), entered from the
  emitter's trampoline when a prologue check fails: moves the stack to a
  range at least twice as large and rewrites the stack addresses that the
  frame records and the stack maps designate (`Scc.IR.StackMap`); past the
  per-thread cap `lay.stackCapBytes`, the abort outcome (`AbortKind.stack`).
* `scc_rt_thr_<f>(a₁, …, aₙ)`: the entry of threads spawned on block `f`,
  whose argument words it takes as parameters (the `clone` argument and the
  `IR.spawnReg` registers, `Term.spawn`): calls `f`, release-stores the TCB's
  `exited` flag (the TCB is the thread pointer), and ends the thread (`exit`).
* `scc_rt_print(p, n)`: the `write` loop: `write(1, p, n)` until `n` bytes are
  out; a positive result advances; `-EINTR` and `-EAGAIN` retry; zero or any
  other error takes the abort outcome (`AbortKind.write`).  With `fence` (an
  AArch64 program that spawns, `lowerWithMarks`), a full barrier precedes the
  `svc`, so no promise is outstanding at the `write` (`Scc/DESIGN.md` §4, *No
  promise across `clone`*).
* `scc_rt_park` / `scc_rt_unpark(t)`: a permit word in the TCB with a futex
  (`FUTEX_WAIT_PRIVATE` / `FUTEX_WAKE_PRIVATE`).  `park` consumes the permit if
  set, else waits while it is 0, then consumes it; it may return spuriously,
  which WeakCore's `park` allows (a return without a permit is a spurious wake).
* `scc_rt_abort(k)`: dispatches on the `AbortKind` code to
  `scc_rt_abort_<kind>`, which writes the kind's message to fd 2 and exits
  with status `abortExitCode` (101); one `exit_group` site per kind, the
  trap instruction itself labelled `scc_rt_abort_<kind>_exit`.
* `scc_rt_alloc_tcb(h, k)`: the same allocator over the **pinned region**, a
  separate `.bss` range that holds only thread control blocks, so "pinned"
  is a property of the address; its exhaustion (which the thread cap
  prevents: `pinnedBytes`) is the `AbortKind.threads` outcome (as is a failed
  `clone`).  A TCB is an object of kind `pinned`: its fields are its first
  scalar words and a spawned thread's argument words follow them by region
  (`Term.tcbLayout`).
* `scc_rt_thread_reserve`: the first step of every spawn: an atomic add on
  `scc_rt_nthreads` gives the child's thread index `i`; `i > lay.maxThreads`
  is the `AbortKind.threads` outcome, before the spawn takes a TCB or a stack
  or calls `clone`.  The count is never decremented, so a program runs at
  most `lay.maxThreads + 1` threads (the main thread is index 0).

## Sites

Two `nop`s carry global labels (`Inst.site`), each placed exactly once, so
that a specification can name the moments a stack range changes hands:

* `scc_rt_take_site` is the single exit of `scc_rt_stack_take`, after the
  range is popped from a free array (lock released) or bumped from the
  pool, with the range's base in the first argument register (`x0`/`%rdi`)
  and its size in the second (`x1`/`%rsi`).  Every take passes it: the
  start routine's (the main thread's first range), the parent's for a
  spawned child (in `scc_rt_thread_init`, before `clone`), and the grow
  routine's.
* `scc_rt_release_site` is the first instruction of `scc_rt_stack_release`,
  with base and size in the same registers, before the lock is taken and the
  range pushed onto its free array.  The only caller is the emitter's grow
  trampoline, which runs on the new range: the thread has left the old range
  when the release site runs.
-/

open Scc.IR

namespace Scc.Lower.Runtime

open Scc.Lower

/-- Linux constants. -/
def sigpipe : Nat := 13
def eintr : Nat := 4
def eagain : Nat := 11
def futexWaitPrivate : Nat := 128
def futexWakePrivate : Nat := 129

/-- Abort with `k` (a call that does not return). -/
def abortWith (k : AbortKind) : B Unit := do
  emit (.call [] Names.abort [imm k.code])
  terminate .unreachable

/-- Bytes of the pinned region: room for the TCBs of `lay.maxThreads + 1`
threads with the largest argument (`maxSpawnArgs` words), each with its header,
so the thread cap is reached before the region is full. -/
def pinnedBytes (lay : Layout) : Nat := (lay.maxThreads + 1) * (8 + Tcb.size + 8 * maxSpawnArgs)

/-- The heap counter's limit in source units: an object takes at most two
words per source unit (a locative is one source word and two runtime words;
the header is one word for the unit `+ 1`), so `heapCells` units fit
`heapBytes`. -/
def heapCells (lay : Layout) : Nat := lay.heapBytes / 16

/-- The bump allocator `name(h, k)` over the region `region` of `bytes` bytes
with cursor `cursor` (a byte offset): `h` is a header word with length 0 (`Obj.header0`), `k`
the element count (1 for an object).  It takes `1 + k·(n + m)` words, writes
the header `h | k << lenShift` before the trace region
(`headerBeforeTrace`) or between the regions, and returns the base, which has
the `k·m` trace words below it (and the header) and the `k·n` scalar words
from it.  `k ≥ 2^lenBits` or exhaustion aborts with `kind` (`heap` for
`scc_rt_alloc` over the arena, `threads` for `scc_rt_alloc_tcb` over the
pinned region).  Both regions are `.bss`: zero-filled and never reused, so
every allocation starts zeroed and every trace slot null.

With `counter` (`scc_rt_alloc`), the cursor is the heap counter
`scc_rt_heap_use`, counting 16-byte cells (`heapCells`, `bytes / 16`, which
must be exact), and the function takes a third argument `u`, the
allocation's source units: after the length check (`entry`), `old ← cursor
+= u` (atomic, `cnt`); if `old + u ≤ cells` the object is the `u` cells from
`region + 16·old` (`ok`), which hold it (an object takes at most 16 bytes per
source unit, `Runtime.heapCells`); otherwise (`slow`) `old > cells` spins
(`spin`: another thread crossed the limit and is exiting the process) and
`old ≤ cells` aborts with `kind` (`full`).  The add is the allocation's only
access to shared state, so its order is the allocations' order.  Each thread
adds once more after the counter passes `cells` (it then spins or aborts),
so the counter stays below `cells + (maxThreads + 1)·umax`, with `umax ≤
2^lenBits·maxWords + 1` after the length check: far from wrapping. -/
def allocF (lay : Layout) (name : Sym := Names.alloc) (region : Sym := Names.heap)
    (cursor : Sym := Names.heapUse) (bytes : Nat := lay.heapBytes) (kind : AbortKind := .heap)
    (counter : Bool := true) : Except String Func := do
  let o := lay.obj
  if counter && bytes % 16 != 0 then
    throw s!"{name}: the arena's size {bytes} is not a multiple of 16 bytes"
  buildFunc name (if counter then ["h", "k", "u"] else ["h", "k"]) false do
    terminate (.br .uge (.reg "k") (imm (2 ^ o.lenBits)) "full" (if counter then "cnt" else "len"))
    if counter then
      let cells := bytes / 16
      startBlock "cnt"
      let ca ← fresh "ca"
      emit (.la ca cursor)
      let old ← fresh "old"
      emit (.rmw .add old ⟨ca, 0⟩ (.reg "u"))
      let top ← binR .add (.reg old) (.reg "u") "top"
      terminate (.br .ugt top (imm cells) "slow" "ok")
      startBlock "slow"
      terminate (.br .ugt (.reg old) (imm cells) "spin" "full")
      startBlock "spin"
      terminate (.jmp "spin")
      startBlock "full"
      abortWith kind
      startBlock "ok"
      let m0 ← binR .lshr (.reg "h") (imm (Obj.mShift o)) "m"
      let m ← binR .and m0 (imm (2 ^ o.mBits - 1)) "m"
      let r ← fresh "r"
      emit (.la r region)
      let s ← binR .add (.reg r) (← binR .shl (.reg old) (imm 4) "off") "s"
      finish o s m
      return
    startBlock "len"
    let n0 ← binR .lshr (.reg "h") (imm (Obj.nShift o)) "n"
    let n ← binR .and n0 (imm (2 ^ o.nBits - 1)) "n"
    let m0 ← binR .lshr (.reg "h") (imm (Obj.mShift o)) "m"
    let m ← binR .and m0 (imm (2 ^ o.mBits - 1)) "m"
    let w ← binR .add n m "w"
    let kw ← binR .mul (.reg "k") w "kw"
    let words ← binR .add kw (imm 1) "words"
    let sz ← binR .shl words (imm 3) "size"
    let cur ← fresh "cur"
    emit (.la cur cursor)
    let old ← fresh "old"
    emit (.rmw .add old ⟨cur, 0⟩ sz)
    let e ← binR .add (.reg old) sz "end"
    terminate (.br .ugt e (imm bytes) "full" "ok")
    startBlock "full"
    abortWith kind
    startBlock "ok"
    let r ← fresh "r"
    emit (.la r region)
    let s ← binR .add (.reg r) (.reg old) "s"
    finish o s m
where
  /-- The object at `s` (its first byte) with `m` trace words per element:
  the header store and the return of the base. -/
  finish (o : ObjLayout) (s m : Operand) : B Unit := do
    let km ← binR .mul (.reg "k") m "km"
    let tr ← binR .shl km (imm 3) "tr"
    let kl ← binR .shl (.reg "k") (imm (Obj.lenShift o)) "kl"
    let hdr ← binR .or (.reg "h") kl "hdr"
    let hp ← if o.headerBeforeTrace then pure s else binR .add s tr "hp"
    emit (.store .plain .w64 ⟨← inReg hp, 0⟩ hdr)
    let b1 ← binR .add s tr "b"
    terminate (.ret [← binR .add b1 (imm 8) "base"])

/-! ## The stack pool

Stack ranges have sizes `lay.stackBytes · 2^k` (size class `k`) up to
`lay.stackCapBytes`.  A range comes from the free array of its class if that
is not empty, else from the pool's bump cursor.  The pool region holds stack
contents only: the cursor, the lock, the free counts and the free arrays are
separate data items.  Class `k`'s free array has room for every range of that
class the pool can hold (`stackPoolBytes / (stackBytes · 2^k)`), so it never
overflows.  The free arrays are guarded by a spin lock (`xchg` to take,
release store to give back); the cursor is an atomic add. -/

/-- The number of size classes. -/
def numClasses (lay : Layout) : Nat :=
  ((List.range 64).filter fun k => lay.stackBytes * 2 ^ k ≤ lay.stackCapBytes).length

/-- Words of the free arrays of all classes. -/
def freeWords (lay : Layout) : Nat :=
  ((List.range (numClasses lay)).map fun k => lay.stackPoolBytes / (lay.stackBytes * 2 ^ k)).sum

/-- Registers holding the address of the free count of the class of `size`
(a class size) and the base of its free array. -/
def classOf (lay : Layout) (size : Operand) : B (Reg × Reg) := do
  let sz ← fresh "sz"
  let off ← fresh "off"
  let cnt ← fresh "cnt"
  let k8 ← fresh "k8"
  emit (.mov sz (imm lay.stackBytes))
  emit (.mov off (imm 0))
  emit (.mov cnt (imm (lay.stackPoolBytes / lay.stackBytes)))
  emit (.mov k8 (imm 0))
  let loop ← freshLabel "cls"
  let body ← freshLabel "clsnext"
  let done ← freshLabel "clsdone"
  startBlock loop
  terminate (.br .ult (.reg sz) size body done)
  startBlock body
  let bytes ← binR .shl (.reg cnt) (imm 3) "bytes"
  emit (.bin .add off (.reg off) bytes)
  emit (.bin .lshr cnt (.reg cnt) (imm 1))
  emit (.bin .shl sz (.reg sz) (imm 1))
  emit (.bin .add k8 (.reg k8) (imm 8))
  terminate (.jmp loop)
  startBlock done
  let fn ← fresh "fn"
  emit (.la fn Names.stackFreeN)
  let na ← fresh "na"
  emit (.bin .add na (.reg fn) (.reg k8))
  let fa ← fresh "fa"
  emit (.la fa Names.stackFree)
  let arr ← fresh "arr"
  emit (.bin .add arr (.reg fa) (.reg off))
  pure (na, arr)

/-- Take the pool's lock (spin on `xchg`). -/
def lockPool : B Unit := do
  let l ← fresh "lk"
  emit (.la l Names.stackLock)
  let spin ← freshLabel "spin"
  let got ← freshLabel "locked"
  startBlock spin
  let o ← fresh "o"
  emit (.rmw .xchg o ⟨l, 0⟩ (imm 1))
  terminate (.br .eq (.reg o) (imm 0) got spin)
  startBlock got

/-- Release the pool's lock (release store). -/
def unlockPool : B Unit := do
  let l ← fresh "lk"
  emit (.la l Names.stackLock)
  emit (.store .rel .w64 ⟨l, 0⟩ (imm 0))

/-- `scc_rt_stack_take(size)`: a range of class size `size`, from the free
array of its class or the bump cursor; abort `AbortKind.stack` when the pool
is exhausted.  Both ways join at the take site (`Names.takeSite`), the
function's single exit. -/
def stackTakeF (lay : Layout) : Except String Func :=
  buildFunc Names.stackTake ["size"] false do
    let base ← fresh "base"
    let (na, arr) ← classOf lay (.reg "size")
    lockPool
    let n ← fresh "n"
    emit (.load .plain .w64 n ⟨na, 0⟩)
    terminate (.br .eq (.reg n) (imm 0) "bump" "pop")
    startBlock "pop"
    let n1 ← binR .sub (.reg n) (imm 1) "n1"
    emit (.store .plain .w64 ⟨na, 0⟩ n1)
    let off ← binR .shl n1 (imm 3) "off"
    let a ← binR .add (.reg arr) off "a"
    emit (.load .plain .w64 base ⟨← inReg a, 0⟩)
    unlockPool
    terminate (.jmp "taken")
    startBlock "bump"
    unlockPool
    let cur ← fresh "cur"
    emit (.la cur Names.stackNext)
    let old ← fresh "old"
    emit (.rmw .add old ⟨cur, 0⟩ (.reg "size"))
    let e ← binR .add (.reg old) (.reg "size") "end"
    terminate (.br .ugt e (imm lay.stackPoolBytes) "full" "ok")
    startBlock "full"
    abortWith .stack
    startBlock "ok"
    let s ← fresh "pool"
    emit (.la s Names.stacks)
    emit (.bin .add base (.reg s) (.reg old))
    terminate (.jmp "taken")
    startBlock "taken"
    emit (.site Names.takeSite [.reg base, .reg "size"])
    terminate (.ret [.reg base])

/-- `scc_rt_stack_release(base, size)`: push a range onto the free array of
its class.  The release site (`Names.releaseSite`) comes first. -/
def stackReleaseF (lay : Layout) : Except String Func :=
  buildFunc Names.stackRelease ["base", "size"] false do
    emit (.site Names.releaseSite [.reg "base", .reg "size"])
    let (na, arr) ← classOf lay (.reg "size")
    lockPool
    let n ← fresh "n"
    emit (.load .plain .w64 n ⟨na, 0⟩)
    let off ← binR .shl (.reg n) (imm 3) "off"
    let a ← binR .add (.reg arr) off "a"
    emit (.store .plain .w64 ⟨← inReg a, 0⟩ (.reg "base"))
    emit (.store .plain .w64 ⟨na, 0⟩ (← binR .add (.reg n) (imm 1) "n1"))
    unlockPool
    terminate (.ret [])

/-- `scc_rt_thread_reserve`: count a spawn (`Names.nthreads`) and return
its thread index, 1 for the first spawn; past `lay.maxThreads`, abort
`AbortKind.threads`. -/
def threadReserveF (lay : Layout) : Except String Func :=
  buildFunc Names.threadReserve [] false do
    let cnt ← fresh "cnt"
    emit (.la cnt Names.nthreads)
    let old ← fresh "old"
    emit (.rmw .add old ⟨cnt, 0⟩ (imm 1))
    let i ← binR .add (.reg old) (imm 1) "tidx"
    terminate (.br .ugt i (imm lay.maxThreads) "full" "ok")
    startBlock "full"
    abortWith .threads
    startBlock "ok"
    terminate (.ret [i])

def threadInitF (lay : Layout) : Except String Func :=
  buildFunc Names.threadInit ["tcb"] false do
    markHeap "tcb"
    let base ← fresh "base"
    emit (.call [base] Names.stackTake [imm lay.stackBytes])
    let lim ← binR .add (.reg base) (imm Tcb.headroom) "limit"
    let top ← binR .add (.reg base) (imm lay.stackBytes) "top"
    emit (.store .plain .w64 ⟨"tcb", Tcb.self⟩ (.reg "tcb"))
    emit (.store .plain .w64 ⟨"tcb", Tcb.stackLimit⟩ lim)
    emit (.store .plain .w64 ⟨"tcb", Tcb.permit⟩ (imm 0))
    emit (.store .plain .w64 ⟨"tcb", Tcb.exited⟩ (imm 0))
    emit (.store .plain .w64 ⟨"tcb", Tcb.stackBase⟩ (.reg base))
    emit (.store .plain .w64 ⟨"tcb", Tcb.stackTop⟩ top)
    terminate (.ret [top])

/-- Bytes the grow routine leaves free below the frame that did not fit, on
top of `Tcb.headroom`. -/
def growSlack : Nat := 256

/-- `scc_rt_grow(fp, need)` (`Growth.grow`; the protocol is in
`Scc.IR.StackMap`): the new size is the smallest `2^j` times the old one
(`j ≥ 1`) that holds the live stack `[fp, stackTop)`, `need` more bytes,
`Tcb.headroom` and `growSlack`; above `lay.stackCapBytes`, abort.  It copies
the live stack to the top of the new range, rewrites the saved frame pointers
of the frame records and the map-designated stack addresses, updates the TCB,
and returns `(delta, oldBase, oldBytes)`. -/
def growF (lay : Layout) : Except String Func :=
  buildFunc Names.grow ["fp", "need"] false do
    let tp ← fresh "tp"
    emit (.getTp tp)
    let base ← fresh "base"
    emit (.load .plain .w64 base ⟨tp, Tcb.stackBase⟩)
    let top ← fresh "top"
    emit (.load .plain .w64 top ⟨tp, Tcb.stackTop⟩)
    let size ← binR .sub (.reg top) (.reg base) "size"
    let used ← binR .sub (.reg top) (.reg "fp") "used"
    let w1 ← binR .add used (.reg "need") "want"
    let want ← binR .add w1 (imm (Tcb.headroom + growSlack)) "want"
    let ns ← fresh "ns"
    emit (.bin .shl ns size (imm 1))
    startBlock "dbl"
    terminate (.br .ult (.reg ns) want "dbl2" "cap")
    startBlock "dbl2"
    emit (.bin .shl ns (.reg ns) (imm 1))
    terminate (.jmp "dbl")
    startBlock "cap"
    terminate (.br .ugt (.reg ns) (imm lay.stackCapBytes) "full" "take")
    startBlock "full"
    abortWith .stack
    startBlock "take"
    let nb ← fresh "nbase"
    -- The words live across `stackTake` are raw stack addresses of the old
    -- range and sizes (`Func.scalarRegs`): none is a trace word.
    for o in [Operand.reg "fp", .reg tp, .reg base, .reg top, size, .reg ns] do
      if let .reg r := o then markScalar r
    emit (.call [nb] Names.stackTake [.reg ns])
    let ntop ← binR .add (.reg nb) (.reg ns) "ntop"
    let delta ← binR .sub ntop (.reg top) "delta"
    -- Copy the live words [fp, top) to [fp + delta, top + delta).
    let src ← fresh "src"
    emit (.mov src (.reg "fp"))
    startBlock "copy"
    terminate (.br .uge (.reg src) (.reg top) "walk0" "copy1")
    startBlock "copy1"
    let w ← fresh "w"
    emit (.load .plain .w64 w ⟨src, 0⟩)
    let dst ← binR .add (.reg src) delta "dst"
    emit (.store .plain .w64 ⟨← inReg dst, 0⟩ (.reg w))
    emit (.bin .add src (.reg src) (imm 8))
    terminate (.jmp "copy")
    -- Walk the frame records from fp, reading the old copy, writing the new.
    startBlock "walk0"
    let p ← fresh "p"
    emit (.mov p (.reg "fp"))
    let tab ← fresh "tab"
    emit (.la tab StackMap.tableSym)
    let n ← fresh "n"
    emit (.load .plain .w64 n ⟨tab, 0⟩)
    let ib ← binR .mul (.reg n) (imm StackMap.entryBytes) "ib"
    let ib8 ← binR .add ib (imm 8) "ib"
    let offs ← binR .add (.reg tab) ib8 "offs"
    startBlock "walk"
    let s ← fresh "saved"
    emit (.load .plain .w64 s ⟨p, 0⟩)
    terminate (.br .ult (.reg s) (.reg base) "done" "walk1")
    startBlock "walk1"
    terminate (.br .uge (.reg s) (.reg top) "done" "walk2")
    startBlock "walk2"
    let np ← binR .add (.reg p) delta "np"
    emit (.store .plain .w64 ⟨← inReg np, 0⟩ (← binR .add (.reg s) delta "ns"))
    let ra ← fresh "ra"
    emit (.load .plain .w64 ra ⟨p, 8⟩)
    -- Bisection for the entry of return address ra.
    let lo ← fresh "lo"
    let hi ← fresh "hi"
    emit (.mov lo (imm 0))
    emit (.mov hi (.reg n))
    startBlock "bs"
    terminate (.br .uge (.reg lo) (.reg hi) "next" "bs1")
    startBlock "bs1"
    let sum ← binR .add (.reg lo) (.reg hi) "sum"
    let mid ← fresh "mid"
    emit (.bin .lshr mid sum (imm 1))
    let eo ← binR .mul (.reg mid) (imm StackMap.entryBytes) "eo"
    let e ← fresh "e"
    emit (.bin .add e (.reg tab) eo)
    emit (.bin .add e (.reg e) (imm 8))
    let a ← fresh "a"
    emit (.load .plain .w64 a ⟨e, 0⟩)
    terminate (.br .eq (.reg a) (.reg ra) "found" "bs2")
    startBlock "bs2"
    terminate (.br .ult (.reg a) (.reg ra) "bslo" "bshi")
    startBlock "bslo"
    emit (.bin .add lo (.reg mid) (imm 1))
    terminate (.jmp "bs")
    startBlock "bshi"
    emit (.mov hi (.reg mid))
    terminate (.jmp "bs")
    -- Rewrite the entry's stack slots that hold old-range addresses.
    startBlock "found"
    let cntS ← fresh "nstack"
    emit (.load .plain .w64 cntS ⟨e, 8⟩)
    let first ← fresh "first"
    emit (.load .plain .w64 first ⟨e, 24⟩)
    let q ← fresh "q"
    emit (.bin .shl q (.reg first) (imm 3))
    emit (.bin .add q (.reg q) offs)
    let i ← fresh "i"
    emit (.mov i (imm 0))
    startBlock "fix"
    terminate (.br .uge (.reg i) (.reg cntS) "next" "fix1")
    startBlock "fix1"
    let o ← fresh "o"
    emit (.load .plain .w64 o ⟨q, 0⟩)
    let addr ← fresh "addr"
    emit (.bin .add addr (.reg s) (.reg o))
    let v ← fresh "v"
    emit (.load .plain .w64 v ⟨addr, 0⟩)
    terminate (.br .ult (.reg v) (.reg base) "skip" "fix2")
    startBlock "fix2"
    terminate (.br .uge (.reg v) (.reg top) "skip" "fix3")
    startBlock "fix3"
    let na ← binR .add (.reg addr) delta "na"
    emit (.store .plain .w64 ⟨← inReg na, 0⟩ (← binR .add (.reg v) delta "nv"))
    terminate (.jmp "skip")
    startBlock "skip"
    emit (.bin .add i (.reg i) (imm 1))
    emit (.bin .add q (.reg q) (imm 8))
    terminate (.jmp "fix")
    startBlock "next"
    emit (.mov p (.reg s))
    terminate (.jmp "walk")
    -- The thread now owns the new range.
    startBlock "done"
    emit (.store .plain .w64 ⟨tp, Tcb.stackBase⟩ (.reg nb))
    emit (.store .plain .w64 ⟨tp, Tcb.stackTop⟩ ntop)
    emit (.store .plain .w64 ⟨tp, Tcb.stackLimit⟩ (← binR .add (.reg nb) (imm Tcb.headroom) "limit"))
    terminate (.ret [delta, .reg base, size])

def printF (fence : Bool := false) : Except String Func :=
  buildFunc Names.print ["p", "n"] false do
    startBlock "loop"
    terminate (.br .eq (.reg "n") (imm 0) "done" "write")
    startBlock "write"
    let r ← fresh "r"
    if fence then emit (.fence .full)
    emit (.syscall r .write [imm 1, .reg "p", .reg "n"])
    terminate (.br .eq (.reg r) (immNeg eintr) "loop" "chk2")
    startBlock "chk2"
    terminate (.br .eq (.reg r) (immNeg eagain) "loop" "chk3")
    startBlock "chk3"
    terminate (.br .sle (.reg r) (imm 0) "fail" "adv")
    startBlock "adv"
    emit (.bin .add "p" (.reg "p") (.reg r))
    emit (.bin .sub "n" (.reg "n") (.reg r))
    terminate (.jmp "loop")
    startBlock "fail"
    abortWith .write
    startBlock "done"
    terminate (.ret [])

def parkF : Except String Func :=
  buildFunc Names.park [] false do
    let t ← fresh "tp"
    emit (.getTp t)
    let old ← fresh "old"
    emit (.rmw .xchg old ⟨t, Tcb.permit⟩ (imm 0))
    terminate (.br .eq (.reg old) (imm 1) "done" "wait")
    startBlock "wait"
    let w ← binR .add (.reg t) (imm Tcb.permit) "word"
    let r ← fresh "r"
    emit (.syscall r .futex [w, imm futexWaitPrivate, imm 0, imm 0, imm 0, imm 0])
    let old2 ← fresh "old"
    emit (.rmw .xchg old2 ⟨t, Tcb.permit⟩ (imm 0))
    terminate (.ret [])
    startBlock "done"
    terminate (.ret [])

def unparkF : Except String Func :=
  buildFunc Names.unpark ["t"] false do
    let old ← fresh "old"
    emit (.rmw .xchg old ⟨"t", Tcb.permit⟩ (imm 1))
    terminate (.br .eq (.reg old) (imm 0) "wake" "done")
    startBlock "wake"
    let w ← binR .add (.reg "t") (imm Tcb.permit) "word"
    let r ← fresh "r"
    emit (.syscall r .futex [w, imm futexWakePrivate, imm 1, imm 0, imm 0, imm 0])
    terminate (.ret [])
    startBlock "done"
    terminate (.ret [])

def abortKinds : List AbortKind := [.overflow, .heap, .stack, .write, .threads]

def AbortKind.message : AbortKind → String
  | .overflow => "scc: abort: Int addition overflow\n"
  | .heap => "scc: abort: out of heap or threads\n"
  | .stack => "scc: abort: out of stack\n"
  | .write => "scc: abort: write to standard output failed\n"
  | .threads => "scc: abort: cannot create a thread\n"

/-- `scc_rt_abort_<kind>`: the message of `k` to fd 2, then
`exit_group(abortExitCode)`: one exit site per abort kind, its trap
instruction labelled `scc_rt_abort_<kind>_exit` (`Names.abortExit`). -/
def abortKindF (k : AbortKind) : Except String Func :=
  buildFunc (Names.abortKind k) [] false do
    let m ← fresh "msg"
    emit (.la m (Names.abortMsg k))
    let r ← fresh "r"
    emit (.syscall r .write [imm 2, .reg m, imm (AbortKind.message k).utf8ByteSize])
    let x ← fresh "r"
    emit (.syscall x .exitGroup [imm abortExitCode] (some (Names.abortExit k)))
    terminate .unreachable

/-- `scc_rt_abort(k)` (`Program.abortFn`): tail-calls the routine of kind
`k` (callers pass only `AbortKind.code`s). -/
def abortF : Except String Func :=
  buildFunc Names.abort ["k"] false do
    for k in abortKinds do
      let l ← freshLabel "is"
      let nx ← freshLabel "next"
      terminate (.br .eq (.reg "k") (imm k.code) l nx)
      startBlock l
      terminate (.tail (Names.abortKind k) [])
      startBlock nx
    terminate .unreachable

def startF (lay : Layout) : Except String Func :=
  buildFunc Names.start [] false do
    let sa ← fresh "sa"
    emit (.la sa Names.sigign)
    let r ← fresh "r"
    emit (.syscall r .rtSigaction [imm sigpipe, .reg sa, imm 0, imm 8])
    let tcb ← fresh "tcb"
    markHeap tcb
    -- The main thread's TCB: no argument words; its index field stays 0.
    let (h, _) ← tcbLayout lay.obj .unit
    emit (.call [tcb] Names.allocTcb [imm h, imm 1])
    let top ← fresh "top"
    emit (.call [top] Names.threadInit [.reg tcb])
    terminate (.switchTo (.reg top) (.reg tcb) Names.mainThread (.reg tcb))

def mainThreadF (entry : Frontend.Entry) (setupWords : Nat) : Except String Func :=
  buildFunc Names.mainThread ["tcb"] true do
    markHeap "tcb"
    let args ← match entry.arg with
      | .unit => pure []
      | .tid => pure [Operand.reg "tcb"]
      | .setupTid => do
          let ds ← (List.range setupWords).mapM fun _ => fresh "s"
          emit (.call ds (Names.user "rodata") [])
          pure (ds.map Operand.reg ++ [.reg "tcb"])
    let code ← if entry.retInt then do
        let v ← fresh "v"
        emit (.call [v] (Names.user "main") args)
        pure (Operand.reg v)
      else do
        emit (.call [] (Names.user "main") args)
        pure (imm 0)
    let r ← fresh "r"
    emit (.syscall r .exitGroup [code])
    terminate .unreachable

/-- The trampoline of threads spawned on block `f` with argument type `T`:
its parameters are the argument words (`Term.spawn` passes them in the
`clone` argument and the `IR.spawnReg` registers), one per word of `T`'s
layout (`tcbLayout`). -/
def threadF (obj : ObjLayout) (f : String) (T : CoreLang.Ty) : Except String Func := do
  let sl ← match Obj.slots T (Tcb.size / 8) 0 with
    | some sl => pure sl
    | none => throw s!"no runtime layout for type {repr T}"
  let ps := (List.range sl.length).map fun i => s!"a{i}"
  buildFunc (Names.thread f) ps true do
    -- The layout `Term.spawn` checked (and still reserves in the TCB).
    let _ ← tcbLayout obj T
    -- A future barrier site: under a collector the argument words cross the
    -- `clone` in registers, and a phase flip can happen between the
    -- parent's last barrier and the child's first instruction
    -- (`Scc/LAYOUT.md` §10).  With `--gc none` nothing is needed.
    let args := ps.map Operand.reg
    markWords T args
    emit (.call [] (Names.user f) args)
    let tcb ← fresh "tcb"
    emit (.getTp tcb)
    markHeap tcb
    emit (.store .rel .w64 ⟨tcb, Tcb.exited⟩ (imm 1))
    let r ← fresh "r"
    emit (.syscall r .exit [imm 0])
    terminate .unreachable

/-- Little-endian bytes of a 64-bit word. -/
def le64 (v : Nat) : List UInt8 := (List.range 8).map fun i => UInt8.ofNat ((v / 2 ^ (8 * i)) % 256)

/-- The runtime's data items, the zero-initialised (`.bss`) ones first.  The
heap arena, the pinned region and the stack pool are the last of those, in that
order, so that in `.bss` they follow every counter: a link puts them after the
counters, each a contiguous range of its own that a layout read off the
executable gives from its symbol and size. -/
def data (lay : Layout) : List Data :=
  -- 16-aligned, as each counter was when it followed its region.
  [ { name := Names.heapUse, align := 16, init := .zero 8 },
    { name := Names.pinnedNext, align := 16, init := .zero 8 },
    { name := Names.stackNext, align := 16, init := .zero 8 },
    { name := Names.stackLock, init := .zero 8 },
    { name := Names.stackFreeN, init := .zero (8 * numClasses lay) },
    { name := Names.stackFree, init := .zero (8 * freeWords lay) },
    { name := Names.nthreads, init := .zero 8 },
    { name := Names.heap, align := 16, init := .zero lay.heapBytes },
    { name := Names.pinned, align := 16, init := .zero (pinnedBytes lay) },
    { name := Names.stacks, align := 16, init := .zero lay.stackPoolBytes },
    -- struct sigaction { handler = SIG_IGN, flags = 0, restorer = 0, mask = 0 }
    { name := Names.sigign, init := .bytes (le64 1 ++ le64 0 ++ le64 0 ++ le64 0) } ] ++
  abortKinds.map fun k =>
    { name := Names.abortMsg k, align := 1, init := .bytes (AbortKind.message k).toUTF8.toList }

end Scc.Lower.Runtime
