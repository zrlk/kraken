/-!
# scc configuration

The compilation configuration `(arch, host, gc)`, and the target
table: which Kraken instruction set and memory model each architecture is
checked against (used by the certificates of later stages; recorded here so
that the CLI, the emitters and the correctness statement agree on one table).
-/

namespace Scc

/-- Target architecture. -/
inductive Arch
  /-- x86-64, AT&T syntax; Kraken's `isa` under `Arch.tso`. -/
  | x64
  /-- AArch64 with FEAT_LSE2; Kraken's `isaLSE2` under `Arch.armv8`. -/
  | arm
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Target host. -/
inductive Host
  /-- A freestanding static Linux binary: `_start`, raw system calls, no libc. -/
  | linux
  /-- Bare metal with scc's own scheduler (not implemented). -/
  | raw
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Garbage collector. -/
inductive Gc
  /-- A bump allocator that never frees. -/
  | none
  deriving Repr, BEq, DecidableEq, Inhabited

def Arch.name : Arch → String | .x64 => "x64" | .arm => "arm"
def Host.name : Host → String | .linux => "linux" | .raw => "raw"
def Gc.name : Gc → String | .none => "none"

def Arch.ofString? : String → Option Arch
  | "x64" => some .x64 | "arm" => some .arm | _ => Option.none
def Host.ofString? : String → Option Host
  | "linux" => some .linux | "raw" => some .raw | _ => Option.none
def Gc.ofString? : String → Option Gc
  | "none" => some Gc.none | _ => Option.none

/-- The names of the Kraken instruction set and memory model each
architecture is verified against (stage 1 onwards). -/
def Arch.krakenTarget : Arch → String × String
  | .x64 => ("isa", "Arch.tso")
  | .arm => ("isaLSE2", "Arch.armv8")

/-- The object header (provisional; `Scc/LAYOUT.md` "Header").  Every object
in the arena and in the pinned region has one header word, laid out from
bit 0 as `kind | gc | n | m | len` with the widths below (they must sum to
64).  `n`/`m` are the scalar/trace words of the object's type, or of the
element type for an array, and `len` is the number of elements (1 for a
plain object), so the object occupies `1 + len·(n + m)` words.  The exact
encoding and the placement are open questions of WeakCore's GC design. -/
structure ObjLayout where
  /-- `false` (the default, the chosen placement): the header sits
  between the regions, `[trace][header][scalars]`, at `base − 8`, so a
  reference reaches its header in one load.  The heap is not linearly
  parsable and there is no object-start bitmap: a moving, evacuating
  collector never walks the heap linearly, and liveness comes from its mark
  bitmap.  `true`: the header precedes the trace region,
  `[header][trace][scalars]`, at `base − 8·(len·m + 1)`, so a linear walk
  from low addresses would parse the heap from headers alone. -/
  headerBeforeTrace : Bool := false
  /-- Bits of the object kind (`HeaderKind`). -/
  kindBits : Nat := 3
  /-- Bits reserved for the collector (always zero under `gc none`). -/
  gcBits : Nat := 5
  /-- Bits of the scalar word count `n`. -/
  nBits : Nat := 14
  /-- Bits of the trace word count `m`. -/
  mBits : Nat := 14
  /-- Bits of the element count `len`; an allocation of `2^lenBits` or more
  elements takes the heap abort outcome. -/
  lenBits : Nat := 28
  deriving Repr, Inhabited

/-- Sizes of the runtime's static regions. -/
structure Layout where
  /-- Bytes of heap arena (bump allocated, never freed). -/
  heapBytes : Nat := 64 * 1024 * 1024
  /-- Bytes of each thread's initial stack range (stacks grow by doubling). -/
  stackBytes : Nat := 16 * 1024
  /-- The largest stack range a thread may grow to (`stackBytes` times a
  power of two); a frame that needs more takes the abort outcome. -/
  stackCapBytes : Nat := 64 * 1024 * 1024
  /-- Bytes of the shared stack pool (`.bss`) all stack ranges come from. -/
  stackPoolBytes : Nat := 512 * 1024 * 1024
  /-- The most threads a program may spawn (the main thread not counted):
  the spawn that would exceed it takes the abort outcome (`threads`) before
  it takes a stack or calls `clone`.  A program therefore runs at most
  `maxThreads + 1` threads, and its certificates set
  `CertCfg.slots = maxThreads + 1`. -/
  maxThreads : Nat := 1023
  /-- The object layout's header (`ObjLayout`). -/
  obj : ObjLayout := {}
  deriving Repr, Inhabited

/-- A compilation configuration. -/
structure Config where
  arch : Arch := .x64
  host : Host := .linux
  gc : Gc := .none
  layout : Layout := {}
  deriving Repr, Inhabited

end Scc
