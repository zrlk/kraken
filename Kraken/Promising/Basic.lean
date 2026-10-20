/-
Promising-ARM/RISC-V for Kraken: basic types.

This is the ISA-generic weak-memory layer of Kraken, after Pulte,
Pichon-Pharabod, Kang, Lee and Hur, "Promising-ARM/RISC-V: a simpler and
faster operational concurrency model" (PLDI 2019), appendix A. A thread is an
ISA interpreter (Kraken's `Executable.step` for x64 or AArch64) that emits
memory *events*; this layer interprets the events against a global
timestamped memory and per-thread views.

The ISA is abstracted by `Promising.ISA`: how to fetch and run one
instruction as an event tree, and the syntactic register dependencies of an
instruction. Architecture-specific choices that the paper makes with its
`a ∈ {ARM, RISC-V}` flag, together with the x86-TSO instantiation, are an
`Arch` profile.

The single-threaded semantics of the ISAs is untouched by this layer: shared
memory is simply left out of a thread's `dmem`, so every shared access reaches
this layer as the `nonmem_*`/`sync_*`/`rmw`/`fence` effect the ISA already
emits for unmapped memory.

Values and widths. Handoff note:
- A value is a `Val`, a `BitVec 128` payload: the access value zero-extended,
  so the bits above its width are zero. The width is not stored next to the
  payload: it is the `bytes` of the `Loc` the value travels with (every event
  and message carries one), so the two cannot disagree. Adapters store
  `v.setWidth 128` and load `v.setWidth w.bits`.
- A `Loc` is a footprint `(addr, bytes)` compared structurally. Adapters emit
  the real access footprint (`bytes` ∈ 1, 2, 4, 8, 16). `bytes = 0` is an
  *unsized* location: width-agnostic, every access width reaches the same
  location (herd's non-mixed default, which ignores access sizes). It is
  only ever created by a declaration, never by an access.
- Declarations (`Decls`) are the locations a test or program names. An
  access is resolved against them (`Decls.resolve`) before it becomes an
  event: a declared location is reached only at its own width (or at any
  width if unsized); an access at another width to a declared address, or
  overlapping a sized declaration at another address, is reported as a
  mixed-size fault rather than silently becoming another location.
- Pitfall: `Memory.initVal` looks a location up by structural equality and
  falls back to `0`. Build `Memory.init` from the same declarations as the
  adapters' `Decls` (`Decls.initMem`), so that every access to a declared
  location resolves to exactly the `Loc` the initial value is stored under.
- Two *undeclared* footprints that overlap (e.g. a 4-byte and an 8-byte
  access to an address no declaration names) are two locations to
  `resolve`, which does not see the memory; the explorer reports the second
  one as mixed-size (`Machine.overlapFault`). The merged link
  (`SeqLink*`) excludes such accesses by its layout condition
  `SharedLayout.Ok`.
- The litmus and `.kl` front ends (`Kraken/Litmus/Layout.lean`) declare
  every symbol: at its C type's width if the test types it (strict mode),
  otherwise unsized, in legacy mode if the test types no location.
- The model stays non-mixed-size: the rules never split or merge values.
-/
import Kraken.MemKinds

namespace Kraken.Promising

/-! ## Timestamps, views, locations, memory -/

/-- A timestamp: the position of a write in the global memory. `0` is the
initial write of every location. -/
abbrev Time := Nat

/-- A view is a timestamp: the latest write a thread (or register) has
"seen", in the sense that a later read must not observe anything older. -/
abbrev View := Nat

/-- A location is a footprint: an address and a width in bytes. Two accesses
are to the same location iff footprints are equal. `bytes = 0` is an
*unsized* location, which every access width reaches (see the header and
`Decls.resolve`); an access at another width to a declared location, or one
overlapping a sized declaration, is reported as mixed-size by
`Decls.resolve` (herd's non-mixed-size default). -/
structure Loc where
  addr : BitVec 64
  bytes : Nat
  deriving Repr, DecidableEq, Hashable, Inhabited

instance : Ord Loc where
  compare a b := (compare a.addr.toNat b.addr.toNat).then (compare a.bytes b.bytes)

/-- A value: a 128-bit payload, the access value zero-extended. Its width is
the `bytes` of its location (1, 2, 4, 8 or 16; any width up to 16 for an
unsized location). -/
abbrev Val := BitVec 128

/-- Values hash by their low 64 bits (the hash of a 64-bit `BitVec`). Core's
`BitVec` hash for widths above 64 shifts and truncates, i.e. does bignum
arithmetic, on every call, and the explorer hashes every message of every
configuration it visits: with core's hash the LockFree runs took about 30%
longer. -/
scoped instance (priority := high) instHashableVal : Hashable Val := ⟨fun v => v.toNat.toUInt64⟩

/-- A write message. -/
structure Msg where
  loc : Loc
  val : Val
  tid : Nat
  deriving Repr, DecidableEq, Hashable, Inhabited

/-- The global memory: `mem[i]` is the message at timestamp `i + 1`.
Timestamp `0` is the initial state, held separately. -/
structure Memory where
  init : List (Loc × Val)
  msgs : Array Msg
  deriving Repr, BEq, Hashable, Inhabited

namespace Memory

/-- The latest timestamp in memory, `|M|`. -/
def last (m : Memory) : Time := m.msgs.size

/-- The message at timestamp `t ≥ 1`. -/
def get? (m : Memory) (t : Time) : Option Msg :=
  if t = 0 then none else m.msgs[t - 1]?

/-- The initial value of a location: as declared, else `0`. -/
def initVal (m : Memory) (l : Loc) : Val :=
  ((m.init.find? (·.1 == l)).map (·.2)).getD 0

/-- `read(M, l, t)`: the value a read of `l` at timestamp `t` returns, if `t`
is a write to `l` (or the initial write). -/
def read? (m : Memory) (l : Loc) (t : Time) : Option Val :=
  if t = 0 then some (m.initVal l)
  else match m.get? t with
    | some w => if w.loc == l then some w.val else none
    | none => none

/-- Is there a write to `l` with timestamp in `(lo, hi]`? -/
def writeIn (m : Memory) (l : Loc) (lo hi : Time) : Bool :=
  (List.range (hi - lo)).any fun i =>
    match m.get? (lo + i + 1) with
    | some w => w.loc == l
    | none => false

/-- `atomic(M, l, tid, tr, tw)`: an exclusive write to `l` at `tw` by `tid`
paired with an exclusive read at `tr` is atomic iff, when `tr` was a write
to `l`, every write to `l` strictly between them is by `tid`. -/
def atomic (m : Memory) (l : Loc) (tid : Nat) (tr tw : Time) : Bool :=
  match m.read? l tr with
  | none => true
  | some _ =>
    (List.range (tw - tr - 1)).all fun i =>
      match m.get? (tr + i + 1) with
      | some w => w.loc != l || w.tid == tid
      | none => true

/-- Append a message; its timestamp is the new `last`. -/
def append (m : Memory) (w : Msg) : Memory × Time :=
  ({ m with msgs := m.msgs.push w }, m.msgs.size + 1)

/-- The final value of every location: the last write, else the initial value. -/
def finalVal (m : Memory) (l : Loc) : Val :=
  match m.msgs.findRev? (·.loc == l) with
  | some w => w.val
  | none => m.initVal l

/-- Every location mentioned by the initial state or any message. -/
def locs (m : Memory) : List Loc :=
  (m.init.map (·.1) ++ m.msgs.toList.map (·.loc)).eraseDups

end Memory

/-! ## Declared locations -/

/-- The locations a test or program declares, and how an access to an
address no declaration names is resolved. The adapters resolve every access
against these (`resolve`) before it becomes an event. -/
structure Decls where
  /-- Declared locations, pairwise disjoint; `bytes = 0` is unsized. -/
  locs : List Loc := []
  /-- Legacy mode (herd's non-mixed default, today's litmus front ends): an
  undeclared address is an unsized location. Otherwise (strict, the default)
  an undeclared access is its own footprint. -/
  unsizedDefault : Bool := false
  deriving Repr, BEq, Hashable, Inhabited

namespace Decls

/-- Do the byte ranges `[a, a + n)` and `[b, b + m)` share a byte? -/
def overlaps (a : BitVec 64) (n : Nat) (b : BitVec 64) (m : Nat) : Bool :=
  a.toNat < b.toNat + m && b.toNat < a.toNat + n

/-- The location an access of `n` bytes at `addr` reaches, or a mixed-size
report:
- a declaration at `addr` of width `n`, or an unsized one, is the location
  (an unsized location is reached at any width up to 8 bytes; a wider access
  is reported, since an unsized location's values have no width to check
  it against: a 16-byte location must be declared with a 16-byte type);
- a declaration at `addr` of another width, or a sized declaration
  overlapping `[addr, addr + n)` at another address, is a mixed-size access;
- otherwise the access is undeclared: an unsized location in legacy mode
  (`unsizedDefault`), else its own footprint `⟨addr, n⟩`.

In strict mode two *undeclared* footprints at the same address (or
overlapping) with different widths become distinct locations here; the
explorer reports the access that overlaps a footprint already in memory
(`Machine.overlapFault`), since that needs the memory, which `resolve` does
not see. -/
def resolve (ds : Decls) (addr : BitVec 64) (n : Nat) : Except String Loc :=
  let here (b : BitVec 64) : String := s!"0x{b.toHex}"
  match ds.locs.find? (·.addr == addr) with
  | some l =>
    if l.bytes == n then .ok l
    else if l.bytes == 0 then
      if n ≤ 8 then .ok l
      else .error s!"mixed-size access: {n} bytes at {here addr}, declared unsized"
    else .error s!"mixed-size access: {n} bytes at {here addr}, declared {l.bytes} bytes"
  | none =>
    match ds.locs.find? (fun l => l.bytes != 0 && overlaps l.addr l.bytes addr n) with
    | some l =>
      .error s!"mixed-size access: {n} bytes at {here addr} overlaps the location of {l.bytes} bytes at {here l.addr}"
    | none =>
      if ds.unsizedDefault then
        if n ≤ 8 then .ok { addr, bytes := 0 }
        else .error s!"mixed-size access: {n} bytes at {here addr}, declared unsized"
      else .ok { addr, bytes := n }

/-- The declarations of an initial memory, plus further locations declared
without an initial value (initially `0`). Building `Memory.init` and the
adapters' `Decls` from one list keeps `Memory.initVal` from missing a
declared location. -/
def ofInit (init : List (Loc × Val)) (extra : List Loc := []) (unsizedDefault : Bool := false) : Decls :=
  { locs := (init.map (·.1) ++ extra).eraseDups, unsizedDefault }

/-- Strict, no declarations: every access is its own footprint. -/
theorem resolve_empty (addr : BitVec 64) (n : Nat) : resolve {} addr n = .ok { addr, bytes := n } := rfl

end Decls

/-- info: [Except.ok { addr := 0x0000000000001000#64, bytes := 8 },
 Except.error "mixed-size access: 4 bytes at 0x0000000000001000, declared 8 bytes",
 Except.error "mixed-size access: 4 bytes at 0x0000000000001004 overlaps the location of 8 bytes at 0x0000000000001000",
 Except.ok { addr := 0x0000000000001100#64, bytes := 0 },
 Except.ok { addr := 0x0000000000001100#64, bytes := 0 },
 Except.error "mixed-size access: 16 bytes at 0x0000000000001100, declared unsized",
 Except.ok { addr := 0x0000000000002000#64, bytes := 4 }] -/
#guard_msgs in
#eval
  let ds : Decls := { locs := [⟨0x1000, 8⟩, ⟨0x1100, 0⟩] }
  [ds.resolve 0x1000 8, ds.resolve 0x1000 4, ds.resolve 0x1004 4, ds.resolve 0x1100 4, ds.resolve 0x1100 8,
   ds.resolve 0x1100 16, ds.resolve 0x2000 4]

-- Legacy mode: undeclared addresses are unsized; a 16-byte access to one is reported.
/-- info: [Except.ok { addr := 0x0000000000002000#64, bytes := 0 },
 Except.error "mixed-size access: 16 bytes at 0x0000000000002000, declared unsized"] -/
#guard_msgs in
#eval
  let ds : Decls := { unsizedDefault := true }
  [ds.resolve 0x2000 4, ds.resolve 0x2000 16]

/-! ## Memory events

The ISA's `Effects` trees are translated into this ISA-independent tree so
that the thread rules are written once. `undef` is finite nondeterminism
(`undefined Bool` of a spurious store-exclusive failure, an unknown flag);
the translation is partial and reports anything it cannot handle as `fault`.
-/

/-- A thread's event tree for one instruction, parameterised by the ISA's
machine state `σ`. -/
inductive EvTree (σ : Type) : Type
  | done (s : σ)
  | fault (msg : String)
  | choose (n : Nat) (k : Fin n → EvTree σ)
  | load (k : LoadKind) (xcl : Bool) (loc : Loc) (ret : Val → EvTree σ)
  | store (k : StoreKind) (xcl : Bool) (loc : Loc) (v : Val) (ret : Bool → EvTree σ)
  /-- A read-modify-write. `noRet`: the value read is discarded (herd's `NoRet`
  AArch64 atomics, destination `XZR`/`WZR`): the read is not ordered by
  `fence .ld` and is never an acquire (`runTree`). Always `false` on x86. -/
  | rmw (k : RmwKind) (noRet : Bool) (loc : Loc) (op : Val → Option Val) (ret : Val → EvTree σ)
  | fence (k : FenceKind) (ret : Unit → EvTree σ)

namespace EvTree

/-- An access of `n` bytes at `addr`, resolved against the declarations: the
event `k` builds from the location reached, or a mixed-size fault. The ISA
adapters build every load, store and RMW through this. -/
def access {σ : Type} (ds : Decls) (addr : BitVec 64) (n : Nat) (k : Loc → EvTree σ) : EvTree σ :=
  match ds.resolve addr n with
  | .ok l => k l
  | .error m => .fault m

/-- With no declarations (strict), an access is its own footprint. -/
theorem access_empty {σ : Type} (addr : BitVec 64) (n : Nat) (k : Loc → EvTree σ) :
    access {} addr n k = k { addr, bytes := n } := rfl

def map {σ τ : Type} (f : σ → τ) : EvTree σ → EvTree τ
  | .done s => .done (f s)
  | .fault m => .fault m
  | .choose n k => .choose n fun i => map f (k i)
  | .load k x l ret => .load k x l fun v => map f (ret v)
  | .store k x l v ret => .store k x l v fun b => map f (ret b)
  | .rmw k nr l op ret => .rmw k nr l op fun v => map f (ret v)
  | .fence k ret => .fence k fun u => map f (ret u)
end EvTree

/-! ## The ISA interface -/

/-- What this layer needs from an ISA. `State` is the whole per-thread
machine state (registers, flags, private memory, pc). Registers are indexed
densely by `regIndex` so that a thread's register views are an array. -/
structure ISA where
  State : Type
  RegId : Type
  /-- The number of distinct register identities. -/
  numRegs : Nat
  regIndex : RegId → Fin numRegs
  /-- Run the instruction at the pc, as an event tree. `none`: the thread has
  halted (reached its end address). -/
  exec : State → Option (EvTree State)
  /-- The syntactic register dependencies of the instruction at the pc. -/
  deps : State → InstrDeps RegId
  beqState : State → State → Bool
  hashState : State → UInt64
  /-- The instruction at the pc, for traces. -/
  showInstr : State → String := fun _ => "?"

/-! ## Architecture profiles -/

/-- The architecture-dependent choices. `Arch.armv8` is the paper's ARM
instance. `Arch.tso` is x86-TSO as an instance of the same rules: every
load is an RCpc acquire, every store a release, and a locked RMW is also a
full barrier; a non-temporal store (`movnti`) is the one store that is not a
release (`StoreKind.nt`, see `writeSuccs`). -/
structure Arch where
  /-- The kind a plain load has: `.plain` on ARM, `.acqPc` on TSO. -/
  plainLoad : LoadKind
  /-- The kind a plain store has: `.plain` on ARM, `.rel` on TSO. -/
  plainStore : StoreKind
  /-- The kind a non-temporal store (`StoreKind.nt`) has: `.plain` on ARM
  (no such stores; never emitted), `.nt` on TSO (x86's weakly ordered
  `movnti`). -/
  ntStore : StoreKind
  /-- A plain RMW's kind: `.plain` on ARM, `.acqRel` on TSO. -/
  plainRmw : RmwKind
  /-- An RMW also acts as `fence .sy` before and after: TSO's `lock`. -/
  rmwFence : Bool
  /-- `read-view`: only a plain load may take the forwarding view of an
  exclusive write (Pulte et al.'s `a = ARM ∧ rk ⊑ pln`). `false` on ARM:
  herd's `aarch64.cat` lets an acquire forward from it too (see `readView`). `true` on
  TSO, where every load is an acquire, so a locked RMW's write never
  forwards; that does not matter, as the RMW is also a full barrier. -/
  fwdXclOnlyPlain : Bool
  /-- The success register of a store exclusive gets view `⊥` (ARM) rather
  than the store's post-view (RISC-V). -/
  succViewBot : Bool
  deriving Repr, BEq, Hashable, Inhabited

namespace Arch

def armv8 : Arch :=
  { plainLoad := .plain, plainStore := .plain, ntStore := .plain, plainRmw := .plain, rmwFence := false,
    fwdXclOnlyPlain := false, succViewBot := true }

def tso : Arch :=
  { plainLoad := .acqPc, plainStore := .rel, ntStore := .nt, plainRmw := .acqRel, rmwFence := true,
    fwdXclOnlyPlain := true, succViewBot := true }

/-- The effective kind of a load under the profile. -/
def loadKind (a : Arch) : LoadKind → LoadKind
  | .plain => a.plainLoad | k => k

def storeKind (a : Arch) : StoreKind → StoreKind
  | .plain => a.plainStore | .nt => a.ntStore | k => k

def rmwKind (a : Arch) : RmwKind → RmwKind
  | .plain => a.plainRmw | k => k

end Arch

end Kraken.Promising
