/-!
# Certificate tables: root maps, block successors, restart descriptors (format only)

The data types of the three tables a
certificate will carry once a consumer (the collector track, inline allocation) needs them. Nothing
here is emitted: no emitter, runtime or trusted file reads these types. Where the tables will live in
the image (`.rodata` or a section of their own) is decided when bytes are emitted.

* **Root maps** (`RootMap`), one per safe point (`SafePt`): block entries, calls (keyed at the
  call's return address, as the `scc_stackmap` entry, `Scc/IR/StackMap.lean`, whose slots are the
  map's slot part; the return address also gets its own block-entry map since a thread can be
  preempted there) and `ret` instructions. A map lists the locations (`Loc`: a machine register by number, or a frame slot by
  signed byte offset from the frame record) that hold a heap reference or a stack address
  (`Tag`), and the derived-pointer pairs (`Derived`: a derived heap address and the location of its
  base, both live at the safe point).
* **Block successors** (`Succs`): per block entry, the addresses of the safe points control reaches
  next, and the functions a tail jump enters (by symbol: their entries; at most two in all for a
  conditional branch; none after `ret` or a trap).
* **Restart descriptors** (`Rseq`): `(start, commit, restart)` per inline restartable sequence.
  scc emits no inline allocation yet, so the table is empty (`Tables.rseq = []`).

Addresses are byte offsets from the start of the text (as `Scc.Sem.X64.Asm.labelOffs`), so that the
tables do not depend on where the text is linked. Registers are numbered by ISA (`Loc.reg`): x64
`%rax` = 0 … `%r15` = 15 in encoding order; AArch64 `x0` … `x30` = 0 … 30.

Untrusted: the theorem does not depend on these tables yet. A failed check fails a certificate,
it never makes one unsound.
-/

namespace Scc.Cert.Maps

/-- A location that may hold a root at a safe point. -/
inductive Loc where
  /-- A machine register, by its ISA number. -/
  | reg (n : Nat)
  /-- A frame slot: the 8-byte word at this signed byte offset from the frame record
  (x64 `%rbp`, AArch64 `x29`). -/
  | slot (off : Int)
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- What a location holds. -/
inductive Tag where
  /-- A heap reference (the collector traces and may rewrite it). -/
  | heap
  /-- A stack address (the stack move rewrites it). -/
  | stack
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A derived heap address: `derived` holds an address inside (or one past) the object whose
base `base` holds. Both are live at the safe point. -/
structure Derived where
  derived : Loc
  base : Loc
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The kind of a safe point. -/
inductive Kind where
  /-- The first instruction of a basic block. -/
  | blockEntry
  /-- A call, keyed at its return address (the address of the instruction after the call
  instruction, where a thread stopped in the callee resumes). Its slot part equals the
  `scc_stackmap` entry keyed at the same address, which is also a block entry with a map of its
  own (listed after the call's). -/
  | call
  /-- A `ret` instruction (its own address). -/
  | ret
  /-- The `start` of an armed restartable sequence (none yet). -/
  | seqStart
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A safe point: its kind and its address (byte offset from the start of the text). -/
structure SafePt where
  kind : Kind
  addr : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- **A root map**: the tagged locations and the derived pairs at one safe point, and whether the
function's own frame record is absent there (`frameless`: at the function's entry, before the
prologue sets the record up, and at every `ret`, after the epilogue tore it down; the reader then
finds the caller's frame record in the frame pointer, and the return address on the stack (x64)
or in the link register (AArch64)). The bit is exactly `kind = ret`, or the function's entry
(`FnTags.paramPts`'s first label), as `Scc.Cert.Maps.fnMapsW` sets it: the reader reads only the
bit, never the kind, to tell a frameless point. -/
structure RootMap where
  pt : SafePt
  roots : List (Loc × Tag)
  derived : List Derived := []
  frameless : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The number of a kind in the serialised tables. -/
def Kind.num : Kind → Nat
  | .blockEntry => 0
  | .call => 1
  | .ret => 2
  | .seqStart => 3

/-- **The kind word of a map** in the serialised tables: the kind's number, plus 256 if the point
is frameless (bit 8). -/
def RootMap.kindWord (m : RootMap) : Nat := m.pt.kind.num + 256 * (if m.frameless then 1 else 0)

/-- **A block's successors**: the safe-point addresses control reaches from the block entered at
`addr` without passing another block entry (`next`), and the functions it enters by a tail jump
(`tail`: their symbols, whose entries are the successors; a name needs no rebasing, so a slice's
tables keep their own coordinates). At most two in all. In the bytes a tail name is one more
successor word, its label (`Scc.Cert.Maps.tableItems`). -/
structure Succs where
  addr : Nat
  next : List Nat
  tail : List String := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- **A restart descriptor**: an armed sequence `[start, commit)`, restarted at `restart`. -/
structure Rseq where
  start : Nat
  commit : Nat
  restart : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- **The tables of one text.** Each list is sorted by address, as a reader would search it by
bisection. -/
structure Tables where
  maps : List RootMap
  succs : List Succs
  rseq : List Rseq := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Sorted strictly ascending (by the given key). -/
def sortedBy {α : Type} (key : α → Nat) : List α → Bool
  | a :: b :: rest => key a < key b && sortedBy key (b :: rest)
  | _ => true

/-- The format's shape conditions, independent of the text: the successor and descriptor tables
strictly sorted by address (the root maps are sorted by address but may repeat one: a block entry
can also be a call's return address), at most two successors per block (addresses and tail names
together), and each descriptor a
non-empty range whose restart point lies outside it. -/
def Tables.shapeOk (t : Tables) : Bool :=
  sortedBy Succs.addr t.succs &&
  t.succs.all (fun s => s.next.length + s.tail.length ≤ 2) &&
  sortedBy Rseq.start t.rseq &&
  t.rseq.all (fun r => r.start < r.commit && !(r.start ≤ r.restart && r.restart < r.commit))

/-- **At most two maps at one address, and then a call's and a block entry's**, in that order (a
call's return address is also a block entry): no other kinds share an address, so a reader picks
by the kind at a shared address only between those two. -/
def dupsOk : List RootMap → Bool
  | a :: b :: rest =>
    (a.pt.addr != b.pt.addr ||
      (a.pt.kind == .call && b.pt.kind == .blockEntry &&
        (rest.head?.all fun c => c.pt.addr != b.pt.addr))) && dupsOk (b :: rest)
  | _ => true

/-- scc emits no restartable sequence yet; the maps share an address only as `dupsOk` allows. -/
def Tables.g1Ok (t : Tables) : Bool := t.shapeOk && t.rseq.isEmpty && dupsOk t.maps

/-- Every tail name of the tables is one of the function symbols `names`. -/
def Tables.tailsIn (t : Tables) (names : List String) : Bool :=
  t.succs.all fun s => s.tail.all names.contains

/-! ## Tests -/

/-- info: true -/
#guard_msgs in
#eval ({ maps := [], succs := [⟨0, [8, 16], []⟩, ⟨8, [], []⟩] } : Tables).g1Ok

/-- info: false -/
#guard_msgs in
#eval ({ maps := [], succs := [⟨8, [], []⟩, ⟨0, [], []⟩] } : Tables).g1Ok

-- A tail name counts as a successor: two addresses and a name are too many.
#guard ({ maps := [], succs := [⟨0, [8], ["f"]⟩] } : Tables).g1Ok
#guard !({ maps := [], succs := [⟨0, [8, 16], ["f"]⟩] } : Tables).g1Ok
#guard ({ maps := [], succs := [⟨0, [8], ["f"]⟩] } : Tables).tailsIn ["g", "f"]
#guard !({ maps := [], succs := [⟨0, [8], ["f"]⟩] } : Tables).tailsIn ["g"]

/-- info: false -/
#guard_msgs in
#eval ({ maps := [], succs := [], rseq := [⟨0, 4, 8⟩] } : Tables).g1Ok

-- A call's and a block entry's map at one address are allowed, in that order; a `ret`'s and a
-- block entry's, a block entry before a call, or three maps at one address are not.
#guard dupsOk [{ pt := ⟨.call, 8⟩, roots := [] }, { pt := ⟨.blockEntry, 8⟩, roots := [] },
  { pt := ⟨.ret, 12⟩, roots := [], frameless := true }]
#guard !dupsOk [{ pt := ⟨.blockEntry, 8⟩, roots := [] }, { pt := ⟨.ret, 8⟩, roots := [] }]
#guard !dupsOk [{ pt := ⟨.blockEntry, 8⟩, roots := [] }, { pt := ⟨.call, 8⟩, roots := [] }]
#guard !dupsOk [{ pt := ⟨.call, 8⟩, roots := [] }, { pt := ⟨.blockEntry, 8⟩, roots := [] },
  { pt := ⟨.blockEntry, 8⟩, roots := [] }]
-- The kind word: bit 8 is the frame state.
#guard ({ pt := ⟨.ret, 12⟩, roots := [], frameless := true } : RootMap).kindWord == 258
#guard ({ pt := ⟨.blockEntry, 0⟩, roots := [], frameless := true } : RootMap).kindWord == 256
#guard ({ pt := ⟨.call, 8⟩, roots := [] } : RootMap).kindWord == 1

theorem empty_g1Ok : ({ maps := [], succs := [] } : Tables).g1Ok = true := by decide

/-- info: 'Scc.Cert.Maps.empty_g1Ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms empty_g1Ok

end Scc.Cert.Maps
