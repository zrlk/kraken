import Scc.Config
import Scc.Cert.MapsCompute

/-!
# Routine-relative tables of the runtime routines (untrusted)

The tables (`Scc.Cert.Maps.compute`) of the runtime routines are the same
in every program of one ISA and layout, but computing them inside a certificate's kernel run
costs more memory than the run has (the user functions' tables alone fit). So they are written
out once, as constants (`MapsRtConstX64`, `MapsRtConstA64`), with every address replaced by a
**routine-relative key** (`RKey`) that the text resolves:

* the routine (`RKey.routine`);
* the anchor (`RKey.anchor`): the last label at or before the point, inside the routine (from
  its entry symbol up to its end label `endL r`), that is no fresh label of the emitter
  (`freshLabel`: the x64 `.L{f}.x{n}` and AArch64 `….sp{n}` labels, numbered across a function or
  the program, are never anchors); a run of labels is keyed by its last one, and a point before
  every other label of the routine by its entry symbol;
* the index (`RKey.idx`): the number of instructions from the anchor to the point.

Instruction indices do not depend on the instruction sizes, so the keys hold for the assembler's
sizes as for unit sizes.

A key resolves (`RKey.resolve`) only if its anchor occurs exactly once in the text, inside the
routine, and the routine has that many instructions after it; a constant set resolves
(`RTables.resolve`) only if every key does. A set that does not resolve is not used: the tables
are computed instead, which is no worse for soundness.

The constants are for the default configuration only (`defaultCfg`: Linux, no collector, the
default `Layout`); `consts?` of the ISA modules is `none` for any other.

**Which routines are constant** (`constRoutine`): the runtime functions `scc_rt_*` other than
`scc_rt_main`, which calls the program's entry with its arguments, and `scc_rt_thr_worker`, which
calls the spawned functions; those two and the user functions are computed per program.

Untrusted: nothing reads these constants yet (the emitter does not emit tables); the tests pin
them against `compute` on the test programs.
-/

namespace Scc.Cert.Maps

/-- **A routine-relative key** of an instruction (see the module docstring). -/
structure RKey where
  routine : String
  anchor : String
  idx : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A root map keyed by `RKey`. -/
structure RMap where
  kind : Kind
  key : RKey
  roots : List (Loc × Tag)
  derived : List Derived := []
  /-- The frame state (`RootMap.frameless`). -/
  frameless : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A block's successors keyed by `RKey`, and the functions it enters by a tail jump (by name,
`Succs.tail`: names need no key). -/
structure RSuccs where
  key : RKey
  next : List RKey
  tail : List String := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- **The tables of some routines**, keyed by `RKey`, in the order of `compute`'s tables. -/
structure RTables where
  routines : List String
  maps : List RMap
  succs : List RSuccs
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The runtime routines whose tables are constants (see the module docstring). -/
def constRoutine (name : String) : Bool :=
  startsK name "scc_rt_" && name != "scc_rt_main" && name != "scc_rt_thr_worker"

/-- A fresh label of the emitter: its last `.`-separated component is `x` or `sp` followed by
digits. Never an anchor. -/
def freshLabel (l : String) : Bool :=
  let digits (ds : List Char) : Bool := !ds.isEmpty && ds.all Char.isDigit
  match ((splitK l ".").getLast?.getD l).toList with
  | 'x' :: ds => digits ds
  | 's' :: 'p' :: ds => digits ds
  | _ => false

/-- The items of routine `r`: from its label up to its end label `endL r` (exclusive). -/
def routineItems (endL : String → String) (items : List Item) (r : String) : List Item :=
  (items.dropWhile fun | .label _ l => l != r | _ => true).takeWhile fun
    | .label _ l => l != endL r | _ => true

/-- The key of each instruction of routine `r`, with its address. -/
def routineKeys (endL : String → String) (items : List Item) (r : String) : List (Nat × RKey) :=
  ((routineItems endL items r).foldl (fun (acc : List (Nat × RKey) × String × Nat) it =>
    match it with
    | .label _ l => if freshLabel l then acc else (acc.1, l, 0)
    | .ins a _ _ => ((a, ⟨r, acc.2.1, acc.2.2⟩) :: acc.1, acc.2.1, acc.2.2 + 1)) ([], r, 0)).1.reverse

/-- **The tables `t` of the routines `rs`, keyed by `RKey`**. An error if a point is no
instruction of the routines. -/
def relTables (endL : String → String) (items : List Item) (rs : List String) (t : Tables) :
    Except String RTables := do
  let ks := rs.flatMap (routineKeys endL items)
  let key (a : Nat) : Except String RKey := match ks.lookup a with
    | some k => pure k
    | none => throw s!"relTables: no instruction of the routines at {a}"
  let maps ← t.maps.mapM fun m => do
    pure { kind := m.pt.kind, key := ← key m.pt.addr, roots := m.roots, derived := m.derived,
           frameless := m.frameless }
  let succs ← t.succs.mapM fun s => do
    pure { key := ← key s.addr, next := ← s.next.mapM key, tail := s.tail }
  pure { routines := rs, maps, succs }

/-- **The address of a key**: the `idx`th instruction after its anchor, if the anchor occurs
exactly once in the text, inside the routine, and the instruction is before the routine's end. -/
def RKey.resolve (endL : String → String) (items : List Item) (k : RKey) : Option Nat :=
  if (items.filter fun | .label _ l => l == k.anchor | _ => false).length != 1 then none
  else if !((routineItems endL items k.routine).any fun | .label _ l => l == k.anchor | _ => false)
  then none
  else
    let rest := (items.dropWhile fun | .label _ l => l != k.anchor | _ => true).takeWhile fun
      | .label _ l => l != endL k.routine | _ => true
    (rest.filterMap fun | .ins a _ _ => some a | _ => none)[k.idx]?

/-- **The tables of a constant set** on a text, if every key resolves. -/
def RTables.resolve (endL : String → String) (items : List Item) (c : RTables) : Option Tables := do
  let maps ← c.maps.mapM fun m => do
    pure { pt := ⟨m.kind, ← m.key.resolve endL items⟩, roots := m.roots, derived := m.derived,
           frameless := m.frameless }
  let succs ← c.succs.mapM fun s => do
    pure ({ addr := ← s.key.resolve endL items, next := ← s.next.mapM (·.resolve endL items),
            tail := s.tail } : Succs)
  pure { maps, succs }

/-- The keys of a constant set, each once. -/
def RTables.keys (c : RTables) : List RKey :=
  (c.maps.map (·.key) ++ c.succs.flatMap (fun s => s.key :: s.next)).eraseDups

/-- **The configuration the constants are for**: Linux, no collector, the default layout. (The
patterns name every field, so a new field of `Layout` or `ObjLayout` fails to compile here until
it is compared too. The GC tables' witness `gcWit` is not compared: the constants do not depend
on it.) -/
def defaultCfg (cfg : Config) : Bool :=
  let d : Layout := {}
  match cfg with
  | ⟨_, host, gc, ⟨hb, sb, cb, pb, mt, ⟨hbt, kb, gb, nb, mb, lb⟩⟩, _⟩ =>
    host == .linux && gc == .none &&
    hb == d.heapBytes && sb == d.stackBytes && cb == d.stackCapBytes && pb == d.stackPoolBytes &&
    mt == d.maxThreads && hbt == d.obj.headerBeforeTrace && kb == d.obj.kindBits &&
    gb == d.obj.gcBits && nb == d.obj.nBits && mb == d.obj.mBits && lb == d.obj.lenBits

/-! ## Tests -/

#guard freshLabel ".Lscc_rt_alloc.x4" && freshLabel ".L8_scc_rt_grow.sp12" &&
  !freshLabel ".L8_scc_rt_grow.sp_check" && !freshLabel ".L8_scc_rt_grow.0_entry" &&
  !freshLabel ".Lscc_rt_grow.entry" && !freshLabel "scc_rt_grow" && !freshLabel ".Lf.x"
#guard defaultCfg {} && defaultCfg { arch := .arm } &&
  !defaultCfg { layout := { maxThreads := 7 } } && !defaultCfg { host := .raw } &&
  !defaultCfg { layout := { obj := { headerBeforeTrace := true } } }
#guard constRoutine "scc_rt_grow" && !constRoutine "scc_rt_main" &&
  !constRoutine "scc_rt_thr_worker" && !constRoutine "wc_main"

/-- A toy text: routine `r` (an anchor `r.a`, a fresh label `r.x1`), then `s`. -/
private def rtToyItems : List Item :=
  [.label 0 "r", .ins 0 2 {}, .label 2 "r.a", .ins 2 1 {}, .label 3 "r.x1", .ins 3 4 {},
   .label 7 "e.r", .label 7 "s", .ins 7 1 {}, .label 8 "e.s"]

private def rtToyEnd (f : String) : String := "e." ++ f

#guard routineKeys rtToyEnd rtToyItems "r" ==
  [(0, ⟨"r", "r", 0⟩), (2, ⟨"r", "r.a", 0⟩), (3, ⟨"r", "r.a", 1⟩)]
#guard (⟨"r", "r.a", 1⟩ : RKey).resolve rtToyEnd rtToyItems == some 3
-- Past the routine's end, an anchor outside the routine, an unknown anchor: no address.
#guard (⟨"r", "r.a", 2⟩ : RKey).resolve rtToyEnd rtToyItems == none
#guard (⟨"r", "s", 0⟩ : RKey).resolve rtToyEnd rtToyItems == none
#guard (⟨"r", "r.b", 0⟩ : RKey).resolve rtToyEnd rtToyItems == none
-- A duplicated anchor: no address.
#guard (⟨"r", "r.a", 0⟩ : RKey).resolve rtToyEnd (rtToyItems ++ [.label 8 "r.a"]) == none
-- Keying and resolving are inverse on the routine's points.
#guard (do
    let t : Tables := { maps := [{ pt := ⟨.blockEntry, 2⟩, roots := [(.reg 0, .heap)] }],
                        succs := [{ addr := 2, next := [3] }] }
    let c ← (relTables rtToyEnd rtToyItems ["r"] t).toOption
    let t' ← c.resolve rtToyEnd rtToyItems
    pure (t' == t)) == some true

end Scc.Cert.Maps
