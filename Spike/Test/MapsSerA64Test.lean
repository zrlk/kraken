import Scc.Cert.MapsCheckA64
import Scc.Cert.MapsEmitA64
import Scc.Sem.Target
import Scc.Cert.MapsSer
import Scc.Emit.Data
import Scc.Emit.A64
import Scc.Frontend
import Scc.Lower.Program
import Scc.Test.Src

/-!
# The GC tables' bytes on AArch64 (untrusted test)

`Scc.Cert.Maps.tableItems` and `readTables` on the tables `computeA64` gives for `hello.w`,
`hello1.w`, `ret0.w`, `call1.w` and `wake.w` (the text at 0x400000):

* every key of the tables has a label of its own in the text (`labelAt`; P5's return-site
  labels before each `ret` and the fall-through labels after an overflow check's branch):
  serialisation with the text's labels alone succeeds (its refusal at an unlabelled key is
  the enforcement);
* with the text's labels (a stand-in `.Lser<a>` at any unlabelled key), the tables survive
  the bytes: laid out in a data section behind the program's `scc_stackmap`
  (`Scc.Emit.Data.mapItems`), resolved, and read back from `scc_gc_desc` (`roundTrip`);
* the tables' bytes are the same wherever the unit is loaded (every address word relative,
  `samePlaced`);
* the tables W1 checks (the constant routines' merged with the split) serialise to the same items;
* the blocks without successors: traps and non-returning calls only (a tail
  jump is succeeded by its target's entry).

The descriptor's `scc_text_start` and `scc_text_end` and the morestack return label
`.Lscc_rt_morestack.ret` are labels of the text (P5).

The emitter's table stage (`emitTables`): with the text's labels alone it succeeds; with
stand-ins, the text with its items appended reads back (`Scc.Sem.dataSections`, the loader's
reader) to the sections `Secs.ofProgram` gives with its data (`tbl`), so a certificate's
sections and the text agree; every difference word is the sole operand of its `.quad` line
(`diffLines`).
-/

namespace Scc.Cert.MapsSerA64Test
open Scc.Cert.Maps Scc.Cert.MapsA64 Scc.Cert.MapsRtA64

/-- The AArch64 IR, items and safepoints of a WeakCore source. -/
def compileW (src : String) :
    Except String (IR.Program × List Scc.Emit.A64.Item × List (String × List Int × List Int)) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let ir ← Lower.lowerProgram { arch := .arm } c
  let (its, ms) ← Scc.Emit.A64.emitItemsMaps ir
  pure (ir, its, ms)

/-- The base of the text. -/
def textBase : Nat := 0x400000

/-- The base of the data section of the tables. -/
def dataBase : Nat := 0x600000

/-- The stand-in label of an unlabelled key. -/
def standIn (a : Nat) : String := s!".Lser{a}"

/-- The keys of the tables: map points, successor entries and their targets. -/
def keys (t : Tables) : List Nat :=
  (t.maps.map (·.pt.addr) ++ t.succs.flatMap (fun s => s.addr :: s.next)).eraseDups

/-- The end of the text (after its last instruction). -/
def textEnd (items : List Item) : Nat :=
  items.foldl (fun e it => match it with | .ins a z _ => max e (a + z) | .label a _ => max e a) 0

/-- The tables of a source, its items and safepoints. -/
def tablesOf (src : String) :
    Except String (Tables × List Item × List (String × List Int × List Int)) := do
  let (p, its, ms) ← compileW src
  let items ← itemsOf its
  pure (← computeA64 p its, items, ms)

/-- The keys without a label in the text (with the instruction there). -/
def unlabelled (src : String) : Except String (List (Nat × String)) := do
  let (t, items, _) ← tablesOf src
  pure <| (keys t).filterMap fun a => match labelAt items a with
    | some _ => none
    | none => some (a, match items.find? (fun | .ins a' .. => a' == a | _ => false) with
      | some (.ins _ _ i) => reprStr i.flow
      | _ => "?")

/-- Serialisation with the text's labels alone (would refuse at the first unlabelled key). -/
def serPlain (src : String) : Except String Nat := do
  let (t, items, _) ← tablesOf src
  pure (← tableItems t (labelAt items)).length

/-- **The round trip** with stand-in labels at the unlabelled keys: whether the tables read back
equal the computed ones (a tail name as its function's entry, `Tables.flatTails`), and the
descriptor's text range. -/
def trip (src : String) : Except String (Bool × Nat × Nat) := do
  let (t, items, ms) ← tablesOf src
  let lab (a : Nat) := (labelAt items a).getD (standIn a)
  let code (l : String) : Option Nat :=
    (if l.startsWith ".Lser" then (l.drop 5).toNat? else labelAddr items l).map (textBase + ·)
  let (d, t') ← roundTrip t (some ∘ lab) {} code dataBase (Scc.Emit.Data.mapItems ms)
  -- a tail name reads back as its function's entry address
  pure (t' == t.flatTails (labelAddr items ·), d.textStart, d.textEnd)

/-- **Position independence**: the tables' bytes (from `scc_gc_maps` to the end of
`scc_gc_desc`, with the text's labels or stand-ins) with the unit at its base and moved by `s`
(text and data together, `s` a granule multiple) are the same. -/
def samePlaced (src : String) (s : Nat) : Except String Bool := do
  let (t, items, _) ← tablesOf src
  let lab (a : Nat) := some ((labelAt items a).getD (standIn a))
  let tbl ← tableItems t lab
  let img (k : Nat) : List UInt8 :=
    let code (l : String) : BitVec 64 := BitVec.ofNat 64 <|
      ((if l.startsWith ".Lser" then (l.drop 5).toNat? else labelAddr items l).getD 0) + textBase + k
    Kraken.DataImage.image (Kraken.DataImage.resolve code (dataBase + k) tbl) (dataBase + k) tbl
  pure (img 0 == img s && !(img 0).isEmpty)

/-- The tables W1 checks (constant routines merged with the split) serialise as the full ones. -/
def mergedSame (src : String) : Except String Bool := do
  let (p, its, ms) ← compileW src
  let items ← itemsOf its
  let rt ← match (consts? {}).bind (·.resolve endL items) with
    | some t => pure t
    | none => rtTablesOf p its
  let user ← computeSplit p its ms
  let full ← computeA64 p its
  let lab (a : Nat) := some ((labelAt items a).getD (standIn a))
  pure ((tableItems (mergeTables rt user) lab).toOption == (tableItems full lab).toOption &&
    (tableItems full lab).toOption.isSome)

/-- **How each block without successors ends**: the flow of its first instruction that does not
fall through (a call would give it its return address as a successor). -/
def deadEnds (src : String) : Except String (List (Nat × Flow)) := do
  let (t, items, _) ← tablesOf src
  pure <| (t.succs.filter fun s => s.next.isEmpty && s.tail.isEmpty).map fun s => (s.addr,
    (items.findSome? fun | .ins a _ i => if a ≥ s.addr && i.flow != .fall then some i.flow else none
                         | _ => none).getD .fall)

/-- A block end that leaves for good: a trap or a call after a zeroed frame pointer (`stop`).
(A tail jump to a function's symbol is no dead end: it is succeeded by the target's entry,
`Scc.Cert.Maps.entryTail`.) -/
def leaves : Flow → Bool
  | .stop => true
  | _ => false

/-- The fixtures. -/
def srcs : List String :=
  [w_src% "Scc/Test/hello.w", w_src% "Scc/Test/hello1.w", w_src% "Scc/Test/ret0.w",
   w_src% "Scc/Test/call1.w", w_src% "Scc/Test/wake.w"]

-- Every key has a label of its own in the text (P5: the `ret`s' return-site labels, the
-- fall-through after an overflow check's branch), so nothing is left unlabelled ...
#guard srcs.map (fun s => (unlabelled s).toOption) == [some [], some [], some [], some [], some []]
-- ... and serialisation with the text's labels alone succeeds.
/-- info: Except.ok 1641 -/
#guard_msgs in #eval serPlain (w_src% "Scc/Test/wake.w")
-- With stand-in labels the tables survive the bytes, and the descriptor's text range is the text.
#guard srcs.all fun s => match trip s, tablesOf s with
  | .ok (same, lo, hi), .ok (_, items, _) => same && lo == textBase && hi == textBase + textEnd items
  | _, _ => false
-- The tables' bytes do not depend on where the unit is loaded (relative words).
#guard srcs.all fun s => (samePlaced s 0x7a30000).toOption == some true
-- The tables W1 checks serialise as the full ones.
#guard srcs.all fun s => (mergedSame s).toOption == some true
-- Open point 1: the blocks without successors, per program, all leave for good: a trap or a
-- non-returning call. The tail jumps (`scc_rt_abort`'s to its stubs, `wc_main`'s and
-- `wc_waitLoop`'s to `wc_waitLoop`) are succeeded by their targets' entries.
#guard srcs.map (fun s => (deadEnds s).toOption.map fun ds => (ds.length, ds.all (leaves ·.2)))
  == [some (1, true), some (1, true), some (1, true), some (1, true), some (1, true)]
/--
info: Except.ok [(84, Scc.Cert.Maps.Flow.stop)]
-/
#guard_msgs in #eval deadEnds (w_src% "Scc/Test/wake.w")

/-- **The table stage on a source**, with stand-in labels at the unlabelled keys: whether the
text with the stage's items appended reads back (`Scc.Sem.dataSections`) to `Secs.ofProgram`'s
sections with the stage's data, and the number of table items. -/
def staged (src : String) : Except String (Bool × Nat) := do
  let (p, its, ms) ← compileW src
  let (tits, tbl) ← emitTablesWith (fun items a => some ((labelAt items a).getD (standIn a))) p its
  let text ← Scc.Emit.A64.render (its ++ tits)
  let secs := Scc.Emit.Data.Secs.ofProgram p.data (some ms) tbl
  pure ((Scc.Sem.dataSections text).any (fun d =>
      d.rodata == secs.rodata && d.data == secs.data && d.bss == secs.bss), tbl.length)

/-- **Every difference word is the sole operand of its `.quad` line** (the emitter rule: never
`.quad a - ., b - .`): the number of the stage's `.quad` lines with a difference (` - `), none
of which has a comma, or an error naming the first that has. -/
def diffLines (src : String) : Except String Nat := do
  let (p, its, _) ← compileW src
  let (tits, _) ← emitTables p its
  let text ← Scc.Emit.A64.render tits
  let ls := (text.splitOn "\n").filter fun l =>
    (l.splitOn ".quad").length > 1 && (l.splitOn " - ").length > 1
  match ls.find? fun l => (l.splitOn ",").length > 1 with
  | some l => throw s!"a difference word shares its line: {l}"
  | none => pure ls.length

/-- The table stage with the text's labels alone (its error, if any). -/
def stagedPlain (src : String) : String := Id.run do
  let some (p, its, _) := (compileW src).toOption | return "no program"
  match emitTables p its with
  | .ok _ => return "ok"
  | .error e => return e

-- The table stage: with stand-ins, the text and the sections agree; with the text's labels
-- alone (the serialiser's refusal at an unlabelled key being the enforcement), it succeeds.
#guard srcs.all fun s => match staged s with | .ok (b, n) => b && n > 0 | _ => false
#guard srcs.all fun s => stagedPlain s == "ok"
-- Every difference word of the stage is alone on its `.quad` line (and there are some).
#guard srcs.all fun s => match diffLines s with | .ok n => n > 0 | _ => false
-- A program without growable stacks (none is lowered so; here `ret0`'s IR with its growth
-- dropped and re-emitted) is refused, not given empty tables.
#guard (match compileW (w_src% "Scc/Test/ret0.w") with
  | .ok (p, _, _) =>
    let p' := { p with growth := none }
    match Scc.Emit.A64.emitItemsMaps p' with
    | .ok (its, _) => (match emitTables p' its with
      | .error e => e == "gc tables: no Program.growth (no scc_stackmap to take call maps from)"
      | .ok _ => false)
    | .error _ => false
  | .error _ => false)
-- Every fixture's IR has growth.
#guard srcs.all fun s => match compileW s with | .ok (p, _, _) => p.growth.isSome | _ => false

/-! ## The serialiser before its linear rewrite (the reference)

`tableItemsOld` is `tableItems` as it was before the rewrite (an accumulator appended to per
entry, `labelAt` per lookup); the rewrite (`firsts`, `mapM`, `labelIn (labelMap items)`) must
give the same items, or the same error, on every fixture. -/

/-- **The reference serialiser** (`tableItems` before its rewrite, kept verbatim). -/
def tableItemsOld (t : Tables) (labelOf : Nat → Option String) (d : DescLabels := {})
    (isLabel : String → Bool := fun _ => true) : Except String (List DItem) := do
  let lab (a : Nat) : Except String String := match labelOf a with
    | some l => pure l
    | none => throw s!"gc tables: no label at address {a}"
  unless t.rseq.isEmpty do throw "gc tables: restart descriptors are not in format 1"
  for m in t.maps do
    unless m.derived.isEmpty do throw s!"gc tables: derived pairs at {m.pt.addr} are not in format 1"
    if m.pt.kind == .seqStart then throw s!"gc tables: a sequence start at {m.pt.addr} is not in format 1"
    if m.pt.kind == .call && m.frameless then throw s!"gc tables: a frameless call map at {m.pt.addr}"
  let key (l : String) : DItem := .quadDiff l (some d.textStart)
  let (mapEntries, r) ← t.maps.foldlM (fun (acc, first) m => do
      let l ← lab m.pt.addr
      pure (acc ++ [key l, .quad m.kindWord, .quad m.roots.length, .quad first,
        .quad 0], first + m.roots.length)) (([] : List DItem), (0 : Nat))
  for s in t.succs do
    for g in s.tail do
      unless isLabel g do throw s!"gc tables: no label {g} (a tail successor at {s.addr})"
  let (succEntries, k) ← t.succs.foldlM (fun (acc, first) s => do
      let l ← lab s.addr
      let nn := s.next.length + s.tail.length
      pure (acc ++ [key l, .quad nn, .quad first], first + nn))
    (([] : List DItem), (0 : Nat))
  let nexts ← t.succs.flatMap (fun s => s.next.map Sum.inl ++ s.tail.map Sum.inr) |>.mapM fun
    | .inl a => key <$> lab a
    | .inr g => pure (key g)
  pure ([.align 8, .label mapsSym] ++ mapsHeader t.maps.length r ++ mapEntries ++
    t.maps.flatMap (fun m => m.roots.map fun r => Kraken.DataImage.Item.quad (encRoot r)) ++
    [.label succsSym] ++ succsHeader t.succs.length k ++ succEntries ++ nexts ++
    [.label rseqSym, .quad 0, .label descSym] ++ descItems d)

/-- **The reference label lookup** (`labelAt` before the rewrite, kept verbatim: core
`String.startsWith`, which the kernel does not evaluate; `labelAt` now tests the prefix on bytes,
`startsK`). -/
def labelAtOld (items : List Maps.Item) (a : Nat) : Option String :=
  (items.filterMap fun
    | .label a' l => if a' == a && !l.startsWith ".Lgw" then some l else none
    | .ins .. => none).getLast?

/-- The table stage with the reference serialiser and `labelAtOld` (`emitTables` before the
rewrite). -/
def emitTablesOld (p : IR.Program) (its : List Scc.Emit.A64.Item) (d : DescLabels := {}) :
    Except String (List Scc.Emit.A64.Item × List DItem) := do
  if p.growth.isNone then throw "gc tables: no Program.growth (no scc_stackmap to take call maps from)"
  let items ← itemsOf its 
  let t ← computeA64 p its 
  let tbl ← tableItemsOld t (labelAtOld items) d (fun g => (labelAddr items g).isSome)
  pure (.raw ".section .rodata" :: tbl.map dataItem, tbl)

/-- The fixtures the rewrite is pinned on. -/
def refSrcs : List String :=
  srcs ++ [w_src% "Scc/Test/hello1L.w", w_src% "Scc/Test/handoff.w",
    w_src% "Scc/Test/growmany.w", w_src% "Scc/Test/deeprec.w"]

/-- **Old against new** on a source: the table stage (`emitTables` against `emitTablesOld`,
the text's labels alone), and the serialiser with stand-ins at unlabelled keys (as
`samePlaced` and `staged` use it), item for item; and whether the stage succeeded. -/
def oldNew (src : String) : Bool × Bool := Id.run do
  let some (p, its, _) := (compileW src).toOption | return (false, false)
  let stage := match emitTables p its, emitTablesOld p its with
    | .ok (a, x), .ok (b, y) => (Scc.Emit.A64.render a).toOption == (Scc.Emit.A64.render b).toOption && x == y
    | .error e, .error e' => e == e'
    | _, _ => false
  let some (t, items, _) := (tablesOf src).toOption | return (false, false)
  let m := labelMap items
  let ser := match tableItems t (fun a => some ((labelIn m a).getD (standIn a))),
      tableItemsOld t (fun a => some ((labelAtOld items a).getD (standIn a))) with
    | .ok x, .ok y => x == y
    | .error e, .error e' => e == e'
    | _, _ => false
  (stage && ser, (emitTables p its).toOption.isSome)

-- The rewritten serialiser and stage give the reference's items on every fixture (all succeed).
#guard refSrcs.all fun s => oldNew s == (true, true)
-- The label map gives `labelAt`'s label, and the reference's, at every key and every text
-- address; the byte prefix test agrees with core's on every label of the text.
#guard refSrcs.all fun s => match tablesOf s with
  | .ok (t, items, _) => let m := labelMap items
    ((keys t) ++ List.range (textEnd items + 1)).all (fun a =>
      labelIn m a == labelAt items a && labelAt items a == labelAtOld items a) &&
    items.all fun | .label _ l => startsK l ".Lgw" == l.startsWith ".Lgw" | _ => true
  | .error _ => false

/-! ## The stage from a ranked witness (`emitTablesW`) -/

/-- The first (function, entry) of a ranked witness whose entry has a slot of positive rank. -/
def firstRanked (gw : GcWit) : Option (Nat × Nat) :=
  gw.zipIdx.findSome? fun ((_, r), f) =>
    r.zipIdx.findSome? fun (rk, j) => if rk.any (· > 0) then some (f, j) else none

/-- A ranked witness with its first positive-rank entry's ranks all set to 0 (a corrupted rank:
a slot live only through a successor claims to be read where it is). -/
def corruptRank (gw : GcWit) : Option GcWit := do
  let (f, j) ← firstRanked gw
  pure <| gw.modify f fun (w, r) => (w, r.modify j fun rk => rk.map fun _ => 0)

/-- A ranked witness with the first slot of its first positive-rank entry dropped (and its rank). -/
def dropSlot (gw : GcWit) : Option GcWit := do
  let (f, j) ← firstRanked gw
  pure <| gw.modify f fun (w, r) => (w.modify j List.tail, r.modify j List.tail)

/-- **The stage from scc's ranked witness against `emitTables`**, and whether a corrupted rank,
a dropped slot, a dropped function and an extra function are each refused. -/
def stagedW (src : String) : Bool × Bool := Id.run do
  let some (p, its, _) := (compileW src).toOption | return (false, false)
  let some gw := (gcWitness p its).toOption | return (false, false)
  let same := match emitTablesW p its gw, emitTables p its with
    | .ok (a, x), .ok (b, y) =>
      (Scc.Emit.A64.render a).toOption == (Scc.Emit.A64.render b).toOption && x == y
    | _, _ => false
  let refused (g : Option GcWit) : Bool := match g with
    | some g => (emitTablesW p its g).toOption.isNone
    | none => false
  (same, refused (corruptRank gw) && refused (dropSlot gw) && refused (some gw.tail) &&
    refused (some (gw ++ gw.take 1)))

-- With scc's ranked witness the stage is `emitTables`; each corruption is refused.
#guard refSrcs.all fun s => stagedW s == (true, true)

end Scc.Cert.MapsSerA64Test
