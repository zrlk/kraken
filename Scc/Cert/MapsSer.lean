import Scc.Cert.MapsCompute
import Scc.IR.StackMap
import Kraken.DataImage

/-!
# Certificate tables in the image: serialisation and its reader

The words of a program's `Scc.Cert.Maps.Tables` in `.rodata` (after `scc_stackmap`,
`Scc.IR.StackMap`), as `Kraken.DataImage.Item`s (`tableItems`), and a reader that gives the
tables back from the bytes (`readTables`), as the kernel's reader does (format version 1).
Every address word is **relative** (position
independence): a key address (a map's `pt`, a block's `blk`, a successor) is `.quad L - T`, its
label minus `scc_text_start` (`T`), and a descriptor address word is `.quad L - .`, its label
minus the word's own address (`Kraken.DataImage.Item.quadDiff`). No word holds an absolute
address, so the bytes do not depend on where the unit is loaded, and no word holds an
instruction size (the assembler computes the differences). `labelOf` names a code label at each
key address of the tables (`labelAt`: the last label at the address in the text, never a
granule label).

```
scc_gc_maps:  .quad 1, N, R                          -- version, entries, root words (mapsHeader)
              N × { .quad L_pt - T, kindWord, nRoots, firstRoot, nDerived = 0 }
              R × root word                          -- shared by all entries (encRoot)
scc_gc_succs: .quad M, K                             -- entries, successor words (succsHeader)
              M × { .quad L_blk - T, nNext, firstNext }
              K × .quad L - T                        -- shared by all entries (a tail name: its
                                                     -- symbol, after the addresses' labels)
scc_gc_rseq:  .quad 0                                -- no restartable sequences in format 1
scc_gc_desc:  .quad magic, 1, T - ., scc_text_end - ., scc_gc_maps - ., scc_gc_succs - .,
                    scc_gc_rseq - ., scc_stackmap - ., scc_rt_morestack - .,
                    .Lscc_rt_morestack.ret - .                              -- (descItems)
```

Descriptor words 7–9 (the stack-move table and morestack's range) are `0` when absent (no
label is at its own word's address, so 0 is no relative address); every lowered program has
growth, so `emitTables` always names them.

The kind word is `RootMap.kindWord` (kind number, plus 256 if frameless). A root is one word: a
register `n` as `4n + t`, a frame slot at signed offset `o` as `4o + 2 + t`, with `t` = 0 for a
heap reference and 1 for a stack address (the word modulo 4, Euclidean, says which). Format 1
carries no derived pairs and no restart descriptors; tables with either, with a sequence-start
map, or with a frameless call map do not serialise (the reader refuses them).

The header words and the descriptor are each written by one function (`mapsHeader`,
`succsHeader`, `descItems`) and read by one (`readTables`), with the constants named, so that a
change of the format's headers is local. The label names of the descriptor are a parameter
(`DescLabels`), by default the emitter's (`IR.StackMap.textStartSym`, `textEndSym`,
`msRetLabel`; the morestack ret label is emitted with P5's ret labels); its address words are
one list (`DescLabels.words`), so a word appended to the descriptor is one more entry there and
in `Desc`.

The reader (`readTables`) reads 8-byte little-endian words through `rd` (absolute address to the
signed word there), starting at the descriptor, adds each descriptor word's own address (`0` in
words 7–9: absent), and refuses what a version-1 reader refuses: a wrong magic or
version, a kind other than 0–2, kind bits other than 0–8, a frameless call, `n_derived ≠ 0`,
`first + n > R` (or `K`), a non-empty `scc_gc_rseq`, a descriptor word outside the address space,
and a key outside the text (`text_start + word ≥ text_end`). Key addresses come back relative to
`text_start`, as `Tables` keeps them (the words themselves).

Untrusted, like the tables: nothing trusted reads these bytes.
-/

namespace Scc.Cert.Maps

/-- A data item (`Kraken.DataImage.Item`; `Item` is the text's, `Scc.Cert.Maps.Item`). -/
abbrev DItem := Kraken.DataImage.Item

/-! ## The format's constants -/

/-- The symbols of the tables and the descriptor. -/
def mapsSym : String := "scc_gc_maps"
def succsSym : String := "scc_gc_succs"
def rseqSym : String := "scc_gc_rseq"
def descSym : String := "scc_gc_desc"

/-- The descriptor's magic word: the bytes `"SCCGCDS1"` in memory order. -/
def descMagic : Nat := 0x3153444347434353

/-- The descriptor's version (word 1). -/
def descVersion : Nat := 1

/-- The format version of `scc_gc_maps` (its first word). -/
def mapsVersion : Nat := 1

/-- The kind bits of a kind word, and the frameless bit. -/
def kindMask : Nat := 0xff
def framelessBit : Nat := 256

/-- **The code labels the descriptor names** besides the tables: the text range (`textStart`
is also the base of every key word), the stack-move table, and morestack's range (`msStart` up
to its ret label `msRet`); `none` for the last three is an absent word (`.quad 0`). -/
structure DescLabels where
  textStart : String := IR.StackMap.textStartSym
  textEnd : String := IR.StackMap.textEndSym
  stackmap : Option String := some IR.StackMap.tableSym
  msStart : Option String := some IR.StackMap.morestackSym
  msRet : Option String := some IR.StackMap.msRetLabel
  deriving Repr, BEq, Inhabited

/-- The labels of descriptor words 2–9, in order (`none`: absent). -/
def DescLabels.words (d : DescLabels) : List (Option String) :=
  [some d.textStart, some d.textEnd, some mapsSym, some succsSym, some rseqSym, d.stackmap,
   d.msStart, d.msRet]

/-- The kind of a kind number. -/
def Kind.ofNum? : Nat → Option Kind
  | 0 => some .blockEntry | 1 => some .call | 2 => some .ret | 3 => some .seqStart | _ => none

#guard [Kind.blockEntry, .call, .ret, .seqStart].all fun k => Kind.ofNum? k.num == some k

/-! ## Root words -/

/-- The word of a root. -/
def encRoot : Loc × Tag → Int
  | (l, g) =>
    let t : Int := match g with | .heap => 0 | .stack => 1
    match l with
    | .reg n => 4 * (n : Int) + t
    | .slot o => 4 * o + 2 + t

/-- The root of a word (`Int`'s `/` and `%` are Euclidean); a register word must not be
negative. -/
def decRoot (v : Int) : Except String (Loc × Tag) :=
  let g : Tag := if v % 2 == 0 then .heap else .stack
  if v % 4 < 2 then
    if v < 0 then throw s!"gc tables: negative register root word {v}" else pure (.reg (v / 4).toNat, g)
  else pure (.slot (v / 4), g)

#guard [(Loc.reg 7, Tag.heap), (.reg 0, .stack), (.reg 30, .heap), (.slot (-8), .heap),
    (.slot (-64), .stack), (.slot 16, .heap), (.slot 0, .stack)].all fun r =>
  (decRoot (encRoot r)).toOption == some r
#guard encRoot (.slot (-8), .stack) == -29 && encRoot (.reg 5, .stack) == 21
#guard (decRoot (-4)).toOption.isNone

/-! ## The serialiser -/

/-- The header of `scc_gc_maps`: version, `n` entries, `r` root words. -/
def mapsHeader (n r : Nat) : List DItem := [.quad mapsVersion, .quad n, .quad r]

/-- The header of `scc_gc_succs`: `m` entries, `k` successor words. -/
def succsHeader (m k : Nat) : List DItem := [.quad m, .quad k]

/-- The descriptor's words: magic, version, then each label minus the word's own address
(`.quad L - .`), `.quad 0` for an absent one. -/
def descItems (d : DescLabels) : List DItem :=
  [.quad descMagic, .quad descVersion] ++ d.words.map fun
    | some l => .quadDiff l none
    | none => .quad 0

/-- The running sums of a list from `acc` (each element's first index in the concatenation,
offset by `acc`) and the total. Structural and linear, so the kernel evaluates it in one pass. -/
def firstsFrom (acc : Nat) : List Nat → List Nat × Nat
  | [] => ([], acc)
  | x :: xs => let p := firstsFrom (acc + x) xs; (acc :: p.1, p.2)

/-- The running sums of a list from 0, and its total (`firstsFrom 0`). -/
def firsts (ls : List Nat) : List Nat × Nat := firstsFrom 0 ls

#guard firsts [2, 0, 3, 1] == ([0, 2, 2, 5], 6)

/-- **The items of the tables** (see the module docstring), 8-aligned, from `scc_gc_maps` to
the end of `scc_gc_desc`: `labelOf a` names the code label at text address `a`, each key word
that label minus `d.textStart` (`.quad L - T`). A block's tail
names (`Succs.tail`) are successor words after its addresses', each the function's symbol, so
the reader sees one more key word (the format does not change); `isLabel` says which symbols
the text defines. An error if an address has no label or a tail name is no label of the text,
or the tables are not of format 1 (restart descriptors, derived pairs, a sequence-start map, a
frameless call map). -/
def tableItems (t : Tables) (labelOf : Nat → Option String) (d : DescLabels := {})
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
  -- each entry's first index and the total, by one scan of the lengths (`firsts`); the entries
  -- by `mapM`, flattened once (no accumulator appended to per entry)
  let (mfs, r) := firsts (t.maps.map (·.roots.length))
  let mapEntries ← (t.maps.zip mfs).mapM fun (m, first) => do
      let l ← lab m.pt.addr
      pure [key l, .quad m.kindWord, .quad m.roots.length, .quad first, .quad 0]
  for s in t.succs do
    for g in s.tail do
      unless isLabel g do throw s!"gc tables: no label {g} (a tail successor at {s.addr})"
  let (sfs, k) := firsts (t.succs.map fun s => s.next.length + s.tail.length)
  let succEntries ← (t.succs.zip sfs).mapM fun (s, first) => do
      let l ← lab s.addr
      pure [key l, .quad (s.next.length + s.tail.length), .quad first]
  let nexts ← t.succs.flatMap (fun s => s.next.map Sum.inl ++ s.tail.map Sum.inr) |>.mapM fun
    | .inl a => key <$> lab a
    | .inr g => pure (key g)
  pure ([.align 8, .label mapsSym] ++ mapsHeader t.maps.length r ++ mapEntries.flatten ++
    t.maps.flatMap (fun m => m.roots.map fun r => Kraken.DataImage.Item.quad (encRoot r)) ++
    [.label succsSym] ++ succsHeader t.succs.length k ++ succEntries.flatten ++ nexts ++
    [.label rseqSym, .quad 0, .label descSym] ++ descItems d)

/-- **The tables as the reader gives them back**: a block's tail names (`Succs.tail`) become
successor addresses after its others, each the address `entry g` of the function's symbol `g`
(none if it has none). -/
def Tables.flatTails (t : Tables) (entry : String → Option Nat) : Tables :=
  { t with succs := t.succs.map fun s =>
      { addr := s.addr, next := s.next ++ s.tail.filterMap entry } }

/-- **The label of text address `a`** for the tables: the last label at `a` (a fresh label at a
point label's address is emitted after it, so it is the one glued to the instruction), never a
granule label (`.Lgw…`, the granule pass's own; the prefix tested on bytes, `startsK`, which
the kernel evaluates). -/
def labelAt (items : List Maps.Item) (a : Nat) : Option String :=
  (items.filterMap fun
    | .label a' l => if a' == a && !startsK l ".Lgw" then some l else none
    | .ins .. => none).getLast?

/-- **The text's labels for the tables, built once**: every label but a granule label, with its
address, last first (so `List.lookup` finds the last label at an address, as `labelAt`).
`labelAt` filters the whole text on each lookup; the serialiser looks up through this list
(`labelIn`) instead, one pass over the text in all. -/
def labelMap (items : List Maps.Item) : List (Nat × String) :=
  (items.filterMap fun
    | .label a l => if startsK l ".Lgw" then none else some (a, l)
    | .ins .. => none).reverse

/-- The label of text address `a` in a label map (`labelMap`). -/
def labelIn (m : List (Nat × String)) (a : Nat) : Option String := m.lookup a

private theorem lookup_eq_head (a : Nat) : ∀ L : List (Nat × String),
    L.lookup a = (L.filterMap fun p => if p.1 == a then some p.2 else none).head?
  | [] => rfl
  | (b, v) :: L => by
    have ih := lookup_eq_head a L
    rw [List.filterMap_cons]
    by_cases h : b = a
    · subst h; simp [List.lookup]
    · have h1 : (b == a) = false := by simpa using h
      have h2 : (a == b) = false := by
        cases hh : a == b
        · rfl
        · exact absurd (beq_iff_eq.mp hh).symm h
      rw [List.lookup, h2, ih]; simp only [h1]; rfl

private theorem lookup_rev_eq (a : Nat) (L : List (Nat × String)) :
    L.reverse.lookup a = (L.filterMap fun p => if p.1 == a then some p.2 else none).getLast? := by
  rw [lookup_eq_head, List.filterMap_reverse, List.head?_reverse]

-- The kernel evaluates the label map (the granule prefix on bytes): the last non-granule label
-- at an address, none at an address with granule labels only.
example : labelIn (labelMap [.label 4 "a", .label 4 ".Lgw0", .label 4 "b", .label 8 ".Lgw1"]) 4 = some "b" ∧
    labelIn (labelMap [.label 4 "a", .label 4 ".Lgw0", .label 4 "b", .label 8 ".Lgw1"]) 8 = none := by
  decide +kernel

/-- The label map gives the label `labelAt` gives. -/
theorem labelIn_labelMap (items : List Maps.Item) (a : Nat) :
    labelIn (labelMap items) a = labelAt items a := by
  unfold labelIn labelMap labelAt
  rw [lookup_rev_eq, List.filterMap_filterMap]
  congr 2
  funext it
  cases it with
  | ins => rfl
  | label a' l =>
    by_cases hg : startsK l ".Lgw" = true
    · simp [hg]
    · simp [hg]

/-! ## The reader -/

/-- **The descriptor's address words**, as absolute addresses (each word plus its own
address); `none` for an absent one (`0`). -/
structure Desc where
  textStart : Nat
  textEnd : Nat
  maps : Nat
  succs : Nat
  rseq : Nat
  stackmap : Option Nat
  msStart : Option Nat
  msRet : Option Nat
  deriving Repr, BEq, Inhabited

/-- An unsigned word (a negative signed word is not a valid count, index or address here). -/
def uword (rd : Nat → Except String Int) (a : Nat) : Except String Nat := do
  let v ← rd a
  if v < 0 then throw s!"gc tables: word {v} at {a} out of range" else pure v.toNat

/-- The absolute address of descriptor word `i` of the descriptor at `desc` (`rd` the signed
word there): the word plus its own address; `none` if the word is 0 (absent). -/
def descWord (rd : Nat → Except String Int) (desc i : Nat) : Except String (Option Nat) := do
  let a := desc + 8 * i
  let v ← rd a
  if v == 0 then return none
  let x := (a : Int) + v
  unless 0 ≤ x && x < 2 ^ 64 do throw s!"gc tables: descriptor word {i} ({v}) out of range"
  pure (some x.toNat)

/-- **The tables of an image**, read from the descriptor at address `desc` through `rd` (the
signed 64-bit word at an address), with the descriptor. Key words in the tables are relative to
`text_start` and must lie in the text; they come back as they are. -/
def readTables (rd : Nat → Except String Int) (desc : Nat) : Except String (Desc × Tables) := do
  let w (i : Nat) := uword rd (desc + 8 * i)
  unless (← w 0) == descMagic do throw "gc tables: no descriptor magic"
  let v ← w 1
  unless v == descVersion do throw s!"gc tables: descriptor version {v}"
  let req (i : Nat) : Except String Nat := do
    match ← descWord rd desc i with
    | some a => pure a
    | none => throw s!"gc tables: descriptor word {i} is 0"
  let d : Desc := ⟨← req 2, ← req 3, ← req 4, ← req 5, ← req 6, ← descWord rd desc 7,
    ← descWord rd desc 8, ← descWord rd desc 9⟩
  let off (o : Nat) : Except String Nat :=
    if d.textStart + o < d.textEnd then pure o
    else throw s!"gc tables: text offset {o} outside the text"
  -- scc_gc_maps
  let mv ← uword rd d.maps
  unless mv == mapsVersion do throw s!"gc tables: maps version {mv}"
  let n ← uword rd (d.maps + 8)
  let r ← uword rd (d.maps + 16)
  let roots := d.maps + 24 + 40 * n
  if n + r > 0 then discard <| rd (roots + 8 * r - 8)  -- its last word is readable
  let maps ← (List.range n).mapM fun i => do
    let e := d.maps + 24 + 40 * i
    let a ← off (← uword rd e)
    let kw ← uword rd (e + 8)
    let nr ← uword rd (e + 16)
    let fst ← uword rd (e + 24)
    let nd ← uword rd (e + 32)
    unless kw / framelessBit < 2 do throw s!"gc tables: kind word {kw} at {a}"
    let fl := kw / framelessBit == 1
    let kind ← match Kind.ofNum? (kw &&& kindMask) with
      | some .seqStart | none => throw s!"gc tables: kind word {kw} at {a}"
      | some k => pure k
    if kind == .call && fl then throw s!"gc tables: a frameless call at {a}"
    unless nd == 0 do throw s!"gc tables: derived pairs at {a}"
    unless fst + nr ≤ r do throw s!"gc tables: roots {fst}+{nr} beyond {r} at {a}"
    let rs ← (List.range nr).mapM fun j => do decRoot (← rd (roots + 8 * (fst + j)))
    pure ({ pt := ⟨kind, a⟩, roots := rs, frameless := fl } : RootMap)
  -- scc_gc_succs
  let m ← uword rd d.succs
  let k ← uword rd (d.succs + 8)
  let nexts := d.succs + 16 + 24 * m
  if m + k > 0 then discard <| rd (nexts + 8 * k - 8)
  let succs ← (List.range m).mapM fun i => do
    let e := d.succs + 16 + 24 * i
    let a ← off (← uword rd e)
    let nn ← uword rd (e + 8)
    let fst ← uword rd (e + 16)
    unless fst + nn ≤ k do throw s!"gc tables: successors {fst}+{nn} beyond {k} at {a}"
    let ns ← (List.range nn).mapM fun j => do off (← uword rd (nexts + 8 * (fst + j)))
    pure ({ addr := a, next := ns } : Succs)
  -- scc_gc_rseq
  unless (← uword rd d.rseq) == 0 do throw "gc tables: restart descriptors are not in format 1"
  pure (d, { maps, succs })

/-- **A word reader on an image** `img` laid out from `base`: the signed little-endian 64-bit
word at an address, or an error outside the image. -/
def imageWord (base : Nat) (img : Array UInt8) (a : Nat) : Except String Int :=
  if base ≤ a && a + 8 ≤ base + img.size then
    let u := Int.ofBytes ((img.extract (a - base) (a - base + 8)).toList)
    pure (if u ≥ 2 ^ 63 then u - 2 ^ 64 else u)
  else throw s!"gc tables: address {a} outside the image"

/-- **Round trip through the bytes**: the tables `t` serialised with `labelOf`, laid out in a
data section from `base` behind the items `pre` (e.g. `scc_stackmap`), resolved with `code` (a
code label's absolute address), and read back from `scc_gc_desc`. -/
def roundTrip (t : Tables) (labelOf : Nat → Option String) (d : DescLabels)
    (code : String → Option Nat) (base : Nat) (pre : List DItem := []) :
    Except String (Desc × Tables) := do
  let items := pre ++ (← tableItems t labelOf d)
  for l in Kraken.DataImage.quadLabels items do
    if (Kraken.DataImage.dataLabel base items l).isNone && (code l).isNone then
      throw s!"gc tables: label {l} does not resolve"
  let res := Kraken.DataImage.resolve (fun l => BitVec.ofNat 64 ((code l).getD 0)) base items
  let img := (Kraken.DataImage.image res base items).toArray
  let some desc := Kraken.DataImage.dataLabel base items descSym | throw "gc tables: no descriptor"
  readTables (imageWord base img) desc

/-! ## Tests -/

/-- A small table with labels `L<a>` at every address; the text at 0x400000, 64 bytes long. -/
def toyTables : Tables :=
  { maps := [{ pt := ⟨.blockEntry, 0⟩, roots := [(.reg 7, .heap)], frameless := true },
             { pt := ⟨.call, 8⟩, roots := [(.reg 7, .heap), (.slot (-8), .stack)] },
             { pt := ⟨.blockEntry, 8⟩, roots := [(.slot (-8), .stack), (.reg 7, .heap)] },
             { pt := ⟨.ret, 12⟩, roots := [(.reg 0, .heap)], frameless := true }],
    succs := [{ addr := 0, next := [8] }, { addr := 8, next := [12] }, { addr := 12, next := [] }] }

def toyLabel (a : Nat) : Option String := some s!"L{a}"
def toyDesc : DescLabels := { stackmap := some "sm" }
/-- The toy's code labels with the text at `0x400000 + s`. -/
def toyCodeAt (s : Nat) (l : String) : Option Nat :=
  (match l with
    | "scc_text_start" => some 0
    | "scc_text_end" | "scc_rt_morestack" | ".Lscc_rt_morestack.ret" => some 0x40
    | _ => if l.startsWith "L" then (l.drop 1).toNat? else none).map (0x400000 + s + ·)
def toyCode : String → Option Nat := toyCodeAt 0

/-- The error of a result (`""` if none). -/
def errOf {α : Type} : Except String α → String
  | .error e => e
  | .ok _ => ""

/-- The toy round trip behind a two-word stand-in for `scc_stackmap`. -/
def toyTrip (t : Tables) (lab : Nat → Option String := toyLabel) : Except String (Desc × Tables) :=
  roundTrip t lab toyDesc toyCode 0x600000 [.align 8, .label "sm", .quad 0, .quad 7]

#guard (toyTrip toyTables).toOption == some
  (⟨0x400000, 0x400040, 0x600010, 0x6000f8, 0x600160, some 0x600000, some 0x400040, some 0x400040⟩,
    toyTables)
-- Absent descriptor words 7–9 (`none`: `.quad 0`) read back as absent.
#guard (roundTrip toyTables toyLabel { stackmap := none, msStart := none, msRet := none } toyCode
    0x600000).toOption.map (fun (d, t) => (d.stackmap, d.msStart, d.msRet, t == toyTables)) ==
  some (none, none, none, true)
-- Refused: an unlabelled address, a restart descriptor, a derived pair, a frameless call.
#guard errOf (toyTrip toyTables (fun a => if a == 12 then none else toyLabel a)) == "gc tables: no label at address 12"
#guard errOf (toyTrip { toyTables with rseq := [⟨0, 4, 8⟩] }) == "gc tables: restart descriptors are not in format 1"
-- A tail name is one more successor word, the function's symbol: read back, the target's entry
-- (`L12` here, at 12); a tail name the text does not define is refused.
/-- The toy with a tail jump from the block at 8 to the function at 12 (`L12`). -/
def toyTail : Tables :=
  { toyTables with succs := [{ addr := 0, next := [8] }, { addr := 8, next := [], tail := ["L12"] },
                             { addr := 12, next := [] }] }
#guard (toyTrip toyTail).toOption.map (·.2) ==
  some (toyTail.flatTails fun g => if g == "L12" then some 12 else none)
#guard (toyTrip toyTail).toOption.map (·.2.succs.map (·.next)) == some [[8], [12], []]
#guard errOf (roundTrip toyTail toyLabel toyDesc toyCode 0x600000 [.align 8, .label "sm", .quad 0, .quad 7]) == ""
#guard errOf (tableItems toyTail toyLabel toyDesc (fun g => g != "L12")) ==
  "gc tables: no label L12 (a tail successor at 8)"
/-- The toy with its call map changed by `f`. -/
def toyCall (f : RootMap → RootMap) : Tables := { toyTables with maps := toyTables.maps.modify 1 f }

#guard errOf (toyTrip (toyCall fun m => { m with derived := [⟨.reg 1, .reg 7⟩] })) == "gc tables: derived pairs at 8 are not in format 1"
#guard errOf (toyTrip (toyCall fun m => { m with frameless := true })) == "gc tables: a frameless call map at 8"
-- The bytes: the maps header is at 0x600010 (after the 16 bytes of `sm`), the kind words of
-- the toy's entries are 256, 1, 0, 258, the roots start at 0x600010 + 24 + 4 · 40, `scc_gc_succs`
-- at 0x6000f8 (after 6 root words), `scc_gc_rseq` at 0x600160, `scc_gc_desc` at 0x600168.
/-- The toy's image with the text at `0x400000 + s` and the data at `0x600000 + s`. -/
def toyImage (s : Nat := 0) : Array UInt8 :=
  match tableItems toyTables toyLabel toyDesc with
  | .ok its =>
    let items := [.align 8, .label "sm", .quad 0, .quad 7] ++ its
    let res := Kraken.DataImage.resolve (fun l => BitVec.ofNat 64 ((toyCodeAt s l).getD 0))
      (0x600000 + s) items
    (Kraken.DataImage.image res (0x600000 + s) items).toArray
  | .error _ => #[]
/-- The words of the toy's image from address `a` on (`n` words). -/
def toyWords (a n : Nat) : List Int :=
  (List.range n).filterMap fun i => (imageWord 0x600000 toyImage (a + 8 * i)).toOption
-- Key words are text offsets (the first map's `pt` is 0) ...
#guard toyWords 0x600010 8 == [1, 4, 6, 0, 256, 1, 0, 0]
#guard toyWords (0x600010 + 24 + 160) 6 == [28, 28, -29, -29, 28, 0]
#guard toyWords 0x6000f8 8 == [3, 2, 0, 1, 0, 8, 1, 1]
-- ... and descriptor words 2–9 are each label minus the word's own address (0x600178 on).
#guard toyWords 0x600160 11 == [0, (descMagic : Int), 1, 0x400000 - 0x600178, 0x400040 - 0x600180,
  0x600010 - 0x600188, 0x6000f8 - 0x600190, 0x600160 - 0x600198, 0x600000 - 0x6001a0,
  0x400040 - 0x6001a8, 0x400040 - 0x6001b0]
-- Position independence: the unit moved by a granule multiple has the same bytes.
#guard toyImage 0x30000 == toyImage 0 && (toyImage 0).size == 0x1b8

/-- The toy's image with the word at `a` replaced by `v`, read back. -/
def toyPatched (a : Nat) (v : Int) : Except String (Desc × Tables) :=
  match tableItems toyTables toyLabel toyDesc with
  | .ok its =>
    let items := [.align 8, .label "sm", .quad 0, .quad 7] ++ its
    let res := Kraken.DataImage.resolve (fun l => BitVec.ofNat 64 ((toyCode l).getD 0)) 0x600000 items
    let img := (Kraken.DataImage.image res 0x600000 items).toArray
    readTables (fun x => if x == a then pure v else imageWord 0x600000 img x) 0x600168
  | .error e => throw e

#guard (toyPatched 0 0).toOption.isSome
-- Refused: wrong magic, descriptor or maps version, kind 3, bit 9, a frameless call,
-- n_derived ≠ 0, first + n > R, first + n > K, a non-empty rseq, a key outside the text (at
-- its end, or a negative word), a descriptor word 2–6 of 0, a descriptor word below address 0.
#guard errOf (toyPatched 0x600168 0) == "gc tables: no descriptor magic"
#guard errOf (toyPatched 0x600170 2) == "gc tables: descriptor version 2"
#guard errOf (toyPatched 0x600010 2) == "gc tables: maps version 2"
#guard errOf (toyPatched (0x600028 + 8) 3) == "gc tables: kind word 3 at 0"
#guard errOf (toyPatched (0x600028 + 8) 512) == "gc tables: kind word 512 at 0"
#guard errOf (toyPatched (0x600028 + 40 + 8) 257) == "gc tables: a frameless call at 8"
#guard errOf (toyPatched (0x600028 + 32) 1) == "gc tables: derived pairs at 0"
#guard errOf (toyPatched (0x600028 + 24) 6) == "gc tables: roots 6+1 beyond 6 at 0"
#guard errOf (toyPatched (0x6000f8 + 16 + 24 + 16) 2) == "gc tables: successors 2+1 beyond 2 at 8"
#guard errOf (toyPatched 0x600160 1) == "gc tables: restart descriptors are not in format 1"
#guard errOf (toyPatched 0x600028 0x40) == "gc tables: text offset 64 outside the text"
#guard errOf (toyPatched 0x600028 (-8)) == "gc tables: word -8 at 6291496 out of range"
#guard errOf (toyPatched 0x600178 0) == "gc tables: descriptor word 2 is 0"
#guard errOf (toyPatched 0x600188 (-0x600189)) == "gc tables: descriptor word 4 (-6291849) out of range"
-- An absent word 7–9 reads as absent.
#guard (toyPatched 0x6001a8 0).toOption.map (·.1.msStart) == some none

end Scc.Cert.Maps
