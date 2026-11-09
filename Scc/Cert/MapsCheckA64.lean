import Scc.Cert.MapsRtA64
import Scc.Cert.MapsRtConstA64

/-!
# scc's check of the tables on AArch64 (untrusted)

The AArch64 twin of `Scc.Cert.MapsCheckX64`. Before it writes a text, scc puts
the tables together from the constant routines' constants `consts? cfg` resolved on the text
(else `rtTablesOf`) and the non-constant functions' tables on two text ranges (`computeSplit`),
merges them in address order (`mergeTables`), and refuses (`checkTables` fails, so the CLI exits
with status 2) unless the result equals the full text's tables (`computeA64`) and is
`Tables.g1Ok`. A wrong constant or a wrong split therefore causes a refusal, never a wrong
table. It also refuses a call whose read result's tag in the caller differs from the callee's
result tag (`checkResultTags`), and tables whose frame state (`RootMap.frameless`) disagrees
with the text's prologues and epilogues (`frameCheck`). (Every AArch64 instruction is 4 bytes.)
-/

namespace Scc.Cert.MapsA64
open Maps

/-- **Two parts' tables merged** in address order, as `compute` merges its functions' tables
(stable, so the order of a block entry and a call map at one address is kept). -/
def mergeTables (a b : Tables) : Tables :=
  { maps := sortStable (fun x y => decide (x.pt.addr ≤ y.pt.addr)) (a.maps ++ b.maps),
    succs := sortStable (fun x y => decide (x.addr ≤ y.addr)) (a.succs ++ b.succs) }

/-- **Result-tag agreement** at every call `ds ← g(..)` from `f` of a program function `g` that
has a `ret`. Its results' tags are those of the operands of its first `ret` (as `resultTags`;
`tagsOf` checks that its `ret`s agree), a list `hts` with one entry per result register, in
order. The rule, per position `i`:

* `ds` and `hts` must have the same length (else refusal);
* if `f` reads `ds[i]` (anywhere in its body), `f`'s tag of `ds[i]` must equal `hts[i]`, in both
  directions (a tag `f` lacks is a missing root; a tag `g` lacks roots a non-pointer);
* if `f` never reads `ds[i]` (an unused result), position `i` is not compared, so a heap result
  that the caller drops is not a refusal.

Calls of routines that are not program functions are not compared. The tags are trusted from
the IR; this catches a callee and a caller that disagree, as the allocator once (result
untagged, destination heap) and `scc_rt_main` once (`rodata`'s result heap, destination
untagged) did. -/
def checkResultTags (p : IR.Program) : Except String Unit :=
  p.funcs.forM fun f => do
    let reads := f.blocks.flatMap fun b =>
      b.insts.flatMap IR.StackMap.instUses ++ IR.StackMap.termUses b.term
    f.blocks.forM fun b => b.insts.forM fun
      | .call ds g _ => match p.funcs.find? (·.name == g) with
        | none => pure ()
        | some h => do
          let hts := (h.blocks.findSome? fun b => match b.term with
            | .ret vs => some (vs.map fun | .reg v => tagOf h v | .imm _ => none)
            | _ => none).getD []
          unless hts.isEmpty || ds.length == hts.length do
            throw s!"tables: {f.name}'s call of {g}: {ds.length} destinations for {hts.length} results"
          (ds.zip hts).forM fun (d, ht) =>
            unless !reads.contains d || tagOf f d == ht do
              throw s!"tables: {f.name}'s call of {g}: result {d}'s tag differs from {g}'s"
      | _ => pure ()

/-! ## The frame state -/

/-- The instructions of the text with their addresses, counted as `itemsOf` counts them (from
address `a`, `.p2align` included), up to the first section switch. -/
def insDirs : List Scc.Emit.A64.Item → Nat → List (Nat × Directive)
  | [], _ => []
  | .raw s :: rest, a =>
    if endsText s then [] else match p2alignOf? s with
      | some k => insDirs rest ((a + 2 ^ k - 1) / 2 ^ k * 2 ^ k)
      | none => insDirs rest a
  | .d (.label _) :: rest, a => insDirs rest a
  | .d d :: rest, a => (a, d) :: insDirs rest (a + 4)
  | .comment _ :: rest, a => insDirs rest a

/-- The prologue's first instruction: the frame's allocation `sub sp, sp, #F`, the stack check's
`sub x9, sp, #F`, or (a frame beyond the immediate range) `movz x16, ..` of `addImm`. -/
def isFrameAlloc : Directive → Bool
  | .instr ⟨_, .SUB_e d s (.imm _)⟩ => isSp s && (isSp d || spReg d == some .X9)
  | .instr ⟨_, .MOVZ d _ _⟩ => zrReg d == some .X16
  | _ => false

/-- The epilogue's last instruction before `ret`: the frame's release `add sp, sp, ..`. -/
def isFrameFree : Directive → Bool
  | .instr ⟨_, .ADD_e d s _⟩ => isSp d && isSp s
  | _ => false

/-- `ret`. -/
def isRet : Directive → Bool
  | .instr ⟨_, .RET _⟩ => true
  | _ => false

/-- **The frame state against the text** (`RootMap.frameless`): a map is frameless exactly if it
is a `ret`'s or the block entry at an IR function's symbol; every such function has that map; a
frameless block entry is on the frame's allocation (`isFrameAlloc`: the frame record is not set
up yet), a `ret`'s map on a `ret` right after the frame's release (`isFrameFree`: it is torn
down), and no other map is on an allocation. The tables are built that way (`fnMapsW`); this
guards the rule against the emitted text. -/
def frameCheck (p : IR.Program) (its : List Scc.Emit.A64.Item) (items : List Item) (t : Tables) :
    Except String Unit := do
  let ds := insDirs its 0
  let at? (a : Nat) : Option Directive := ds.lookup a
  -- `before?` scans the text from the start on each call (quadratic in the text over all ret
  -- maps); fine at fixture sizes, an index would make it linear.
  let before? (a : Nat) : Option Directive := ((ds.takeWhile (·.1 != a)).getLast?).map (·.2)
  let entries ← p.funcs.mapM fun f => match labelAddr items f.name with
    | some a => pure a
    | none => throw s!"tables: no label {f.name}"
  for (f, a) in p.funcs.zip entries do
    unless t.maps.any (fun m => m.pt.kind == .blockEntry && m.pt.addr == a && m.frameless) do
      throw s!"tables: {f.name}'s entry {a} has no frameless block entry"
  for m in t.maps do
    let a := m.pt.addr
    let want := m.pt.kind == .ret || (m.pt.kind == .blockEntry && entries.contains a)
    unless m.frameless == want do throw s!"tables: the map at {a} is {if want then "not " else ""}frameless"
    if m.frameless then
      if m.pt.kind == .ret then
        unless (at? a).any isRet && (before? a).any isFrameFree do
          throw s!"tables: the frameless ret map at {a} is not on add sp, sp, ..; ret"
      else unless (at? a).any isFrameAlloc do
        throw s!"tables: the frameless block entry at {a} is not on the frame's allocation"
    else if (at? a).any isFrameAlloc then
      throw s!"tables: the map at {a} is on the frame's allocation but not frameless"

/-- **The check with constants `c`**: the constant routines' tables (`c` resolved on the text,
else `rtTablesOf`) merged with `computeSplit`'s equal `computeA64`'s tables, which are
`g1Ok`, their frame state agrees with the text (`frameCheck`), the certificate's checker
accepts them with scc's liveness witnesses (`checkW`, `witness`), and the program's result tags
agree (`checkResultTags`). -/
def checkTablesWith (c : Option RTables) (p : IR.Program) (its : List Scc.Emit.A64.Item)
    (ms : List (String × List Int × List Int)) : Except String Unit := do
  let items ← itemsOf its
  let rt ← match c.bind (·.resolve endL items) with
    | some t => pure t
    | none => rtTablesOf p its
  let user ← computeSplit p its ms
  let full ← computeA64 p its
  unless mergeTables rt user == full do
    throw "tables: the constant routines' and the split tables differ from the text's"
  unless full.g1Ok do throw "tables: not of the format's shape"
  frameCheck p its items full
  -- the certificate's checker accepts these tables with scc's liveness witnesses (the
  -- reference liveness is a post-fixpoint: its iteration converged)
  let (items', fns) ← fnTagsA64 p its
  unless checkW fns items' (witness fns items') full do
    throw "tables: the liveness witnesses are no post-fixpoint, or their tables differ"
  checkResultTags p

/-- **The check scc runs** for configuration `cfg` (see the module docstring). -/
def checkTables (cfg : Config) (p : IR.Program) (its : List Scc.Emit.A64.Item)
    (ms : List (String × List Int × List Int)) : Except String Unit :=
  checkTablesWith (Scc.Cert.MapsRtA64.consts? cfg) p its ms

end Scc.Cert.MapsA64
