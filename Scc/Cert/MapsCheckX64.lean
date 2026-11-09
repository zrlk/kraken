import Scc.Cert.MapsRtX64
import Scc.Cert.MapsRtConstX64

/-!
# scc's check of the tables on x64 (untrusted)

Before it writes a text, scc checks that the tables it would emit from the
constants are the tables of the text. The tables it would emit are put together from two parts:

* the constant runtime routines' tables: the constants `consts? cfg`
  (`Scc.Cert.MapsRtConstX64`) resolved on the text, or computed (`rtTablesOf`) if there are no
  constants for the configuration or they do not resolve;
* the non-constant functions' tables on two text ranges (`computeSplit`, with the emitter's
  safepoints).

They are merged in address order (`mergeTables`), and the result must equal the full text's
tables (`computeX64`) and have the format's shape (`Tables.g1Ok`). Otherwise scc refuses the
program (`checkTables` fails, so the CLI exits with status 2). A wrong constant or a wrong split
therefore causes a refusal, never a wrong table. It also refuses a call whose read result's
tag in the caller differs from the callee's result tag (`checkResultTags`), and tables whose
frame state (`RootMap.frameless`) disagrees with the text's prologues and epilogues
(`frameCheck`).

Instruction sizes are all 1 (`unitSizes`). A table is keyed by addresses, but neither the
constants (routine-relative keys, `Scc.Cert.Maps.RKey`) nor the split depend on the sizes, so
one size vector is enough to compare them.
-/

namespace Scc.Cert.MapsX64
open Maps

/-- The number of instructions of the text (up to the first section switch). -/
def textInsCount : List Scc.Emit.X64.Item → Nat
  | [] => 0
  | .dir s :: rest => if endsText s then 0 else textInsCount rest
  | .d (.label _) :: rest => textInsCount rest
  | .d _ :: rest => textInsCount rest + 1
  | _ :: rest => textInsCount rest

/-- Instruction sizes all 1. -/
def unitSizes (its : List Scc.Emit.X64.Item) : List Nat := List.replicate (textInsCount its) 1

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

/-- The instructions of the text with their addresses, counted as `itemsOf` counts them (sizes
`zs`, from address `a`), up to the first section switch. -/
def insDirs : List Scc.Emit.X64.Item → List Nat → Nat → List (Nat × Directive)
  | [], _, _ => []
  | .dir s :: rest, zs, a => if endsText s then [] else insDirs rest zs a
  | .d (.label _) :: rest, zs, a => insDirs rest zs a
  | .d d :: rest, z :: zs, a => (a, d) :: insDirs rest zs (a + z)
  | .d _ :: _, [], _ => []
  | _ :: rest, zs, a => insDirs rest zs a

/-- `pushq %rbp`, the prologue's first instruction. -/
def isPushRbp : Directive → Bool
  | .instr (.regular _ _ (.push (.regOrMem (.reg (.low .rbp _))))) => true
  | _ => false

/-- `popq %rbp`, the epilogue's last instruction before `ret`. -/
def isPopRbp : Directive → Bool
  | .instr (.regular _ _ (.pop (.reg (.low .rbp _)))) => true
  | _ => false

/-- `ret`. -/
def isRet : Directive → Bool
  | .instr (.regular _ _ .ret) => true
  | _ => false

/-- **The frame state against the text** (`RootMap.frameless`): a map is frameless exactly if it
is a `ret`'s or the block entry at an IR function's symbol; every such function has that map; a
frameless block entry is on `pushq %rbp` (the frame record is not set up yet), a `ret`'s map on
a `ret` right after `popq %rbp` (it is torn down), and no other map is on `pushq %rbp`. The
tables are built that way (`fnMapsW`); this guards the rule against the emitted text. -/
def frameCheck (p : IR.Program) (its : List Scc.Emit.X64.Item) (sizes : List Nat)
    (items : List Item) (t : Tables) : Except String Unit := do
  let ds := insDirs its sizes 0
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
        unless (at? a).any isRet && (before? a).any isPopRbp do
          throw s!"tables: the frameless ret map at {a} is not on popq %rbp; ret"
      else unless (at? a).any isPushRbp do
        throw s!"tables: the frameless block entry at {a} is not on pushq %rbp"
    else if (at? a).any isPushRbp then
      throw s!"tables: the map at {a} is on pushq %rbp but not frameless"

/-- **The check with constants `c`**: the constant routines' tables (`c` resolved on the text,
else `rtTablesOf`) merged with `computeSplit`'s equal `computeX64`'s tables, which are
`g1Ok`, their frame state agrees with the text (`frameCheck`), the certificate's checker
accepts them with scc's liveness witnesses (`checkW`, `witness`), and the program's result tags
agree (`checkResultTags`). -/
def checkTablesWith (c : Option RTables) (p : IR.Program) (its : List Scc.Emit.X64.Item)
    (ms : List (String × List Int × List Int)) : Except String Unit := do
  let sizes := unitSizes its
  let items ← itemsOf its sizes
  let rt ← match c.bind (·.resolve endL items) with
    | some t => pure t
    | none => rtTablesOf p its sizes
  let user ← computeSplit p its ms sizes
  let full ← computeX64 p its sizes
  unless mergeTables rt user == full do
    throw "tables: the constant routines' and the split tables differ from the text's"
  unless full.g1Ok do throw "tables: not of the format's shape"
  frameCheck p its sizes items full
  -- the certificate's checker accepts these tables with scc's liveness witnesses (the
  -- reference liveness is a post-fixpoint: its iteration converged)
  let (items', fns) ← fnTagsX64 p its sizes
  unless checkW fns items' (witness fns items') full do
    throw "tables: the liveness witnesses are no post-fixpoint, or their tables differ"
  checkResultTags p

/-- **The check scc runs** for configuration `cfg` (see the module docstring). -/
def checkTables (cfg : Config) (p : IR.Program) (its : List Scc.Emit.X64.Item)
    (ms : List (String × List Int × List Int)) : Except String Unit :=
  checkTablesWith (Scc.Cert.MapsRtX64.consts? cfg) p its ms

end Scc.Cert.MapsX64
