import Scc.Emit.GranuleA64
import Scc.Emit.A64
import Scc.Cert.MapsA64
import Scc.Frontend
import Scc.Lower.Program
import Scc.Emit.A64Test
import Scc.Test.Src

/-!
# The granule pass is invisible to the AArch64 tables (untrusted, empirical)

The AArch64 analogue of `Scc.Test.GranuleTablesX64`: the stack-map tables
(`Scc.Cert.MapsA64.computeA64`) computed on the text *after* the granule pass, with small test
granules (so that blocks really move), are those computed *before* it, once the pass's own
items are accounted for:

* the pass's labels (`.Lgw<n>`), filler (`.zero k`) and words (`.quad scc_gc_desc - .`), and the
  tail, are erased (the table reader rejects data lines in the text and has no use for the
  labels); an instruction the pass inserted would be kept, so that its effect on blocks,
  leaders and successors is seen (the pass inserts none: every outcome below has 0 jumps);
* every instruction is 4 bytes (no relaxation), sized as the pass laid it out;
* the post-pass tables' addresses are mapped to the pre-pass addresses of the same instruction
  (`back`); an address of an inserted `b` maps to `jumpMark + a`, so a map or successor at an
  inserted jump shows up as a difference.
-/

namespace Scc.Test.GranuleTablesA64
open Scc.Emit.A64 Scc.Emit.Granule Scc.Cert

/-- The rendered line of an item, for alignment. -/
def line (it : Item) : String := it.render

/-- The output without the pass's labels, filler, words and tail, and for each of its
instructions whether it is an inserted `b`. -/
def erase (inp out : List Item) : List Item × List Bool :=
  let isOwn : Item → Bool
    | .d (.label l) => l.startsWith wordPrefix
    | .raw s => s.startsWith ".zero " || s == wordLine ||
        tailA64.any (fun | .raw t => t == s && s != ".text" | _ => false)
    | _ => false
  let kept := out.filter (!isOwn ·)
  -- align `kept` with `inp`: an instruction of `kept` that is not the next input item is an
  -- inserted `b`
  let rec go : List Item → List Item → List Bool
    | _, [] => []
    | is, k :: ks =>
      let isIns : Bool := match k with | .d (.instr _) => true | _ => false
      match is with
      | i :: is' => if line i == line k then (if isIns then [false] else []) ++ go is' ks
          else (if isIns then [true] else []) ++ go (i :: is') ks
      | [] => (if isIns then [true] else []) ++ go [] ks
  (kept, go inp kept)

/-- The sizes of the instructions of the text part of `items` at their layout. -/
def insSizes (items : List Item) : Except String (List Nat) := do
  let zs ← layout isaA64 items
  pure (((textPart isaA64 items).zip zs).filterMap fun
    | (.d (.instr _), z) => some z
    | _ => none)

/-- The instruction addresses of laid-out sizes. -/
def addrs (zs : List Nat) : List Nat :=
  (zs.foldl (fun (a, acc) z => (a + z, a :: acc)) (0, [])).2.reverse

/-- Where an address of an inserted jump goes. -/
def jumpMark : Nat := 1000000000

/-- Map a post-pass address back: the pre-pass address of the first post-pass instruction at
or after it (`jumpMark + a` for an inserted jump), or the end of the pre-pass text. -/
def back (post : List (Nat × Bool)) (pre : List Nat) (preEnd : Nat) (a : Nat) : Nat :=
  let rec go : List (Nat × Bool) → List Nat → Nat
    | (p, ins) :: ps, qs =>
      if p ≥ a then (if ins then jumpMark + a else qs.headD preEnd)
      else go ps (if ins then qs else qs.tail)
    | [], _ => preEnd
  go post pre

/-- The tables with every address mapped by `f`. -/
def mapTables (f : Nat → Nat) (t : Maps.Tables) : Maps.Tables :=
  { t with maps := t.maps.map fun m => { m with pt := { m.pt with addr := f m.pt.addr } },
           succs := t.succs.map fun s => { s with addr := f s.addr, next := s.next.map f } }

/-- The outcome on one program with granule size `gs`. -/
structure Outcome where
  words : Nat
  jumps : Nat
  /-- Non-vacuity: the number of maps and successor entries of the pre-pass tables. -/
  nMaps : Nat
  nSuccs : Nat
  /-- Non-vacuity: the post-pass tables *before* mapping addresses back differ from the
  pre-pass ones (blocks really moved). -/
  moved : Bool
  mapsEq : Bool
  succsEq : Bool
  deriving Repr, BEq

def outcome (p : IR.Program) (gs : Nat) : Except String Outcome := do
  let items ← emitItems p
  let out ← granuleWith isaA64 gs (pointsA64 p) items
  let (kept, insFlags) := erase items out
  let zPre ← insSizes items
  let zPost ← insSizes kept
  let tPre ← MapsA64.computeA64 p items
  let tPost ← MapsA64.computeA64 p kept
  let back' := back ((addrs zPost).zip insFlags) (addrs zPre) zPre.sum
  let tBack := mapTables back' tPost
  let words := out.countP fun | .d (.label l) => l.startsWith wordPrefix | _ => false
  pure { words, jumps := insFlags.countP id, nMaps := tPre.maps.length,
         nSuccs := tPre.succs.length,
         moved := !(tPost.maps == tPre.maps && tPost.succs == tPre.succs),
         mapsEq := tBack.maps == tPre.maps, succsEq := tBack.succs == tPre.succs }

/-- The IR of a WeakCore source text for AArch64. -/
def compileIR (src : String) : Except String IR.Program := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error _ => throw "frontend"
  Lower.lowerProgram { arch := .arm } c

def progs : List (String × Except String IR.Program) :=
  [("helloIR", .ok Scc.Emit.A64.Test.helloIR),
   ("hello1", compileIR (w_src% "Scc/Test/hello1.w")),
   ("hello", compileIR (w_src% "Scc/Test/hello.w")),
   ("wake", compileIR (w_src% "Scc/Test/wake.w"))]

def run (gs : Nat) : List (String × Except String Outcome) :=
  progs.map fun (n, p) => (n, p >>= (outcome · gs))

/-- The expected outcome: `helloIR` has no stack-map descriptor (the tables reader rejects it
before and after the pass alike); on the compiled programs the pass inserts words (more than
one: blocks moved) and no jump, and mapped back the tables are the pre-pass ones. The raw
post-pass tables are not required to differ (`moved`): on these programs they are already
equal to the pre-pass ones (no inserted `b`), so the check is the mapped-back equality. -/
def expected (gs : Nat) : Bool :=
  (run gs).all fun
    | ("helloIR", r) => match r with | .error e => e == "no scc_stackmap" | .ok _ => false
    | (_, .ok o) => o.words > 1 && o.jumps == 0 && o.nMaps > 0 && o.nSuccs > 0 &&
        o.mapsEq && o.succsEq
    | (_, .error _) => false

#guard expected 384
#guard expected 512
#guard expected 1024

-- The counts at 384-byte granules (non-vacuity, as of this commit).
#guard (run 384).map (fun (n, r) => (n, r.toOption.map (fun o => (o.words, o.jumps)))) ==
  [("helloIR", none), ("hello1", some (16, 0)), ("hello", some (20, 0)), ("wake", some (18, 0))]

-- At 256 bytes the `wc_rodata` block does not fit: the pass fails closed rather than enter it
-- by a jump.
#guard (run 256).map (fun (n, r) => (n, match r with | .error e => e | .ok _ => "ok")) ==
  [("helloIR", "no scc_stackmap"),
   ("hello1", "granule: block wc_rodata (260 bytes) does not fit a granule"),
   ("hello", "granule: block wc_rodata (264 bytes) does not fit a granule"), ("wake", "ok")]

end Scc.Test.GranuleTablesA64
