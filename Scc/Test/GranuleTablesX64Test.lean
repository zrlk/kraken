import Scc.Emit.GranuleX64
import Scc.Emit.X64
import Scc.Cert.MapsX64
import Scc.Frontend
import Scc.Lower.Program
import Scc.Emit.X64Test
import Scc.Test.Src

/-!
# The granule pass is invisible to the x64 tables (untrusted, empirical)

The pipeline computes the stack-map tables (`Scc.Cert.MapsX64.computeX64`) on the text
*before* the granule pass. This test checks, on real programs with small test granules (so
that blocks really move), that computing them *after* the pass gives the same tables once the
pass's own items are accounted for:

* the pass's labels (`.Lgw<n>`), filler and words, and the tail, are erased (the table reader
  charges a directive line nothing and has no use for the labels); an instruction the pass
  inserted would be kept, so that its effect on blocks, leaders and successors is seen (the
  pass inserts none: every outcome below has 0 jumps);
* every instruction is sized as the pass laid it out (a `jcc`/`jmp` may change width when its
  target moves);
* the post-pass tables' addresses are mapped to the pre-pass addresses of the same
  instruction (`back`); an address of an inserted jump maps to `jumpMark + a`, so a map or
  successor at an inserted jump shows up as a difference.

Equal maps and successors then say: the tables of the text are those of its pre-pass form,
up to the renaming of addresses that label-keyed tables abstract away.
-/

namespace Scc.Test.GranuleTablesX64
open Scc.Emit.X64 Scc.Emit.Granule Scc.Cert

/-- The lines of items, for alignment. -/
def line (it : Item) : String := it.line?.getD "?"

/-- The output without the pass's labels, filler, words and tail, and for each of its
instructions whether it is an inserted jump. -/
def erase (inp out : List Item) : List Item × List Bool :=
  let isOwn : Item → Bool
    | .d (.label l) => l.startsWith wordPrefix
    | .dir s => s.startsWith ".zero " || s == wordLine ||
        tailX64.any (fun | .dir t => t == s && s != ".text" | _ => false)
    | _ => false
  let kept := out.filter (!isOwn ·)
  -- align `kept` with `inp`: an item of `kept` that is not the next input item is an
  -- inserted jump
  let rec go : List Item → List Item → List Bool
    | _, [] => []
    | is, k :: ks =>
      let isIns : Bool := match k with | .d (.label _) => false | .d _ => true | _ => false
      match is with
      | i :: is' => if line i == line k then (if isIns then [false] else []) ++ go is' ks
          else (if isIns then [true] else []) ++ go (i :: is') ks
      | [] => (if isIns then [true] else []) ++ go [] ks
  (kept, go inp kept)

/-- The sizes of the instructions of the text part of `items` at their layout. -/
def insSizes (items : List Item) : Except String (List Nat) := do
  let zs ← layout isaX64 items
  pure (((textPart isaX64 items).zip zs).filterMap fun
    | (.d (.label _), _) => none
    | (.d _, z) => some z
    | _ => none)

/-- The instruction addresses of laid-out sizes. -/
def addrs (zs : List Nat) : List Nat := (zs.foldl (fun (a, acc) z => (a + z, a :: acc)) (0, [])).2.reverse

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

/-- The outcome on one program with granule size `gs`: the number of words and inserted jumps,
and whether maps and successors agree. -/
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
  let out ← granuleWith isaX64 gs (pointsX64 p) items
  let (kept, insFlags) := erase items out
  let zPre ← insSizes items
  let zPost ← insSizes out
  let tPre ← MapsX64.computeX64 p items zPre
  let tPost ← MapsX64.computeX64 p kept zPost
  let preAs := addrs zPre
  let postAs := addrs zPost
  let back' := back (postAs.zip insFlags) preAs zPre.sum
  let tBack := mapTables back' tPost
  let words := out.countP fun | .d (.label l) => l.startsWith wordPrefix | _ => false
  pure { words, jumps := insFlags.countP id, nMaps := tPre.maps.length,
         nSuccs := tPre.succs.length,
         moved := !(tPost.maps == tPre.maps && tPost.succs == tPre.succs),
         mapsEq := tBack.maps == tPre.maps,
         succsEq := tBack.succs == tPre.succs }

/-- The IR of a WeakCore source text for x64. -/
def compileIR (src : String) : Except String IR.Program := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error _ => throw "frontend"
  Lower.lowerProgram { arch := .x64 } c

def progs : List (String × Except String IR.Program) :=
  [("helloIR", .ok Scc.Emit.X64.Test.helloIR),
   ("hello1", compileIR (w_src% "Scc/Test/hello1.w")),
   ("hello", compileIR (w_src% "Scc/Test/hello.w")),
   ("wake", compileIR (w_src% "Scc/Test/wake.w"))]

def run (gs : Nat) : List (String × Except String Outcome) :=
  progs.map fun (n, p) => (n, p >>= (outcome · gs))

/-- The expected outcome: `helloIR` has no stack-map descriptor (the tables reader rejects it
before and after the pass alike); on the compiled programs the pass inserts words and no jump,
the raw post-pass tables differ (blocks moved), and mapped back they are the pre-pass ones. -/
def expected (gs : Nat) : Bool :=
  (run gs).all fun
    | ("helloIR", r) => match r with | .error e => e == "no scc_stackmap" | .ok _ => false
    | (_, .ok o) => o.words > 1 && o.jumps == 0 && o.nMaps > 0 && o.nSuccs > 0 && o.moved &&
        o.mapsEq && o.succsEq
    | (_, .error _) => false

#guard expected 1024

-- The counts at 1024-byte granules (non-vacuity, as of this commit).
#guard (run 1024).map (fun (n, r) => (n, r.toOption.map (fun o => (o.words, o.jumps)))) ==
  [("helloIR", none), ("hello1", some (6, 0)), ("hello", some (6, 0)), ("wake", some (6, 0))]

-- At smaller granules the pass fails closed rather than enter a block by a jump: a `ud2` does
-- not end the flow (as in the loader's block check), so the runtime's abort tail glues to the
-- first user function and `_start` to `scc_rt_start`/`scc_rt_main`; at 512 bytes `hello` and
-- `wake` still place.
#guard (run 512).map (fun (n, r) => (n, match r with | .error e => e | .ok o => s!"ok {o.words} {o.jumps}")) ==
  [("helloIR", "no scc_stackmap"),
   ("hello1", "granule: block .Lscc_rt_abort.next9 (515 bytes) does not fit a granule"),
   ("hello", "ok 13 0"), ("wake", "ok 13 0")]
#guard (run 512).all fun
  | ("hello", .ok o) | ("wake", .ok o) => o.moved && o.mapsEq && o.succsEq
  | _ => true
#guard (run 384).map (fun (n, r) => (n, match r with | .error e => e | .ok _ => "ok")) ==
  [("helloIR", "no scc_stackmap"),
   ("hello1", "granule: block .Lscc_rt_abort.next9 (515 bytes) does not fit a granule"),
   ("hello", "granule: block .Lscc_rt_abort.next9 (498 bytes) does not fit a granule"),
   ("wake", "granule: block .Lscc_rt_abort.next9 (466 bytes) does not fit a granule")]
#guard (run 256).map (fun (n, r) => (n, match r with | .error e => e | .ok _ => "ok")) ==
  [("helloIR", "no scc_stackmap"), ("hello1", "granule: block _start (266 bytes) does not fit a granule"),
   ("hello", "granule: block _start (266 bytes) does not fit a granule"),
   ("wake", "granule: block .Lscc_rt_abort.next9 (466 bytes) does not fit a granule")]

end Scc.Test.GranuleTablesX64
