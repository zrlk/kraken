import WeakCore.TermC1Defs
import WeakCore.TermScopeW
import WeakCore.ArrayLib
import WeakCore.BufSmoke
import WeakCore.Caps
import WeakCore.Complete
import WeakCore.CoreTerm
import WeakCore.CoreTyping
import WeakCore.FlatHashMap
import WeakCore.Freeze
import WeakCore.HashMap
import WeakCore.HashMapLF
import WeakCore.HashMapOwn
import WeakCore.RWLock
import WeakCore.Robust
import WeakCore.SubWord
import WeakCore.TermRun
import WeakCore.TermSmoke
import WeakCore.Typestate

/-! # TermC1Guards: region c1 guards as `#guard` lines.

Temporary parallel module: checks the new `TermC1.checkW1` / `TermC1.ProgScopeOKW1` only; nothing
switches.  Deleted (or re-pointed) when the change is adopted.

* 24 negatives (12 `guards`, 10 `guards2`, 2 `guards3`) are rejected by `checkW1` with a `c1:` message;
  20 of them are accepted by today's `TermScope.checkW` (recorded as `#guard`s, so the guards bite).
* positives / controls are accepted by `checkW1`.
* census: on the 51 accepted-program sites (every `#guard accepts (checkProg _)` and every
  `theorem _ : ProgT _`), `ProgScopeOKW p → ProgScopeOKW1 p` (superset, per program and per decl),
  and exactly the 7 rows mutexLib (x2), rwLib, [semAcqD, semRelD], bsemLib 2/0, localLib are newly
  admitted.
* the seqP negatives (`seqTD`) give their token back (`store rel w (c+2)`), so only `monoSaw` rejects
  them (nit).
-/

open CoreLang CoreTerm Syntax TermScope

namespace TermC1Guards

open TermC1

def cx1 (d : Decl) : Cx :=
  { inames := d.idx.reverse, vars := [(d.arg, d.argTy, true)], ret := d.retTy,
    ke := d.tparams.reverse.map some }

/-- `checkW1` accepts the body of `d` in program `p`. -/
def acc1 (p : Prog) (d : Decl) : Bool := checkW1 p (cx1 d) d.body matches .ok _
/-- `checkW1` rejects the body of `d` in program `p` with a `c1:` message. -/
def rej1 (p : Prog) (d : Decl) : Bool :=
  match checkW1 p (cx1 d) d.body with
  | .error e => (e.splitOn "c1:").length > 1
  | .ok _ => false
/-- Today's `TermScope.checkW` accepts the body of `d` in program `p`. -/
def acc0 (p : Prog) (d : Decl) : Bool := checkW p (cx1 d) d.body matches .ok _


private def w (x : String) : At := .var x

/-- int payload, region live, body `b` after `p := new x; region p r d t0`. -/
def gd (n : String) (ity : Ty) (idx : List String) (b : List (String × Op)) (tail : Expr := .ret .unit) : Decl where
  name := n; idx := idx; arg := "x"; argTy := ity; retTy := .unit
  body := lets [("p", .new (w "x"))] (.region (w "p") "r" "d" "t0" (lets b tail))

def tokT : Ty := .tok (.var 0) none

def n3 : Decl where
  name := "n3"; idx := ["q"]; arg := "x"; argTy := .prod .int tokT; retTy := .unit
  body := .split (w "x") "x1" "x2" (lets [("p", .new (w "x1"))] (.region (w "p") "r" "d" "t0"
    (lets [("q", .new (w "x2")), ("z", .intoRgn "r" (w "q"))] (.ret .unit))))

/-- wide iex: ∃i. Int(i)×Int(i)×Int(i) — 3 words, countI 0 = 3, not granule. -/
def wideT : Ty := .iex (.prod (.intS (.var 0)) (.prod (.intS (.var 0)) (.intS (.var 0))))
def narrowT : Ty := .iex (.prod (.intS (.var 0)) (.intS (.var 0)))

def n12 (ty : Ty) (nm : String) : Decl where
  name := nm; idx := []; arg := "x"; argTy := .prod .int ty; retTy := .unit
  body := .split (w "x") "x1" "x2" (lets [("p", .new (w "x1"))] (.region (w "p") "r" "d" "t0"
    (lets [("q", .new (w "x2")), ("z", .intoRgn "r" (w "q"))] (.ret .unit))))

/-- Context decl over region index r: arg = (d : Ptr (rgn r) Int) × (wit × Cap c r). -/
def cxd (nm : String) (wit : Ty) (c : Cap) (b : List (String × Op)) (tail : Expr := .ret .unit) : Decl where
  name := nm; idx := ["r"]; arg := "a"; retTy := .unit
  argTy := .prod (.ptr (.rgn (.var 0)) .int) (.prod wit (.cap c (.var 0)))
  body := .split (w "a") "d" "wc" (.split (w "wc") "wt" "c" (lets b tail))

def shT : Ty := .share (.var 0)

def guards2 : List (String × String × Decl) := [
  ("G-a1 intoRgn wide iex cell", "-", n12 wideT "ga1"),
  ("G-a2 intoRgn narrow iex cell (ctrl)", "+", n12 narrowT "ga2"),
  ("G-b1 share+cap pub: load (ctrl)", "+", cxd "gb1" shT .pub [("y", .load false (w "d"))]),
  ("G-b2 share+cap pub: store", "-", cxd "gb2" shT .pub [("u", .store false (w "d") (.lit 1) none)]),
  ("G-b3 share+cap bor: store", "-", cxd "gb3" shT .bor [("u", .store false (w "d") (.lit 1) none)]),
  ("G-b4 tok+cap bor: store (ctrl)", "+", cxd "gb4" tokT .bor [("u", .store false (w "d") (.lit 1) none)]),
  ("G-b5 tok+cap bor: xchg", "-", cxd "gb5" tokT .bor [("y", .xchg (w "d") (.lit 1))]),
  ("G-b6 tok+cap bor: fetch", "-", cxd "gb6" tokT .bor [("y", .fetch .add false false (w "d") (.lit 1))]),
  ("G-b7 tok+cap bor: cas", "-", cxd "gb7" tokT .bor [] (.cas false false (w "d") (.lit 0) (.lit 1) "t" (.ret .unit) (.ret .unit))),
  ("G-b8 tok+cap pub: xchg", "-", cxd "gb8" tokT .pub [("y", .xchg (w "d") (.lit 1))]),
  ("G-b9 tok+cap pub: cas", "-", cxd "gb9" tokT .pub [] (.cas false false (w "d") (.lit 0) (.lit 1) "t" (.ret .unit) (.ret .unit))),
  ("G-b10 cap bor only (unit wit): load", "-", cxd "gb10" .unit .bor [("y", .load false (w "d"))]),
  ("G-b11 cap bor only (unit wit): store", "-", cxd "gb11" .unit .bor [("u", .store false (w "d") (.lit 1) none)])
]

def guards : List (String × String × Decl) := [
  ("P1 int ld/st under t0", "+", gd "p1" .int [] [("y", .load false (w "d")), ("u", .store false (w "d") (w "y") none)]),
  ("P2 int ld under t0 only", "+", gd "p2" .int [] [("y", .load false (w "d"))]),
  ("N1d tok payload, dead binder (e1: ok)", "+?", gd "n1" tokT ["q"] [("y", .atom (.lit 0))]),
  ("N2d cap pub payload, dead binder (e1: ok)", "+?", gd "n2" (.cap .pub (.var 0)) ["q"] [("y", .atom (.lit 0))]),
  ("N1 tok payload live (d used)", "-", gd "n1l" tokT ["q"] [("y", .atom (w "d"))]),
  ("N2 cap pub payload live (d used)", "-", gd "n2l" (.cap .pub (.var 0)) ["q"] [("y", .atom (w "d"))]),
  ("N2s share payload live (d used)", "-", gd "n2s" (.share (.var 0)) ["q"] [("y", .atom (w "d"))]),
  ("N11 load tok payload under t0", "-", gd "n11" tokT ["q"] [("y", .load false (w "d"))]),
  ("N3 intoRgn of tok cell", "-", n3),
  ("N4 borrow bor t0 then load d", "-", gd "n4" .int [] [("c", .borrow .bor (w "t0")), ("y", .load false (w "d"))]),
  ("N5 borrow bor t0 then store d", "-", gd "n5" .int [] [("c", .borrow .bor (w "t0")), ("u", .store false (w "d") (.lit 1) none)]),
  ("N6 freeze t0 then load d", "-", gd "n6" .int [] [("c", .freeze (w "t0")), ("y", .load false (w "d"))]),
  ("N7 cas at region cell", "-", gd "n7" .int [] [] (.cas false false (w "d") (.lit 0) (.lit 1) "t" (.ret .unit) (.ret .unit))),
  ("N8 xchg at region cell", "-", gd "n8" .int [] [("y", .xchg (w "d") (.lit 1))]),
  ("N9 fetch at region cell", "-", gd "n9" .int [] [("y", .fetch .add false false (w "d") (.lit 1))]),
  ("N10 store after t0 moved away", "-", gd "n10" .int [] [("pp", .pair (w "t0") (.lit 0)), ("u", .store false (w "d") (.lit 1) none)])
]

/-- A region-cell load under the (sealed) lock token after an ordered observation of the word. -/
def tornD (acqW : Bool) (nm : String) : Decl where
  name := nm; idx := ["r"]; arg := "m"; argTy := cell mutexP .int; retTy := .unit
  body := lets [("t", .call "lock" ["r"] (v "m")), ("w", .fld 0 (v "m")), ("c", .load acqW (v "w")),
                ("d0", .fld 1 (v "m")), ("d", .load false (v "d0")), ("x", .load false (v "d")),
                ("p", .pair (v "m") (v "t")), ("u2", .call "unlock" ["r"] (v "p"))] (.ret .unit)
def tornFD : Decl where
  name := "tornF"; idx := ["r"]; arg := "m"; argTy := cell mutexP .int; retTy := .unit
  body := lets [("t", .call "lock" ["r"] (v "m")), ("w", .fld 0 (v "m")), ("c", .load false (v "w")),
                ("f", .fence .ld),
                ("d0", .fld 1 (v "m")), ("d", .load false (v "d0")), ("x", .load false (v "d")),
                ("p", .pair (v "m") (v "t")), ("u2", .call "unlock" ["r"] (v "p"))] (.ret .unit)

/-- seqP (monotone) writer: cas the even counter to odd (token), then an ordered observation of
the same word (`load acq w`, or `load w; fence ld`), then a region load; the token is then given back
(`store rel w (c+2)`), so today's checkW accepts the whole decl and only monoSaw rejects it. -/
def seqTD (fenceForm : Bool) (nm : String) : Decl where
  name := nm; idx := ["r"]; arg := "m"; argTy := cell seqP .int; retTy := .unit
  body := lets [("w", .fld 0 (v "m")), ("c", .load false (v "w"))]
    (.parity (v "c") "k"
      (lets [("c1", .add (v "c") (.lit 1))]
        (.cas true false (v "w") (v "c") (v "c1") "t"
          (lets ((if fenceForm then [("c2", .load false (v "w")), ("f", .fence .ld)]
                  else [("c2", .load true (v "w"))]) ++
                 [("d0", .fld 1 (v "m")), ("d", .load false (v "d0")), ("x", .load false (v "d")),
                  ("c3", .add (v "c1") (.lit 1)), ("u2", .store true (v "w") (v "c3") (some (v "t")))])
            (.ret .unit))
          (.ret .unit)))
      (.ret .unit))

def guards3 : List (String × String × Decl) := [
  ("G-t1 tok + mutexP ordered Saw [load acq w]: region load (non-monotone, ctrl)", "+", tornD true "gt1"),
  ("G-t1f tok + mutexP ordered Saw [load w; fence ld]: region load (ctrl)", "+", tornFD),
  ("G-t3 tok + mutexP unordered Saw: region load (ctrl)", "+", tornD false "gt3"),
  ("G-t4 tok + seqP ordered Saw [load acq w]: region load", "-", seqTD false "gt4"),
  ("G-t2 tok + seqP ordered Saw [load w; fence ld]: region load", "-", seqTD true "gt2")
]


/-- Expectation check: `+`/`+?` accepted by `checkW1`, `-` rejected with `c1:`. -/
def expOK (p : Prog) : String × String × Decl → Bool
  | (_, ex, d) => if ex == "-" then rej1 p d else acc1 p d

def negs (l : List (String × String × Decl)) : List Decl :=
  (l.filter fun (_, ex, _) => ex == "-").map fun (_, _, d) => d

#guard guards.all fun g => expOK [g.2.2] g
#guard guards2.all fun g => expOK [g.2.2] g
#guard guards3.all fun g => expOK (mutexLib ++ [g.2.2]) g
#guard (negs guards).length + (negs guards2).length + (negs guards3).length == 24
-- 20 of the 24 negatives pass today's checkW (N11, N7, N9, N10 are already rejected).
#guard ((negs guards ++ negs guards2).filter fun d => acc0 [d] d).length +
       ((negs guards3).filter fun d => acc0 (mutexLib ++ [d]) d).length == 20
#guard monotone mutexP == false && monotone seqP == true


def corpusAll : List (String × Prog) := [
  ("ArrayLib:640 lib", (open ArrayLib in (lib))),
  ("ArrayLib:641 prog", (open ArrayLib in (prog))),
  ("BufSmoke:104 mpGood", (open BufSmoke in (mpGood))),
  ("BufSmoke:116 [getAt 0 (B .pub E 2 1), dcl 'caller' (B .pub E 2 2) .int (l", (open BufSmoke in ([getAt 0 (B .pub E 2 1), dcl "caller" (B .pub E 2 2) .int (lets [("r", .call "get" [] (v "a"))] (.ret (v "r")))]))),
  ("BufSmoke:162 zProg", (open BufSmoke in (zProg))),
  ("Caps:89 capLib", (open Caps in (capLib))),
  ("Complete:157 w1Prog", (open Complete in (w1Prog))),
  ("CoreTerm:2561 mutexLib", (open CoreTerm in (mutexLib))),
  ("CoreTerm:2633 seqLib", (open CoreTerm in (seqLib))),
  ("CoreTerm:2810 (queueLib .int)", (open CoreTerm in ((queueLib .int)))),
  ("CoreTerm:2812 (queueLib pay)", (open CoreTerm in ((queueLib pay)))),
  ("CoreTerm:2814 (queueLib (.ptr .pub .int))", (open CoreTerm in ((queueLib (.ptr .pub .int))))),
  ("CoreTerm:2879 (polyQueueLib)", (open CoreTerm in ((polyQueueLib)))),
  ("CoreTerm:3050 (claimLib .int true ++ [useClaimedD])", (open CoreTerm in ((claimLib .int true ++ [useClaimedD])))),
  ("CoreTerm:3056 (claimLib .int)", (open CoreTerm in ((claimLib .int)))),
  ("CoreTerm:3197 (pcLib)", (open CoreTerm in ((pcLib)))),
  ("CoreTerm:3250 pcIntLib", (open CoreTerm in (pcIntLib))),
  ("CoreTerm:3310 cloLib", (open CoreTerm in (cloLib))),
  ("CoreTyping:3278 mutexLib", (open CoreTyping in (mutexLib))),
  ("CoreTyping:3281 seqLib", (open CoreTyping in (seqLib))),
  ("CoreTyping:3284 (queueLib .int)", (open CoreTyping in ((queueLib .int)))),
  ("CoreTyping:3287 polyQueueLib", (open CoreTyping in (polyQueueLib))),
  ("CoreTyping:3290 (claimLib .int true ++ [useClaimedD])", (open CoreTyping in ((claimLib .int true ++ [useClaimedD])))),
  ("CoreTyping:3293 pcLib", (open CoreTyping in (pcLib))),
  ("FlatHashMap:392 (lib false)", (open FlatHashMap in ((lib false)))),
  ("FlatHashMap:393 (lib true)", (open FlatHashMap in ((lib true)))),
  ("FlatHashMap:454 (instLib false 9 false)", (open FlatHashMap in ((instLib false 9 false)))),
  ("FlatHashMap:455 (instLib true 20 true)", (open FlatHashMap in ((instLib true 20 true)))),
  ("FlatHashMap:505 (ownLib false)", (open FlatHashMap in ((ownLib false)))),
  ("FlatHashMap:506 (ownLib true)", (open FlatHashMap in ((ownLib true)))),
  ("Freeze:137 frzLib", (open Freeze in (frzLib))),
  ("Freeze:265 frzCLib", (open Freeze in (frzCLib))),
  ("HashMap:266 hmLib", (open HashMap in (hmLib))),
  ("HashMap:314 instLib", (open HashMap in (instLib))),
  ("HashMap:423 intLib", (open HashMap in (intLib))),
  ("HashMap:494 rwProg", (open HashMap in (rwProg))),
  ("HashMapLF:127 lfLib", (open HashMapLF in (lfLib))),
  ("HashMapLF:176 lfProg", (open HashMapLF in (lfProg))),
  ("HashMapOwn:156 ohmLib", (open HashMapOwn in (ohmLib))),
  ("HashMapOwn:197 oInstLib", (open HashMapOwn in (oInstLib))),
  ("RWLock:171 (rwLib)", (open RWLock in ((rwLib)))),
  ("RWLock:254 [semAcqD, semRelD]", (open RWLock in ([semAcqD, semRelD]))),
  ("RWLock:312 (bsemLib 2)", (open RWLock in ((bsemLib 2)))),
  ("RWLock:313 (bsemLib 0)", (open RWLock in ((bsemLib 0)))),
  ("Robust:343 localLib", (open Robust in (localLib))),
  ("SubWord:82 swLib", (open SubWord in (swLib))),
  ("TermRun:1494 progGood", (open TermRun TermRun.MP in (progGood))),
  ("TermSmoke:118 seqProg", (open TermSmoke in (seqProg))),
  ("TermSmoke:235 bProg", (open TermSmoke in (bProg))),
  ("TermSmoke:272 cloProg", (open TermSmoke in (cloProg))),
  ("Typestate:85 fileLib", (open Typestate in (fileLib)))]


/-- The 7 newly admitted rows (by label prefix). -/
def newRows : List String :=
  ["CoreTerm:2561 mutexLib", "CoreTyping:3278 mutexLib", "RWLock:171 (rwLib)",
   "RWLock:254 [semAcqD, semRelD]", "RWLock:312 (bsemLib 2)", "RWLock:313 (bsemLib 0)",
   "Robust:343 localLib"]

def declSuper (p : Prog) : Bool :=
  p.all fun d =>
    !(drf d.argTy && drf d.retTy && allOK d.body && declWrapOK p d) ||
    (drf1 d.argTy && drf1 d.retTy && allOK1 d.body && declWrapOK1 p d)

#guard corpusAll.length == 51
-- superset, per program and per decl
#guard corpusAll.all fun (_, p) => !ProgScopeOKW p || ProgScopeOKW1 p
#guard corpusAll.all fun (_, p) => declSuper p
-- exactly the 7 newly admitted rows
#guard (corpusAll.filter fun (_, p) => !ProgScopeOKW p && ProgScopeOKW1 p).map (·.1) == newRows

end TermC1Guards
