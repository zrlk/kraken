import WeakCore.RWLock

/-!
# Caps — one library for every holder

`Cap s r` is a zero-width, copyable capability for region `r`:

* `pub` — the region is published memory (`openPub`); first-class.
* `bor` — a token lent for a scope (`borrow .bor t` … `endBorrow t`); pub
  discipline on `rgn r`: loads, stores, cell `cas`, with `acq`/`rel` on
  view-sensitive types.  Second-class: passed, never stored or returned.
* `rd`  — a token or read share lent for a scope; loads only.  Second-class.

`pub ≤ bor ≤ rd` by subsumption, so a helper asks for the *weakest* capability
it needs and every holder can call it: a token holder lends, a share holder
lends `rd`, and published memory is opened.  While lent, the token or share is
used up; `endBorrow` gives it back and drops the second-class capabilities.
-/

namespace Caps
open CoreLang CoreTerm TermRun TermSmoke RWLock

def rgnInt : Ty := .ptr (.rgn (.var 0)) .int

/-! ## The helpers, written once -/

/-- Read under any capability. -/
def getD : Decl where
  name := "get"; idx := ["r"]; arg := "a"
  argTy := .prod rgnInt (.cap .rd (.var 0)); retTy := .int
  body := .split (v "a") "p" "c" (lets [("x", .load false (v "p"))] (.ret (v "x")))

/-- Increment by `cas` under a capability that writes. -/
def incrD : Decl where
  name := "incr"; idx := ["r"]; arg := "a"
  argTy := .prod rgnInt (.cap .bor (.var 0)); retTy := .unit
  body := .split (v "a") "p" "c"
    (lets [("x", .load false (v "p")), ("y", .add (v "x") (.lit 1))]
      (.cas false false (v "p") (v "x") (v "y") "t" (.ret .unit)
        (lets [("q", .pair (v "p") (v "c"))] (.tail "incr" ["r"] (v "q")))))

/-! ## Four kinds of caller -/

/-- Own data: make it a region, lend the token, take it back, store under it. -/
def ownUseD (extra : List (String × Op) := []) (afterEnd : List (String × Op) := []) : Decl where
  name := "ownUse"; idx := []; arg := "x"; argTy := .int; retTy := .int
  body := lets [("p", .new (v "x"))]
    (.region (v "p") "r" "d" "t"
      (lets ([("c", .borrow .bor (v "t")), ("q", .pair (v "d") (v "c")),
              ("u", .call "incr" ["r"] (v "q"))] ++ extra ++
             [("q2", .pair (v "d") (v "c")), ("y", .call "get" ["r"] (v "q2")),
              ("e", .endBorrow (v "t"))] ++ afterEnd ++
             [("u2", .store false (v "d") (.lit 7) none)])
        (.ret (v "y"))))

/-- A readers–writer reader: lend its share `rd`. -/
def rdReadD (lend : Cap := .rd) (f : String := "get") : Decl where
  name := "rdRead"; idx := ["r"]; arg := "m"; argTy := cell rwP .int; retTy := .int
  body := lets [("s", .call "readLock" ["r"] (v "m")),
                ("d0", .fld 1 (v "m")), ("d", .load false (v "d0")),
                ("c", .borrow lend (v "s")), ("q", .pair (v "d") (v "c")), ("x", .call f ["r"] (v "q")),
                ("e", .endBorrow (v "s")),
                ("p", .pair (v "m") (v "s")), ("u", .call "readUnlock" ["r"] (v "p"))]
    (.ret (v "x"))

/-- A readers–writer writer: lend its token `bor`. -/
def rdWriteD : Decl where
  name := "rdWrite"; idx := ["r"]; arg := "m"; argTy := cell rwP .int; retTy := .unit
  body := lets [("t", .call "writeLock" ["r"] (v "m")),
                ("d0", .fld 1 (v "m")), ("d", .load false (v "d0")),
                ("c", .borrow .bor (v "t")), ("q", .pair (v "d") (v "c")), ("u", .call "incr" ["r"] (v "q")),
                ("e", .endBorrow (v "t")),
                ("p", .pair (v "m") (v "t")), ("u3", .call "writeUnlock" ["r"] (v "p"))]
    (.ret .unit)

/-- Published memory: open it as a region with a `pub` capability. -/
def pubUseD : Decl where
  name := "pubUse"; idx := []; arg := "g"; argTy := .ptr .pub .int; retTy := .int
  body := .openPub (v "g") "r" "p" "c"
    (lets [("q", .pair (v "p") (v "c")), ("u", .call "incr" ["r"] (v "q")),
           ("q2", .pair (v "p") (v "c")), ("x", .call "get" ["r"] (v "q2"))] (.ret (v "x")))

def mkPubD : Decl where
  name := "mkPub"; idx := []; arg := "x"; argTy := .int; retTy := .ptr .pub .int
  body := lets [("p", .new (v "x")), ("g", .publish (v "p"))] (.ret (v "g"))

def capLib : Prog := [getD, incrD, ownUseD, rdReadD, rdWriteD, pubUseD, mkPubD] ++ rwLib

#guard accepts (checkProg capLib)

/-! ## Hazards, each refused for its reason -/

-- A borrowed capability returned: it would outlive the loan.
#guard rejects (checkDecl [] (dcl "leak" (.prod rgnInt (.cap .bor (.var 0))) (.cap .bor (.var 0))
    (.split (v "a") "p" "c" (.ret (v "c"))) ["r"])) "may be passed, not returned or stored"
-- … or stored.
#guard rejects (checkDecl capLib (ownUseD [("h", .new (v "c"))])) "second-class capability cannot be stored"
-- … or smuggled through a type parameter.
def idD : Decl where
  name := "id"; tparams := [{}]; idx := []; arg := "a"; argTy := .tvar 0; retTy := .tvar 0
  body := .ret (v "a")
#guard accepts (checkDecl [] idD)
#guard rejects (checkDecl (idD :: capLib)
    (ownUseD [("h", .call "id" [] (v "c") [.cap .bor (.var 0)])]))
  "a type argument does not have its parameter's kind"
-- The token used while it is lent.
#guard rejects (checkDecl capLib (ownUseD [("z", .atom (v "t"))])) "already used (affine)"
-- The capability used after the loan ends.
#guard rejects (checkDecl capLib (ownUseD [] [("q3", .pair (v "d") (v "c"))])) "unbound variable c"
-- Taking back what was never lent.
#guard rejects (checkDecl capLib (ownUseD [("e0", .endBorrow (v "d"))])) "nothing is lent"
-- A read share lends only `rd`, and `rd` does not write.
#guard rejects (checkDecl capLib (rdReadD .bor)) "a read share lends only rd"
#guard rejects (checkDecl capLib (rdReadD .rd "incr")) "call incr: argument type mismatch"
#guard rejects (checkDecl [] (dcl "setRd" (.prod rgnInt (.cap .rd (.var 0))) .unit
    (.split (v "a") "p" "c" (lets [("u", .store false (v "p") (.lit 1) none)] (.ret .unit))) ["r"]))
  "store into a region without its token"
-- A `pub` capability is first-class: it may be returned and stored.
#guard accepts (checkDecl [] (dcl "keep" (.cap .pub (.var 0)) (.cap .pub (.var 0)) (.ret (v "a")) ["r"]))
#guard accepts (checkDecl [] (dcl "keep2" (.cap .pub (.var 0)) (.ptr .own (.cap .pub (.var 0)))
    (lets [("h", .new (v "a"))] (.ret (v "h"))) ["r"]))

/-! ## On the promise machine -/

def pubSetup : Option Setup := runSetup capLib "mkPub" [] .int [cst (.num 0)]
-- Two threads increment the same published counter through the generic helper.
#guard let r := runE capLib pubSetup (fun s =>
    [("pubUse", [], .ptr .pub .int, s.res), ("pubUse", [], .ptr .pub .int, s.res)]) 0
  clean r && (List.range 2).all fun i =>
    (resultsOf r i).all fun x => x == [.num 1] || x == [.num 2]
-- Own data through the same helpers: lent, incremented, read, taken back.
#guard let r := runE capLib pubSetup (fun _ => [("ownUse", [], .int, [cst (.num 3)])]) 0
  clean r && resultsOf r 0 == [[.num 4]]

end Caps
