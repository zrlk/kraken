import WeakCore.HashMap

/-!
# Freeze — immutability, derived

Nothing new in the core.  A frozen value is a region whose protocol word has
**no clause that gives the region up**:

* `0` — frozen, no read shares out;
* `2k + 2` — frozen, `k + 1` read shares out (a lending family).

(Even values leave the odd ones free for a control that adds a thaw state.)
Transitions: `0 → 2` and `2k+2 → 2k+4`, each lending one `share r` (`cas` with
`acq`).  There is no transition back down and no non-holding clause, so after
`mkWord` no `cas` or `store` can ever produce the region's token.  Every write
into region memory needs that token, so none can type-check again: the region
is immutable from its birth on.

This is the RW lock with the writer and the reader exit deleted:

* the owner builds the value **while it is own** (plain writes, no protocol);
* `freeze` turns it into a region (the buffer becomes the region, the table
  cell is moved in with `intoRgn`: a region cell holds no `own` reference), births
  the word holding the region, and publishes the handle with a release;
* a reader takes a `share r` once (one `cas acq`), and from then on every read
  is a plain load.  The share is first-class and affine: keep it, pass it on,
  or drop it — it never has to be given back, because nobody waits for it.

Why this is immutability and not merely "read-locked":
`GovernsFrom` — below the publication floor, ordering hides the stale messages
(the reader's `acq` covers the freezing release); at or above it, exclusion
does the rest (no token, so no later writes).

Costs: one `cas` per share taken (not per read).  The counter only grows, so it
has the usual `2⁶³` ceiling on shares ever taken.
-/

namespace Freeze
open CoreLang CoreTerm TermRun TermSmoke HashMap

/-! ## The protocol -/

def frzP : Proto := ⟨[⟨0, 0, true⟩, ⟨2, 2, true⟩], [(0, 1, 0), (1, 1, 1)], false, [1], [], [], false, false, false, false, false, []⟩
#guard pwf frzP

/-- A frozen `τ`: a published handle to the word and the region's contents. -/
def Frozen (τ : Ty) : Ty := guardedBy frzP τ

/-! ## A frozen lookup table -/

def c1 : Idx := .add (.var 0) (.lit 1)
/-- `∃n. Int(n+1) × Buf own Int (n+1) (n+1)`: the table while it is built. -/
def Tab : Ty := .iex (.prod (.intS c1) (buf .own .int c1 c1))
/-- The same table with its buffer in region `r` (an index of the scope outside
the package): what a frozen handle reaches. -/
def TabR (r : Idx) : Ty := .iex (.prod (.intS c1) (buf (.rgn (r.shift 0)) .int c1 c1))
/-- `Ptr pub (Word[r, P] × Ptr r τ)` for a `τ` that names `r` itself (the
innermost index). -/
def cellR (P : Proto) (τ : Ty) : Ty := .ptr .pub (.prod (.word (.var 0) P) (.ptr (.rgn (.var 0)) τ))
/-- A frozen table: `∃r. Ptr pub (Word[r, frz] × Ptr r (TabR r))`. -/
def FrozenTab : Ty := .iex (cellR frzP (TabR (.var 0)))

/-- Open the table's buffer as region `r` (token `t0`), repack the table in
`r` and move its cell in: `d : Ptr r (TabR r)`.  Continue with `k`. -/
def tabIntoRgn (a : String) (k : Expr) : Expr :=
  .unpack (v a) "n" "tp" (.split (v "tp") "cv" "b"
    (.region (v "b") "r" "bb" "t0"
      (lets [("tp2", .pair (v "cv") (v "bb")), ("tb", .pack (v "tp2") "n" (TabR (.var 0))),
             ("cc", .new (v "tb")), ("d", .intoRgn "r" (v "cc"))] k)))

/-- Build `[10, 20, 30, 40]` — mutably, while it is still own. -/
def mkTabD : Decl := dcl "mkTab" .int Tab
  (lets [("z", .nameI (.lit 3)), ("c2", .add (v "z") (.lit 1)), ("b", .newBuf (v "c2") .int),
         ("o0", .xchgAt (v "b") (.lit 0) (.lit 10)), ("o1", .xchgAt (v "b") (.lit 1) (.lit 20)),
         ("o2", .xchgAt (v "b") (.lit 2) (.lit 30)), ("o3", .xchgAt (v "b") (.lit 3) (.lit 40)),
         ("tp", .pair (v "c2") (v "b")), ("t", .pack (v "tp") "z" Tab)] (.ret (v "t")))

/-- Freeze: region, word born at `0` (holding the region, so the token is gone
for good), publish, pack.  The same code as `mkRW`, with `frzP`, for a `τ`
with no `own` reference inside. -/
def freezeD (τ : Ty) : Decl := dcl "freeze" τ (Frozen τ)
  (lets [("p", .new (v "a"))]
    (.region (v "p") "r" "d" "t0"
      (lets [("wv", .mkWord "r" frzP (.lit 0) (v "t0")), ("pr", .pair (v "wv") (v "d")),
             ("s", .new (v "pr")), ("s2", .publish (v "s")), ("fz", .pack (v "s2") "r" (Frozen τ))]
        (.ret (v "fz")))))

/-- Freeze the table: its buffer becomes the region (`tabIntoRgn`), then as
`freeze`. -/
def freezeTabD : Decl := dcl "freeze" Tab FrozenTab
  (tabIntoRgn "a"
    (lets [("wv", .mkWord "r" frzP (.lit 0) (v "t0")), ("pr", .pair (v "wv") (v "d")),
           ("s", .new (v "pr")), ("s2", .publish (v "s")), ("fz", .pack (v "s2") "r" FrozenTab)]
      (.ret (v "fz"))))

/-- Take a read share: `0 → 2` or `2k+2 → 2k+4`, with `acq`.  Retry on contention. -/
def shareD (acq : Bool := true) : Decl where
  name := "share"; idx := ["r"]; arg := "m"
  argTy := cellR frzP (TabR (.var 0))
  retTy := .share (.var 0)
  body :=
    let retry := .tail "share" ["r"] (v "m")
    lets [("w", .fld 0 (v "m")), ("c", .load false (v "w"))]
      (.parity (v "c") "k"
        (.ifeq (v "c") (.lit 0)
          (.cas acq false (v "w") (v "c") (.lit 2) "t" (.ret (v "t")) retry)
          (lets [("c1", .add (v "c") (.lit 2))]
            (.cas acq false (v "w") (v "c") (v "c1") "t" (.ret (v "t")) retry)))
        retry)

/-- Read slot `i mod n` under a share: plain loads only.  The share comes back. -/
def getD : Decl where
  name := "get"; idx := ["r"]; arg := "a"
  argTy := .prod (.share (.var 0)) (.prod (cellR frzP (TabR (.var 0))) .int)
  retTy := .prod (.share (.var 0)) .int
  body := .split (v "a") "s" "a1" (.split (v "a1") "m" "i"
    (lets [("d0", .fld 1 (v "m")), ("d", .load false (v "d0")), ("tb", .load false (v "d"))]
      (.unpack (v "tb") "n" "tt" (.split (v "tt") "cv" "b"
        (lets [("j", .rem (v "i") (v "cv")), ("l", .idx (v "b") (v "j")), ("x", .load false (v "l")),
               ("o", .pair (v "s") (v "x"))] (.ret (v "o")))))))

/-- A reader: one share, two reads, their sum. -/
def useD : Decl := dcl "use" FrozenTab .int
  (.unpack (v "a") "r" "c"
    (lets [("s", .call "share" ["r"] (v "c")), ("q1", .pair (v "c") (.lit 1)), ("w1", .pair (v "s") (v "q1")),
           ("g1", .call "get" ["r"] (v "w1"))]
      (.split (v "g1") "s1" "x1"
        (lets [("q2", .pair (v "c") (.lit 7)), ("w2", .pair (v "s1") (v "q2")), ("g2", .call "get" ["r"] (v "w2"))]
          (.split (v "g2") "s2" "x2" (lets [("y", .bits .wadd (v "x1") (v "x2"))] (.ret (v "y"))))))))

/-- Build and freeze in one go (the setup). -/
def mkFrozenD : Decl := dcl "mkFrozen" .int FrozenTab
  (lets [("t", .call "mkTab" [] (v "a")), ("f", .call "freeze" [] (v "t"))] (.ret (v "f")))

def frzLib : Prog := [mkTabD, freezeTabD, shareD, getD, useD, mkFrozenD]

#guard accepts (checkProg frzLib)
-- The pre-D1 shape — the own table inside the region's cell — is refused: a
-- region cell holds no `own` reference.
#guard rejects (checkDecl frzLib (freezeD Tab)) "not shareable"

/-! ## Hazards: every way back to mutation is refused -/

/-- `get`'s body with one extra operation `op` on slot `l`, under the share. -/
def getWith (op : Op) : Decl := { getD with
  body := .split (v "a") "s" "a1" (.split (v "a1") "m" "i"
    (lets [("d0", .fld 1 (v "m")), ("d", .load false (v "d0")), ("tb", .load false (v "d"))]
      (.unpack (v "tb") "n" "tt" (.split (v "tt") "cv" "b"
        (lets [("j", .rem (v "i") (v "cv")), ("l", .idx (v "b") (v "j")), ("u", op),
               ("x", .load false (v "l")), ("o", .pair (v "s") (v "x"))] (.ret (v "o"))))))) }

-- A store into frozen memory, a share in hand: a share licenses loads only.
#guard rejects (checkDecl frzLib (getWith (.store false (v "l") (.lit 0) none)))
  "store into a region without its token"
-- Nor an exchange.
#guard rejects (checkDecl frzLib (getWith (.xchg (v "l") (.lit 0))))
  "needs its sealed token or a bor capability"
-- Replacing the table pointer itself is a store too.
#guard rejects (checkDecl frzLib (getWith (.store false (v "d") (v "tb") none)))
  "store into a region without its token"
-- Reading without a share.
#guard rejects (checkDecl frzLib { getD with
    argTy := .prod .unit (.prod (cellR frzP (TabR (.var 0))) .int) })
  "load from a region without its token"
-- A share without `acq` would not see the freezing writes.
#guard rejects (checkDecl frzLib (shareD false)) "taking a read share needs acq"
-- No transition takes the region back: `0 → 1` names no state at all …
#guard rejects (checkDecl frzLib (dcl "thaw" (cellR frzP (TabR (.var 0))) .unit
    (lets [("w", .fld 0 (v "a"))]
      (.cas true false (v "w") (.lit 0) (.lit 1) "t" (.ret .unit) (.ret .unit))) ["r"]))
  "the value is in no single state of the protocol"
-- … and giving a share back (`k+2 → k+1`) is not one either: shares are never
-- waited for, so there is nothing to count down to.
#guard rejects (checkDecl frzLib (dcl "unshare" (.prod (cellR frzP (TabR (.var 0))) (.share (.var 0))) .unit
    (.split (v "a") "m" "s" (lets [("w", .fld 0 (v "m")), ("c", .load false (v "w"))]
      (.parity (v "c") "k"
        (.ifeq (v "c") (.lit 0) (.ret .unit)
          (lets [("d", .sub (v "c") (.lit 2))]
            (.ifeq (v "d") (.lit 0)
              (.cas false true (v "w") (v "c") (.lit 0) "u" (.ret .unit) (.ret .unit))
              (.cas false true (v "w") (v "c") (v "d") "u" (.ret .unit) (.ret .unit)))))
        (.ret .unit)))) ["r"]))
  "not a transition of the protocol"

/-- The control: the same protocol plus a thaw clause (`1`, not holding) and a
transition `0 → 1`.  Now a `cas` hands out the token, and the store goes
through — so it is the protocol's shape, nothing else, that freezes. -/
def thawP : Proto := ⟨[⟨0, 0, true⟩, ⟨2, 2, true⟩, ⟨0, 1, false⟩], [(0, 1, 0), (1, 1, 1), (0, 2, 0)],
  false, [1], [], [], false, false, false, false, false, []⟩
#guard pwf thawP
#guard accepts (checkDecl [] (dcl "thaw" (cellR thawP (TabR (.var 0))) .unit
    (lets [("w", .fld 0 (v "a"))]
      (.cas true false (v "w") (.lit 0) (.lit 1) "t"
        (lets [("d0", .fld 1 (v "a")), ("d", .load false (v "d0")), ("tb", .load false (v "d"))]
          (.unpack (v "tb") "n" "tt" (.split (v "tt") "cv" "b"
            (lets [("l", .idx (v "b") (.lit 0)), ("f", .fence .st),
                   ("u", .store false (v "l") (.lit 5) none)] (.ret .unit)))))
        (.ret .unit))) ["r"]))

/-! ## On the promise machine: two readers of one frozen table -/

def frzSetup : Option Setup := runSetup frzLib "mkFrozen" [] .int [cst (.num 0)]
#guard frzSetup.isSome

-- Each reader takes its own share (the two `cas`es race; the loser retries) and
-- reads slots 1 and 3: `20 + 40`, in every execution.
#guard let r := runE frzLib frzSetup (fun s => [("use", [], FrozenTab, s.res), ("use", [], FrozenTab, s.res)]) 0
  clean r && resultsOf r 0 == [[.num 60]] && resultsOf r 1 == [[.num 60]]

/-! ## `Cap.frz`: the zero-cost frozen share

One core change instead of a protocol: `freeze t` spends a **fresh** region
token for good and hands back `Cap frz r` — first-class, copyable, zero-width,
read-only.  Fresh means no word was ever born for `r` (`mkWord` eats the fresh
token), and no borrow is out (`borrow` eats the token until `endBorrow`), so
after `freeze` nothing can ever write `r` again.  Readers pay nothing per
share: no `cas`, no counter, no ceiling.  The ordering is paid once, where the
handle travels: `Cap frz` is view-sensitive, so it crosses threads by rel/acq
(or inside a `publish`), and whoever holds it has seen the initialising stores.
-/

/-- `∃r. Cap frz r × Ptr (rgn r) τ`: a frozen `τ`, copyable. -/
def FrzH (τ : Ty) : Ty := .iex (.prod (.cap .frz (.var 0)) (.ptr (.rgn (.var 0)) (τ.shiftI 0)))
/-- Its body, for code that has `r` as an index parameter. -/
def frzBody (τ : Ty) : Ty := .prod (.cap .frz (.var 0)) (.ptr (.rgn (.var 0)) τ)
/-- The frozen table, by capability: `∃r. Cap frz r × Ptr r (TabR r)`. -/
def FrzHTab : Ty := .iex (frzBody (TabR (.var 0)))

/-- Freeze: region, `freeze` the fresh token, pack.  No word, no publish. -/
def freezeCD (τ : Ty) : Decl := dcl "freezeC" τ (FrzH τ)
  (lets [("p", .new (v "a"))]
    (.region (v "p") "r" "d" "t0"
      (lets [("c", .freeze (v "t0")), ("h", .pair (v "c") (v "d")), ("fz", .pack (v "h") "r" (FrzH τ))]
        (.ret (v "fz")))))

/-- The table: its buffer becomes the region, then `freeze`. -/
def freezeCTabD : Decl := dcl "freezeC" Tab FrzHTab
  (tabIntoRgn "a"
    (lets [("c", .freeze (v "t0")), ("h", .pair (v "c") (v "d")), ("fz", .pack (v "h") "r" FrzHTab)]
      (.ret (v "fz"))))

/-- Read slot `i mod n` under the frozen capability: plain loads, nothing to give back. -/
def getCD : Decl where
  name := "getC"; idx := ["r"]; arg := "a"
  argTy := .prod (frzBody (TabR (.var 0))) .int
  retTy := .int
  body := .split (v "a") "h" "i" (.split (v "h") "c" "d"
    (lets [("tb", .load false (v "d"))]
      (.unpack (v "tb") "n" "tt" (.split (v "tt") "cv" "b"
        (lets [("j", .rem (v "i") (v "cv")), ("l", .idx (v "b") (v "j")), ("x", .load false (v "l"))]
          (.ret (v "x")))))))

/-- A reader: the handle is copied into both calls; two plain reads, their sum. -/
def useCD : Decl := dcl "useC" FrzHTab .int
  (.unpack (v "a") "r" "h"
    (lets [("q1", .pair (v "h") (.lit 1)), ("x1", .call "getC" ["r"] (v "q1")),
           ("q2", .pair (v "h") (.lit 7)), ("x2", .call "getC" ["r"] (v "q2")),
           ("y", .bits .wadd (v "x1") (v "x2"))] (.ret (v "y"))))

def mkFrozenCD : Decl := dcl "mkFrozenC" .int FrzHTab
  (lets [("t", .call "mkTab" [] (v "a")), ("f", .call "freezeC" [] (v "t"))] (.ret (v "f")))

def frzCLib : Prog := [mkTabD, freezeCTabD, getCD, useCD, mkFrozenCD]

#guard accepts (checkProg frzCLib)

/-! ### The handle crosses threads by rel/acq -/

/-- Stash a frozen handle in published memory. -/
def stashD (rel : Bool) : Decl := dcl "stash" (.prod (.ptr .pub FrzHTab) FrzHTab) .unit
  (.split (v "a") "p" "h" (lets [("u", .store rel (v "p") (v "h") none)] (.ret .unit)))
/-- Fetch one. -/
def grabD (acq : Bool) : Decl := dcl "grab" (.ptr .pub FrzHTab) FrzHTab
  (lets [("h", .load acq (v "a"))] (.ret (v "h")))

#guard accepts (checkDecl frzCLib (stashD true))
#guard accepts (checkDecl frzCLib (grabD true))
#guard rejects (checkDecl frzCLib (stashD false)) "a view-sensitive type needs rel"
#guard rejects (checkDecl frzCLib (grabD false)) "a view-sensitive type needs acq"

/-! ### Hazards -/

/-- `getC`'s body with one extra operation `op` on slot `l`. -/
def getCWith (op : Op) : Decl := { getCD with
  body := .split (v "a") "h" "i" (.split (v "h") "c" "d"
    (lets [("tb", .load false (v "d"))]
      (.unpack (v "tb") "n" "tt" (.split (v "tt") "cv" "b"
        (lets [("j", .rem (v "i") (v "cv")), ("l", .idx (v "b") (v "j")), ("u", op),
               ("x", .load false (v "l"))] (.ret (v "x"))))))) }

-- `frz` licenses loads only: no store, no exchange, not even of the table pointer.
#guard rejects (checkDecl frzCLib (getCWith (.store false (v "l") (.lit 0) none)))
  "store into a region without its token"
#guard rejects (checkDecl frzCLib (getCWith (.xchg (v "l") (.lit 0))))
  "needs its sealed token or a bor capability"
#guard rejects (checkDecl frzCLib (getCWith (.store true (v "d") (v "tb") none)))
  "store into a region without its token"
-- Reading without the capability.
#guard rejects (checkDecl frzCLib { getCD with
    argTy := .prod (.prod .unit (.ptr (.rgn (.var 0)) (TabR (.var 0)))) .int })
  "load from a region without its token"

/-- `freezeC`'s region body with `extra` spliced in after `freeze`. -/
def freezeWith (pre post : List (String × Op)) : Decl := dcl "freezeC" Tab FrzHTab
  (tabIntoRgn "a"
    (lets (pre ++ [("c", .freeze (v "t0"))] ++ post ++
           [("h", .pair (v "c") (v "d")), ("fz", .pack (v "h") "r" FrzHTab)])
      (.ret (v "fz"))))

-- The freezer cannot write either, once frozen: the token is gone.
#guard accepts (checkDecl frzCLib (freezeWith [] []))
#guard rejects (checkDecl frzCLib (freezeWith [] [("q", .load false (v "d")),
    ("u", .store false (v "d") (v "q") none)])) "store into a region without its token"
-- Freezing twice: the token was spent.
#guard rejects (checkDecl frzCLib (freezeWith [] [("c2", .freeze (v "t0"))])) "t0 was already used"
-- A word already born: `mkWord` ate the fresh token.
#guard rejects (checkDecl frzCLib (freezeWith [("wv", .mkWord "r" frzP (.lit 0) (v "t0"))] []))
  "t0 was already used"
-- `borrow` cannot mint `frz`.
#guard rejects (checkDecl frzCLib (freezeWith [("c", .borrow .frz (v "t0"))] []))
  "not frz"
-- While lent (`borrow rd`), the token is out: nothing to freeze.
#guard rejects (checkDecl frzCLib (freezeWith [("k", .borrow .rd (v "t0"))] [])) "t0 was already used"

/-- Freeze a token passed in. -/
def frzTokD (tk : Option (Proto × Idx)) : Decl := dcl "frzTok" (.tok (.var 0) tk) (.cap .frz (.var 0))
  (lets [("c", .freeze (v "a"))] (.ret (v "c"))) ["r"]
#guard accepts (checkDecl [] (frzTokD none))
-- A taken token (from a `cas` on the region's word) cannot be frozen: others
-- may hold shares, or the word may hand the region to a writer later.
#guard rejects (checkDecl [] (frzTokD (some (mutexP, .lit 1)))) "fresh region token, not a taken one"
-- `pub` does not grant `frz`: a `pub` region may still be written by others.
#guard rejects (checkDecl [] (dcl "pubFrz" (.cap .pub (.var 0)) (.cap .frz (.var 0)) (.ret (v "a")) ["r"]))
  "ret: the value does not have the return type"
#guard !Cap.le .pub .frz && Cap.le .frz .rd && !Cap.le .frz .pub

/-! ### On the promise machine: two readers, no `cas` anywhere -/

def frzCSetup : Option Setup := runSetup frzCLib "mkFrozenC" [] .int [cst (.num 0)]
#guard frzCSetup.isSome

def frzCThr (s : Setup) := [("useC", ([] : List Ty), FrzHTab, s.res), ("useC", ([] : List Ty), FrzHTab, s.res)]
#guard let r := runE frzCLib frzCSetup frzCThr 0
  clean r && resultsOf r 0 == [[.num 60]] && resultsOf r 1 == [[.num 60]]

end Freeze
