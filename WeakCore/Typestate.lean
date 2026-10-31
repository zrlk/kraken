/-
# Typestate — ghost protocol words

A **ghost** protocol (`Proto.ghost = true`) runs the same state machine and the same token discipline as a real protocol word, but at compile time only. The word has width 0: it cannot be loaded or `cas`-ed, and stores to it are erased. The state lives in the token's index.

A real word is born in a holding state, and a thread takes the region with `cas`. A ghost word has no runtime value to arbitrate a take, so it is **born taken**: `mkWord` hands back the word and a token already in a non-holding state.

The example is a file handle:
- `open` gives a handle and a token in state `Open`;
- `read` needs that token;
- `close` moves the word to `Closed`.

`Closed` holds the region, so `close` consumes the token. After it, the handle's data is unreachable (use after close is rejected), and there is no token to close with again (double close is rejected).

Build: LEAN_PATH=build lean Typestate.lean   (after TermRun.olean)
-/
import WeakCore.TermRun
open CoreLang CoreTerm TermRun

namespace Typestate

/-- `2k ↦ ∅` (open: the token holder owns the file), `2k+1 ↦ r` (closed: final,
the word takes the region back and nobody can take it out again). -/
def fileP : Proto := ⟨[⟨2, 0, false⟩, ⟨2, 1, true⟩], [(0, 1, 0)], true, [], [], [], false, false, false, false, false, []⟩

#guard pwf fileP
#guard (Ty.word (.lit 0) fileP).words = some 0          -- erased
#guard TermRun.accs (.word (.lit 0) fileP) = some []

/-- A handle at region `r = var 0`: the ghost word, and the file's data. -/
def hndB : Ty := .prod (.ptr .own (.word (.var 0) fileP)) (.ptr (.rgn (.var 0)) .int)
def openTok : Ty := .tok (.var 0) (some (fileP, .lit 0))
def file : Ty := .iex (.prod hndB openTok)

def openF : Decl where
  name := "open"; idx := []; arg := "x"
  argTy := .int
  retTy := file
  body := lets [("p", .new (v "x") (some .int))]
    (.region (v "p") "r" "d" "t0"
      (lets [("wt", .mkWord "r" fileP (.lit 0) (v "t0"))]
        (.split (v "wt") "w" "t"
          (lets [("pw", .new (v "w") (some (.word (.var 0) fileP))), ("h", .pair (v "pw") (v "d")),
                 ("ht", .pair (v "h") (v "t")), ("f", .pack (v "ht") "r" file)]
            (.ret (v "f"))))))

def readF : Decl where
  name := "read"; idx := ["r"]; arg := "a"
  argTy := .prod (.ptr (.rgn (.var 0)) .int) openTok
  retTy := .prod .int openTok
  body := .split (v "a") "d" "t"
    (lets [("x", .load false (v "d")), ("r2", .pair (v "x") (v "t"))] (.ret (v "r2")))

/-- `store 1` takes `Open(0)` to `Closed(0)`, which holds the region: the token
is consumed.  No `rel`: nobody can observe a ghost word. -/
def closeF : Decl where
  name := "close"; idx := ["r"]; arg := "a"
  argTy := .prod hndB openTok
  retTy := .unit
  body := .split (v "a") "h" "t"
    (.split (v "h") "pw" "d"
      (lets [("u", .store false (v "pw") (.lit 1) (some (v "t")))] (.ret .unit)))

/-- A client: open, read, close.  `after` is spliced in after the close, which
is where the hazards below go. -/
def useBody (after : List (String × Op) := []) : Expr :=
  lets [("f", .call "open" [] (v "x"))]
    (.unpack (v "f") "r" "ht"
      (.split (v "ht") "h" "t"
        (.split (v "h") "pw" "d"
          (lets [("a", .pair (v "d") (v "t")), ("xt", .call "read" ["r"] (v "a"))]
            (.split (v "xt") "y" "t2"
              (lets ([("h2", .pair (v "pw") (v "d")), ("a2", .pair (v "h2") (v "t2")),
                      ("u", .call "close" ["r"] (v "a2"))] ++ after)
                (.ret (v "y"))))))))

def useF (after : List (String × Op) := []) : Decl where
  name := "use"; idx := []; arg := "x"
  argTy := .int
  retTy := .int
  body := useBody after

def fileLib : Prog := [openF, readF, closeF, useF]

#guard accepts (checkProg fileLib)

/-! ### The hazards, each rejected for its reason -/

-- Double close: the open token went into the first `close`.
#guard rejects (checkDecl fileLib (useF [("u2", .call "close" ["r"] (v "a2"))])) "already used"

-- Use after close: the data is in region `r`, and nobody holds its token any more.
-- (A ghost word cannot be loaded, so there is no torn-read licence either.)
#guard rejects (checkDecl fileLib (useF [("z", .load false (v "d"))]))
  "load from a region without its token, and no observation of its word"

-- A ghost word has no runtime value: no loads, no `cas`.
#guard rejects (checkDecl fileLib { readF with
    argTy := .prod hndB openTok
    body := .split (v "a") "h" "t"
      (.split (v "h") "pw" "d" (lets [("c", .load true (v "pw"))] (.ret .unit)))
    retTy := .unit }) "no runtime value to load"
#guard rejects (checkDecl fileLib { closeF with
    body := .split (v "a") "h" "t"
      (.split (v "h") "pw" "d"
        (.cas true true (v "pw") (.lit 0) (.lit 1) "k" (.ret .unit) (.ret .unit))) })
  "cas on a ghost word"

-- Born taken: a ghost word may not be born in the state that holds its region.
#guard rejects (checkDecl fileLib { openF with
    body := lets [("p", .new (v "x") (some .int))]
      (.region (v "p") "r" "d" "t0"
        (lets [("wt", .mkWord "r" fileP (.lit 1) (v "t0"))] (.ret .unit)))
    retTy := .unit }) "born in a state that does not hold"

/-- A reopenable file: `Closed` does not hold, so `close` keeps the token, now
at `Closed`, and `reopen` goes back to `Open` at the next version. -/
def fileP2 : Proto := ⟨[⟨2, 0, false⟩, ⟨2, 1, false⟩], [(0, 1, 0), (1, 0, 1)], true, [], [], [], false, false, false, false, false, []⟩

def hndB2 : Ty := .prod (.ptr .own (.word (.var 0) fileP2)) (.ptr (.rgn (.var 0)) .int)
def openTok2 : Ty := .tok (.var 0) (some (fileP2, .lit 0))

/-- Close, reopen, close: every step is a transition. -/
def cycleF : Decl where
  name := "cycle"; idx := ["r"]; arg := "a"
  argTy := .prod hndB2 openTok2
  retTy := .tok (.var 0) (some (fileP2, .lit 3))
  body := .split (v "a") "h" "t"
    (.split (v "h") "pw" "d"
      (lets [("t1", .store false (v "pw") (.lit 1) (some (v "t"))),
             ("t2", .store false (v "pw") (.lit 2) (some (v "t1"))),
             ("t3", .store false (v "pw") (.lit 3) (some (v "t2")))] (.ret (v "t3"))))

#guard accepts (checkDecl [cycleF] cycleF)

-- Double close, with a token in hand: `Closed → Closed` is not a transition.
#guard rejects (checkDecl [cycleF] { cycleF with
    retTy := .unit
    body := .split (v "a") "h" "t"
      (.split (v "h") "pw" "d"
        (lets [("t1", .store false (v "pw") (.lit 1) (some (v "t"))),
               ("t2", .store false (v "pw") (.lit 1) (some (v "t1")))] (.ret .unit))) })
  "not a transition"

-- Reading while closed: the `Closed` token does not match `read`'s `Open` one.
def readWhileClosed : Decl := { cycleF with
    retTy := .unit
    body := .split (v "a") "h" "t"
      (.split (v "h") "pw" "d"
        (lets [("t1", .store false (v "pw") (.lit 1) (some (v "t"))),
               ("a2", .pair (v "d") (v "t1")), ("xt", .call "read" ["r"] (v "a2"))]
          (.ret .unit))) }
#guard rejects (checkDecl (readF :: [cycleF]) readWhileClosed) "call read: argument type mismatch"

/-! ### Run: the ghost word is erased -/

/-- `use 5` alone on the promise machine. -/
def runUse : Option (List WeakMem.Val × Nat × Nat) := do
  let c : Cfg := { mem := #[], ths := #[{ term := .tail "use" [] (v "a") [], env := [("a", .int, [cst (.num 5)])] }] }
  let fin ← (explore fileLib Promises.Knobs.all .arm { maxP := 0 } 80 c).head?
  let th ← fin.ths[0]?
  let res ← match th.term with
    | .ret a => (evalAt th.env a).map (·.2.map (·.val))
    | _ => none
  pure (res, th.undefs, fin.mem.size)

#guard (runUse.map (·.1)) == some [.num 5]
#guard (runUse.map (·.2.1)) == some 0
-- Two messages, both for the data cell (its `undef`, then 5): the ghost word has none.
#guard (runUse.map (·.2.2)) == some 2

end Typestate
