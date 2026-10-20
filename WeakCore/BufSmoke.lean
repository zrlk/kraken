/-
# BufSmoke — §3.7 buffers, checked and run

The checker's buffer rules (`newBuf`, `idx`, `bufInit`, `publish` of a `Buf`,
`ini` weakening), each hazard rejected for its reason, and message passing of
a buffer on the promise machine:
- a non-Zeroable buffer published with `rel`/`acq` never reads `undef`; the same
  program with plain accesses — rejected by the checker (Hole 1) — does;
- a Zeroable buffer may be passed plainly (§3.8's Zeroable row), and reads 0 or
  the value, never `undef`.

Build: LEAN_PATH=build lean BufSmoke.lean   (after TermSmoke.olean)
-/
import WeakCore.TermSmoke
open CoreLang CoreTerm TermRun TermSmoke
open WeakMem (Val)

namespace BufSmoke

/-- A non-Zeroable element: a published pointer. -/
def E : Ty := .ptr .pub .int
def B (μ : Mode) (τ : Ty) (n k : Nat) : Ty := buf μ τ (.lit n) (.lit k)

def dcl (name : String) (argTy retTy : Ty) (body : Expr) (idx : List String := []) : Decl :=
  { name := name, idx := idx, arg := "a", argTy := argTy, retTy := retTy, body := body }

/-! ### The checker -/

/-- Fill a two-slot buffer, in order, and publish it. -/
def fill2 : Decl := dcl "fill2" .int (B .pub E 2 2)
  (lets [("p", .new (v "a")), ("q", .publish (v "p")), ("b", .newBuf (.lit 2) E),
         ("b1", .bufInit (v "b") (.lit 0) (v "q")), ("b2", .bufInit (v "b1") (.lit 1) (v "q")),
         ("bp", .publish (v "b2"))] (.ret (v "bp")))
#guard accepts (checkDecl [] fill2)

def getAt (i : Nat) (ty : Ty := B .pub E 2 2) : Decl := dcl "get" ty .int
  (lets [("l", .idx (v "a") (.lit i)), ("y", .load false (v "l")), ("z", .load false (v "y"))]
    (.ret (v "z")))
#guard accepts (checkDecl [] (getAt 1))
#guard rejects (checkDecl [] (getAt 2)) "not provably below the capacity"
#guard rejects (checkDecl [] (getAt 1 (B .pub E 2 1))) "not provably initialised"

-- `bufInit` writes the next slot, and only while there is room.
#guard rejects (checkDecl [] { fill2 with
    body := lets [("p", .new (v "a")), ("q", .publish (v "p")), ("b", .newBuf (.lit 2) E),
                  ("b1", .bufInit (v "b") (.lit 1) (v "q"))] (.ret .unit), retTy := .unit })
  "not the next uninitialised one"
#guard rejects (checkDecl [] (dcl "full" (.prod (B .own E 1 1) E) .unit
    (.split (v "a") "b" "q" (lets [("b1", .bufInit (v "b") (.lit 1) (v "q"))] (.ret .unit)))))
  "the buffer is full"

-- Affine element types are accepted: `xchg` moves a slot's value out (HashMap.lean).
#guard accepts (checkDecl [] (dcl "aff" .unit .unit
    (lets [("b", .newBuf (.lit 2) (.ptr .own .int))] (.ret .unit))))

-- A locative into an `own` buffer is a second owner, as with `fld`.
#guard rejects (checkDecl [] (dcl "twice" (B .own .int 2 2) .unit
    (lets [("l", .idx (v "a") (.lit 0)), ("m", .idx (v "a") (.lit 1))] (.ret .unit))))
  "already used"

-- Symbolic bounds: `n < n+1`, by the linear test; `n < n` is refused.
def symGet (cap : Idx) : Decl := dcl "sget"
  (.prod (buf .pub E cap cap) (.intS (.var 0))) E
  (.split (v "a") "b" "i" (lets [("l", .idx (v "b") (v "i")), ("y", .load false (v "l"))]
    (.ret (v "y")))) ["n"]
#guard accepts (checkDecl [] (symGet (.add (.var 0) (.lit 1))))
#guard rejects (checkDecl [] (symGet (.var 0))) "not provably below the capacity"

-- Zeroable elements: born initialised, readable at once.
#guard accepts (checkDecl [] (dcl "z" .unit .int
    (lets [("b", .newBuf (.lit 3) .int), ("l", .idx (v "b") (.lit 2)), ("x", .load false (v "l"))]
      (.ret (v "x")))))

/-! #### Crossing threads: Hole 1 is §3.8's rule -/

def cellT : Ty := .ptr .pub (B .pub E 1 1)

/-- The writer gets the cell and the payload (an `Int`, so that `new` makes a
`Ptr own Int` rather than one to a singleton). -/
def wrBody (rel : Bool) (pub : Bool := true) : Expr :=
  .split (v "a") "c" "x"
    (lets ([("p", .new (v "x")), ("q", .publish (v "p")), ("b", .newBuf (.lit 1) E),
            ("b1", .bufInit (v "b") (.lit 0) (v "q"))] ++
           (if pub then [("bp", .publish (v "b1"))] else [("bp", .atom (v "b1"))]) ++
           [("u", .store rel (v "c") (v "bp") none)]) (.ret .unit))
/-- The reader returns the slot's word itself: an `undef` there would otherwise
make the dereference stuck, and a stuck run has no final state to report. -/
def rdBody (acq : Bool) : Expr :=
  lets [("bb", .load acq (v "a")), ("l", .idx (v "bb") (.lit 0)), ("y", .load false (v "l"))]
    (.ret (v "y"))

def mkC : Decl := dcl "mkC" .int cellT
  (lets [("p", .new (v "a")), ("q", .publish (v "p")), ("b", .newBuf (.lit 1) E),
         ("b1", .bufInit (v "b") (.lit 0) (v "q")), ("bp", .publish (v "b1")),
         ("c", .new (v "bp")), ("cp", .publish (v "c"))] (.ret (v "cp")))
def wr (rel : Bool) (pub : Bool := true) : Decl := dcl "wr" (.prod cellT .int) .unit (wrBody rel pub)
def rd (acq : Bool) : Decl := dcl "rd" cellT E (rdBody acq)

def mpGood : Prog := [mkC, wr true, rd true]
def mpPlain : Prog := [mkC, wr false, rd false]
/-- No `publish` and a plain store: the buffer is handed over still `own`. -/
def mpBad : Prog := [mkC, wr false false, rd false]

#guard accepts (checkProg mpGood)
#guard rejects (checkDecl mpPlain (wr false)) "a view-sensitive type needs rel"
#guard rejects (checkDecl mpPlain (rd false)) "a view-sensitive type needs acq"
#guard rejects (checkDecl mpBad (wr false false)) "store: the value does not have the cell's type"

-- The escape hatch: forget the refinement, and the plain store is legal — but
-- the receiver has a bare `Loc`, and cannot index it.
def locT : Ty := .loc .pub (.array (.lit 1) E)
#guard accepts (checkDecl [] (dcl "fwd" (.prod (.ptr .pub locT) (B .pub E 1 1)) .unit
    (.split (v "a") "c" "b" (lets [("u", .store false (v "c") (v "b") none)] (.ret .unit)))))
#guard rejects (checkDecl [] (getAt 0 locT)) "idx needs a buffer"
-- Weakening `ini 2 ≤ ini 1` at a call.
#guard accepts (checkProg [getAt 0 (B .pub E 2 1),
    dcl "caller" (B .pub E 2 2) .int (lets [("r", .call "get" [] (v "a"))] (.ret (v "r")))])

/-! ### The machine -/

def mpSetup (p : Prog) : Option Setup := runSetup p "mkC" [] .int [cst (.num 7)]
def mpThr (s : Setup) : List (String × List Ty × Ty × List Word) :=
  [("wr", [], .prod cellT .int, s.res ++ [cst (.num 42)]), ("rd", [], cellT, s.res)]

def undefSeen (r : Option Explored) : Bool :=
  match r with
  | some r => r.finals.any (·.ths.any (·.undefs > 0))
  | none => false

-- Well typed: the reader gets the old buffer's pointer or the new one's, never `undef`.
#guard let r := runE mpGood (mpSetup mpGood) mpThr 0
  clean r && (resultsOf r 1).length == 2
#guard let r := runE mpGood (mpSetup mpGood) mpThr 1; clean r
-- Unpublished and stored plainly: the writer may promise the cell's store before
-- the slot's initialising one, so the reader indexes a buffer whose only visible
-- message is the `undef` page.  Needs a promise: in order, the address dependency
-- alone would save it.
#guard let r := runE mpBad (mpSetup mpBad) mpThr 1; !r.any (·.cut) && undefSeen r
#guard let r := runE mpBad (mpSetup mpBad) mpThr 0; clean r
-- Finding: published but passed plainly (the checker's Hole 1 rejection), the
-- machine never reads `undef`: `publish`'s `dmb ishst` orders the slot's store
-- before the cell's, and the reader's `idx` is address-dependent on the loaded
-- pointer.  §3.8's rule is conservative here.
#guard let r := runE mpPlain (mpSetup mpPlain) mpThr 1; clean r

/-! #### A Zeroable buffer, passed plainly -/

def cellZ : Ty := .ptr .pub (B .pub .int 1 1)
#guard !(Ty.sensitiveIn [] (B .pub .int 1 1))

def mkZ : Decl := dcl "mkC" .unit cellZ
  (lets [("b", .newBuf (.lit 1) .int), ("bp", .publish (v "b")), ("c", .new (v "bp")),
         ("cp", .publish (v "c"))] (.ret (v "cp")))
def wrZ : Decl := dcl "wr" cellZ .unit
  (lets [("b", .newBuf (.lit 1) .int), ("bp", .publish (v "b")), ("l", .idx (v "bp") (.lit 0)),
         ("u1", .store false (v "l") (.lit 7) none), ("u", .store false (v "a") (v "bp") none)]
    (.ret .unit))
def rdZ : Decl := dcl "rd" cellZ .int
  (lets [("bb", .load false (v "a")), ("l", .idx (v "bb") (.lit 0)), ("z", .load false (v "l"))]
    (.ret (v "z")))
def zProg : Prog := [mkZ, wrZ, rdZ]
#guard accepts (checkProg zProg)

def zSetup : Option Setup := runSetup zProg "mkC" [] .unit []
def zThr (s : Setup) : List (String × List Ty × Ty × List Word) :=
  [("wr", [], cellZ, s.res), ("rd", [], cellZ, s.res)]
-- Pre-zeroed pages: 0 (either buffer, before the 7) or 7, and never `undef`.
#guard let r := runE zProg zSetup zThr 0
  clean r && sameSet (resultsOf r 1) [[.num 0], [.num 7]]
#guard let r := runE zProg zSetup zThr 1; clean r

/-! ### Arrays are not values (T3c-5, D1')

TermRun has no layout for an array, so every one of these used to be accepted
and then stuck at run time. -/

def A2 : Ty := .array (.lit 2) .int
#guard rejects (checkDecl [] (dcl "za" .unit .unit (lets [("z", .zero A2)] (.ret .unit))))
  "array by value"
#guard rejects (checkDecl [] (dcl "ba" .unit .unit (lets [("b", .newBuf (.lit 1) A2)] (.ret .unit))))
  "a slot cannot hold an array"
#guard rejects (checkDecl [] (dcl "la" (.loc .own A2) .unit (lets [("y", .load false (v "a"))] (.ret .unit))))
  "array by value"
-- An inline array in a tuple is an array outside a reference too.
#guard rejects (checkDecl [] (dcl "ta" .unit .unit
    (lets [("z", .zero (.prod .int A2))] (.ret .unit)))) "array by value"
-- A generic load would hold one at `α := Array 2 Int`: the type argument is refused.
def copyK : Kind := { copy := true }
def gl : Decl where
  name := "gl"
  tparams := [copyK]
  idx := []
  arg := "a"
  argTy := .ptr .own (.tvar 0)
  retTy := .unit
  body := lets [("y", .load false (v "a"))] (.ret .unit)
#guard accepts (checkDecl [] gl)
#guard rejects (checkDecl [gl] (dcl "gc" (.ptr .own A2) .unit
    (lets [("r", .call "gl" [] (v "a") [A2])] (.ret .unit)))) "does not have its parameter's kind"
-- Behind a reference an array is fine: a buffer, and a locative to it.
#guard accepts (checkDecl [] (dcl "ok" .unit .unit
    (lets [("b", .newBuf (.lit 2) .int)] (.ret .unit))))

/-! ### Offsets never depend on an unpacked type (T3c-5, D4)

TermRun computes in-allocation offsets from the runtime type, where an unpacked
witness is erased to `Unit`. Each of these used to be accepted and read the wrong
word: the `fld` and `loadAtF` ones returned 7 at type `IntS 9`. -/

def P2 (a : Ty) : Ty := .prod a (.intS (.lit 9))
-- A cell `(7, 9)` packed as `∃α. Ptr own (α × IntS 9)`.
def opqCell (k : Expr) : Expr :=
  lets [("p", .pair (.lit 7) (.lit 9)), ("r", .new (v "p")),
        ("k", .packT (v "r") (.intS (.lit 7)) (.tex {} (.ptr .own (P2 (.tvar 0)))))]
    (.unpackT (v "k") "α" "y" k)
#guard rejects (checkDecl [] (dcl "of" .unit (.intS (.lit 9))
    (opqCell (lets [("l", .fld 1 (v "y")), ("z", .load false (v "l"))] (.ret (v "z"))))))
  "offset depends on an unpacked type"
-- Field 0 is at offset 0 whatever the witness: still fine.
#guard accepts (checkDecl [] (dcl "o0" .unit .unit
    (opqCell (lets [("l", .fld 0 (v "y"))] (.ret .unit)))))
-- A one-slot buffer of `(7, 9)` packed as `∃α. Buf own (α × IntS 9) 1 1`.
def opqBuf (k : Expr) : Expr :=
  lets [("p", .pair (.lit 7) (.lit 9)), ("b", .newBuf (.lit 1) (P2 (.intS (.lit 7)))),
        ("b1", .bufInit (v "b") (.lit 0) (v "p")),
        ("k", .packT (v "b1") (.intS (.lit 7))
          (.tex {} (.refine (.loc .own (.array (.lit 1) (P2 (.tvar 0)))) (.ini (.lit 1)))))]
    (.unpackT (v "k") "α" "y" k)
#guard accepts (checkDecl [] (dcl "ob" .unit .unit (opqBuf (.ret .unit))))
#guard rejects (checkDecl [] (dcl "lf" .unit (.intS (.lit 9))
    (opqBuf (lets [("z", .loadAtF (v "y") (.lit 0) [1])] (.ret (v "z"))))))
  "layout depends on an unpacked type"
#guard rejects (checkDecl [] (dcl "xf" .unit (.intS (.lit 9))
    (opqBuf (lets [("z", .xchgAtF (v "y") (.lit 0) [1] (.lit 9))] (.ret (v "z"))))))
  "layout depends on an unpacked type"
#guard rejects (checkDecl [] (dcl "ix" .unit .unit
    (opqBuf (lets [("l", .idx (v "y") (.lit 0))] (.ret .unit)))))
  "layout depends on an unpacked type"

end BufSmoke
