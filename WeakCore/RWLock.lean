/-
# RWLock — signed transitions, `ifeq` learning, and read shares

Readers–writer items 1–4 (see the `rwlock_implications` notes):
1. transitions carry a signed count step `dk`; a negative step is checked as
   `k = k' + |dk|`, so no subtraction appears in the index language;
2. `ifeq x 0` teaches both branches: `u = 0` in the true branch when `x` is
   `(s+1)·u`, and `u = u' + 1` for a fresh `u'` in the false branch;
3. `sub a b`, typed only where `b ≤ a` follows from the facts;
4. **read shares**: `Share r` is an affine, zero-width permission to *load*
   from region `r`.  A protocol's `lends` clauses are holding states whose
   parameter counts outstanding shares (`k + 1`); a `cas` into or up such a
   family lends one (`acq`), a `cas` down or out takes one back (`rel`), and
   no `cas` may take the region from a lending state.  The readers–writer
   lock and a counting semaphore are then library code.

Build: LEAN_PATH=build lean RWLock.lean   (after TermSmoke.olean)
-/
import WeakCore.TermSmoke
open CoreLang CoreTerm TermRun TermSmoke
open WeakMem (Val)

namespace RWLock

/-! ### Item 1: signed transitions -/

/-- A bare counter that only counts down. -/
def downP : Proto := ⟨[⟨1, 0, true⟩], [(0, 0, -1)], false, [], [], [], false, false, false, false, false, []⟩
#guard pwf downP
#guard pstep downP 0 (.ofConst 3) 0 (.ofConst 2)
#guard !pstep downP 0 (.ofConst 3) 0 (.ofConst 4)
-- Symbolically: from `k'+1` down to `k'`.
#guard pstep downP 0 ((Lin.ofVar 0).add (.ofConst 1)) 0 (.ofVar 0)
#guard !pstep downP 0 (.ofVar 0) 0 ((Lin.ofVar 0).add (.ofConst 1))
-- A step down has no version measure.
#guard !monotone downP
#guard monotone ⟨[⟨1, 0, true⟩], [(0, 0, 1)], false, [], [], [], false, false, false, false, false, []⟩

/-! ### Item 2: `ifeq x 0` teaches both branches -/

def dcl (name : String) (argTy retTy : Ty) (body : Expr) (idx : List String := []) : Decl :=
  { name := name, idx := idx, arg := "a", argTy := argTy, retTy := retTy, body := body }

/-- Read slot 0 of a buffer of symbolic size `n`, guarded by `n ≠ 0`: the false
branch knows `n = n' + 1`, so `0 < n`. -/
def first (guard : Bool) : Decl := dcl "first"
  (.prod (buf .pub .int (.var 0) (.var 0)) (.intS (.var 0))) .int
  (.split (v "a") "b" "n"
    (let rd := lets [("l", .idx (v "b") (.lit 0)), ("y", .load false (v "l"))] (.ret (v "y"))
     if guard then .ifeq (v "n") (.lit 0) (.ret (.lit 0)) rd else rd)) ["n"]
#guard accepts (checkDecl [] (first true))
#guard rejects (checkDecl [] (first false)) "not provably below the capacity"

/-- The true branch of `2·n = 0` knows `n = 0`, so `2·n : Int 0`. -/
def zero (c : Nat) : Decl := dcl "zero" (.intS (.var 0)) (.intS (.lit 0))
  (lets [("d", .add (v "a") (v "a"))]
    (.ifeq (v "d") (.lit c) (.ret (v "d")) (.ret (.lit 0)))) ["n"]
#guard accepts (checkDecl [] (zero 0))
-- `2·n = 2` is not a fact the index language can record (it would need `n = 1`
-- by division), so it is refused rather than silently ignored.
#guard rejects (checkDecl [] (zero 2)) "cannot record the equality"
-- The false branch learns `n = n'+1`, so `2·n` there is not `Int 0`.
#guard rejects (checkDecl [] (dcl "zn" (.intS (.var 0)) (.intS (.lit 0))
    (lets [("d", .add (v "a") (v "a"))] (.ifeq (v "d") (.lit 0) (.ret (v "d")) (.ret (v "d"))))
    ["n"])) "does not have the return type"

/-! ### Items 3–4: the readers–writer lock

`0` free, `1` writer, `2k+2` for `k+1` readers.  Readers hold `Share r`; the
writer holds the token.  Reader entry and exit are `cas`es between holding
states, so the protocol, not a separate counter, bounds the readers. -/

def rwP : Proto :=
  ⟨[⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨2, 2, true⟩],
   [(0, 1, 0), (1, 0, 0), (0, 2, 0), (2, 2, 1), (2, 2, -1), (2, 0, 0)], false, [2], [], [], false, false, false, false, false, []⟩
#guard pwf rwP && !monotone rwP
-- A lending clause must be a holding one.
#guard !pwf { rwP with lends := [1] }

def retryL : Expr := .tail "readLock" ["r"] (v "m")

/-- Parity splits free/readers from writer; `ifeq c 0` splits free (`k = 0`)
from readers (`k = k'+1`), and each branch's `cas` target is then a state. -/
def readLockD (acq : Bool := true) (up : Nat := 2) : Decl where
  name := "readLock"; idx := ["r"]; arg := "m"
  argTy := cell rwP .int
  retTy := .share (.var 0)
  body := lets [("w", .fld 0 (v "m")), ("c", .load false (v "w"))]
    (.parity (v "c") "k"
      (.ifeq (v "c") (.lit 0)
        (.cas acq false (v "w") (v "c") (.lit 2) "t" (.ret (v "t")) retryL)
        (lets [("c2", .add (v "c") (.lit up))]
          (.cas acq false (v "w") (v "c") (v "c2") "t" (.ret (v "t")) retryL)))
      retryL)

def retryU : Expr := lets [("p", .pair (v "m") (v "s"))] (.tail "readUnlock" ["r"] (v "p"))

/-- `c = 2k'+2`; `d = c − 2 = 2k'`; `ifeq d 0` picks leaving (to free) or
counting down.  The `cas` consumes the share `s` on success only. -/
def readUnlockD (rel : Bool := true) (down : Nat := 2) : Decl where
  name := "readUnlock"; idx := ["r"]; arg := "a"
  argTy := .prod (cell rwP .int) (.share (.var 0))
  retTy := .unit
  body := .split (v "a") "m" "s" (lets [("w", .fld 0 (v "m")), ("c", .load false (v "w"))]
    (.parity (v "c") "k"
      (.ifeq (v "c") (.lit 0) retryU
        (lets [("d", .sub (v "c") (.lit down))]
          (.ifeq (v "d") (.lit 0)
            (.cas false rel (v "w") (v "c") (.lit 0) "u" (.ret .unit) retryU)
            (.cas false rel (v "w") (v "c") (v "d") "u" (.ret .unit) retryU))))
      retryU))

def writeLockD : Decl where
  name := "writeLock"; idx := ["r"]; arg := "m"
  argTy := cell rwP .int
  retTy := .tok (.var 0) (some (rwP, .lit 1))
  body := lets [("w", .fld 0 (v "m"))]
    (.cas true false (v "w") (.lit 0) (.lit 1) "t" (.ret (v "t")) (.tail "writeLock" ["r"] (v "m")))

def writeUnlockD : Decl where
  name := "writeUnlock"; idx := ["r"]; arg := "a"
  argTy := .prod (cell rwP .int) (.tok (.var 0) (some (rwP, .lit 1)))
  retTy := .unit
  body := .split (v "a") "m" "t"
    (lets [("w", .fld 0 (v "m")), ("u", .store true (v "w") (.lit 0) (some (v "t")))] (.ret .unit))

/-- A reader: the payload is loaded under the share. -/
def readD : Decl where
  name := "read"; idx := ["r"]; arg := "m"
  argTy := cell rwP .int
  retTy := .int
  body := lets [("s", .call "readLock" ["r"] (v "m")),
                ("d0", .fld 1 (v "m")), ("d", .load false (v "d0")), ("x", .load false (v "d")),
                ("p", .pair (v "m") (v "s")), ("u", .call "readUnlock" ["r"] (v "p"))]
    (.ret (v "x"))

/-- A writer: two stores in one critical section, so a reader that ever sees
the first has read inside it. -/
def writeD : Decl where
  name := "write"; idx := ["r"]; arg := "m"
  argTy := cell rwP .int
  retTy := .unit
  body := lets [("t", .call "writeLock" ["r"] (v "m")),
                ("d0", .fld 1 (v "m")), ("d", .load false (v "d0")),
                ("u1", .store false (v "d") (.lit 1) none), ("u2", .store false (v "d") (.lit 2) none),
                ("p", .pair (v "m") (v "t")), ("u3", .call "writeUnlock" ["r"] (v "p"))]
    (.ret .unit)

def mkRWD : Decl where
  name := "mkRW"; idx := []; arg := "x"
  argTy := .int
  retTy := guardedBy rwP .int
  body := lets [("p", .new (v "x") (some .int))]
    (.region (v "p") "r" "d" "t0"
      (lets [("wv", .mkWord "r" rwP (.lit 0) (v "t0")),
             ("pr", .pair (v "wv") (v "d")), ("s", .new (v "pr") (some (.prod (.word (.var 0) rwP) (.ptr (.rgn (.var 0)) .int)))),
             ("s2", .publish (v "s")), ("mx", .pack (v "s2") "r" (guardedBy rwP .int))]
        (.ret (v "mx"))))

def useRD : Decl where
  name := "useR"; idx := []; arg := "m"; argTy := guardedBy rwP .int; retTy := .int
  body := .unpack (v "m") "r" "s" (lets [("x", .call "read" ["r"] (v "s"))] (.ret (v "x")))

def useWD : Decl where
  name := "useW"; idx := []; arg := "m"; argTy := guardedBy rwP .int; retTy := .unit
  body := .unpack (v "m") "r" "s" (lets [("u", .call "write" ["r"] (v "s"))] (.ret .unit))

def rwLib (acq rel : Bool := true) : Prog :=
  [readLockD acq, readUnlockD rel, writeLockD, writeUnlockD, readD, writeD, mkRWD, useRD, useWD]

#guard accepts (checkProg (rwLib))

/-! #### Hazards, each refused for its reason -/

-- A reader that stores: a share licenses loads only.
#guard rejects (checkProg ([{ readD with
    body := lets [("s", .call "readLock" ["r"] (v "m")), ("d0", .fld 1 (v "m")),
                  ("d", .load false (v "d0")), ("u", .store false (v "d") (.lit 7) none),
                  ("p", .pair (v "m") (v "s")), ("u2", .call "readUnlock" ["r"] (v "p"))]
      (.ret (.lit 0)) }] ++ rwLib)) "store into a region without its token"
-- Entry without `acq`, exit without `rel`.
#guard rejects (checkDecl (rwLib) (readLockD false)) "taking a read share needs acq"
#guard rejects (checkDecl (rwLib) (readUnlockD false)) "giving a read share back needs rel"
-- Exit without a share to give back.
def noShareD : Decl := { readUnlockD with
  name := "noShare", argTy := .prod (cell rwP .int) .unit
  body := .split (v "a") "m" "s" (lets [("w", .fld 0 (v "m")), ("c", .load false (v "w"))]
    (.parity (v "c") "k"
      (.ifeq (v "c") (.lit 0) (.ret .unit)
        (lets [("d", .sub (v "c") (.lit 2))]
          (.ifeq (v "d") (.lit 0)
            (.cas false true (v "w") (v "c") (.lit 0) "u" (.ret .unit) (.ret .unit))
            (.ret .unit))))
      (.ret .unit))) }
#guard rejects (checkDecl [] noShareD) "giving a read share back needs one"
-- A reader loading the payload after giving the share back.
#guard rejects (checkProg ([{ readD with
    body := lets [("s", .call "readLock" ["r"] (v "m")), ("p", .pair (v "m") (v "s")),
                  ("u", .call "readUnlock" ["r"] (v "p")),
                  ("d0", .fld 1 (v "m")), ("d", .load false (v "d0")), ("x", .load false (v "d"))]
      (.ret (v "x")) }] ++ rwLib)) "load from a region without its token"
-- Two readers at once (`c → c+4`) is not a transition; with a `+2` step
-- added to the protocol it is, but it is not a move of the lending protocol.
#guard rejects (checkDecl (rwLib) (readLockD true 4)) "not a transition"
def rwP2 : Proto := { rwP with trans := rwP.trans ++ [(2, 2, 2)] }
def readLock2 : Decl := { readLockD true 4 with argTy := cell rwP2 .int }
#guard rejects (checkDecl [readLock2] readLock2) "not a move of the lending protocol"
-- A writer entering from the readers' state: a transition to add, and still
-- refused, since shares are out.
def rwP3 : Proto := { rwP with trans := rwP.trans ++ [(2, 1, 0)] }
#guard rejects (checkDecl [] { writeLockD with
    argTy := cell rwP3 .int,
    body := lets [("w", .fld 0 (v "m"))]
      (.cas true false (v "w") (.lit 2) (.lit 1) "t" (.ret (v "t")) (.tail "writeLock" ["r"] (v "m"))) })
  "taking the region from a lending state"
-- `sub` without a proof that it does not wrap.
#guard rejects (checkDecl [] (dcl "s" (.intS (.var 0)) .int
    (lets [("d", .sub (v "a") (.lit 1))] (.ret (v "d"))) ["n"])) "not provably nonnegative"

/-! #### A counting semaphore: permits are shares

`0` free, `k+1` with `k+1` permits out.  Unbounded: counting *up*, a bound
would need an inequality fact.  The bounded one below counts down instead. -/

def semP : Proto :=
  ⟨[⟨0, 0, true⟩, ⟨1, 1, true⟩], [(0, 1, 0), (1, 1, 1), (1, 1, -1), (1, 0, 0)], false, [1], [], [], false, false, false, false, false, []⟩

def semAcqD : Decl where
  name := "semAcq"; idx := ["r"]; arg := "m"
  argTy := cell semP .int
  retTy := .share (.var 0)
  body :=
    let retry := .tail "semAcq" ["r"] (v "m")
    lets [("w", .fld 0 (v "m")), ("c", .load false (v "w"))]
      (.ifeq (v "c") (.lit 0)
        (.cas true false (v "w") (v "c") (.lit 1) "t" (.ret (v "t")) retry)
        (lets [("c1", .add (v "c") (.lit 1))]
          (.cas true false (v "w") (v "c") (v "c1") "t" (.ret (v "t")) retry)))

def semRelD : Decl where
  name := "semRel"; idx := ["r"]; arg := "a"
  argTy := .prod (cell semP .int) (.share (.var 0))
  retTy := .unit
  body := .split (v "a") "m" "s"
    (let retry := lets [("p", .pair (v "m") (v "s"))] (.tail "semRel" ["r"] (v "p"))
     lets [("w", .fld 0 (v "m")), ("c", .load false (v "w"))]
      (.ifeq (v "c") (.lit 0) retry
        (lets [("d", .sub (v "c") (.lit 1))]
          (.ifeq (v "d") (.lit 0)
            (.cas false true (v "w") (v "c") (.lit 0) "u" (.ret .unit) retry)
            (.cas false true (v "w") (v "c") (v "d") "u" (.ret .unit) retry)))))

#guard pwf semP
#guard accepts (checkProg [semAcqD, semRelD])

/-! #### A bounded semaphore: count the free permits down

The word holds the number of *free* permits, so the capacity is the value it is
created with.  Clause `0` is a counting-down lending family (`lendsDown`):
taking a permit is `k + 1 → k`, which `pstep` with `dk = -1` accepts only when
a permit is free, and it lends a share; giving one back is `k → k + 1` and
consumes the share.  No inequality fact is needed: the bound is the transition.
No `cas` may enter, leave, or take the region from the family. -/

def bsemP : Proto := ⟨[⟨1, 0, true⟩], [(0, 0, -1), (0, 0, 1)], false, [], [0], [], false, false, false, false, false, []⟩
#guard pwf bsemP
-- A clause cannot lend both ways.
#guard !pwf { bsemP with lends := [0] }

/-- `ifeq c 0`: none free, retry; otherwise `c = u' + 1`, so `c − 1` is typed
and the `cas` is a `−1` step of the family. -/
def bsemAcqD (acq : Bool := true) : Decl where
  name := "bsemAcq"; idx := ["r"]; arg := "m"
  argTy := cell bsemP .int
  retTy := .share (.var 0)
  body :=
    let retry := .tail "bsemAcq" ["r"] (v "m")
    lets [("w", .fld 0 (v "m")), ("c", .load false (v "w"))]
      (.ifeq (v "c") (.lit 0) retry
        (lets [("d", .sub (v "c") (.lit 1))]
          (.cas acq false (v "w") (v "c") (v "d") "t" (.ret (v "t")) retry)))

def bsemRelD : Decl where
  name := "bsemRel"; idx := ["r"]; arg := "a"
  argTy := .prod (cell bsemP .int) (.share (.var 0))
  retTy := .unit
  body := .split (v "a") "m" "s"
    (let retry := lets [("p", .pair (v "m") (v "s"))] (.tail "bsemRel" ["r"] (v "p"))
     lets [("w", .fld 0 (v "m")), ("c", .load false (v "w")), ("d", .add (v "c") (.lit 1))]
      (.cas false true (v "w") (v "c") (v "d") "u" (.ret .unit) retry))

/-- A holder loads the payload under its permit. -/
def bsemUseD : Decl where
  name := "bsemUse"; idx := []; arg := "m"; argTy := guardedBy bsemP .int; retTy := .int
  body := .unpack (v "m") "r" "g" (lets [("s", .call "bsemAcq" ["r"] (v "g")),
      ("d0", .fld 1 (v "g")), ("d", .load false (v "d0")), ("x", .load false (v "d")),
      ("p", .pair (v "g") (v "s")), ("u", .call "bsemRel" ["r"] (v "p"))] (.ret (v "x")))

/-- Capacity `n`: the word starts at `n`. -/
def mkBSemD (n : Nat) : Decl where
  name := "mkBSem"; idx := []; arg := "x"
  argTy := .int
  retTy := guardedBy bsemP .int
  body := lets [("p", .new (v "x") (some .int))]
    (.region (v "p") "r" "d" "t0"
      (lets [("wv", .mkWord "r" bsemP (.lit n) (v "t0")),
             ("pr", .pair (v "wv") (v "d")), ("s", .new (v "pr") (some (.prod (.word (.var 0) bsemP) (.ptr (.rgn (.var 0)) .int)))),
             ("s2", .publish (v "s")), ("mx", .pack (v "s2") "r" (guardedBy bsemP .int))]
        (.ret (v "mx"))))

def bsemLib (n : Nat := 2) : Prog := [bsemAcqD, bsemRelD, bsemUseD, mkBSemD n]
#guard accepts (checkProg (bsemLib 2))
#guard accepts (checkProg (bsemLib 0))  -- capacity 0: typed, and nobody ever gets in

-- Taking a permit without checking one is free: `c − 1` may wrap.
#guard rejects (checkDecl (bsemLib) { bsemAcqD with
    body := lets [("w", .fld 0 (v "m")), ("c", .load false (v "w")), ("d", .sub (v "c") (.lit 1))]
      (.cas true false (v "w") (v "c") (v "d") "t" (.ret (v "t")) (.tail "bsemAcq" ["r"] (v "m"))) })
  "not provably nonnegative"
-- Taking a permit by counting *up* (even with `acq rel`): that direction gives a share back.
#guard rejects (checkDecl (bsemLib) { bsemAcqD with
    body := lets [("w", .fld 0 (v "m")), ("c", .load false (v "w")), ("d", .add (v "c") (.lit 1))]
      (.cas true true (v "w") (v "c") (v "d") "t" (.ret (v "t")) (.tail "bsemAcq" ["r"] (v "m"))) })
  "giving a read share back needs one"
-- Taking a permit without `acq`.
#guard rejects (checkDecl (bsemLib) (bsemAcqD false)) "taking a read share needs acq"
-- A writer state reachable from the family (with no permits free): still
-- refused, since the region is never taken back from a counting-down family.
def bsemWP : Proto := ⟨[⟨2, 0, true⟩, ⟨0, 1, false⟩], [(0, 0, -1), (0, 0, 1), (0, 1, 0)], false, [], [0], [], false, false, false, false, false, []⟩
#guard pwf bsemWP
#guard rejects (checkDecl [] (dcl "tw" (cell bsemWP .int) .unit
    (lets [("w", .fld 0 (v "a"))]
      (.cas true false (v "w") (.lit 0) (.lit 1) "t" (.ret .unit) (.ret .unit))) ["r"]))
  "taking the region from a lending state"

/-! #### On the promise machine

Two readers and a writer from a lock at `0`.  The writer stores `1` then `2`
in one critical section, so a reader returning `1` has read inside it. -/

def rwSetup (acq rel : Bool := true) : Option Setup := runSetup (rwLib acq rel) "mkRW" [] .int [cst (.num 0)]
def rwThr (nr : Nat) (s : Setup) : List (String × List Ty × Ty × List Word) :=
  (List.replicate nr ("useR", [], guardedBy rwP .int, s.res)) ++ [("useW", [], guardedBy rwP .int, s.res)]

def readsOK (r : Option Explored) (nr : Nat) : Bool :=
  (List.range nr).all fun i => (resultsOf r i).all fun x => x == [.num 0] || x == [.num 2]
def sawInside (r : Option Explored) : Bool := (resultsOf r 0).contains [.num 1]

-- One reader and the writer: never inside the critical section.  The `maxP 1`
-- runs (with a promise) are in RWLockSlow.lean, also gated.
#guard let r := runE (rwLib) rwSetup (rwThr 1) 0; clean r && readsOK r 1
-- Entry without `acq` (message passing): the reader sees the writer's first store.
#guard let r := runE (rwLib false true) (rwSetup false true) (rwThr 1) 0; clean r && sawInside r
-- Exit without `rel` (load buffering): invisible without promises (seen with
-- one; see RWLockSlow.lean).
#guard let r := runE (rwLib true false) (rwSetup true false) (rwThr 1) 0; clean r && readsOK r 1

-- Two readers and the writer.  The second reader can acquire from the first
-- reader's plain `cas` write (coherence-after the writer's release) rather than
-- from the release itself.  ARM forbids it seeing the critical section anyway:
-- an acquire read of an *external* write orders later accesses after the read
-- timestamp (`obs ⊇ rfe`, `bob ⊇ [A];po`).  The model used to join only the
-- message's carried view, and this run returned `1`; see `extTs` in
-- WeakMem.lean and litmus/aarch64-acq/ (five WRC shapes herd7 forbids).
#guard let r := runE (rwLib) rwSetup (rwThr 2) 0; clean r && readsOK r 2

-- The bounded semaphore at capacity 1, two holders: both finish and read the payload.
def bsSetup (n : Nat) : Option Setup := runSetup (bsemLib n) "mkBSem" [] .int [cst (.num 7)]
#guard let r := runE (bsemLib 1) (bsSetup 1) (fun s =>
    [("bsemUse", [], guardedBy bsemP .int, s.res), ("bsemUse", [], guardedBy bsemP .int, s.res)]) 0
  clean r && (resultsOf r 0).all (· == [.num 7]) && (resultsOf r 1).all (· == [.num 7])

end RWLock
