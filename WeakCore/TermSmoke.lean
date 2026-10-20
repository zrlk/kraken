/-
# TermSmoke — the library programs run on the promise machine  (T2 smoke test)

Each library program from `CoreTerm` §6 is set up by one thread alone, then
two threads are spawned on the result (inheriting the setup thread's views:
spawning synchronises) and every run is explored with `TermRun.exploreM`.
The guards say: the search finished inside its bound, no load ever returned
`undef`, and the outcomes are exactly the linearisable ones.  The boxed tier
(a sum with a two-word arm) is exercised twice: the polymorphic queue at a
two-word payload, and a plainly stored boxed sum whose injection fence is
shown to be load-bearing.

Promises are explored (`maxP = 1`) where that is cheap; the claim queue with
promises visits ~34k configurations and is left out of the gate.

Build: LEAN_PATH=build lean TermSmoke.lean   (after TermRun.olean)
-/
import WeakCore.TermRun
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

namespace TermSmoke

/-- A setup run: one thread alone, to a final state. -/
structure Setup where
  mem : Memory
  pairs : List Ts
  vs : VState
  nalloc : Nat
  res : List Word

def runSetup (p : Prog) (f : String) (ts : List Ty) (argTy : Ty) (arg : List Word)
    (depth : Nat := 60) : Option Setup := do
  let c : Cfg := { mem := #[], ths := #[{ term := .tail f [] (v "a") ts, env := [("a", argTy, arg)] }] }
  let fin ← (explore p Promises.Knobs.all .arm { maxP := 0 } depth c).head?
  let th ← fin.ths[0]?
  let res ← match th.term with
    | .ret a => (evalAt th.env a).map (·.2)
    | _ => none
  if th.undefs > 0 then none
  pure ⟨fin.mem, fin.pairs, th.vs, th.nalloc, res⟩

/-- Spawn threads after a setup: they inherit its view (spawn synchronises). -/
def spawn (s : Setup) (thr : List (String × List Ty × Ty × List Word)) : Cfg :=
  { mem := s.mem, pairs := s.pairs, lbase := s.nalloc,
    ths := (thr.map fun (f, ts, t, ws) =>
      ({ term := .tail f [] (v "a") ts, env := [("a", t, ws)], vs := s.vs } : TTh)).toArray }

def resWs (th : TTh) : Option (List Val) :=
  match th.term with
  | .ret a => (evalAt th.env a).map (·.2.map (·.val))
  | _ => none

/-- The coherence-last value at `a` (timestamps are coherence order). -/
def lastAt (c : Cfg) (a : Address) : Option Val :=
  (c.mem.toList.filter (·.loc == a)).getLast?.map (·.val)

structure Report where
  finals : Nat
  undef  : Bool
  outs   : List (List (Option (List Val)))
  deriving Repr

def report (fs : List Cfg) : Report :=
  ⟨fs.length, fs.any (·.ths.any (·.undefs > 0)),
   (fs.map fun c => c.ths.toList.map resWs).eraseDups⟩

/-- Explore spawned threads. -/
def runE (p : Prog) (s : Option Setup) (thr : Setup → List (String × List Ty × Ty × List Word))
    (maxP : Nat) (depth : Nat := 300) : Option Explored :=
  s.map fun s => exploreM p Promises.Knobs.all .arm { maxP := maxP } depth (spawn s (thr s))

/-- Finished within bound, some final state, no `undef` anywhere. -/
def clean (r : Option Explored) : Bool :=
  match r with
  | some r => !r.cut && !r.finals.isEmpty && !r.finals.any (·.ths.any (·.undefs > 0))
  | none => false

/-- The distinct results of thread `i`. -/
def resultsOf (r : Option Explored) (i : Nat) : List (List Val) :=
  match r with
  | some r => (r.finals.filterMap fun c => (c.ths[i]?).bind resWs).eraseDups
  | none => []

def sameSet (xs ys : List (List Val)) : Bool := xs.all ys.contains && ys.all xs.contains

/-! ### Mutex: two increments of a counter at 0 -/

def mSetup : Option Setup := runSetup mutexLib "mkMutex" [] .int [cst (.num 0)]
def mThr (s : Setup) : List (String × List Ty × Ty × List Word) :=
  [("useMutex", [], mutex .int, s.res), ("useMutex", [], mutex .int, s.res)]

/-- Every final state has the counter (label 0, the payload) at 2. -/
def countIs2 (r : Option Explored) : Bool :=
  match r with
  | some r => r.finals.all fun c => lastAt c ⟨0, 0⟩ == some (.num 2)
  | none => false

#guard let r := runE mutexLib mSetup mThr 0; clean r && countIs2 r
#guard let r := runE mutexLib mSetup mThr 1; clean r && countIs2 r

/-! ### Seqlock: writer (1,1) → (2,2) ∥ reader; never a torn pair -/

def wrC : Decl where
  name := "wr"; idx := []; arg := "a"
  argTy := .prod (seqLock pay) pay
  retTy := .unit
  body := .split (v "a") "s" "x" (.unpack (v "s") "r" "c"
    (lets [("p", .pair (v "c") (v "x")), ("u", .call "write" ["r"] (v "p"))] (.ret .unit)))

def rdC : Decl where
  name := "rd"; idx := []; arg := "s"
  argTy := seqLock pay
  retTy := pay
  body := .unpack (v "s") "r" "c" (lets [("y", .call "read" ["r"] (v "c"))] (.ret (v "y")))

def seqProg : Prog := seqLib ++ [wrC, rdC]
#guard accepts (checkProg seqProg)

def sSetup : Option Setup := runSetup seqProg "mkSeq" [] pay [cst (.num 1), cst (.num 1)]
def seqThr (s : Setup) : List (String × List Ty × Ty × List Word) :=
  [("wr", [], .prod (seqLock pay) pay, s.res ++ [cst (.num 2), cst (.num 2)]),
   ("rd", [], seqLock pay, s.res)]
def seqOK : List (List Val) := [[.num 1, .num 1], [.num 2, .num 2]]

#guard let r := runE seqProg sSetup seqThr 0; clean r && sameSet (resultsOf r 1) seqOK
#guard let r := runE seqProg sSetup seqThr 1; clean r && sameSet (resultsOf r 1) seqOK

/-! ### Michael–Scott queue: enqueue 7 ∥ deq -/

/-- `deq`'s two answers, as a wide `τ + Unit`: `[0, payload]` or `[1, 0]`. -/
def deqOK (payload : Val) : List (List Val) := [[.num 0, payload], [.num 1, .num 0]]

def qProg : Prog := queueLib .int
def qSetup : Option Setup := runSetup qProg "mkQueue" [] .int [cst (.num 0)]
def qThr (s : Setup) : List (String × List Ty × Ty × List Word) :=
  [("enqueue", [], .prod (queue .int) .int, s.res ++ [cst (.num 7)]),
   ("deq", [], queue .int, s.res)]

#guard let r := runE qProg qSetup qThr 0; clean r && sameSet (resultsOf r 1) (deqOK (.num 7))
#guard let r := runE qProg qSetup qThr 1; clean r && sameSet (resultsOf r 1) (deqOK (.num 7))

/-! ### Claim-cell queue: enqueue 7 ∥ deq; the claimed cell holds 7 -/

/-- `deq` answered either empty, or a claimed reference whose cell's
coherence-last value is 7. -/
def claimOK (r : Option Explored) (i : Nat) : Bool :=
  match r with
  | some r =>
      let arms := (r.finals.filterMap fun c => (c.ths[i]?).bind resWs).map (·.head?)
      arms.contains (some (.num 0)) && arms.contains (some (.num 1)) &&
      r.finals.all fun c =>
        match (c.ths[i]?).bind resWs with
        | some [.num 0, .loc a _] => lastAt c a == some (.num 7)
        | some [.num 1, .num 0] => true
        | _ => false
  | none => false

def cProg : Prog := claimLib .int
def cSetup : Option Setup := runSetup cProg "mkQueue" [] .int [cst (.num 0)]
def cThr (s : Setup) : List (String × List Ty × Ty × List Word) :=
  [("enqueue", [], .prod (cqueue .int) .int, s.res ++ [cst (.num 7)]),
   ("deq", [], cqueue .int, s.res)]

#guard let r := runE cProg cSetup cThr 0; clean r && claimOK r 1

/-! ### Polymorphic queue -/

def pqSetup (τ : Ty) (x : List Word) : Option Setup := runSetup polyQueueLib "mkQueue" [τ] τ x
def pqThr (τ : Ty) (x : List Word) (s : Setup) : List (String × List Ty × Ty × List Word) :=
  [("enqueue", [τ], .prod (queue τ) τ, s.res ++ x), ("deq", [τ], queue τ, s.res)]

#guard let r := runE polyQueueLib (pqSetup .int [cst (.num 0)]) (pqThr .int [cst (.num 7)]) 0
  clean r && sameSet (resultsOf r 1) (deqOK (.num 7))

-- At a two-word payload `deq` returns `pay + Unit`, a *boxed* sum: the
-- answer is a reference to a born-frozen `[tag, 7, 8]` or `[tag]` block.
#guard (Ty.sum pay .unit).tier == .boxed

/-- `deq` answered with a box holding `inl (7, 8)` or `inr ()`; both occur. -/
def boxedDeqOK (r : Option Explored) (i : Nat) : Bool :=
  match r with
  | some r =>
      let tags := r.finals.map fun c =>
        match (c.ths[i]?).bind resWs with
        | some [.loc a _] =>
            match lastAt c a with
            | some (.num 0) =>
                if lastAt c (offs a 1) == some (.num 7) && lastAt c (offs a 2) == some (.num 8)
                then some 0 else none
            | some (.num 1) => some 1
            | _ => none
        | _ => none
      tags.all (·.isSome) && tags.contains (some 0) && tags.contains (some 1)
  | none => false

def pqPay : Option Explored :=
  runE polyQueueLib (pqSetup pay [cst (.num 0), cst (.num 0)]) (pqThr pay [cst (.num 7), cst (.num 8)]) 0

#guard clean pqPay && boxedDeqOK pqPay 1

/-! ### A boxed sum stored plainly: the injection's own fence publishes it

The cell holds `pay + Unit` (boxed).  The writer injects `(7, 8)` and stores
the reference with a *plain* store; the reader loads plainly and cases.  With
the injection's `dmb ishst` no run reads `undef`; with it switched off
(`boxFence := false`) the reference can be promised ahead of the block's
initialisation, exactly as in MP, and the reader sees `undef`. -/

def bsum : Ty := .sum pay .unit
def bcell : Ty := .ptr .pub bsum

def bMk : Decl where
  name := "mk"; idx := []; arg := "x"
  argTy := .unit
  retTy := bcell
  body := lets [("e", .inr pay (v "x")), ("c", .new (v "e")), ("q", .publish (v "c"))] (.ret (v "q"))

def bWr : Decl where
  name := "bwr"; idx := []; arg := "a"
  argTy := .prod bcell pay
  retTy := .unit
  body := .split (v "a") "f" "x"
    (lets [("s", .inl .unit (v "x")), ("u", .store false (v "f") (v "s") none)] (.ret .unit))

def bRd : Decl where
  name := "brd"; idx := []; arg := "f"
  argTy := bcell
  retTy := pay
  body := lets [("r", .load false (v "f"))]
    (.case (v "r") "x" (.ret (v "x")) "y"
      (lets [("z", .add (.lit 0) (.lit 0)), ("zz", .pair (v "z") (v "z"))] (.ret (v "zz"))))

def bProg : Prog := [bMk, bWr, bRd]
#guard accepts (checkProg bProg)

def bSetup : Option Setup := runSetup bProg "mk" [] .unit []
def bThr (s : Setup) : List (String × List Ty × Ty × List Word) :=
  [("bwr", [], .prod bcell pay, s.res ++ [cst (.num 7), cst (.num 8)]), ("brd", [], bcell, s.res)]

def bRun (fence : Bool) : Option Explored :=
  bSetup.map fun s =>
    exploreM bProg Promises.Knobs.all .arm { maxP := 1 } 300 { spawn s (bThr s) with boxFence := fence }

#guard let r := bRun true; clean r && sameSet (resultsOf r 1) [[.num 7, .num 8], [.num 0, .num 0]]
#guard match bRun false with
  | some r => !r.cut && r.finals.any (·.ths.any (·.undefs > 0))
  | none => false

/-! ### Polymorphic claim queue at Int -/

def pcSetup : Option Setup := runSetup pcIntLib "mkQueueI" [] .int [cst (.num 0)]
def pcThr (s : Setup) : List (String × List Ty × Ty × List Word) :=
  [("enqueueI", [], .prod (cqueue .int) .int, s.res ++ [cst (.num 7)]),
   ("deq", [.int], cqueue .int, s.res)]

#guard let r := runE pcIntLib pcSetup pcThr 0; clean r && claimOK r 1

/-! ### A closure, run: the witness is erased

`mkClo` packs `addEnv` with a published `Int` cell as `∃E. Code(Int × Ptr pub E,
Int) × Ptr pub E`; `useClo` unpacks it (the machine pushes a placeholder for
`E`) and calls through the code value.  37 in the cell, 5 from the caller. -/

def cloDemoD : Decl where
  name := "cloDemo"; idx := []; arg := "n"; argTy := .int; retTy := .int
  body := lets [("c0", .new (v "n")), ("e", .publish (v "c0")), ("c", .call "mkClo" [] (v "e")),
                ("r", .call "useClo" [] (v "c"))] (.ret (v "r"))

def cloProg : Prog := cloLib ++ [cloDemoD]

#guard accepts (checkProg cloProg)
#guard (runSetup cloProg "cloDemo" [] .int [cst (.num 37)] 200).map (fun s => s.res.map (·.val))
  == some [Val.num 42]

end TermSmoke
