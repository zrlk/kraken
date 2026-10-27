import WeakCore.EM0Prelude
import WeakCore.TermStartW
import WeakCore.TermSpawnSuccs

/-! # EM0: "Hello, world" end to end (heap-bytes fallback)

The program (prelude: `EM0Prelude`):
* `hello` builds the 13 bytes "Hello, world\n" as two little-endian `LanesU8` words in a fresh buffer,
  publishes it and returns the slice (`exists q. ({Loc pub Array[q] LanesU8 | ini >= q} * Int[q]) * Int`);
* `main` calls `hello`, allocates and publishes a claim cell `c`, takes its own `ThreadId` (`current ()`),
  spawns `worker` on `((slice, c), me)` and joins in `waitLoop`: acquire-load `c`, `park` until it reads 1,
  then `ret 0`;
* `worker` prints the slice (`print`, one `emit` per byte), release-stores 1 to `c` and `unpark`s `main`.

It runs from the wrapper start `TermStartW.startW em0 2` (thread 0 calls `main`, then `exitEv r`; capacity
2 for the one spawn).  `TermScopeEM0` proves the program-side obligations and instantiates the EM0 finals.

**What is and is not established about the output.**  With promises
on, the worker may promise its `store rel c 1` before its remaining `emit`s (an `emit` may run with
promises outstanding); `main` can then read 1 and make its exit event early.  So the exit event may
precede some or all of the bytes; the release/acquire join orders memory, not I/O.  What holds, under
Kraken's first-exit reading, is: the output is a prefix of "Hello, world\n", followed by `exit 0`.  In
the bounded explorer every complete run prints all 13 bytes and makes exactly one `exit 0`, and the bytes
before the exit are a prefix of "Hello, world\n" (the `#guard`s below).  These are bounded-search facts
for this program, **not theorems**; the proved results are the soundness finals of `TermScopeEM0` (and
"every exit is `exit 0`" is not proved either: R2, deferred).  With promises off the only run prints
"Hello, world\n" and then exits 0.

The explorer has no `Spawn` successors in `successorsAll`; the tests use `TermSpawnSuccs.exploreMS`.
-/

namespace EM0

open CoreLang CoreTerm TermRun TermStartW TermSpawnSuccs EM0Prelude

/-- `hello`, the bytes, in the concrete syntax: 8583909746840200520 = "Hello, w", 44634501743 = "orld\n". -/
def helloSrc : String := "
def hello(u : Unit) : exists q. ({Loc pub Array[q] LanesU8 | ini >= q} * Int[q]) * Int =
  let two = 2
  let m = nameI two
  let b = newBuf[LanesU8] m
  let w0 = asLanes U8 8583909746840200520
  let o0 = xchg b[0] w0
  let w1 = asLanes U8 44634501743
  let o1 = xchg b[1] w1
  let s = publish b
  let n = 13
  let sm = (s, m)
  let sl0 = (sm, n)
  let sl = pack sl0 at m : exists a. ({Loc pub Array[a] LanesU8 | ini >= a} * Int[a]) * Int
  ret sl
"

/-- `worker`, `waitLoop` and `main` in the concrete syntax. -/
def progSrc : String := "
def worker(a : ((exists q. ({Loc pub Array[q] LanesU8 | ini >= q} * Int[q]) * Int) * Ptr pub Int) * ThreadId) : Unit =
  let (slc, j) = a
  let (sl0, c) = slc
  let <q, sl> = unpack sl0
  let u = print{q}(sl)
  let d = store rel c 1
  let w = unpark j
  ret ()

def waitLoop(c : Ptr pub Int) : Int =
  let d = load acq c
  if d = 1 then
    ret 0
  else
    let p = park ()
    tail waitLoop(c)

def main(u : Unit) : Int =
  let sl = hello(())
  let z = zero[Int]
  let o = new z
  let c = publish o
  let me = current ()
  let p0 = (sl, c)
  let p = (p0, me)
  let t = spawn worker p : ((exists q. ({Loc pub Array[q] LanesU8 | ini >= q} * Int[q]) * Int) * Ptr pub Int) * ThreadId
  tail waitLoop(c)
"

/-- The single-thread test `main` (no spawn): print the bytes, then return 0. -/
def mainTSrc : String := "
def main(u : Unit) : Int =
  let sl = hello(())
  let <q, s> = unpack sl
  let r = print{q}(s)
  ret 0
"

/-- `hello`, `worker`, `waitLoop`, `main` as checked code blocks (generated from `helloSrc ++ progSrc`). -/
def progDecls : Prog := [
  { name := "hello", idx := [], arg := "u",
    argTy := (CoreLang.Ty.unit),
    retTy := (CoreLang.Ty.iex
  (CoreLang.Ty.prod
    (CoreLang.Ty.prod
      (CoreLang.Ty.refine
        (CoreLang.Ty.loc
          (CoreLang.Mode.pub)
          (CoreLang.Ty.array (CoreLang.Idx.var 0) (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
        (CoreLang.Pred.ini (CoreLang.Idx.var 0)))
      (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
    (CoreLang.Ty.int))),
    body := (CoreTerm.Expr.let_
  "two"
  (CoreTerm.Op.atom (CoreTerm.At.lit 2))
  (CoreTerm.Expr.let_
    "m"
    (CoreTerm.Op.nameI (CoreTerm.At.var "two"))
    (CoreTerm.Expr.let_
      "b"
      (CoreTerm.Op.newBuf (CoreTerm.At.var "m") (CoreLang.Ty.lanes false (CoreLang.Wd.w8)))
      (CoreTerm.Expr.let_
        "w0"
        (CoreTerm.Op.asLanes false (CoreLang.Wd.w8) (CoreTerm.At.lit 8583909746840200520))
        (CoreTerm.Expr.let_
          "o0"
          (CoreTerm.Op.xchgAt (CoreTerm.At.var "b") (CoreTerm.At.lit 0) (CoreTerm.At.var "w0"))
          (CoreTerm.Expr.let_
            "w1"
            (CoreTerm.Op.asLanes false (CoreLang.Wd.w8) (CoreTerm.At.lit 44634501743))
            (CoreTerm.Expr.let_
              "o1"
              (CoreTerm.Op.xchgAt (CoreTerm.At.var "b") (CoreTerm.At.lit 1) (CoreTerm.At.var "w1"))
              (CoreTerm.Expr.let_
                "s"
                (CoreTerm.Op.publish (CoreTerm.At.var "b"))
                (CoreTerm.Expr.let_
                  "n"
                  (CoreTerm.Op.atom (CoreTerm.At.lit 13))
                  (CoreTerm.Expr.let_
                    "sm"
                    (CoreTerm.Op.pair (CoreTerm.At.var "s") (CoreTerm.At.var "m"))
                    (CoreTerm.Expr.let_
                      "sl0"
                      (CoreTerm.Op.pair (CoreTerm.At.var "sm") (CoreTerm.At.var "n"))
                      (CoreTerm.Expr.let_
                        "sl"
                        (CoreTerm.Op.pack
                          (CoreTerm.At.var "sl0")
                          "m"
                          (CoreLang.Ty.iex
                            (CoreLang.Ty.prod
                              (CoreLang.Ty.prod
                                (CoreLang.Ty.refine
                                  (CoreLang.Ty.loc
                                    (CoreLang.Mode.pub)
                                    (CoreLang.Ty.array (CoreLang.Idx.var 0) (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
                                  (CoreLang.Pred.ini (CoreLang.Idx.var 0)))
                                (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
                              (CoreLang.Ty.int))))
                        (CoreTerm.Expr.ret (CoreTerm.At.var "sl")))))))))))))) },
  { name := "worker", idx := [], arg := "a",
    argTy := (CoreLang.Ty.prod
  (CoreLang.Ty.prod
    (CoreLang.Ty.iex
      (CoreLang.Ty.prod
        (CoreLang.Ty.prod
          (CoreLang.Ty.refine
            (CoreLang.Ty.loc
              (CoreLang.Mode.pub)
              (CoreLang.Ty.array (CoreLang.Idx.var 0) (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
            (CoreLang.Pred.ini (CoreLang.Idx.var 0)))
          (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
        (CoreLang.Ty.int)))
    (CoreLang.Ty.ptr (CoreLang.Mode.pub) (CoreLang.Ty.int)))
  (CoreLang.Ty.tid)),
    retTy := (CoreLang.Ty.unit),
    body := (CoreTerm.Expr.split
  (CoreTerm.At.var "a")
  "slc"
  "j"
  (CoreTerm.Expr.split
    (CoreTerm.At.var "slc")
    "sl0"
    "c"
    (CoreTerm.Expr.unpack
      (CoreTerm.At.var "sl0")
      "q"
      "sl"
      (CoreTerm.Expr.let_
        "u"
        (CoreTerm.Op.call "print" ["q"] (CoreTerm.At.var "sl") [])
        (CoreTerm.Expr.let_
          "d"
          (CoreTerm.Op.store true (CoreTerm.At.var "c") (CoreTerm.At.lit 1) none)
          (CoreTerm.Expr.let_
            "w"
            (CoreTerm.Op.ext CoreTerm.ExtName.unpark
  (CoreTerm.At.var "j"))
            (CoreTerm.Expr.ret (CoreTerm.At.unit)))))))) },
  { name := "waitLoop", idx := [], arg := "c",
    argTy := (CoreLang.Ty.ptr (CoreLang.Mode.pub) (CoreLang.Ty.int)),
    retTy := (CoreLang.Ty.int),
    body := (CoreTerm.Expr.let_
  "d"
  (CoreTerm.Op.load true (CoreTerm.At.var "c"))
  (CoreTerm.Expr.ifeq
    (CoreTerm.At.var "d")
    (CoreTerm.At.lit 1)
    (CoreTerm.Expr.ret (CoreTerm.At.lit 0))
    (CoreTerm.Expr.let_
      "p"
      (CoreTerm.Op.ext CoreTerm.ExtName.park (CoreTerm.At.unit))
      (CoreTerm.Expr.tail "waitLoop" [] (CoreTerm.At.var "c") [])))) },
  { name := "main", idx := [], arg := "u",
    argTy := (CoreLang.Ty.unit),
    retTy := (CoreLang.Ty.int),
    body := (CoreTerm.Expr.let_
  "sl"
  (CoreTerm.Op.call "hello" [] (CoreTerm.At.unit) [])
  (CoreTerm.Expr.let_
    "z"
    (CoreTerm.Op.zero (CoreLang.Ty.int))
    (CoreTerm.Expr.let_
      "o"
      (CoreTerm.Op.new (CoreTerm.At.var "z"))
      (CoreTerm.Expr.let_
        "c"
        (CoreTerm.Op.publish (CoreTerm.At.var "o"))
        (CoreTerm.Expr.let_
          "me"
          (CoreTerm.Op.ext (CoreTerm.ExtName.current) (CoreTerm.At.unit))
          (CoreTerm.Expr.let_
            "p0"
            (CoreTerm.Op.pair (CoreTerm.At.var "sl") (CoreTerm.At.var "c"))
            (CoreTerm.Expr.let_
              "p"
              (CoreTerm.Op.pair (CoreTerm.At.var "p0") (CoreTerm.At.var "me"))
              (CoreTerm.Expr.let_
                "t"
                (CoreTerm.Op.spawn
                  "worker"
                  (CoreTerm.At.var "p")
                  (CoreLang.Ty.prod
                    (CoreLang.Ty.prod
                      (CoreLang.Ty.iex
                        (CoreLang.Ty.prod
                          (CoreLang.Ty.prod
                            (CoreLang.Ty.refine
                              (CoreLang.Ty.loc
                                (CoreLang.Mode.pub)
                                (CoreLang.Ty.array (CoreLang.Idx.var 0) (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
                              (CoreLang.Pred.ini (CoreLang.Idx.var 0)))
                            (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
                          (CoreLang.Ty.int)))
                      (CoreLang.Ty.ptr (CoreLang.Mode.pub) (CoreLang.Ty.int)))
                    (CoreLang.Ty.tid))
                  [])
                (CoreTerm.Expr.tail "waitLoop" [] (CoreTerm.At.var "c") []))))))))) }]

/-- The test `main` as a checked code block (generated from `mainTSrc`). -/
def mainTDecls : Prog := [
  { name := "main", idx := [], arg := "u",
    argTy := (CoreLang.Ty.unit),
    retTy := (CoreLang.Ty.int),
    body := (CoreTerm.Expr.let_
  "sl"
  (CoreTerm.Op.call "hello" [] (CoreTerm.At.unit) [])
  (CoreTerm.Expr.unpack
    (CoreTerm.At.var "sl")
    "q"
    "s"
    (CoreTerm.Expr.let_
      "r"
      (CoreTerm.Op.call "print" ["q"] (CoreTerm.At.var "s") [])
      (CoreTerm.Expr.ret (CoreTerm.At.lit 0))))) }]

/-- **The EM0 program**: the prelude, then `hello`, `worker`, `waitLoop`, `main`. -/
def em0 : Prog := prelude ++ progDecls

/-- The single-thread test program: the prelude, `hello` and the test `main`. -/
def em0T : Prog := prelude ++ progDecls.take 1 ++ mainTDecls

/-! ## The syntax: source ≡ AST, round trip, checker -/

#guard parsesTo (preludeSrc ++ helloSrc ++ progSrc) em0
#guard parsesTo (preludeSrc ++ helloSrc ++ mainTSrc) em0T
#guard
  em0.map (·.name) == ["spin", "exit", "emit8", "printL", "print", "hello", "worker", "waitLoop", "main"]
#guard (em0.filter (!Syntax.roundTrips ·)).isEmpty
#guard parsesTo (Syntax.showProg em0) em0
#guard accepts (checkProg em0)
#guard accepts (checkProg em0T)
#guard mainRetNum em0 && mainRetNum em0T

/-! ## The exit argument by `main`'s result type (Kraken: exit `n mod 256` for one number word, else 0) -/

/-- A one-block program from source (tests only). -/
def P (s : String) : Prog := match Syntax.parseProg s with | .ok p => p | .error _ => []

/-- `main` returning `U64` 300: the wrapper converts the word (`cvt U64`, `toInt`) and exits 300 mod 256 = 44. -/
def progU : Prog := P "
def main(u : Unit) : U64 =
  let x = cvt U64 300
  ret x
"
/-- `main` returning `I8` with bit pattern 255 (−1): exit 255. -/
def progS : Prog := P "
def main(u : Unit) : I8 =
  let x = cvt I8 255
  ret x
"
/-- `main` returning `Unit`: exit 0. -/
def progV : Prog := P "
def main(u : Unit) : Unit =
  ret ()
"

/-- The traces of the finals of the full search from the wrapper start. -/
def tracesW (p : Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (cap fuel : Nat) : List (List Event) × Bool :=
  let r := exploreMS p k arch {} fuel (startW p cap)
  (r.finals.map (·.trace), r.cut)

#guard progU.length == 1 && progS.length == 1 && progV.length == 1
#guard mainRetNum progU && mainRetNum progS && !mainRetNum progV
#guard accepts (check progU wcx (wrapTerm (mainRet progU)))
#guard accepts (check progS wcx (wrapTerm (mainRet progS)))
#guard accepts (check progV wcx (wrapTerm (mainRet progV)))
#guard wrapTerm (mainRet progU) matches .let_ "r" (.call "main" [] (.var "a") _)
  (.let_ "v" (.cvt false .w64 (.var "r")) (.let_ "n" (.toInt (.var "v")) (.let_ "u" (.ext .exitEv (.var "n")) (.ret .unit))))
#guard tracesW progU {} .arm 1 50 == ([[.exit 44]], false)
#guard tracesW progS {} .arm 1 50 == ([[.exit 255]], false)
#guard tracesW progV {} .arm 1 50 == ([[.exit 0]], false)

/-! ## Runs of EM0 (bounded search, `exploreMS`) -/

/-- "Hello, world\n", then `exit 0`. -/
def helloTrace : List Event := ([72, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 10].map Event.out) ++ [.exit 0]

/-- The output events of a trace. -/
def outs (t : List Event) : List Event := t.filter fun e => match e with | .out _ => true | _ => false

/-- A complete EM0 trace as the explorer finds it: all 13 bytes in order, exactly one `exit 0`, and the
bytes before the exit a prefix of "Hello, world\n". -/
def okTrace (t : List Event) : Bool :=
  outs t == outs helloTrace && t.count (.exit 0) == 1 && t.length == 14 &&
    (t.takeWhile (· != .exit 0)).isPrefixOf (outs helloTrace)

/-- Promises off. -/
def kOff : Promises.Knobs := { (default : Promises.Knobs) with promises := false }

-- promises off: the only run prints "Hello, world\n", then exits 0 (arm and tso)
#guard (tracesW em0 kOff .arm 2 600).1.eraseDups == [helloTrace] && !(tracesW em0 kOff .arm 2 600).2
#guard (tracesW em0 kOff .tso 2 600).1.eraseDups == [helloTrace] && !(tracesW em0 kOff .tso 2 600).2
-- two finals, same trace: they differ only in main's leftover permit (worker's unpark after main's park returned; T5)
#guard (tracesW em0 kOff .arm 2 600).1.length == 2
#guard (tracesW em0 kOff .tso 2 600).1.length == 2
-- the single-thread test, promises on and off: always "Hello, world\n", then exit 0.  With promises
-- on the search is cut (certification and promise-candidate fuel: `TermRun.Trunc`)
#guard (tracesW em0T {} .arm 1 600).1.all (· == helloTrace) && (tracesW em0T {} .arm 1 600).2
#guard tracesW em0T kOff .arm 1 600 == ([helloTrace], false)
-- promises on (default bounds): every complete run found is `okTrace`, and (R1) some run exits before the
-- last byte.  The search is cut (promise-candidate fuel: more solo fuel finds more finals), so this is a
-- bounded statement
#guard let r := tracesW em0 {} .arm 2 600; r.2 && !r.1.isEmpty && r.1.all okTrace && r.1.any (· != helloTrace)
#guard let r := tracesW em0 {} .tso 2 600; r.2 && !r.1.isEmpty && r.1.all okTrace && r.1.any (· != helloTrace)

end EM0
