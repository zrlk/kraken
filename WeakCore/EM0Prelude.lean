import WeakCore.Syntax

/-! # EM0Prelude: the EM0 prelude

Library code blocks every EM0 program is built on, in the concrete syntax (`preludeSrc`) and as the
checked AST (`prelude`, generated mechanically from the source and compared with it by `#guard`).

* `spin(n : Int) : Void`, `exit(n : Int) : Void`: an explicit exit from any thread (one `exitEv`, then no
  further event or memory step).  `main`'s own exit goes through the start wrapper (`TermStartW`), not here.
* `emit8(a : LanesU8 * U64 * Int) : U64`: emit lanes `j..7` of one word, one `emit` per byte, while the
  byte counter is nonzero; returns the remaining count.
* `printL{i, d}`, `print{m}`: the ArrayLib `{i, d}` loop over a published `LanesU8` slice
  `({Loc pub Array[m] LanesU8 | ini >= m} * Int[m]) * Int` (words, byte count): plain loads at the thread's
  view, in program order, no fence.
-/

namespace EM0Prelude

open CoreLang CoreTerm

/-- The prelude in the concrete syntax. -/
def preludeSrc : String := "
def spin(n : Int) : Void =
  tail spin(n)

def exit(n : Int) : Void =
  let u = exitEv n
  tail spin(n)

def emit8(a : LanesU8 * U64 * Int) : U64 =
  let (w, r) = a
  let (cnt, j) = r
  let nil = cvt U64 0
  let z = fcmp eq cnt nil
  if z = 1 then
    ret cnt
  else
    let b = lane w j
    let e = emit b
    let one = cvt U64 1
    let cnt1 = fop sub cnt one
    if j = 7 then
      ret cnt1
    else
      let j1 = j + 1
      let q = (cnt1, j1)
      let q1 = (w, q)
      tail emit8(q1)

def printL{i, d}(a : {Loc pub Array[i+1+d] LanesU8 | ini >= i+1+d} * Int[i] * Int[d] * U64) : U64 =
  let (s, r1) = a
  let (iv, r2) = r1
  let (dv, cnt) = r2
  let l = s[iv]
  let w = load l
  let j0 = 0
  let cj = (cnt, j0)
  let wc = (w, cj)
  let cnt1 = emit8(wc)
  if dv = 0 then
    ret cnt1
  else
    let d1 = dv - 1
    let un = nameI d1
    let i1 = iv + 1
    let jn = nameI i1
    let q3 = (un, cnt1)
    let q2 = (jn, q3)
    let q1 = (s, q2)
    tail printL{jn, un}(q1)

def print{m}(a : ({Loc pub Array[m] LanesU8 | ini >= m} * Int[m]) * Int) : Unit =
  let (sm, n) = a
  let (s, mv) = sm
  let cnt = cvt U64 n
  if mv = 0 then
    ret ()
  else
    let k = mv - 1
    let kn = nameI k
    let z = nameI 0
    let q3 = (kn, cnt)
    let q2 = (z, q3)
    let q1 = (s, q2)
    let r = printL{z, kn}(q1)
    ret ()
"

/-- The prelude as checked code blocks (generated from `preludeSrc` by `Syntax.parseProg` and `reprArg`). -/
def prelude : Prog := [
  { name := "spin", idx := [], arg := "n",
    argTy := (CoreLang.Ty.int),
    retTy := (CoreLang.Ty.void),
    body := (CoreTerm.Expr.tail "spin" [] (CoreTerm.At.var "n") []) },
  { name := "exit", idx := [], arg := "n",
    argTy := (CoreLang.Ty.int),
    retTy := (CoreLang.Ty.void),
    body := (CoreTerm.Expr.let_
  "u"
  (CoreTerm.Op.ext (CoreTerm.ExtName.exitEv) (CoreTerm.At.var "n"))
  (CoreTerm.Expr.tail "spin" [] (CoreTerm.At.var "n") [])) },
  { name := "emit8", idx := [], arg := "a",
    argTy := (CoreLang.Ty.prod
  (CoreLang.Ty.lanes false (CoreLang.Wd.w8))
  (CoreLang.Ty.prod (CoreLang.Ty.fix false (CoreLang.Wd.w64)) (CoreLang.Ty.int))),
    retTy := (CoreLang.Ty.fix false (CoreLang.Wd.w64)),
    body := (CoreTerm.Expr.split
  (CoreTerm.At.var "a")
  "w"
  "r"
  (CoreTerm.Expr.split
    (CoreTerm.At.var "r")
    "cnt"
    "j"
    (CoreTerm.Expr.let_
      "nil"
      (CoreTerm.Op.cvt false (CoreLang.Wd.w64) (CoreTerm.At.lit 0))
      (CoreTerm.Expr.let_
        "z"
        (CoreTerm.Op.fcmp (CoreTerm.FCmp.eq) (CoreTerm.At.var "cnt") (CoreTerm.At.var "nil"))
        (CoreTerm.Expr.ifeq
          (CoreTerm.At.var "z")
          (CoreTerm.At.lit 1)
          (CoreTerm.Expr.ret (CoreTerm.At.var "cnt"))
          (CoreTerm.Expr.let_
            "b"
            (CoreTerm.Op.lane (CoreTerm.At.var "w") (CoreTerm.At.var "j"))
            (CoreTerm.Expr.let_
              "e"
              (CoreTerm.Op.ext (CoreTerm.ExtName.emit) (CoreTerm.At.var "b"))
              (CoreTerm.Expr.let_
                "one"
                (CoreTerm.Op.cvt false (CoreLang.Wd.w64) (CoreTerm.At.lit 1))
                (CoreTerm.Expr.let_
                  "cnt1"
                  (CoreTerm.Op.fop (CoreTerm.FOp.sub) (CoreTerm.At.var "cnt") (CoreTerm.At.var "one"))
                  (CoreTerm.Expr.ifeq
                    (CoreTerm.At.var "j")
                    (CoreTerm.At.lit 7)
                    (CoreTerm.Expr.ret (CoreTerm.At.var "cnt1"))
                    (CoreTerm.Expr.let_
                      "j1"
                      (CoreTerm.Op.add (CoreTerm.At.var "j") (CoreTerm.At.lit 1))
                      (CoreTerm.Expr.let_
                        "q"
                        (CoreTerm.Op.pair (CoreTerm.At.var "cnt1") (CoreTerm.At.var "j1"))
                        (CoreTerm.Expr.let_
                          "q1"
                          (CoreTerm.Op.pair (CoreTerm.At.var "w") (CoreTerm.At.var "q"))
                          (CoreTerm.Expr.tail "emit8" [] (CoreTerm.At.var "q1") [])))))))))))))) },
  { name := "printL", idx := ["i", "d"], arg := "a",
    argTy := (CoreLang.Ty.prod
  (CoreLang.Ty.refine
    (CoreLang.Ty.loc
      (CoreLang.Mode.pub)
      (CoreLang.Ty.array
        (CoreLang.Idx.add (CoreLang.Idx.add (CoreLang.Idx.var 1) (CoreLang.Idx.lit 1)) (CoreLang.Idx.var 0))
        (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
    (CoreLang.Pred.ini
      (CoreLang.Idx.add (CoreLang.Idx.add (CoreLang.Idx.var 1) (CoreLang.Idx.lit 1)) (CoreLang.Idx.var 0))))
  (CoreLang.Ty.prod
    (CoreLang.Ty.intS (CoreLang.Idx.var 1))
    (CoreLang.Ty.prod (CoreLang.Ty.intS (CoreLang.Idx.var 0)) (CoreLang.Ty.fix false (CoreLang.Wd.w64))))),
    retTy := (CoreLang.Ty.fix false (CoreLang.Wd.w64)),
    body := (CoreTerm.Expr.split
  (CoreTerm.At.var "a")
  "s"
  "r1"
  (CoreTerm.Expr.split
    (CoreTerm.At.var "r1")
    "iv"
    "r2"
    (CoreTerm.Expr.split
      (CoreTerm.At.var "r2")
      "dv"
      "cnt"
      (CoreTerm.Expr.let_
        "l"
        (CoreTerm.Op.idx (CoreTerm.At.var "s") (CoreTerm.At.var "iv"))
        (CoreTerm.Expr.let_
          "w"
          (CoreTerm.Op.load false (CoreTerm.At.var "l"))
          (CoreTerm.Expr.let_
            "j0"
            (CoreTerm.Op.atom (CoreTerm.At.lit 0))
            (CoreTerm.Expr.let_
              "cj"
              (CoreTerm.Op.pair (CoreTerm.At.var "cnt") (CoreTerm.At.var "j0"))
              (CoreTerm.Expr.let_
                "wc"
                (CoreTerm.Op.pair (CoreTerm.At.var "w") (CoreTerm.At.var "cj"))
                (CoreTerm.Expr.let_
                  "cnt1"
                  (CoreTerm.Op.call "emit8" [] (CoreTerm.At.var "wc") [])
                  (CoreTerm.Expr.ifeq
                    (CoreTerm.At.var "dv")
                    (CoreTerm.At.lit 0)
                    (CoreTerm.Expr.ret (CoreTerm.At.var "cnt1"))
                    (CoreTerm.Expr.let_
                      "d1"
                      (CoreTerm.Op.sub (CoreTerm.At.var "dv") (CoreTerm.At.lit 1))
                      (CoreTerm.Expr.let_
                        "un"
                        (CoreTerm.Op.nameI (CoreTerm.At.var "d1"))
                        (CoreTerm.Expr.let_
                          "i1"
                          (CoreTerm.Op.add (CoreTerm.At.var "iv") (CoreTerm.At.lit 1))
                          (CoreTerm.Expr.let_
                            "jn"
                            (CoreTerm.Op.nameI (CoreTerm.At.var "i1"))
                            (CoreTerm.Expr.let_
                              "q3"
                              (CoreTerm.Op.pair (CoreTerm.At.var "un") (CoreTerm.At.var "cnt1"))
                              (CoreTerm.Expr.let_
                                "q2"
                                (CoreTerm.Op.pair (CoreTerm.At.var "jn") (CoreTerm.At.var "q3"))
                                (CoreTerm.Expr.let_
                                  "q1"
                                  (CoreTerm.Op.pair (CoreTerm.At.var "s") (CoreTerm.At.var "q2"))
                                  (CoreTerm.Expr.tail "printL" ["jn", "un"] (CoreTerm.At.var "q1") [])))))))))))))))))) },
  { name := "print", idx := ["m"], arg := "a",
    argTy := (CoreLang.Ty.prod
  (CoreLang.Ty.prod
    (CoreLang.Ty.refine
      (CoreLang.Ty.loc
        (CoreLang.Mode.pub)
        (CoreLang.Ty.array (CoreLang.Idx.var 0) (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
      (CoreLang.Pred.ini (CoreLang.Idx.var 0)))
    (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
  (CoreLang.Ty.int)),
    retTy := (CoreLang.Ty.unit),
    body := (CoreTerm.Expr.split
  (CoreTerm.At.var "a")
  "sm"
  "n"
  (CoreTerm.Expr.split
    (CoreTerm.At.var "sm")
    "s"
    "mv"
    (CoreTerm.Expr.let_
      "cnt"
      (CoreTerm.Op.cvt false (CoreLang.Wd.w64) (CoreTerm.At.var "n"))
      (CoreTerm.Expr.ifeq
        (CoreTerm.At.var "mv")
        (CoreTerm.At.lit 0)
        (CoreTerm.Expr.ret (CoreTerm.At.unit))
        (CoreTerm.Expr.let_
          "k"
          (CoreTerm.Op.sub (CoreTerm.At.var "mv") (CoreTerm.At.lit 1))
          (CoreTerm.Expr.let_
            "kn"
            (CoreTerm.Op.nameI (CoreTerm.At.var "k"))
            (CoreTerm.Expr.let_
              "z"
              (CoreTerm.Op.nameI (CoreTerm.At.lit 0))
              (CoreTerm.Expr.let_
                "q3"
                (CoreTerm.Op.pair (CoreTerm.At.var "kn") (CoreTerm.At.var "cnt"))
                (CoreTerm.Expr.let_
                  "q2"
                  (CoreTerm.Op.pair (CoreTerm.At.var "z") (CoreTerm.At.var "q3"))
                  (CoreTerm.Expr.let_
                    "q1"
                    (CoreTerm.Op.pair (CoreTerm.At.var "s") (CoreTerm.At.var "q2"))
                    (CoreTerm.Expr.let_
                      "r"
                      (CoreTerm.Op.call "printL" ["z", "kn"] (CoreTerm.At.var "q1") [])
                      (CoreTerm.Expr.ret (CoreTerm.At.unit))))))))))))) }]

/-- The prelude source parses to exactly `prelude`. -/
def parsesTo (src : String) (p : Prog) : Bool :=
  match Syntax.parseProg src with
  | .ok q => q.length == p.length && (q.zip p).all fun (a, b) => Syntax.sameDecl a b
  | .error _ => false

#guard parsesTo preludeSrc prelude
#guard prelude.map (·.name) == ["spin", "exit", "emit8", "printL", "print"]
#guard accepts (checkProg prelude)

end EM0Prelude
