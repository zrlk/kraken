import Scc.Cert.SrcTerm
import Scc.Test.Src
import Spike.Lib.X64WakeA64

/-!
# `hello.w`'s source program and source machine (x86-64 side)

`helloSrc` is the program the frontend reads from `Scc/Test/hello.w`
(`printL`, `print`, the setup block `rodata`, `worker`, `waitLoop`, `main`),
written out as a term (the output of `Scc.Cert.SrcTerm.progTerm`) so that the
kernel can reduce scc's pipeline on it (the frontend's parser is `partial`).
`helloSrcOk` checks, by evaluation, that the frontend reads `Scc/Test/hello.w`
as it (`Scc.Cert.SrcTerm.reads`).

`helloS` is wake's two-thread source machine at `helloSrc`: `Scc.Sem.SrcSem.source` of
`X64WakeT1.srcPo 2` (which is `Scc.Sem.SrcSem.srcPo`, `X64WakeT1.srcPo_eq`). Its `main` takes
`S * ThreadId`, so it starts before the setup block on the main thread's own `ThreadId`
(`hello_start`: `X64WakeT1.setupStartT 2`), where wake's starts at `main` (`X64WakeT1.wake_start`).

Unlike AArch64 (`Spike/Lib/HelloSrc.lean`), this module does not import `Spike.Lib.WakeA64`
(it reaches AArch64's syntax), and there is no `srcS` abbreviation: `helloS` unfolds directly to the
source machine. The literal is the same term (both are compared with `Scc/Test/hello.w` by `#guard`).
-/

namespace Spike.Lib.X64HelloSrc

open Spike.Lib.X64WakeT1

/-- **hello.w**, elaborated (`Scc.Cert.SrcTerm.progTerm` of the frontend's reading). -/
def helloSrc : CoreTerm.Prog :=
  [{
    name := "printL",
    tparams := [],
    idx := ["i", "d"],
    arg := "a",
    argTy := CoreLang.Ty.prod
        (CoreLang.Ty.prod
          (CoreLang.Ty.prod
            (CoreLang.Ty.refine
              (CoreLang.Ty.loc
                (CoreLang.Mode.pub)
                (CoreLang.Ty.array
                  (CoreLang.Idx.add
                    (CoreLang.Idx.add (CoreLang.Idx.var 1) (CoreLang.Idx.lit 1))
                    (CoreLang.Idx.var 0))
                  (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
              (CoreLang.Pred.ini
                (CoreLang.Idx.add
                  (CoreLang.Idx.add (CoreLang.Idx.var 1) (CoreLang.Idx.lit 1))
                  (CoreLang.Idx.var 0))))
            (CoreLang.Ty.intS (CoreLang.Idx.var 1)))
          (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
        (CoreLang.Ty.prod (CoreLang.Ty.prod (CoreLang.Ty.int) (CoreLang.Ty.int)) (CoreLang.Ty.int)),
    retTy := CoreLang.Ty.unit,
    body := CoreTerm.Expr.split
        (CoreTerm.At.var "a")
        "w"
        "q"
        (CoreTerm.Expr.split
          (CoreTerm.At.var "w")
          "bi"
          "dv"
          (CoreTerm.Expr.split
            (CoreTerm.At.var "bi")
            "b"
            "iv"
            (CoreTerm.Expr.split
              (CoreTerm.At.var "q")
              "cn"
              "j"
              (CoreTerm.Expr.split
                (CoreTerm.At.var "cn")
                "c"
                "n"
                (CoreTerm.Expr.ifeq
                  (CoreTerm.At.var "c")
                  (CoreTerm.At.var "n")
                  (CoreTerm.Expr.ret (CoreTerm.At.unit))
                  (CoreTerm.Expr.ifeq
                    (CoreTerm.At.var "j")
                    (CoreTerm.At.lit 8)
                    (CoreTerm.Expr.ifeq
                      (CoreTerm.At.var "dv")
                      (CoreTerm.At.lit 0)
                      (CoreTerm.Expr.ret (CoreTerm.At.unit))
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
                                "bi1"
                                (CoreTerm.Op.pair (CoreTerm.At.var "b") (CoreTerm.At.var "jn"))
                                (CoreTerm.Expr.let_
                                  "w1"
                                  (CoreTerm.Op.pair (CoreTerm.At.var "bi1") (CoreTerm.At.var "un"))
                                  (CoreTerm.Expr.let_
                                    "z"
                                    (CoreTerm.Op.atom (CoreTerm.At.lit 0))
                                    (CoreTerm.Expr.let_
                                      "q1"
                                      (CoreTerm.Op.pair
                                        (CoreTerm.At.var "cn")
                                        (CoreTerm.At.var "z"))
                                      (CoreTerm.Expr.let_
                                        "a1"
                                        (CoreTerm.Op.pair
                                          (CoreTerm.At.var "w1")
                                          (CoreTerm.At.var "q1"))
                                        (CoreTerm.Expr.tail
                                          "printL"
                                          ["jn", "un"]
                                          (CoreTerm.At.var "a1")
                                          [])))))))))))
                    (CoreTerm.Expr.let_
                      "l"
                      (CoreTerm.Op.idx (CoreTerm.At.var "b") (CoreTerm.At.var "iv"))
                      (CoreTerm.Expr.let_
                        "wd"
                        (CoreTerm.Op.load false (CoreTerm.At.var "l"))
                        (CoreTerm.Expr.let_
                          "x"
                          (CoreTerm.Op.lane (CoreTerm.At.var "wd") (CoreTerm.At.var "j"))
                          (CoreTerm.Expr.let_
                            "r"
                            (CoreTerm.Op.ext (CoreTerm.ExtName.emit) (CoreTerm.At.var "x"))
                            (CoreTerm.Expr.let_
                              "c1"
                              (CoreTerm.Op.add (CoreTerm.At.var "c") (CoreTerm.At.lit 1))
                              (CoreTerm.Expr.let_
                                "j1"
                                (CoreTerm.Op.add (CoreTerm.At.var "j") (CoreTerm.At.lit 1))
                                (CoreTerm.Expr.let_
                                  "cn1"
                                  (CoreTerm.Op.pair (CoreTerm.At.var "c1") (CoreTerm.At.var "n"))
                                  (CoreTerm.Expr.let_
                                    "q1"
                                    (CoreTerm.Op.pair
                                      (CoreTerm.At.var "cn1")
                                      (CoreTerm.At.var "j1"))
                                    (CoreTerm.Expr.let_
                                      "bi2"
                                      (CoreTerm.Op.pair
                                        (CoreTerm.At.var "b")
                                        (CoreTerm.At.var "iv"))
                                      (CoreTerm.Expr.let_
                                        "w2"
                                        (CoreTerm.Op.pair
                                          (CoreTerm.At.var "bi2")
                                          (CoreTerm.At.var "dv"))
                                        (CoreTerm.Expr.let_
                                          "a1"
                                          (CoreTerm.Op.pair
                                            (CoreTerm.At.var "w2")
                                            (CoreTerm.At.var "q1"))
                                          (CoreTerm.Expr.tail
                                            "printL"
                                            ["i", "d"]
                                            (CoreTerm.At.var "a1")
                                            [])))))))))))))))))) },
  {
    name := "print",
    tparams := [],
    idx := ["m"],
    arg := "a",
    argTy := CoreLang.Ty.prod
        (CoreLang.Ty.prod
          (CoreLang.Ty.refine
            (CoreLang.Ty.loc
              (CoreLang.Mode.pub)
              (CoreLang.Ty.array (CoreLang.Idx.var 0) (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
            (CoreLang.Pred.ini (CoreLang.Idx.var 0)))
          (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
        (CoreLang.Ty.int),
    retTy := CoreLang.Ty.unit,
    body := CoreTerm.Expr.split
        (CoreTerm.At.var "a")
        "bm"
        "n"
        (CoreTerm.Expr.split
          (CoreTerm.At.var "bm")
          "b"
          "mv"
          (CoreTerm.Expr.ifeq
            (CoreTerm.At.var "mv")
            (CoreTerm.At.lit 0)
            (CoreTerm.Expr.ret (CoreTerm.At.unit))
            (CoreTerm.Expr.let_
              "m1"
              (CoreTerm.Op.sub (CoreTerm.At.var "mv") (CoreTerm.At.lit 1))
              (CoreTerm.Expr.let_
                "mn"
                (CoreTerm.Op.nameI (CoreTerm.At.var "m1"))
                (CoreTerm.Expr.let_
                  "z"
                  (CoreTerm.Op.nameI (CoreTerm.At.lit 0))
                  (CoreTerm.Expr.let_
                    "bi"
                    (CoreTerm.Op.pair (CoreTerm.At.var "b") (CoreTerm.At.var "z"))
                    (CoreTerm.Expr.let_
                      "w"
                      (CoreTerm.Op.pair (CoreTerm.At.var "bi") (CoreTerm.At.var "mn"))
                      (CoreTerm.Expr.let_
                        "c0"
                        (CoreTerm.Op.atom (CoreTerm.At.lit 0))
                        (CoreTerm.Expr.let_
                          "j0"
                          (CoreTerm.Op.atom (CoreTerm.At.lit 0))
                          (CoreTerm.Expr.let_
                            "cn"
                            (CoreTerm.Op.pair (CoreTerm.At.var "c0") (CoreTerm.At.var "n"))
                            (CoreTerm.Expr.let_
                              "q"
                              (CoreTerm.Op.pair (CoreTerm.At.var "cn") (CoreTerm.At.var "j0"))
                              (CoreTerm.Expr.let_
                                "a1"
                                (CoreTerm.Op.pair (CoreTerm.At.var "w") (CoreTerm.At.var "q"))
                                (CoreTerm.Expr.tail
                                  "printL"
                                  ["z", "mn"]
                                  (CoreTerm.At.var "a1")
                                  []))))))))))))) },
  {
    name := "rodata",
    tparams := [],
    idx := [],
    arg := "u",
    argTy := CoreLang.Ty.unit,
    retTy := CoreLang.Ty.iex
        (CoreLang.Ty.prod
          (CoreLang.Ty.prod
            (CoreLang.Ty.refine
              (CoreLang.Ty.loc
                (CoreLang.Mode.pub)
                (CoreLang.Ty.array (CoreLang.Idx.var 0) (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
              (CoreLang.Pred.ini (CoreLang.Idx.var 0)))
            (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
          (CoreLang.Ty.int)),
    body := CoreTerm.Expr.let_
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
                (CoreTerm.Op.xchgAt
                  (CoreTerm.At.var "b")
                  (CoreTerm.At.lit 0)
                  (CoreTerm.At.var "w0"))
                (CoreTerm.Expr.let_
                  "w1"
                  (CoreTerm.Op.asLanes false (CoreLang.Wd.w8) (CoreTerm.At.lit 44634501743))
                  (CoreTerm.Expr.let_
                    "o1"
                    (CoreTerm.Op.xchgAt
                      (CoreTerm.At.var "b")
                      (CoreTerm.At.lit 1)
                      (CoreTerm.At.var "w1"))
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
                                          (CoreLang.Ty.array
                                            (CoreLang.Idx.var 0)
                                            (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
                                        (CoreLang.Pred.ini (CoreLang.Idx.var 0)))
                                      (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
                                    (CoreLang.Ty.int))))
                              (CoreTerm.Expr.ret (CoreTerm.At.var "sl"))))))))))))) },
  {
    name := "worker",
    tparams := [],
    idx := [],
    arg := "a",
    argTy := CoreLang.Ty.prod
        (CoreLang.Ty.prod
          (CoreLang.Ty.iex
            (CoreLang.Ty.prod
              (CoreLang.Ty.prod
                (CoreLang.Ty.refine
                  (CoreLang.Ty.loc
                    (CoreLang.Mode.pub)
                    (CoreLang.Ty.array
                      (CoreLang.Idx.var 0)
                      (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
                  (CoreLang.Pred.ini (CoreLang.Idx.var 0)))
                (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
              (CoreLang.Ty.int)))
          (CoreLang.Ty.ptr (CoreLang.Mode.pub) (CoreLang.Ty.int)))
        (CoreLang.Ty.tid),
    retTy := CoreLang.Ty.unit,
    body := CoreTerm.Expr.split
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
                  (CoreTerm.Op.ext (CoreTerm.ExtName.unpark) (CoreTerm.At.var "j"))
                  (CoreTerm.Expr.ret (CoreTerm.At.unit))))))) },
  {
    name := "waitLoop",
    tparams := [],
    idx := [],
    arg := "c",
    argTy := CoreLang.Ty.ptr (CoreLang.Mode.pub) (CoreLang.Ty.int),
    retTy := CoreLang.Ty.int,
    body := CoreTerm.Expr.let_
        "d"
        (CoreTerm.Op.load true (CoreTerm.At.var "c"))
        (CoreTerm.Expr.ifeq
          (CoreTerm.At.var "d")
          (CoreTerm.At.lit 1)
          (CoreTerm.Expr.ret (CoreTerm.At.lit 0))
          (CoreTerm.Expr.let_
            "p"
            (CoreTerm.Op.ext (CoreTerm.ExtName.park) (CoreTerm.At.unit))
            (CoreTerm.Expr.tail "waitLoop" [] (CoreTerm.At.var "c") []))) },
  {
    name := "main",
    tparams := [],
    idx := [],
    arg := "a",
    argTy := CoreLang.Ty.prod
        (CoreLang.Ty.iex
          (CoreLang.Ty.prod
            (CoreLang.Ty.prod
              (CoreLang.Ty.refine
                (CoreLang.Ty.loc
                  (CoreLang.Mode.pub)
                  (CoreLang.Ty.array
                    (CoreLang.Idx.var 0)
                    (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
                (CoreLang.Pred.ini (CoreLang.Idx.var 0)))
              (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
            (CoreLang.Ty.int)))
        (CoreLang.Ty.tid),
    retTy := CoreLang.Ty.int,
    body := CoreTerm.Expr.split
        (CoreTerm.At.var "a")
        "sl"
        "me"
        (CoreTerm.Expr.let_
          "z"
          (CoreTerm.Op.zero (CoreLang.Ty.int))
          (CoreTerm.Expr.let_
            "o"
            (CoreTerm.Op.new (CoreTerm.At.var "z") (some (CoreLang.Ty.int)))
            (CoreTerm.Expr.let_
              "c"
              (CoreTerm.Op.publish (CoreTerm.At.var "o"))
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
                                    (CoreLang.Ty.array
                                      (CoreLang.Idx.var 0)
                                      (CoreLang.Ty.lanes false (CoreLang.Wd.w8))))
                                  (CoreLang.Pred.ini (CoreLang.Idx.var 0)))
                                (CoreLang.Ty.intS (CoreLang.Idx.var 0)))
                              (CoreLang.Ty.int)))
                          (CoreLang.Ty.ptr (CoreLang.Mode.pub) (CoreLang.Ty.int)))
                        (CoreLang.Ty.tid))
                      [])
                    (CoreTerm.Expr.tail "waitLoop" [] (CoreTerm.At.var "c") []))))))) }]

/-- **`helloSrc` is the frontend's reading of `Scc/Test/hello.w`** (compared by
printed forms, `SrcTerm.reads`: `Decl` has no equality instance). -/
def helloSrcOk : Bool := Scc.Cert.SrcTerm.reads (w_src% "Scc/Test/hello.w") helloSrc

#guard helloSrcOk

/-- **hello.w's start**: before the setup block, on the main thread's own `ThreadId`. -/
theorem hello_start : progInitT helloSrc 2 = (· = setupStartT 2) := by unfold progInitT; rfl

/-- **The source semantics of hello.w** at `n = 2` (wake's source machine at `helloSrc`). -/
abbrev helloS (arch : WeakMem.Arch) : Scc.Sem.SrcSem := Scc.Sem.SrcSem.source (srcPo 2 arch helloSrc) helloSrc

/-- `helloS` is the neutral source machine `Scc.Sem.SrcSem.srcPo` at `helloSrc`. -/
theorem helloS_eq (arch : WeakMem.Arch) :
    helloS arch = Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcPo 2 arch helloSrc) helloSrc := by
  rw [helloS, srcPo_eq]

end Spike.Lib.X64HelloSrc

/-- info: 'Spike.Lib.X64HelloSrc.hello_start' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrc.hello_start
