/-
**Prototype: `print` as a WeakCore loop of `emit`s** (design spike for
output). hello1's `print` has the owned-slice signature (`printOwnSig`) and
today's body `ret ()`, so its source prints nothing. Here its body is an
ordinary WeakCore model: for each of the first `n` bytes, load the slice's
word, take the lane, `emit` it. The model is a well-typed WeakCore program
(`checkProg`), and the only part of it outside scc's accepted fragment is
the extern call itself (`acceptDiags`): accepting `emit` (one byte per
call) is the scc change this source model asks for.
-/
import WeakCore.Syntax
import Scc.Frontend

namespace Spike.Test.PrintEmitLoop

open CoreLang CoreTerm

/-- `print` and its loop `printL{i, d}` (word `i` of the slice, `d` words
after it; `c` bytes emitted of `n`, lane `j` of word `i`). -/
def src : String := "
def printL{i, d}(a : (({Loc own Array[i+1+d] LanesU8 | ini >= i+1+d} * Int[i]) * Int[d]) * ((Int * Int) * Int)) : Unit =
  let (w, q) = a
  let (bi, dv) = w
  let (b, iv) = bi
  let (cn, j) = q
  let (c, n) = cn
  if c = n then
    ret ()
  else
    if j = 8 then
      if dv = 0 then
        ret ()
      else
        let d1 = dv - 1
        let un = nameI d1
        let i1 = iv + 1
        let jn = nameI i1
        let bi1 = (b, jn)
        let w1 = (bi1, un)
        let z = 0
        let q1 = (cn, z)
        let a1 = (w1, q1)
        tail printL{jn, un}(a1)
    else
      let wd = load b[iv]
      let x = lane wd j
      let r = emit x
      let c1 = c + 1
      let j1 = j + 1
      let cn1 = (c1, n)
      let q1 = (cn1, j1)
      let bi2 = (b, iv)
      let w2 = (bi2, dv)
      let a1 = (w2, q1)
      tail printL{i, d}(a1)

def print{m}(a : ({Loc own Array[m] LanesU8 | ini >= m} * Int[m]) * Int) : Unit =
  let (bm, n) = a
  let (b, mv) = bm
  if mv = 0 then
    ret ()
  else
    let m1 = mv - 1
    let mn = nameI m1
    let z = nameI 0
    let bi = (b, z)
    let w = (bi, mn)
    let c0 = 0
    let j0 = 0
    let cn = (c0, n)
    let q = (cn, j0)
    let a1 = (w, q)
    tail printL{z, mn}(a1)
"

/-- The parsed program. -/
def prog : Prog := (Syntax.parseProg src).toOption.getD []

#guard prog.map (·.name) == ["printL", "print"]

-- A well-typed WeakCore program.
#guard accepts (checkProg prog)

-- In scc's fragment: `printL` is now the output extern's loop (`declIs
-- printLoopD`, `Scc/PrintModel.lean`), part of the extern, so `acceptDiags`
-- skips it.
#guard (Scc.Frontend.acceptDiags "" prog).map (·.msg) == []

end Spike.Test.PrintEmitLoop
