-- `hello1.w` with `print`'s WeakCore model written out: its `emit` loop
-- `printL` (`printLoopD`, `Scc/PrintModel.lean`), which the frontend takes as
-- part of the extern (neither checked nor compiled).
--
-- Hello, world on one thread: the setup block `rodata` builds the bytes on
-- the heap (static data by the heap-bytes route); `main` prints them with the
-- output extern and returns 0.  No spawn, no park/unpark, and no `publish`
-- (the program is publish-free, `Scc.Sem.PubFree.ProgPubFree`): the slice
-- stays owned and `print` takes it by its owned signature (`printOwnSig`),
-- consuming it.  `print`'s body is a WeakCore model that is not compiled;
-- `ThreadId` is stubbed as `Ptr pub Void`.

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

def rodata(u : Unit) : exists q. ({Loc own Array[q] LanesU8 | ini >= q} * Int[q]) * Int =
  let two = 2
  let m = nameI two
  let b = newBuf[LanesU8] m
  let w0 = asLanes U8 8583909746840200520
  let o0 = xchg b[0] w0
  let w1 = asLanes U8 44634501743
  let o1 = xchg b[1] w1
  let n = 13
  let sm = (b, m)
  let sl0 = (sm, n)
  let sl = pack sl0 at m : exists a. ({Loc own Array[a] LanesU8 | ini >= a} * Int[a]) * Int
  ret sl

def main(a : (exists q. ({Loc own Array[q] LanesU8 | ini >= q} * Int[q]) * Int) * Ptr pub Void) : Int =
  let (sl0, me) = a
  let <q, sl> = unpack sl0
  let u = print{q}(sl)
  ret 0
