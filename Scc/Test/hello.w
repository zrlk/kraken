-- Hello, world: WeakCore's hello-world program text, with `main` written in
-- concrete syntax.  The setup block `rodata` builds the bytes on the heap
-- (static data by the heap-bytes route) and publishes them.  The order of
-- events: `main` spawns `worker` and sleeps (`waitLoop`: an acquire load of
-- the flag, parking while it is 0); `worker` prints the published slice with
-- the output extern, then wakes `main` (a release store of the flag and
-- `unpark`) and exits; `main` sees the flag and returns 0.
--
-- Provisional forms (see Scc/Frontend.lean): `spawn{f}(a)` is the spawn;
-- `print` with this signature is the runtime's output extern on a published
-- slice, and `printL` is its loop.  Both are written textually as the
-- extern's WeakCore model on a published slice (`printExtPubD`,
-- `printLoopPubD` in Scc/PrintModel.lean: `printExtD`/`printLoopD` with
-- `pub` for `own` and `load b[iv]` as `let l = b[iv]` then `load l`) and are
-- not compiled.  `park`, `unpark` and `ThreadId` are WeakCore's own.

def printL{i, d}(a : (({Loc pub Array[i+1+d] LanesU8 | ini >= i+1+d} * Int[i]) * Int[d]) * ((Int * Int) * Int)) : Unit =
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
      let l = b[iv]
      let wd = load l
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

def print{m}(a : ({Loc pub Array[m] LanesU8 | ini >= m} * Int[m]) * Int) : Unit =
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

def rodata(u : Unit) : exists q. ({Loc pub Array[q] LanesU8 | ini >= q} * Int[q]) * Int =
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

def main(a : (exists q. ({Loc pub Array[q] LanesU8 | ini >= q} * Int[q]) * Int) * ThreadId) : Int =
  let (sl, me) = a
  let z = zero[Int]
  let o = new[Int] z
  let c = publish o
  let p0 = (sl, c)
  let p = (p0, me)
  let t = spawn{worker}(p)
  tail waitLoop(c)
