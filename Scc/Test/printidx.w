-- The pre-rewrite hello.w (owned print, compiled printL), kept for its checked index `+`.
-- concrete syntax.  The setup block `rodata` builds the bytes on the heap
-- (static data by the heap-bytes route); `main` spawns `worker`, which prints
-- the slice and signals `main` through a release store and `unpark`; `main`
-- waits with an acquire load and `park`, then returns 0.
--
-- Provisional forms (see Scc/Frontend.lean): `spawn{f}(a)` is the spawn;
-- `print` with this signature is the runtime's output extern, and its body
-- here is a WeakCore model that is not compiled.  `park`, `unpark` and
-- `ThreadId` are WeakCore's own.

def spin(n : Int) : Void =
  tail spin(n)

def emit8(a : LanesU8 * U64) : U64 =
  let (w, cnt0) = a
  let nil = cvt U64 0
  let one = cvt U64 1
  let b0 = lane w 0
  let z0 = fcmp eq cnt0 nil
  if z0 = 1 then
    ret cnt0
  else
    let e0 = toInt b0
    let cnt1 = fop sub cnt0 one
    let b1 = lane w 1
    let z1 = fcmp eq cnt1 nil
    if z1 = 1 then
      ret cnt1
    else
      let e1 = toInt b1
      let cnt2 = fop sub cnt1 one
      let b2 = lane w 2
      let z2 = fcmp eq cnt2 nil
      if z2 = 1 then
        ret cnt2
      else
        let e2 = toInt b2
        let cnt3 = fop sub cnt2 one
        let b3 = lane w 3
        let z3 = fcmp eq cnt3 nil
        if z3 = 1 then
          ret cnt3
        else
          let e3 = toInt b3
          let cnt4 = fop sub cnt3 one
          let b4 = lane w 4
          let z4 = fcmp eq cnt4 nil
          if z4 = 1 then
            ret cnt4
          else
            let e4 = toInt b4
            let cnt5 = fop sub cnt4 one
            let b5 = lane w 5
            let z5 = fcmp eq cnt5 nil
            if z5 = 1 then
              ret cnt5
            else
              let e5 = toInt b5
              let cnt6 = fop sub cnt5 one
              let b6 = lane w 6
              let z6 = fcmp eq cnt6 nil
              if z6 = 1 then
                ret cnt6
              else
                let e6 = toInt b6
                let cnt7 = fop sub cnt6 one
                let b7 = lane w 7
                let z7 = fcmp eq cnt7 nil
                if z7 = 1 then
                  ret cnt7
                else
                  let e7 = toInt b7
                  let cnt8 = fop sub cnt7 one
                  ret cnt8

def printL{i, d}(a : {Loc pub Array[i+1+d] LanesU8 | ini >= i+1+d} * Int[i] * Int[d] * U64) : U64 =
  let (s, r1) = a
  let (iv, r2) = r1
  let (dv, cnt) = r2
  let l = s[iv]
  let w = load l
  let wc = (w, cnt)
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
