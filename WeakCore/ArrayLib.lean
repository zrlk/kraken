import WeakCore.Syntax
import WeakCore.TermSmoke

/-!
# ArrayLib — higher-order functions over own buffers

`map`, `fold_left`, `iter` and `iter_i` over buffers
`{Loc own Array[n] A | ini >= n}` (and the borrowing `fold_left_r`, `iter_r`), each taking a *closure-converted closure*
as its function parameter, written in CoreLang source (`Syntax.lean`), checked
by `checkProg` and run on the machine.

## The closure type

A closure is CoreLang's region arrow, `CoreLang.arrowRgn .bor σ τ`, written
`Fn(σ, τ)` in source:

  `exists (E : *). exists s. (Code(exists q. (σ * Cap[bor, q]) * Ptr[q] E, τ) * Ptr[s] E) * Cap[bor, s]`

a type existential (24e) over the environment's type `E` and an index
existential over the environment's region `s`, with a capability for `s`.
The code block receives the element and the *environment pointer* (24f), and
the capability to use it.  Passing the pointer is what lets a closure keep
state across calls (the `iter` example below counts into its environment).

The environment lives in any region the caller has a capability for, so
nothing has to be published: an own cell opened with `region` and lent with
`borrow bor t` works, and so does a published one (`openPub`, whose `Cap pub`
subsumes into `Cap[bor, s]`; `demoIterI`).  The region is bound *in the code
block's argument* (`exists q`), not as a parameter of the block, because
`fnptr` takes only monomorphic blocks; each call site packs its region with
`pack p0 at s : …`.  The capability makes a `Fn` second-class: it may be
passed, never stored or returned, and `endBorrow` on the environment's token
takes it away.  (`arrowRgn .pub` is first-class.)

Each loop step opens the package twice (`unpack` is free: witnesses are
erased), and passes the package itself on to the next step.  The opened `E`
cannot be passed on as a type argument instead: the checker refuses a type
argument that exposes an unpacked type, because the machine erases the
witness, so a callee could not lay out a value of type `E`.

## Loops and bounds

Every loop follows `FlatHashMap.mvGD`: index parameters `{i, d}` with the
length written `i+1+d`, so `i < i+1+d` is a static fact and `load b[i]`,
`xchg b[i] v` and `bufInit b i v` need no dynamic bounds check.  `d = 0` ends
the loop; otherwise the `else` branch knows `d = d'+1` and the recursive call
is at `{i+1, d-1}`.  The top-level wrapper `{n}` handles `n = 0` and starts
the loop at `{0, n-1}`.  `map` fills a fresh `newBuf[B] n` slot by slot with
`bufInit` (the slot must be the next uninitialised one), so `B` needs no
`zero` kind; `iter`/`iter_i` update in place with `load` then `xchg` (the
closure returns the new element, as with Rust's `iter_mut`).

## Borrowing instead of passing ownership

An own buffer is affine, so `fold_left` above must hand it back: it returns
`C * {Loc own …}`, and the caller rebinds the array.  `fold_left_r` and
`iter_r` borrow instead.  The caller opens the buffer as a region,
`let <r, p, t> = region b` (a region over an own buffer directly, without a
`new` cell around it), takes a capability from the token (`borrow rd t` for
reading, `borrow bor t` for writing) and passes the capability with the region
locative `p : {Loc[r] Array[n] A | ini >= n}`.  Both are copyable, so the
functions return just `C` (or `Unit`), and the caller may call them again.
`endBorrow t` gives the token back, and with it plain access through `p`.
The element kind adds `insens`: a load under a capability of a view-sensitive
type needs `acq` (§3.8), and these loops use plain loads.
-/

open CoreLang CoreTerm TermRun TermSmoke Syntax WeakMem

namespace ArrayLib

/-- The library, as CoreLang source. -/
def libSrc : String := "
-- map: dst[j] := f(src[j]), for a fresh dst.
def mapL[A : {copy}, B : *]{i, d}(a : Fn(A, B) * {Loc own Array[i+1+d] A | ini >= i+1+d} * {Loc own Array[i+1+d] B | ini >= i} * Int[i] * Int[d]) : {Loc own Array[i+1+d] A | ini >= i+1+d} * {Loc own Array[i+1+d] B | ini >= i+1+d} =
  let (f, r1) = a
  let (src, r2) = r1
  let (dst, r3) = r2
  let (iv, dv) = r3
  let <[E], g> = unpack f
  let <s, h> = unpack g
  let (ce, kf) = h
  let (c, env) = ce
  let x = load src[iv]
  let xk = (x, kf)
  let p0 = (xk, env)
  let p = pack p0 at s : exists q. (A * Cap[bor, q]) * Ptr[q] E
  let y = callc c p
  let dst1 = bufInit dst iv y
  if dv = 0 then
    let o = (src, dst1)
    ret o
  else
    let d1 = dv - 1
    let un = nameI d1
    let i1 = iv + 1
    let jn = nameI i1
    let q3 = (jn, un)
    let q2 = (dst1, q3)
    let q1 = (src, q2)
    let q0 = (f, q1)
    tail mapL[A, B]{jn, un}(q0)

def map[A : {copy}, B : *]{n}(a : Fn(A, B) * {Loc own Array[n] A | ini >= n} * Int[n]) : {Loc own Array[n] A | ini >= n} * {Loc own Array[n] B | ini >= n} =
  let (f, r1) = a
  let (src, nv) = r1
  let dst = newBuf[B] nv
  if nv = 0 then
    let o = (src, dst)
    ret o
  else
    let m = nv - 1
    let mn = nameI m
    let z = nameI 0
    let q3 = (z, mn)
    let q2 = (dst, q3)
    let q1 = (src, q2)
    let q0 = (f, q1)
    let res = mapL[A, B]{z, mn}(q0)
    ret res

-- fold_left: acc := f(acc, src[j]), left to right.
def foldL[A : {copy}, C : *]{i, d}(a : Fn(C * A, C) * C * {Loc own Array[i+1+d] A | ini >= i+1+d} * Int[i] * Int[d]) : C * {Loc own Array[i+1+d] A | ini >= i+1+d} =
  let (f, r1) = a
  let (acc, r2) = r1
  let (src, r3) = r2
  let (iv, dv) = r3
  let <[E], g> = unpack f
  let <s, h> = unpack g
  let (ce, kf) = h
  let (c, env) = ce
  let x = load src[iv]
  let ax = (acc, x)
  let axk = (ax, kf)
  let p0 = (axk, env)
  let p = pack p0 at s : exists q. ((C * A) * Cap[bor, q]) * Ptr[q] E
  let acc1 = callc c p
  if dv = 0 then
    let o = (acc1, src)
    ret o
  else
    let d1 = dv - 1
    let un = nameI d1
    let i1 = iv + 1
    let jn = nameI i1
    let q3 = (jn, un)
    let q2 = (src, q3)
    let q1 = (acc1, q2)
    let q0 = (f, q1)
    tail foldL[A, C]{jn, un}(q0)

def fold_left[A : {copy}, C : *]{n}(a : Fn(C * A, C) * C * {Loc own Array[n] A | ini >= n} * Int[n]) : C * {Loc own Array[n] A | ini >= n} =
  let (f, r1) = a
  let (acc, r2) = r1
  let (src, nv) = r2
  if nv = 0 then
    let o = (acc, src)
    ret o
  else
    let m = nv - 1
    let mn = nameI m
    let z = nameI 0
    let q3 = (z, mn)
    let q2 = (src, q3)
    let q1 = (acc, q2)
    let q0 = (f, q1)
    let res = foldL[A, C]{z, mn}(q0)
    ret res

-- iter: b[j] := f(b[j]), in place.
def iterL[A : {copy}]{i, d}(a : Fn(A, A) * {Loc own Array[i+1+d] A | ini >= i+1+d} * Int[i] * Int[d]) : {Loc own Array[i+1+d] A | ini >= i+1+d} =
  let (f, r1) = a
  let (b, r2) = r1
  let (iv, dv) = r2
  let <[E], g> = unpack f
  let <s, h> = unpack g
  let (ce, kf) = h
  let (c, env) = ce
  let x = load b[iv]
  let xk = (x, kf)
  let p0 = (xk, env)
  let p = pack p0 at s : exists q. (A * Cap[bor, q]) * Ptr[q] E
  let y = callc c p
  let old = xchg b[iv] y
  if dv = 0 then
    ret b
  else
    let d1 = dv - 1
    let un = nameI d1
    let i1 = iv + 1
    let jn = nameI i1
    let q2 = (jn, un)
    let q1 = (b, q2)
    let q0 = (f, q1)
    tail iterL[A]{jn, un}(q0)

def iter[A : {copy}]{n}(a : Fn(A, A) * {Loc own Array[n] A | ini >= n} * Int[n]) : {Loc own Array[n] A | ini >= n} =
  let (f, r1) = a
  let (b, nv) = r1
  if nv = 0 then
    ret b
  else
    let m = nv - 1
    let mn = nameI m
    let z = nameI 0
    let q2 = (z, mn)
    let q1 = (b, q2)
    let q0 = (f, q1)
    let res = iterL[A]{z, mn}(q0)
    ret res

-- iter_i: b[j] := f(j, b[j]), in place.
def iterIL[A : {copy}]{i, d}(a : Fn(Int * A, A) * {Loc own Array[i+1+d] A | ini >= i+1+d} * Int[i] * Int[d]) : {Loc own Array[i+1+d] A | ini >= i+1+d} =
  let (f, r1) = a
  let (b, r2) = r1
  let (iv, dv) = r2
  let <[E], g> = unpack f
  let <s, h> = unpack g
  let (ce, kf) = h
  let (c, env) = ce
  let x = load b[iv]
  let ix = (iv, x)
  let ixk = (ix, kf)
  let p0 = (ixk, env)
  let p = pack p0 at s : exists q. ((Int * A) * Cap[bor, q]) * Ptr[q] E
  let y = callc c p
  let old = xchg b[iv] y
  if dv = 0 then
    ret b
  else
    let d1 = dv - 1
    let un = nameI d1
    let i1 = iv + 1
    let jn = nameI i1
    let q2 = (jn, un)
    let q1 = (b, q2)
    let q0 = (f, q1)
    tail iterIL[A]{jn, un}(q0)

def iter_i[A : {copy}]{n}(a : Fn(Int * A, A) * {Loc own Array[n] A | ini >= n} * Int[n]) : {Loc own Array[n] A | ini >= n} =
  let (f, r1) = a
  let (b, nv) = r1
  if nv = 0 then
    ret b
  else
    let m = nv - 1
    let mn = nameI m
    let z = nameI 0
    let q2 = (z, mn)
    let q1 = (b, q2)
    let q0 = (f, q1)
    let res = iterIL[A]{z, mn}(q0)
    ret res

-- fold_left, borrowing: reads through a region locative under a read capability.
def foldRL[A : {copy, insens}, C : *]{r, i, d}(a : Fn(C * A, C) * C * Cap[rd, r] * {Loc[r] Array[i+1+d] A | ini >= i+1+d} * Int[i] * Int[d]) : C =
  let (f, r1) = a
  let (acc, r2) = r1
  let (k, r3) = r2
  let (src, r4) = r3
  let (iv, dv) = r4
  let <[E], g> = unpack f
  let <s, h> = unpack g
  let (ce, kf) = h
  let (c, env) = ce
  let l = src[iv]
  let x = load l
  let ax = (acc, x)
  let axk = (ax, kf)
  let p0 = (axk, env)
  let p = pack p0 at s : exists q. ((C * A) * Cap[bor, q]) * Ptr[q] E
  let acc1 = callc c p
  if dv = 0 then
    ret acc1
  else
    let d1 = dv - 1
    let un = nameI d1
    let i1 = iv + 1
    let jn = nameI i1
    let q4 = (jn, un)
    let q3 = (src, q4)
    let q2 = (k, q3)
    let q1 = (acc1, q2)
    let q0 = (f, q1)
    tail foldRL[A, C]{r, jn, un}(q0)

def fold_left_r[A : {copy, insens}, C : *]{r, n}(a : Fn(C * A, C) * C * Cap[rd, r] * {Loc[r] Array[n] A | ini >= n} * Int[n]) : C =
  let (f, r1) = a
  let (acc, r2) = r1
  let (k, r3) = r2
  let (src, nv) = r3
  if nv = 0 then
    ret acc
  else
    let m = nv - 1
    let mn = nameI m
    let z = nameI 0
    let q4 = (z, mn)
    let q3 = (src, q4)
    let q2 = (k, q3)
    let q1 = (acc, q2)
    let q0 = (f, q1)
    let res = foldRL[A, C]{r, z, mn}(q0)
    ret res

-- iter, borrowing: writes through a region locative under a borrow capability.
def iterRL[A : {copy, insens}]{r, i, d}(a : Fn(A, A) * Cap[bor, r] * {Loc[r] Array[i+1+d] A | ini >= i+1+d} * Int[i] * Int[d]) : Unit =
  let (f, r1) = a
  let (k, r2) = r1
  let (b, r3) = r2
  let (iv, dv) = r3
  let <[E], g> = unpack f
  let <s, h> = unpack g
  let (ce, kf) = h
  let (c, env) = ce
  let l = b[iv]
  let x = load l
  let xk = (x, kf)
  let p0 = (xk, env)
  let p = pack p0 at s : exists q. (A * Cap[bor, q]) * Ptr[q] E
  let y = callc c p
  let w = store l y
  if dv = 0 then
    let u = ()
    ret u
  else
    let d1 = dv - 1
    let un = nameI d1
    let i1 = iv + 1
    let jn = nameI i1
    let q3 = (jn, un)
    let q2 = (b, q3)
    let q1 = (k, q2)
    let q0 = (f, q1)
    tail iterRL[A]{r, jn, un}(q0)

def iter_r[A : {copy, insens}]{r, n}(a : Fn(A, A) * Cap[bor, r] * {Loc[r] Array[n] A | ini >= n} * Int[n]) : Unit =
  let (f, r1) = a
  let (k, r2) = r1
  let (b, nv) = r2
  if nv = 0 then
    let u = ()
    ret u
  else
    let m = nv - 1
    let mn = nameI m
    let z = nameI 0
    let q3 = (z, mn)
    let q2 = (b, q3)
    let q1 = (k, q2)
    let q0 = (f, q1)
    let res = iterRL[A]{r, z, mn}(q0)
    ret res
"

/-- The closures' code blocks, the example array, and one driver per function. -/
def demoSrc : String := "
-- x + k, with k captured in the environment.
def addK(a : exists q. (Int * Cap[bor, q]) * Ptr[q] Int) : Int =
  let <q, a1> = unpack a
  let (xk, p) = a1
  let (x, kc) = xk
  let k = load p
  let y = x + k
  ret y

-- acc + x; nothing captured.
def plus(a : exists q. ((Int * Int) * Cap[bor, q]) * Ptr[q] Unit) : Int =
  let <q, a1> = unpack a
  let (axk, p) = a1
  let (ax, kc) = axk
  let (acc, x) = ax
  let y = acc + x
  ret y

-- x + 1, adding x to a running total kept in the environment.
def incCount(a : exists q. (Int * Cap[bor, q]) * Ptr[q] Int) : Int =
  let <q, a1> = unpack a
  let (xk, p) = a1
  let (x, kc) = xk
  let s = load p
  let s1 = s + x
  let w = store p s1
  let y = x + 1
  ret y

-- i * x; nothing captured.
def mulIdx(a : exists q. ((Int * Int) * Cap[bor, q]) * Ptr[q] Unit) : Int =
  let <q, a1> = unpack a
  let (ixk, p) = a1
  let (ix, kc) = ixk
  let (i, x) = ix
  let y = bits wmul i x
  ret y

-- [10, 20, 30, 40]
def mk4(u : Unit) : {Loc own Array[4] Int | ini >= 4} =
  let four = nameI 4
  let b = newBuf[Int] four
  let o0 = xchg b[0] 10
  let o1 = xchg b[1] 20
  let o2 = xchg b[2] 30
  let o3 = xchg b[3] 40
  ret b

def demoMap(k : Int) : Int * Int * Int * Int =
  let u = ()
  let src = mk4(u)
  let e0 = new k
  let <re, env, te> = region e0
  let ke = borrow bor te
  let c = fnptr addK
  let ce = (c, env)
  let h = (ce, ke)
  let g = pack h at re : exists s. (Code(exists q. (Int * Cap[bor, q]) * Ptr[q] Int, Int) * Ptr[s] Int) * Cap[bor, s]
  let f = pack g at [Int] : Fn(Int, Int)
  let four = nameI 4
  let q1 = (src, four)
  let q0 = (f, q1)
  let r = map[Int, Int]{four}(q0)
  let e = endBorrow te
  let (src1, dst) = r
  let y0 = load dst[0]
  let y1 = load dst[1]
  let y2 = load dst[2]
  let y3 = load dst[3]
  let t2 = (y2, y3)
  let t1 = (y1, t2)
  let t0 = (y0, t1)
  ret t0

def demoFold(z : Int) : Int =
  let u = ()
  let src = mk4(u)
  let e0 = new u
  let <re, env, te> = region e0
  let ke = borrow bor te
  let c = fnptr plus
  let ce = (c, env)
  let h = (ce, ke)
  let g = pack h at re : exists s. (Code(exists q. ((Int * Int) * Cap[bor, q]) * Ptr[q] Unit, Int) * Ptr[s] Unit) * Cap[bor, s]
  let f = pack g at [Unit] : Fn(Int * Int, Int)
  let four = nameI 4
  let q2 = (src, four)
  let q1 = (z, q2)
  let q0 = (f, q1)
  let r = fold_left[Int, Int]{four}(q0)
  let e = endBorrow te
  let (sum, src1) = r
  ret sum

def demoIter(z : Int) : Int * Int * Int * Int * Int =
  let u = ()
  let b = mk4(u)
  let e0 = new z
  let <re, env, te> = region e0
  let ke = borrow bor te
  let c = fnptr incCount
  let ce = (c, env)
  let h = (ce, ke)
  let g = pack h at re : exists s. (Code(exists q. (Int * Cap[bor, q]) * Ptr[q] Int, Int) * Ptr[s] Int) * Cap[bor, s]
  let f = pack g at [Int] : Fn(Int, Int)
  let four = nameI 4
  let q1 = (b, four)
  let q0 = (f, q1)
  let b1 = iter[Int]{four}(q0)
  let e = endBorrow te
  let y0 = load b1[0]
  let y1 = load b1[1]
  let y2 = load b1[2]
  let y3 = load b1[3]
  let s = load env
  let t3 = (y3, s)
  let t2 = (y2, t3)
  let t1 = (y1, t2)
  let t0 = (y0, t1)
  ret t0

def demoIterI(u : Unit) : Int * Int * Int * Int =
  let b = mk4(u)
  let e0 = new u
  let e1 = publish e0
  let <re, env, ke> = openPub e1
  let c = fnptr mulIdx
  let ce = (c, env)
  let h = (ce, ke)
  let g = pack h at re : exists s. (Code(exists q. ((Int * Int) * Cap[bor, q]) * Ptr[q] Unit, Int) * Ptr[s] Unit) * Cap[bor, s]
  let f = pack g at [Unit] : Fn(Int * Int, Int)
  let four = nameI 4
  let q1 = (b, four)
  let q0 = (f, q1)
  let b1 = iter_i[Int]{four}(q0)
  let y0 = load b1[0]
  let y1 = load b1[1]
  let y2 = load b1[2]
  let y3 = load b1[3]
  let t2 = (y2, y3)
  let t1 = (y1, t2)
  let t0 = (y0, t1)
  ret t0

def demoFoldR(z : Int) : Int =
  let u = ()
  let b = mk4(u)
  let <r, p, t> = region b
  let e0 = new u
  let <re, env, te> = region e0
  let ke = borrow bor te
  let c = fnptr plus
  let ce = (c, env)
  let h = (ce, ke)
  let g = pack h at re : exists s. (Code(exists q. ((Int * Int) * Cap[bor, q]) * Ptr[q] Unit, Int) * Ptr[s] Unit) * Cap[bor, s]
  let f = pack g at [Unit] : Fn(Int * Int, Int)
  let four = nameI 4
  let k = borrow rd t
  let q3 = (p, four)
  let q2 = (k, q3)
  let q1 = (z, q2)
  let q0 = (f, q1)
  let s1 = fold_left_r[Int, Int]{r, four}(q0)
  let q3b = (p, four)
  let q2b = (k, q3b)
  let q1b = (s1, q2b)
  let q0b = (f, q1b)
  let s2 = fold_left_r[Int, Int]{r, four}(q0b)
  let e = endBorrow t
  let e2 = endBorrow te
  ret s2

def demoIterR(z : Int) : Int * Int * Int * Int * Int =
  let u = ()
  let b = mk4(u)
  let <r, p, t> = region b
  let e0 = new z
  let <re, env, te> = region e0
  let ke = borrow bor te
  let c = fnptr incCount
  let ce = (c, env)
  let h = (ce, ke)
  let g = pack h at re : exists s. (Code(exists q. (Int * Cap[bor, q]) * Ptr[q] Int, Int) * Ptr[s] Int) * Cap[bor, s]
  let f = pack g at [Int] : Fn(Int, Int)
  let four = nameI 4
  let k = borrow bor t
  let q2 = (p, four)
  let q1 = (k, q2)
  let q0 = (f, q1)
  let v = iter_r[Int]{r, four}(q0)
  let e = endBorrow t
  let e2 = endBorrow te
  let l0 = p[0]
  let y0 = load l0
  let l1 = p[1]
  let y1 = load l1
  let l2 = p[2]
  let y2 = load l2
  let l3 = p[3]
  let y3 = load l3
  let s = load env
  let t3 = (y3, s)
  let t2 = (y2, t3)
  let t1 = (y1, t2)
  let t0 = (y0, t1)
  ret t0
-- A histogram of x >> 4 in three published counters, bumped with `fetch add`:
-- any number of threads may run `histo` on their own arrays at once.
def countBin(a : exists q. (Int * Cap[bor, q]) * Ptr[q] (Ptr pub Int * Ptr pub Int * Ptr pub Int)) : Int =
  let <q, a1> = unpack a
  let (xk, p) = a1
  let (x, kc) = xk
  let bins = load p
  let (b0, b12) = bins
  let (b1, b2) = b12
  let k = bits shr x 4
  if k = 0 then
    let o = fetch add b0 1
    ret x
  else
    if k = 1 then
      let o = fetch add b1 1
      ret x
    else
      let o = fetch add b2 1
      ret x
def histo(bins : Ptr pub Int * Ptr pub Int * Ptr pub Int) : Unit =
  let u = ()
  let b = mk4(u)
  let e0 = new bins
  let <re, env, te> = region e0
  let ke = borrow bor te
  let c = fnptr countBin
  let ce = (c, env)
  let h = (ce, ke)
  let g = pack h at re
    : exists s. (Code(exists q. (Int * Cap[bor, q]) * Ptr[q] (Ptr pub Int * Ptr pub Int * Ptr pub Int), Int) * Ptr[s] (Ptr pub Int * Ptr pub Int * Ptr pub Int)) * Cap[bor, s]
  let f = pack g at [Ptr pub Int * Ptr pub Int * Ptr pub Int] : Fn(Int, Int)
  let four = nameI 4
  let q1 = (b, four)
  let q0 = (f, q1)
  let b1 = iter[Int]{four}(q0)
  let e = endBorrow te
  ret u
def mkBins(z : Int) : Ptr pub Int * Ptr pub Int * Ptr pub Int =
  let c0 = new z
  let p0 = publish c0
  let c1 = new z
  let p1 = publish c1
  let c2 = new z
  let p2 = publish c2
  let t = (p1, p2)
  let bins = (p0, t)
  ret bins
def bump(bins : Ptr pub Int * Ptr pub Int * Ptr pub Int) : Int =
  let (b0, b12) = bins
  let (b1, b2) = b12
  let o = fetch add b1 1
  ret o
"

def parses (s : String) : Bool :=
  match parseProg s with | .ok _ => true | .error _ => false

def parsed (s : String) : Prog :=
  match parseProg s with | .ok p => p | .error _ => []

#guard parses libSrc
#guard parses demoSrc

/-- The library: `mapL map foldL fold_left iterL iter iterIL iter_i`, and the
borrowing `foldRL fold_left_r iterRL iter_r`. -/
def lib : Prog := parsed libSrc
/-- The example closures and drivers. -/
def demos : Prog := parsed demoSrc
/-- Both, for running the drivers. -/
def prog : Prog := lib ++ demos

#guard lib.map (·.name) == ["mapL", "map", "foldL", "fold_left", "iterL", "iter", "iterIL", "iter_i",
                            "foldRL", "fold_left_r", "iterRL", "iter_r"]
#guard accepts (checkProg lib)
#guard accepts (checkProg prog)

/-- A block of `prog` by name. -/
def blk (n : String) : Decl :=
  match prog.find? (·.name == n) with
  | some d => d
  | none => { name := "?", idx := [], arg := "a", argTy := .unit, retTy := .unit, body := .ret (.var "a") }

def mapLD := blk "mapL"
def mapD := blk "map"
def foldLD := blk "foldL"
def foldLeftD := blk "fold_left"
def iterLD := blk "iterL"
def iterD := blk "iter"
def iterILD := blk "iterIL"
def iterID := blk "iter_i"
def addKD := blk "addK"
def plusD := blk "plus"
def incCountD := blk "incCount"
def mulIdxD := blk "mulIdx"
def mk4D := blk "mk4"
def demoMapD := blk "demoMap"
def demoFoldD := blk "demoFold"
def demoIterD := blk "demoIter"
def demoIterID := blk "demoIterI"
def foldRLD := blk "foldRL"
def foldLeftRD := blk "fold_left_r"
def iterRLD := blk "iterRL"
def iterRD := blk "iter_r"
def demoFoldRD := blk "demoFoldR"
def demoIterRD := blk "demoIterR"
def countBinD := blk "countBin"
def histoD := blk "histo"
def mkBinsD := blk "mkBins"
def bumpD := blk "bump"

#guard [mapLD, mapD, foldLD, foldLeftD, iterLD, iterD, iterILD, iterID, addKD, plusD, incCountD,
        mulIdxD, mk4D, demoMapD, demoFoldD, demoIterD, demoIterID, foldRLD, foldLeftRD, iterRLD,
        iterRD, demoFoldRD, demoIterRD, countBinD, histoD, mkBinsD, bumpD].all (·.name != "?")

/-! ## Refusals: the static bounds and the closure kind do their work -/

def refusal (s : String) : String :=
  match parseProg s with
  | .ok p => match checkProg p with | .ok _ => "" | .error e => e
  | .error _ => "parse"

def mentions (e why : String) : Bool := (e.splitOn why).length > 1

-- Filling dst out of order: `bufInit` wants the next uninitialised slot.
#guard mentions (refusal ((libSrc.replace "let dst1 = bufInit dst iv y" "let dst1 = bufInit dst i9 y").replace
    "let y = callc c p\n  let dst1" "let y = callc c p\n  let i9 = iv + 1\n  let dst1"))
  "bufInit: the slot is not the next uninitialised one"
-- Reading one past the current slot: not provably below the capacity when d = 0.
#guard mentions (refusal (libSrc.replace "let x = load b[iv]\n  let xk = (x, kf)"
    "let i9 = iv + 1\n  let x = load b[i9]\n  let xk = (x, kf)"))
  "loadAt: the index is not provably below the capacity"
-- The library cannot look into an environment: its type is the unpacked `E`,
-- of which nothing is known.  A plain load under the capability is refused
-- (`E` may be view-sensitive), and an acquiring one too (`E` may be affine).
#guard mentions (refusal (libSrc.replace "let x = load b[iv]\n  let xk = (x, kf)"
    "let e9 = load env\n  let x = load b[iv]\n  let xk = (x, kf)"))
  "load under a capability: a view-sensitive type needs acq"
#guard mentions (refusal (libSrc.replace "let x = load b[iv]\n  let xk = (x, kf)"
    "let e9 = load acq env\n  let x = load b[iv]\n  let xk = (x, kf)"))
  "load would duplicate an affine value"
-- Nor pass the opened `E` on as a type argument (so the loop passes the package).
def touchSrc : String := "
def touch[E : *]{r}(p : Ptr[r] E) : Unit =
  let u = ()
  ret u
"
#guard mentions (refusal (touchSrc ++ libSrc.replace "let x = load b[iv]\n  let xk = (x, kf)"
    "let t9 = touch[E]{s}(env)\n  let x = load b[iv]\n  let xk = (x, kf)"))
  "touch: a type argument exposes an unpacked type"

/-! ## Refusals: a borrowing closure is second-class -/

-- A `Fn` carries a `bor` capability, so it may be passed but not stored ...
#guard mentions (refusal (libSrc ++ demoSrc.replace
    "  let f = pack g at [Int] : Fn(Int, Int)\n  let four = nameI 4\n  let q1 = (b, four)"
    "  let f = pack g at [Int] : Fn(Int, Int)\n  let c9 = new f\n  let four = nameI 4\n  let q1 = (b, four)"))
  "new: a second-class capability cannot be stored"
-- ... nor returned (it would outlive the borrow of its environment) ...
def mkCloSrc : String := "
def mkClo(e0 : Ptr own Int) : Fn(Int, Int) =
  let <re, env, te> = region e0
  let ke = borrow bor te
  let c = fnptr addK
  let ce = (c, env)
  let h = (ce, ke)
  let g = pack h at re : exists s. (Code(exists q. (Int * Cap[bor, q]) * Ptr[q] Int, Int) * Ptr[s] Int) * Cap[bor, s]
  let f = pack g at [Int] : Fn(Int, Int)
  ret f
"
#guard mentions (refusal (libSrc ++ demoSrc ++ mkCloSrc))
  "mkClo: a second-class capability may be passed, not returned or stored"
-- ... and `endBorrow` on the environment's token takes it away.
#guard mentions (refusal (libSrc ++ demoSrc.replace
    "  let b1 = iter[Int]{four}(q0)\n  let e = endBorrow te\n"
    "  let e = endBorrow te\n  let b1 = iter[Int]{four}(q0)\n"))
  "unbound variable q0"
-- A closure over a published environment, at `Cap pub` throughout, is
-- first-class: it may be stored.
def pubCloSrc : String := "
def addKP(a : exists q. (Int * Cap[pub, q]) * Ptr[q] Int) : Int =
  let <q, a1> = unpack a
  let (xk, p) = a1
  let (x, kc) = xk
  let k = load p
  let y = x + k
  ret y

def pubClo(z : Int) : Int =
  let e0 = new z
  let e1 = publish e0
  let <re, env, ke> = openPub e1
  let c = fnptr addKP
  let ce = (c, env)
  let h = (ce, ke)
  let g = pack h at re : exists s. (Code(exists q. (Int * Cap[pub, q]) * Ptr[q] Int, Int) * Ptr[s] Int) * Cap[pub, s]
  let f = pack g at [Int] : exists (E : *). exists s. (Code(exists q. (Int * Cap[pub, q]) * Ptr[q] E, Int) * Ptr[s] E) * Cap[pub, s]
  let cell = new f
  ret z
"
#guard refusal (libSrc ++ demoSrc ++ pubCloSrc) == ""

/-! ## Refusals: the region token and capabilities do their work -/

-- `iter_r` writes, so a read capability is not enough.
#guard mentions (refusal ((libSrc.replace "Fn(A, A) * Cap[bor, r]" "Fn(A, A) * Cap[rd, r]") ++ demoSrc))
  "store into a region without its token"
-- While a read borrow is out, the owner has given up its token: no stores.
#guard mentions (refusal (libSrc ++ demoSrc.replace "  let k = borrow rd t\n"
    "  let k = borrow rd t\n  let l9 = p[0]\n  let w9 = store l9 5\n"))
  "store into a region without its token"
-- `endBorrow` takes the capability back: whatever holds it goes out of scope.
#guard mentions (refusal (libSrc ++ demoSrc.replace
    "  let s2 = fold_left_r[Int, Int]{r, four}(q0b)\n  let e = endBorrow t\n"
    "  let e = endBorrow t\n  let s2 = fold_left_r[Int, Int]{r, four}(q0b)\n"))
  "unbound variable q0b"
-- `region` consumes the buffer: `b` itself is gone, only `p` remains.
#guard mentions (refusal (libSrc ++ demoSrc.replace
    "  let <r, p, t> = region b\n  let e0 = new u\n"
    "  let <r, p, t> = region b\n  let x9 = load b[0]\n  let e0 = new u\n"))
  "b was already used (affine)"
-- The region's initialised prefix is fixed: no `bufInit` through `p`.
#guard mentions (refusal (libSrc ++ demoSrc.replace
    "  let <r, p, t> = region b\n  let e0 = new u\n"
    "  let <r, p, t> = region b\n  let p2 = bufInit p 0 5\n  let e0 = new u\n"))
  "bufInit needs an own buffer"
-- Only an own reference or an own buffer opens as a region, not a published one.
#guard mentions (refusal (libSrc ++ demoSrc.replace
    "  let <r, p, t> = region b\n  let e0 = new u\n"
    "  let q9 = new u\n  let pq = publish q9\n  let <r9, p9, t9> = region pq\n  let <r, p, t> = region b\n  let e0 = new u\n"))
  "region needs an own reference or an own buffer"

/-! ## The examples, on the machine -/

def runD (f : String) (argTy : Ty) (args : List Nat) : Option (List Val) :=
  (runSetup prog f [] argTy (args.map fun n => cst (.num n)) 600).map fun s => s.res.map (·.val)

def nums (ns : List Nat) : Option (List Val) := some (ns.map .num)

-- map (· + k) [10,20,30,40] with k = 1 captured.
#guard runD "demoMap" .int [1] == nums [11, 21, 31, 41]
-- fold_left (+) 0 [10,20,30,40].
#guard runD "demoFold" .int [0] == nums [100]
-- iter: every element + 1, and the closure's running total (from 0) is 100.
#guard runD "demoIter" .int [0] == nums [11, 21, 31, 41, 100]
-- iter_i: b[j] := j * b[j].
#guard runD "demoIterI" .unit [] == nums [0, 20, 60, 120]
-- fold_left_r (+) twice over the same borrowed array: 0 + 100, then + 100.
#guard runD "demoFoldR" .int [0] == nums [200]
-- iter_r: as demoIter, but the array stays with the caller.
#guard runD "demoIterR" .int [0] == nums [11, 21, 31, 41, 100]

end ArrayLib
