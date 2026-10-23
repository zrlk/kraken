-- The object layout: a product cell mixing a scalar and a reference, field
-- locatives into published cells (two words, passed to a block), buffers of
-- reference and locative elements filled with bufInit, loads through each.
-- Returns 12 + 7 + 13 + 7 + 7 = 46.
def g(a : Loc pub Int * Int) : Int =
  let (l, x) = a
  let v = load l
  let s = store l x
  let w = v + 1
  ret w

def main(u : Unit) : Int =
  let z = zero[Int]
  let c0 = new z
  let s0 = store c0 7
  let p = publish c0
  let v7 = load p
  let x5 = v7 + 5
  let q = (x5, p)
  let c1 = new q
  let c = publish c1
  let l1 = fld 1 c
  let pp = load l1
  let v1 = load pp
  let l0 = fld 0 c
  let v0 = load l0
  let r = (v1, v0)
  let c2 = new r
  let c2p = publish c2
  let m1 = fld 1 c2p
  let a = (m1, v7)
  let w = g(a)
  let k = 3
  let m = nameI k
  let b = newBuf[Ptr pub Int] m
  let b1 = bufInit b 0 p
  let b2 = bufInit b1 1 pp
  let b3 = bufInit b2 2 p
  let e = load b3[1]
  let ev = load e
  let lb = newBuf[Loc pub Int] m
  let lb1 = bufInit lb 0 m1
  let lb2 = bufInit lb1 1 m1
  let lb3 = bufInit lb2 2 m1
  let ll = load lb3[2]
  let lv = load ll
  let t1 = v0 + v1
  let t2 = t1 + w
  let t3 = t2 + ev
  let t4 = t3 + lv
  ret t4
