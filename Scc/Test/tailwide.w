-- Tail calls that pass more stack words than the calling block's own
-- argument: `wl` (four words, all in registers) tail-calls `ww` (nine words:
-- x64 passes three on the stack, AArch64 one), which tail-calls `wv` (twelve
-- words), which tail-calls `wl` again.  A tail call is a jump, so the loop
-- runs 1000000 rounds in constant stack: with a frame kept per round it
-- would need hundreds of MiB, past the 64 MiB per-thread stack cap.
-- Each round adds the cell's 7 to the accumulator, which starts at 7.
-- Exit status: (7 + 1000000 * 7) mod 256 = 199.
def wl(a : (Loc pub Int * U64) * Int) : Int =
  let (x, acc) = a
  let (l, n) = x
  let nil = cvt U64 0
  let c = fcmp eq n nil
  if c = 1 then
    ret acc
  else
    let v = load l
    let acc1 = acc + v
    let one = cvt U64 1
    let n1 = fop sub n one
    let x1 = (l, n1)
    let y1 = (l, n1)
    let xy1 = (x1, y1)
    let z1 = (l, acc1)
    let q = (xy1, z1)
    tail ww(q)

def ww(a : ((Loc pub Int * U64) * (Loc pub Int * U64)) * (Loc pub Int * Int)) : Int =
  let (xy, z) = a
  let (x, y) = xy
  let (l0, n) = x
  let (l1, k) = y
  let (l2, acc) = z
  let x1 = (l0, n)
  let y1 = (l1, k)
  let xy1 = (x1, y1)
  let z1 = (l2, acc)
  let w1 = (l2, acc)
  let zw = (z1, w1)
  let q = (xy1, zw)
  tail wv(q)

def wv(a : ((Loc pub Int * U64) * (Loc pub Int * U64)) * ((Loc pub Int * Int) * (Loc pub Int * Int))) : Int =
  let (xy, zw) = a
  let (x, y) = xy
  let (z, w) = zw
  let (l0, n) = x
  let (l3, acc) = w
  let x1 = (l0, n)
  let q = (x1, acc)
  tail wl(q)

def main(u : Unit) : Int =
  let z = zero[Int]
  let c0 = new[Int] z
  let s0 = store c0 7
  let p = publish c0
  let v7 = load p
  let v9 = v7 + 2
  let q = (v7, v9)
  let c1 = new[Int * Int] q
  let c = publish c1
  let la = fld 0 c
  let n = cvt U64 1000000
  let x = (la, n)
  let a = (x, v7)
  let r = wl(a)
  ret r
