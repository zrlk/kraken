-- A tail-recursive loop of 100000 iterations (the stack is 16 KiB, so tail
-- calls must not grow it), summing 1..100000 with a checked Int `+`.
-- Exit status: 5000050000 mod 256 = 80.
def loop(a : U64 * Int) : Int =
  let (i, acc) = a
  let z = cvt U64 0
  let c = fcmp eq i z
  if c = 1 then
    ret acc
  else
    let iv = toInt i
    let acc1 = acc + iv
    let one = cvt U64 1
    let i1 = fop sub i one
    let p = (i1, acc1)
    tail loop(p)

def main(u : Unit) : Int =
  let n = cvt U64 100000
  let p = (n, 0)
  let r = loop(p)
  ret r
