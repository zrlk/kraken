-- Non-tail recursion 100000 deep: the initial 16 KiB stack must grow by
-- doubling several times (the frames of every level stay live).  sum(n) is
-- 1 + 2 + ... + n with a checked Int `+` after each return.
-- Exit status: 5000050000 mod 256 = 80.
def sum(n : U64) : Int =
  let z = cvt U64 0
  let c = fcmp eq n z
  if c = 1 then
    ret 0
  else
    let one = cvt U64 1
    let m = fop sub n one
    let r = sum(m)
    let iv = toInt n
    let s = r + iv
    ret s

def main(u : Unit) : Int =
  let n = cvt U64 100000
  let r = sum(n)
  ret r
