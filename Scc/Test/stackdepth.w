-- Unbounded recursion mixing tail and non-tail calls: `up` calls `hop`
-- (counted by the stack depth counter, `Tcb.depth`) and `hop` tail calls `up`
-- (not counted).  The counter reaches the program's limit before the stack
-- reaches its cap, and the call past the limit takes the abort outcome
-- (status 101, the stack message on standard error).
def up(n : U64) : Int =
  let one = cvt U64 1
  let m = fop add n one
  let r = hop(m)
  let iv = toInt n
  let s = r + iv
  ret s

def hop(n : U64) : Int =
  tail up(n)

def main(u : Unit) : Int =
  let z = cvt U64 0
  let r = up(z)
  ret r
