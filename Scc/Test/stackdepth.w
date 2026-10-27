-- Unbounded recursion mixing tail and non-tail calls: `up` calls `hop`
-- (a frame that stays live) and `hop` tail calls `up` (its frame replaced).
-- The stack doubles towards the per-thread cap, and the frame that no longer
-- fits takes the abort outcome in the grow routine (status 101, the stack
-- message on standard error).
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
