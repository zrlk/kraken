-- Unbounded non-tail recursion: the stack doubles towards the per-thread
-- cap, and the stack depth counter (`Tcb.depth`) takes the abort outcome at
-- the program's limit, before a frame no longer fits in the cap (status 101,
-- the stack message on standard error).
def down(n : U64) : Int =
  let one = cvt U64 1
  let m = fop add n one
  let r = down(m)
  ret r

def main(u : Unit) : Int =
  let z = cvt U64 0
  let r = down(z)
  ret r
