-- Rejected: a buffer of a literal length whose region would take 4 GiB
-- (2^29 one-word elements), beyond the 32-bit byte offsets of a locative.
def main(u : Unit) : Int =
  let b = newBuf[Int] 536870912
  ret 0
