-- Rejected by WeakCore's checker: a device extern called from a plain block.
def main(u : Unit) : Int =
  let x = cvt U64 0
  let o = devOut[64] x
  ret 0
