-- Rejected: `parity` is not in the accepted fragment.
def half{i}(a : Int[i]) : Int =
  parity a of
    2k => ret 0
    2k+1 => ret 1

def main(u : Unit) : Int =
  ret 0
