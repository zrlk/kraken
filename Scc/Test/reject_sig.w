-- Rejected: a sum type in a block's signature.
def pick(a : Int + Unit) : Int =
  ret 0

def main(u : Unit) : Int =
  ret 0
