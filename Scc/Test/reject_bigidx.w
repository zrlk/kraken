-- Rejected: an index literal in a type that does not fit in 64 bits.
def first(a : Int[18446744073709551616]) : Int =
  ret a

def main(u : Unit) : Int =
  ret 0
