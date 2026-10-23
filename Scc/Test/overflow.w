-- An Int addition past 2^64 - 1 takes the abort outcome: a message on
-- standard error and exit status 101.
def main(u : Unit) : Int =
  let big = 18446744073709551615
  let s = big + 1
  ret s
