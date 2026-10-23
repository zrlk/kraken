-- Rejected: a fetch-op is not in the accepted fragment.
def main(u : Unit) : Int =
  let z = zero[Int]
  let o = new z
  let c = publish o
  let old = fetch add c 1
  ret 0
