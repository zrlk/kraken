-- Rejected by the provisional regionHomog check: a locative (base and offset
-- words in different regions) inline in a shared cell could tear.
def main(u : Unit) : Int =
  let z = zero[Int]
  let c = new z
  let p = publish c
  let q = (p, 1)
  let d = new q
  let dp = publish d
  let l = fld 0 dp
  let e = new l
  let ep = publish e
  ret 0
