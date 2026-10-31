-- Rejected by the provisional regionHomog check: a locative (base and offset
-- words in different regions) inline in a shared cell could tear.
def main(u : Unit) : Int =
  let z = zero[Int]
  let c = new[Int] z
  let p = publish c
  let q = (p, 1)
  let d = new[Ptr pub Int * Int[1]] q
  let dp = publish d
  let l = fld 0 dp
  let e = new[Loc pub Ptr pub Int] l
  let ep = publish e
  ret 0
