-- A call of a code block with an `if` and a `-` (the fragment
-- `Scc.Lower.Accepted1`): `main` calls `pick(0)`, which takes the `then` arm
-- and returns 50 - 8 = 42.
def pick(n : Int) : Int =
  if n = 0 then
    let a = 50
    let b = 8
    let d = a - b
    ret d
  else
    ret n

def main(u : Unit) : Int =
  let z = 0
  let r = pick(z)
  ret r
