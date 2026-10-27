-- A main-only call-free `Accepted1` program: an `if` on a computed `Int`
-- and a saturating `-`: exits 42.
def main(u : Unit) : Int =
  let a = 50
  let b = 8
  let d = a - b
  let z = 0
  let c = z + z
  if c = z then
    ret d
  else
    ret b
