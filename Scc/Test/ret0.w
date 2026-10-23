-- main returns 40 + 2 = 42: one thread, no allocation, no output; the first
-- certification target.

def main(u : Unit) : Int =
  let x = 40
  let y = x + 2
  ret y
