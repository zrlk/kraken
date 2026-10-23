-- Copy of Scc/Test/ret0.w: below this line it must stay identical (regen_a64.sh checks).
-- main returns 40 + 2 = 42: one thread, no allocation, no output; the first
-- certification target.

def main(u : Unit) : Int =
  let x = 40
  let y = x + 2
  ret y
