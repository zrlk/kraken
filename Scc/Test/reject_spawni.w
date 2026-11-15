-- Rejected: an index-parameter spawn (`spawnI`) has no lowering yet.
def worker(a : (Ptr pub Int * Ptr pub Int) * ThreadId) : Unit =
  let (cells, me) = a
  let (d, f) = cells
  let s1 = store d 42
  let s2 = store rel f 1
  let w = unpark me
  ret ()

def main(me : ThreadId) : Int =
  let z = zero[Int]
  let d0 = new[Int] z
  let d = publish d0
  let f0 = new[Int] z
  let f = publish f0
  let cells = (d, f)
  let arg = (cells, me)
  let t = spawnI worker(arg) : (Ptr pub Int * Ptr pub Int) * ThreadId
  ret 0
