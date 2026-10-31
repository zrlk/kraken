-- Message passing between two threads: the worker writes the payload with a
-- plain store, then sets the flag with a release store and unparks main;
-- main waits for the flag with an acquire load (parking in between) and then
-- reads the payload.  Exit status: the payload, 42.
def worker(a : (Ptr pub Int * Ptr pub Int) * ThreadId) : Unit =
  let (cells, me) = a
  let (d, f) = cells
  let s1 = store d 42
  let s2 = store rel f 1
  let w = unpark me
  ret ()

def wait(a : Ptr pub Int * Ptr pub Int) : Int =
  let (d, f) = a
  let x = load acq f
  if x = 1 then
    let v = load d
    ret v
  else
    let p = park ()
    tail wait(a)

def main(me : ThreadId) : Int =
  let z = zero[Int]
  let d0 = new[Int] z
  let d = publish d0
  let f0 = new[Int] z
  let f = publish f0
  let cells = (d, f)
  let arg = (cells, me)
  let t = spawn{worker}(arg)
  tail wait(cells)
