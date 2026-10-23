-- More spawns than the thread cap (Layout.maxThreads, 1023 by default): each
-- worker returns at once, but the count of spawned threads is never
-- decremented, so spawn 1024 takes the abort outcome (status 101, the threads
-- message on standard error) before it takes a stack or calls clone.
def worker(u : Unit) : Unit =
  ret ()

def spawnMany(k : U64) : Int =
  let z = cvt U64 0
  let c = fcmp eq k z
  if c = 1 then
    ret 0
  else
    let t = spawn{worker}(())
    let one = cvt U64 1
    let k1 = fop sub k one
    tail spawnMany(k1)

def main(u : Unit) : Int =
  let n = cvt U64 2000
  let r = spawnMany(n)
  ret r
