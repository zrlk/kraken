-- Sixteen threads grow their stacks at the same time: each worker runs a
-- non-tail recursion 10000 deep (1 + 2 + ... + 10000 = 50005000), stores the
-- sum in its own cell with a release store and unparks main.  spawnAll
-- spawns the workers recursively and, on the way back, waits for each cell
-- (acquire load, parking in between) and adds the sums.
-- Exit status: 16 * 50005000 mod 256 = 128.
def park(u : Unit) : Unit =
  ret ()

def unpark(t : Ptr pub Void) : Unit =
  ret ()

def sum(n : U64) : Int =
  let z = cvt U64 0
  let c = fcmp eq n z
  if c = 1 then
    ret 0
  else
    let one = cvt U64 1
    let m = fop sub n one
    let r = sum(m)
    let iv = toInt n
    let s = r + iv
    ret s

def worker(a : Ptr pub Int * Ptr pub Void) : Unit =
  let (d, me) = a
  let n = cvt U64 10000
  let r = sum(n)
  let s = store rel d r
  let w = unpark(me)
  ret ()

def wait(d : Ptr pub Int) : Int =
  let x = load acq d
  if x = 0 then
    let p = park(())
    tail wait(d)
  else
    ret x

def spawnAll(a : U64 * Ptr pub Void) : Int =
  let (k, me) = a
  let z = cvt U64 0
  let c = fcmp eq k z
  if c = 1 then
    ret 0
  else
    let zi = zero[Int]
    let d0 = new zi
    let d = publish d0
    let arg = (d, me)
    let t = spawn{worker}(arg)
    let one = cvt U64 1
    let k1 = fop sub k one
    let b = (k1, me)
    let r = spawnAll(b)
    let v = wait(d)
    let s = r + v
    ret s

def main(me : Ptr pub Void) : Int =
  let n = cvt U64 16
  let a = (n, me)
  let r = spawnAll(a)
  ret r
