-- Wake: `hello.w` without the output.  `main` spawns `worker` on the flag
-- cell `c` and its own `ThreadId`, then sleeps (`waitLoop`: an acquire load
-- of the flag, parking while it is 0); `worker` wakes `main` (a release store
-- of the flag and `unpark`) and exits; `main` sees the flag and returns 0.
--
-- Provisional forms (see Scc/Frontend.lean): `spawn{f}(a)` is the spawn.
-- `park`, `unpark` and `ThreadId` are WeakCore's own.

def worker(a : Ptr pub Int * ThreadId) : Unit =
  let (c, j) = a
  let d = store rel c 1
  let w = unpark j
  ret ()

def waitLoop(c : Ptr pub Int) : Int =
  let d = load acq c
  if d = 1 then
    ret 0
  else
    let p = park ()
    tail waitLoop(c)

def main(me : ThreadId) : Int =
  let z = zero[Int]
  let o = new[Int] z
  let c = publish o
  let p = (c, me)
  let t = spawn{worker}(p)
  tail waitLoop(c)
