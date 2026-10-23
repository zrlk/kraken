-- Copy of Scc/Test/hello1.w: below this line it must stay identical (regen_a64.sh checks).
-- Hello, world on one thread: the setup block `rodata` builds the bytes on
-- the heap (static data by the heap-bytes route); `main` prints them with the
-- output extern and returns 0.  No spawn, no park/unpark, and no `publish`
-- (the program is publish-free, `Scc.Sem.PubFree.ProgPubFree`): the slice
-- stays owned and `print` takes it by its owned signature (`printOwnSig`),
-- consuming it.  `print`'s body is a WeakCore model that is not compiled;
-- `ThreadId` is stubbed as `Ptr pub Void`.

def print{m}(a : ({Loc own Array[m] LanesU8 | ini >= m} * Int[m]) * Int) : Unit =
  ret ()

def rodata(u : Unit) : exists q. ({Loc own Array[q] LanesU8 | ini >= q} * Int[q]) * Int =
  let two = 2
  let m = nameI two
  let b = newBuf[LanesU8] m
  let w0 = asLanes U8 8583909746840200520
  let o0 = xchg b[0] w0
  let w1 = asLanes U8 44634501743
  let o1 = xchg b[1] w1
  let n = 13
  let sm = (b, m)
  let sl0 = (sm, n)
  let sl = pack sl0 at m : exists a. ({Loc own Array[a] LanesU8 | ini >= a} * Int[a]) * Int
  ret sl

def main(a : (exists q. ({Loc own Array[q] LanesU8 | ini >= q} * Int[q]) * Int) * Ptr pub Void) : Int =
  let (sl0, me) = a
  let <q, sl> = unpack sl0
  let u = print{q}(sl)
  ret 0
