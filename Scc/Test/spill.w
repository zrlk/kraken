-- Argument words past the register limit (x64: six, AArch64: eight): every
-- block below takes nine words, three locatives (two words each) and three
-- scalars, so three or one of them travel in the caller's outgoing area.
-- `rec` recurses 20000 deep without a tail call, so the 16 KiB initial stack
-- grows while stack parameters (locative bases among them) are live at the
-- prologue check; `loop` tail-calls itself 100000 times with nine words,
-- overwriting its own incoming area.  `mix` checks the order of the words.
-- rec: 7 + 9 + 7 + 7 + 20000 * 9 = 180030; loop: 7 + 100000 * 7 = 700007;
-- mix: 7 + 2 * 9 + 4 * 7 + 8 * 5 + 16 * 7 = 205.
-- Exit status: (180030 + 700007 + 205) mod 256 = 114.
def rec(a : ((Loc pub Int * U64) * (Loc pub Int * U64)) * (Loc pub Int * Int)) : Int =
  let (xy, z) = a
  let (x, y) = xy
  let (l0, n) = x
  let (l1, k) = y
  let (l2, acc) = z
  let nil = cvt U64 0
  let c = fcmp eq n nil
  if c = 1 then
    let v0 = load l0
    let v1 = load l1
    let v2 = load l2
    let s1 = v0 + v1
    let s2 = s1 + v2
    let s3 = s2 + acc
    ret s3
  else
    let one = cvt U64 1
    let n1 = fop sub n one
    let x1 = (l0, n1)
    let y1 = (l1, k)
    let xy1 = (x1, y1)
    let z1 = (l2, acc)
    let a1 = (xy1, z1)
    let r = rec(a1)
    let v = load l1
    let s = r + v
    ret s

def loop(a : ((Loc pub Int * U64) * (Loc pub Int * U64)) * (Loc pub Int * Int)) : Int =
  let (xy, z) = a
  let (x, y) = xy
  let (l0, n) = x
  let (l1, k) = y
  let (l2, acc) = z
  let nil = cvt U64 0
  let c = fcmp eq n nil
  if c = 1 then
    ret acc
  else
    let v = load l2
    let acc1 = acc + v
    let one = cvt U64 1
    let n1 = fop sub n one
    let x1 = (l0, n1)
    let y1 = (l1, k)
    let xy1 = (x1, y1)
    let z1 = (l2, acc1)
    let a1 = (xy1, z1)
    tail loop(a1)

def mix(a : ((Loc pub Int * U64) * (Loc pub Int * U64)) * (Loc pub Int * Int)) : Int =
  let (xy, z) = a
  let (x, y) = xy
  let (l0, n) = x
  let (l1, k) = y
  let (l2, acc) = z
  let v0 = load l0
  let v1 = load l1
  let v2 = load l2
  let kv = toInt k
  let b1 = v1 + v1
  let c2 = v2 + v2
  let c4 = c2 + c2
  let k2 = kv + kv
  let k4 = k2 + k2
  let k8 = k4 + k4
  let a2 = acc + acc
  let a4 = a2 + a2
  let a8 = a4 + a4
  let a16 = a8 + a8
  let s1 = v0 + b1
  let s2 = s1 + c4
  let s3 = s2 + k8
  let s4 = s3 + a16
  ret s4

def main(u : Unit) : Int =
  let z = zero[Int]
  let c0 = new[Int] z
  let s0 = store c0 7
  let p = publish c0
  let v7 = load p
  let v9 = v7 + 2
  let q = (v7, v9)
  let c1 = new[Int * Int] q
  let c = publish c1
  let la = fld 0 c
  let lb = fld 1 c
  let n = cvt U64 20000
  let k = cvt U64 5
  let x = (la, n)
  let y = (lb, k)
  let xy = (x, y)
  let zz = (la, v7)
  let a = (xy, zz)
  let r1 = rec(a)
  let m = cvt U64 100000
  let x2 = (la, m)
  let xy2 = (x2, y)
  let a2 = (xy2, zz)
  let r2 = loop(a2)
  let r3 = mix(a)
  let t1 = r1 + r2
  let t2 = t1 + r3
  ret t2
