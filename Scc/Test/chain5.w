-- A chain of code blocks (`f0` to `f7`; five in its first version), each
-- with an `if`, a `-` and a call: a listing over the certificates'
-- threshold for checking the block table one function at a time
-- (`Scc.Cert.Gen.blocksSplitMin`).

def f0(n : Int) : Int =
  if n = 0 then
    let a0 = 49
    let b0 = 7
    let d0 = a0 - b0
    ret d0
  else
    ret n

def f1(n : Int) : Int =
  if n = 0 then
    let a1 = 51
    let b1 = 1
    let d1 = a1 - b1
    let r1 = f0(d1)
    ret r1
  else
    let s1 = f0(n)
    ret s1

def f2(n : Int) : Int =
  if n = 0 then
    let a2 = 52
    let b2 = 2
    let d2 = a2 - b2
    let r2 = f1(d2)
    ret r2
  else
    let s2 = f1(n)
    ret s2

def f3(n : Int) : Int =
  if n = 0 then
    let a3 = 53
    let b3 = 3
    let d3 = a3 - b3
    let r3 = f2(d3)
    ret r3
  else
    let s3 = f2(n)
    ret s3

def f4(n : Int) : Int =
  if n = 0 then
    let a4 = 54
    let b4 = 4
    let d4 = a4 - b4
    let r4 = f3(d4)
    ret r4
  else
    let s4 = f3(n)
    ret s4

def f5(n : Int) : Int =
  if n = 0 then
    let a5 = 55
    let b5 = 5
    let d5 = a5 - b5
    let r5 = f4(d5)
    ret r5
  else
    let s5 = f4(n)
    ret s5

def f6(n : Int) : Int =
  if n = 0 then
    let a6 = 56
    let b6 = 6
    let d6 = a6 - b6
    let r6 = f5(d6)
    ret r6
  else
    let s6 = f5(n)
    ret s6

def f7(n : Int) : Int =
  if n = 0 then
    let a7 = 57
    let b7 = 7
    let d7 = a7 - b7
    let r7 = f6(d7)
    ret r7
  else
    let s7 = f6(n)
    ret s7

def main(u : Unit) : Int =
  let z = 0
  let r = f7(z)
  ret r
