import Spike.Test.HelloLinkedX64

/-! # `hello.w` on x86-64: placement component A12 (code part) of hello's output

One `decide +kernel` per module (`Spike/Test/HelloLinkedX64.lean`'s `Λ1`). Unlike AArch64, whose `PlaceW`
subset is A1, A2, A4, A6, A8, x86-64's `PlaceWX` takes every component of `placeOK2At`. -/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib.X64.HelloPh.RootLit (oH pcfgH)

/-- **A12's code part of hello's output** (layout-free) (kernel-checked). -/
theorem hello1_a12c : Scc.Cert.Spawn.X64.a12code' oH = true := by decide +kernel

end Spike.Test.HelloLinkedX64
