/-
**The layout facts the spawned child's segment reads** (x86-64; the twin of `Spike/Lib/A64HelloXHFSeg.lean`'s live
part): the layout's immediate table has no immediate at the child's control `kidC` nor at `print`'s call
`workerCallH`, the premises of `XHNode.zObl_XH` (`hik`, `hiw`).

- `ImmsKid`: the two facts.

## Differences from the AArch64 version

- `ImmsKid.ofIH` and `seg_childXHF` (unused in the AArch64 build) are not twinned; so the module imports only
  `X64HelloXH` and `X64HelloSplit` (AArch64: `XHNode`, `XHLand`, `FlagR`, `PlacedZObl`).
-/
import Spike.Lib.X64HelloXH
import Spike.Lib.X64HelloSplit

namespace Spike.Lib.X64.HelloPh.XHFSeg

open CoreLang CoreTerm

/-- **The layout's immediate table has no immediate at the child's controls**: none at `kidC` (`hkid`) nor at
`workerCallH` (`hwc`). These are the only facts of the table the child's segment reads (`XHNode.zObl_XH`'s `hik`,
`hiw`). Its producer at the root's layout is `X64HelloImmsKid`'s pair `⟨kid_root hp, wcall_root hp⟩`
(`Spike.Lib.X64.HelloImms`). -/
structure ImmsKid (Λ : Scc.Sem.Layout) : Prop where
  /-- No immediate at the child's control `kidC`. -/
  hkid : ∀ (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (y : String) (k : Nat),
    Λ.imms (XH.kidC T w0 w1 w2 w3 w4).term y k = none
  /-- No immediate at `workerCallH`. -/
  hwc : ∀ (y : String) (k : Nat), Λ.imms Spike.Lib.X64HelloSplit.workerCallH y k = none

end Spike.Lib.X64.HelloPh.XHFSeg
