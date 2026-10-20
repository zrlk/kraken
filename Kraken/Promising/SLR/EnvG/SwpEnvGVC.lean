/-
**Part 2: the SWP spinlock's release VC on
`EnvGC`**, for `swpWorker` (`EnvG/SwpEnvGSmoke.lean`).

Everything up to the release is the `swpl` lock's (`EnvG/SwplLockVC.lean`,
reused unchanged: the environment `SwplLock.E` = `EnvGC` with the x64 lock's
plan `xlockPlan`, the table predicates `Fr`, `H1`–`H3`, `QEnd`, and the VCs
`vc_swpa`, `vc_ldr_spin`, `vc_ldr_c`, `vc_str_c`). The release here is the
store release `stlr wzr, [x0]`, whose permission on `EnvGC` is `EnvG`'s
`StoreOk` (claim-conditional environments change only the RMW clauses).

- `storeOk_of_storeKind`: `StoreOk` depends on the architecture and the store
  kind only through the effective kind `A.storeKind k`; so the x64 lock's
  release permission `storeOk_xlockRelease` (`Arch.tso`, `.plain`, effective
  `.rel`) is the permission of an armv8 `stlr` (`.rel`). (Moved,
  same name, to the ISA-neutral `EnvG/LockVC.lean`.)
- `vc_stlr`: the VC of the release, with the proof of the x64 xchg lock's
  `X64Spin.vc_rel` (`EnvG/X64SpinVC.lean`, x64-only, so restated here) at
  `Arch.armv8` and store kind `.rel`. (Now an instance of the
  generic `LockVC.vc_relG`, as are `X64Spin.vc_rel` and `SwplLock.vc_swpl`.)
-/
import Kraken.Promising.SLR.EnvG.SwpEnvGSmoke
import Kraken.Promising.SLR.EnvG.SwplLockVC

namespace Kraken.Promising.SLR.EnvG.SwpEnvG

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin
open Kraken.Promising.SLR.EnvG.SwplLock (E Fr H1 H2 H3 QEnd)

variable {P : Sys} {tid : Nat}

/-- **VC `stlr wzr, [x0]`** (the lock release, a store release of `0`;
`xlockPlan`'s split): permitted from `H3` (`storeOk_xlockRelease` through
`storeOk_of_storeKind`), and every outcome ends in `QEnd`
(`xlockRelease_post`; without a surplus, `LkLe` bounds the own non-zero writes
of `Lk` by the coherence view, below the release). `X64Spin.vc_rel`'s proof
(an instance of `LockVC.vc_relG`). -/
theorem vc_stlr (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32)
    (x5 : BitVec 32) (σ : State isa) (h : H3 P tid x5 σ) :
    (E P tid).ok (.store .rel false P.Lk.addr P.Lk.bytes 0) σ ∧
      ∀ b (σ' : State isa), (E P tid).step (.store .rel false P.Lk.addr P.Lk.bytes 0) σ b σ' → QEnd P σ' :=
  have hG := LockVC.vc_relG (A := Arch.armv8) (sk := .rel) rfl hL hN0 htid hN32 h
  ⟨hG.1, fun _ _ hs => by
    obtain ⟨_, _, hanc, -, hwb, -, -, ⟨_, hPc, hr⟩, hcl', -⟩ := step_storeFacts (pl := xlockPlan P tid) hs
    exact hG.2 hanc.ghost hcl' hwb.coh hPc hr⟩

end Kraken.Promising.SLR.EnvG.SwpEnvG
