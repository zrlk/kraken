import Spike.Test.WakeLinkedX64Le
import Spike.Lib.X64WakeOInit
import Spike.Lib.X64WakeGOf2
import Spike.Lib.X64WakeOSide
import Spike.Lib.X64WakeA64

/-!
# wake's x86-64 linked-instance facts in the root's terms

`Spike/Test/WakeLinkedX64Le.lean` decides the layout facts at `Λe` with local
copies of the root's definitions (`NtZ`, `lim2A`, `r1Of`) and states the goal
at `{ Λe with imms := ie }` and the neutral source semantics `wakeSX` at the
certificate's `prog_src`. The root `X64WakeRootO.wake_finalX_LUO` reads them
as `X64WakeOInit.NtZ`, `X64WakeGOf2.lim2A`, `X64WakeOSide.r1W`, at `Le.Λ` and
at `X64WakeA64.wakeS` (the local `srcPo` at `wakeSrc`). This module identifies
the two, each by `rfl`:

- `ntZ_eq`, `lim2A_eq`, `r1Of_eq`: the local definitions are the root's;
- `hnz_W`, `hinit2_W`, `hsub1_W`: `hnz`, `hinit2`, `hsub1` in the root's terms;
- `ie_eq`: the goal's `ie` is the root's `X64.WakeImms.iW Λe`;
- `Le_Λ`: `Le.Λ` is the goal's layout `{ Λe with imms := ie }`;
- `wakeSrc_eq`, `wakeS_eq`: the local source is `prog_src`, and the root's
  source semantics is the goal's `wakeSX`.

Unlike AArch64 (`Spike/Test/WakeSrcPoEq.lean`, the local `srcPo` only), the
x86-64 goal is also stated at the certificate's `prog_src`, not the root's
local `wakeSrc` (`Spike.Lib.WakeA64` reaches AArch64's syntax; the x86-64
`X64WakeA64` does not, but the goal keeps the neutral form), so the program
itself is bridged here too.
-/

namespace Spike.Test.WakeLinkedX64Br

open Spike.Lib
open Spike.Test.WakeLinkedX64
open SccCertificate (outLit placeCfg prog_src)

/-- The local `NtZ` is `X64WakeOInit.NtZ`. -/
theorem ntZ_eq : Spike.Test.WakeLinkedX64.NtZ = X64WakeOInit.NtZ := rfl

/-- The local `lim2A` is `X64WakeGOf2.lim2A`. -/
theorem lim2A_eq : Spike.Test.WakeLinkedX64.lim2A = X64WakeGOf2.lim2A := rfl

/-- The local `r1Of` at `Le` is `X64WakeOSide.r1W` at `placeWX_e`, `ie`. -/
theorem r1Of_eq : r1Of Le.lab = X64WakeOSide.r1W placeWX_e ie := rfl

/-- `hnz` as the root reads it. -/
theorem hnz_W : X64WakeOInit.NtZ Λe outLit = true := hnz

/-- `hinit2` as the root reads it. -/
theorem hinit2_W :
    (Spike.Lib.X64.PhRec.m0Of Le.Λ outLit.prog outLit.secs).initVal ⟨X64WakeGOf2.lim2A Le, 8⟩ = 0 := hinit2

/-- `hsub1` as the root reads it. -/
theorem hsub1_W : (X64WakeOSide.r1W placeWX_e ie).Sub Le.Λ.stackPool := hsub1

/-- The goal's immediate table is the root's `X64.WakeImms.iW` at `Λe` (the
placement rows hold at `i := iW Λ0`). -/
theorem ie_eq : ie = Spike.Lib.X64.WakeImms.iW Λe := rfl

/-- `Le.Λ` is the goal's layout. -/
theorem Le_Λ : Le.Λ = { Λe with imms := ie } := rfl

/-- **The root's local source is the certificate's `prog_src`.** -/
theorem wakeSrc_eq : Spike.Lib.X64WakeT1.wakeSrc = prog_src := rfl

/-- **The root's source semantics is the goal's.** -/
theorem wakeS_eq (arch : WeakMem.Arch) : Spike.Lib.X64WakeA64.wakeS arch = wakeSX arch := by
  unfold Spike.Lib.X64WakeA64.wakeS wakeSX
  rw [Spike.Lib.X64WakeT1.srcPo_eq, wakeSrc_eq]

end Spike.Test.WakeLinkedX64Br

/-- info: 'Spike.Test.WakeLinkedX64Br.wakeSrc_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64Br.wakeSrc_eq

/-- info: 'Spike.Test.WakeLinkedX64Br.wakeS_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64Br.wakeS_eq

/-- info: 'Spike.Test.WakeLinkedX64Br.Le_Λ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64Br.Le_Λ
