/-
**wake.w on x86-64: the runtime layout's executable is in the one-word
fragment** (the instance fact `hwide` of `X64WakeFinal`'s statements and
`X64WakeMainHRI.hMainR_I`'s `hw`, X64-MainHR-hw), for every output with
wake's placement facts.

- `hwide_W hp i`: `Scc.Cert.WideX64.ExeWide (RuntimeLayout.ofPlaceWX hp i).exe`,
  from `PlaceWX`'s A4 (`PlaceWX.wideIn_of_placeWX`) and `wideSt_threadAt`
  (`ofPlaceWX`'s executable is the canonical thread's).

**Where this differs from AArch64**: AArch64 decides `hwide` at the linked
layout (`WakeLinkedA64.hwide`, from `wake_exeWide` at `wakeProg`); here it
holds at any `PlaceWX` output, so it is no longer an instance premise.
-/
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64WakeHwW

open Spike.Lib.PlaceWX

/-- **`hwide` at `ofPlaceWX`**: A4 puts the output's cells in the fragment,
and `ofPlaceWX`'s executable is the canonical thread's of those cells. -/
theorem hwide_W {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    Scc.Cert.WideX64.ExeWide (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).exe :=
  (Scc.Cert.WideX64.wideSt_threadAt (wideIn_of_placeWX hp) Scc.Sem.Entry.linux _ _).2

end Spike.Lib.X64WakeHwW

/-- info: 'Spike.Lib.X64WakeHwW.hwide_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHwW.hwide_W
