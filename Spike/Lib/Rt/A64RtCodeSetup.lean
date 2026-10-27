/-
**The runtime's code checks but `scc_rt_main`'s, on either tail**
(`RtCodeIn0`): `_start`'s branch, `scc_rt_start`'s pieces,
`scc_rt_alloc_tcb`'s, `scc_rt_thread_init`'s and `scc_rt_stack_take`'s
checks, which A11 gives at a bare tail (`rtCodeOk` at `bareMC`) and at a
`.setup` tail (`setupOk`, `Spike/Lib/Rt/A64CodeInSetup.lean`) alike.

- `rtCodeIn0_of_ok`, `rtCodeIn0_of_okS`: from the bare and the setup pass.
- `rtCode0_of_placeOKAt`: from `placeOKAt`, whatever the tail; the proofs of
  the runtime's start before `scc_rt_main` read only these.
- `scc_rt_main`'s own check needs the tail: at a bare one
  `rtCodeOk_bare_of_placeOKAt` (`RtCodeIn.main`).
-/
import Spike.Lib.Rt.A64RtCode
import Scc.Cert.PlaceOKA64

namespace Spike.Lib.A64.Rt

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64 Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (startCallIn startTailIn tiSpIn entryB)
open Scc.Cert.Rt.A64 (RGrp rtIn rtIn_sound RtAll RtAll.append blockAt)

/-- **The runtime's code checks but `scc_rt_main`'s**, one field each
(`RtCodeIn` without `main`). -/
structure RtCodeIn0 (prog : List Directive) : Prop where
  entry : blockAt prog "_start" 0 entryB = true
  start : startIn prog = true
  call : startCallIn prog = true
  tail : startTailIn prog = true
  tcb : Ret0.AllocTcb.allocTcbIn prog = true
  ti : Ret0.ThreadInit.threadInitIn prog = true
  tiSp : tiSpIn prog = true
  take : Ret0.StackTake.stackTakeIn prog = true

section Of

variable {prog : List Directive}

/-- The checks from the runtime's groups with any `scc_rt_main` groups `gm`. -/
theorem rtCodeIn0_of_all {gm : List RGrp}
    (h : RtAll prog (startGrps ++ gm ++ tcbGrps ++ tiGrps ++ takeGrps)) : RtCodeIn0 prog := by
  obtain ⟨h, hk⟩ := RtAll.append h
  obtain ⟨h, hi⟩ := RtAll.append h
  obtain ⟨h, ht⟩ := RtAll.append h
  obtain ⟨hs, -⟩ := RtAll.append h
  obtain ⟨h0, h1, h2, h3⟩ := start_of (prog := prog) hs
  obtain ⟨h5, h6⟩ := threadInitIn_of (prog := prog) hi
  exact ⟨h0, h1, h2, h3, allocTcbIn_of ht, h5, h6, stackTakeIn_of hk⟩

/-- The checks from the bare pass. -/
theorem rtCodeIn0_of_ok {mc : MainCode} (h : rtCodeOk prog mc = true) : RtCodeIn0 prog :=
  rtCodeIn0_of_all (rtIn_sound h)

/-- The checks from the setup pass. -/
theorem rtCodeIn0_of_okS {sc : SetupCode} (h : rtCodeOkS prog sc = true) : RtCodeIn0 prog :=
  rtCodeIn0_of_all (rtIn_sound h)

/-- The checks from A11 at a `.setup` tail. -/
theorem rtCodeIn0_of_setupOk {lo : Nat} {Λ : Scc.Sem.Layout} (h : setupOk prog lo Λ = true) :
    RtCodeIn0 prog := by
  obtain ⟨sw, -, h⟩ := List.any_eq_true.mp h
  exact rtCodeIn0_of_okS (Bool.and_eq_true _ _ ▸ h).1

end Of

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out}

/-- **A11, the runtime's code but `scc_rt_main`'s**, whatever the tail. -/
theorem rtCode0_of_placeOKAt (h : placeOKAt cfg Λ o = true) : RtCodeIn0 o.prog := by
  cases hs : o.place.tail with
  | bare => exact rtCodeIn0_of_ok (rtCodeOk_bare_of_placeOKAt h hs)
  | setup => exact rtCodeIn0_of_setupOk (setupOk_of_placeOKAt h hs)

/-- `rtCode0_of_placeOKAt` at the static link. -/
theorem rtCode0_of_placeOK (h : placeOK cfg o = true) : RtCodeIn0 o.prog :=
  rtCode0_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

end Place

end Spike.Lib.A64.Rt
