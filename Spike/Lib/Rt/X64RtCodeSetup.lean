/-
**The x86-64 runtime's code checks but `scc_rt_main`'s and
`scc_rt_thread_init`'s, on either tail** (`RtCodeIn0`): `_start`'s,
`scc_rt_start`'s pieces, `scc_rt_alloc_tcb`'s and `scc_rt_stack_take`'s
checks, which A11 gives at a bare tail (`rtCodeOk` at `bareMC`) and at a
`.setup` tail (`setupOk`, `Spike/Lib/Rt/X64CodeInSetup.lean`) alike. The
twin of `Spike/Lib/Rt/A64RtCodeSetup.lean`.

- `rtCodeIn0_of_ok`, `rtCodeIn0_of_okS`: from the bare and the setup pass.
- `rtCode0_of_placeOKAt`: from `placeOKAt`, whatever the tail; the proofs of
  the runtime's start before `scc_rt_main` read only these.
- `scc_rt_main`'s own check needs the tail: at a bare one
  `rtCodeOk_bare_of_placeOKAt` (`RtCodeIn.main`).
- `scc_rt_thread_init`'s needs it too, unlike on AArch64: x86-64 numbers
  the `.x` labels with one counter over the program, so after a setup
  block its return point is `.x8`, not the `.x7` the hand check
  (`Ret0.ThreadInit.threadInitIn`) and its phase record (`TiPh`) name. At a
  bare tail `RtCodeIn.ti` gives it; at either tail
  `threadInitInAt_of_placeOKAt` gives `Ret0.ThreadInit.threadInitInAt` at
  the tail's return point (`tiOf`: `.x7` or `.x8`), and
  `rtCodeTi_of_placeOKAt` `RtCodeIn0` with it (`RtCodeInTi`).
-/
import Spike.Lib.Rt.X64RtCode
import Scc.Cert.PlaceOKX64

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (startCallIn startCall2In startTailIn)
open Scc.Cert.Rt.X64 (RGrp rtIn rtIn_sound RtAll RtAll.append)

/-- **The runtime's code checks but `scc_rt_main`'s and
`scc_rt_thread_init`'s**, one field each (`RtCodeIn` without `main` and
`ti`). -/
structure RtCodeIn0 (cells : List (Directive × Nat)) : Prop where
  start0 : Code.Start.entryIn cells = true
  start : startIn cells = true
  call : startCallIn cells = true
  call2 : startCall2In cells = true
  tail : startTailIn cells = true
  tcb : Ret0.AllocTcb.allocTcbIn cells = true
  take : Ret0.StackTake.stackTakeIn cells = true

section Of

variable {cells : List (Directive × Nat)}

/-- The checks from the runtime's groups with any `scc_rt_main` groups `gm`
and `scc_rt_thread_init` groups `gt`. -/
theorem rtCodeIn0_of_all {gm gt : List RGrp}
    (h : RtAll cells (startGrpsH ++ gm ++ tcbGrpsH ++ gt ++ takeGrpsH)) : RtCodeIn0 cells := by
  obtain ⟨h, hk⟩ := RtAll.append h
  obtain ⟨h, -⟩ := RtAll.append h
  obtain ⟨h, ht⟩ := RtAll.append h
  obtain ⟨hs, -⟩ := RtAll.append h
  obtain ⟨h0, h1, h2, h3, h4⟩ := start_of hs
  exact ⟨h0, h1, h2, h3, h4, allocTcbIn_of ht, stackTakeIn_of hk⟩

/-- `RtCodeIn` forgets to `RtCodeIn0`. -/
theorem RtCodeIn.toIn0 {mc : MainCode} (h : RtCodeIn cells mc) : RtCodeIn0 cells :=
  ⟨h.start0, h.start, h.call, h.call2, h.tail, h.tcb, h.take⟩

/-- The checks from the bare pass. -/
theorem rtCodeIn0_of_ok {mc : MainCode} (h : rtCodeOk cells mc = true) : RtCodeIn0 cells :=
  (rtCodeIn_of_ok h).toIn0

/-- The checks from the setup pass. -/
theorem rtCodeIn0_of_okS {sc : SetupCode} (h : rtCodeOkS cells sc = true) : RtCodeIn0 cells :=
  rtCodeIn0_of_all (gm := mainSGrps sc) (gt := tiGrpsAt sc.ti) (rtIn_sound h)

/-- The checks from A11 at a `.setup` tail. -/
theorem rtCodeIn0_of_setupOk {lo : Nat} {Λ : Scc.Sem.Layout} (h : setupOk cells lo Λ = true) :
    RtCodeIn0 cells := by
  obtain ⟨sw, -, h⟩ := List.any_eq_true.mp h
  exact rtCodeIn0_of_okS (Bool.and_eq_true _ _ ▸ h).1

/-- `scc_rt_thread_init`'s groups in the setup pass are the hand groups at
the same return point. -/
theorem tiGrpsAt_eq (x : Label) : tiGrpsAt x = tiGrpsHAt x := rfl

/-- **`scc_rt_thread_init`'s code from the setup pass**, its return point at
`sc.ti`. -/
theorem threadInitInAt_of_okS {sc : SetupCode} (h : rtCodeOkS cells sc = true) :
    Ret0.ThreadInit.threadInitInAt cells sc.ti = true := by
  have h := rtIn_sound h
  unfold rtCodeTabS at h
  obtain ⟨h, -⟩ := RtAll.append h
  obtain ⟨-, h⟩ := RtAll.append h
  exact threadInitInAt_of (tiGrpsAt_eq sc.ti ▸ h)

/-- `scc_rt_thread_init`'s return point after a setup block (`SetupCode.ti`
of `setupMC`, whatever the width). -/
abbrev x8L : Label := ".Lscc_rt_thread_init.x8"

theorem setupMC_ti (sw : Nat) : (setupMC sw).ti = x8L := rfl

/-- **`scc_rt_thread_init`'s code from A11 at a `.setup` tail**, its return
point at `.x8`. -/
theorem threadInitInAt_of_setupOk {lo : Nat} {Λ : Scc.Sem.Layout} (h : setupOk cells lo Λ = true) :
    Ret0.ThreadInit.threadInitInAt cells x8L = true := by
  obtain ⟨sw, -, h⟩ := List.any_eq_true.mp h
  exact threadInitInAt_of_okS (sc := setupMC sw) (Bool.and_eq_true _ _ ▸ h).1

end Of

/-- **The runtime's code checks but `scc_rt_main`'s, `scc_rt_thread_init`'s
with its return point at `x`**: `RtCodeIn0` and `threadInitInAt` (`.x7`
after a bare `scc_rt_main`, where it is `RtCodeIn.ti`; `.x8` after a setup
block). -/
structure RtCodeInTi (cells : List (Directive × Nat)) (x : Label) : Prop extends RtCodeIn0 cells where
  ti : Ret0.ThreadInit.threadInitInAt cells x = true

/-- `RtCodeIn` gives `RtCodeInTi` at `.x7`. -/
theorem RtCodeIn.toInTi {cells : List (Directive × Nat)} {mc : MainCode} (h : RtCodeIn cells mc) :
    RtCodeInTi cells Code.Ti.x7L :=
  { h.toIn0 with ti := h.ti }

/-- The checks with `scc_rt_thread_init`'s from the setup pass, at `sc.ti`. -/
theorem rtCodeInTi_of_okS {cells : List (Directive × Nat)} {sc : SetupCode} (h : rtCodeOkS cells sc = true) :
    RtCodeInTi cells sc.ti :=
  { rtCodeIn0_of_okS h with ti := threadInitInAt_of_okS h }

/-- **`scc_rt_thread_init`'s return point** at the shape of `scc_rt_main`'s
tail: `.x7` after a bare `scc_rt_main`, `.x8` after a setup block (the
emitter's one counter of `.x` labels, `Scc.Emit.X64.freshL`). -/
def tiOf : Scc.Cert.PlaceOK.X64.MainShape → Label
  | .bare => Code.Ti.x7L
  | .setup => x8L

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}

/-- **A11, the runtime's code but `scc_rt_main`'s and
`scc_rt_thread_init`'s**, whatever the tail. -/
theorem rtCode0_of_placeOKAt (h : placeOKAt cfg Λ o = true) : RtCodeIn0 o.prog := by
  cases hs : o.place.tail with
  | bare => exact rtCodeIn0_of_ok (rtCodeOk_bare_of_placeOKAt h hs)
  | setup => exact rtCodeIn0_of_setupOk (setupOk_of_placeOKAt h hs)

/-- **A11, `scc_rt_thread_init`'s code, whatever the tail**, its return
point at `tiOf` of the tail (`threadInitIn` at a bare one,
`Ret0.ThreadInit.threadInitInAt_x7`). -/
theorem threadInitInAt_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Ret0.ThreadInit.threadInitInAt o.prog (tiOf o.place.tail) = true := by
  cases hs : o.place.tail with
  | bare => exact (rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)).ti
  | setup => exact threadInitInAt_of_setupOk (setupOk_of_placeOKAt h hs)

/-- `threadInitInAt_of_placeOKAt` at the static link. -/
theorem threadInitInAt_of_placeOK (h : placeOK cfg o = true) :
    Ret0.ThreadInit.threadInitInAt o.prog (tiOf o.place.tail) = true :=
  threadInitInAt_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- **A11, the runtime's code but `scc_rt_main`'s, whatever the tail**:
`RtCodeIn0` with `scc_rt_thread_init`'s at the tail's return point. -/
theorem rtCodeTi_of_placeOKAt (h : placeOKAt cfg Λ o = true) : RtCodeInTi o.prog (tiOf o.place.tail) :=
  { rtCode0_of_placeOKAt h with ti := threadInitInAt_of_placeOKAt h }

/-- `rtCodeTi_of_placeOKAt` at the static link. -/
theorem rtCodeTi_of_placeOK (h : placeOK cfg o = true) : RtCodeInTi o.prog (tiOf o.place.tail) :=
  rtCodeTi_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `rtCode0_of_placeOKAt` at the static link. -/
theorem rtCode0_of_placeOK (h : placeOK cfg o = true) : RtCodeIn0 o.prog :=
  rtCode0_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

end Place

end Spike.Lib.X64.Rt
