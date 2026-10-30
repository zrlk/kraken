/-
**The main side's thread pointer** (wake, `htp`): at `scc_rt_main`'s entry
as `_start` leaves it (`MainE`, `Spike/Lib/Rt/A64StartE.lean`, the exit of
`startE_segW(S)` at the first take's TCB `tcb = pinA + n0 + 8`), `TPIDR_EL0`
holds the thread pointer `tcb`; at `n0 = 0` that is the record's
`pinA + 0 + 8` (`MainPieces.htp`'s value).

- `tpM`: the thread pointer at `scc_rt_main`'s entry, `UInt64.ofBitVec`
  of `pinA + n0 + 8` at the executable's labels (`MainE`'s `tcb`).
- `mainJ_tp`: `mainE0`'s invariant fixes `TPIDR_EL0` to its ghost `tp`
  (the form of `WakeWc.wJ0_tp`'s premise, a `UInt64` equality).
- `mainJ_tcb`: the same at `MainE`'s ghosts, `TPIDR_EL0` is `tcb`.
- `tpM_toBitVec`, `tpM_ofPlaceOK`: at `n0 = 0`, `(tpM L 0).toBitVec` is
  the record's `pinA + 0#64 + 8#64` (`lab_pin`), for every record and at
  `RuntimeLayout.ofPlaceW`.
-/
import Spike.Lib.Rt.A64StartE
import Spike.Lib.Rt.A64LayoutOfPlaceOK
import Spike.Lib.PlaceWRt

namespace Spike.Lib.A64.Flow.WakeHtp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow.Ret0 (MainG mainN0)
open Spike.Lib.A64.Rt (MainE mainE0 RuntimeLayout)

/-- **The thread pointer at `scc_rt_main`'s entry**: `MainE`'s `tcb`
(`pinA + n0 + 8`, the first take's TCB) as the register's `UInt64`. -/
abbrev tpM (lab : Label → Int64) (n0 : BitVec 64) : UInt64 :=
  UInt64.ofBitVec (Ret0.pinA lab + n0 + 8#64)

/-- **`mainE0` fixes the thread pointer**: its invariant holds `TPIDR_EL0`
at the ghost `tp` (`mainN0`'s third conjunct). -/
theorem mainJ_tp {lab : Label → Int64} {g : MainG} {σ : AS} {c : Ctl}
    (h : (mainE0 lab g).J σ c) : σ.regs.TPIDR_EL0 = g.tp :=
  h.1.2.2

/-- `mainJ_tp` at `MainE`'s ghosts: the thread pointer is `tcb`. -/
theorem mainJ_tcb {lab : Label → Int64} {tcb top : BitVec 64} {c0 : Ctl} {σ : AS} {c : Ctl}
    (h : (mainE0 lab ⟨top, UInt64.ofBitVec tcb, c0⟩).J σ c) :
    σ.regs.TPIDR_EL0.toBitVec = tcb := by
  rw [mainJ_tp h]

/-- **At the first take (`n0 = 0`) the thread pointer is the record's
`pinA + 0 + 8`** (`lab_pin`). -/
theorem tpM_toBitVec (L : RuntimeLayout) {n0 : BitVec 64} (hn0 : n0 = 0#64) :
    (tpM L.lab n0).toBitVec = L.pinA + 0#64 + 8#64 := by
  subst hn0
  show Ret0.pinA L.lab + 0#64 + 8#64 = _
  rw [L.lab_pin]

/-- `tpM_toBitVec` at the record of a placed output (`MainPieces.htp`'s
form). -/
theorem tpM_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    {n0 : BitVec 64} (hn0 : n0 = 0#64) :
    (tpM (RuntimeLayout.ofPlaceW hp i).lab n0).toBitVec = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 :=
  tpM_toBitVec _ hn0

/-- **The main entry's thread pointer, both halves** (`WakeWc.wJ0_tp`'s
premise and `MainPieces.htp`'s value): at `MainE`'s invariant with
`tcb = pinA + n0 + 8`, `n0 = 0`, `TPIDR_EL0` is `t := tpM L.lab n0` and
`t.toBitVec = L.pinA + 0#64 + 8#64`. -/
theorem main_htp (L : RuntimeLayout) {n0 top : BitVec 64} {c0 : Ctl} (hn0 : n0 = 0#64) :
    (∀ σ c, (mainE0 L.lab ⟨top, UInt64.ofBitVec (Ret0.pinA L.lab + n0 + 8#64), c0⟩).J σ c →
      σ.regs.TPIDR_EL0 = tpM L.lab n0) ∧ (tpM L.lab n0).toBitVec = L.pinA + 0#64 + 8#64 :=
  ⟨fun _ _ h => mainJ_tp h, tpM_toBitVec L hn0⟩

end Spike.Lib.A64.Flow.WakeHtp

/-- info: 'Spike.Lib.A64.Flow.WakeHtp.mainJ_tp' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeHtp.mainJ_tp

/-- info: 'Spike.Lib.A64.Flow.WakeHtp.tpM_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeHtp.tpM_ofPlaceOK

/-- info: 'Spike.Lib.A64.Flow.WakeHtp.main_htp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeHtp.main_htp
