/-
**The main side's thread pointer on x86-64** (wake, `htp`; the twin of
`Spike/Lib/A64WakeHtp.lean`): at `scc_rt_main`'s entry as `_start` leaves
it (`MainE`, `Spike/Lib/Rt/X64StartE.lean`, the exit of `startE_segW(S)` at
the first take's TCB `tcb = pinA + n0 + 8`, set by `arch_prctl(158, 4098)`),
the `%fs` base holds the thread pointer `tcb`; at `n0 = 0` that is the
record's `pinA + 0 + 8`.

- `tpM`: the thread pointer at `scc_rt_main`'s entry, `tpOf` of
  `pinA + n0 + 8` at the executable's labels (`MainE`'s `tcb`).
- `mainJ_tp`: `mainE0`'s invariant fixes `fsBase` to its ghost `tp`.
- `mainJ_tcb`: the same at `MainE`'s ghosts, `fsBase` is `tcb`.
- `tpM_toBitVec`, `tpM_ofPlaceWX`: at `n0 = 0`, `(tpM L 0).toBitVec` is the
  record's `pinA + 0#64 + 8#64` (`lab_pin`), for every record and at
  `RuntimeLayout.ofPlaceWX` (A64's `ofPlaceW`).
- `main_htp`: both halves.
-/
import Spike.Lib.Rt.X64StartE
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64.Flow.WakeHtp

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Flow.Ret0 (MainG mainN0 tpOf)
open Spike.Lib.X64.Rt (MainE mainE0 RuntimeLayout)
open Spike.Lib (PlaceWX)

/-- **The thread pointer at `scc_rt_main`'s entry**: `MainE`'s `tcb`
(`pinA + n0 + 8`, the first take's TCB) as the register's `UInt64`. -/
abbrev tpM (lab : Label → Int64) (n0 : BitVec 64) : UInt64 :=
  tpOf (Ret0.pinA lab + n0 + 8#64)

/-- **`mainE0` fixes the thread pointer**: its invariant holds `fsBase` at
the ghost `tp` (`mainN0`'s third conjunct). -/
theorem mainJ_tp {lab : Label → Int64} {g : MainG} {σ : AS} {c : Ctl}
    (h : (mainE0 lab g).J σ c) : σ.regs.fsBase = g.tp :=
  h.1.2.2

/-- `mainJ_tp` at `MainE`'s ghosts: the thread pointer is `tcb`. -/
theorem mainJ_tcb {lab : Label → Int64} {tcb top : BitVec 64} {c0 : Ctl} {σ : AS} {c : Ctl}
    (h : (mainE0 lab ⟨top, tpOf tcb, c0⟩).J σ c) :
    σ.regs.fsBase.toBitVec = tcb := by
  rw [mainJ_tp h]
  show BitVec.ofNat 64 tcb.toNat = tcb
  simp

/-- **At the first take (`n0 = 0`) the thread pointer is the record's
`pinA + 0 + 8`** (`lab_pin`). -/
theorem tpM_toBitVec (L : RuntimeLayout) {n0 : BitVec 64} (hn0 : n0 = 0#64) :
    (tpM L.lab n0).toBitVec = L.pinA + 0#64 + 8#64 := by
  subst hn0
  show BitVec.ofNat 64 (Ret0.pinA L.lab + 0#64 + 8#64).toNat = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, L.lab_pin]

/-- `tpM_toBitVec` at the record of a placed output. -/
theorem tpM_ofPlaceWX {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    {n0 : BitVec 64} (hn0 : n0 = 0#64) :
    (tpM (RuntimeLayout.ofPlaceWX hp i).lab n0).toBitVec = (RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64 :=
  tpM_toBitVec _ hn0

/-- **The main entry's thread pointer, both halves**: at `MainE`'s
invariant with `tcb = pinA + n0 + 8`, `n0 = 0`, `fsBase` is
`t := tpM L.lab n0` and `t.toBitVec = L.pinA + 0#64 + 8#64`. -/
theorem main_htp (L : RuntimeLayout) {n0 top : BitVec 64} {c0 : Ctl} (hn0 : n0 = 0#64) :
    (∀ σ c, (mainE0 L.lab ⟨top, tpOf (Ret0.pinA L.lab + n0 + 8#64), c0⟩).J σ c →
      σ.regs.fsBase = tpM L.lab n0) ∧ (tpM L.lab n0).toBitVec = L.pinA + 0#64 + 8#64 :=
  ⟨fun _ _ h => mainJ_tp h, tpM_toBitVec L hn0⟩

end Spike.Lib.X64.Flow.WakeHtp

/-- info: 'Spike.Lib.X64.Flow.WakeHtp.mainJ_tp' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeHtp.mainJ_tp

/-- info: 'Spike.Lib.X64.Flow.WakeHtp.mainJ_tcb' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeHtp.mainJ_tcb

/-- info: 'Spike.Lib.X64.Flow.WakeHtp.tpM_ofPlaceWX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeHtp.tpM_ofPlaceWX

/-- info: 'Spike.Lib.X64.Flow.WakeHtp.main_htp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeHtp.main_htp
