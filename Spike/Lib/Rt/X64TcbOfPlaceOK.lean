import Spike.Lib.Rt.X64LayoutOfPlaceOK

/-!
**The main thread's TCB at an output passing `placeOK`** (x86-64): the
thread pointer `scc_rt_start` hands `scc_rt_main` (`MainE`'s `tcb`,
`alloc_tcb`'s `pinned + n0 + 8` at `n0 = 0`, the header word skipped) is
the canonical link's `scc_rt_pinned + 8`, whatever immediates the layout
record's link carries (`rtA` reads the code base, the symbols and the
`.rodata` base only).

- `pinA_ofPlaceOK`: the record's `pinA` is `rtA … "scc_rt_pinned"`;
- `mainE_tcb_ofPlaceOK`: `MainE`'s `tcb` at `n0 = 0`;
- `mainE_tp_ofPlaceOK`: its thread pointer word (`tpOf`).
-/

namespace Spike.Lib.X64.Rt

open Spike.Lib.X64.Flow.Ret0 (tpOf)

section TcbOfPlaceOK

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **The record's first TCB word** is the canonical link's
`scc_rt_pinned`, independent of the immediates `i`. -/
theorem pinA_ofPlaceOK : (RuntimeLayout.ofPlaceOK h i).pinA = Scc.Cert.Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned" :=
  rfl

/-- **`MainE`'s thread pointer base at the first TCB** (`n0 = 0`). -/
theorem mainE_tcb_ofPlaceOK :
    (RuntimeLayout.ofPlaceOK h i).pinA + 0#64 + 8#64 = Scc.Cert.Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned" + 8#64 := by
  rw [pinA_ofPlaceOK, BitVec.add_zero]

/-- **`main`'s thread pointer word** at the first TCB. -/
theorem mainE_tp_ofPlaceOK :
    tpOf ((RuntimeLayout.ofPlaceOK h i).pinA + 0#64 + 8#64) =
      tpOf (Scc.Cert.Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned" + 8#64) := by
  rw [mainE_tcb_ofPlaceOK]

end TcbOfPlaceOK

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Rt.mainE_tcb_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainE_tcb_ofPlaceOK

end Spike.Lib.X64.Rt
