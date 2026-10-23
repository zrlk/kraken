/-
**`tcbW_gen` at `ret0.x`'s instance** (`Spike/Lib/Rt/X64RtTcb.lean`):
`ret0.x`'s `scc_rt_alloc_tcb` has its phase facts at the hand labels,
phases and owned words (`ret0_tcbPh`), and the hand `tcbW`
(`Spike/Lib/X64Ret0I.lean`) follows from the generic one with the hand
premises. The twin of `Spike/Test/A64RtTcb.lean`.
-/
import Spike.Lib.Rt.X64RtTcb
import Spike.Test.X64RtW

namespace Spike.Lib.X64.Rt.Test

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib.X64Consumer Spike.Lib.X64
open Spike.Lib.X64.Rt Spike.Lib.X64.Rt.Tcb Spike.Lib.X64.Flow.Ret0.Inst
open Spike.Lib.X64.Flow.Ret0 (TcbG TcbW pnA pinA)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0End ret0F ret0Words_mapped)
open SccCode (ret0Λ)

/-- `scc_rt_alloc_tcb` returns to `scc_rt_start`'s `.x0`. -/
abbrev ret0TcbRa : Label → Int64 := fun _ => labT ".Lscc_rt_start.x0"

/-- Every pc of the function before the take. -/
theorem ret0_tcbBT : ∀ p ∈ tcbPcs labT, bT p.toBitVec.toNat = true := by decide +kernel

/-- **`ret0.x`'s `scc_rt_alloc_tcb` phase facts**, its header at `scc_rt_pinned`. -/
theorem ret0_tcbPh : TcbPh okPc ph Tk ownOf labT ret0TcbRa 0#64 where
  e := by decide +kernel
  entry := by decide +kernel
  j1 := by decide +kernel
  len := by decide +kernel
  l1 := by decide +kernel
  l2 := by decide +kernel
  l3 := by decide +kernel
  l4 := by decide +kernel
  l5 := by decide +kernel
  l6 := by decide +kernel
  arg := by decide +kernel
  bnd := by decide +kernel
  j2 := by decide +kernel
  o1 := by decide +kernel
  o2 := by decide +kernel
  o3 := by decide +kernel
  o4 := by decide +kernel
  o5 := by decide +kernel
  ret := by decide +kernel
  fullNe := by decide +kernel
  step := by decide +kernel
  rmwOk := by decide +kernel
  noTk := fun p hp s hs => not_tk (hs ▸ ret0_tcbBT p hp)
  rmwIn := by rw [labT_pnA]; exact ⟨_, .head _⟩
  rmwUpd := by rw [labT_pnA]; decide +kernel
  hdrNo := by rw [labT_pinA]; exact not_own (by decide)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

/-- **The hand `tcbW` from the generic one.** -/
example (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → ret0F m) (q : TcbG) (hq : q.c0 = c0) (hn0 : q.n0 = 0#64)
    (hra : q.g.ra = (labT ".Lscc_rt_start.x0").toBitVec) :
    ∀ i, TcbW (Wr rS) (Kr rS) ret0Exe ret0End R F q i :=
  tcbW_gen ret0_instOk ret0_own Flow.Ret0.AllocTcb.ret0_allocTcbIn hC0 hR hlo hhi q hq hra
    (hn0 ▸ ret0_tcbPh) (by rw [labT_pnA]; exact (ret0Words_mapped (by decide)).1)
    (by rw [hn0, labT_pinA]; exact (ret0Words_mapped (by decide)).1)
    (fun m hm => by rw [labT_pnA]; exact hFr m hm _ (by decide))
    (fun m hm => by rw [hn0, labT_pinA]; exact hFr m hm _ (by decide))

end Spike.Lib.X64.Rt.Test
