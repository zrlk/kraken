/-
**`tiW_gen` at `ret0.w`'s instance** (`Spike/Lib/Rt/A64RtTi.lean`):
`ret0.w`'s `scc_rt_thread_init` has its phase facts at the hand labels and
phases (`ret0_tiPh`), and the hand `tiW` (`Spike/Lib/A64Ret0I.lean`) follows
from the generic one with the hand premises, without its take site premise.
-/
import Spike.Lib.Rt.A64RtTi
import Spike.Test.A64RtTake

namespace Spike.Lib.A64.Rt.Test

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Spike.Lib.A64Consumer Spike.Lib.A64
open Spike.Lib.A64.Rt Spike.Lib.A64.Rt.Ti Spike.Lib.A64.Flow.Ret0.Inst
open Spike.Lib.A64.Flow (FStable)
open Spike.Lib.A64.Flow.Ret0 (TiG TiW StackM stacksA)
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F ret0Words_mapped)
open SccCode (ret0Λ ret0Prog)

/-- `scc_rt_thread_init` returns to `scc_rt_start`'s `.sp3`. -/
abbrev ret0TiRa : Label → Int64 := fun _ => labT ".L0_scc_rt_start.sp3"

/-- The prologue's and the call's pcs, before the take. -/
theorem ret0_tiBT : ∀ p ∈ [labT Flow.Ret0.ThreadInit.fnL + Int64.ofNat (4 * 0),
    labT Flow.Ret0.ThreadInit.entryL + Int64.ofNat (4 * 0)], bT p.toBitVec.toNat = true := by decide +kernel

/-- **`ret0.w`'s `scc_rt_thread_init` phase facts.** -/
theorem ret0_tiPh : TiPh okPc ph Tk labT ret0TiRa where
  e := by decide +kernel
  entry := by decide +kernel
  sp := by decide +kernel
  f1 := by decide +kernel
  f2 := by decide +kernel
  f3 := by decide +kernel
  f4 := by decide +kernel
  f5 := by decide +kernel
  ret := by decide +kernel
  st := by decide +kernel
  noTk := fun p hp s hs => not_tk (hs ▸ ret0_tiBT p hp)

/-- The TCB at `scc_rt_pinned + 8`: its six words. -/
theorem ret0_tiAddrs_eq : tiAddrs 134217736#64 =
    [134217736#64, 134217744#64, 134217752#64, 134217760#64, 134217768#64, 134217776#64] := rfl

/-- The TCB's six words among `ret0.w`'s, owned at no phase. -/
theorem ret0_tiAddrs : ∀ a ∈ tiAddrs 134217736#64,
    a ∈ Flow.Ret0.Mem.ret0Words ∧ a ∉ [6291472#64, 6291496#64, 6291504#64, 6291488#64] := by
  rw [ret0_tiAddrs_eq]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

/-- **The hand `tiW` from the generic one**, without its take site premise. -/
example (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) (q : TiG)
    (hq : q.c0 = c0) (hra : q.g.ra = (labT ".L0_scc_rt_start.sp3").toBitVec) (htcb : q.tcb = 134217736#64)
    (hrS : rS = ⟨(stacksA labT + q.k0).toNat, 16384⟩)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS))
    (hSM' : FStable (R.callee Flow.Ret0.ThreadInit.oI.sp (-208) 0) (StackM rS)) :
    ∀ i, TiW (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q i :=
  tiW_gen ret0_instOk ret0_own Flow.Ret0.ThreadInit.ret0_threadInitIn hC0 hR hal hlo hhi q hq hra ret0_tiPh
    (fun a ha => (ret0Words_mapped (ret0_tiAddrs a (htcb ▸ ha)).1).1)
    (fun a ha m hm => hFr m hm a (ret0_tiAddrs a (htcb ▸ ha)).1)
    (fun a ha => not_own (ret0_tiAddrs a (htcb ▸ ha)).2)
    hsub hSM hSM' Flow.Ret0.StackTake.ret0_stackTakeIn ret0_takePh
    (by rw [labT_lockA]; exact (ret0Words_mapped (by decide)).1)
    (by rw [labT_freeNA]; exact (ret0Words_mapped (by decide)).2.1)
    (by rw [labT_nextA]; exact (ret0Words_mapped (by decide)).1)
    (fun m hm => by rw [labT_lockA]; exact hFr m hm _ (by decide))
    (fun m hm => by rw [labT_freeNA]; exact hFr m hm _ (by decide))
    (fun m hm => by rw [labT_nextA]; exact hFr m hm _ (by decide))
    hrS (by unfold Scc.Sem.Range.Disjoint; decide +kernel)

end Spike.Lib.A64.Rt.Test
