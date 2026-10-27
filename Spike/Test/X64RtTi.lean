/-
**`tiW_gen` at `ret0.x`'s instance** (`Spike/Lib/Rt/X64RtTi.lean`):
`ret0.x`'s `scc_rt_thread_init` has its phase facts at the hand labels and
phases (`ret0_tiPh`), and the hand `tiW` (`Spike/Lib/X64Ret0I.lean`) follows
from the generic one with the hand premises, without its take site premise.
The twin of `Spike/Test/A64RtTi.lean`.
-/
import Spike.Lib.Rt.X64RtTi
import Spike.Test.X64RtTake

namespace Spike.Lib.X64.Rt.Test

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib.X64Consumer Spike.Lib.X64
open Spike.Lib.X64.Rt Spike.Lib.X64.Rt.Ti Spike.Lib.X64.Flow.Ret0.Inst
open Spike.Lib.X64.Flow.Ret0 (TiG TiW StackM stacksA)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0End ret0F ret0Words_mapped)
open SccCode (ret0Λ)

/-- `scc_rt_thread_init` returns to `scc_rt_start`'s `.x1`. -/
abbrev ret0TiRa : Label → Int64 := fun _ => labT ".Lscc_rt_start.x1"

/-- The pcs before the call, before the take. -/
theorem ret0_tiBT : ∀ p ∈ preTkPcs labT, bT p.toBitVec.toNat = true := by decide +kernel

/-- **`ret0.x`'s `scc_rt_thread_init` phase facts.** -/
theorem ret0_tiPh : TiPh okPc ph Tk labT ret0TiRa where
  e := by decide +kernel
  entry := by decide +kernel
  c7 := by decide +kernel
  x7 := by decide +kernel
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

/-- The TCB's six words among `ret0.x`'s, owned at no phase. -/
theorem ret0_tiAddrs : ∀ a ∈ tiAddrs 134217736#64,
    a ∈ Flow.Ret0.Mem.ret0Words ∧ a ∉ [6291472#64, 6291496#64, 6291504#64, 6291488#64] := by
  rw [ret0_tiAddrs_eq]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

/-- **The hand `tiW` from the generic one**, without its take site premise. -/
example (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → ret0F m) (q : TiG) (hq : q.c0 = c0) (hra : q.g.ra = (labT ".Lscc_rt_start.x1").toBitVec)
    (htcb : q.tcb = 134217736#64) (hrS : rS = ⟨(stacksA labT + q.k0).toNat, 16384⟩)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS))
    (hSM' : FStable (R.callee (-48 - 0) (-200) 8) (StackM rS)) :
    ∀ i, TiW (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q i :=
  tiW_gen ret0_instOk ret0_own Flow.Ret0.ThreadInit.ret0_threadInitIn hC0 hR hlo hhi q hq hra ret0_tiPh
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

/-- **The same from `tiWAt_gen` at `.x7`** (`TiWAt` at `.x7` is `TiW`,
`tiWAt_x7`; `threadInitInAt` at `.x7` is `threadInitIn`, `TiPhAt` at `.x7`
`TiPh`). -/
example (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → ret0F m) (q : TiG) (hq : q.c0 = c0) (hra : q.g.ra = (labT ".Lscc_rt_start.x1").toBitVec)
    (htcb : q.tcb = 134217736#64) (hrS : rS = ⟨(stacksA labT + q.k0).toNat, 16384⟩)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS))
    (hSM' : FStable (R.callee (-48 - 0) (-200) 8) (StackM rS)) :
    ∀ i, TiWAt (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q Flow.Ret0.ThreadInit.x7L i :=
  tiWAt_gen ret0_instOk ret0_own Flow.Ret0.ThreadInit.ret0_threadInitIn hC0 hR hlo hhi q hq hra ret0_tiPh.toAt
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

end Spike.Lib.X64.Rt.Test
