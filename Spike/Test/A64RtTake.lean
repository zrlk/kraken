/-
**`takeW_gen` at `ret0.w`'s instance** (`Spike/Lib/Rt/A64RtTake.lean`):
`ret0.w`'s `scc_rt_stack_take` has its phase facts at the hand labels,
phases, owned words and marks (`ret0_takePh`), and the hand `takeSiteW` and
`takeW` (`Spike/Lib/A64Ret0I.lean`) follow from the generic one with the
hand premises.
-/
import Spike.Lib.Rt.A64RtTake
import Spike.Test.A64RtW

namespace Spike.Lib.A64.Rt.Test

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Spike.Lib.A64Consumer Spike.Lib.A64
open Spike.Lib.A64.Rt Spike.Lib.A64.Rt.Take Spike.Lib.A64.Flow.Ret0.Inst
open Spike.Lib.A64.Flow (FStable)
open Spike.Lib.A64.Flow.Ret0 (TakeG TakeW StackM stacksA)
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F ret0Words_mapped)
open SccCode (ret0Λ ret0Prog)

/-- `scc_rt_stack_take` returns to `scc_rt_thread_init`'s `.sp0`. -/
abbrev ret0TakeRa : Label → Int64 := fun _ => labT ".L5_scc_rt_thread_init.sp0"

/-- Every pc of the function before the take. -/
theorem ret0_takeBT : ∀ p ∈ takePcs labT, bT p.toBitVec.toNat = true := by decide +kernel

/-- **`ret0.w`'s `scc_rt_stack_take` phase facts.** -/
theorem ret0_takePh : TakePh okPc ph Tk ownOf μ0 labT ret0TakeRa where
  e := by decide +kernel
  entry := by decide +kernel
  cls := by decide +kernel
  j1 := by decide +kernel
  d2 := by decide +kernel
  d9 := by decide +kernel
  d16 := by decide +kernel
  sp0 := by decide +kernel
  sp3 := by decide +kernel
  lk0 := by decide +kernel
  lk2 := by decide +kernel
  b2 := by decide +kernel
  b8 := by decide +kernel
  b12 := by decide +kernel
  b21 := by decide +kernel
  ok2 := by decide +kernel
  tk := by decide +kernel
  ret := by decide +kernel
  si := by decide +kernel
  swpOk := by decide +kernel
  ldnOk := by decide +kernel
  unlOk := by decide +kernel
  nxtOk := by decide +kernel
  ldnPh := by decide +kernel
  noTk := fun p hp s hs => not_tk (hs ▸ ret0_takeBT p hp)
  swpIn := by rw [labT_lockA]; exact ⟨_, .tail _ (.head _)⟩
  swpUpd := by rw [labT_lockA]; decide +kernel
  unlIn := by rw [labT_lockA]; exact ⟨_, .tail _ (.head _)⟩
  unlUpd := by rw [labT_lockA]; decide +kernel
  nxtIn := by rw [labT_nextA]; exact ⟨_, .tail _ (.tail _ (.tail _ (.head _)))⟩
  nxtUpd := by rw [labT_nextA]; decide +kernel
  siteRel := fun a ha => by cases ha; decide +kernel
  siteAb := fun k a ha => by cases k <;> cases ha <;> decide +kernel
  siteAt := mu0_take
  siteOwn := by decide +kernel
  tk4 := fun s hs => by show ph (Scc.Sem.A64.pcOf s) / 8 % 2 = 0; rw [hs]; decide +kernel

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

/-- **The hand `takeSiteW` and `takeW` from the generic one.** -/
example (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) (q : TakeG)
    (hq : q.c0 = c0) (hra : q.g.ra = (labT ".L5_scc_rt_thread_init.sp0").toBitVec)
    (hrS : rS = ⟨(stacksA labT + q.k0).toNat, 16384⟩)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS)) :
    ∀ i, TakeW (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q i :=
  takeW_gen ret0_instOk ret0_own Flow.Ret0.StackTake.ret0_stackTakeIn hC0 hR hal hlo hhi q hq hra ret0_takePh
    (by rw [labT_lockA]; exact (ret0Words_mapped (by decide)).1)
    (by rw [labT_freeNA]; exact (ret0Words_mapped (by decide)).2.1)
    (by rw [labT_nextA]; exact (ret0Words_mapped (by decide)).1)
    (fun m hm => by rw [labT_lockA]; exact hFr m hm _ (by decide))
    (fun m hm => by rw [labT_freeNA]; exact hFr m hm _ (by decide))
    (fun m hm => by rw [labT_nextA]; exact hFr m hm _ (by decide))
    hrS hsub (by unfold Scc.Sem.Range.Disjoint; decide +kernel) hSM

end Spike.Lib.A64.Rt.Test
