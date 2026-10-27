/-
**The generic block and node lemmas at `hello1.w`'s instance**
(`Spike/Lib/Rt/A64RtW.lean`, `Spike/Lib/Rt/A64RtNodes.lean`): `hello1.w`'s
hand facts (`Spike/Lib/A64Hello1I.lean`) are an `InstOk`, and the rows of
its placement data at the hand table's labels pass their phase checks
(`RtNodesOk`) at the hand labels (`labT`), phase index (`ph`) and off-site
pcs (`okPc`), each function returning where hello1's single call path calls
it from, a row's dead targets those off its entry's phase.

- `hello1_instOk`: the instance's facts, as `ret0_instOk`
  (`Spike/Test/A64RtW.lean`).
- `hello1Rows`: the placement data's groups at a label of the hand table
  (`hello1Tab`); the groups off it (`scc_rt_grow`, `scc_rt_park`, …) are
  not reached on hello1's path.
- `hello1Ra`: the return points (`scc_rt_alloc` to `wc_rodata`'s `.sp0`,
  `wc_rodata` to `scc_rt_main`'s `.sp0`, `scc_rt_print` to `wc_main`'s
  `.sp4`, `wc_main` to `scc_rt_main`'s `.sp1`, and the runtime start's
  three as for `ret0.w`); `0` at a group without a `ret`, and at
  `scc_rt_morestack` (several callers; reached only past a failed stack
  check, outside the levels' nodes).
- `labX`: the hand labels extended by the two branch targets off the hand
  table (`hello1TabX`: `scc_rt_abort`, `scc_rt_morestack`), equal to
  `labT` (`labT_eq_labX`), so the kernel reduces every row's targets.
- `hello1_rtNodesOk`: every row passes, one kernel decision at `labX`.
-/
import Spike.Lib.Rt.A64RtW
import Spike.Lib.A64Hello1I
import Spike.Test.A64Hello1PlaceOK

namespace Spike.Test.A64Hello1RtW

open Scc.Sem (Range)
open Spike.Lib.A64.Rt Spike.Lib.A64.Flow.Hello1.Inst
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1End hello1_lays)
open SccCode (hello1Prog)

variable {rS : Range}

/-- **`hello1.w`'s instance facts.** -/
theorem hello1_instOk : InstOk hello1Exe hello1End hello1Prog labT μ0 own Tk (Kr rS) okPc ph :=
  ⟨hello1_lays, rfl, hello1_labT, ph_same, pcOff_of_okPc⟩

/-- The rows of `hello1.w`'s placement data at a label of the hand table. -/
def hello1Rows : List Scc.Cert.Rt.A64.OGrp :=
  Scc.Cert.PlaceOK.A64.Test.hello1Place.blocks.filter fun g => (hello1Tab.lookup g.l).isSome

/-- **The return points on hello1's path**, keyed by the group holding the
`ret`. -/
noncomputable def hello1Ra : Label → Int64
  | ".L2_scc_rt_alloc.5_ok" => labT ".L18_wc_rodata.sp0"
  | ".L3_scc_rt_alloc_tcb.3_ok" => labT ".L0_scc_rt_start.sp2"
  | ".L5_scc_rt_thread_init.sp0" => labT ".L0_scc_rt_start.sp3"
  | "scc_rt_take_site" => labT ".L5_scc_rt_thread_init.sp0"
  | ".L9_scc_rt_print.7_done" => labT ".L19_wc_main.sp4"
  | ".L18_wc_rodata.sp0" => labT ".L1_scc_rt_main.sp0"
  | ".L19_wc_main.sp4" => labT ".L1_scc_rt_main.sp1"
  | _ => 0

/-- A row's dead targets: those off its entry's phase. -/
noncomputable def hello1Dead (l : Label) (k : Nat) (t : Nat) : Bool :=
  ph t != ph (labT l + Int64.ofNat (4 * k)).toBitVec.toNat

/-- The labels the rows branch to off the hand table: the abort's and
`scc_rt_morestack`'s, at their `labIn` addresses. -/
def hello1TabX : List (Label × Nat) := [("scc_rt_abort", 4198284), ("scc_rt_morestack", 4199372)]

theorem hello1TabX_ok : hello1TabX.all tabChk = true := by decide +kernel

/-- The loaded thread's labels, the hand table's and then `hello1TabX`'s. -/
noncomputable def labX (l : Label) : Int64 :=
  match hello1Tab.lookup l with
  | some n => Int64.ofNat n
  | none =>
    match hello1TabX.lookup l with
    | some n => Int64.ofNat n
    | none => (_root_.Executable.labels hello1Exe).label l

/-- `labT` is `labX`: `hello1TabX`'s entries are the loaded thread's labels. -/
theorem labT_eq_labX : labT = labX := by
  funext l
  unfold labT labX
  cases h0 : hello1Tab.lookup l with
  | some n => rfl
  | none =>
    cases hn : hello1TabX.lookup l with
    | some n =>
      have h := List.all_eq_true.mp hello1TabX_ok _ (Spike.Lib.A64.Flow.Ret0.Inst.lookup_mem hn)
      simp only [tabChk, Bool.and_eq_true, beq_iff_eq] at h
      show _ = Int64.ofNat n
      rw [← h.2]
      exact Spike.Lib.A64.OwnLimRt.label_labIn hello1_lays rfl h.1
    | none => rfl

/-- **`hello1.w`'s rows pass their phase checks.** -/
theorem hello1_rtNodesOk : RtNodesOk okPc ph hello1Dead labT hello1Ra hello1Rows := by
  rw [labT_eq_labX]
  exact rtNodesOk_sound (by decide +kernel)

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.A64Hello1RtW.hello1_instOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_instOk

/--
info: 'Spike.Test.A64Hello1RtW.hello1_rtNodesOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_rtNodesOk

end Spike.Test.A64Hello1RtW
