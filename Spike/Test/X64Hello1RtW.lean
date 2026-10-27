/-
**The generic block and node lemmas at `hello1.x`'s instance**
(`Spike/Lib/Rt/X64RtW.lean`, `Spike/Lib/Rt/X64RtNodes.lean`): `hello1.x`'s
hand facts (`Spike/Lib/X64Hello1I.lean`) are an `InstOk`, and the rows of
its placement data at the hand table's labels pass their phase checks
(`RtNodesOk`) at the hand labels (`labT`), phase index (`ph`) and off-site
pcs (`okPc`), each function returning where hello1's single call path calls
it from, a row's dead targets those off its entry's phase. The twin of
`Spike/Test/A64Hello1RtW.lean`.

- `hello1_instOk`: the instance's facts, as `ret0_instOk`
  (`Spike/Test/X64RtW.lean`).
- `hello1Rows`: the placement data's groups at a label of the hand table
  (`hello1Tab`); the groups off it (`scc_rt_grow`, `scc_rt_park`, …) are
  not reached on hello1's path.
- `hello1Ra`: the return points (`scc_rt_alloc` to `wc_rodata`'s `.x13`,
  `wc_rodata` to `scc_rt_main`'s `.x2`, `scc_rt_print` to `wc_main`'s
  `.x15`, `wc_main` to `scc_rt_main`'s `.x3`, and the runtime start's
  three as for `ret0.x`, `scc_rt_stack_take` returning to
  `scc_rt_thread_init`'s `.x8`); `0` at a group without a `ret`, and at
  `scc_rt_thread_reserve` (no caller on hello1's path).
- `hello1Dead`: a row's dead targets, as `ret0Dead`
  (`Spike/Test/X64RtNodes.lean`), at the row's byte offset.
- `labX`: the hand labels extended by the two branch targets off the hand
  table (`hello1TabX`: `scc_rt_abort`, `scc_rt_morestack`), equal to
  `labT` (`labT_eq_labX`), so the kernel reduces every row's targets.
- `hello1_rtNodesOk`: every row passes, one kernel decision at `labX`.
-/
import Spike.Lib.Rt.X64RtW
import Spike.Lib.X64Hello1I
import Spike.Test.X64Hello1PlaceOK

namespace Spike.Test.X64Hello1RtW

open Kraken
open Scc.Sem (Range)
open Spike.Lib.X64.Rt Spike.Lib.X64.Flow.Hello1.Inst
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End hello1_lays)
open Spike.Lib.X64.OwnLimRt (labIn label_labIn)
open Scc.Cert.Rt.X64 (labelIdx)
open SccCode (hello1Λ hello1Cells)

variable {rS : Range}

/-- **`hello1.x`'s instance facts.** -/
theorem hello1_instOk : InstOk hello1Exe hello1End hello1Cells labT μ0 own Tk (Kr rS) okPc ph :=
  ⟨hello1_lays, rfl, hello1_labT, ph_same, pcOff_of_okPc⟩

/-- The rows of `hello1.x`'s placement data at a label of the hand table. -/
def hello1Rows : List Scc.Cert.Rt.X64.OGrp :=
  Scc.Cert.PlaceOK.X64.Test.hello1Place.blocks.filter fun g => (hello1Tab.lookup g.l).isSome

/-- **The return points on hello1's path**, keyed by the group holding the
`ret`. -/
noncomputable def hello1Ra : Label → Int64
  | ".Lscc_rt_alloc.ok" => labT ".Lwc_rodata.x13"
  | ".Lscc_rt_alloc_tcb.ok" => labT ".Lscc_rt_start.x0"
  | ".Lscc_rt_thread_init.x8" => labT ".Lscc_rt_start.x1"
  | "scc_rt_take_site" => labT ".Lscc_rt_thread_init.x8"
  | ".Lscc_rt_print.done" => labT ".Lwc_main.x15"
  | ".Lwc_rodata.x13" => labT ".Lscc_rt_main.x2"
  | ".Lwc_main.x15" => labT ".Lscc_rt_main.x3"
  | _ => 0

/-- A row's dead targets: those off its entry's phase. -/
noncomputable def hello1Dead (l : Label) (k : Nat) (t : Nat) : Bool :=
  ph t != ph (labT l + Int64.ofNat (((hello1Rows.find? (·.l == l)).bind fun g =>
    (g.bs.find? (·.k == k)).map (·.off)).getD 0)).toBitVec.toNat

/-- A label of the cells at its `labIn` address. -/
noncomputable def tabChk (p : Label × Nat) : Bool :=
  (labelIdx hello1Cells p.1).isSome && labIn hello1Λ.code.lo hello1Cells p.1 == Int64.ofNat p.2

/-- The labels the rows branch to off the hand table: the abort's and
`scc_rt_morestack`'s, at their `labIn` addresses. -/
def hello1TabX : List (Label × Nat) := [("scc_rt_abort", 4198390), ("scc_rt_morestack", 4199229)]

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
      have h := List.all_eq_true.mp hello1TabX_ok _ (Spike.Lib.X64.Flow.Ret0.Inst.lookup_mem hn)
      simp only [tabChk, Bool.and_eq_true, beq_iff_eq] at h
      show _ = Int64.ofNat n
      rw [← h.2]
      exact label_labIn hello1_lays rfl h.1
    | none => rfl

/-- **`hello1.x`'s rows pass their phase checks.** -/
theorem hello1_rtNodesOk : RtNodesOk okPc ph hello1Dead labT hello1Ra hello1Rows := by
  rw [labT_eq_labX]
  exact rtNodesOk_sound (by decide +kernel)

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.X64Hello1RtW.hello1_instOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_instOk

/--
info: 'Spike.Test.X64Hello1RtW.hello1_rtNodesOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_rtNodesOk

end Spike.Test.X64Hello1RtW
