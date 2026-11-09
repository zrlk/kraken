/-
**`RtNodesOk` on `ret0.w`** (`Spike/Lib/Rt/A64RtNodes.lean`): the rows of
`ret0.w`'s placement data under the runtime's code groups (`rtCodeTab`)
pass their phase checks at the hand labels (`labT`), phase index (`ph`) and
off-site pcs (`okPc`) of `Spike/Lib/A64Ret0I.lean`, each function returning
where the main path calls it from, a row's dead targets those off its entry's
phase.
-/
import Spike.Lib.Rt.A64RtNodes
import Spike.Lib.Rt.A64CodeIn
import Spike.Lib.A64Ret0I
import Spike.Test.A64Ret0PlaceOK

namespace Spike.Lib.A64.Rt.Test

open Spike.Lib.A64.Rt Spike.Lib.A64.Flow.Ret0.Inst

/-- The rows of `ret0.w`'s placement data under the runtime's code groups. -/
def ret0RtRows : List Scc.Cert.Rt.A64.OGrp :=
  Scc.Cert.PlaceOK.A64.Test.ret0Place.blocks.filter fun g => (rtCodeTab bareMC).any fun r => r.l == g.l

/-- Every runtime group of `rtCodeTab` has its rows but `scc_rt_main`'s
label, which falls through into its check without code of its own. -/
example : ((rtCodeTab bareMC).map (·.l)).filter (fun l => !(ret0RtRows.any (·.l == l))) = ["scc_rt_main"] := by
  decide +kernel

/-- The return points on the main path, keyed by the group holding the `ret`
(its own label since P5: `.x<n>` before each function's `ret`):
`scc_rt_alloc_tcb` to `.sp2`, `scc_rt_thread_init` to `.sp3`,
`scc_rt_stack_take` to `scc_rt_thread_init`'s `.sp0`; no `ret` elsewhere. -/
def ret0Ra : Label → Int64
  | ".L3_scc_rt_alloc_tcb.x25" => labT ".L0_scc_rt_start.sp2"
  | ".L5_scc_rt_thread_init.x9" => labT ".L0_scc_rt_start.sp3"
  | ".L6_scc_rt_stack_take.x42" => labT ".L5_scc_rt_thread_init.sp0"
  | _ => 0

/-- A row's dead targets: those off its entry's phase. -/
def ret0Dead (l : Label) (k : Nat) (t : Nat) : Bool := ph t != ph (labT l + Int64.ofNat (4 * k)).toBitVec.toNat

/-- The rows' labels off the hand table: the `ret` groups' labels, at their
`labIn` addresses. -/
def ret0TabX : List (Label × Nat) :=
  [(".L3_scc_rt_alloc_tcb.x25", 4195384), (".L5_scc_rt_thread_init.x9", 4195652),
    (".L6_scc_rt_stack_take.x42", 4196216)]

theorem ret0TabX_ok : ret0TabX.all (fun p => Spike.Lib.A64.OwnLimRt.labOk SccCode.ret0Prog p.1 &&
    Spike.Lib.A64.OwnLimRt.labIn SccCode.ret0Λ.code.lo SccCode.ret0Prog p.1 == Int64.ofNat p.2) = true := by
  decide +kernel

/-- No data symbol of the loaded thread is below the code. -/
theorem ret0Syms_above : ((Scc.Sem.loadSyms SccCode.ret0Λ SccCode.ret0Secs.rodata).all fun p =>
    decide (SccCode.ret0Λ.code.lo ≤ p.2)) = true := by
  decide +kernel

/-- The loaded thread starts at the code (`exeStart_of_above`), stated so that `label_labIn`'s base
needs no unfolding of the layout. -/
theorem ret0Exe_fst : Spike.Lib.A64.Flow.Ret0.Mem.ret0Exe.1 = Int64.ofNat SccCode.ret0Λ.code.lo := by
  show Int64.ofNat (Scc.Sem.exeStart SccCode.ret0Λ.code.lo (Scc.Sem.loadSyms SccCode.ret0Λ SccCode.ret0Secs.rodata)) = _
  rw [Scc.Cert.PlaceSyms.exeStart_of_above fun p hp => of_decide_eq_true (List.all_eq_true.mp ret0Syms_above p hp)]

/-- The loaded thread's labels, the hand table's and then `ret0TabX`'s. -/
def labX (l : Label) : Int64 :=
  match ret0Tab.lookup l with
  | some n => Int64.ofNat n
  | none =>
    match ret0TabX.lookup l with
    | some n => Int64.ofNat n
    | none => (_root_.Executable.labels Spike.Lib.A64.Flow.Ret0.Mem.ret0Exe).label l

/-- `labT` is `labX`: `ret0TabX`'s entries are the loaded thread's labels. -/
theorem labT_eq_labX : labT = labX := by
  funext l
  unfold labT labX
  cases h0 : ret0Tab.lookup l with
  | some n => rfl
  | none =>
    cases hn : ret0TabX.lookup l with
    | some n =>
      have h := List.all_eq_true.mp ret0TabX_ok _ (lookup_mem hn)
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      show _ = Int64.ofNat n
      rw [← h.2]
      exact Spike.Lib.A64.OwnLimRt.label_labIn Spike.Lib.A64.Flow.Ret0.Mem.ret0_lays ret0Exe_fst h.1
    | none => rfl

/-- **`ret0.w`'s runtime rows pass their phase checks**, one kernel decision at `labX`. -/
theorem ret0_rtNodesOk : RtNodesOk okPc ph ret0Dead labT ret0Ra ret0RtRows := by
  rw [labT_eq_labX]
  exact rtNodesOk_sound (by decide +kernel)

/-- A row with a phase crossing: `scc_rt_alloc_tcb`'s check branches to the
abort, off its phase; with no dead target the check fails. -/
example : rtNodesOk okPc ph (fun _ _ _ => false) labT ret0Ra ret0RtRows = false := by decide +kernel

end Spike.Lib.A64.Rt.Test
