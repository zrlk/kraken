import Spike.Lib.LowerA64.BodyW
import Spike.Lib.A64Ret0I
import Spike.Test.LowerA64Ret0Oracle
import Spike.Test.SegLag

/-!
# `bodyPhOk` at `ret0.w`'s `main` (AArch64)

The body's three blocks (the checked add, its store, the return) pass the
phase check at the hand placement's tables (`Ret0.Inst.okPc`, `ph`, `labT`),
the return's target `scc_rt_main`'s call site plus 4; with no pc allowed, or
with a return target in another phase, they fail. `blkPh_of_inBody` then gives
each block's `blkPh`; `BodyW0` is satisfiable.
-/

namespace Spike.Test.LowerA64BodyW

open Spike.Lib.LowerA64
open Spike.Test.LowerInv (mainCtx ret0Res)
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.A64.Flow.Ret0.Inst (okPc ph labT)

/-- The return address: after `scc_rt_main`'s `bl wc_main`. -/
abbrev raT : Int64 := labT ".L1_scc_rt_main.0_entry" + 4

/- The body's blocks: three, at offsets 0 (the add), its store, the return. -/
#guard (bodyBlks mainCtx 0 ret0Res.insts ret0Res.ret).length == 3

/- The hand placement's tables: the body passes. -/
#guard bodyPhOk okPc ph (fun _ => false) labT mainCtx ".L18_wc_main.0_entry" ret0Res.insts ret0Res.ret raT

/- No pc allowed: the body fails. -/
#guard !bodyPhOk (fun _ => false) ph (fun _ => false) labT mainCtx ".L18_wc_main.0_entry" ret0Res.insts
  ret0Res.ret raT

/- A phase table moving the body's pcs (`+ 1` everywhere off the body's
label): the body's blocks leave their phase and fail. -/
#guard !bodyPhOk okPc (fun pc => if pc == (labT ".L18_wc_main.0_entry").toBitVec.toNat then ph pc else ph pc + 1)
  (fun _ => false) labT mainCtx ".L18_wc_main.0_entry" ret0Res.insts ret0Res.ret raT

/- A return into `scc_rt_stack_take` (phase 12, the stack not taken):
the return block's target leaves the body's phase 0 and fails. -/
#guard ph 4195700 == 12 && ph (labT ".L18_wc_main.0_entry").toBitVec.toNat == 0
#guard !bodyPhOk okPc ph (fun _ => false) labT mainCtx ".L18_wc_main.0_entry" ret0Res.insts ret0Res.ret
  (Int64.ofNat 4195700)

/- The same return target declared dead: it passes again. -/
#guard bodyPhOk okPc ph (· == 4195700) labT mainCtx ".L18_wc_main.0_entry" ret0Res.insts ret0Res.ret
  (Int64.ofNat 4195700)

/-- Soundness: every block of the body passes `blkPh` at its pc. -/
example (h : bodyPhOk okPc ph (fun _ => false) labT mainCtx ".L18_wc_main.0_entry" ret0Res.insts ret0Res.ret
    raT = true) : ∀ x ∈ bodyBlks mainCtx 0 ret0Res.insts ret0Res.ret,
    blkPh okPc ph (fun _ => false) labT (labT ".L18_wc_main.0_entry" + Int64.ofNat (4 * x.1)) raT x.2 = true :=
  fun x hx => blkPh_of_inBody ⟨x.1, rfl, hx⟩ h

/-- `BodyW0` is satisfiable: at `A64Consumer.c0` (`Quiet`) with `SFacts`
at `c0` it holds. -/
example {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {own : Spike.Lib.A64Consumer.Own} {rS : Scc.Sem.Range}
    {Tk : Kraken.Promising.AArch64.State → Prop} {lbl : Spike.Lib.A64Consumer.Lbl}
    {s : Kraken.Promising.AArch64.State}
    (h : Spike.Lib.A64Consumer.SFacts Λ μ own rS Tk lbl s Spike.Lib.A64Consumer.c0) :
    BodyW0 Λ μ own rS Tk lbl Spike.Lib.A64Consumer.c0 s Spike.Lib.A64Consumer.c0 :=
  ⟨Spike.Lib.SegLagTest.quiet_of (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp), h⟩

/-- `hQ` at `ret0.w`: its controls from the consumer's start are `Quiet`. -/
example : ∀ c, Spike.Lib.LocalRun Spike.Lib.Ret0Src.ret0Src Spike.Lib.A64Consumer.c0 c → Spike.Lib.Quiet c :=
  quiet_c0 (Spike.Test.LowerInv.ret0Src_eq ▸ Spike.Test.LowerInv.main0_accepted)

/-- A body with a load is not `body0`: `quiet_run`'s premise rejects it. -/
example : Scc.Lower.body0 [] (.let_ "x" (.load true (.var "u")) (.ret (.var "x"))) = false := by decide

end Spike.Test.LowerA64BodyW
