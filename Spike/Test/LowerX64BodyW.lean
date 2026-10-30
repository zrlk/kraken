import Spike.Lib.LowerX64.BodyW
import Spike.Lib.X64Ret0I
import Spike.Test.LowerX64Ret0Oracle
import Spike.Test.LowerInvBodyX64
import Spike.Test.SegLag

/-!
# `bodyPhOk` at `ret0.w`'s `main` (x86-64)

The twin of `Spike/Test/LowerA64BodyW.lean`. The body's three blocks (the
checked add, its store, the return) pass the phase check at the hand
placement's tables (`Ret0.Inst.okPc`, `ph`, `labT`), the return's target
past `scc_rt_main`'s `call wc_main` (5 bytes); with no pc allowed, with the
phases moved, or with a return target in another phase, they fail.
`blkPh_of_inBody` then gives each block's `blkPh`; `BodyW0` is satisfiable;
`hQ` holds at `ret0.w`.
-/

namespace Spike.Test.LowerX64BodyW

open Spike.Lib.LowerX64
open Spike.Test.LowerInvX64 (mainFr)
open Spike.Test.LowerX64Ret0Oracle (ret0Res)
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.X64.Flow.Ret0.Inst (okPc ph labT)

/-- The return address: after `scc_rt_main`'s `call wc_main`, the label
`.Lscc_rt_main.x2`. -/
abbrev raT : Int64 := labT ".Lscc_rt_main.entry" + 5

#guard raT == labT ".Lscc_rt_main.x2"

/- The body's blocks: three, at byte offsets 0 (the add), 19 (its store),
23 (the return). -/
#guard (bodyBlks SccCode.ret0Cells mainFr ".Lwc_main.entry" 0 ret0Res.insts ret0Res.ret).map (·.1) == [0, 19, 23]

/- The hand placement's tables: the body passes. -/
#guard bodyPhOk okPc ph (fun _ => false) labT SccCode.ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts
  ret0Res.ret raT

/- No pc allowed: the body fails. -/
#guard !bodyPhOk (fun _ => false) ph (fun _ => false) labT SccCode.ret0Cells mainFr ".Lwc_main.entry"
  ret0Res.insts ret0Res.ret raT

/- A phase table moving the body's pcs (`+ 1` everywhere off the body's
label): the body's blocks leave their phase and fail. -/
#guard !bodyPhOk okPc (fun pc => if pc == (labT ".Lwc_main.entry").toBitVec.toNat then ph pc else ph pc + 1)
  (fun _ => false) labT SccCode.ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts ret0Res.ret raT

/- A return into `scc_rt_stack_take` (phase 12, the stack not taken):
the return block's target leaves the body's phase 0 and fails. -/
#guard ph 4195700 == 12 && ph (labT ".Lwc_main.entry").toBitVec.toNat == 0
#guard !bodyPhOk okPc ph (fun _ => false) labT SccCode.ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts
  ret0Res.ret (Int64.ofNat 4195700)

/- The same return target declared dead: it passes again. -/
#guard bodyPhOk okPc ph (· == 4195700) labT SccCode.ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts
  ret0Res.ret (Int64.ofNat 4195700)

/-- Soundness: every block of the body passes `blkPh` at its pc. -/
example (h : bodyPhOk okPc ph (fun _ => false) labT SccCode.ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts
    ret0Res.ret raT = true) : ∀ x ∈ bodyBlks SccCode.ret0Cells mainFr ".Lwc_main.entry" 0 ret0Res.insts ret0Res.ret,
    blkPh okPc ph (fun _ => false) labT (labT ".Lwc_main.entry" + Int64.ofNat x.1) raT x.2 = true :=
  fun x hx => blkPh_of_inBody ⟨x.1, rfl, hx⟩ h

/-- `bodyIn` holds at `ret0.w`'s listing, so `mem_bodyBlks`,
`okBlk_bodyBlks` and `blockAt_of_bodyBlks` apply to its blocks. -/
example : bodyIn SccCode.ret0Cells mainFr ".Lwc_main.entry" 0 ret0Res.insts ret0Res.ret = true := by
  decide +kernel

/-- `BodyW0` is satisfiable: at `X64Consumer.c0` (`Quiet`) with `SFacts`
at `c0` it holds. -/
example {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {own : Spike.Lib.X64Consumer.Own} {rS : Scc.Sem.Range}
    {Tk : Kraken.Promising.X64.State → Prop} {lbl : Spike.Lib.X64Consumer.Lbl}
    {s : Kraken.Promising.X64.State}
    (h : Spike.Lib.X64Consumer.SFacts Λ μ own rS Tk lbl s Spike.Lib.X64Consumer.c0) :
    BodyW0 Λ μ own rS Tk lbl Spike.Lib.X64Consumer.c0 s Spike.Lib.X64Consumer.c0 :=
  ⟨Spike.Lib.SegLagTest.quiet_of (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp), h⟩

/-- `hC0` at the consumer's start. -/
example {Λ : Scc.Sem.Layout} {lbl : Spike.Lib.X64Consumer.Lbl} :
    Spike.Lib.X64Consumer.CFacts Λ lbl Spike.Lib.X64Consumer.c0 :=
  Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0

/-- `hQ` at `ret0.w`: its controls from the consumer's start are `Quiet`. -/
example : ∀ c, Spike.Lib.LocalRun Spike.Lib.Ret0Src.ret0Src Spike.Lib.X64Consumer.c0 c → Spike.Lib.Quiet c :=
  quiet_c0 (Spike.Test.LowerInvBodyX64.ret0Src_eq ▸ Spike.Test.LowerInvBodyX64.main0_accepted)

end Spike.Test.LowerX64BodyW
