import Spike.Lib.LowerX64.BodyPh
import Spike.Test.LowerX64Ret0Oracle

/-!
# `bodyPhOk` at `ret0.w`'s `main` (x86-64)

The body's three blocks (the add, its store, the return) pass the phase
check in one phase with every pc allowed; with no pc allowed they fail. The
soundness lemma `blkPh_of_inBody` then gives each block's `blkPh`.
-/

namespace Spike.Test.LowerX64BodyPh

open Spike.Lib.LowerX64
open Spike.Test.LowerInvX64 (mainFr)
open Spike.Test.LowerX64Ret0Oracle (ret0Res)
open Spike.Lib.X64Consumer (blkPh)

/-- The labels at `ret0.w`'s hand placement. -/
abbrev lab : String → Int64 := Spike.Lib.X64.Flow.Ret0.Inst.labT

/-- One phase, every pc allowed: the body passes. -/
theorem ret0_bodyPh : bodyPhOk (fun _ => true) (fun _ => 0) (fun _ => false) lab SccCode.ret0Cells mainFr
    ".Lwc_main.entry" ret0Res.insts ret0Res.ret 0 = true := by
  decide +kernel

/-- No pc allowed: the body fails. -/
example : bodyPhOk (fun _ => false) (fun _ => 0) (fun _ => false) lab SccCode.ret0Cells mainFr
    ".Lwc_main.entry" ret0Res.insts ret0Res.ret 0 = false := by
  decide +kernel

/-- Soundness: every `InBody` block passes `blkPh` at its pc. -/
example : ∀ x ∈ bodyBlks SccCode.ret0Cells mainFr ".Lwc_main.entry" 0 ret0Res.insts ret0Res.ret,
    blkPh (fun _ => true) (fun _ => 0) (fun _ => false) lab (lab ".Lwc_main.entry" + Int64.ofNat x.1) 0 x.2 = true :=
  fun x hx => blkPh_of_inBody ⟨x.1, rfl, hx⟩ ret0_bodyPh

end Spike.Test.LowerX64BodyPh
