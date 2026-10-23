/-
**The overflow stub's write tail at `ret0`** (`Spike/Lib/LowerA64/OvfDt.lean`):
`tailNoFul_ovf` and `ovfDt_noSite` at `ret0.w`'s instance (`ret0_instOk`,
`Spike/Test/A64RtW.lean`), with the program's abort code and the path's
phase check decided; `ovfDt_of_at`'s premise holds at a concrete state on the
entry stack (`ret0_svc_at`); the tail is inhabited at each later position; a state
at the `write` with `x8 ≠ 64`, and one past the exit call, are not in it.
-/
import Spike.Lib.LowerA64.OvfDt
import Spike.Test.A64RtW
import Spike.Test.A64StubW
import Spike.Lib.A64Ret0Correct

namespace Spike.Lib.LowerA64.OvfDtTest

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Spike.Lib.A64 Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0.Inst (labT μ0 okPc ph)
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End)
open Spike.Lib.A64Consumer (WrIn Inv TailNoFul)
open SccCode (ret0Prog)

/-- `ret0`'s hand labels are the test labels of `Spike/Test/A64StubW.lean`. -/
theorem labT_eq : labT = StubW.Test.labR :=
  Spike.Lib.A64.Flow.Ret0.Inst.ret0_labT.symm.trans StubW.Test.ret0_labR

/-- The abort path's phase check at `ret0`'s hand tables and labels. -/
theorem ret0_phs : StubW.abortPhOk okPc ph labT = true := labT_eq ▸ StubW.Test.ret0_abortPhOk_hand

/-- `ret0`'s abort code. -/
theorem ret0_abortIn : Scc.Cert.Rt.A64.Abort.abortIn ret0Prog = true := by decide +kernel

/-- The exit call's pc at `ret0`. -/
theorem ret0_exit : (labT Abort.overflow.exit).toBitVec.toNat = 4198508 := labT_eq ▸ StubW.Test.ret0_exit

theorem ret0_hrel : ∀ a, μ0.site .release = some a → (labT Abort.overflow.exit).toBitVec.toNat ≠ a := by
  rw [ret0_exit]; intro a h; cases h; decide

theorem ret0_htk : ∀ a, μ0.site .take = some a → (labT Abort.overflow.exit).toBitVec.toNat ≠ a := by
  rw [ret0_exit]; intro a h; cases h; decide

/-- **The tail is off the transfer sites at `ret0`.** -/
theorem ret0_noSite {rS : Range} :
    ∀ s, OvfDt ret0Exe ret0End labT s → Scc.Sem.Kernel.siteAt Scc.Sem.A64.abi μ0 s = none :=
  ovfDt_noSite (Spike.Lib.A64.Rt.Test.ret0_instOk (rS := rS)) ret0_phs ret0_hrel ret0_htk

/-- **The consumer's closed tail at `ret0`**, from `WrIn`. -/
theorem ret0_tail {rS : Range} {I : Inv} {Λ : Scc.Sem.Layout} {rS' : Range} {Tk : State → Prop}
    (hW : WrIn I (OvfDt ret0Exe ret0End labT)) : TailNoFul I Λ rS' Tk μ0 (OvfDt ret0Exe ret0End labT) :=
  tailNoFul_ovf (Spike.Lib.A64.Rt.Test.ret0_instOk (rS := rS)) ret0_abortIn ret0_phs ret0_hrel ret0_htk hW

/-- info: 'Spike.Lib.LowerA64.OvfDtTest.ret0_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ret0_tail

/-- A state of `ret0`'s executable at `pc` with machine data `m`. -/
def at0 (m : MachineData) (pc : Int64) : State :=
  { (Scc.Sem.A64.threadAt Scc.Sem.Entry.linux SccCode.ret0Λ.code.lo ret0Prog
      (Scc.Sem.loadSyms SccCode.ret0Λ SccCode.ret0Secs.rodata)) with st := (m, pc) }

set_option maxRecDepth 100000

/-- **Satisfiable**: the tail holds at the two `movz` and at the exit call. -/
example (m : MachineData) : OvfDt ret0Exe ret0End labT (at0 m (Abort.pcSvc labT Abort.overflow + 4 + 4)) :=
  ⟨rfl, Scc.Cert.Rt.A64.endPc_threadAt _ _ _ _ (Scc.Cert.Link.A64.above_of_loadOk SccCode.ret0Λ_load), .inr (.inr (.inl rfl))⟩

example (m : MachineData) : OvfDt ret0Exe ret0End labT (at0 m (Abort.pcSvc labT Abort.overflow + 4 + 4 + 4)) :=
  ⟨rfl, Scc.Cert.Rt.A64.endPc_threadAt _ _ _ _ (Scc.Cert.Link.A64.above_of_loadOk SccCode.ret0Λ_load), .inr (.inr (.inr (.inl rfl)))⟩

example (m : MachineData) (h8 : m.regs.X8 = 94) : OvfDt ret0Exe ret0End labT (at0 m (labT Abort.overflow.exit)) :=
  ⟨rfl, Scc.Cert.Rt.A64.endPc_threadAt _ _ _ _ (Scc.Cert.Link.A64.above_of_loadOk SccCode.ret0Λ_load), .inr (.inr (.inr (.inr ⟨rfl, h8⟩)))⟩

/-- The machine data at the stub's `write` on `ret0`'s entry stack: `x0 = 2`,
`x8 = 64`, `sp` 48 bytes below the entry stack's top. -/
def mSvc : MachineData :=
  { Spike.Lib.A64.Flow.Ret0.Correct.ret0S0.st.1 with
    regs := { Spike.Lib.A64.Flow.Ret0.Correct.ret0S0.st.1.regs with
      X0 := 2, X8 := 64, SP := UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.Correct.R0.addr (-48)) } }

/-- **`ovfDt_of_at`'s premise is satisfiable at `ret0`**: the stub's `write`
node holds at `mSvc` in the entry region, so the state is in the tail. -/
theorem ret0_svc_at :
    At ret0Exe ret0End Spike.Lib.A64.Flow.Ret0.Correct.R0 (fun _ => True)
      (Abort.N labT Abort.overflow Spike.Lib.A64Consumer.c0 .svc) (at0 mSvc (Abort.pcSvc labT Abort.overflow))
      Spike.Lib.A64Consumer.c0 := by
  refine ⟨rfl, Scc.Cert.Rt.A64.endPc_threadAt _ _ _ _ (Scc.Cert.Link.A64.above_of_loadOk SccCode.ret0Λ_load), rfl, rfl, ⟨mSvc.regs, mSvc.status, fun k =>
    BitVec.ofInt 64 ((Mem.loadInt mSvc.dmem (Spike.Lib.A64.Flow.Ret0.Correct.R0.addr k) 8).getD 0)⟩,
    ⟨rfl, rfl, ?_, ?_⟩, trivial, rfl, rfl, rfl⟩
  · intro r k hr
    rcases r with x | _
    · simp [Abort.N, Abort.oI, SO.get, lk] at hr
    · simp only [Abort.N, SO.get, Option.some.injEq] at hr
      subst hr
      rfl
  · intro k hk
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (Spike.Lib.A64.Flow.Ret0.Correct.stack_word hk)
    exact ⟨j, hj, by show _ = BitVec.ofInt 64 ((Mem.loadInt Scc.Sem.Entry.linux.stackMem _ 8).getD 0); rw [hj]; rfl⟩

example : OvfDt ret0Exe ret0End labT (at0 mSvc (Abort.pcSvc labT Abort.overflow)) :=
  ovfDt_of_at Spike.Lib.A64.Flow.Ret0.Inst.entryR_al (by decide) (by decide) ret0_svc_at

/-- The tail's pcs at `ret0` are pairwise distinct. -/
theorem ret0_pcs :
    (Abort.pcSvc labT Abort.overflow).toBitVec.toNat = 4198492 ∧
    (Abort.pcSvc labT Abort.overflow + 4).toBitVec.toNat = 4198496 ∧
    (Abort.pcSvc labT Abort.overflow + 4 + 4).toBitVec.toNat = 4198500 ∧
    (Abort.pcSvc labT Abort.overflow + 4 + 4 + 4).toBitVec.toNat = 4198504 := by
  rw [labT_eq]; decide +kernel

/-- **Negative**: at the `write` with `x8 ≠ 64`, the state is not in the tail. -/
example (m : MachineData) (h8 : m.regs.X8 ≠ 64) :
    ¬ OvfDt ret0Exe ret0End labT (at0 m (Abort.pcSvc labT Abort.overflow)) := by
  have hp := ret0_pcs
  have hx := ret0_exit
  rintro ⟨-, -, ⟨-, -, h, -⟩ | ⟨h, -⟩ | h | h | ⟨h, -⟩⟩
  · exact h8 h
  all_goals
    have := congrArg (fun p : Int64 => p.toBitVec.toNat) h
    simp only [at0] at this
    omega

/-- **Negative**: past the exit call no state is in the tail. -/
example (m : MachineData) : ¬ OvfDt ret0Exe ret0End labT (at0 m (labT Abort.overflow.exit + 4)) := by
  have hp := ret0_pcs
  have hx : (labT Abort.overflow.exit + 4).toBitVec.toNat = 4198512 := by rw [labT_eq]; decide +kernel
  have hx' := ret0_exit
  rintro ⟨-, -, ⟨h, -⟩ | ⟨h, -⟩ | h | h | ⟨h, -⟩⟩
  all_goals
    have := congrArg (fun p : Int64 => p.toBitVec.toNat) h
    simp only [at0] at this
    omega

end Spike.Lib.LowerA64.OvfDtTest
