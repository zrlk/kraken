/-
**The overflow stub's write tail at `ret0`** (`Spike/Lib/LowerX64/OvfDt.lean`):
`tailNoFul_ovf` and `ovfDt_noSite` at `ret0.x`'s instance (`ret0_instOk`,
`Spike/Test/X64RtW.lean`), with the program's abort code and the path's
phase check decided; `ovfDt_of_at`'s premise holds at a concrete state on the
entry stack (`ret0_sys_at`); the tail is inhabited at each later position; a
state at the `write` with `%rax ≠ 1`, and one past the exit call, are not in
it. The twin of `Spike/Test/LowerA64OvfDt.lean`.
-/
import Spike.Lib.LowerX64.OvfDt
import Spike.Test.LowerX64AbortCall
import Spike.Lib.X64Ret0Correct

namespace Spike.Lib.LowerX64.OvfDtTest

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0.Inst (labT μ0 okPc ph own Tk Kr)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0End)
open Spike.Lib.X64.Flow.Ret0.Correct (ret0S0 R0 stack_word)
open Spike.Lib.X64Consumer (WrIn Inv TailNoFul)
open Spike.Test.LowerX64AbortCall (labT_labR ret0_hprog ret0_hphs)
open SccCode (ret0Cells)

/-- The exit call's pc at `ret0`. -/
theorem ret0_exit : (labT Abort.overflow.exit).toBitVec.toNat = 4198555 := by
  rw [labT_labR]; exact Spike.Lib.X64.StubW.Test.ret0_exit

theorem ret0_hrel : ∀ a, μ0.site .release = some a → (labT Abort.overflow.exit).toBitVec.toNat ≠ a := by
  rw [ret0_exit]; intro a h; cases h; decide

theorem ret0_htk : ∀ a, μ0.site .take = some a → (labT Abort.overflow.exit).toBitVec.toNat ≠ a := by
  rw [ret0_exit]; intro a h; cases h; decide

/-- **The tail is off the transfer sites at `ret0`.** -/
theorem ret0_noSite {rS : Range} :
    ∀ s, OvfDt ret0Exe ret0End labT s → Scc.Sem.Kernel.siteAt Scc.Sem.X64.abi μ0 s = none :=
  ovfDt_noSite (Spike.Lib.X64.Rt.Test.ret0_instOk (rS := rS)) ret0_hphs ret0_hrel ret0_htk

/-- **The consumer's closed tail at `ret0`**, from `WrIn`. -/
theorem ret0_tail {rS : Range} {I : Inv} {Λ : Scc.Sem.Layout} {rS' : Range} {Tk' : State → Prop}
    (hW : WrIn I (OvfDt ret0Exe ret0End labT)) : TailNoFul I Λ rS' Tk' μ0 (OvfDt ret0Exe ret0End labT) :=
  tailNoFul_ovf (Spike.Lib.X64.Rt.Test.ret0_instOk (rS := rS)) ret0_hprog ret0_hphs ret0_hrel ret0_htk hW

/-- info: 'Spike.Lib.LowerX64.OvfDtTest.ret0_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ret0_tail

/-- A state of `ret0`'s executable at `pc` with machine data `m`. -/
def at0 (m : MachineData) (pc : Int64) : State := { ret0S0 with st := (m, pc) }

set_option maxRecDepth 100000

/-- The tail's pcs at `ret0`. -/
theorem ret0_pcs :
    (Abort.pcSys labT Abort.overflow).toBitVec.toNat = 4198537 ∧
    (labT Abort.overflow.entry + 36).toBitVec.toNat = 4198539 ∧
    (labT Abort.overflow.entry + 40).toBitVec.toNat = 4198543 ∧
    (labT Abort.overflow.entry + 47).toBitVec.toNat = 4198550 := by
  rw [labT_labR]; decide +kernel

/-- **Satisfiable**: the tail holds at the two moves and at the exit call. -/
example (m : MachineData) : OvfDt ret0Exe ret0End labT (at0 m (labT Abort.overflow.entry + 40)) :=
  ⟨rfl, Scc.Cert.Link.X64.endPc_threadAt _ _ _ _ (Scc.Cert.Link.X64.above_of_loadOk SccCode.ret0Λ_load), .inr (.inr (.inl rfl))⟩

example (m : MachineData) : OvfDt ret0Exe ret0End labT (at0 m (labT Abort.overflow.entry + 47)) :=
  ⟨rfl, Scc.Cert.Link.X64.endPc_threadAt _ _ _ _ (Scc.Cert.Link.X64.above_of_loadOk SccCode.ret0Λ_load), .inr (.inr (.inr (.inl rfl)))⟩

example (m : MachineData) (h : m.regs.get64 .rax = 231) :
    OvfDt ret0Exe ret0End labT (at0 m (labT Abort.overflow.exit)) :=
  ⟨rfl, Scc.Cert.Link.X64.endPc_threadAt _ _ _ _ (Scc.Cert.Link.X64.above_of_loadOk SccCode.ret0Λ_load), .inr (.inr (.inr (.inr ⟨rfl, h⟩)))⟩

/-- The stub's frame on `ret0`'s entry stack: `[-24, 16)` from 32 bytes
below the entry stack's top. -/
def Rs : Region := ⟨R0.addr (-32), -24, 16⟩

/-- A word of the stub's frame reads. -/
theorem rs_word {k : Int} (hk : Rs.Off k) : (Mem.loadInt Scc.Sem.Entry.linux.stackMem (Rs.addr k) 8).isSome := by
  obtain ⟨h8, hlo, hhi⟩ := hk
  simp only [Rs] at hlo hhi
  have he : Rs.addr k = R0.addr (-32 + k) := by
    simp only [Rs, Region.addr, BitVec.ofInt_add, BitVec.add_assoc]
  rw [he]
  exact stack_word ⟨by omega, by simp only [R0]; omega, by simp only [R0]; omega⟩

/-- The machine data at the stub's `write` on `ret0`'s entry stack:
`%rax = 1`, `%rdi = 2`, `%rbp` the frame's base and `%rsp` 32 bytes below. -/
def mSys : MachineData :=
  { ret0S0.st.1 with
    regs := { ret0S0.st.1.regs with
      rax := 1, rdi := 2, rbp := UInt64.ofBitVec (Rs.addr 0), rsp := UInt64.ofBitVec (Rs.addr (-32)) } }

/-- **`ovfDt_of_at`'s premise is satisfiable at `ret0`**: the stub's `write`
node holds at `mSys` in the frame `Rs`, so the state is in the tail. -/
theorem ret0_sys_at :
    At ret0Exe ret0End Rs (fun _ => True) (Abort.N labT Abort.overflow Spike.Lib.X64Consumer.c0 .sys)
      (at0 mSys (Abort.pcSys labT Abort.overflow)) Spike.Lib.X64Consumer.c0 := by
  refine ⟨rfl, Scc.Cert.Link.X64.endPc_threadAt _ _ _ _ (Scc.Cert.Link.X64.above_of_loadOk SccCode.ret0Λ_load), rfl, rfl, ⟨mSys.regs, mSys.zmms, mSys.status, fun k =>
    BitVec.ofInt 64 ((Mem.loadInt mSys.dmem (Rs.addr k) 8).getD 0)⟩,
    ⟨rfl, rfl, rfl, ?_, ?_⟩, trivial, rfl, rfl, rfl⟩
  · intro r k hr
    cases r <;> simp [Abort.N, Abort.oI, SO.get, lk] at hr <;> subst hr <;> rfl
  · intro k hk
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (rs_word hk)
    exact ⟨j, hj, by show _ = BitVec.ofInt 64 ((Mem.loadInt Scc.Sem.Entry.linux.stackMem _ 8).getD 0); rw [hj]; rfl⟩

example : OvfDt ret0Exe ret0End labT (at0 mSys (Abort.pcSys labT Abort.overflow)) :=
  ovfDt_of_at (by decide) (by decide) ret0_sys_at

/-- **Negative**: at the `write` with `%rax ≠ 1`, the state is not in the tail. -/
example (m : MachineData) (ha : m.regs.get64 .rax ≠ 1) :
    ¬ OvfDt ret0Exe ret0End labT (at0 m (Abort.pcSys labT Abort.overflow)) := by
  have hp := ret0_pcs
  have hx := ret0_exit
  rintro ⟨-, -, ⟨-, h, -⟩ | ⟨h, -⟩ | h | h | ⟨h, -⟩⟩
  · exact ha h
  all_goals
    have := congrArg (fun p : Int64 => p.toBitVec.toNat) h
    simp only [at0] at this
    omega

/-- **Negative**: past the exit call no state is in the tail. -/
example (m : MachineData) : ¬ OvfDt ret0Exe ret0End labT (at0 m (labT Abort.overflow.exit + 2)) := by
  have hp := ret0_pcs
  have hx : (labT Abort.overflow.exit + 2).toBitVec.toNat = 4198557 := by rw [labT_labR]; decide +kernel
  have hx' := ret0_exit
  rintro ⟨-, -, ⟨h, -⟩ | ⟨h, -⟩ | h | h | ⟨h, -⟩⟩
  all_goals
    have := congrArg (fun p : Int64 => p.toBitVec.toNat) h
    simp only [at0] at this
    omega

end Spike.Lib.LowerX64.OvfDtTest
