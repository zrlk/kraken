import Spike.Lib.LowerX64.StartU
import Spike.Test.LowerX64AbortCall

/-!
# `swUW_gen_dt` with `userCallW_sw` at `ret0` (x86-64)

`ret0.x`'s switch and `scc_rt_main` with `ret0.w`'s lowered `main` as the
user function, inside `SFacts … WrT` (the overflow stub's write states), at
the closed depth `swL mainFr.size = 120` and the user's `D = 64`
(`swL_ok`): the interface `SwUW` with only the memory side's premises and
the immediates left. `swL_ok`'s bound holds at the largest `MainSeg` frame
(`4096`) and fails past the stack. `uPost_exit` is `startU_segW`'s
`hexit` at the placement's memory side.
-/

namespace Spike.Test.LowerX64StartU

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib Spike.Lib.X64 Spike.Lib.LowerX64
open Spike.Lib.X64Consumer (SFacts)
open Spike.Lib.X64.Rt (SwUW)
open Spike.Lib.X64.Rt.Test (ret0_instOk ret0_mainPh ret0_swPh ret0_limMapped)
open Spike.Lib.X64.Rt (ret0MC ret0_mainUIn)
open Spike.Lib.X64.Flow.Ret0 (StackM tpOf)
open Spike.Lib.X64.Flow.Ret0.Inst (okPc ph labT μ0 own Tk Kr cfacts_c0)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0End)
open Spike.Test.LowerInvX64 (mainFr)
open Spike.Test.LowerX64Construct (mainFr_ok mainFr_small)
open Spike.Test.LowerX64Ret0Oracle (main0 ret0Res ret0_lower0 ret0_proInC ret0_bodyIn mainFr_size)
open Spike.Test.LowerX64MainSeg (main0_accepted)
open Spike.Test.LowerX64UserCall (ret0_bodyPh ret0_proPhFr)
open Spike.Test.LowerX64AbortCall (WrT ret0_hblk ret0_hphA ret0_hprog ret0_hphs)
open SccCode (ret0Λ ret0Cells)

/-- `swL` at `main`'s frame. -/
example : swL mainFr.size = 120 := by rw [mainFr_size]; rfl

/-- **Oracle**: `swL_ok` at the largest `MainSeg` frame. -/
example : swL 4096 ≤ 16384 := (swL_ok (n := 4096) (by decide) (by decide)).2.2.2.1

/-- **Negative**: a frame of a whole stack does not fit. -/
example : ¬ (swL 16384 ≤ 16384) := by decide

variable {rS : Range} {ms : MemSide isa}

/-- **`ret0`'s switch and `scc_rt_main` with the lowered `main`, the
overflow abort discharged** (`swUW_gen_dt` with `userCallW_sw`), at the
closed depth `swL mainFr.size`. -/
example {R : Region} {F : MachineData → Prop} {top : BitVec 64} (h8 : top.toNat % 8 = 0)
    (hok : (swR top (-swL mainFr.size) 0).OK) (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (himm : ret0Λ.imms = Spike.Lib.LowerNode.immsOf main0)
    (hKex : ∀ s s', Scc.Sem.X64.pcOf s = (labT Abort.overflow.exit).toBitVec.toNat → ¬ Kr rS s s')
    (hms : ∀ s : State, s.exe = ret0Exe → s.st.2 = labT Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi) :
    SwUW (fun s c => SFacts ret0Λ μ0 own rS Tk ret0Λ.static s c WrT) (Kr rS) [main0] ret0Λ.static ret0Exe ret0End
      R (fun m => F m ∧ StackM rS m) ms rS 134217736#64 top Spike.Lib.X64Consumer.c0 (swL mainFr.size) ret0MC
      (mainFr.size + 48) (Int64.ofInt mainFr.size) (UPost [main0] ret0Λ.static Spike.Lib.X64Consumer.c0) := by
  have hfr := mainFr_size
  have hL := swL_ok (n := mainFr.size) (by omega) (by omega)
  have hZ : ret0MC.Z.toInt = 32 := by decide
  have hZb : Spike.Lib.X64.Rt.bareMC.Z.toInt = 32 := by decide
  have hex : (labT Abort.overflow.exit).toBitVec.toNat = 4198555 := by
    rw [Spike.Test.LowerX64AbortCall.labT_labR]; exact Spike.Lib.X64.StubW.Test.ret0_exit
  have hph : bodyPhOk okPc ph (fun _ => false) labT ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts ret0Res.ret
      (Int64.ofBitVec ((_root_.Executable.labels ret0Exe).label ret0MC.sp0).toBitVec) = true := by
    rw [Spike.Lib.X64.Flow.Ret0.Inst.ret0_labT]; exact ret0_bodyPh
  exact swUW_gen_dt ret0_instOk Flow.Ret0.ret0_startTailIn ret0_mainUIn cfacts_c0 (fun _ _ h => h.1 ▸ cfacts_c0)
    ret0_mainPh ret0_swPh h8 hok (by omega) hL.2.1 (by decide) (by decide) (by decide) (by decide)
    ret0_limMapped hsub hfit
    (userCallW_sw main0_accepted mainFr_ok mainFr_small ret0_proInC ret0_lower0 ret0_bodyIn ret0_instOk
      (by omega) hL.2.2.2.2 h8 hok (by omega) hL.2.1 (by decide) (by decide) hph ret0_proPhFr cfacts_c0
      ret0_limMapped hsub hfit (fun _ => ⟨ret0_hblk, ret0_hphA⟩) ret0_hprog Spike.Lib.X64.StubW.Test.ret0_sysIn
      ret0_hphs himm
      (fun a h => by rw [hex]; cases h; decide) (fun a h => by rw [hex]; cases h; decide)
      (fun k a h e => by rw [hex] at e; subst e; cases k <;> simp [μ0] at h ⊢) hKex hms hK
      (fun R' F' _ _ c s c' h => ⟨R', F', c, c', h⟩))

end Spike.Test.LowerX64StartU
