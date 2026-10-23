import Spike.Lib.LowerX64.AbortCall
import Spike.Test.LowerX64UserCall
import Spike.Test.X64StubW

/-!
# `hab_of`'s premises and `userCallW_main` at `ret0.w`'s `main` (x86-64)

`main`'s `.ovf` block is `Abort.Local.lb` in `ret0`'s cells (`hblk`), passes
its phase check at the hand tables (`hphA`), the cells have the abort code
and the stub's `write` call (`hprog`, `hsysIn`) and the abort path passes
its phase check there (`hphs`); the block has no `ret`. A pc table
excluding the block's call, or a phase table moving its call target, fails
the check; `lb` is not at another label. `frame_mod8` at `main`'s frame.
With them, `userCallW_main` gives `ret0`'s `main` as `scc_rt_main`'s user
function at the switch's top with the overflow abort discharged (the
memory side's abort facts, the write tail and the immediates premises).
-/

namespace Spike.Test.LowerX64AbortCall

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib Spike.Lib.X64 Spike.Lib.LowerX64
open Spike.Lib.X64Consumer (CFacts SFacts blkPh noRetBlk)
open Spike.Lib.X64.Rt (UserCallW stackOff_callee swFSL)
open Spike.Lib.X64.Rt.Test (ret0_instOk ret0_limMapped)
open Spike.Lib.X64.Rt (ret0MC)
open Spike.Lib.X64.Flow.Ret0 (CallerCells limA tpOf)
open Spike.Lib.X64.Flow.Ret0.Inst (okPc ph labT μ0 own Tk Kr cfacts_c0)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0End)
open Spike.Lib.X64.StubW (abortPhOk)
open Spike.Lib.X64.StubW.Test (labR ret0_labR)
open Spike.Test.LowerInvX64 (mainFr)
open Spike.Test.LowerX64Construct (mainFr_ok mainFr_small)
open Spike.Test.LowerX64Ret0Oracle (main0 ret0Res ret0_lower0 ret0_proInC ret0_bodyIn mainFr_size)
open Spike.Test.LowerX64MainSeg (main0_accepted)
open Spike.Test.LowerX64UserCall (ret0_bodyPh ret0_proPhFr mR uR)
open SccCode (ret0Λ ret0Cells)

/-- **`hblk` at `ret0`**: `main`'s `.ovf` block is the checked `ovfBlk` (`= lb`). -/
theorem ret0_hblk : Scc.Cert.Rt.X64.blockAtB ret0Cells (ovfL mainFr) 0 ovfBlk = true := by
  decide +kernel

/-- `labT` and `labR` are both the executable's labels. -/
theorem labT_labR : labT = labR := by
  rw [← Spike.Lib.X64.Flow.Ret0.Inst.ret0_labT, ret0_labR]

/-- **`hphA` at `ret0`**, on the hand tables. -/
theorem ret0_hphA : blkPh okPc ph (fun _ => false) labT (labT (ovfL mainFr) + Int64.ofNat 0) 0
    Abort.Local.lb = true := by
  rw [labT_labR]; decide +kernel

/-- **`hprog` at `ret0`.** -/
theorem ret0_hprog : Scc.Cert.Rt.X64.Abort.abortIn ret0Cells = true := SccCode.ret0_abort

/-- **`hphs` at `ret0`**, on the hand tables at `labT`. -/
theorem ret0_hphs : abortPhOk okPc ph labT = true := by
  rw [labT_labR]; exact Spike.Lib.X64.StubW.Test.ret0_abortPhOk_hand

/-- The block has no `ret` (`lb_noRet`). -/
example : noRetBlk Abort.Local.lb = true := lb_noRet

/-- No pc allowed: the check fails. -/
example : blkPh (fun _ => false) ph (fun _ => false) labR (labR (ovfL mainFr) + Int64.ofNat 0) 0
    Abort.Local.lb = false := by decide +kernel

/-- A phase table putting `scc_rt_abort` in another phase than the block: the check fails. -/
example : blkPh okPc (fun pc => if pc = (labR "scc_rt_abort").toBitVec.toNat then ph pc + 1 else ph pc)
    (fun _ => false) labR (labR (ovfL mainFr) + Int64.ofNat 0) 0 Abort.Local.lb = false := by decide +kernel

/-- `lb` is not at `main`'s check label. -/
example : Scc.Cert.Rt.X64.blockAtB ret0Cells ".Lwc_main.chk" 0 ovfBlk = false := by decide +kernel

/-- **`frame_mod8` at `main`'s frame** (16), and a cell `rsOf_bounds` gives is inside it. -/
example {r : Scc.IR.Reg} {k : Int} (h : rsOf mainFr r = some k) : -16 ≤ k ∧ k ≤ -8 ∧ mainFr.size % 8 = 0 := by
  have := rsOf_bounds mainFr_ok h
  have := frame_mod8 mainFr_ok
  rw [mainFr_size] at *
  omega

variable {rS : Range} {ms : MemSide isa}

/-- The write tail: a state at the stub's `write` (the weakest `hwr` allows). -/
def WrT (s : State) : Prop :=
  ∃ (R' : Region) (F' : MachineData → Prop) (c c' : Ctl),
    At ret0Exe ret0End R' F' (Abort.N labT Abort.overflow c .sys) s c'

/-- **`ret0`'s lowered `main` is `scc_rt_main`'s user function with its
overflow abort discharged** (`userCallW_main` at the switch's top, the
depth `D = 64 = fr.size + 48`): the remaining premises are the memory
side's (`hKex`, `hms`, `hK`) and the immediates at the abort's source
(`himm`); the write tail is the stub's `write` states (`WrT`). -/
example {top : BitVec 64} (h8 : top.toNat % 8 = 0) (hok : (swR top (-120) 0).OK)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) {F' : MachineData → Prop}
    (hF' : ∀ m, F' m → swFSL 120 rS top (limA (tpOf 134217736#64)) top m ∧
      CallerCells (swR top (-120) 0) (-8 - 0) (8 - 120) 8 m)
    (himm : ret0Λ.imms = Spike.Lib.LowerNode.immsOf main0)
    (hKex : ∀ s s', Scc.Sem.X64.pcOf s = (labT Abort.overflow.exit).toBitVec.toNat → ¬ Kr rS s s')
    (hms : ∀ s : State, s.exe = ret0Exe → s.st.2 = labT Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi) :
    UserCallW (fun s c => SFacts ret0Λ μ0 own rS Tk ret0Λ.static s c WrT) (Kr rS) [main0] ret0Λ.static ms
      ret0Exe ret0End ((swR top (-120) 0).callee (-8 - 0) (8 - 120) 8) F' ret0MC.fn ret0MC.Z 64
      (Int64.ofInt mainFr.size) (UPost [main0] ret0Λ.static Spike.Lib.X64Consumer.c0)
      ((_root_.Executable.labels ret0Exe).label ret0MC.sp0).toBitVec Spike.Lib.X64Consumer.c0
      (tpOf 134217736#64) := by
  have hR : ((swR top (-120) 0).callee (-8 - 0) (8 - 120) 8).OK :=
    Region.callee_ok hok (by show (-120 : Int) ≤ _; decide) (by decide) (by show _ < (0 : Int); decide)
      (by show _ ≤ (0 : Int); decide)
  have hb8 : ((swR top (-120) 0).callee (-8 - 0) (8 - 120) 8).base.toNat % 8 = 0 :=
    addr_toNat_mod8 _ h8 (by decide)
  have hph : bodyPhOk okPc ph (fun _ => false) labT ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts ret0Res.ret
      (Int64.ofBitVec ((_root_.Executable.labels ret0Exe).label ret0MC.sp0).toBitVec) = true := by
    rw [Spike.Lib.X64.Flow.Ret0.Inst.ret0_labT]; exact ret0_bodyPh
  have hex : (labT Abort.overflow.exit).toBitVec.toNat = 4198555 := by
    rw [labT_labR]; exact Spike.Lib.X64.StubW.Test.ret0_exit
  exact userCallW_main main0_accepted mainFr_ok mainFr_small ret0_proInC ret0_lower0 ret0_bodyIn ret0_instOk
    hb8 (by decide) (by rw [mainFr_size]; decide) (by decide) hph ret0_proPhFr cfacts_c0 ret0_limMapped
    (fun _ h => (hF' _ h).1.1.2) hsub hfit
    (fun _ h hc => stackOff_callee hR hb8 (by show (8 - 120 : Int) % 8 = 0; decide)
      (by show (8 : Int) % 8 = 0; decide) (by show (8 - 120 : Int) ≤ _; decide) (by decide)
      (by show _ < (8 : Int); decide) (by decide)
      (stackOff_callee hok h8 (by show (-120 : Int) % 8 = 0; decide) (by show (0 : Int) % 8 = 0; decide)
        (by show (-120 : Int) ≤ _; decide) (by decide) (by show _ < (0 : Int); decide) (by decide)
        (hF' _ h).1.2 (hF' _ h).2) hc)
    (fun _ => ⟨ret0_hblk, ret0_hphA⟩) ret0_hprog Spike.Lib.X64.StubW.Test.ret0_sysIn ret0_hphs himm
    (fun a h => by rw [hex]; cases h; decide) (fun a h => by rw [hex]; cases h; decide)
    (fun k a h e => by rw [hex] at e; subst e; cases k <;> simp [μ0] at h ⊢) hKex hms hK
    (fun R' F' _ _ c s c' h => ⟨R', F', c, c', h⟩)

end Spike.Test.LowerX64AbortCall
