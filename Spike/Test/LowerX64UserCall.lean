import Spike.Lib.LowerX64.UserCall
import Spike.Test.X64RtMainU
import Spike.Test.LowerX64MainSeg
import Spike.Test.LowerX64UserW

/-!
# `userCallW_of_fn` as `swUW_gen`'s user function at `ret0` (x86-64)

`ret0.w`'s lowered `main` is the user function of `ret0.x`'s switch: the
interface `SwUW` from the generic `swUW_gen` with its user premise `hU`
discharged by `userCallW_of_fn` at the lowering's facts (`ret0_lower0`,
`ret0_proInC`, `ret0_bodyIn`), the hand instance (`ret0_instOk`) and the
phase facts at the return address `.Lscc_rt_main.x2` (`ret0_bodyPh`,
`ret0_proPh`); the overflow abort `hab` left a premise. The switch's other
stack values than its top are dead (`swF`), so the user function there is
vacuous.
-/

namespace Spike.Test.LowerX64UserCall

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib Spike.Lib.X64 Spike.Lib.LowerX64
open Spike.Lib.X64Consumer (CFacts SFacts)
open Spike.Lib.X64.Rt (SwUW swUW_gen UserCallW stackOff_callee swFSL)
open Spike.Lib.X64.Rt.Test (ret0_instOk ret0_mainPh ret0_swPh ret0_limMapped)
open Spike.Lib.X64.Rt (ret0MC ret0_mainUIn)
open Spike.Lib.X64.Flow.Ret0 (StackM StackOff CallerCells limA tpOf)
open Spike.Lib.X64.Flow.Ret0.Inst (okPc ph labT μ0 own Tk Wr Kr cfacts_c0)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0End)
open Spike.Test.LowerInvX64 (mainFr)
open Spike.Test.LowerX64Construct (mainFr_ok mainFr_small)
open Spike.Test.LowerX64Ret0Oracle (main0 ret0Res ret0_lower0 ret0_proInC ret0_bodyIn mainFr_size)
open Spike.Test.LowerX64MainSeg (main0_accepted)
open Scc.Emit.X64 (labelOf)
open SccCode (ret0Λ ret0Cells)

/-- **The body's phase facts at the return address** `.Lscc_rt_main.x2`. -/
theorem ret0_bodyPh : bodyPhOk okPc ph (fun _ => false) labT ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts
    ret0Res.ret (labT ".Lscc_rt_main.x2") = true := by decide +kernel

/-- **The prologue's phase facts at `main`'s frame.** -/
theorem ret0_proPhFr : ProPh okPc ph labT "wc_main" (labelOf mainFr.fn "chk") (Int64.ofInt mainFr.size)
    (proL mainFr) 5 9 3 2 4 [] := by
  obtain ⟨h1, h2, h3⟩ := Spike.Test.LowerX64UserW.fr_eq
  rw [h1, h2, h3]; exact Spike.Test.LowerX64UserW.ret0_proPh

/-- The region of `scc_rt_main` called from the switch's top. -/
abbrev mR (top : BitVec 64) : Region := (swR top (-80) 0).callee (-8 - 0) (8 - 80) 8

/-- The user function's region inside it. -/
abbrev uR (top : BitVec 64) : Region := (mR top).callee (-8 - ret0MC.Z.toInt - 8 - 0) (-24) 8

variable {rS : Range} {ms : MemSide isa}

/-- **`ret0`'s lowered `main` is `scc_rt_main`'s user function**
(`userCallW_of_fn` at the switch's top), the overflow abort `hab` a
premise. -/
theorem ret0_userCallW {top : BitVec 64} (h8 : top.toNat % 8 = 0) (hok : (swR top (-80) 0).OK)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) {F' : MachineData → Prop}
    (hF' : ∀ m, F' m → swFSL 80 rS top (limA (tpOf 134217736#64)) top m ∧
      CallerCells (swR top (-80) 0) (-8 - 0) (8 - 80) 8 m)
    (hab : ∀ F'' : MachineData → Prop, (uR top).OK → (uR top).base.toNat % 8 = 0 → FStable (uR top) F'' →
      (∀ m, F'' m → F' m ∧ CallerCells (mR top) (-8 - ret0MC.Z.toInt - 8 - 0) (-24) 8 m) →
      ∀ fp ra' : BitVec 64,
      SegW (fun s c => SFacts ret0Λ μ0 own rS Tk ret0Λ.static s c) (Kr rS) [main0] ret0Λ.static ms
        (Lag [main0] (· = Spike.Lib.X64Consumer.c0) (At ret0Exe ret0End (rbR (uR top)) F''
          (abortN (Spike.Lib.LowerNode.immsOf main0) (Spike.Lib.LowerNode.InWalk main0)
            [main0] ret0Λ.static mainFr (_root_.Executable.labels ret0Exe).label fp ra'
            Spike.Lib.X64Consumer.c0)))
        (fun _ _ => False)) :
    UserCallW (fun s c => SFacts ret0Λ μ0 own rS Tk ret0Λ.static s c) (Kr rS) [main0] ret0Λ.static ms ret0Exe
      ret0End (mR top) F' ret0MC.fn ret0MC.Z 24 (Int64.ofInt mainFr.size)
      (UPost [main0] ret0Λ.static Spike.Lib.X64Consumer.c0)
      ((_root_.Executable.labels ret0Exe).label ret0MC.sp0).toBitVec Spike.Lib.X64Consumer.c0 (tpOf 134217736#64) := by
  have hR : (mR top).OK := Region.callee_ok hok (by show (-80 : Int) ≤ _; decide) (by decide)
    (by show _ < (0 : Int); decide) (by show _ ≤ (0 : Int); decide)
  have hb8 : (mR top).base.toNat % 8 = 0 := addr_toNat_mod8 _ h8 (by decide)
  have hph : bodyPhOk okPc ph (fun _ => false) labT ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts ret0Res.ret
      (Int64.ofBitVec ((_root_.Executable.labels ret0Exe).label ret0MC.sp0).toBitVec) = true := by
    rw [Spike.Lib.X64.Flow.Ret0.Inst.ret0_labT]; exact ret0_bodyPh
  exact userCallW_of_fn main0_accepted mainFr_ok mainFr_small ret0_proInC ret0_lower0 ret0_bodyIn ret0_instOk
    hb8 (by decide) (by rw [mainFr_size]; decide) (by decide) hph ret0_proPhFr cfacts_c0 ret0_limMapped
    (fun _ h => (hF' _ h).1.1.2) hsub hfit
    (fun _ h hc => stackOff_callee hR hb8 (by show (8 - 80 : Int) % 8 = 0; decide)
      (by show (8 : Int) % 8 = 0; decide) (by show (8 - 80 : Int) ≤ _; decide) (by decide)
      (by show _ < (8 : Int); decide) (by decide)
      (stackOff_callee hok h8 (by show (-80 : Int) % 8 = 0; decide) (by show (0 : Int) % 8 = 0; decide)
        (by show (-80 : Int) ≤ _; decide) (by decide) (by show _ < (0 : Int); decide) (by decide)
        (hF' _ h).1.2 (hF' _ h).2) hc)
    hab

/-- **`swUW_gen` at `ret0.x` with `ret0.w`'s lowered `main` as the user
function** (`ret0_userCallW`), the post `UPost`, the overflow abort a
premise at every frame condition of the switch's top. -/
example {R : Region} {F : MachineData → Prop} {top : BitVec 64} (h8 : top.toNat % 8 = 0)
    (hok : (swR top (-80) 0).OK) (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hab : ∀ F' F'' : MachineData → Prop, (uR top).OK → (uR top).base.toNat % 8 = 0 → FStable (uR top) F'' →
      (∀ m, F'' m → F' m ∧ CallerCells (mR top) (-8 - ret0MC.Z.toInt - 8 - 0) (-24) 8 m) →
      ∀ fp ra' : BitVec 64,
      SegW (fun s c => SFacts ret0Λ μ0 own rS Tk ret0Λ.static s c) (Kr rS) [main0] ret0Λ.static ms
        (Lag [main0] (· = Spike.Lib.X64Consumer.c0) (At ret0Exe ret0End (rbR (uR top)) F''
          (abortN (Spike.Lib.LowerNode.immsOf main0) (Spike.Lib.LowerNode.InWalk main0)
            [main0] ret0Λ.static mainFr (_root_.Executable.labels ret0Exe).label fp ra'
            Spike.Lib.X64Consumer.c0)))
        (fun _ _ => False)) :
    SwUW (Wr rS) (Kr rS) [main0] ret0Λ.static ret0Exe ret0End R (fun m => F m ∧ StackM rS m) ms rS 134217736#64
      top Spike.Lib.X64Consumer.c0 80 ret0MC 24 (Int64.ofInt mainFr.size)
      (UPost [main0] ret0Λ.static Spike.Lib.X64Consumer.c0) :=
  swUW_gen ret0_instOk Flow.Ret0.ret0_startTailIn ret0_mainUIn cfacts_c0 (fun _ _ h => h.1 ▸ cfacts_c0)
    ret0_mainPh ret0_swPh h8 hok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ret0_limMapped hsub hfit fun v F' hF' => by
      by_cases hv : v = top
      · subst hv
        exact ret0_userCallW h8 hok hsub hfit hF' (hab F')
      · intro F'' _ _ hFF _ _ _ _
        exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, hD, _⟩ => hv ((hF' _ (hFF _ hD).1).1.1.1)

end Spike.Test.LowerX64UserCall
