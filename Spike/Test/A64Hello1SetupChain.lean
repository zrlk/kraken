/-
**`hello1.w` from the loaded thread to `scc_rt_main`'s exits at the setup
block's source** (AArch64): `startE_segWS` (`Spike/Lib/Rt/A64StartE.lean`,
the code checks `hello1_rtCodeIn0`) then `hello1_setup_segWS`
(`Spike/Lib/A64Hello1SetupGlue.lean`) at the control of the start before the
setup block (`setupTerm` in `setupStart`'s environment,
`Spike/Test/SetupStartSrc.lean`), the new stack's region of depth `setupL`.

- `setupC`: the loaded thread's source control, `setupTerm` with `me` and
  `u` bound.
- `setupTerm_eq`: `setupTerm` is the setup block's call `setupCall`.
- `hello1_setup_chainWS`: from `_start` (`entryN`) at the empty frames to
  `print`'s abort or the heap abort, the start's premises (`startE_segWS`'s
  but the code checks) and cuts A and B's per value of the new stack's base.
-/
import Spike.Lib.A64Hello1SetupGlue
import Spike.Test.A64Hello1StartE
import Spike.Test.SetupStartSrc

namespace Spike.Test.A64Hello1SetupChain

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Hello1
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (MainE swFSL StartEW startE_segWS)
open Spike.Lib.A64.Rt.Test (hello1_rtCodeIn0)
open Scc.Sem.SrcSem (setupTerm)
open Spike.Lib.Hello1Src (hello1Src)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- **The loaded thread's source control**: `setupTerm`, `me` the stand-in
`meW`, `u` the unit. -/
def setupC (meW : TermRun.Word) : Ctl :=
  ⟨setupTerm, [("me", .ptr .pub .void, [meW]), ("u", .unit, [])], none⟩

/-- `setupTerm` is the setup block's call, `main`'s argument pair and tail
call after it. -/
theorem setupTerm_eq : setupTerm = setupCall (.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a"))) :=
  rfl

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`hello1.w` from `_start` to `scc_rt_main`'s exits at the setup
block's source**: `startE_segWS` at `hello1_rtCodeIn0` and the depth
`setupL`, then `hello1_setup_segWS` at `setupC meW`. Exits: `print`'s abort
with no frame, the heap abort under `rodata`'s frame. -/
theorem hello1_setup_chainWS {W : FragS isaLSE2} {rS : Scc.Sem.Range} {meW : TermRun.Word}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk (ms []) F exe endPc (pinA (_root_.Executable.labels exe).label + n0)
      (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F exe endPc n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk (ms []) F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F exe endPc k0)
    (h16 : (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-setupL) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-setupL) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-setupL) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-setupL) 0).addr k).toNat ∧
      rS.contains
        (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-setupL) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -setupL ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartEW (fun s c => W s c []) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F rS n0 k0 (setupC meW) setupL)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?)
    {Jp J1 J2 J3 J4 Jr Jw : BitVec 64 → MachineData → AS → AS → Ctl → Prop}
    (hWe : ∀ s c, MainE exe endPc rS (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (setupC meW) setupL s c → W s c [])
    (hPre : ∀ v, SetupPreP W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) lbl ms exe endPc
      (swR v (-setupL) 0) (swFSL setupL rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v)
      [setupFrame (.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a"))) (setupC meW).env]
      (rdJ' ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64,
        UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64), setupC meW⟩))
    (hret : ∀ v m0 σC σ c,
      (rX (ms [setupFrame (.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a")))
          (setupC meW).env]) (_root_.Executable.labels exe).label lbl
        (mRdJ0 (mNC (_root_.Executable.labels exe).label
          (rdJ' ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64,
            UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64), setupC meW⟩)).J σC) .sp0).J
        σ c → Jp v m0 σC σ c)
    (hPost : ∀ v m0 σC, SetupPostP W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      exe endPc (swR v (-setupL) 0)
      (swFSL setupL rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v)
      (setupFrame (.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a"))) (setupC meW).env)
      m0 σC (Jp v m0 σC) (J1 v m0 σC) (J2 v m0 σC) (J3 v m0 σC) (J4 v m0 σC) (Jr v m0 σC) (Jw v m0 σC)) :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN (_root_.Executable.labels exe).label (setupC meW))).at [])
      (fun s c fs => ∃ v : BitVec 64,
        (At exe endPc (swR v (-setupL) 0)
          (swFSL setupL rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
            (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v)
          (mAb (_root_.Executable.labels exe).label)).at [] s c fs ∨
        Frag.at (fun s c => ∃ m0 σC, At exe endPc (mR (swR v (-setupL) 0))
          (mF (swR v (-setupL) 0)
            (swFSL setupL rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
              (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v) m0 σC)
          (rX (ms [setupFrame (.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a")))
              (setupC meW).env]) (_root_.Executable.labels exe).label lbl
            (mRdJ0 (mNC (_root_.Executable.labels exe).label
              (rdJ' ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64,
                UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64), setupC meW⟩)).J σC)
            .abort) s c)
          [setupFrame (.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a"))) (setupC meW).env]
          s c fs) :=
  hello1_setup_segWS hp hend (by decide) hK hfit hout hfitS rfl hd rfl
    (startE_segWS hp hend hello1_rtCodeIn0 hK hF hR hal hlo hhi n0 k0 _ hn hhdr htcb hk hfld htk h16 hok hsub hfit
      hout hun hRS hfitS houtS hFt hW) hWe hPre hret hPost

end Spike.Test.A64Hello1SetupChain
