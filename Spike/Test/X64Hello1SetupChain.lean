/-
**`hello1.w` from the loaded thread to `scc_rt_main`'s exits at the setup
block's source** (x86-64): `startE_segWS` (`Spike/Lib/Rt/X64StartE.lean`,
the code checks `hello1_rtCodeInTi`) then `hello1_setup_segWS`
(`Spike/Lib/X64Hello1SetupGlue.lean`) at the control of the start before the
setup block (`setupTerm` in `setupStart`'s environment,
`Spike/Test/SetupStartSrc.lean`), the new stack's region of depth
`setupL + 8`. The x86-64 twin of `Spike/Test/A64Hello1SetupChain.lean`.

- `setupC`: the loaded thread's source control, `setupTerm` with `me` and
  `u` bound.
- `setupTerm_eq`: `setupTerm` is the setup block's call `setupCall`.
- `hello1_setup_chainWS`: from `_start` (`entryN0`) at the empty frames to
  `print`'s abort or the heap abort, the start's premises (`startE_segWS`'s
  but the code checks) and cuts A and B's per value of the new stack's base.
- The axioms of the setup chain's and the levels' rules.

Where x86-64 differs from AArch64: the depth is `setupL + 8` (`scc_rt_main`
in `call scc_rt_main`'s callee region, deep enough for the abort tails of
`Spike/Lib/X64Hello1SetupTail.lean`); `scc_rt_main`'s ghosts are the pushed
return address's slot `top - 8` and `tpOf tcb`; there is no `h16`.
-/
import Spike.Lib.X64Hello1Levels
import Spike.Test.X64Hello1StartE
import Spike.Test.SetupStartSrc

namespace Spike.Test.X64Hello1SetupChain

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Hello1
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Rt (MainE swFSL StartEW startE_segWS)
open Spike.Lib.X64.Rt.Test (hello1_rtCodeInTi)
open Scc.Sem.SrcSem (setupTerm)
open Spike.Lib.Hello1Src (hello1Src)
open Scc.Cert.Rt.X64 (Lays endOf)

/-- **The loaded thread's source control**: `setupTerm`, `me` the stand-in
`meW`, `u` the unit. -/
def setupC (meW : TermRun.Word) : Ctl :=
  ⟨setupTerm, [("me", .ptr .pub .void, [meW]), ("u", .unit, [])], none⟩

/-- `setupTerm` is the setup block's call, `main`'s argument pair and tail
call after it. -/
theorem setupTerm_eq : setupTerm = setupCall (.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a"))) :=
  rfl

/-- The setup block's continuation after `rodata`'s return. -/
abbrev setupK : Expr := .let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a"))

/-- The thread's TCB for the pinned slot `n0`. -/
abbrev tcbA (lab : Label → Int64) (n0 : BitVec 64) : BitVec 64 := pinA lab + n0 + 8#64

/-- The new stack's top for the taken stack `k0`. -/
abbrev topA (lab : Label → Int64) (k0 : BitVec 64) : BitVec 64 := stacksA lab + k0 + 16384#64

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`hello1.w` from `_start` to `scc_rt_main`'s exits at the setup
block's source**: `startE_segWS` at `hello1_rtCodeInTi` and the depth
`setupL + 8`, then `hello1_setup_segWS` at `setupC meW`. Exits: `print`'s
abort with no frame, the heap abort under `rodata`'s frame. -/
theorem hello1_setup_chainWS {W : FragS isa} {rS : Scc.Sem.Range} {meW : TermRun.Word}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk (ms []) F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F exe endPc n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (tcbA (_root_.Executable.labels exe).label n0)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk (ms []) F (tcbA (_root_.Executable.labels exe).label n0 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F exe endPc k0)
    (hok : (swR (topA (_root_.Executable.labels exe).label k0) (-(setupL + 8)) 0).OK)
    (hsub : ∀ k, (swR (topA (_root_.Executable.labels exe).label k0) (-(setupL + 8)) 0).Off k →
      ((swR (topA (_root_.Executable.labels exe).label k0) (-(setupL + 8)) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (topA (_root_.Executable.labels exe).label k0) (-(setupL + 8)) 0).addr k).toNat ∧
      rS.contains (((swR (topA (_root_.Executable.labels exe).label k0) (-(setupL + 8)) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (tcbA (_root_.Executable.labels exe).label n0))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (tcbA (_root_.Executable.labels exe).label n0))).toNat : Int) + 8 ≤
        (topA (_root_.Executable.labels exe).label k0).toNat + -(setupL + 8) ∨
      ((topA (_root_.Executable.labels exe).label k0).toNat : Int) + 0 ≤
        (limA (tpOf (tcbA (_root_.Executable.labels exe).label n0))).toNat)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (tpOf (tcbA (_root_.Executable.labels exe).label n0))) 8 = none)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartEW (fun s c => W s c []) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F rS n0 k0 (setupC meW) (setupL + 8) Rt.x8L)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?)
    {Jp J1 J2 J3 J4 Jr Jw : BitVec 64 → MachineData → AS → AS → Ctl → Prop}
    (hWe : ∀ s c, MainE exe endPc rS (tcbA (_root_.Executable.labels exe).label n0)
      (topA (_root_.Executable.labels exe).label k0) (setupC meW) (setupL + 8) s c → W s c [])
    (hPre : ∀ v, SetupPreP W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) lbl ms exe endPc
      (mainR v (setupL + 8))
      (mainF rS (tcbA (_root_.Executable.labels exe).label n0) (topA (_root_.Executable.labels exe).label k0) v
        (setupL + 8))
      [setupFrame setupK (setupC meW).env]
      (rdJ' ⟨topA (_root_.Executable.labels exe).label k0 - 8#64,
        tpOf (tcbA (_root_.Executable.labels exe).label n0), setupC meW⟩))
    (hret : ∀ v m0 σC σ c,
      (rX (ms [setupFrame setupK (setupC meW).env]) (_root_.Executable.labels exe).label lbl
        (mR (mainR v (setupL + 8)))
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (mainR v (setupL + 8))
          (rdJ' ⟨topA (_root_.Executable.labels exe).label k0 - 8#64,
            tpOf (tcbA (_root_.Executable.labels exe).label n0), setupC meW⟩)).J σC) .x13).J
        σ c → Jp v m0 σC σ c)
    (hPost : ∀ v m0 σC, SetupPostP W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      exe endPc (mainR v (setupL + 8))
      (mainF rS (tcbA (_root_.Executable.labels exe).label n0) (topA (_root_.Executable.labels exe).label k0) v
        (setupL + 8))
      (setupFrame setupK (setupC meW).env)
      m0 σC (Jp v m0 σC) (J1 v m0 σC) (J2 v m0 σC) (J3 v m0 σC) (J4 v m0 σC) (Jr v m0 σC) (Jw v m0 σC)) :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (Rt.entryN0 (_root_.Executable.labels exe).label (setupC meW))).at [])
      (fun s c fs => ∃ v : BitVec 64,
        (At exe endPc (mainR v (setupL + 8))
          (mainF rS (tcbA (_root_.Executable.labels exe).label n0) (topA (_root_.Executable.labels exe).label k0) v
            (setupL + 8))
          (mAb (_root_.Executable.labels exe).label)).at [] s c fs ∨
        Frag.at (fun s c => ∃ m0 σC, At exe endPc (mR (mainR v (setupL + 8)))
          (mF (mainR v (setupL + 8))
            (mainF rS (tcbA (_root_.Executable.labels exe).label n0) (topA (_root_.Executable.labels exe).label k0)
              v (setupL + 8)) m0 σC)
          (rX (ms [setupFrame setupK (setupC meW).env]) (_root_.Executable.labels exe).label lbl
            (mR (mainR v (setupL + 8)))
            (mRdJ0 (mNC (_root_.Executable.labels exe).label (mainR v (setupL + 8))
              (rdJ' ⟨topA (_root_.Executable.labels exe).label k0 - 8#64,
                tpOf (tcbA (_root_.Executable.labels exe).label n0), setupC meW⟩)).J σC)
            .abort) s c)
          [setupFrame setupK (setupC meW).env] s c fs) :=
  hello1_setup_segWS hp hend (by decide) (by decide) hK hfit hout hfitS rfl hd rfl
    (startE_segWS hp hend hello1_rtCodeInTi (by decide) hK hF hR hal hlo hhi n0 k0 _ hn hhdr htcb hk hfld htk hok
      hsub hfit hout hun hRS hfitS houtS hFt hW) hWe hPre hret hPost

-- No axioms beyond Lean's.
/--
info: 'Spike.Test.X64Hello1SetupChain.hello1_setup_chainWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_setup_chainWS

/--
info: 'Spike.Lib.X64.Flow.Hello1.hello1_setup_closedWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_setup_closedWS

/--
info: 'Spike.Lib.X64.Flow.Hello1.hello1_main_post_closedWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_main_post_closedWS

/--
info: 'Spike.Lib.X64.Flow.Hello1.hello1_setup_pre_closedWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_setup_pre_closedWS

/--
info: 'Spike.Lib.X64.Flow.Hello1.hello1_post_closedWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_post_closedWS

/--
info: 'Spike.Lib.X64.Flow.Hello1.rd_land' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rd_land

/--
info: 'Spike.Lib.X64.Flow.Hello1.land_post' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms land_post

end Spike.Test.X64Hello1SetupChain
