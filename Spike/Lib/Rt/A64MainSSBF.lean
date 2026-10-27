/-
**The setup block's call at its ghost frame condition, with an extra frame
`Fw` after the switch** (AArch64): `mainES_segWSFB` and `startS_segWSFB`
(`Spike/Lib/Rt/A64MainSSB.lean`) with `scc_rt_main`'s frame
`Fw ∧ swFSL L rS top a v` in place of `swFSL L rS top a v`, from
`startEF_segWS` (`Spike/Lib/Rt/A64StartEF.lean`). The setup callee's frame
condition `F'` then gives `Fw` on the memory (`hFF`'s first conjunct), e.g.
`WordsNone Λ` at the setup frame.

- `mainESF_segWSFB`: from `MainEF` on, over the frame-generic
  `mainS_segWSFB`, the new frame `FStable` by `hFwS`;
- `startSF_segWSFB`: from `_start` (`startEF_segWS` then
  `mainESF_segWSFB`).
-/
import Spike.Lib.Rt.A64MainSSB
import Spike.Lib.Rt.A64StartEF

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

set_option linter.unusedSimpArgs false

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`mainES_segWSFB` with the extra frame `Fw` after the switch** (over
`mainS_segWSFB`, which is frame-generic; the new frame `FStable` by
`hFwS`). -/
theorem mainESF_segWSFB {W : FragS isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {sc : SetupCode} (hin : mainSIn prog sc = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    {rS : Scc.Sem.Range} {L : Int}
    (hL1 : sc.Z.toInt + D1 ≤ L) (hL2 : sc.Z.toInt + D2 ≤ L)
    (hK : (ms []).K = some Scc.Sem.A64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    {Fw : _root_.Mem 64 → Prop}
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m))
    {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec tcb)) (top - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec tcb)) (top - sc.Z.toBitVec - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec tcb)) (top - sc.Z.toBitVec - ZU2.toBitVec))
    (hS : ∀ v, SetupCallWSB W K p lbl ms exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m)
      sc.setup sc.Z D1 ZU1 PostR ((_root_.Executable.labels exe).label sc.e0 + 4).toBitVec c0 (UInt64.ofBitVec tcb)
      (SetupGF p (_root_.Executable.labels exe).label (ms []) exe endPc (swR v (-L) 0)
        (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m)
        sc D1 ZU1 ⟨top, UInt64.ofBitVec tcb, c0⟩ tcb))
    (hcall : ∃ cE fr, CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, At exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m)
      (mainSC (_root_.Executable.labels exe).label sc ⟨top, UInt64.ofBitVec tcb, c0⟩ tcb) s c → W s c [])
    (hU : ∀ v, MainCallWSF W K p lbl ms exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw tcb) Post ((_root_.Executable.labels exe).label sc.sp1).toBitVec
      (UInt64.ofBitVec tcb))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainSW (nilW W) K exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m) (ms [])
      sc PostS (fun c v => Post c [] v) ⟨top, UInt64.ofBitVec tcb, c0⟩ tcb)
    (hWx : ∀ v fs, ExitW (fun s c => W s c fs) K exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m)
      (mainSR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) sc.k)
    {Q : FragS isaLSE2} :
    SegWS W K p lbl ms ((MainEF exe endPc rS Fw tcb top c0 L).at []) Q := by
  let a := limA (UInt64.ofBitVec tcb)
  refine (SegWS.exists_pre (P := fun g : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK} =>
      (At exe endPc (swR g.1 (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top a g.1 m)
        (mainSN0 (_root_.Executable.labels exe).label ⟨top, UInt64.ofBitVec tcb, c0⟩ tcb)).at [])
    fun g => ?_).mono_pre fun _ _ _ ⟨⟨v, h1, h2, hA⟩, e⟩ => ⟨⟨v, h1, h2⟩, hA, e⟩
  obtain ⟨v, hv, hR⟩ := g
  have hF2 : FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top a v m) := hFwS v
  exact mainS_segWSFB hp hend hin h16 hZ hsw hZw hk hD10 hD18 hD20 hD28 hK hF2 hR hv
    (show -L ≤ -sc.Z.toInt - D1 by omega) (show -L ≤ -sc.Z.toInt - D2 by omega) (Int.le_refl _)
    ⟨top, UInt64.ofBitVec tcb, c0⟩ tcb ⟨hlimM.rt, hlimM.mp, fun _ h => h.2.1.2, hlimM.room⟩
    ⟨hlimS.rt, hlimS.mp, fun _ h => h.2.1.2, hlimS.room⟩ ⟨hlimU.rt, hlimU.mp, fun _ h => h.2.1.2, hlimU.room⟩
    (hS v) hcall hPS (hWC v) (hU v) (fun s c fs x hP hAt => hexit _ _ s c fs x hP hAt) (hW v) (hWx v)

/-- **`startS_segWSFB` with the extra frame `Fw` after the switch**
(`startEF_segWS` then `mainESF_segWSFB`). -/
theorem startSF_segWSFB {W : FragS isaLSE2} {rS : Scc.Sem.Range} {Fw : _root_.Mem 64 → Prop} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hc : RtCodeIn0 prog) {L : Int}
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk (ms []) F exe endPc (pinA (_root_.Executable.labels exe).label + n0)
      (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F exe endPc n0)
    (hk0 : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk (ms []) F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F exe endPc k0)
    (h16t : (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
      (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m))
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hWE : StartEWF (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F Fw rS n0 k0 c0 L)
    {sc : SetupCode} (hin : mainSIn prog sc = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hL1 : sc.Z.toInt + D1 ≤ L) (hL2 : sc.Z.toInt + D2 ≤ L) {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - sc.Z.toBitVec - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F₀ exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - sc.Z.toBitVec - ZU2.toBitVec))
    (hS : ∀ v, SetupCallWSB W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms exe endPc
      (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m)
      sc.setup sc.Z D1 ZU1 PostR ((_root_.Executable.labels exe).label sc.e0 + 4).toBitVec c0
      (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))
      (SetupGF p (_root_.Executable.labels exe).label (ms []) exe endPc (swR v (-L) 0)
        (fun m => Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) sc D1 ZU1
        ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64,
          UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
    (hcall : ∃ cE fr, CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, At exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m)
      (mainSC (_root_.Executable.labels exe).label sc ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64,
        UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)) s c → W s c [])
    (hU : ∀ v, MainCallWSF W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms exe endPc
      (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw (pinA (_root_.Executable.labels exe).label + n0 + 8#64)) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec
      (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainSW (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) (ms [])
      sc PostS (fun c v => Post c [] v) ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64,
        UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
      (pinA (_root_.Executable.labels exe).label + n0 + 8#64))
    (hWx : ∀ v fs, ExitW (fun s c => W s c fs) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS)
      exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m)
      (mainSR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) sc.k)
    {Q : FragS isaLSE2} :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN (_root_.Executable.labels exe).label c0)).at []) Q :=
  (startEF_segWS hp hend hc hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk0 hfld htk h16t hok hsub hun hFw hFwS
    hRS hfitS houtS hFt hWE).seq
    (mainESF_segWSFB hp hend hin h16 hZ hsw hZw hk hD10 hD18 hD20 hD28 hL1 hL2 hK _ _ c0 hFwS hlimM hlimS
      hlimU hS hcall hPS hWC hU hexit hW hWx)

end Proof

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.mainESF_segWSFB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainESF_segWSFB

/-- info: 'Spike.Lib.A64.Rt.startSF_segWSFB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startSF_segWSFB

end Spike.Lib.A64.Rt
