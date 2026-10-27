/-
**The x86-64 setup block's call at its ghost frame condition, with an extra
frame `Fw` after the switch**: `mainES_segWSFB` and `startS_segWSFB`
(`Spike/Lib/Rt/X64MainSSB.lean`) over `MainEF`/`StartEWF`
(`Spike/Lib/Rt/X64StartEF.lean`), so that a frame fact `Fw` on the memory
of `_start`'s frame (`hFw`), `FStable` in the switched stack's region with
`swFSL` (`hFwS`), reaches the setup call's and the user function's frame
conditions.

- `mainESF_segWSFB`: `mainES_segWSFB` from `MainEF` (`hFwS` in place of
  `hfit`, `hout`, `hfitS`);
- `startSF_segWSFB`: `startS_segWSFB` from `_start` at `StartEWF` (`hFw`,
  `hFwS` in place of `hfit`, `hout`).
-/
import Spike.Lib.Rt.X64MainSSB
import Spike.Lib.Rt.X64StartEF

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`mainES_segWSFB` with the extra frame `Fw` after the switch**
(`mainS_segWSFB` at `MainEF`'s region and frame condition, `mainEF_ok`). -/
theorem mainESF_segWSFB {W : FragS isa} {K : State → State → Prop} {rS : Scc.Sem.Range} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {sc : SetupCode} (hin : mainSIn cells sc = true)
    (hZ8 : sc.Z.toInt % 8 = 0) (hsw : sc.sw ≤ 5) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop} {L : Int}
    (hL1 : 8 + 8 + sc.Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + sc.Z.toInt + 8 + D2 ≤ L) (hL8 : L % 8 = 0)
    (hK : (ms []).K = some Scc.Sem.X64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    {Fw : _root_.Mem 64 → Prop}
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m))
    {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ (limA (tpOf tcb)) (top - 8#64 - 8#64 - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F₀ (limA (tpOf tcb)) (top - 8#64 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F₀ (limA (tpOf tcb)) (top - 8#64 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU2.toBitVec))
    (hS : ∀ v, SetupCallWSB W K p lbl ms exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.setup sc.Z D1 ZU1 PostR ((_root_.Executable.labels exe).label sc.sp0).toBitVec c0 (tpOf tcb)
      (SetupGF p (_root_.Executable.labels exe).label (ms []) ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
        (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
        sc D1 ZU1 ⟨top - 8#64, tpOf tcb, c0⟩ (tpOf tcb).toBitVec))
    (hcall : ∃ cE fr, CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, At exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSC (_root_.Executable.labels exe).label sc ⟨top - 8#64, tpOf tcb, c0⟩ (tpOf tcb).toBitVec) s c →
      W s c [])
    (hU : ∀ v, MainCallWSF W K p lbl ms exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw (tpOf tcb).toBitVec) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec (tpOf tcb))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label sc.sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU sc.Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainSW (nilW W) K exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (ms [])
      sc PostS (fun c v => Post c [] v) ⟨top - 8#64, tpOf tcb, c0⟩ (tpOf tcb).toBitVec)
    (hWx : ∀ v fs, XExitW (fun s c => W s c fs) K exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSRR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) (-8 - sc.Z.toInt) (-8) sc.k 4 4 5)
    {Q : FragS isa} :
    SegWS W K p lbl ms ((MainEF exe endPc Fw rS tcb top c0 L).at []) Q := by
  refine (SegWS.exists_pre (P := fun g : {v : BitVec 64 // (swR v (-L) 0).OK} =>
      (At exe endPc ((swR g.1 (-L) 0).callee (-8 - 0) (8 - L) 8)
        (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) g.1 m) ∧
          CallerCells (swR g.1 (-L) 0) (-8 - 0) (8 - L) 8 m)
        (mainSN0 (_root_.Executable.labels exe).label ⟨top - 8#64, tpOf tcb, c0⟩ (tpOf tcb).toBitVec)).at [])
    fun g => ?_).mono_pre fun _ _ _ ⟨⟨v, h1, hA⟩, e⟩ => ⟨⟨v, h1⟩, hA, e⟩
  obtain ⟨v, hv⟩ := g
  obtain ⟨hR, hF⟩ := mainEF_ok (rS := rS) (tcb := tcb) (top := top) (by omega) hL8 hv (hFwS v)
  have hun : ∀ m, ((Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧
      CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) →
      Mem.loadInt m.dmem (limA (tpOf tcb)) 8 = none := fun _ h => h.1.2.1.2
  exact mainS_segWSFB hp hend hin hZ8 hsw hZw hk hD10 hD18 hD20 hD28 hK hF hR
    (show 8 - L ≤ -8 - sc.Z.toInt - 8 - D1 by omega) (show 8 - L ≤ -8 - sc.Z.toInt - 8 - D2 by omega)
    (show (0 : Int) ≤ 8 by decide) ⟨top - 8#64, tpOf tcb, c0⟩ (tpOf tcb).toBitVec
    ⟨hlimM.rt, hlimM.mp, hun, hlimM.room⟩ ⟨hlimS.rt, hlimS.mp, hun, hlimS.room⟩
    ⟨hlimU.rt, hlimU.mp, hun, hlimU.room⟩ (hS v) hcall hPS (hWC v) (hU v)
    (fun s c fs x hP hAt => hexit _ _ s c fs x hP hAt) (hW v)
    (hWx v)

/-- **`startS_segWSFB` with the extra frame `Fw` after the switch**
(`startEF_segWS` then `mainESF_segWSFB`). -/
theorem startSF_segWSFB {W : FragS isa} {rS : Scc.Sem.Range} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {xr : Label} (hc : RtCodeInTi cells xr) {L : Int}
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk (ms []) F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F exe endPc n0)
    (hk0 : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk (ms []) F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F exe endPc k0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    {Fw : _root_.Mem 64 → Prop} (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧
      swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m))
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hWE : StartEWF (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F Fw rS n0 k0 c0 L xr)
    {sc : SetupCode} (hin : mainSIn cells sc = true)
    (hZ8 : sc.Z.toInt % 8 = 0) (hsw : sc.sw ≤ 5) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hL1 : 8 + 8 + sc.Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + sc.Z.toInt + 8 + D2 ≤ L) (hL8 : L % 8 = 0)
    {F₀ : MachineData → Prop}
    (hlimM : LimOk (ms []) F₀ (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec))
    (hlimS : LimOk (ms []) F₀ (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec -
        8#64 - 8#64 - ZU1.toBitVec))
    (hlimU : LimOk (ms []) F₀ (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - sc.Z.toBitVec -
        8#64 - 8#64 - ZU2.toBitVec))
    (hS : ∀ v, SetupCallWSB W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms exe endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.setup sc.Z D1 ZU1 PostR ((_root_.Executable.labels exe).label sc.sp0).toBitVec c0
      (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))
      (SetupGF p (_root_.Executable.labels exe).label (ms []) ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
        (fun m => (Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
            (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) ∧
          CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
        sc D1 ZU1 ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64,
          tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
        (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)).toBitVec))
    (hcall : ∃ cE fr, CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, CallTo p c0 cE fr → PostR c rs → ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hWC : ∀ v s c, At exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSC (_root_.Executable.labels exe).label sc ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 -
        8#64, tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
        (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)).toBitVec) s c → W s c [])
    (hU : ∀ v, MainCallWSF W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms exe endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)).toBitVec)
      Post ((_root_.Executable.labels exe).label sc.sp1).toBitVec
      (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
    (hexit : ∀ R' F' s c fs (v : BitVec 64), Post c fs v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label sc.sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU sc.Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c → MainExitFA p (ms []) s c fs v.toNat)
    (hW : ∀ v, MainSW (nilW W) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (ms [])
      sc PostS (fun c v => Post c [] v) ⟨stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64,
        tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64), c0⟩
      (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)).toBitVec)
    (hWx : ∀ v fs, XExitW (fun s c => W s c fs) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS)
      exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
          (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSRR (_root_.Executable.labels exe).label sc (fun c v => Post c fs v)) (-8 - sc.Z.toInt) (-8) sc.k 4 4 5)
    {Q : FragS isa} :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN0 (_root_.Executable.labels exe).label c0)).at []) Q :=
  (startEF_segWS hp hend hc (by omega) hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk0 hfld htk hok hsub
    hun hFw hFwS hRS hfitS houtS hFt hWE).seq
    (mainESF_segWSFB hp hend hin hZ8 hsw hZw hk hD10 hD18 hD20 hD28 hL1 hL2 hL8 hK _ _ c0 hFwS hlimM hlimS
      hlimU hS hcall hPS hWC hU hexit hW hWx)

end Proof

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Rt.mainESF_segWSFB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainESF_segWSFB

/-- info: 'Spike.Lib.X64.Rt.startSF_segWSFB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startSF_segWSFB

end Spike.Lib.X64.Rt
