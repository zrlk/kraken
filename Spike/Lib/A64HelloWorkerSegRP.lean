/-
**hello.w's spawned child's segment inside `ZR ∧ X`** (row 5i-ZObl, AArch64): `seg_childR`
(`Spike/Lib/A64HelloWorkerSegR.lean`)
lifted to an extra fragment `X`, once `X` holds at every node of the
child's run (`ZObl`). The three segment theorems it composes
(`Child.seg_childStubS`, `Child.seg_thrWorkerS`, `Wk.seg_wcWorkerS`) are
generic in their fragment; each `Z`-obligation at `ZR ∧ X` is the
`ZR` one (`Spike/Lib/A64HelloZR.lean`) and its `ZObl` field (`NodeZA.and`,
`Wake.ZX.NodeW.and`, `Wake.ZX.ProW.and`); `print`'s `write` (`hsvc`) is
`SvcX` at `Xf := X · [fr]`, from `ZObl`'s `print` nodes at `svc`.

- `WcObl`, `ZObl`: `X` at every node of the child's run (the stub, the thread
  worker, `wc_worker`, `print`, the store's tail, the `unpark`), and on
  `print`'s abort results (`hZA`).
- `ZObl.triv`, `ZObl.and`, `WcObl.and`: at `True`, at a conjunction.
- `seg_childRP`: from the stub's node at `[]` to `False`, inside
  `SH exe endPc (ZR exe kp ∧ X)`; `SegTCS.toZHRP`: such a segment inside
  `NNH ∧ ZHR exe kp ∧ X`.
- `seg_childPP`: `helloDR`'s `hseg` at `Z := ZHR ∧ X`, from `childP`, once
  `ZObl X` holds at every datum of `childP`.
-/
import Spike.Lib.A64HelloWorkerSegP

namespace Spike.Lib.A64.Flow.Worker.Hello.SegRP

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.PcRuns (PcIn)
open Spike.Lib.A64.Flow.RelZ (RelZ)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (wcP wcR kid_splitH worker_find)
open Spike.Lib.HelloWorkerCallSrc (PrW KcW kcW_callI kcW_P0 kcW_done kcW_call)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE thrJE thrJ childN cN cBlk pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ wcPs)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZR ZHR prW_notUnpk kcW_notPass wcP_notPass wcR_notPass c1_pass
  c2_pass)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (kidH cS1 cS2 kidH_notPass SvcX ChildPrem ChildD childP)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

/-- **`X` at `wc_worker`'s nodes** in a region `R'`, `F'` and at a return
`x29`, `ra` (`seg_wcWorkerS`'s `hz`, `hZE`, `hZC`, `hZP`, `hZA`, `hZW`,
`hZU` at `Z := X`). `hZP` at `R''.lo ≤ -48` (`print`'s nodes, also the
`svc` node `SvcX` needs); `hZP` and `hZA` given their frame condition's
landing at the call node (`PrintF.CallFC`), `hZA` an `AbortObl` in any
dispatcher region; `hZU` at the return address `.sp6` (`hra`). -/
structure WcObl (X : FragS isaLSE2) (exe : _root_.Executable) (endPc : Int64)
    (ms : List TermRun.Frame → MemSide isaLSE2) (R' : Region) (F' : MachineData → Prop) (x29 ra : BitVec 64)
    (w : Words) (tp sp0 : BitVec 64) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) : Prop where
  hz : ProW (fun s c => X s c []) (fun _ _ => False) exe endPc R' F' (ms [])
      ((_root_.Executable.labels exe).label "wc_worker") 96 8 ".L20_wc_worker.stack_grow" wcPs
      (fun σ c => wcJE (wcP w0 w1 w2 w3 w4) w x29 ra tp σ c ∧ σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec)
  hZE : NodeZA (fun s c => X s c []) exe endPc R' F'
      (Body.wN (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (fun _ => PrW w0 w2 n m) .e) Body.wkE
  hZC : NodeW (fun s c => X s c []) (fun _ _ => False) exe endPc R' F'
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m))
  hZP : ∀ fr (R'' : Region) (F'' : MachineData → Prop), R''.OK → R''.base.toNat % 16 = 0 → R''.lo ≤ -48 →
      0 ≤ R''.hi → FStable R'' F'' → (∀ m, F'' m → F' m) →
      PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)) F'' → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)).J σC c → CallToI helloSrc c cE fr →
      ∀ i, NodeZA (fun s c => X s c [fr]) exe endPc R'' F''
        (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m) (fun _ => PrW w0 w2 n m) σC i)
        (PrintF.FA.blkN i)
  hZA : ∀ fr (RA : Region) (FA : MachineData → Prop), RA.OK → RA.base.toNat % 16 = 0 → RA.lo ≤ -48 →
      0 ≤ RA.hi → FStable RA FA → (∀ m, FA m → F' m) →
      PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)) FA → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)).J σC c →
      CallToI helloSrc c cE fr → ∀ k c', PrW w0 w2 n m k c' → AbortObl (fun s c => X s c [fr]) exe endPc RA FA c'
  hZW : ∀ i, NodeZA (fun s c => X s c []) exe endPc R' F'
      (HelloTail.N (_root_.Executable.labels exe).label (wcR w0 w1 w2 w3 w4) (cS1 w0 w1 w2 w3 w4)
        (cS2 w0 w1 w2 w3 w4) w.w4 w.w5 x29 ra tp i) (HelloTail.blkN i)
  hZU : ∀ (R'' : Region) (F'' : MachineData → Prop), R''.OK → R''.base.toNat % 16 = 0 → R''.lo ≤ -48 →
      0 ≤ R''.hi → FStable R'' F'' → (∀ m, F'' m → F' m) → ∀ x29' ra',
      Int64.ofBitVec ra' = (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" → ∀ i,
      NodeZA (fun s c => X s c []) exe endPc R'' F''
        (Unpark.N (_root_.Executable.labels exe).label (cS1 w0 w1 w2 w3 w4) (cS2 w0 w1 w2 w3 w4) w.w5 x29' ra' tp i)
        (Unpark.blkN i)

/-- **`X` at every node of the spawned child's run** (`seg_childR`'s data):
the stub (`hZc`), the thread worker's prologue, head and tail (`hzT`,
`hZEt`, `hZT`), and `wc_worker` in every sub-region (`hwc`), at the return
address `.sp0` (`hra`). -/
structure ZObl (X : FragS isaLSE2) (exe : _root_.Executable) (endPc : Int64)
    (ms : List TermRun.Frame → MemSide isaLSE2) (R : Region) (F : MachineData → Prop) (w : Words)
    (tp sp0 : BitVec 64) (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) : Prop where
  hZc : ∀ i, NodeZA (fun s c => X s c []) exe endPc R F
      (cN pfxM (_root_.Executable.labels exe).label (kidH T w0 w1 w2 w3 w4) w tp sp0 i) (cBlk i)
  hzT : ProW (fun s c => X s c []) (fun _ _ => False) exe endPc R F (ms [])
      ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 80 8 (HThrTail.pfx0 ++ ".stack_grow") thrPs
      (thrJE (kidH T w0 w1 w2 w3 w4) w tp sp0)
  hZEt : NodeZA (fun s c => X s c []) exe endPc R F
      (HThrHead.tN HThrTail.pfx0 (_root_.Executable.labels exe).label (thrJ (kidH T w0 w1 w2 w3 w4) w tp sp0)
        (fun _ c => c = wcP w0 w1 w2 w3 w4) .e) HThrHead.thE
  hZT : ∀ i, NodeZA (fun s c => X s c []) exe endPc R F
      (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label (cS2 w0 w1 w2 w3 w4) tp i) (HThrTail.blkN i)
  hwc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -192 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ x29 ra : BitVec 64,
      Int64.ofBitVec ra = (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") →
      WcObl X exe endPc ms R' F' x29 ra w tp sp0 w0 w1 w2 w3 w4 n m

/-- **`ZObl` at `X := True`.** -/
theorem ZObl.triv {exe : _root_.Executable} {endPc : Int64} {ms : List TermRun.Frame → MemSide isaLSE2}
    {R : Region} {F : MachineData → Prop} {w : Words} {tp sp0 : BitVec 64} {T : Ty}
    {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} :
    ZObl (fun _ _ _ => True) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m where
  hZc _ := BlkW.triv
  hzT := ProW.triv
  hZEt := BlkW.triv
  hZT _ := BlkW.triv
  hwc _ _ _ _ _ _ _ _ _ _ _ :=
    { hz := ProW.triv, hZE := BlkW.triv, hZC := NodeW.triv
      hZP := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => BlkW.triv
      hZA := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => AbortObl.triv
      hZW := fun _ => BlkW.triv
      hZU := fun _ _ _ _ _ _ _ _ _ _ _ _ => BlkW.triv }

/-- **Two `WcObl`s combine** (`X₁ ∧ X₂`). -/
theorem WcObl.and {X₁ X₂ : FragS isaLSE2} {exe : _root_.Executable} {endPc : Int64}
    {ms : List TermRun.Frame → MemSide isaLSE2} {R' : Region} {F' : MachineData → Prop} {x29 ra : BitVec 64}
    {w : Words} {tp sp0 : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (h₁ : WcObl X₁ exe endPc ms R' F' x29 ra w tp sp0 w0 w1 w2 w3 w4 n m)
    (h₂ : WcObl X₂ exe endPc ms R' F' x29 ra w tp sp0 w0 w1 w2 w3 w4 n m) :
    WcObl (fun s c fs => X₁ s c fs ∧ X₂ s c fs) exe endPc ms R' F' x29 ra w tp sp0 w0 w1 w2 w3 w4 n m where
  hz := Wake.ZX.ProW.and h₁.hz h₂.hz
  hZE := NodeZA.and h₁.hZE h₂.hZE
  hZC := Wake.ZX.NodeW.and h₁.hZC h₂.hZC
  hZP fr R'' F'' a b c d e f g σC cc cE hJ hC i :=
    NodeZA.and (h₁.hZP fr R'' F'' a b c d e f g σC cc cE hJ hC i) (h₂.hZP fr R'' F'' a b c d e f g σC cc cE hJ hC i)
  hZA fr RA FA a b c d e f g σC cc cE hJ hC k c' hQ :=
    (h₁.hZA fr RA FA a b c d e f g σC cc cE hJ hC k c' hQ).and (h₂.hZA fr RA FA a b c d e f g σC cc cE hJ hC k c' hQ)
  hZW i := NodeZA.and (h₁.hZW i) (h₂.hZW i)
  hZU R'' F'' a b c d e f x29' ra' hra i :=
    NodeZA.and (h₁.hZU R'' F'' a b c d e f x29' ra' hra i) (h₂.hZU R'' F'' a b c d e f x29' ra' hra i)

/-- **Two `ZObl`s combine** (`X₁ ∧ X₂`). -/
theorem ZObl.and {X₁ X₂ : FragS isaLSE2} {exe : _root_.Executable} {endPc : Int64}
    {ms : List TermRun.Frame → MemSide isaLSE2} {R : Region} {F : MachineData → Prop} {w : Words}
    {tp sp0 : BitVec 64} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (h₁ : ZObl X₁ exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m)
    (h₂ : ZObl X₂ exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m) :
    ZObl (fun s c fs => X₁ s c fs ∧ X₂ s c fs) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m where
  hZc i := NodeZA.and (h₁.hZc i) (h₂.hZc i)
  hzT := Wake.ZX.ProW.and h₁.hzT h₂.hzT
  hZEt := NodeZA.and h₁.hZEt h₂.hZEt
  hZT i := NodeZA.and (h₁.hZT i) (h₂.hZT i)
  hwc R' F' a b c d e f x29 ra hra :=
    (h₁.hwc R' F' a b c d e f x29 ra hra).and (h₂.hwc R' F' a b c d e f x29 ra hra)

section Seg

variable {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The spawned child's segment inside `SH exe endPc (ZR exe kp ∧ X)`**:
`seg_childR` with `print`'s `write` generic in `X` (`SvcX`) and `X` at every
node (`ZObl`). -/
theorem seg_childRP {X : FragS isaLSE2} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -272) (hhi : 0 ≤ R.hi)
    {w : Words} {tp sp0 : BitVec 64} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hlimT : ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = tp →
      (ms []).rt (tcbA r 8).toNat ∧ (ms []).mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, (ms []).G ⟨tcbA r 8, 8⟩ v → (v.setWidth 64).toNat ≤ (sp0 - (80 : Int64).toBitVec).toNat)
    (hlimW : ∀ x29 ra σ c, wcJE (wcP w0 w1 w2 w3 w4) w x29 ra tp σ c →
      σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec →
      (ms []).rt (tcbA σ.regs 8).toNat ∧ (ms []).mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, (ms []).G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat)
    (hm : w.w2.toNat * 8 < 2 ^ 63)
    (hx1 : ∀ x29 ra σ, wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp σ (wcP w0 w1 w2 w3 w4) →
      (Body.wkC (_root_.Executable.labels exe).label σ).regs.X1.toBitVec.toNat = printN n m)
    (hwm : w1.val = .num m) (hm0 : m ≠ 0) (hwn : w2.val = .num n)
    (hsvc : SvcX exe endPc kp lbl ms F w tp w0 w1 w2 w3 w4 n m)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem w.w4 8 = none)
    (hv : Scc.Sem.ValRep lbl w3.val w.w4.toNat) (htag : ∃ sa, w3.val = .loc sa 0)
    (hvu : Scc.Sem.ValRep lbl w4.val w.w5.toNat)
    (hS : StOk (ms []) F exe endPc (w.w5 + 16#64) 1#64) (htp4 : (w.w5 + 16#64).toNat % 4 = 0)
    (hSx : StOk (ms []) F exe endPc (tp + 24#64) 1#64)
    (habt : ∀ fr s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit →
      (ms [fr]).abortAt s)
    (hX : ZObl X exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m) :
    SegTCS (SH exe endPc (fun s c fs => ZR exe kp s c fs ∧ X s c fs)) helloSrc lbl ms
      ((At exe endPc R F (childN pfxM (_root_.Executable.labels exe).label (kidH T w0 w1 w2 w3 w4) w tp sp0)).at [])
      (fun _ _ _ => False) := by
  refine Child.seg_childStubS (Z := fun s c fs => ZR exe kp s c fs ∧ X s c fs) hp hend hF hR hal
    (Int.le_trans hlo (by decide)) hhi ?_
    (fun i => NodeZA.and (Z.childR_hZc hp hend hR hal (Int.le_trans hlo (by decide)) hhi
      (kidH_notPass T w0 w1 w2 w3 w4) i) (hX.hZc i))
  refine Child.seg_thrWorkerS (Z := fun s c fs => ZR exe kp s c fs ∧ X s c fs) (c1 := wcP w0 w1 w2 w3 w4)
    (c3 := cS2 w0 w1 w2 w3 w4) hp hend hF hR hal hlo hhi
    hlimT (kid_splitH worker_find w0 w1 w2 w3 w4).toLocalRun ?_ (hK []) (ar := .unit) rfl hSx
    (Wake.ZX.ProW.and (Z.thrR_hz hp hend hR hal (Int.le_trans hlo (by decide)) hhi
      (kidH_notPass T w0 w1 w2 w3 w4)) hX.hzT)
    (NodeZA.and (Z.thrR_hZE hp hend hR hal (Int.le_trans hlo (by decide)) hhi
      (kidH_notPass T w0 w1 w2 w3 w4)) hX.hZEt)
    (fun i => NodeZA.and (Z.thrR_hZT hp hend hR hal (Int.le_trans hlo (by decide)) hhi c2_pass i) (hX.hZT i))
  intro R' F' hR' hal' hlo' hhi' hF' hFF x29 ra hra
  have hW := hX.hwc R' F' hR' hal' hlo' hhi' hF' hFF x29 ra hra
  exact Wk.seg_wcWorkerS (Z := fun s c fs => ZR exe kp s c fs ∧ X s c fs)
    (c1 := cS1 w0 w1 w2 w3 w4) (c2 := cS2 w0 w1 w2 w3 w4)
    (X := fun σ => σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec)
    (Pr := fun _ => PrW w0 w2 n m) (Qa := fun _ => PrW w0 w2 n m) (Kc := KcW w0 w1 w2 w3 w4 n m)
    hp hend hF' hR' hal' hlo' hhi'
    (fun σ c hJ hX => by
      obtain ⟨h1, h2, h3, h4⟩ := hlimW x29 ra σ c hJ hX
      exact ⟨h1, h2, fun m hm => h3 m (hFF m hm), h4⟩)
    hm (kcW_call rfl (hx1 x29 ra)) (fun _ _ h => kcW_callI h) (fun _ _ _ _ h hc => kcW_P0 hwm hm0 hwn h hc)
    (fun _ _ _ _ _ _ h hc hP => kcW_done h hc hP) hK
    (fun fr R'' F'' hR'' hal'' hlo'' hhi'' hF'' hFF'' hFC σC c cE hJ hC =>
      hsvc x29 ra fr R'' F'' hR'' hal'' hlo'' hhi'' hF'' (fun m h => hFF m (hFF'' m h)) σC c cE hJ hC
        (fun s c => X s c [fr])
        (hW.hZP fr R'' F'' hR'' hal'' hlo'' hhi'' hF'' hFF'' hFC σC c cE hJ hC .svc).toW)
    (fun m h => hdm m (hFF m h))
    rfl rfl hv htag rfl (by simp [TermRun.cst, Promises.TVal.mk0, Scc.Sem.ValRep]) rfl
    (hS.mono hFF) htp4 rfl rfl rfl hvu rfl
    (Wake.ZX.ProW.and (Z.wcR_hz hp hend hR' hal' (Int.le_trans hlo' (by decide)) hhi'
      (wcP_notPass w0 w1 w2 w3 w4)) hW.hz)
    (NodeZA.and (Z.wcR_hZE hp hend hR' hal' (Int.le_trans hlo' (by decide)) hhi'
      (wcP_notPass w0 w1 w2 w3 w4)) hW.hZE)
    (Wake.ZX.NodeW.and (Z.wcR_hZC hp hend hR' hal' hlo' hhi' fun _ _ h => kcW_notPass h) hW.hZC)
    (fun fr R'' F'' hR'' hal'' hlo'' hhi'' hF'' hFF'' hFC σC c cE hJ hC i =>
      NodeZA.and (Z.wcR_hZP hp hend hR'' hal'' (Int.le_trans hlo'' (by decide)) hhi''
        (fun _ _ h => prW_notUnpk h) (fun _ _ h => prW_notUnpk h) i)
        (hW.hZP fr R'' F'' hR'' hal'' (Int.le_trans hlo'' (by decide)) hhi'' hF'' hFF'' hFC σC c cE hJ hC i))
    (fun fr RA FA hRA halA hloA hhiA hFA hFAF hFC σC c cE hJ hC k c' hQ =>
      (AbortObl.ofPc hp hend SccCode.hello_abort hFA hRA halA hloA hhiA fun _ he hpc _ hr =>
        Z.wcR_hZA hp (prW_notUnpk hQ) he hpc hr).and
        (hW.hZA fr RA FA hRA halA hloA hhiA hFA hFAF hFC σC c cE hJ hC k c' hQ))
    habt (fun fr s c h => Z.wcR_hZu fr s c h.1)
    (fun i => NodeZA.and (Z.wcR_hZW hp hend hR' hal' (Int.le_trans hlo' (by decide)) hhi'
      (wcR_notPass w0 w1 w2 w3 w4) c1_pass c2_pass i) (hW.hZW i))
    (fun R'' F'' hR'' hal'' hlo'' hhi'' hF'' hFF'' x29' ra' hra' i =>
      NodeZA.and (Z.wcR_hZU hp hend hR'' hal'' hlo'' hhi'' c1_pass c2_pass i)
        (hW.hZU R'' F'' hR'' hal'' hlo'' hhi'' hF'' hFF'' x29' ra' hra' i))

end Seg

/-- **Into `helloDR`'s `hseg` fragment** (`Z := ZHR ∧ X`): a segment inside
`SH exe endPc (ZR exe kp ∧ X)` is one inside `NNH ∧ ZHR exe kp ∧ X`. -/
theorem SegTCS.toZHRP {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64} {kp : Nat}
    {X P Q : FragS isaLSE2}
    (h : SegTCS (SH exe endPc (fun s c fs => ZR exe kp s c fs ∧ X s c fs)) p lbl ms P Q) :
    SegTCS (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs ∧ X s c fs) p lbl ms P Q :=
  h.mono_S fun _ _ _ h => ⟨h.1, h.2.1.1.toZHR h.2.2, h.2.1.2⟩

/-- **`helloDR`'s `hseg` at `Z := ZHR ∧ X`**: from `childP`, never leaving,
once `X` holds at every node of the child's run at every datum of `childP`
(`hX`). -/
theorem seg_childPP {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat} {X : FragS isaLSE2}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi)
    (hX : ∀ d : ChildD, d.ok →
      ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m →
      ZObl X exe endPc ms d.R d.F d.w d.tp d.sp0 d.T d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m) :
    SegTCS (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs ∧ X s c fs) helloSrc lbl ms
      (childP exe endPc kp lbl ms) (fun _ _ _ => False) := by
  refine SegTCS.toZHRP ((SegTCS.exists_pre fun d : ChildD => SegR.SegTCS.of_imp
    (A := d.ok ∧ ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m)
    (P := (At exe endPc d.R d.F (childN pfxM (_root_.Executable.labels exe).label
      (kidH d.T d.w0 d.w1 d.w2 d.w3 d.w4) d.w d.tp d.sp0)).at []) fun ⟨hok, h⟩ =>
      have ⟨hF, hR, hal, hlo, hhi⟩ := hok
      seg_childRP hp hend hK hF hR hal hlo hhi h.hlimT h.hlimW h.hm h.hx1 h.hwm h.hm0 h.hwn h.hsvc h.hdm h.hv
        h.htag h.hvu h.hS h.htp4 h.hSx h.habt (hX d hok h)).mono_pre ?_)
  rintro s c fs ⟨rfl, d, hok, hpr, hA⟩
  exact ⟨d, ⟨hok, hpr⟩, hA, rfl⟩

end Spike.Lib.A64.Flow.Worker.Hello.SegRP

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegRP.seg_childRP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.SegRP.seg_childRP

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegRP.seg_childPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.SegRP.seg_childPP
