/-
**hello.w's spawned child's segment inside `ZR ∧ X`, landing in `X`** (hello.w, row 5j-wit-W; AArch64):
`Spike/Lib/A64HelloWorkerSegRP.lean`'s `seg_childRP` and `seg_childPP` over `Spike/Lib/HelloSegTCSX.lean`'s
`SegTCSX`, composing the `X` links `Child.seg_childStubSX`, `Child.seg_thrWorkerSX` (`A64HelloThrTCSX`) and
`Wk.seg_wcWorkerSX` (`A64HelloWorkerTCSX`). The closed invariant of the result lies inside `X`
(`SegTCSX.closedX`), so `helloDR` reads `X`'s facts (`XHF`: `hplW`, `hcall`, the flag) off every pair of it.

`X` at every landing pair: at the nodes from `ZObl` (as in `seg_childRP`), and at the two landings off the
nodes from `ZXObl`: `print`'s return landing (`hXR`, the caller's return address with `print`'s control at
`[fr]`) and `wc_worker`'s return landing (`hXE`, the thread worker's `.sp0` with `wc_worker`'s control at `[]`).

Release note: when the `X` chain replaces the `SegTCS` one, `seg_childRP`, `SegTCS.toZHRP` and `seg_childPP`
become one-line corollaries through `SegTCSX.toS` or are deleted; the release keeps one chain.

- `WcXObl`, `ZXObl`: `X` at the two landings off the nodes, per `wc_worker` region (`ZObl.hwc`'s data);
  `ZXObl.and`: at a conjunction.
- `seg_childRPX`: from the stub's node at `[]` to `False`, inside `SH exe endPc (ZR exe kp ∧ X)`, landing in `X`.
- `SegTCSX.toZHRPX`: into `NNH ∧ ZHR exe kp ∧ X`.
- `seg_childPPX`: from `childP`, never leaving, once `ZObl X` and `ZXObl X` hold at every datum of `childP`.
- `childPX cS`, `seg_childPPXc`: `childP` with word 3 the flag `cS`'s locative, the obligations asked under it.
-/
import Spike.Lib.A64HelloWorkerSegRP
import Spike.Lib.A64HelloThrTCSX
import Spike.Lib.A64HelloWorkerTCSX

namespace Spike.Lib.A64.Flow.Worker.Hello.SegRP

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.PcRuns (PcIn)
open Spike.Lib.A64.Flow.RelZ (RelZ)
open Spike.Lib.HelloSegTCSX (SegTCSX)
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

/-- **`X` at `wc_worker`'s two landings off its nodes** in a region `R'`, `F'` at a return `x29`, `ra`
(`seg_wcWorkerSX`'s `hXR`, `hXE`): `print`'s return landing at `[fr]` in every `print` region whose frame
condition lands at the call node (`hXR`), and `wc_worker`'s return landing at `[]` (`hXE`). -/
structure WcXObl (X : FragS isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R' : Region)
    (F' : MachineData → Prop) (x29 ra : BitVec 64) (w : Words) (tp : BitVec 64) (w0 w1 w2 w3 w4 : TermRun.Word)
    (n m : Nat) : Prop where
  hXR : ∀ fr (R'' : Region) (F'' : MachineData → Prop), R''.OK → R''.base.toNat % 16 = 0 → R''.lo ≤ -96 →
      0 ≤ R''.hi → FStable R'' F'' → (∀ m, F'' m → F' m) →
      PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)) F'' → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)).J σC c →
      CallToI helloSrc c cE fr →
      ∀ s c', At exe endPc R'' F'' ((PrintA.E (_root_.Executable.labels exe).label σC.regs.X29.toBitVec
          σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat (PrW w0 w2 n m) (PrW w0 w2 n m) .ret).withTp
            σC.regs.TPIDR_EL0) s c' →
      X s c' [fr]
  hXE : ∀ s c, (∃ y, At exe endPc R' F' (HelloTail.E (cS2 w0 w1 w2 w3 w4) x29 ra tp y) s c) → X s c []

/-- **`X` at the landings off the nodes of the spawned child's run**: `WcXObl` in every `wc_worker` region
(`ZObl.hwc`'s data, at the return address `.sp0`). -/
structure ZXObl (X : FragS isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (w : Words) (tp : BitVec 64) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) :
    Prop where
  hwcX : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -192 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ x29 ra : BitVec 64,
      Int64.ofBitVec ra = (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") →
      WcXObl X exe endPc R' F' x29 ra w tp w0 w1 w2 w3 w4 n m

/-- **Two `ZXObl`s combine** (`X₁ ∧ X₂`). -/
theorem ZXObl.and {X₁ X₂ : FragS isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {w : Words} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (h₁ : ZXObl X₁ exe endPc R F w tp w0 w1 w2 w3 w4 n m) (h₂ : ZXObl X₂ exe endPc R F w tp w0 w1 w2 w3 w4 n m) :
    ZXObl (fun s c fs => X₁ s c fs ∧ X₂ s c fs) exe endPc R F w tp w0 w1 w2 w3 w4 n m where
  hwcX R' F' a b k d e f x29 ra hra :=
    { hXR := fun fr R'' F'' a' b' c' d' e' f' hFC σC cc cE hJ hC s c'' hAt =>
        ⟨(h₁.hwcX R' F' a b k d e f x29 ra hra).hXR fr R'' F'' a' b' c' d' e' f' hFC σC cc cE hJ hC s c'' hAt,
          (h₂.hwcX R' F' a b k d e f x29 ra hra).hXR fr R'' F'' a' b' c' d' e' f' hFC σC cc cE hJ hC s c'' hAt⟩
      hXE := fun s c h => ⟨(h₁.hwcX R' F' a b k d e f x29 ra hra).hXE s c h,
        (h₂.hwcX R' F' a b k d e f x29 ra hra).hXE s c h⟩ }

section Seg

variable {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The spawned child's segment inside `SH exe endPc (ZR exe kp ∧ X)`, landing in `X`** (`seg_childRP` over
`SegTCSX`): `X` at every node (`ZObl`) and at the two landings off the nodes (`ZXObl`). -/
theorem seg_childRPX {X : FragS isaLSE2} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
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
    (hX : ZObl X exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m)
    (hXX : ZXObl X exe endPc R F w tp w0 w1 w2 w3 w4 n m) :
    SegTCSX (SH exe endPc (fun s c fs => ZR exe kp s c fs ∧ X s c fs)) X helloSrc lbl ms
      ((At exe endPc R F (childN pfxM (_root_.Executable.labels exe).label (kidH T w0 w1 w2 w3 w4) w tp sp0)).at [])
      (fun _ _ _ => False) := by
  have hZX : ∀ s c fs, ZR exe kp s c fs ∧ X s c fs → X s c fs := fun _ _ _ h => h.2
  refine Child.seg_childStubSX (Z := fun s c fs => ZR exe kp s c fs ∧ X s c fs) hp hend hF hR hal
    (Int.le_trans hlo (by decide)) hhi hZX ?_
    (fun i => NodeZA.and (Z.childR_hZc hp hend hR hal (Int.le_trans hlo (by decide)) hhi
      (kidH_notPass T w0 w1 w2 w3 w4) i) (hX.hZc i))
  refine Child.seg_thrWorkerSX (Z := fun s c fs => ZR exe kp s c fs ∧ X s c fs) (c1 := wcP w0 w1 w2 w3 w4)
    (c3 := cS2 w0 w1 w2 w3 w4) hp hend hF hR hal hlo hhi
    hlimT (kid_splitH worker_find w0 w1 w2 w3 w4).toLocalRun hZX ?_ (hK []) (ar := .unit) rfl hSx
    (Wake.ZX.ProW.and (Z.thrR_hz hp hend hR hal (Int.le_trans hlo (by decide)) hhi
      (kidH_notPass T w0 w1 w2 w3 w4)) hX.hzT)
    (NodeZA.and (Z.thrR_hZE hp hend hR hal (Int.le_trans hlo (by decide)) hhi
      (kidH_notPass T w0 w1 w2 w3 w4)) hX.hZEt)
    (fun i => NodeZA.and (Z.thrR_hZT hp hend hR hal (Int.le_trans hlo (by decide)) hhi c2_pass i) (hX.hZT i))
  intro R' F' hR' hal' hlo' hhi' hF' hFF x29 ra hra
  have hW := hX.hwc R' F' hR' hal' hlo' hhi' hF' hFF x29 ra hra
  have hWX := hXX.hwcX R' F' hR' hal' hlo' hhi' hF' hFF x29 ra hra
  exact Wk.seg_wcWorkerSX (Z := fun s c fs => ZR exe kp s c fs ∧ X s c fs)
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
    hZX hWX.hXR hWX.hXE

end Seg

/-- **Into `helloDR`'s fragment** (`Z := ZHR ∧ X`): a segment inside `SH exe endPc (ZR exe kp ∧ X)` landing in
`X` is one inside `NNH ∧ ZHR exe kp ∧ X`. -/
theorem SegTCSX.toZHRPX {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64} {kp : Nat}
    {X P Q : FragS isaLSE2}
    (h : SegTCSX (SH exe endPc (fun s c fs => ZR exe kp s c fs ∧ X s c fs)) X p lbl ms P Q) :
    SegTCSX (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs ∧ X s c fs) X p lbl ms P Q :=
  h.mono_S fun _ _ _ h => ⟨h.1, h.2.1.1.toZHR h.2.2, h.2.1.2⟩

/-- **The child's segment from `childP` at `Z := ZHR ∧ X`, landing in `X`**: never leaving, once `X` holds at
every node (`hX`) and at the landings off the nodes (`hXX`) at every datum of `childP`. -/
theorem seg_childPPX {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat} {X : FragS isaLSE2}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi)
    (hX : ∀ d : ChildD, d.ok →
      ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m →
      ZObl X exe endPc ms d.R d.F d.w d.tp d.sp0 d.T d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m)
    (hXX : ∀ d : ChildD, d.ok →
      ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m →
      ZXObl X exe endPc d.R d.F d.w d.tp d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m) :
    SegTCSX (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs ∧ X s c fs) X helloSrc lbl ms
      (childP exe endPc kp lbl ms) (fun _ _ _ => False) := by
  refine SegTCSX.toZHRPX ((SegTCSX.exists_pre fun d : ChildD => SegTCSX.of_imp
    (A := d.ok ∧ ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m)
    (P := (At exe endPc d.R d.F (childN pfxM (_root_.Executable.labels exe).label
      (kidH d.T d.w0 d.w1 d.w2 d.w3 d.w4) d.w d.tp d.sp0)).at []) fun ⟨hok, h⟩ =>
      have ⟨hF, hR, hal, hlo, hhi⟩ := hok
      seg_childRPX hp hend hK hF hR hal hlo hhi h.hlimT h.hlimW h.hm h.hx1 h.hwm h.hm0 h.hwn h.hsvc h.hdm h.hv
        h.htag h.hvu h.hS h.htp4 h.hSx h.habt (hX d hok h) (hXX d hok h)).mono_pre ?_)
  rintro s c fs ⟨rfl, d, hok, hpr, hA⟩
  exact ⟨d, ⟨hok, hpr⟩, hA, rfl⟩

/-- **`childP` with the packet's word 3 the flag `cS`**: the stub node at some data whose premises hold and whose
word 3 is `cS`'s locative (the clone's argument, bound by `spawn` to the flag's cell). -/
def childPX (exe : _root_.Executable) (endPc : Int64) (kp : Nat) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) (cS : WeakMem.Address) : FragS isaLSE2 := fun s c fs =>
  fs = [] ∧ ∃ d : ChildD, d.ok ∧ ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m ∧
    d.w3.val = .loc cS 0 ∧
    At exe endPc d.R d.F (childN pfxM (_root_.Executable.labels exe).label (kidH d.T d.w0 d.w1 d.w2 d.w3 d.w4)
      d.w d.tp d.sp0) s c

/-- **The child's segment from `childPX cS`, landing in `X`**: as `seg_childPPX`, the obligations asked only at
data whose word 3 is `cS`'s locative (`hcS`). -/
theorem seg_childPPXc {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat} {X : FragS isaLSE2}
    {cS : WeakMem.Address} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi)
    (hX : ∀ d : ChildD, d.ok →
      ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m → d.w3.val = .loc cS 0 →
      ZObl X exe endPc ms d.R d.F d.w d.tp d.sp0 d.T d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m)
    (hXX : ∀ d : ChildD, d.ok →
      ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m → d.w3.val = .loc cS 0 →
      ZXObl X exe endPc d.R d.F d.w d.tp d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m) :
    SegTCSX (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs ∧ X s c fs) X helloSrc lbl ms
      (childPX exe endPc kp lbl ms cS) (fun _ _ _ => False) := by
  refine SegTCSX.toZHRPX ((SegTCSX.exists_pre fun d : ChildD => SegTCSX.of_imp
    (A := d.ok ∧ ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m ∧
      d.w3.val = .loc cS 0)
    (P := (At exe endPc d.R d.F (childN pfxM (_root_.Executable.labels exe).label
      (kidH d.T d.w0 d.w1 d.w2 d.w3 d.w4) d.w d.tp d.sp0)).at []) fun ⟨hok, h, hcS⟩ =>
      have ⟨hF, hR, hal, hlo, hhi⟩ := hok
      seg_childRPX hp hend hK hF hR hal hlo hhi h.hlimT h.hlimW h.hm h.hx1 h.hwm h.hm0 h.hwn h.hsvc h.hdm h.hv
        h.htag h.hvu h.hS h.htp4 h.hSx h.habt (hX d hok h hcS) (hXX d hok h hcS)).mono_pre ?_)
  rintro s c fs ⟨rfl, d, hok, hpr, hcS, hA⟩
  exact ⟨d, ⟨hok, hpr, hcS⟩, hA, rfl⟩

end Spike.Lib.A64.Flow.Worker.Hello.SegRP

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegRP.seg_childRPX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.SegRP.seg_childRPX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegRP.seg_childPPX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.SegRP.seg_childPPX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegRP.seg_childPPXc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.SegRP.seg_childPPXc
