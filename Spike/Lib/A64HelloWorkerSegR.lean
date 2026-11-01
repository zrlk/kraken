/-
**hello.w's spawned child's frame-aware segment at the concrete control
fact** (row 5j-misc, AArch64): the child's stub, the thread
worker and `wc_worker` (`Child.seg_childStubS`, `Child.seg_thrWorkerS`,
`Wk.seg_wcWorkerS`) composed at `Z := ZR exe kp` (`Z0 ∧ RelZ`,
`Spike/Lib/A64HelloZR.lean`), `print`'s predicate `PrW` and the call's
control `KcW` (`Spike/Lib/HelloWorkerCallSrc.lean`), on the packet's five
source words `w0 .. w4` (the slice's three, the flag's, main's `ThreadId`).
The source controls are the child's tail call (`kidH`), `wcP` at `print`'s
call, `wcR` at the store, `cS1` past it, `cS2` past the `unpark`.

- `kidH`, `cS1`, `cS2`; `kidH_notPass`.
- `SvcX` (`print`'s `write` segment generic in an extra fragment, the
  child's `hsvc` premise), `SvcX.toR` (at `Xf := True`).
- `seg_childR`: from the stub's node at `[]` to `False`, inside
  `SH exe endPc (ZR exe kp)`; `SegTCS.toZHR`: such a segment inside
  `NNH ∧ ZHR exe kp` (`helloDR`'s `hseg` fragment at `Z := ZHR`).

Its premises left explicit (rows; `seg_wcWorkerS`'s names):
- the stacks' bounds at the thread pointer's `tcb` word (`hlimT`, `hlimW`)
  and `w.w2.toNat * 8 < 2 ^ 63` (`hm`);
- the count register at the call is `printN n m`, the slice nonempty
  (`hx1`, `hwm`, `hm0`, `hwn`);
- `print`'s `write` (`hsvc`) and the abort's exit (`habt`);
- the cell's and main's words: `hdm`, `hv`, `htag`, `hvu`, `hS`, `htp4`,
  `hSx`.
-/
import Spike.Lib.A64HelloThrTCS
import Spike.Lib.A64HelloZR
import Spike.Lib.A64HelloZSrc

namespace Spike.Lib.A64.Flow.Worker.Hello.SegR

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (wcP wcR kid_splitH worker_find)
open Spike.Lib.HelloWorkerCallSrc (PrW KcW kcW_callI kcW_P0 kcW_done kcW_call)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE thrJE childN pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.A64.Flow.Worker.Hello.Pass (HPassC)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZR ZHR prW_notUnpk kcW_notPass wcP_notPass wcR_notPass c1_pass
  c2_pass)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

/-- **The child's control after the spawn**: `tail worker [] (var "a") []`
on the packet's five words. -/
def kidH (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) : Ctl :=
  ⟨.tail "worker" [] (.var "a") [], [("a", T, [w0, w1, w2, w3, w4])], none⟩

/-- The control past the store: `d` bound, at the `unpark`. -/
def cS1 (w0 w1 w2 w3 w4 : TermRun.Word) : Ctl :=
  ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wcR w0 w1 w2 w3 w4).env, none⟩

/-- The control past the `unpark`: `ret ()`. -/
def cS2 (w0 w1 w2 w3 w4 : TermRun.Word) : Ctl :=
  ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: (cS1 w0 w1 w2 w3 w4).env, none⟩

theorem kidH_notPass (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) : ¬ HPassC (kidH T w0 w1 w2 w3 w4) := by
  simp [HPassC, kidH, Spike.Lib.WorkerSrc.wkUnpark]

/-- **`print`'s `write` segment, generic in an extra fragment** (the
child segment's `hsvc` premise, `ChildPrem.hsvc`): at every call state of
`wc_worker`'s call node on the packet's words, for every fragment `Xf` that
holds at `print`'s `write` node, the `write` is a segment inside
`NNZP SysW1 (ZR ∧ Xf)` from the `svc` node to `n5`. `Xf := True` is the
`ZR`-only premise of `seg_childR` (`SvcX.toR`); a lifted fragment
`ZR ∧ X` (`SegRP.seg_childRP`) instantiates `Xf` at `X`'s `print` nodes. -/
def SvcX (exe : _root_.Executable) (endPc : Int64) (kp : Nat) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) (F : MachineData → Prop) (w : Words) (tp : BitVec 64)
    (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) : Prop :=
  ∀ x29 ra fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 →
    R'.lo ≤ -48 → 0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c cE,
    (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
      (KcW w0 w1 w2 w3 w4 n m)).J σC c → CallToI helloSrc c cE fr →
    ∀ Xf : Frag isaLSE2, NodeW Xf (fun _ _ => False) exe endPc R' F'
      (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m) (fun _ => PrW w0 w2 n m) σC .svc) →
    SegTC (NNZP SysW1 exe endPc (fun s c => ZR exe kp s c [fr] ∧ Xf s c)) helloSrc lbl (ms [fr])
      (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m)
        (fun _ => PrW w0 w2 n m) σC .svc))
      (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m)
        (fun _ => PrW w0 w2 n m) σC .n5))

/-- **`SvcX` at `Xf := True`**: `seg_childR`'s `hsvc`. -/
theorem SvcX.toR {exe : _root_.Executable} {endPc : Int64} {kp : Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2} {F : MachineData → Prop} {w : Words} {tp : BitVec 64}
    {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} (h : SvcX exe endPc kp lbl ms F w tp w0 w1 w2 w3 w4 n m) :
    ∀ x29 ra fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 →
      R'.lo ≤ -48 → 0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)).J σC c → CallToI helloSrc c cE fr →
      SegTC (NNZP SysW1 exe endPc (fun s c => ZR exe kp s c [fr])) helloSrc lbl (ms [fr])
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m)
          (fun _ => PrW w0 w2 n m) σC .svc))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m)
          (fun _ => PrW w0 w2 n m) σC .n5)) :=
  fun x29 ra fr R' F' hR hal hlo hhi hF hFF σC c cE hJ hC =>
    (h x29 ra fr R' F' hR hal hlo hhi hF hFF σC c cE hJ hC (fun _ _ => True) NodeW.triv).mono_S
      fun _ _ h => ⟨h.1, h.2.1⟩

section Seg

variable {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The spawned child's segment inside `SH exe endPc (ZR exe kp)`**: from
the stub's node at `[]`, never leaving (`False`). -/
theorem seg_childR (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
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
    (hsvc : ∀ x29 ra fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 →
      R'.lo ≤ -48 → 0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp)
        (KcW w0 w1 w2 w3 w4 n m)).J σC c → CallToI helloSrc c cE fr →
      SegTC (NNZP SysW1 exe endPc (fun s c => ZR exe kp s c [fr])) helloSrc lbl (ms [fr])
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m)
          (fun _ => PrW w0 w2 n m) σC .svc))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m)
          (fun _ => PrW w0 w2 n m) σC .n5)))
    (hdm : ∀ m, F m → Mem.loadInt m.dmem w.w4 8 = none)
    (hv : Scc.Sem.ValRep lbl w3.val w.w4.toNat) (htag : ∃ sa, w3.val = .loc sa 0)
    (hvu : Scc.Sem.ValRep lbl w4.val w.w5.toNat)
    (hS : StOk (ms []) F exe endPc (w.w5 + 16#64) 1#64) (htp4 : (w.w5 + 16#64).toNat % 4 = 0)
    (hSx : StOk (ms []) F exe endPc (tp + 24#64) 1#64)
    (habt : ∀ fr s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit →
      (ms [fr]).abortAt s) :
    SegTCS (SH exe endPc (ZR exe kp)) helloSrc lbl ms
      ((At exe endPc R F (childN pfxM (_root_.Executable.labels exe).label (kidH T w0 w1 w2 w3 w4) w tp sp0)).at [])
      (fun _ _ _ => False) := by
  refine Child.seg_childStubS hp hend hF hR hal (Int.le_trans hlo (by decide)) hhi ?_
    (fun i => Z.childR_hZc hp hend hR hal (Int.le_trans hlo (by decide)) hhi (kidH_notPass T w0 w1 w2 w3 w4) i)
  refine Child.seg_thrWorkerS (c1 := wcP w0 w1 w2 w3 w4) (c3 := cS2 w0 w1 w2 w3 w4) hp hend hF hR hal hlo hhi
    hlimT (kid_splitH worker_find w0 w1 w2 w3 w4).toLocalRun ?_ (hK []) (ar := .unit) rfl hSx
    (Z.thrR_hz hp hend hR hal (Int.le_trans hlo (by decide)) hhi (kidH_notPass T w0 w1 w2 w3 w4))
    (Z.thrR_hZE hp hend hR hal (Int.le_trans hlo (by decide)) hhi (kidH_notPass T w0 w1 w2 w3 w4))
    (fun i => Z.thrR_hZT hp hend hR hal (Int.le_trans hlo (by decide)) hhi c2_pass i)
  intro R' F' hR' hal' hlo' hhi' hF' hFF x29 ra _
  exact Wk.seg_wcWorkerS (c1 := cS1 w0 w1 w2 w3 w4) (c2 := cS2 w0 w1 w2 w3 w4)
    (X := fun σ => σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec)
    (Pr := fun _ => PrW w0 w2 n m) (Qa := fun _ => PrW w0 w2 n m) (Kc := KcW w0 w1 w2 w3 w4 n m)
    hp hend hF' hR' hal' hlo' hhi'
    (fun σ c hJ hX => by
      obtain ⟨h1, h2, h3, h4⟩ := hlimW x29 ra σ c hJ hX
      exact ⟨h1, h2, fun m hm => h3 m (hFF m hm), h4⟩)
    hm (kcW_call rfl (hx1 x29 ra)) (fun _ _ h => kcW_callI h) (fun _ _ _ _ h hc => kcW_P0 hwm hm0 hwn h hc)
    (fun _ _ _ _ _ _ h hc hP => kcW_done h hc hP) hK (fun fr R'' F'' hR'' hal'' hlo'' hhi'' hF'' hFF'' _ =>
      hsvc x29 ra fr R'' F'' hR'' hal'' hlo'' hhi'' hF'' fun m h => hFF m (hFF'' m h))
    (fun m h => hdm m (hFF m h))
    rfl rfl hv htag rfl (by simp [TermRun.cst, Promises.TVal.mk0, Scc.Sem.ValRep]) rfl
    (hS.mono hFF) htp4 rfl rfl rfl hvu rfl
    (Z.wcR_hz hp hend hR' hal' (Int.le_trans hlo' (by decide)) hhi' (wcP_notPass w0 w1 w2 w3 w4))
    (Z.wcR_hZE hp hend hR' hal' (Int.le_trans hlo' (by decide)) hhi' (wcP_notPass w0 w1 w2 w3 w4))
    (Z.wcR_hZC hp hend hR' hal' hlo' hhi' fun _ _ h => kcW_notPass h)
    (fun _ R'' F'' hR'' hal'' hlo'' hhi'' _ _ _ _ _ _ _ _ i =>
      Z.wcR_hZP hp hend hR'' hal'' (Int.le_trans hlo'' (by decide)) hhi''
        (fun _ _ h => prW_notUnpk h) (fun _ _ h => prW_notUnpk h) i)
    (fun _ _ _ hRA halA hloA hhiA hFA _ _ _ _ _ _ _ _ _ hQ =>
      AbortObl.ofPc hp hend SccCode.hello_abort hFA hRA halA hloA hhiA fun _ he hpc _ hr =>
        Z.wcR_hZA hp (prW_notUnpk hQ) he hpc hr)
    habt Z.wcR_hZu
    (fun i => Z.wcR_hZW hp hend hR' hal' (Int.le_trans hlo' (by decide)) hhi' (wcR_notPass w0 w1 w2 w3 w4)
      c1_pass c2_pass i)
    (fun R'' F'' hR'' hal'' hlo'' hhi'' _ _ _ _ _ i => Z.wcR_hZU hp hend hR'' hal'' hlo'' hhi'' c1_pass c2_pass i)

end Seg

/-- **Into `helloDR`'s `hseg` fragment** (`Z := ZHR`): a segment inside
`SH exe endPc (ZR exe kp)` is one inside `NNH ∧ ZHR exe kp`. -/
theorem SegTCS.toZHR {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} {endPc : Int64} {kp : Nat} {P Q : FragS isaLSE2}
    (h : SegTCS (SH exe endPc (ZR exe kp)) p lbl ms P Q) :
    SegTCS (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs) p lbl ms P Q :=
  h.mono_S fun _ _ _ h => ⟨h.1, h.2.1.toZHR h.2.2⟩

end Spike.Lib.A64.Flow.Worker.Hello.SegR

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegR.seg_childR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.SegR.seg_childR
