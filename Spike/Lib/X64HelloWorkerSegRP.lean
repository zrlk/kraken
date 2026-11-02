/-
**hello.w's spawned child's obligations at an extra fragment `X`** (x86-64; the twin of
`Spike/Lib/A64HelloWorkerSegRP.lean`): `X` at every node of the child's run, in the shapes the three segment
theorems that compose the child's segment ask for (`Child.seg_childStubSX`, `Child.seg_thrWorkerSX`,
`Wk.seg_wcWorkerSX`, all generic in their fragment). Each `Z`-obligation at `ZR ∧ X` is the `ZR` one
(`Spike/Lib/X64HelloZR.lean`) and its field here (`NodeZA.and`, `XProW.and`, `AbortObl.and`); `print`'s `write`
(`hsvc`) is `SegR.SvcX` at `Xf := X · [fr]`, from `WcObl.hZP` at `.sys`.

- `WcObl`, `ZObl`: `X` at every node of the child's run (the stub, the thread worker, `wc_worker`, `print`, the
  store's tail, the `unpark`), and on `print`'s abort results (`hZA`).
- `WcObl.and`, `ZObl.and`: at a conjunction.

## Differences from the AArch64 version

- The fields take the x86-64 segment theorems' premise shapes: `wc_worker`'s prologue an `XProW` of frame 80
  (`.Lwc_worker.stk`), its `.entry` blocks three nodes (`.e`, the flag multiply, `.e2`), its call node a
  `NodeZA` at `Print.x0`, the store's tail at `HelloTail.NA`, the `unpark` from `CallerF` at the tail's `.unpk`
  node; `wkJ` reads the frame at `R'.addr 0`.
- `print`'s nodes (`hZP`) at `R''.lo ≤ -40`, `16 ≤ R''.hi` (also the `write` node `SvcX` needs), at
  `PrintF.cN … (-96) σC`; the abort (`hZA`) at `RA.lo ≤ -24`, `16 ≤ RA.hi`. No alignment premises.
- The thread worker's fields (`hzT`, `hZEt`, `hZT`, `hwc`) are at the re-based region `thrR R` from `sp0 - 8`,
  where `Child.seg_childStubSX` enters it; its prologue an `XProW` of frame 64, its tail at `HThrTail.NA`;
  `wc_worker` in every sub-region with `R'.lo ≤ -176`, `8 ≤ R'.hi`, at the return address `.x13`.
- `seg_childRP`, `seg_childPP`, `SegTCS.toZHRP` and `ZObl.triv` are not twinned.
-/
import Spike.Lib.X64HelloWorkerSegR
import Spike.Lib.X64HelloThrTCSX

namespace Spike.Lib.X64.Flow.Worker.Hello.SegRP

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloSplit (wcP wcR)
open Spike.Lib.X64HelloWorkerCallSrc (PrW KcW)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words wcJE thrJE thrJ childN cN cBlk)
open Spike.Lib.X64.Flow.Worker.Hello.Wk (wkJ wcPs)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (kidH cS1 cS2)
open Spike.Lib.X64WakeMainR (XProW.and)
open Spike.Lib.X64.Flow.Worker.Wake.Child (thrR)

/-- **`X` at `wc_worker`'s nodes** in a region `R'`, `F'` and at a return `rbp`, `ra`, the thread worker's stack
pointer `sp0` (`Wk.seg_wcWorkerSX`'s `hz`, `hZE`, `hZC`, `hZP`, `hZA`, `hZW`, `hZU` at `Z := X`). `hZP` at
`R''.lo ≤ -40` (`print`'s nodes, also the `write` node `SvcX` needs); `hZP` and `hZA` given their frame
condition's landing at the call node (`PrintF.CallFC`); `hZU` from the tail's `.unpk` node (`CallerF`), at the
return address `.x18` (`hra`). -/
structure WcObl (X : FragS isa) (exe : _root_.Executable) (endPc : Int64)
    (ms : List TermRun.Frame → MemSide isa) (R' : Region) (F' : MachineData → Prop) (rbp ra : BitVec 64)
    (w : Words) (tp sp0 : BitVec 64) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) : Prop where
  hz : XProW (fun s c => X s c []) (fun _ _ => False) exe endPc R' F' (ms [])
      ((_root_.Executable.labels exe).label "wc_worker") 80 8 ".Lwc_worker.stk" 5 9 3 6 4 wcPs
      (fun σ c => wcJE (wcP w0 w1 w2 w3 w4) w rbp ra tp σ c ∧ σ.regs.rsp.toBitVec = sp0 - 80#64)
  hZE : NodeZA (fun s c => X s c []) exe endPc R' F'
        (Body.wN (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
          (fun _ => PrW w0 w2 n m) .e) Body.wkE1 ∧
      NodeZA (fun s c => X s c []) exe endPc R' F'
        (Body.wN (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
          (fun _ => PrW w0 w2 n m) .mul) [(Body.wkMul.toDir, 4)] ∧
      NodeZA (fun s c => X s c []) exe endPc R' F'
        (Body.wN (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
          (fun _ => PrW w0 w2 n m) .e2) Body.wkE2
  hZC : NodeZA (fun s c => X s c []) exe endPc R' F'
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
        (KcW w0 w1 w2 w3 w4 n m)) Spike.Lib.X64.Print.x0
  hZP : ∀ fr (R'' : Region) (F'' : MachineData → Prop), R''.OK → R''.lo ≤ -40 → 16 ≤ R''.hi →
      FStable R'' F'' → (∀ m, F'' m → F' m) →
      PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label
        (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0)) (KcW w0 w1 w2 w3 w4 n m)) F'' → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
        (KcW w0 w1 w2 w3 w4 n m)).J σC c → CallToI helloSrc c cE fr →
      ∀ i, NodeZA (fun s c => X s c [fr]) exe endPc R'' F''
        (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m) (fun _ => PrW w0 w2 n m) (-96)
          σC i) (PrintF.FA.blkN i)
  hZA : ∀ fr (RA : Region) (FA : MachineData → Prop), RA.OK → RA.lo ≤ -24 → 16 ≤ RA.hi →
      FStable RA FA → (∀ m, FA m → F' m) →
      PrintF.CallFC R' (Body.wCall (_root_.Executable.labels exe).label
        (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0)) (KcW w0 w1 w2 w3 w4 n m)) FA → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (R'.addr 0))
        (KcW w0 w1 w2 w3 w4 n m)).J σC c →
      CallToI helloSrc c cE fr → ∀ k c', PrW w0 w2 n m k c' → AbortObl (fun s c => X s c [fr]) exe endPc RA FA c'
  hZW : ∀ i, NodeZA (fun s c => X s c []) exe endPc R' F'
      (HelloTail.NA (_root_.Executable.labels exe).label (wcR w0 w1 w2 w3 w4) (cS1 w0 w1 w2 w3 w4)
        (cS2 w0 w1 w2 w3 w4) w.w4 w.w5 rbp ra tp (R'.addr 0) i) (HelloTail.blkN i)
  hZU : ∀ (R'' : Region) (F'' : MachineData → Prop),
      CallerF R' F' (HelloTail.N (_root_.Executable.labels exe).label (wcR w0 w1 w2 w3 w4) (cS1 w0 w1 w2 w3 w4)
        (cS2 w0 w1 w2 w3 w4) w.w4 w.w5 rbp ra tp (R'.addr 0) .unpk) 0 (-40) 8 R'' F'' →
      ∀ rbp1 ra1, Int64.ofBitVec ra1 = (_root_.Executable.labels exe).label ".Lwc_worker.x18" → ∀ i,
      NodeZA (fun s c => X s c []) exe endPc R'' F''
        (Unpark.N (_root_.Executable.labels exe).label (cS1 w0 w1 w2 w3 w4) (cS2 w0 w1 w2 w3 w4) w.w5 rbp1 ra1 tp i)
        (Unpark.blkN i)

/-- **`X` at every node of the spawned child's run**: the stub (`hZc`) in `R`, the thread worker's prologue,
head and tail (`hzT`, `hZEt`, `hZT`) in `thrR R` from `sp0 - 8`, and `wc_worker` in every sub-region of it
(`hwc`), at the return address `.x13`. -/
structure ZObl (X : FragS isa) (exe : _root_.Executable) (endPc : Int64)
    (ms : List TermRun.Frame → MemSide isa) (R : Region) (F : MachineData → Prop) (w : Words)
    (tp sp0 : BitVec 64) (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) : Prop where
  hZc : ∀ i, NodeZA (fun s c => X s c []) exe endPc R F
      (cN (_root_.Executable.labels exe).label (kidH T w0 w1 w2 w3 w4) w tp sp0 i) (cBlk i)
  hzT : XProW (fun s c => X s c []) (fun _ _ => False) exe endPc (thrR R) F (ms [])
      ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 64 8 ".Lscc_rt_thr_worker.stk" 5 9 3 2 4 thrPs
      (thrJE (kidH T w0 w1 w2 w3 w4) w tp (sp0 - 8#64))
  hZEt : NodeZA (fun s c => X s c []) exe endPc (thrR R) F
      (HThrHead.tN (_root_.Executable.labels exe).label (thrJ (kidH T w0 w1 w2 w3 w4) w tp (sp0 - 8#64))
        (fun _ c => c = wcP w0 w1 w2 w3 w4) .e) HThrHead.thE
  hZT : ∀ i, NodeZA (fun s c => X s c []) exe endPc (thrR R) F
      (HThrTail.NA (_root_.Executable.labels exe).label (cS2 w0 w1 w2 w3 w4) tp (sp0 - 8#64) i) (HThrTail.blkN i)
  hwc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -176 → 8 ≤ R'.hi →
      FStable R' F' → (∀ m, F' m → F m) → ∀ rbp ra : BitVec 64,
      Int64.ofBitVec ra = (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x13" →
      WcObl X exe endPc ms R' F' rbp ra w tp (sp0 - 8#64) w0 w1 w2 w3 w4 n m

/-- **Two `WcObl`s combine** (`X₁ ∧ X₂`). -/
theorem WcObl.and {X₁ X₂ : FragS isa} {exe : _root_.Executable} {endPc : Int64}
    {ms : List TermRun.Frame → MemSide isa} {R' : Region} {F' : MachineData → Prop} {rbp ra : BitVec 64}
    {w : Words} {tp sp0 : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (h₁ : WcObl X₁ exe endPc ms R' F' rbp ra w tp sp0 w0 w1 w2 w3 w4 n m)
    (h₂ : WcObl X₂ exe endPc ms R' F' rbp ra w tp sp0 w0 w1 w2 w3 w4 n m) :
    WcObl (fun s c fs => X₁ s c fs ∧ X₂ s c fs) exe endPc ms R' F' rbp ra w tp sp0 w0 w1 w2 w3 w4 n m where
  hz := XProW.and h₁.hz h₂.hz
  hZE := ⟨NodeZA.and h₁.hZE.1 h₂.hZE.1, NodeZA.and h₁.hZE.2.1 h₂.hZE.2.1, NodeZA.and h₁.hZE.2.2 h₂.hZE.2.2⟩
  hZC := NodeZA.and h₁.hZC h₂.hZC
  hZP fr R'' F'' a b c d e f σC cc cE hJ hC i :=
    NodeZA.and (h₁.hZP fr R'' F'' a b c d e f σC cc cE hJ hC i) (h₂.hZP fr R'' F'' a b c d e f σC cc cE hJ hC i)
  hZA fr RA FA a b c d e f σC cc cE hJ hC k c' hQ :=
    (h₁.hZA fr RA FA a b c d e f σC cc cE hJ hC k c' hQ).and (h₂.hZA fr RA FA a b c d e f σC cc cE hJ hC k c' hQ)
  hZW i := NodeZA.and (h₁.hZW i) (h₂.hZW i)
  hZU R'' F'' hC rbp1 ra1 hra i :=
    NodeZA.and (h₁.hZU R'' F'' hC rbp1 ra1 hra i) (h₂.hZU R'' F'' hC rbp1 ra1 hra i)

/-- **Two `ZObl`s combine** (`X₁ ∧ X₂`). -/
theorem ZObl.and {X₁ X₂ : FragS isa} {exe : _root_.Executable} {endPc : Int64}
    {ms : List TermRun.Frame → MemSide isa} {R : Region} {F : MachineData → Prop} {w : Words}
    {tp sp0 : BitVec 64} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (h₁ : ZObl X₁ exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m)
    (h₂ : ZObl X₂ exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m) :
    ZObl (fun s c fs => X₁ s c fs ∧ X₂ s c fs) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m where
  hZc i := NodeZA.and (h₁.hZc i) (h₂.hZc i)
  hzT := XProW.and h₁.hzT h₂.hzT
  hZEt := NodeZA.and h₁.hZEt h₂.hZEt
  hZT i := NodeZA.and (h₁.hZT i) (h₂.hZT i)
  hwc R' F' a b c d e rbp ra hra :=
    (h₁.hwc R' F' a b c d e rbp ra hra).and (h₂.hwc R' F' a b c d e rbp ra hra)

/-- `ZObl` is inhabited: at `X := True` every field is its trivial obligation. -/
example {exe : _root_.Executable} {endPc : Int64} {ms : List TermRun.Frame → MemSide isa}
    {R : Region} {F : MachineData → Prop} {w : Words} {tp sp0 : BitVec 64} {T : Ty}
    {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} :
    ZObl (fun _ _ _ => True) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m where
  hZc _ := BlkW.triv
  hzT := XProW.triv
  hZEt := BlkW.triv
  hZT _ := BlkW.triv
  hwc _ _ _ _ _ _ _ _ _ _ :=
    { hz := XProW.triv, hZE := ⟨BlkW.triv, BlkW.triv, BlkW.triv⟩, hZC := BlkW.triv
      hZP := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => BlkW.triv
      hZA := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => AbortObl.triv
      hZW := fun _ => BlkW.triv
      hZU := fun _ _ _ _ _ _ _ => BlkW.triv }

end Spike.Lib.X64.Flow.Worker.Hello.SegRP

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SegRP.ZObl.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SegRP.ZObl.and
