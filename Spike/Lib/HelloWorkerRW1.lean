/-
**hello.w's worker's `hW1` at `helloDR`** (row
AArch64): at `Z := fun _ => ZHR exe kp`
(`Spike/Lib/A64HelloZR.lean`), every state of `helloDR`'s invariant runs an
instruction whose tree writes at most once, a release write
(`WakeConv1`'s `hW1`, the worker's half of `HelloAssembly`'s `hconv`).

- `hRW1_DR`: from `helloDR_inv`'s pending run into `ZHR` (`relW1_of_pend`).
-/
import Spike.Lib.A64HelloZR
import Spike.Lib.HelloWorkerRR

namespace Spike.Lib.HelloWorkerRR

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZHR relW1_of_pend)

/-- **`hW1` at `helloDR`** (`Z := ZHR`): every instruction of a worker's
state writes at most once, a release write. -/
theorem hRW1_DR {ι : Type} (exe : _root_.Executable) (endPc : Int64) (kp : Nat) (SR : ι → SpawnRec)
    (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → List TermRun.Frame → MemSide isaLSE2)
    (P X : ι → FragS isaLSE2) (hK : ∀ w fs, (ms w fs).K = some abi)
    (hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs) (X w) helloSrc (lbl w) (ms w) (P w)
      (fun _ _ _ => False))
    (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat) :
    ∀ w s c fs e, (helloDR exe endPc SR lbl ms P (fun _ => ZHR exe kp) X hK hseg cw bufL nB mB).Wi w s c fs →
      isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e :=
  fun w s c fs e h he =>
    relW1_of_pend (fun _ _ _ h => h.2)
      (helloDR_inv exe endPc SR lbl ms P (fun _ => ZHR exe kp) X hK hseg cw bufL nB mB w s c fs h).2.2 e he

/-- info: 'Spike.Lib.HelloWorkerRR.hRW1_DR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerRR.hRW1_DR

end Spike.Lib.HelloWorkerRR
