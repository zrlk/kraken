/-
**hello.w's worker side per record at `X := XHF`** (hello.w, rows 5j-wit-W, 5j-wit-E-call; AArch64):
`Spike/Lib/HelloWorkerRR.lean`'s `helloDR` at a `SegTCSX` segment per record whose landings lie in
`X w := XHF Λ (lbl w) (cS w)`; the rows `hplW`, `hcall` and the flag are projections of `helloDR_X`.

- `helloDR_hplW`, `helloDR_hcall`, `helloDR_flag`: at `X := XHF`, the rows `hplW`, `hcall` and the flag.
-/
import Spike.Lib.HelloWorkerRR
import Spike.Lib.HelloWorkerSideX
import Spike.Lib.A64HelloXHF

namespace Spike.Lib.HelloWorkerRRX

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.A64.WideKeep (WideX)
open Spike.Lib.HelloSplit (workerCallH workerRestH)
open Spike.Lib.A64.Flow.Worker.Hello.FlagZ (FlagF)
open Spike.Lib.A64.HelloPh.XH (XHF)
open Spike.Lib.HelloWorkerRR (helloDR helloDR_X)

section XHF

variable {ι : Type} {exe : _root_.Executable} {endPc : Int64} {SR : ι → SpawnRec}
  {lbl : ι → WeakMem.AllocLabel → Option Nat} {ms : ι → List TermRun.Frame → MemSide isaLSE2}
  {P Z : ι → FragS isaLSE2} {Λ : Scc.Sem.Layout} {cS : ι → WeakMem.Address} {hK : ∀ w fs, (ms w fs).K = some abi}
  {hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ Z w s c fs) (XHF Λ (lbl w) (cS w)) helloSrc (lbl w)
    (ms w) (P w) (fun _ _ _ => False)}
  {cw : ι → TermRun.Word} {bufL : ι → WeakMem.AllocLabel} {nB mB : ι → Nat}

/-- **The row `hplW` at `helloDR`** (`X := XHF`). -/
theorem helloDR_hplW : ∀ w st c fs,
    (helloDR exe endPc SR lbl ms P Z (fun w => XHF Λ (lbl w) (cS w)) hK hseg cw bufL nB mB).Wi w st c fs →
    PlacedSE Λ (lbl w) st c fs :=
  Spike.Lib.A64.HelloPh.XH.hplW_ofF (helloDR_X exe endPc SR lbl ms P Z _ hK hseg cw bufL nB mB)

/-- **The row `hcall` at `helloDR`** (`X := XHF`). -/
theorem helloDR_hcall : ∀ w st c,
    (helloDR exe endPc SR lbl ms P Z (fun w => XHF Λ (lbl w) (cS w)) hK hseg cw bufL nB mB).Wi w st c [] →
    ∀ c', LocalRunS helloSrc c c' → c'.term = workerCallH →
      FramesPlaced Λ (lbl w) st [⟨"u", workerRestH, c'.env, [], .unit⟩] :=
  Spike.Lib.A64.HelloPh.XH.hcall_ofF (helloDR_X exe endPc SR lbl ms P Z _ hK hseg cw bufL nB mB)

/-- **The flag at `helloDR`** (`X := XHF`): at every pair of the invariant, every control a frame run reaches
accesses no untagged locative but `cS w`. -/
theorem helloDR_flag : ∀ w st c fs,
    (helloDR exe endPc SR lbl ms P Z (fun w => XHF Λ (lbl w) (cS w)) hK hseg cw bufL nB mB).Wi w st c fs →
    FlagF (cS w) st c fs :=
  Spike.Lib.A64.HelloPh.XH.hflag_ofF (helloDR_X exe endPc SR lbl ms P Z _ hK hseg cw bufL nB mB)

end XHF

end Spike.Lib.HelloWorkerRRX

/-- info: 'Spike.Lib.HelloWorkerRRX.helloDR_hplW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerRRX.helloDR_hplW

/-- info: 'Spike.Lib.HelloWorkerRRX.helloDR_hcall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerRRX.helloDR_hcall

/-- info: 'Spike.Lib.HelloWorkerRRX.helloDR_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerRRX.helloDR_flag
