/-
**hello's worker landing fact with the flag** (AArch64; rows 5j-wit-W, 5j-wit-E-call, B8-genP-hmapW-flag): the
fragment `XHF` the worker's segment invariant lies in: `A64HelloXH`'s `XH` (every frame placed, the caller frame of
the call the control runs to placed) and the flag
`FlagZ.FlagF cS` (every control a frame run reaches accesses no untagged locative but `cS`).

`XHF` is the conjunction `XH ∧ FlagF cS` in `SegRP.ZObl.and`'s shape, so its per-node obligations split:
`ZObl (XH Λ lbl)` and `ZObl (FlagF cS)` (`zObl_XHF`). The flag holds at each landing pair of a row from a node
where it holds, once the landing's control is reached by a frame run (`FlagF.run`).

- `XHF`; `hplW_ofF`, `hcall_ofF`, `hflag_ofF`: the rows `hplW`, `hcall` and the flag by projection.
- `zObl_XHF`: `ZObl` at `XHF` from its two parts.
-/
import Spike.Lib.A64HelloXH
import Spike.Lib.A64HelloFlagZ

namespace Spike.Lib.A64.HelloPh.XH

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib (Ctl LocalRunS FragS)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (workerCallH workerRestH)
open Spike.Lib.A64.Flow.Worker.Hello.FlagZ (FlagF)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (ZObl)

/-- **The worker's landing fact with the flag `cS`.** -/
def XHF (Λ : Scc.Sem.Layout) (lbl : Lbl) (cS : WeakMem.Address) : FragS isaLSE2 := fun s c fs =>
  XH Λ lbl s c fs ∧ FlagF cS s c fs

variable {ι : Type} {Λ : Scc.Sem.Layout} {L : ι → Lbl} {cS : ι → WeakMem.Address}

/-- **`hplW` by projection.** -/
theorem hplW_ofF {Wi : ι → FragS isaLSE2} (h : ∀ w s c fs, Wi w s c fs → XHF Λ (L w) (cS w) s c fs) :
    ∀ w st c fs, Wi w st c fs → PlacedSE Λ (L w) st c fs :=
  hplW_of fun w s c fs hw => (h w s c fs hw).1

/-- **`hcall` by projection.** -/
theorem hcall_ofF {Wi : ι → FragS isaLSE2} (h : ∀ w s c fs, Wi w s c fs → XHF Λ (L w) (cS w) s c fs) :
    ∀ w st c, Wi w st c [] → ∀ c', LocalRunS helloSrc c c' → c'.term = workerCallH →
      FramesPlaced Λ (L w) st [⟨"u", workerRestH, c'.env, [], .unit⟩] :=
  hcall_of fun w s c fs hw => (h w s c fs hw).1

/-- **The flag by projection.** -/
theorem hflag_ofF {Wi : ι → FragS isaLSE2} (h : ∀ w s c fs, Wi w s c fs → XHF Λ (L w) (cS w) s c fs) :
    ∀ w st c fs, Wi w st c fs → FlagF (cS w) st c fs :=
  fun w st c fs hw => (h w st c fs hw).2

/-- **`ZObl` at `XHF`** from `XH`'s and the flag's. -/
theorem zObl_XHF {lbl : Lbl} {cS : WeakMem.Address} {exe : _root_.Executable} {endPc : Int64}
    {ms : List TermRun.Frame → MemSide isaLSE2} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {w : Spike.Lib.A64.Flow.Worker.Hello.Child.Words} {tp sp0 : BitVec 64} {T : Ty}
    {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hX : ZObl (XH Λ lbl) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m)
    (hf : ZObl (FlagF cS) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m) :
    ZObl (XHF Λ lbl cS) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m :=
  hX.and hf

end Spike.Lib.A64.HelloPh.XH

/-- info: 'Spike.Lib.A64.HelloPh.XH.hflag_ofF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XH.hflag_ofF

/-- info: 'Spike.Lib.A64.HelloPh.XH.zObl_XHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XH.zObl_XHF
