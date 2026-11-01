/-
**The flag at `wc_worker`'s two landings off its nodes** (rows B8-hflagR and B8-hflagE,
AArch64): `SegRP.ZXObl (FlagZ.FlagF cS)`, the flag half of `seg_childRPX`'s landing obligations at
`X := XHF`, given the packet's flag word is `cS`'s locative (`hcS`, carried by `SegRP.childPX cS`).

- `print`'s return landing (`WcXObl.hXR`): the call node's control is `wcP` (`KcW`), so the frame is
  `uFrame` (`HelloWorkerCallSrc.callI_inv`), and the landing's control is at `PrW`, a term of `print`'s or
  `printL`'s body (`prW_pTerm`, `PrW`'s term conjunct); the flag there is `FlagSrc.flagF_pTerm`.
- `wc_worker`'s return landing (`WcXObl.hXE`): the control is `SegR.cS2` (`HelloTail.E`), the flag there
  `FlagSrc.flagF_cS2`.

`PrW`'s term conjunct is `print`'s or `printL`'s body terms (tightening), so every
`PrW` control's term is `PTermP` (`prW_pTerm`; formerly the premise `hPT`, row B8-hPT-temp).

- `prW_pTerm`: a `PrW` control's term is `PTermP`.
- `at_E_ctl`: the control at `HelloTail.E c2`'s node is `c2`.
- `wcXObl_flag`, `zXObl_flag`: the obligations at `FlagF cS`.
-/
import Spike.Lib.A64HelloFlagSrc
import Spike.Lib.A64HelloWorkerSegRPX

namespace Spike.Lib.A64.Flow.Worker.Hello.FlagR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (wcP)
open Spike.Lib.HelloWorkerCallSrc (PrW KcW callI_inv)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (cS2)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (WcXObl ZXObl)
open Spike.Lib.A64.Flow.Worker.Hello.FlagZ (FlagF)
open Spike.Lib.A64.Flow.Worker.Hello.FlagSrc (PTermP flagF_pTerm flagF_cS2)

variable {exe : _root_.Executable} {endPc : Int64} {w : Words} {tp : BitVec 64}
  {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} {cS : WeakMem.Address}

/-- **The control at `wc_worker`'s exit node is the exit's.** -/
theorem at_E_ctl {R : Region} {F : MachineData → Prop} {c2 : Ctl} {x29 ra : BitVec 64} {s : State} {c : Ctl}
    (h : ∃ y, At exe endPc R F (HelloTail.E c2 x29 ra tp y) s c) : c = c2 := by
  obtain ⟨y, -, -, -, -, σ, -, -, hJ⟩ := h
  cases y
  exact hJ.1

/-- **A `PrW` control's term is `print`'s or `printL`'s** (`PrW`'s term conjunct). -/
theorem prW_pTerm {pw wn : TermRun.Word} {n m k : Nat} {c : Ctl} (h : PrW pw wn n m k c) : PTermP c.term :=
  h.2

/-- **`WcXObl` at the flag**: `print`'s return landing inside `print` on `uFrame`, `wc_worker`'s return
landing at `cS2`. -/
theorem wcXObl_flag (hcS : w3.val = .loc cS 0)
    (R' : Region) (F' : MachineData → Prop) (x29 ra : BitVec 64) :
    WcXObl (FlagF cS) exe endPc R' F' x29 ra w tp w0 w1 w2 w3 w4 n m where
  hXR := by
    intro fr R'' F'' _ _ _ _ _ _ _ σC c cE hJ hci s c' hA
    obtain ⟨-, hK⟩ := hJ
    obtain ⟨rfl, -⟩ := hK
    obtain ⟨-, rfl⟩ := callI_inv hci
    obtain ⟨-, -, -, -, σ, -, -, ⟨⟨-, -, hP⟩, -⟩⟩ := hA
    exact flagF_pTerm hcS (prW_pTerm hP) s
  hXE := by
    intro s c h
    rw [at_E_ctl h]
    exact flagF_cS2 cS w0 w1 w2 w3 w4 s

/-- **`ZXObl` at the flag** (`seg_childRPX`'s landing obligations' flag half, rows B8-hflagR and
B8-hflagE). -/
theorem zXObl_flag {R : Region} {F : MachineData → Prop} (hcS : w3.val = .loc cS 0) :
    ZXObl (FlagF cS) exe endPc R F w tp w0 w1 w2 w3 w4 n m :=
  ⟨fun R' F' _ _ _ _ _ _ x29 ra _ => wcXObl_flag hcS R' F' x29 ra⟩

/-- `hcS` is met by the flag's own locative word: the flag at `print`'s call, non-vacuously. -/
example (cS : WeakMem.Address) (w0 w1 w2 w4 : TermRun.Word) (s : State) :
    FlagF cS s (wcP w0 w1 w2 (TermRun.cst (.loc cS 0)) w4) [] :=
  FlagSrc.flagF_wcP rfl s

end Spike.Lib.A64.Flow.Worker.Hello.FlagR

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.FlagR.zXObl_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.FlagR.zXObl_flag

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.FlagR.prW_pTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.FlagR.prW_pTerm
