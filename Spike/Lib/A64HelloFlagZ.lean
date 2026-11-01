/-
**The flag conjunct of hello.w's worker segment fragment** (AArch64): `HelloHaltMapW.hmapW_flagH`'s `hflag` asks
that at every control a frame run reaches, every untagged locative accessed
is the flag `cS` (`WakeMappedRow.LabPtr`); wake reads it off `wakeZX`'s
`LabPtr` conjunct. Here it is a fragment closed under frame runs
(`FlagF`), conjoined to the segment's extra fragment `X` (`ZF`), so the
child's segment (`SegRP.seg_childPP`, `ZObl`) carries it at
`Z := ZHR ∧ ZF cS X` with no change to `ZObl`: its per-node discharge is
`ZObl (FlagF cS)` (`ZObl.flag`).

- `FlagF cS`: every control a frame run reaches from here accesses no
  untagged locative but `cS`; `FlagF.run`: closed under frame runs;
  `FlagF.ptr`: at the control itself.
- `ZF cS X`: `FlagF cS ∧ X`; `ZObl.flag`: `ZObl` at `ZF` from its parts.
- `flag_of_pend`: under `Pend`, the flag at every control reached from the
  pending witness.
-/
import Spike.Lib.A64HelloWorkerSegRP
import Spike.Lib.WakeMappedRow

namespace Spike.Lib.A64.Flow.Worker.Hello.FlagZ

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.WakeMappedRow (LabPtr)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (ZObl)

/-- **The flag, closed under frame runs**: at every control a frame run of
hello's source reaches from `(c, fs)`, every untagged locative accessed is
`cS`. -/
def FlagF (cS : WeakMem.Address) : FragS isaLSE2 := fun _ c fs =>
  ∀ c₁ fs₁, FrameRun helloSrc (c, fs) (c₁, fs₁) → ∀ sa, LabPtr c₁ sa → sa = cS

/-- `FlagF` after a frame run. -/
theorem FlagF.run {cS : WeakMem.Address} {s : State} {c c' : Ctl} {fs fs' : List TermRun.Frame}
    (h : FlagF cS s c fs) (r : FrameRun helloSrc (c, fs) (c', fs')) (s' : State) : FlagF cS s' c' fs' :=
  fun c₁ fs₁ r₁ => h c₁ fs₁ (r.trans r₁)

/-- `FlagF` at the control itself. -/
theorem FlagF.ptr {cS : WeakMem.Address} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : FlagF cS s c fs) : ∀ sa, LabPtr c sa → sa = cS :=
  h c fs (.refl _)

/-- **The segment's extra fragment with the flag.** -/
def ZF (cS : WeakMem.Address) (X : FragS isaLSE2) : FragS isaLSE2 := fun s c fs => FlagF cS s c fs ∧ X s c fs

/-- **`ZObl` at `ZF`** from the flag's and `X`'s. -/
theorem ZObl.flag {X : FragS isaLSE2} {cS : WeakMem.Address} {exe : _root_.Executable} {endPc : Int64}
    {ms : List TermRun.Frame → MemSide isaLSE2} {R : Region} {F : MachineData → Prop}
    {w : Hello.Child.Words} {tp sp0 : BitVec 64} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    (hf : ZObl (FlagF cS) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m)
    (hX : ZObl X exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m) :
    ZObl (ZF cS X) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m :=
  hf.and hX

/-- **The flag under `Pend`**: at every control reached from the pending
witness. (Controls between the source's own control and the witness are
not covered: see the module docstring of `A64HelloFlagZ` and row
B8-genP-hmapW-flag.) -/
theorem flag_of_pend {cS : WeakMem.Address} {Z : FragS isaLSE2} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : Pend helloSrc (fun s c fs => Z s c fs ∧ FlagF cS s c fs) s c fs) :
    ∃ c' fs', FrameRun helloSrc (c, fs) (c', fs') ∧
      ∀ c₁ fs₁, FrameRun helloSrc (c', fs') (c₁, fs₁) → ∀ sa, LabPtr c₁ sa → sa = cS :=
  let ⟨c', fs', r, _, hf⟩ := h
  ⟨c', fs', r, hf⟩

end Spike.Lib.A64.Flow.Worker.Hello.FlagZ

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.FlagZ.ZObl.flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.FlagZ.ZObl.flag
