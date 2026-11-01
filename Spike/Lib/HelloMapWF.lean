/-
**`hmapW` at `helloDRF`** (hello.w, AArch64): the root's `hmapW` at
the worker's side `HelloWorkerRRXF.helloDRF` (the `DH` of the assembly's switch). `HelloHaltMapW.hmapW_flagH`'s
`hflag` is `helloDRF_flag` verbatim (`FlagZ.FlagF (cS w)` is its body: every control a frame run reaches accesses
no untagged locative but `cS w`); `hl`, `hT`, `hsh` are the record's `GhOK` facts (`cS w` a word of a placed label,
`cT w` its target word, shared).

- `hmapW_DRF`: `hmapW` at `helloDRF` for any records, memory sides mapped in `K0 Λ'` (`hmp`), and the flag's label,
  target word and sharing per record (`hl`, `hT`, `hsh`); `helloDRF`'s abort-fact arguments `hlab`, `hμ` implicit.
- `hmapW_DRF_H`: the same at the placed instance (`ιH hp i`, `SRH`'s labels, `msWH` at `GH`, `cS w := w.1.cS`):
  `hmp` by `mp_msWH`, `hl`/`hT`/`hsh` from `okHR`'s `GhOK` (`w.2.1`). Its premises are only `helloDRF`'s own
  (with `hlab`, `hμ` implicit).
-/
import Spike.Lib.HelloWorkerRRXF
import Spike.Lib.HelloHaltMapW
import Spike.Lib.HelloAssemblyI

namespace Spike.Lib.HelloMapWF

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.A64Consumer (K0)
open Spike.Lib.HelloWorkerRRXF (helloDRF helloDRF_flag)
open Spike.Lib.HelloAssemblyI (LH ιH SRH GH)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

variable {ι : Type} {Λ : Scc.Sem.Layout} {hI : Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid Λ}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat} {SR : ι → SpawnRec}
  {lbl : ι → WeakMem.AllocLabel → Option Nat} {ms : ι → List TermRun.Frame → MemSide isaLSE2}
  {cS : ι → WeakMem.Address} {hp : Lays exe helloProg kp} {hend : endPc = endOf exe helloProg kp}
  {μ : Marks} {hlab : ∀ l x, Scc.Cert.Link.A64.codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x}
  {hμ : Spike.Lib.A64.Flow.Worker.Hello.AbObl.MarksL μ (_root_.Executable.labels exe).label}
  {hK : ∀ w fs, (ms w fs).K = some abi}
  {cw : ι → TermRun.Word} {bufL : ι → WeakMem.AllocLabel} {nB mB : ι → Nat}

/-- **`hmapW` at `helloDRF`** (module doc): `hmapW_flagH` with `hflag := helloDRF_flag`. -/
theorem hmapW_DRF {Λ' : Scc.Sem.Layout} (hmp : ∀ w fs L wr, (ms w fs).mp L wr → mapped (K0 Λ') wr L = true)
    {cT : ι → Loc} {b : ι → Nat} (hl : ∀ w, lbl w (cS w).label = some (b w))
    (hT : ∀ w, cT w = wordLoc (b w + 8 * (cS w).offset)) (hsh : ∀ w, Consumer1.LocIn Λ'.shared (cT w)) :
    ∀ w s c fs, (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w s c fs →
      abi.atSys s = false → ∀ e, isaLSE2.exec s = some e → ¬ Touches (fun l w => mapped (K0 Λ') w l = false) e :=
  HelloHaltMapW.hmapW_flagH hK hmp (fun w s c fs h => helloDRF_flag hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK
    cw bufL nB mB w s c fs h) hl hT hsh

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λp : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λp o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`hmapW` at `helloDRF` at the placed instance** (module doc): the records `ιH hpw i`, their labels `SRH`'s,
memory sides `msWH` at `GH hpw i G0`, flag `w.1.cS`; mapped in `K0` of the placed layout. -/
theorem hmapW_DRF_H {Λ : Scc.Sem.Layout} {hI : Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid Λ}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {hp : Lays exe helloProg kp} {hend : endPc = endOf exe helloProg kp}
    {μ : Marks} {hlab : ∀ l x, Scc.Cert.Link.A64.codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
      (_root_.Executable.labels exe).label l = Int64.ofNat x}
    {hμ : Spike.Lib.A64.Flow.Worker.Hello.AbObl.MarksL μ (_root_.Executable.labels exe).label}
    (G0 : ιH hpw i → Loc → Val → Prop) {cw : ιH hpw i → TermRun.Word} {bufL : ιH hpw i → WeakMem.AllocLabel}
    {nB mB : ιH hpw i → Nat} :
    ∀ w s c fs, (helloDRF hI exe endPc kp (SRH hpw i) (fun w => (SRH hpw i w).lbl)
        (fun w _ => Spike.Lib.HelloMsW.msWH (LH hpw i) (GH hpw i G0) (SRH hpw i) w) (fun w => w.1.cS) hp hend
        hlab hμ (fun _ _ => rfl) cw bufL nB mB).Wi w s c fs →
      abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
        ¬ Touches (fun l w => mapped (K0 (LH hpw i).Λ) w l = false) e :=
  HelloHaltMapW.hmapW_ofH (fun _ _ => rfl) (fun w _ _ _ h => HelloHaltMapW.mp_msWH w h)
    fun w s c fs h c₁ fs₁ hr => by
      obtain ⟨b, hl, -, hT⟩ := w.2.1.2.2.2.1
      exact Spike.Lib.WakeLabMapped.labMapped_flagB
        (helloDRF_flag hI exe endPc kp _ _ _ _ hp hend hlab hμ _ cw bufL nB mB w s c fs h c₁ fs₁ hr) hl hT
        w.2.1.2.2.2.2

end Spike.Lib.HelloMapWF

/-- info: 'Spike.Lib.HelloMapWF.hmapW_DRF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMapWF.hmapW_DRF

/-- info: 'Spike.Lib.HelloMapWF.hmapW_DRF_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMapWF.hmapW_DRF_H
