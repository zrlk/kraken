/-
**hello.w: the worker's memory side with `print`'s byte step** (`msWH`, the
worker side's twin of `HelloMs.msH` at `HelloByteOutP.helloMsW`), and the
lift of the worker's rows from `msH` to it.

`msWH L G SR w` is `msH L G SR w` with `bo := ByteOutP helloSrc (SR w).lbl`
and `we := WeAb abi (WriteAb.Ab lab)` (`HelloByteOutP.helloMsW` at the
spawn record's placement and the write abort's phase from `print`'s refused
`write`, `A64WriteAb.Ab`, as hello1's print path; not the abort stub's two
system calls `Worker.AbW`, which a kernel return from `print`'s `write` never
reaches, `HelloChildSvc.printSvcWeF`; every other
field `msH`'s). `msH`'s byte step and abort justification are `MemSide`'s
defaults (none), so every row proved under `msH` is one under `msWH`
(`MemSideBW`): the thread rows at depth (`OutL.withBW`, `OutT.withBW`,
`OutTS.withBW`), the worker's segment (`SegTCS.withBW`) and so its segment
premise (`hseg_msWH`), which row 5j-misc proves at `msH`.

- `msWH`, `msWH_bo`, `msWH_we`, `msWH_K`, `msWH_G`: the memory side and its
  fields.
- `OutL.withBW`, `OutT.withBW`, `OutTS.withBW`, `SegTCS.withBW`: rows and
  segments under `ms` are ones under `ms.withBW bo we` when `ms`'s byte step
  and abort justification imply `bo` and `we`.
- `segTCS_msWH`, `hseg_msWH`: a worker segment at `msH` is one at `msWH`.
-/
import Spike.Lib.HelloByteOutP
import Spike.Lib.HelloSegTCS
import Spike.Lib.MemSideBW
import Spike.Lib.A64HelloNN
import Spike.Lib.A64WriteAb

namespace Spike.Lib.HelloMsW

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem
open Spike.Lib
open Spike.Lib.HelloSegThrS (OutTS)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloMs (msH)
open Spike.Lib.A64.Rt (RuntimeLayout)

/-! ## Rows under `withBW` -/

section BW

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
  {bo : I.State → Nat → Ctl → (Ctl → Prop) → Prop} {we : I.State → Ctl → Prop}

/-- **An `OutL` row under `ms` is one under `ms.withBW bo we`.** -/
theorem OutL.withBW {X : Frag I} {s : I.State} {c : Ctl} (h : OutL p lbl ms X s c)
    (hbo : ∀ s a c Q, ms.bo s a c Q → bo s a c Q) (hwe : ∀ s c, ms.we s c → we s c) :
    OutL p lbl (ms.withBW bo we) X s c := by
  cases h with
  | out h => exact .out (h.withBW hbo hwe)
  | ldSt kl A g x a e ty w V he ht hev hv hx hy hsa => exact .ldSt kl A g x a e ty w V he ht hev hv hx hy hsa

/-- **An `OutT` row under `ms` is one under `ms.withBW bo we`.** -/
theorem OutT.withBW {X : Frag I} {s : I.State} {c : Ctl} (h : OutT p lbl ms X s c)
    (hbo : ∀ s a c Q, ms.bo s a c Q → bo s a c Q) (hwe : ∀ s c, ms.we s c → we s c) :
    OutT p lbl (ms.withBW bo we) X s c := by
  cases h with
  | outL h => exact .outL (OutL.withBW h hbo hwe)
  | unpk k A B op g x a e ty jw he hrt hmp hop ht hh hev hv hA hX =>
    exact .unpk k A B op g x a e ty jw he hrt hmp hop ht hh hev hv hA hX
  | texit K a hK hat hd ht => exact .texit K a hK hat hd ht
  | fnc k s' c' he hr hx => exact .fnc k s' c' he hr hx

/-- **An `OutTS` row at depth** under the memory sides `ms` is one under
`(ms ·).withBW bo we`. -/
theorem OutTS.withBW {ms : List TermRun.Frame → MemSide I} {X : FragS I} {s : I.State} {c : Ctl}
    {fs : List TermRun.Frame} (h : OutTS p lbl ms X s c fs)
    (hbo : ∀ fs s a c Q, (ms fs).bo s a c Q → bo s a c Q) (hwe : ∀ fs s c, (ms fs).we s c → we s c) :
    OutTS p lbl (fun fs => (ms fs).withBW bo we) X s c fs := by
  cases h with
  | pre c₁ fs₁ hr h => exact .pre c₁ fs₁ hr (OutL.withBW h (hbo fs₁) (hwe fs₁))
  | frame s' c' fs' he hr hx => exact .frame s' c' fs' he hr hx
  | fnc k s' c' fs' he hr hx => exact .fnc k s' c' fs' he hr hx
  | top c₁ hr h => exact .top c₁ hr (OutT.withBW h (hbo []) (hwe []))

/-- **A worker segment at depth** under the memory sides `ms` is one under
`(ms ·).withBW bo we`. -/
theorem SegTCS.withBW {ms : List TermRun.Frame → MemSide I} {S P Q : FragS I} (h : SegTCS S p lbl ms P Q)
    (hbo : ∀ fs s a c Q, (ms fs).bo s a c Q → bo s a c Q) (hwe : ∀ fs s c, (ms fs).we s c → we s c) :
    SegTCS S p lbl (fun fs => (ms fs).withBW bo we) P Q :=
  let ⟨inv, hP, hS, hcl⟩ := h
  ⟨inv, hP, hS, fun s c fs hi => OutTS.withBW (hcl s c fs hi) hbo hwe⟩

end BW

/-! ## The worker's memory side -/

section Ms

variable {ι : Type} (L : RuntimeLayout) (G : ι → Loc → Val → Prop) (SR : ι → Inv2Core.SpawnRec)

/-- **The worker's memory side at record `w`**: `msH` with `print`'s byte
step and the write abort's justification at the write abort's phase
`WriteAb.Ab` (`HelloByteOutP.helloMsW`). -/
abbrev msWH (w : ι) : MemSide isaLSE2 :=
  HelloByteOutP.helloMsW L (G w) (SR w).lbl (SR w).lsize
    (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels L.exe).label)

/-- `msWH` is `msH` with `bo`, `we` set. -/
theorem msWH_eq (w : ι) :
    msWH L G SR w = (msH L G SR w).withBW (HelloByteOutP.ByteOutP HelloSrc.helloSrc (SR w).lbl)
      (A64ConsumerA.WeAb Scc.Sem.A64.abi
        (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels L.exe).label)) := rfl

theorem msWH_bo (w : ι) : (msWH L G SR w).bo = HelloByteOutP.ByteOutP HelloSrc.helloSrc (SR w).lbl := rfl

theorem msWH_we (w : ι) :
    (msWH L G SR w).we = A64ConsumerA.WeAb Scc.Sem.A64.abi (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels L.exe).label) := rfl

/-- `msWH`'s kernel model is `msH`'s. -/
theorem msWH_K (w : ι) : (msWH L G SR w).K = (msH L G SR w).K := rfl

/-- `msWH`'s global invariant is `msH`'s. -/
theorem msWH_G (w : ι) : (msWH L G SR w).G = (msH L G SR w).G := rfl

/-- **A worker segment at `msH` is one at `msWH`** (`msH`'s byte step and
abort justification are none). -/
theorem segTCS_msWH {S P Q : FragS isaLSE2} {w : ι}
    (h : SegTCS S HelloSrc.helloSrc (SR w).lbl (fun _ => msH L G SR w) P Q) :
    SegTCS S HelloSrc.helloSrc (SR w).lbl (fun _ => msWH L G SR w) P Q :=
  SegTCS.withBW h (fun _ _ _ _ _ h => h.elim) fun _ _ _ h => h.elim

/-- **The worker's segment premise at `msWH`** from row 5j-misc's at `msH`. -/
theorem hseg_msWH {exe : _root_.Executable} {endPc : Int64} {P Z : ι → FragS isaLSE2}
    (hseg : ∀ w, SegTCS (fun s c fs => Spike.Lib.A64.Flow.Worker.NNH exe endPc s ∧ Z w s c fs) HelloSrc.helloSrc
      (SR w).lbl (fun _ => msH L G SR w) (P w) (fun _ _ _ => False)) :
    ∀ w, SegTCS (fun s c fs => Spike.Lib.A64.Flow.Worker.NNH exe endPc s ∧ Z w s c fs) HelloSrc.helloSrc
      (SR w).lbl (fun _ => msWH L G SR w) (P w) (fun _ _ _ => False) :=
  fun w => segTCS_msWH L G SR (hseg w)

end Ms

/-- info: 'Spike.Lib.HelloMsW.hseg_msWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hseg_msWH

end Spike.Lib.HelloMsW
