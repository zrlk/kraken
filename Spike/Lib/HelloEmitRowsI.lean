/-
**hello.w's emit rows at the placed instance** (rows
emit-(a), emit-(b) of `HelloEmitStep.post_byte`): at the worker side
`HelloAssemblyI.DH` (`helloDH`, its memory side `HelloMsW.msWH`, `print`'s
byte step) and the relation `QH`:

- `boH` (row emit-(a)): the worker's byte step is `ByteOutP` at its
  placement, at every stack of frames.
- `lblH` (row emit-(b)): the worker's placement is its spawn record's.
- `boH_ex` (non-vacuity of (a)): at the published `print` loop's control
  `PrintCP … k` (`HelloEmitEx.printCP_ex`, it exists for every `k ≤ 13`) on
  hello's buffer placed at `b`, byte `b + k` has the byte step into
  `PrintCP … (k + 1)` (`HelloEmitEx.byteOutP_printCP`).
-/
import Spike.Lib.HelloAssemblyI
import Spike.Lib.HelloEmitEx

namespace Spike.Lib.HelloAssemblyI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.HelloMs (msH)
open Spike.Lib.HelloOkW (lBH)
open Spike.Lib.HelloO (ODataH)
open Spike.Lib.HelloByteOutP (ByteOutP)
open Spike.Lib.HelloPrintSrcPub (PrintCP)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)
  (P Z X : ιH hp i → FragS isaLSE2)
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w) helloSrc (SRH hp i w).lbl
    (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (P w) (fun _ _ _ => False))

/-- **Row emit-(a)**: the worker's byte step is `ByteOutP` at its placement. -/
theorem boH : ∀ w fs, ((DH hp i G0 P Z X hseg).ms w fs).bo = ByteOutP helloSrc ((DH hp i G0 P Z X hseg).lbl w) :=
  fun _ _ => rfl

/-- **Row emit-(b)**: the worker's placement is its spawn record's. -/
theorem lblH {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {E : Entry} {asm : String}
    (hpa : textProgram asm = .ok o.prog) (passT : State → Prop) (Dd : ODataH) (r1c : Range) :
    ∀ w, (DH hp i G0 P Z X hseg).lbl w = ((QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c).SR w).lbl :=
  fun _ => rfl

/-- **Row emit-(a) is inhabited**: at `print`'s published loop on hello's
buffer (placed at `b`, the locative `pw`, `13` bytes), every byte `k < 13`
has a control `PrintCP … k` whose byte step under the worker's memory side
lands in `PrintCP … (k + 1)`. -/
theorem boH_ex (w : ιH hp i) (fs : List TermRun.Frame) (s : isaLSE2.State) {pw wn : TermRun.Word} {b : Nat}
    (hpw : pw.val = .loc ⟨lBH, 0⟩ 0) (hl : (SRH hp i w).lbl lBH = some b) (hwn : wn.val = .num 13)
    (k : Nat) (hk : k < 13) :
    ∃ c1, PrintCP pw wn 13 2 k c1 ∧
      ((DH hp i G0 P Z X hseg).ms w fs).bo s (b + k) c1 (PrintCP pw wn 13 2 (k + 1)) := by
  obtain ⟨c1, hc⟩ := HelloEmitEx.printCP_ex hwn k (by omega)
  exact ⟨c1, hc, HelloEmitEx.byteOutP_printCP (s := s) hpw hl hwn (by simp only [Spike.Lib.PrintSrc.printN]; omega) hc⟩

end Inst

end Spike.Lib.HelloAssemblyI

/-- info: 'Spike.Lib.HelloAssemblyI.boH_ex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.boH_ex
