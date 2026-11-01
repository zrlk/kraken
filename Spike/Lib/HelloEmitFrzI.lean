/-
**hello.w on AArch64: the worker's buffer frozen at the placed instance**
(C4, row B8-emit-frz). `HelloEmitStep.ByteFrz`'s facts at
`HelloAssemblyI`'s instance (records `ιH`, spawn data `SRH`, location data
`PaH`, the buffer `lBH` of `2` words): the layout well formed
(`WakeQ.hwf_ofPlaceOK`), and at the memory relation of the record's
placement the buffer's `2` words inside its label, their target words
frozen (`HelloOkHR.okHR_frz`, `BufPl`'s `2 ≤ lsize`).

- `byteFrz_I`: the facts, stated over `SRH`/`PaH` (the relation `QH`'s
  `SR`/`P` and the worker side `DH`'s `bufL`/`mB` by definition; the
  `example` below checks them at `QH`/`DH`).
-/
import Spike.Lib.HelloAssemblyI

namespace Spike.Lib.HelloEmitFrzI

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.WakeInst
open Spike.Lib.HelloAssemblyI (LH ιH SRH PaH μH DH QH)
open Spike.Lib.HelloOkW (lBH)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **The buffer is frozen at the instance** (row B8-emit-frz): the layout
well formed, and at the memory relation of a record's placement the
buffer's `2` words inside its label with their target words frozen. -/
theorem byteFrz_I (E : Entry) (asm : String) :
    (LH hp i).Λ.WF ∧ ∀ (w : ιH hp i) (b0 : Nat) (ts : Nat → Option Nat) (tm : Memory) (sm : WeakMem.Memory)
      (tp tq sp : List Nat), MemRelP (LH hp i).Λ (SRH hp i w).lbl (SRH hp i w).lsize ts tm sm tp tq sp →
      (SRH hp i w).lbl lBH = some b0 →
      2 ≤ (SRH hp i w).lsize lBH ∧ ∀ k < 2, (PaH hp i E asm w).frz (wordLoc (b0 + 8 * k)) := by
  have hwf := WakeQ.hwf_ofPlaceOK hp i
  refine ⟨hwf, fun w b0 ts tm sm tp tq sp hm hb => ⟨(HelloOkHR.okHR_bufAt w hb).2.1, fun k hk => ?_⟩⟩
  exact HelloOkHR.okHR_frz w hb rfl rfl rfl rfl hm hwf hk

end Inst

/-- `byteFrz_I` at the relation `QH` and the worker side `DH` (their `SR`,
`P`, `bufL`, `mB` are `SRH`, `PaH`, `lBH`, `2` by definition). -/
example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (G0 : ιH hp i → Loc → Val → Prop) (P Z X : ιH hp i → FragS isaLSE2)
    (hseg : ∀ w, HelloSegTCSX.SegTCSX (fun s c fs => A64.Flow.Worker.NNH (LH hp i).exe (HelloAssemblyI.endH hp i) s ∧
      Z w s c fs) (X w) HelloSrc.helloSrc (SRH hp i w).lbl
      (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (HelloAssemblyI.GH hp i G0) (SRH hp i) w) (P w) (fun _ _ _ => False))
    {arch : WeakMem.Arch} {R1 : WakeA64.Cfg → TermRun.Cfg → Prop} {E : Entry} {asm : String}
    (hpa : textProgram asm = .ok o.prog) {passT : AArch64.State → Prop} {Dd : HelloO.ODataH} {r1c : Range} :
    let Q := QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c
    let D := DH hp i G0 P Z X hseg
    (LH hp i).Λ.WF ∧ ∀ w b0 ts tm sm tp tq sp, MemRelP (LH hp i).Λ (Q.SR w).lbl (Q.SR w).lsize ts tm sm tp tq sp →
      (Q.SR w).lbl (D.bufL w) = some b0 →
      D.mB w ≤ (Q.SR w).lsize (D.bufL w) ∧ ∀ k < D.mB w, (Q.P w).frz (wordLoc (b0 + 8 * k)) :=
  byteFrz_I hp i E asm

/-- info: 'Spike.Lib.HelloEmitFrzI.byteFrz_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms byteFrz_I

end Spike.Lib.HelloEmitFrzI
