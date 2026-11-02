/-
**hello.w on x86-64: the worker's buffer frozen at the placed instance**
(the twin of `Spike/Lib/HelloEmitFrzI.lean`). `ByteFrz`'s facts at
`X64HelloAssemblyI`'s instance (records `ιH`, spawn data `SRH`, location
data `PaH`, the buffer `lBH` of `2` words): the layout well formed
(`X64WakeQ.hwf_ofPlaceOK`), and at the memory relation of the record's
placement the buffer's `2` words inside its label, their target words
frozen (`X64HelloOkHR.okHR_frz`, `BufPl`'s `2 ≤ lsize`).

- `byteFrz_I`: the facts, stated over `SRH`/`PaH` (the relation `QH`'s
  `SR`/`P` and the worker side `DH`'s `bufL`/`mB` by definition; the
  `example` below checks them at `QH`/`DH`).

## Differences from the AArch64 version

- The instance is placed by `PlaceWX` (`Scc.Cert.PlaceOK.X64.Out`), the
  target's assembly is an `Asm` (`cellsOf asm = some o.prog` for `QH`),
  and the fragments are over `isa` (AArch64: `PlaceW`, `String`,
  `textProgram`, `isaLSE2`). The proof is the same.
-/
import Spike.Lib.X64HelloAssemblyI

namespace Spike.Lib.X64HelloEmitFrzI

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64WakeInst
open Spike.Lib.X64HelloAssemblyI (LH ιH SRH PaH μH DH QH)
open Spike.Lib.X64HelloOkW (lBH)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **The buffer is frozen at the instance**: the layout well formed, and
at the memory relation of a record's placement the buffer's `2` words
inside its label with their target words frozen. -/
theorem byteFrz_I (E : Entry) (asm : Asm) :
    (LH hp i).Λ.WF ∧ ∀ (w : ιH hp i) (b0 : Nat) (ts : Nat → Option Nat) (tm : Memory) (sm : WeakMem.Memory)
      (tp tq sp : List Nat), MemRelP (LH hp i).Λ (SRH hp i w).lbl (SRH hp i w).lsize ts tm sm tp tq sp →
      (SRH hp i w).lbl lBH = some b0 →
      2 ≤ (SRH hp i w).lsize lBH ∧ ∀ k < 2, (PaH hp i E asm w).frz (wordLoc (b0 + 8 * k)) := by
  have hwf := X64WakeQ.hwf_ofPlaceOK hp i
  refine ⟨hwf, fun w b0 ts tm sm tp tq sp hm hb => ⟨(X64HelloOkHR.okHR_bufAt w hb).2.1, fun k hk => ?_⟩⟩
  exact X64HelloOkHR.okHR_frz w hb rfl rfl rfl rfl hm hwf hk

end Inst

/-- `byteFrz_I` at the relation `QH` and the worker side `DH` (their `SR`,
`P`, `bufL`, `mB` are `SRH`, `PaH`, `lBH`, `2` by definition). -/
example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (G0 : ιH hp i → Loc → Val → Prop) (P Z X : ιH hp i → FragS isa)
    (hseg : ∀ w, HelloSegTCSX.SegTCSX (fun s c fs => X64.Flow.Worker.NNH (LH hp i).exe
      (X64HelloAssemblyI.endH hp i) s ∧ Z w s c fs) (X w) X64HelloSrc.helloSrc (SRH hp i w).lbl
      (fun _ => Spike.Lib.X64HelloOwnLift.msWHX (LH hp i) (X64HelloAssemblyI.GH hp i G0) (SRH hp i) w) (P w)
      (fun _ _ _ => False))
    {arch : WeakMem.Arch} {R1 : X64WakeA64.Cfg → TermRun.Cfg → Prop} {E : Entry} {asm : Asm}
    (hpa : cellsOf asm = some o.prog) {passT : X64.State → Prop} {Dd : X64HelloO.ODataH} {r1c : Range} :
    let Q := QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c
    let D := DH hp i G0 P Z X hseg
    (LH hp i).Λ.WF ∧ ∀ w b0 ts tm sm tp tq sp, MemRelP (LH hp i).Λ (Q.SR w).lbl (Q.SR w).lsize ts tm sm tp tq sp →
      (Q.SR w).lbl (D.bufL w) = some b0 →
      D.mB w ≤ (Q.SR w).lsize (D.bufL w) ∧ ∀ k < D.mB w, (Q.P w).frz (wordLoc (b0 + 8 * k)) :=
  byteFrz_I hp i E asm

/-- info: 'Spike.Lib.X64HelloEmitFrzI.byteFrz_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms byteFrz_I

end Spike.Lib.X64HelloEmitFrzI
