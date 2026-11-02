/-
**hello.w's child abort site on x86-64** (the twin of `Spike/Lib/HelloChildAbt.lean`; the child premise `habt`
of `Hello.SegR.ChildPrem`): at the placed layout, a state of the child's executable at the exit call of
`scc_rt_abort_write` (`Abort.write.exit`, the label `scc_rt_abort_write_exit`) is at an abort site of `msWH`
(`msH`'s at `PhRec.μ L`: its `writeErr` site, `PlaceWX.abortAt_eq`, resolved by `X64HelloCompatI.site_ofH` at
`X64HelloAbExit.hello_exitLabel`).

- `habt_I`: `ChildPrem.habt` at the instance's memory side.

## Differences from the AArch64 version

- Over `PlaceWX` and `X64HelloAssemblyI`'s instance data; `X64HelloCompatI.site_ofH` reads the placed program
  `o.prog` itself, so `habt_I` takes no `ho : o.prog = helloCells` (AArch64's `ho`), and the exit label is
  rewritten to `Link.abortName` by `PlaceWX.abortLbl_of_placeWX`.
- The module imports `X64HelloAssemblyI` and `X64HelloAbExit` (AArch64: through `HelloSegI`, which `habt_I`
  does not use).
-/
import Spike.Lib.X64HelloAssemblyI
import Spike.Lib.X64HelloAbExit
import Spike.Lib.X64HelloWorkerSegP

namespace Spike.Lib.X64HelloAssemblyI

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`ChildPrem.habt` at the placed layout**: the exit call of
`scc_rt_abort_write` is `msWH`'s `writeErr` abort site. -/
theorem habt_I (G0 : ιH hp i → Loc → Val → Prop) (w : ιH hp i) :
    ∀ (_ : TermRun.Frame) (s : isa.State), s.exe = (LH hp i).exe →
      s.st.2 = (_root_.Executable.labels (LH hp i).exe).label Spike.Lib.X64.Abort.write.exit →
      (Spike.Lib.X64HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w).abortAt s := by
  intro _ s _ hpc
  have h := X64HelloCompatI.site_ofH hp i (X64HelloAbExit.hello_exitLabel Λ0)
  rw [PlaceWX.abortLbl_of_placeWX hp] at h
  exact ⟨.writeErr, _, (PlaceWX.abortAt_eq hp i .writeErr).trans h,
    by show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl⟩

/-- `habt_I` is the instance's `ChildPrem.habt` field verbatim. -/
example (G0 : ιH hp i → Loc → Val → Prop) (w : ιH hp i) {F w' tp sp0 w0 w1 w2 w3 w4 n m}
    (h : Spike.Lib.X64.Flow.Worker.Hello.SegR.ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
      (fun _ => Spike.Lib.X64HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) F w' tp sp0 w0 w1 w2 w3 w4 n m) :
    { h with habt := habt_I hp i G0 w } = h := rfl

end Inst

/-- info: 'Spike.Lib.X64HelloAssemblyI.habt_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms habt_I

end Spike.Lib.X64HelloAssemblyI
