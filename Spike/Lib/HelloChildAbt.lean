/-
**hello.w's child abort site** (ChildPrem row `habt` of
`Hello.SegR.ChildPrem`): at the placed layout, a state of the child's
executable at the exit call of `scc_rt_abort_write`
(`Abort.write.exit`, the label `scc_rt_abort_write_exit`) is at an abort
site of `msWH` (`msH`'s, `HelloMs.abt_H`: `PhRec.μ L`'s `writeErr` site,
`PlaceW.abortAt_eq`, resolved by `HelloCompatI.site_ofH` at
`HelloAbExit.hello_exitLabel`).

- `habt_I`: `ChildPrem.habt` at `PI`'s memory side.
-/
import Spike.Lib.HelloSegI
import Spike.Lib.HelloAbExit

namespace Spike.Lib.HelloAssemblyI

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib
open Spike.Lib.HelloMs (msH)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`ChildPrem.habt` at the placed layout**: the exit call of
`scc_rt_abort_write` is `msWH`'s `writeErr` abort site. -/
theorem habt_I (ho : o.prog = helloProg) (G0 : ιH hp i → Loc → Val → Prop) (w : ιH hp i) :
    ∀ (_ : TermRun.Frame) (s : isaLSE2.State), s.exe = (LH hp i).exe →
      s.st.2 = (_root_.Executable.labels (LH hp i).exe).label Spike.Lib.A64.Abort.write.exit →
      (Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w).abortAt s := by
  intro _ s _ hpc
  exact ⟨.writeErr, _, (PlaceW.abortAt_eq hp i .writeErr).trans
      (HelloCompatI.site_ofH hp i ho HelloAbExit.hello_exitLabel),
    by show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl⟩

/-- `habt_I` is `PI`'s `ChildPrem.habt` field verbatim. -/
example (ho : o.prog = helloProg) (G0 : ιH hp i → Loc → Val → Prop) (w : ιH hp i) {F w' tp sp0 w0 w1 w2 w3 w4 n m}
    (h : Spike.Lib.A64.Flow.Worker.Hello.SegR.ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
      (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) F w' tp sp0 w0 w1 w2 w3 w4 n m) :
    { h with habt := habt_I hp i ho G0 w } = h := rfl

end Inst

/-- info: 'Spike.Lib.HelloAssemblyI.habt_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms habt_I

end Spike.Lib.HelloAssemblyI
