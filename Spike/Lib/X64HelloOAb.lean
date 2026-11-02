/-
**hello.w on x86-64: the loaded thread is off the root's abort phases** (the twin of
`Spike/Lib/HelloOAb.lean`; the hello twin of `Spike/Lib/X64WakeOAb.lean`, with `hti0_H`, the hello use of
`X64WakeOSide.hti0_W`).

The root's abort phases are the ones hello's rows instantiate (`X64HelloAllocPh`, `X64HelloAllocWSF.WSHF`):
`AbH`, the write abort's phase `WriteAb.Ab` at the layout's labels, and `AcH`, the threads abort's phase over
main's spawn failure (`Hello.ThreadsAb.AcH` at `HelloPh.StartWf.pfxM`). hello's loaded thread, at `_start` (the
code's base `HelloPh.lo`), is in neither: every pc of either phase is at a label of the runtime's print, abort,
abort stubs or `wc_main`'s spawn, all above `_start` (`not_ab_loH`, `not_ac_loH`, from the labels' addresses in
`helloCells`, decided).

- `not_ab_loH`, `not_ac_loH`: no pc of either phase is the code's base.
- `AbH`, `AcH`: the phases at `ofPlaceWX`'s labels; `wshf_abH_acHg` checks (by `rfl`) that they are the ones
  `WSHFg` (the rows' start level at any owned words) uses; `wshf_abH_acH`: it at `ownGH` (`WSHF`).
- `hab0_H`, `hac0_H`, `hti0_H`: the loaded thread off both; `TIC AbH AcH` at the one-slot load.

## Differences from the AArch64 version

- The layout is `RuntimeLayout.ofPlaceWX` at `PlaceWX`; the parses are `cellsOf asm = some o.prog` and
  `= some helloCells` (`hpa`, `hhp`), the data `dataSections asm.text = some o.secs` (AArch64:
  `textProgram asm = .ok …`, `dataSections asm`); labels are `codeLabel lo helloCells`
  (`X64HelloOInit.hlab_H`).
- The threads phase is `Hello.ThreadsAb.AcH lab ".Lwc_main"` (the spawn's `clone` at `.x25 + 94`, the store at
  `.x26`); its pcs include the `je` at `pcJe`, and its labels are `.x25`, `.x26`, `.spawnfail5` (AArch64:
  `.sp6`, `.clone13`, `.1_spawnfail5`).
- The write phase's pcs are at the dispatcher's `.is6` and the abort stubs' `entry` labels, as wake's
  `X64WakeOAb.not_ab_lo`.
-/
import Spike.Lib.X64HelloOInit
import Spike.Lib.X64HelloAllocWSF
import Spike.Lib.X64WakeOSide

namespace Spike.Lib.X64HelloOAb

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)

section Labels

variable {lab : Label → Int64} (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x)
include hlab

/-- **No pc of the write abort's phase is the code's base.** -/
theorem not_ab_loH {s : State} (hpc : s.st.2 = Int64.ofNat lo) : ¬ Spike.Lib.X64.WriteAb.Ab lab s := by
  refine Spike.Lib.X64.WriteAb.not_ab_of_pc ?_
  rw [hpc]
  simp only [Spike.Lib.X64.WriteAb.abPcs, Spike.Lib.X64.WriteAb.pcRet, Spike.Lib.X64.WriteAb.tailPcs,
    Spike.Lib.X64.WriteAb.failPcs, Spike.Lib.X64.WriteAb.dispEPcs, Spike.Lib.X64.WriteAb.dispTPcs,
    Spike.Lib.X64.WriteAb.g4Pcs, Spike.Lib.X64.WriteAb.stubPcs, Spike.Lib.X64.Abort.write,
    hlab ".Lscc_rt_print.write" 4202070 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_print.chk2" 4202114 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_print.chk3" 4202132 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_print.fail" 4202185 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort" 4202486 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.entry" 4202498 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next1" 4202522 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next3" 4202549 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next5" 4202576 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.is6" 4202594 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_write" 4202836 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort_write.entry" 4202844 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_write_exit" 4202896 (by rw [← codeT_eq]; decide +kernel)]
  decide

/-- **No pc of the threads abort's phase (over main's spawn) is the code's base.** -/
theorem not_ac_loH {s : State} (hpc : s.st.2 = Int64.ofNat lo) :
    ¬ Spike.Lib.X64.Hello.ThreadsAb.AcH lab Spike.Lib.X64.HelloPh.StartWf.pfxM s := by
  refine Spike.Lib.X64.Hello.ThreadsAb.not_ac_of_pc ?_
  rw [hpc]
  simp only [Spike.Lib.X64.Hello.ThreadsAb.acPcs, Spike.Lib.X64.Hello.ThreadsAb.pcRet,
    Spike.Lib.X64.Hello.ThreadsAb.pcJe, Spike.Lib.X64.Hello.ThreadsAb.cloneAt, Spike.Lib.X64.Hello.ThreadsAb.pcSt,
    Spike.Lib.X64.Hello.ThreadsAb.tailPcs, Spike.Lib.X64.ThreadsAb.failPcs, Spike.Lib.X64.WriteAb.dispEPcs,
    Spike.Lib.X64.ThreadsAb.dispTPcs, Spike.Lib.X64.ThreadsAb.g5Pcs, Spike.Lib.X64.ThreadsAb.stubPcs,
    Spike.Lib.X64.Abort.threads, Spike.Lib.X64.HelloPh.StartWf.pfxM, String.reduceAppend,
    hlab ".Lwc_main.x25" 4203774 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lwc_main.x26" 4203875 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lwc_main.spawnfail5" 4203897 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort" 4202486 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.entry" 4202498 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next1" 4202522 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next3" 4202549 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next5" 4202576 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next7" 4202603 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.is8" 4202621 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_threads" 4202904 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort_threads.entry" 4202912 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_threads_exit" 4202964 (by rw [← codeT_eq]; decide +kernel)]
  decide

end Labels

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The root's write abort phase.** -/
abbrev AbH : State → Prop := Spike.Lib.X64.WriteAb.Ab (Ly).lab

/-- **The root's threads abort phase** (main's spawn failure). -/
abbrev AcH : State → Prop := Spike.Lib.X64.Hello.ThreadsAb.AcH (Ly).lab Spike.Lib.X64.HelloPh.StartWf.pfxM

/-- `AbH`, `AcH` are the phases of the rows' start level at any owned words `own` (`X64HelloAllocWSF.WSHFg`), so
the rows and the root cannot drift apart. -/
theorem wshf_abH_acHg (own : Spike.Lib.X64Consumer.Own) (ar : Spike.Lib.Arena) (p : CoreTerm.Prog)
    (Dt Cl : State → Prop) (Ctx : Spike.Lib.FragS isa) (lbl : Spike.Lib.X64Consumer.Lbl)
    (lsize : Spike.Lib.X64Consumer.Lsize) (frM : TermRun.Frame) (X0 : State → Prop) (fs : List TermRun.Frame) :
    Spike.Lib.X64.HelloWf.WSHFg own (Ly) ar p Dt Cl Ctx lbl lsize frM X0 fs = fun s c =>
      Spike.Lib.X64.WakeWf.W0 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) own ar p Dt
        (AbH hp i) Cl (AcH hp i) Ctx lbl lsize frM X0 s c fs :=
  rfl

/-- `AbH`, `AcH` are the phases of the rows' start level (`X64HelloAllocWSF.WSHF`): `wshf_abH_acHg` at `ownGH`. -/
theorem wshf_abH_acH (a : BitVec 64) (ar : Spike.Lib.Arena) (p : CoreTerm.Prog) (Dt Cl : State → Prop)
    (Ctx : Spike.Lib.FragS isa) (lbl : Spike.Lib.X64Consumer.Lbl) (lsize : Spike.Lib.X64Consumer.Lsize)
    (frM : TermRun.Frame) (X0 : State → Prop) (fs : List TermRun.Frame) :
    Spike.Lib.X64.HelloWf.WSHF (Ly) a ar p Dt Cl Ctx lbl lsize frM X0 fs = fun s c =>
      Spike.Lib.X64.WakeWf.W0 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.HelloPh.ownGH (Ly) a) ar p Dt
        (AbH hp i) Cl (AcH hp i) Ctx lbl lsize frM X0 s c fs :=
  wshf_abH_acHg hp i (Spike.Lib.X64.HelloPh.ownGH (Ly) a) ar p Dt Cl Ctx lbl lsize frM X0 fs

/-- **`hti0_H`'s `hab0`**: the loaded thread is off `AbH`. -/
theorem hab0_H {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some helloCells) (hlo : Λ0.code.lo = lo) (E : Scc.Sem.Entry) :
    ¬ AbH hp i (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) :=
  not_ab_loH (Spike.Lib.X64HelloOInit.hlab_H hp i hpa hhp hlo) (show Int64.ofNat Λ0.code.lo = _ by rw [hlo])

/-- **`hti0_H`'s `hac0`**: the loaded thread is off `AcH`. -/
theorem hac0_H {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some helloCells) (hlo : Λ0.code.lo = lo) (E : Scc.Sem.Entry) :
    ¬ AcH hp i (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) :=
  not_ac_loH (Spike.Lib.X64HelloOInit.hlab_H hp i hpa hhp hlo) (show Int64.ofNat Λ0.code.lo = _ by rw [hlo])

/-- **`OPremH.hti0` at `AbH`, `AcH`**: `TIC` at the one-slot load (`X64WakeOSide.hti0_W`). -/
theorem hti0_H {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hd : Scc.Sem.dataSections asm.text = some o.secs)
    (hhp : Scc.Sem.X64.cellsOf asm = some helloCells) (hlo : Λ0.code.lo = lo) (E : Scc.Sem.Entry) :
    ∀ d : Spike.Lib.X64WakeA64.Cfg, (Scc.Sem.X64.target (Scc.Sem.X64.kernel 1) E).load asm (Ly).Λ = some d →
      Spike.Lib.X64ConsumerA.TIC (AbH hp i) (AcH hp i) [] d :=
  Spike.Lib.X64WakeOSide.hti0_W hp i hpa hd E (hab0_H hp i hpa hhp hlo E) (hac0_H hp i hpa hhp hlo E)

end Place

end Spike.Lib.X64HelloOAb

/-- info: 'Spike.Lib.X64HelloOAb.not_ab_loH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOAb.not_ab_loH

/-- info: 'Spike.Lib.X64HelloOAb.not_ac_loH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOAb.not_ac_loH

/-- info: 'Spike.Lib.X64HelloOAb.hti0_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOAb.hti0_H

/-- info: 'Spike.Lib.X64HelloOAb.wshf_abH_acH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOAb.wshf_abH_acH

/-- info: 'Spike.Lib.X64HelloOAb.wshf_abH_acHg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOAb.wshf_abH_acHg
