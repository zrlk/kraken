/-
**hello.w: the loaded thread is off the root's abort phases** (AArch64; the
twin of `Spike/Lib/WakeOAb.lean` at `helloProg`, with `hti0`, the twin of
`WakeOSide.hti0_W`).

The root's abort phases are the ones hello's rows instantiate
(`A64HelloAllocPh`, `A64HelloAllocWSF.WSHF`): `AbH`, the write abort's
phase `WriteAb.Ab` at the layout's labels, and `AcH`, the threads abort's
phase over main's spawn failure (`HelloWf.AcH` at
`Worker.Hello.Child.pfxM`). hello's loaded thread, at `_start` (the code's
base `WakePh.lo`), is in neither: every pc of either phase is at a label of
the runtime's print, abort, abort stubs or `wc_main`'s spawn, all above
`_start` (`not_ab_loH`, `not_ac_loH`, from the labels' addresses in
`helloProg`, decided).

- `not_ab_loH`, `not_ac_loH`: no pc of either phase is the code's base.
- `AbH`, `AcH`: the phases at `ofPlaceW`'s labels; `wshf_abH_acH` checks
  (by `rfl`) that they are the ones `WSHF` (the rows' start level) uses.
- `hab0_H`, `hac0_H`, `hti0_H`: the loaded thread off both; `TIC AbH AcH`
  at the one-slot load (`OPremH.hti0`).
-/
import Spike.Lib.WakeOSide
import Spike.Lib.HelloOInit
import Spike.Lib.A64HelloAllocWSF

namespace Spike.Lib.HelloOAb

variable {asm : String}

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.Rt (RuntimeLayout)

section Labels

variable {lab : Label → Int64} (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → lab l = Int64.ofNat x)
include hlab

/-- **No pc of the write abort's phase is the code's base.** -/
theorem not_ab_loH {s : State} (hpc : s.st.2 = Int64.ofNat lo) : ¬ Spike.Lib.A64.WriteAb.Ab lab s := by
  refine Spike.Lib.A64.WriteAb.not_ab_of_pc ?_
  rw [hpc]
  simp only [Spike.Lib.A64.WriteAb.abPcs, Spike.Lib.A64.WriteAb.pcRet, Spike.Lib.A64.WriteAb.tailPcs,
    Spike.Lib.A64.WriteAb.failPcs, Spike.Lib.A64.WriteAb.dispEPcs, Spike.Lib.A64.WriteAb.dispTPcs,
    Spike.Lib.A64.WriteAb.g4Pcs, Spike.Lib.A64.WriteAb.stubPcs, Spike.Lib.A64.PrintD.pcSvc,
    Spike.Lib.A64.Abort.write,
    hlab ".L9_scc_rt_print.2_write" 2167544 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L9_scc_rt_print.3_chk2" 2167604 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L9_scc_rt_print.4_chk3" 2167636 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L9_scc_rt_print.6_fail" 2167692 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort" 2168032 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.0_entry" 2168052 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.2_next1" 2168088 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.4_next3" 2168124 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.6_next5" 2168160 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.7_is6" 2168180 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_write" 2168452 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L16_scc_rt_abort_write.0_entry" 2168468 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_write_exit" 2168512 (by rw [← codeT_eq]; decide +kernel)]
  decide

/-- **No pc of the threads abort's phase (over main's spawn) is the code's
base.** -/
theorem not_ac_loH {s : State} (hpc : s.st.2 = Int64.ofNat lo) :
    ¬ Spike.Lib.A64.HelloWf.AcH lab Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM s := by
  refine Spike.Lib.A64.Hello.ThreadsAb.not_ac_of_pc ?_
  rw [hpc]
  simp only [Spike.Lib.A64.Hello.ThreadsAb.acPcs, Spike.Lib.A64.Hello.ThreadsAb.pcRet,
    Spike.Lib.A64.Hello.ThreadsAb.pcSt, Spike.Lib.A64.Hello.ThreadsAb.tailPcs, Spike.Lib.A64.ThreadsAb.failPcs,
    Spike.Lib.A64.WriteAb.dispEPcs, Spike.Lib.A64.ThreadsAb.dispTPcs, Spike.Lib.A64.ThreadsAb.g5Pcs,
    Spike.Lib.A64.ThreadsAb.stubPcs, Spike.Lib.A64.Abort.threads, Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM,
    String.reduceAppend,
    hlab ".L22_wc_main.sp6" 2169740 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L22_wc_main.clone13" 2169848 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L22_wc_main.1_spawnfail5" 2169872 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort" 2168032 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.0_entry" 2168052 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.2_next1" 2168088 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.4_next3" 2168124 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.6_next5" 2168160 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.8_next7" 2168196 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.9_is8" 2168216 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_threads" 2168524 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L17_scc_rt_abort_threads.0_entry" 2168540 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_threads_exit" 2168584 (by rw [← codeT_eq]; decide +kernel)]
  decide

end Labels

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **The root's write abort phase.** -/
abbrev AbH : State → Prop := Spike.Lib.A64.WriteAb.Ab (Ly).lab

/-- **The root's threads abort phase** (main's spawn failure). -/
abbrev AcH : State → Prop := Spike.Lib.A64.HelloWf.AcH (Ly).lab Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM

/-- `AbH`, `AcH` are the phases of the rows' start level (`HelloWf.WSHF`,
`HelloWf.allocAbAcH`'s), so the rows and the root cannot drift apart. -/
theorem wshf_abH_acH (a : BitVec 64) (ar : Spike.Lib.Arena) (p : CoreTerm.Prog) (Dt Cl : State → Prop)
    (Ctx : Spike.Lib.FragS isaLSE2) (lbl : Spike.Lib.A64Consumer.Lbl) (lsize : Spike.Lib.A64Consumer.Lsize) (frM :
        TermRun.Frame) (X0 : State → Prop) (fs : List TermRun.Frame) :
    Spike.Lib.A64.HelloWf.WSHF (Ly) a ar p Dt Cl Ctx lbl lsize frM X0 fs = fun s c =>
      Spike.Lib.A64.WakeWf.W0 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) (Spike.Lib.A64.HelloPh.ownGH (Ly) a) ar p Dt (AbH hp
          i) Cl
        (AcH hp i) Ctx lbl lsize frM X0 s c fs :=
  rfl

/-- **`hti0_H`'s `hab0`**: the loaded thread is off `AbH`. -/
theorem hab0_H (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    (hhp : Scc.Sem.A64.textProgram asm = .ok SccCode.helloProg) (hlo : Λ0.code.lo = lo)
    (E : Scc.Sem.Entry) :
    ¬ AbH hp i (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) :=
  not_ab_loH (Spike.Lib.HelloOInit.hlab_H hp i hpa hhp hlo) (show Int64.ofNat Λ0.code.lo = _ by rw [hlo])

/-- **`hti0_H`'s `hac0`**: the loaded thread is off `AcH`. -/
theorem hac0_H (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    (hhp : Scc.Sem.A64.textProgram asm = .ok SccCode.helloProg) (hlo : Λ0.code.lo = lo)
    (E : Scc.Sem.Entry) :
    ¬ AcH hp i (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) :=
  not_ac_loH (Spike.Lib.HelloOInit.hlab_H hp i hpa hhp hlo) (show Int64.ofNat Λ0.code.lo = _ by rw [hlo])

/-- **`OPremH.hti0` at `AbH`, `AcH`**: `TIC` at the one-slot load. -/
theorem hti0_H (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    (hd : Scc.Sem.dataSections asm = some o.secs)
    (hhp : Scc.Sem.A64.textProgram asm = .ok SccCode.helloProg) (hlo : Λ0.code.lo = lo)
    (E : Scc.Sem.Entry) :
    ∀ d : Spike.Lib.WakeA64.Cfg, (Scc.Sem.A64.target (Scc.Sem.A64.kernel 1) E).load asm (Ly).Λ = some d →
      Spike.Lib.A64ConsumerA.TIC (AbH hp i) (AcH hp i) [] d :=
  Spike.Lib.WakePreTi.ti0_of hpa hd (hab0_H hp i hpa hhp hlo E) (hac0_H hp i hpa hhp hlo E)

end Place

/-- info: 'Spike.Lib.HelloOAb.hti0_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hti0_H

/-- info: 'Spike.Lib.HelloOAb.wshf_abH_acH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wshf_abH_acH

end Spike.Lib.HelloOAb
