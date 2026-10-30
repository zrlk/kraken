/-
**The loaded thread is off the root's abort phases** (AArch64):
wake's loaded thread, at `_start` (the code's base `WakePh.lo`), is in
neither `WakeOD.AbW` (the write abort's phase) nor `WakeOD.AcW` (the threads
abort's phase over main's spawn failure): every pc of either phase is at a
label of the runtime's print, abort, abort stubs or `wc_main`'s spawn, all
above `_start` (`not_ab_lo`, `not_ac_lo`, from the labels' addresses in
`wakeProg`, decided). These are `WakeOSide.hti0_W`'s `hab0`, `hac0`
(`hab0_W`, `hac0_W`).
-/
import Spike.Lib.WakeOD
import Spike.Lib.A64ThreadsAb

namespace Spike.Lib.WakeOAb

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.Rt (RuntimeLayout)

section Labels

variable {lab : Label → Int64} (hlab : ∀ l x, codeOf lo wakeProg l = some x → lab l = Int64.ofNat x)
include hlab

/-- **No pc of the write abort's phase is the code's base.** -/
theorem not_ab_lo {s : State} (hpc : s.st.2 = Int64.ofNat lo) : ¬ Spike.Lib.A64.WriteAb.Ab lab s := by
  refine Spike.Lib.A64.WriteAb.not_ab_of_pc ?_
  rw [hpc]
  simp only [Spike.Lib.A64.WriteAb.abPcs, Spike.Lib.A64.WriteAb.pcRet, Spike.Lib.A64.WriteAb.tailPcs,
    Spike.Lib.A64.WriteAb.failPcs, Spike.Lib.A64.WriteAb.dispEPcs, Spike.Lib.A64.WriteAb.dispTPcs,
    Spike.Lib.A64.WriteAb.g4Pcs, Spike.Lib.A64.WriteAb.stubPcs, Spike.Lib.A64.PrintD.pcSvc,
    Spike.Lib.A64.Abort.write,
    hlab ".L9_scc_rt_print.2_write" 2167508 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L9_scc_rt_print.3_chk2" 2167568 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L9_scc_rt_print.4_chk3" 2167600 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L9_scc_rt_print.6_fail" 2167656 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort" 2167996 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.0_entry" 2168016 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.2_next1" 2168052 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.4_next3" 2168088 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.6_next5" 2168124 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.7_is6" 2168144 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_write" 2168416 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L16_scc_rt_abort_write.0_entry" 2168432 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_write_exit" 2168476 (by rw [← codeT_eq]; decide +kernel)]
  decide

/-- **No pc of the threads abort's phase (over main's spawn) is the code's
base.** -/
theorem not_ac_lo {s : State} (hpc : s.st.2 = Int64.ofNat lo) :
    ¬ Spike.Lib.A64.ThreadsAb.Ac lab Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM s := by
  refine Spike.Lib.A64.ThreadsAb.not_ac_of_pc ?_
  rw [hpc]
  simp only [Spike.Lib.A64.ThreadsAb.acPcs, Spike.Lib.A64.ThreadsAb.pcRet, Spike.Lib.A64.ThreadsAb.cloneAt,
    Spike.Lib.A64.ThreadsAb.pcSt, Spike.Lib.A64.ThreadsAb.tailPcs, Spike.Lib.A64.ThreadsAb.failPcs,
    Spike.Lib.A64.WriteAb.dispEPcs, Spike.Lib.A64.ThreadsAb.dispTPcs, Spike.Lib.A64.ThreadsAb.g5Pcs,
    Spike.Lib.A64.ThreadsAb.stubPcs, Spike.Lib.A64.Abort.threads, Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM,
    String.reduceAppend,
    hlab ".L21_wc_main.sp6" 2169292 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L21_wc_main.clone9" 2169352 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L21_wc_main.1_spawnfail5" 2169376 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort" 2167996 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.0_entry" 2168016 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.2_next1" 2168052 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.4_next3" 2168088 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.6_next5" 2168124 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.8_next7" 2168160 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L12_scc_rt_abort.9_is8" 2168180 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_threads" 2168488 (by rw [← codeT_eq]; decide +kernel),
    hlab ".L17_scc_rt_abort_threads.0_entry" 2168504 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_threads_exit" 2168548 (by rw [← codeT_eq]; decide +kernel)]
  decide

end Labels

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- The layout's labels are `wakeProg`'s at `WakePh.lo`, of an output whose
program is `wakeProg` (`hpa`, `hwp`) placed at `WakePh.lo` (`hlo`). -/
theorem hlab_W (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg) (hlo : Λ0.code.lo = lo) :
    ∀ l x, codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x := by
  have ho : o.prog = wakeProg := Except.ok.inj (hpa.symm.trans hwp)
  intro l x h
  exact Spike.Lib.PlaceW.hlab_ofPlaceW hp i l x (by
    show codeOf Λ0.code.lo o.prog l = some x
    rw [hlo, ho]; exact h)

/-- **`hti0_W`'s `hab0`**: the loaded thread is off `AbW`. -/
theorem hab0_W (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg) (hlo : Λ0.code.lo = lo) (E : Scc.Sem.Entry) :
    ¬ WakeOD.AbW hp i (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) :=
  not_ab_lo (hlab_W hp i hpa hwp hlo) (show Int64.ofNat Λ0.code.lo = _ by rw [hlo])

/-- **`hti0_W`'s `hac0`**: the loaded thread is off `AcW`. -/
theorem hac0_W (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg) (hlo : Λ0.code.lo = lo) (E : Scc.Sem.Entry) :
    ¬ WakeOD.AcW hp i (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) :=
  not_ac_lo (hlab_W hp i hpa hwp hlo) (show Int64.ofNat Λ0.code.lo = _ by rw [hlo])

end Place

end Spike.Lib.WakeOAb

/-- info: 'Spike.Lib.WakeOAb.not_ab_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeOAb.not_ab_lo

/-- info: 'Spike.Lib.WakeOAb.not_ac_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeOAb.not_ac_lo

/-- info: 'Spike.Lib.WakeOAb.hab0_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeOAb.hab0_W

/-- info: 'Spike.Lib.WakeOAb.hac0_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeOAb.hac0_W
