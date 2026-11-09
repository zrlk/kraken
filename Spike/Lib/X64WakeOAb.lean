/-
**The loaded thread is off the root's abort phases** (x86-64, the twin of
`Spike/Lib/WakeOAb.lean`, same names): wake's loaded thread, at `_start`
(the code's base `WakePh.lo`), is in neither the write abort's phase
(`WriteAb.Ab`) nor the threads abort's phase over main's spawn failure
(`ThreadsAb.Ac … pfxM`): every pc of either phase is at a label of the
runtime's print, abort, abort stubs or `wc_main`'s spawn, all above
`_start` (`not_ab_lo`, `not_ac_lo`, from the labels' addresses in
`wakeCells`, decided). These are `WakeOSide.hti0_W`'s `hab0`, `hac0`
(`hab0_W`, `hac0_W`).

**Unlike AArch64**: `X64WakeOD` twins only the arena, so `hab0_W`/`hac0_W`
state `¬ WriteAb.Ab (Ly).lab t` and `¬ ThreadsAb.Ac (Ly).lab pfxM t`
(A64: `¬ WakeOD.AbW hp i t`, `¬ WakeOD.AcW hp i t`, which unfold to these);
the layout is `RuntimeLayout.ofPlaceWX` at `PlaceWX`; the parse is
`cellsOf asm = some o.prog` and `= some wakeCells` (`hpa`, `hwp`; A64:
`textProgram asm = .ok …`); labels are `codeLabel lo wakeCells`; the threads
phase's pcs include the `je` at `pcJe`.
-/
import Spike.Lib.X64WakeOD
import Spike.Lib.X64ThreadsAb
import Spike.Lib.X64WakePh
import Spike.Lib.X64WakeStartWfL

namespace Spike.Lib.X64WakeOAb

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)
open Spike.Lib.X64.WakePh (lo)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)

section Labels

variable {lab : Label → Int64} (hlab : ∀ l x, codeLabel lo wakeCells l = some x → lab l = Int64.ofNat x)
include hlab

/-- **No pc of the write abort's phase is the code's base.** -/
theorem not_ab_lo {s : State} (hpc : s.st.2 = Int64.ofNat lo) : ¬ Spike.Lib.X64.WriteAb.Ab lab s := by
  refine Spike.Lib.X64.WriteAb.not_ab_of_pc ?_
  rw [hpc]
  simp only [Spike.Lib.X64.WriteAb.abPcs, Spike.Lib.X64.WriteAb.pcRet, Spike.Lib.X64.WriteAb.tailPcs,
    Spike.Lib.X64.WriteAb.failPcs, Spike.Lib.X64.WriteAb.dispEPcs, Spike.Lib.X64.WriteAb.dispTPcs,
    Spike.Lib.X64.WriteAb.g4Pcs, Spike.Lib.X64.WriteAb.stubPcs, Spike.Lib.X64.Abort.write,
    hlab ".Lscc_rt_print.write" 4202071 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_print.chk2" 4202115 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_print.chk3" 4202133 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_print.fail" 4202186 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort" 4202487 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.entry" 4202499 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next1" 4202523 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next3" 4202550 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next5" 4202577 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.is6" 4202595 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_write" 4202837 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort_write.entry" 4202845 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_write_exit" 4202897 (by rw [← codeT_eq]; decide +kernel)]
  decide

/-- **No pc of the threads abort's phase (over main's spawn) is the code's
base.** -/
theorem not_ac_lo {s : State} (hpc : s.st.2 = Int64.ofNat lo) :
    ¬ Spike.Lib.X64.ThreadsAb.Ac lab Spike.Lib.X64.WakePh.StartWf.pfxM s := by
  refine Spike.Lib.X64.ThreadsAb.not_ac_of_pc ?_
  rw [hpc]
  simp only [Spike.Lib.X64.ThreadsAb.acPcs, Spike.Lib.X64.ThreadsAb.pcRet, Spike.Lib.X64.ThreadsAb.pcJe,
    Spike.Lib.X64.ThreadsAb.cloneAt, Spike.Lib.X64.ThreadsAb.pcSt, Spike.Lib.X64.ThreadsAb.tailPcs,
    Spike.Lib.X64.ThreadsAb.failPcs, Spike.Lib.X64.WriteAb.dispEPcs, Spike.Lib.X64.ThreadsAb.dispTPcs,
    Spike.Lib.X64.ThreadsAb.g5Pcs, Spike.Lib.X64.ThreadsAb.stubPcs, Spike.Lib.X64.Abort.threads,
    Spike.Lib.X64.WakePh.StartWf.pfxM, String.reduceAppend,
    hlab ".Lwc_main.x3" 4203435 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lwc_main.x4" 4203488 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lwc_main.spawnfail5" 4203510 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort" 4202487 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.entry" 4202499 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next1" 4202523 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next3" 4202550 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next5" 4202577 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.next7" 4202604 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort.is8" 4202622 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_threads" 4202905 (by rw [← codeT_eq]; decide +kernel),
    hlab ".Lscc_rt_abort_threads.entry" 4202913 (by rw [← codeT_eq]; decide +kernel),
    hlab "scc_rt_abort_threads_exit" 4202965 (by rw [← codeT_eq]; decide +kernel)]
  decide

end Labels

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- The layout's labels are `wakeCells`'s at `WakePh.lo`, of an output whose
cells are `wakeCells` (`hpa`, `hwp`) placed at `WakePh.lo` (`hlo`). -/
theorem hlab_W {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hwp : Scc.Sem.X64.cellsOf asm = some wakeCells) (hlo : Λ0.code.lo = lo) :
    ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x := by
  have ho : o.prog = wakeCells := Option.some.inj (hpa.symm.trans hwp)
  intro l x h
  exact Spike.Lib.PlaceWX.hlab_ofPlaceWX hp i l x (by
    show codeLabel Λ0.code.lo o.prog l = some x
    rw [hlo, ho]; exact h)

/-- **`hti0_W`'s `hab0`**: the loaded thread is off the write abort's
phase. -/
theorem hab0_W {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hwp : Scc.Sem.X64.cellsOf asm = some wakeCells) (hlo : Λ0.code.lo = lo) (E : Scc.Sem.Entry) :
    ¬ Spike.Lib.X64.WriteAb.Ab (Ly).lab (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) :=
  not_ab_lo (hlab_W hp i hpa hwp hlo) (show Int64.ofNat Λ0.code.lo = _ by rw [hlo])

/-- **`hti0_W`'s `hac0`**: the loaded thread is off the threads abort's
phase. -/
theorem hac0_W {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hwp : Scc.Sem.X64.cellsOf asm = some wakeCells) (hlo : Λ0.code.lo = lo) (E : Scc.Sem.Entry) :
    ¬ Spike.Lib.X64.ThreadsAb.Ac (Ly).lab Spike.Lib.X64.WakePh.StartWf.pfxM
      (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) :=
  not_ac_lo (hlab_W hp i hpa hwp hlo) (show Int64.ofNat Λ0.code.lo = _ by rw [hlo])

end Place

end Spike.Lib.X64WakeOAb

/-- info: 'Spike.Lib.X64WakeOAb.not_ab_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOAb.not_ab_lo

/-- info: 'Spike.Lib.X64WakeOAb.not_ac_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOAb.not_ac_lo

/-- info: 'Spike.Lib.X64WakeOAb.hlab_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOAb.hlab_W

/-- info: 'Spike.Lib.X64WakeOAb.hab0_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOAb.hab0_W

/-- info: 'Spike.Lib.X64WakeOAb.hac0_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOAb.hac0_W
