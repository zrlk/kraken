/-
**main's control at the box** (wake.w, AArch64): `c0W`, the start control
`wake_start_wc_h0` takes as `c0` (abstract there): main's body after
`let z = zero int`, at `me` main's `ThreadId` and `z` the zero word.

- `c0W_term`, `c0W_z`, `c0W_me`: its term (`wakeImm_t1`), `z`, `me`.
- `c0W_box` (`C0Box`), `c0W_ctl` (`hc0`, by `WakeSrcCtl.new_ctl`).
- `c0W_run`: the start's control (`wakeTh0`) runs locally to `c0W` (the
  tail into `main`, then `let z`).
-/
import Spike.Lib.A64WakeStartH0
import Spike.Lib.A64WakeSrcCtl
import Spike.Lib.WakePreAsm
import Spike.Lib.A64WakeCode

namespace Spike.Lib.WakeC0

open CoreLang CoreTerm
open Spike.Lib (Ctl LocalStepS LocalRunS)
open Spike.Lib.WakeT1 (wakeSrc mainTidLbl)

/-- **main's control at the box**: `let o = new z in …` with `z` the zero
word and `me` main's `ThreadId`. -/
def c0W : Ctl :=
  ⟨SccCode.wakeImm_t1, [("z", .int, [TermRun.cst (.num 0)]),
    ("me", .tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])], none⟩

theorem c0W_term : c0W.term = .let_ "o" (.new (.var "z") (some .int)) Spike.Lib.A64.Flow.WakeWc.boxTerm := rfl

theorem c0W_z : ∃ tz, TermRun.lookupE c0W.env "z" = some (tz, [TermRun.cst (.num 0)]) := ⟨_, rfl⟩

theorem c0W_me :
    TermRun.evalAt c0W.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) := rfl

theorem c0W_box : Spike.Lib.A64.WakePh.StartH0.C0Box c0W := ⟨⟨_, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩

theorem c0W_ctl : (∀ a, c0W.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf wakeSrc c0W [] :=
  WakeSrcCtl.new_ctl c0W_term

/-- main's control at its body (after the start's tail call). -/
def cBodyW : Ctl :=
  ⟨.let_ "z" (.zero .int) SccCode.wakeImm_t1, [("me", .tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])], none⟩

theorem step_tail : LocalStepS wakeSrc (Ctl.of WakePreAsm.wakeTh0) cBodyW := by
  refine ⟨rfl, fun g mem pairs th hg ht he hσ => ?_⟩
  obtain ⟨t, e, σs⟩ := th
  simp only at ht he hσ; subst ht he hσ
  simp [TermRun.tstep, TermRun.enter, TermRun.ol, TermRun.close, TermRun.evalAt, TermRun.lookupE, hg, wakeSrc,
    Ctl.of, cBodyW, WakePreAsm.wakeTh0, Spike.Lib.WakeT1.tidStartT, SccCode.wakeImm_t1, SccCode.wakeImm_t0]
  rfl

theorem step_z : LocalStepS wakeSrc cBodyW c0W := by
  refine ⟨rfl, fun g mem pairs th hg ht he hσ => ?_⟩
  obtain ⟨t, e, σs⟩ := th
  simp only at ht he hσ; subst ht he hσ
  rw [TermLocal.tstep_let_gen rfl rfl]
  simp [TermRun.evalOp, TermRun.ol, TermRun.close, TermRun.zeroWords, TermRun.withS, TermRun.stOf, cBodyW, c0W,
    TermStep.substTs_nil']

/-- **The start's control runs locally to `c0W`**: the tail into `main`,
then `let z = zero int`. -/
theorem c0W_run : LocalRunS wakeSrc (Ctl.of WakePreAsm.wakeTh0) c0W :=
  .step step_tail (.step step_z (.refl _))

end Spike.Lib.WakeC0

/-- info: 'Spike.Lib.WakeC0.c0W_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeC0.c0W_run

/-- info: 'Spike.Lib.WakeC0.c0W_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeC0.c0W_ctl
