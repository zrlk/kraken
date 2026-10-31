/-
**main's control at the box** (wake.w, x86-64): `c0W`, the start control
`wake_start_wc_h0` takes as `c0` (abstract there): main's body after
`let z = zero int`, at `me` main's `ThreadId` and `z` the zero word.

- `c0W_term`, `c0W_z`, `c0W_me`: its term (`wakeImm_t1`), `z`, `me`.
- `c0W_box` (`C0Box`), `c0W_ctl` (`hc0`, by `new_ctl`).
- `c0W_run`: the start's control (`wakeTh0`) runs locally to `c0W` (the
  tail into `main`, then `let z`).

Where x86-64 differs from AArch64: nothing in the control itself (the
source, `wakeImm_t1` and main's `ThreadId` label are x86-64's twins of
AArch64's, token for token). AArch64 takes `hc0` from
`WakeSrcCtl.new_ctl` (`A64WakeSrcCtl`, which imports AArch64's consumer);
x86-64 has no `SrcCtl` twin yet, so the same vacuity argument
(`FrameNew.FrameRun.eq_of_new`) is restated here as `new_ctl` at x86-64's
`WakeWf.RunWf`. The box's continuation is `X64WakeBoxDefs.boxTerm` (AArch64
`A64.Flow.WakeWc.boxTerm`).
-/
import Spike.Lib.X64WakeStartH0
import Spike.Lib.X64WakePreAsm
import Spike.Lib.X64WakeCode
import Spike.Lib.X64WakeBoxDefs
import Spike.Lib.FrameNew

namespace Spike.Lib.X64.WakeC0

open CoreLang CoreTerm
open Spike.Lib (Ctl LocalStepS LocalRunS)
open Spike.Lib.X64WakeT1 (wakeSrc mainTidLbl)

/-- **main's control at the box**: `let o = new z in …` with `z` the zero
word and `me` main's `ThreadId`. -/
def c0W : Ctl :=
  ⟨SccCode.wakeImm_t1, [("z", .int, [TermRun.cst (.num 0)]),
    ("me", .tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])], none⟩

theorem c0W_term : c0W.term = .let_ "o" (.new (.var "z") (some .int)) Spike.Lib.X64WakeBoxDefs.boxTerm := rfl

theorem c0W_z : ∃ tz, TermRun.lookupE c0W.env "z" = some (tz, [TermRun.cst (.num 0)]) := ⟨_, rfl⟩

theorem c0W_me :
    TermRun.evalAt c0W.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) := rfl

theorem c0W_box : Spike.Lib.X64.WakePh.StartH0.C0Box c0W := ⟨⟨_, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩

/-- **The source premise at a box allocation** (the start control, `let o =
new z in …`): not at a `ret`, and its runs well formed, vacuously: a frame run
from a `new` is empty (`FrameRun.eq_of_new`). The x86-64 restatement of
`WakeSrcCtl.new_ctl`. -/
theorem new_ctl {p : Prog} {c : Ctl} {x : String} {a : CoreTerm.At} {T : Option Ty} {e : Expr} (ht : c.term = .let_ x (.new a T) e) :
    (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf p c [] := by
  refine ⟨fun a' h => (by rw [ht] at h; cases h), ⟨?_, ?_⟩⟩
  · intro c' fs' hr x' a' e' ty w hc
    cases Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht
    rcases hc with hc | ⟨b, hc⟩ <;> rw [ht] at hc <;> simp at hc
  · intro c' fs' hr x' a' τ e' hc
    cases Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht
    rw [ht] at hc; simp at hc

theorem c0W_ctl : (∀ a, c0W.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf wakeSrc c0W [] :=
  new_ctl c0W_term

/-- main's control at its body (after the start's tail call). -/
def cBodyW : Ctl :=
  ⟨.let_ "z" (.zero .int) SccCode.wakeImm_t1, [("me", .tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])], none⟩

theorem step_tail : LocalStepS wakeSrc (Ctl.of Spike.Lib.X64WakePreAsm.wakeTh0) cBodyW := by
  refine ⟨rfl, fun g mem pairs th hg ht he hσ => ?_⟩
  obtain ⟨t, e, σs⟩ := th
  simp only at ht he hσ; subst ht he hσ
  simp [TermRun.tstep, TermRun.enter, TermRun.ol, TermRun.close, TermRun.evalAt, TermRun.lookupE, hg, wakeSrc,
    Ctl.of, cBodyW, Spike.Lib.X64WakePreAsm.wakeTh0, Spike.Lib.X64WakeT1.tidStartT, SccCode.wakeImm_t1,
    SccCode.wakeImm_t0]
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
theorem c0W_run : LocalRunS wakeSrc (Ctl.of Spike.Lib.X64WakePreAsm.wakeTh0) c0W :=
  .step step_tail (.step step_z (.refl _))

end Spike.Lib.X64.WakeC0

/-- info: 'Spike.Lib.X64.WakeC0.c0W_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeC0.c0W_run

/-- info: 'Spike.Lib.X64.WakeC0.c0W_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeC0.c0W_ctl
