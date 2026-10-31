/-
**The source premise at the box's publication** (wake.w, x86-64): the
control at `boxTerm` (`let c = publish o in let p = pair c me in
spawnTerm`), where the start's thread-init obligation `hti_W` takes
`hSctl`, is not at a `ret` and its runs are well formed: a frame run from
it at no frames passes only `boxTerm`, its `pair`'s `let` and `spawnTerm`
(two local steps, no call, no return; `spawnTerm` takes no step), none a
load, a store or a buffer allocation.

- `frameStep_let`: a frame step at no frames from a `let` of no call is a
  local step to its body.
- `BoxT`: the three terms; `boxT_step`, `boxT_run`: frame runs from them
  stay at them, at no frames.
- `box_ctl`: `hSctl` at `boxTerm`.

The x86-64 twin of `X64.WakeSrcCtl.spawnSrc_ctl` (the control at
`spawnTerm`, which runs nowhere); here the run takes the publication and
the pair first.
-/
import Spike.Lib.X64WakeSrcCtl
import Spike.Lib.X64WakeBoxDefs
import Spike.Lib.Src.SrcNumE

namespace Spike.Lib.X64.WakeBoxCtl

open CoreLang CoreTerm
open Spike.Lib (Ctl LocalStepS FrameStep FrameRun)
open Spike.Lib.X64WakeSrcDefs (spawnTerm)
open Spike.Lib.X64WakeBoxDefs (boxTerm)

/-- **A frame step at no frames from a `let` of no call** is a local step to
the `let`'s body, at no frames. -/
theorem frameStep_let {p : Prog} {c : Ctl} {q : Ctl × List TermRun.Frame} {x : String} {op : Op} {e : Expr}
    (ht : c.term = .let_ x op e) (hc : ∀ f is a ts, op ≠ .call f is a ts) (hcc : ∀ f a, op ≠ .callc f a)
    (h : FrameStep p (c, []) q) : q.2 = [] ∧ q.1.term = e := by
  cases h with
  | loc hs =>
    have h1 := Spike.Lib.LowerNode.LocalStep.tstepE hs.toLocalStep
    rw [ht] at h1
    obtain ⟨t, ws, he, -⟩ := Spike.Lib.LowerNode.tstepE_let h1 hc hcc
    exact ⟨rfl, congrArg Prod.fst he⟩
  | call hcall =>
    rw [ht] at hcall
    simp only [Expr.let_.injEq] at hcall
    exact absurd hcall.2.1 (hc _ _ _ _)

/-- The pair's `let` past the publication. -/
abbrev pairT : Expr := .let_ "p" (.pair (.var "c") (.var "me")) spawnTerm

/-- **The terms a run from `boxTerm` passes.** -/
def BoxT (t : Expr) : Prop := t = boxTerm ∨ t = pairT ∨ t = spawnTerm

/-- **A frame step from the three terms stays at them**, at no frames. -/
theorem boxT_step {p : Prog} {q q' : Ctl × List TermRun.Frame} (h : FrameStep p q q') (h0 : q.2 = [])
    (hb : BoxT q.1.term) : q'.2 = [] ∧ BoxT q'.1.term := by
  obtain ⟨c, fs⟩ := q
  simp only at h0 hb
  subst h0
  rcases hb with ht | ht | ht
  · obtain ⟨h1, h2⟩ := frameStep_let (op := .publish (.var "o")) ht (by intros; simp) (by intros; simp) h
    exact ⟨h1, .inr (.inl h2)⟩
  · obtain ⟨h1, h2⟩ := frameStep_let (op := .pair (.var "c") (.var "me")) ht (by intros; simp) (by intros; simp) h
    exact ⟨h1, .inr (.inr h2)⟩
  · cases Spike.Lib.X64.WakeSrcCtl.frameRun_spawn ht (.single h)
    exact ⟨rfl, .inr (.inr ht)⟩

/-- **A frame run from the three terms stays at them**, at no frames. -/
theorem boxT_run {p : Prog} {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q') :
    q.2 = [] → BoxT q.1.term → q'.2 = [] ∧ BoxT q'.1.term := by
  induction h with
  | refl => exact fun h0 hb => ⟨h0, hb⟩
  | step hs _ ih =>
    intro h0 hb
    obtain ⟨h1, h2⟩ := boxT_step hs h0 hb
    exact ih h1 h2

/-- **`hSctl` at `boxTerm`**: not at a `ret`, and its runs well formed (no
load, store or buffer allocation on them). -/
theorem box_ctl {c : Ctl} (ht : c.term = boxTerm) :
    (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf Spike.Lib.X64WakeT1.wakeSrc c [] := by
  refine ⟨fun a e => by rw [ht] at e; simp [boxTerm] at e, ⟨?_, ?_⟩⟩
  · intro c' fs' hr x a e ty w hc
    obtain ⟨-, hb⟩ := boxT_run hr rfl (.inl ht)
    rcases hb with hb | hb | hb <;>
      rcases hc with hc | ⟨b, hc⟩ <;> rw [hb] at hc <;> simp [boxTerm, spawnTerm] at hc
  · intro c' fs' hr x a τ e hc
    obtain ⟨-, hb⟩ := boxT_run hr rfl (.inl ht)
    rcases hb with hb | hb | hb <;> rw [hb] at hc <;> simp [boxTerm, spawnTerm] at hc

end Spike.Lib.X64.WakeBoxCtl

/-- info: 'Spike.Lib.X64.WakeBoxCtl.frameStep_let' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxCtl.frameStep_let

/-- info: 'Spike.Lib.X64.WakeBoxCtl.boxT_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxCtl.boxT_step

/-- info: 'Spike.Lib.X64.WakeBoxCtl.boxT_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxCtl.boxT_run

/-- info: 'Spike.Lib.X64.WakeBoxCtl.box_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxCtl.box_ctl
