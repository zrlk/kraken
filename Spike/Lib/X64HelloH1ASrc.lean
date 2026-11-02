/-
**The source premises of hello.w's callee at the clone** (x86-64; the source half of the twin of
`Spike/Lib/A64HelloH1A.lean`, the hello counterparts of `X64WakeSrcCtl.frameRun_spawn`/`spawnSrc_ctl` and
`X64WakeBoxCtl.box_ctl`): main's source at `spawnTermH` takes no frame step, and from `boxTermH` (`let c = publish o
in let p0 = pair sl c in let p = pair p0 me in spawnTermH`) a frame run at no frames passes only those four terms, so
neither control is at a `ret` and their runs are well formed (no load, store or buffer allocation on them).

- `frameRun_spawnH`, `spawnSrcH_ctl`, `sctl_SBH`: at `spawnTermH` (wake's `frameRun_spawn`, `spawnSrc_ctl`).
- `BoxTH`, `boxTH_step`, `boxTH_run`, `box_ctlH`, `sctl_QBH`: at `boxTermH` (wake's `BoxT`, `boxT_step`,
  `boxT_run`, `box_ctl`), the callee's `hSctl` at the box's source facts `QBH`.

Unlike AArch64, the callee's source premise is at the box's publication (`QBH`, `boxTermH`; the box is published at
`.x25`'s `mfence`), so the run passes the publication and the two pairs before `spawnTermH` (AArch64: `SBH`, at
`spawnTermH` alone); the source is any program `p`.
-/
import Spike.Lib.X64HelloHMid
import Spike.Lib.X64WakeBoxCtl

namespace Spike.Lib.X64.HelloH1A

open CoreLang CoreTerm
open Spike.Lib (Ctl FrameStep FrameRun)
open Spike.Lib.X64.Flow.WakeWc (MidG)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64HelloHMid (QBH SBH)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH spawnTermH boxTermH p0Term pTerm)
open Spike.Lib.X64.WakeBoxCtl (frameStep_let)

/-! ## At the spawn -/

/-- **A control at `spawnTermH` takes no frame step** at no frames: the spawn is a configuration step, no thread
step, no call (wake's `frameRun_spawn`). -/
theorem frameRun_spawnH {p : Prog} {c : Ctl} {q : Ctl × List TermRun.Frame}
    (ht : c.term = spawnTermH) (h : FrameRun p (c, []) q) : q = (c, []) := by
  cases h with
  | refl => rfl
  | step hs _ =>
    exfalso
    cases hs with
    | loc h =>
      have := h.2 { p := p, k := default, arch := default, n := 1, i := 0, lbase := 0 } #[] []
        { term := c.term, env := c.env } rfl rfl rfl rfl
      simp [TermRun.tstep, ht, spawnTermH, TermRun.evalOp] at this
    | call hc => rw [ht] at hc; simp [spawnTermH] at hc

/-- **The source premise at `SpawnSrcH`**: not at a `ret`, its runs well formed, vacuously (wake's
`spawnSrc_ctl`). -/
theorem spawnSrcH_ctl {p : Prog} {l : WeakMem.AllocLabel} {ws : List TermRun.Word} {c : Ctl}
    (h : SpawnSrcH l ws c) :
    (∀ a, c.term ≠ .ret a) ∧ RunWf p c [] := by
  have ht := h.1
  refine ⟨fun a e => (by rw [ht] at e; simp [spawnTermH] at e), ⟨?_, ?_⟩⟩
  · intro c' fs' hr x a e ty w hc
    cases frameRun_spawnH ht hr
    rcases hc with hc | ⟨b, hc⟩ <;> rw [ht] at hc <;> simp [spawnTermH] at hc
  · intro c' fs' hr x a τ e hc
    cases frameRun_spawnH ht hr
    rw [ht] at hc; simp [spawnTermH] at hc

/-- **The source premise at `SBH`** (the source at the clone). -/
theorem sctl_SBH {p : Prog} {l : WeakMem.AllocLabel} {b : Nat} {ws : List TermRun.Word} :
    ∀ l' A c, SBH l b ws l' A c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [] :=
  fun _ _ _ ⟨_, _, h⟩ => spawnSrcH_ctl h

/-! ## At the box's publication -/

/-- **The terms a run from `boxTermH` passes.** -/
def BoxTH (t : Expr) : Prop := t = boxTermH ∨ t = p0Term ∨ t = pTerm ∨ t = spawnTermH

/-- **A frame step from the four terms stays at them**, at no frames. -/
theorem boxTH_step {p : Prog} {q q' : Ctl × List TermRun.Frame} (h : FrameStep p q q') (h0 : q.2 = [])
    (hb : BoxTH q.1.term) : q'.2 = [] ∧ BoxTH q'.1.term := by
  obtain ⟨c, fs⟩ := q
  simp only at h0 hb
  subst h0
  rcases hb with ht | ht | ht | ht
  · obtain ⟨h1, h2⟩ := frameStep_let (op := .publish (.var "o")) ht (by intros; simp) (by intros; simp) h
    exact ⟨h1, .inr (.inl h2)⟩
  · obtain ⟨h1, h2⟩ := frameStep_let (op := .pair (.var "sl") (.var "c")) ht (by intros; simp) (by intros; simp) h
    exact ⟨h1, .inr (.inr (.inl h2))⟩
  · obtain ⟨h1, h2⟩ := frameStep_let (op := .pair (.var "p0") (.var "me")) ht (by intros; simp) (by intros; simp) h
    exact ⟨h1, .inr (.inr (.inr h2))⟩
  · cases frameRun_spawnH ht (.single h)
    exact ⟨rfl, .inr (.inr (.inr ht))⟩

/-- **A frame run from the four terms stays at them**, at no frames. -/
theorem boxTH_run {p : Prog} {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q') :
    q.2 = [] → BoxTH q.1.term → q'.2 = [] ∧ BoxTH q'.1.term := by
  induction h with
  | refl => exact fun h0 hb => ⟨h0, hb⟩
  | step hs _ ih =>
    intro h0 hb
    obtain ⟨h1, h2⟩ := boxTH_step hs h0 hb
    exact ih h1 h2

/-- **The source premise at `boxTermH`**: not at a `ret`, and its runs well formed (no load, store or buffer
allocation on them). -/
theorem box_ctlH {p : Prog} {c : Ctl} (ht : c.term = boxTermH) :
    (∀ a, c.term ≠ .ret a) ∧ RunWf p c [] := by
  refine ⟨fun a e => by rw [ht] at e; simp [boxTermH] at e, ⟨?_, ?_⟩⟩
  · intro c' fs' hr x a e ty w hc
    obtain ⟨-, hb⟩ := boxTH_run hr rfl (.inl ht)
    rcases hb with hb | hb | hb | hb <;>
      rcases hc with hc | ⟨b, hc⟩ <;> rw [hb] at hc <;> simp [boxTermH, p0Term, pTerm, spawnTermH] at hc
  · intro c' fs' hr x a τ e hc
    obtain ⟨-, hb⟩ := boxTH_run hr rfl (.inl ht)
    rcases hb with hb | hb | hb | hb <;> rw [hb] at hc <;> simp [boxTermH, p0Term, pTerm, spawnTermH] at hc

/-- **The callee's `hSctl` at `QBH`** (the box's source facts). -/
theorem sctl_QBH {p : Prog} {l : WeakMem.AllocLabel} {b : Nat} {ws : List TermRun.Word} :
    ∀ l' A c, QBH l b ws l' A c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [] :=
  fun _ _ _ h => box_ctlH h.2.2.1

/-- **`hSctl` at a ghost of `MidG (QBH …)`**. -/
theorem sctl_midQBH {p : Prog} {l : WeakMem.AllocLabel} {b : Nat} {ws : List TermRun.Word} :
    ∀ c0 cA, MidG (QBH l b ws) c0 cA → (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 [] :=
  fun _ _ ⟨_, _, h, _⟩ => sctl_QBH _ _ _ h

end Spike.Lib.X64.HelloH1A

/-- info: 'Spike.Lib.X64.HelloH1A.spawnSrcH_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloH1A.spawnSrcH_ctl

/-- info: 'Spike.Lib.X64.HelloH1A.box_ctlH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloH1A.box_ctlH

/-- info: 'Spike.Lib.X64.HelloH1A.sctl_midQBH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloH1A.sctl_midQBH
