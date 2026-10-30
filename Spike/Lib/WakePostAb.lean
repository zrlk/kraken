/-
**wake.w on AArch64: aborts after the spawn**:
two facts about `WakeRel.Post` for `WakeObligations`.

- `AbOff μ s`: the state is at neither the `writeErr` nor the `threads`
  abort site (`μ.abortAt`). `abOff_of_sfactsAC`: a state of the consumer's
  fragment with no `writeErr` phase and no `threads` phase
  (`SFactsAC … Dt (fun _ => False) Cl (fun _ => False)`, its `abortOk`) is
  `AbOff`.
- `pt0_abOff`: main's `WakeM0.PT0` is `AbOff` at its side's marks
  (`MSide.off`), `post_abort_kind`'s `hab0`.
- `post_abort_kind` (**the Post-vacuity lemma**): when both thread
  relations put their thread `AbOff`, an abort step from `Post` is of
  neither kind `writeErr` nor `threads`, so `post_abort`'s two
  environment-justified cases are vacuous (`post_abort_env`).
- `post_last_of`, `post_last_kr` (**the premise of
  `WakePreTi.hpost_of`**): with `KR` two slots, the second never dormant
  (`WakeKR.KR`), a `Post` configuration's last slot is not dormant.
-/
import Spike.Lib.WakeA64
import Spike.Lib.WakeKR
import Spike.Lib.A64SFactsAC
import Spike.Lib.WakeM0

namespace Spike.Lib.WakePostAb

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WakeA64

/-- **Off the `writeErr` and `threads` abort sites.** -/
def AbOff (μ : Marks) (s : State) : Prop :=
  ∀ k a, μ.abortAt k = some a → pcOf s = a → k ≠ .writeErr ∧ k ≠ .threads

open Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA in
/-- **A fragment state with neither abort phase is `AbOff`** (`SFactsAC.abortOk`
at `Ab = Ac = False`, as `StubW.stubTW_sfactsAC` gives). -/
theorem abOff_of_sfactsAC {Λ : Scc.Sem.Layout} {μ : Marks} {p : CoreTerm.Prog} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {lbl : Lbl}
    {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} {Dt Cl : State → Prop}
    (h : SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt (fun _ => False) Cl (fun _ => False)) :
    AbOff μ s := by
  intro k a ha hpc
  obtain ⟨hk, -⟩ := h.abortOk k a ha hpc
  rcases hk with ⟨-, h⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, h⟩
  · exact h.elim
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact h.elim

/-- **main's `PT0` is `AbOff`** at its side's marks (`MSide.off`) while
main's source is off its return (`PT0`'s other disjunct, after the exit):
`hab0` of `post_abort_kind` when `Q.PT0 = WakeM0.PT0 D`. -/
theorem pt0_abOff {ι : Type} {D : WakeM0.MSide ι} {w : ι} {tm : Memory} {sm : WeakMem.Memory}
    {t0 : Thread isaLSE2} {s0 : TermRun.TTh} (h : WakeM0.PT0 D w tm sm t0 s0)
    (hl : s0.term ≠ WakeMLive.wlRet) : AbOff D.μ t0.st :=
  fun k a ha hpc => absurd hpc (D.off w _ _ (h.1.resolve_right hl) k a ha)

variable {Q : WakeRel} {Λ : Scc.Sem.Layout}

/-- **The Post-vacuity lemma**: with both thread relations off the two abort
sites (main's while its source is off its return, which `KR`'s `MainLive`
gives while the process runs, as every step's does), an abort step from
`Post` is of neither kind `writeErr` nor `threads`. -/
theorem post_abort_kind {μ : Marks} (hlive : WakeM0.LiveK Q)
    (hab0 : ∀ w tm sm t0 s0, Q.PT0 w tm sm t0 s0 → s0.term ≠ WakeMLive.wlRet → AbOff μ t0.st)
    (hab1 : ∀ w tm sm t1 s1, Q.PT1 w tm sm t1 s1 → AbOff μ t1.st)
    {t t' : Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev} {k : AbortKind} (hP : Q.Post Λ t s)
    (hs : (machine (kernel 2)).Step μ tid t es t') (hk : Ev.abort k ∈ es) :
    k ≠ .writeErr ∧ k ≠ .threads := by
  obtain ⟨a, ha, th, hth, hpc⟩ : ∃ a, μ.abortAt k = some a ∧
      ∃ th : Thread isaLSE2, t.1.threads[tid]? = some th ∧ pcOf th.st = a := hs.abort_at hk
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hT, hS, -, h0, h1, -⟩, hK⟩ := hP
  have hl : s0.term ≠ WakeMLive.wlRet := hlive w t s hK hs.runs.2.1 s0 (by rw [hS]; rfl)
  rw [hT] at hth
  have hoff : AbOff μ th.st := by
    rcases tid with _ | _ | n
    · cases (show some t0 = some th from hth)
      simp only [WakeRel.PTw] at h0
      exact hab0 _ _ _ _ _ h0.2 hl
    · cases (show some t1 = some th from hth)
      simp only [WakeRel.PTw] at h1
      exact hab1 _ _ _ _ _ h1
    · exact absurd hth (by simp)
  exact hoff k a ha hpc

/-- **`post_abort`'s environment cases are vacuous**: from `Post`, no abort
step is `EnvJustified`-shaped (`writeErr`, `threads`). -/
theorem post_abort_env {μ : Marks} (hlive : WakeM0.LiveK Q)
    (hab0 : ∀ w tm sm t0 s0, Q.PT0 w tm sm t0 s0 → s0.term ≠ WakeMLive.wlRet → AbOff μ t0.st)
    (hab1 : ∀ w tm sm t1 s1, Q.PT1 w tm sm t1 s1 → AbOff μ t1.st)
    {t t' : Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev} {k : AbortKind} (hP : Q.Post Λ t s)
    (hs : (machine (kernel 2)).Step μ tid t es t') (hk : Ev.abort k ∈ es) (tr : List Ev) :
    ¬ EnvJustified tr k := by
  obtain ⟨h1, h2⟩ := post_abort_kind hlive hab0 hab1 hP hs hk
  cases k <;> simp_all [EnvJustified]

/-- **A `Post` configuration's last slot is not dormant** when `KR` gives two
slots, the second not dormant (`WakePreTi.hpost_of`'s premise). -/
theorem post_last_of
    (hK : ∀ w t s, Q.KR w t s → t.2.slots.size = 2 ∧ t.2.slots[1]? ≠ some Slot.dormant)
    {t : Cfg} {s : TermRun.Cfg} (hP : Q.Post Λ t s) : t.2.slots.back? ≠ some Slot.dormant := by
  obtain ⟨w, -, hk⟩ := hP
  obtain ⟨hn, h1⟩ := hK w t s hk
  rw [Array.back?_eq_getElem?, hn]
  exact h1

/-- `post_last_of` at wake's `KR` (`WakeKR.KR`). -/
theorem post_last_kr {r0 r1 : Q.ι → Range} (hK : ∀ w t s, Q.KR w t s → WakeKR.KR r0 r1 w t s)
    {t : Cfg} {s : TermRun.Cfg} (hP : Q.Post Λ t s) : t.2.slots.back? ≠ some Slot.dormant :=
  post_last_of (fun w t s h => ⟨(hK w t s h).1, (hK w t s h).2.2.1⟩) hP

/-- info: 'Spike.Lib.WakePostAb.post_abort_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_abort_env

/-- info: 'Spike.Lib.WakePostAb.post_last_kr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_last_kr

end Spike.Lib.WakePostAb
