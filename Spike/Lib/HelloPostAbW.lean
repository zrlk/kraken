/-
**hello.w on AArch64: `TwH` along the run and `post_abort`** (second part of `Spike/Lib/HelloPostAb.lean`):
`hello_obligations`'
`tw_load`, `tw_step` and `post_abort` at `Tw := TwH Λ E Ab`.

- `tw_load`: the load is a lift (`A64TwoSlot.load_two`), whose last slot is
  dormant, so only the run invariant is asked (`WakeRunInv.runInv_load`).
- `tw_step`: before the spawn a lifted step stays a lift; the `clone` makes
  thread 1 the child, out of `Ab` (`hcl`), at no byte. After it main keeps
  `W1` (`w1_step0`), the worker too (`w1_step1`, at `hab1`/`hns1`).
- `post_abortH`: an abort step from `Post` is an `exit_group` at an abort site
  (`WakeNoAbort.step_abort`); main is at none (`hoff0`); the worker is at the
  `writeErr` site in `Ab` (`AbFacts.at_`), so `TwH` puts `writeErr` in the
  trace, which is `AbortJustified … .writeErr`; the source thread is
  `Components.thr_onto`'s at `post_wit`'s witness (`hwit`).
- `tw_stepK`, `post_abortK`: at hello's `KRHE` (`hKR : Q.KR = KRHE D r0 r1`;
  its `KRH` part).

Rows: `hab1` (5i-hab1), `hns1` (the worker off the transfer sites,
`WCompatH.noSite`), `hcl` (5i-hcl), `hoff0` (main's `MSide.off`), `hwit`
(5j-wit).
-/
import Spike.Lib.HelloPostAb
import Spike.Lib.HelloKRE

namespace Spike.Lib.HelloPostAbW

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WakeA64 Spike.Lib.Handover
open Spike.Lib.HelloPostAb
open Spike.Lib.HelloKRE (KRHE)
open Scc.Cert.WideA64 (wideIn)
open Spike.Lib.Consumer1 (Refusal)

variable {Λ : Scc.Sem.Layout} {E : Entry} {μ : Marks} {Ab : State → Prop} {Q : WakeRel}

/-- **`hello_obligations`' `tw_load` at `TwH`.** -/
theorem tw_load {asm : String} (hw : ∀ prog, (textProgram asm).toOption = some prog → wideIn prog = true) :
    ∀ t0, (target (kernel 2) E).load asm Λ = some t0 → TwH Λ E Ab t0 [] := by
  intro t0 h
  refine ⟨WakeRunInv.runInv_load hw h, fun hb => ?_⟩
  obtain ⟨d, u, -, rfl, -⟩ := load_two h
  exact absurd (up_back d u) hb

/-- **`hello_obligations`' `tw_step` at `TwH`** (see the module doc). -/
theorem tw_step
    (hK : ∀ w t s, Q.KR w t s →
      t.2.slots.size = 2 ∧ (∃ j, t.2.slots[0]? = some (.run j)) ∧ t.2.slots[1]? ≠ some Slot.dormant)
    (hab1 : ∀ w tm sm t1 s1, Q.PT1 w tm sm t1 s1 → AbFacts μ Ab t1.st)
    (hns1 : ∀ w tm sm t1 s1, Q.PT1 w tm sm t1 s1 → siteAt abi μ t1.st = none)
    (hcl : ∀ d s tid th stack tls, Q.R1 d s → d.1.threads.size = d.2.slots.size → d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧ ¬ Ab (childAfter abi d.2 tid th stack tls).st) :
    ∀ tid t es t' s pre, Q.Rw Λ t s → (machine (kernel 2)).Step μ tid t es t' →
      TwH Λ E Ab t pre → TwH Λ E Ab t' (pre ++ es) := by
  intro tid t es t' s pre hR hs ⟨hri, hw⟩
  refine ⟨WakeRunInv.runInv_step hri hs, fun hb' => ?_⟩
  rcases hR with ⟨d, u, rfl, -, -, hn, hR1⟩ | ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hT, -, -, -, h1, -⟩, hk⟩
  · obtain ⟨-, ⟨d', -, rfl⟩ | ⟨-, th, stack, tls, r, hth, hsys, -, hex, hcall, -, -, rfl, -⟩⟩ := step_up_cases hn hs
    · exact absurd (up_back d' u) hb'
    · obtain ⟨h1, hAb⟩ := hcl d s tid th stack tls hR1 hn hth hsys hcall hex
      intro t1 ht1
      have hs1 : d.2.slots.size = 1 := hn ▸ h1
      simp only [afterClone, Array.getElem?_push, Array.size_set!, h1, ↓reduceIte, Option.some.injEq] at ht1
      subst ht1
      refine ⟨.inl ?_, fun h => absurd h hAb⟩
      simp only [afterClone, KState.wr, Array.getElem?_push, hs1, ↓reduceIte]
  · obtain ⟨hsz, hs0, hs1⟩ := hK w t s hk
    have hW := hw (by rw [Array.back?_eq_getElem?, hsz]; exact hs1)
    have hn : t.1.threads.size = 2 := by rw [hT]; rfl
    simp only [WakeRel.PTw] at h1
    rcases tid with _ | _ | n
    · exact w1_step0 hn ⟨hs0, hs1⟩ hs hW
    · exact w1_step1 hn ⟨hsz, hs0, hs1⟩ (by rw [hT]; rfl) (hab1 _ _ _ _ _ h1) (hns1 _ _ _ _ _ h1) hs hW
    · exfalso
      obtain ⟨⟨th, hth⟩, -⟩ := hs.runs
      rw [hT] at hth
      simp at hth

/-- **`hello_obligations`' `post_abort` at `Ti0 ∧ TwH`** (see the module
doc). -/
theorem post_abortH {arch : WeakMem.Arch} {B : Budget} {p : CoreTerm.Prog} {Ti0 : Cfg → List Ev → Prop}
    (hlive : WakeM0.LiveK Q)
    (hoff0 : ∀ w tm sm t0 s0, Q.PT0 w tm sm t0 s0 → s0.term ≠ WakeMLive.wlRet →
      ∀ k a, μ.abortAt k = some a → pcOf t0.st ≠ a)
    (hab1 : ∀ w tm sm t1 s1, Q.PT1 w tm sm t1 s1 → AbFacts μ Ab t1.st)
    (hK : ∀ w t s, Q.KR w t s → t.2.slots.size = 2 ∧ t.2.slots[1]? ≠ some Slot.dormant)
    (hwit : ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s) :
    ∀ tr t s tid es t' k, (srcS p arch).Reach (obs tr) s → Q.Post Λ t s → Ti0 t tr ∧ TwH Λ E Ab t tr →
      (machine (kernel 2)).Step μ tid t es t' → Ev.abort k ∈ es →
      ∃ w i, Components (machine (kernel 2)) Λ w t s ∧ w.thr i = some tid ∧
        AbortJustified B (srcS p arch) tr s i k := by
  intro tr t s tid es t' k _ hP hTw hs hk
  obtain ⟨-, hri, hw⟩ := hTw
  obtain ⟨th, v, hth, -, -, a, ha, hpc⟩ := WakeNoAbort.step_abort hs hk
  obtain ⟨wc, hC⟩ := hwit t s hP hri
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hT, hS, -, h0, h1, -⟩, hKR⟩ := hP
  have hl : s0.term ≠ WakeMLive.wlRet := hlive w t s hKR hs.runs.2.1 s0 (by rw [hS]; rfl)
  rw [hT] at hth
  rcases tid with _ | _ | n
  · cases (show some t0 = some th from hth)
    simp only [WakeRel.PTw] at h0
    exact (hoff0 _ _ _ _ _ h0.2 hl k a ha hpc).elim
  · cases (show some t1 = some th from hth)
    simp only [WakeRel.PTw] at h1
    obtain ⟨rfl, hA⟩ := (hab1 _ _ _ _ _ h1).at_ k a ha hpc
    obtain ⟨hsz, hs1⟩ := hK w t s hKR
    have hwe := (hw (by rw [Array.back?_eq_getElem?, hsz]; exact hs1) th (by rw [hT]; rfl)).2 hA
    obtain ⟨i, -, hi⟩ := hC.thr_onto 1 th hs.runs (by rw [hT]; rfl)
    exact ⟨wc, i, hC, hi, hwe⟩
  · exact absurd hth (by simp)

/-! ## At hello's `KRHE` -/

section KRHE

variable {D : HelloW1.WSideH Q.ι} {r0 r1 : Q.ι → Range}

/-- `tw_step` at `Q.KR = KRHE D r0 r1`. -/
theorem tw_stepK (hKR : Q.KR = KRHE D r0 r1)
    (hab1 : ∀ w tm sm t1 s1, Q.PT1 w tm sm t1 s1 → AbFacts μ Ab t1.st)
    (hns1 : ∀ w tm sm t1 s1, Q.PT1 w tm sm t1 s1 → siteAt abi μ t1.st = none)
    (hcl : ∀ d s tid th stack tls, Q.R1 d s → d.1.threads.size = d.2.slots.size → d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧ ¬ Ab (childAfter abi d.2 tid th stack tls).st) :
    ∀ tid t es t' s pre, Q.Rw Λ t s → (machine (kernel 2)).Step μ tid t es t' →
      TwH Λ E Ab t pre → TwH Λ E Ab t' (pre ++ es) :=
  tw_step (fun w t s h => by rw [hKR] at h; exact ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩) hab1 hns1 hcl

/-- `post_abortH` at `Q.KR = KRHE D r0 r1` (`LiveK` by `krh_live`). -/
theorem post_abortK {arch : WeakMem.Arch} {B : Budget} {p : CoreTerm.Prog} {Ti0 : Cfg → List Ev → Prop}
    (hKR : Q.KR = KRHE D r0 r1)
    (hoff0 : ∀ w tm sm t0 s0, Q.PT0 w tm sm t0 s0 → s0.term ≠ WakeMLive.wlRet →
      ∀ k a, μ.abortAt k = some a → pcOf t0.st ≠ a)
    (hab1 : ∀ w tm sm t1 s1, Q.PT1 w tm sm t1 s1 → AbFacts μ Ab t1.st)
    (hwit : ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s) :
    ∀ tr t s tid es t' k, (srcS p arch).Reach (obs tr) s → Q.Post Λ t s → Ti0 t tr ∧ TwH Λ E Ab t tr →
      (machine (kernel 2)).Step μ tid t es t' → Ev.abort k ∈ es →
      ∃ w i, Components (machine (kernel 2)) Λ w t s ∧ w.thr i = some tid ∧
        AbortJustified B (srcS p arch) tr s i k :=
  post_abortH (fun w t s h => by rw [hKR] at h; exact A64HelloWriteK.krh_live h.1) hoff0 hab1
    (fun w t s h => by rw [hKR] at h; exact ⟨h.1.1, h.1.2.2.1⟩) hwit

end KRHE

/-! ## Non-vacuity: the refused `write` enters `Ab` with `writeErr` -/

section Refused

open Kraken.Promising.Lower.A64 (CellAt)

/-- A refusal is no `-EINTR`/`-EAGAIN`. -/
theorem not_eintr_of_refused {r : BitVec 64} (h : writeRefused r = true) : ¬ (r = neg eintr ∨ r = neg eagain) := by
  rintro (rfl | rfl) <;> revert h <;> decide +kernel

/-- **The kernel's refused return to `print`'s `write`** (row 5i's
`Ab` branch is reached): thread `tid` at `print`'s system call (a 4-byte
cell at `Spike.Lib.A64.PrintD.pcSvc lab`), at a `write` with no byte out, its stored length
`[sp + 8]` refused by `r`: the `.ret r` system-call step emits `writeErr`
(`Kernel.sysStep`'s `writeRefused` branch) and leaves the thread in
`WriteAb.Ab lab` (its `.ret` class: `x0 = r`, the pc after the call, the
private memory kept). -/
theorem refused_enters {tid : Nat} {c : Cfg} {t : Thread isaLSE2} {fd buf n : Nat} {r l : BitVec 64}
    {lab : Label → Int64} {d : Directive} (ht : c.1.threads[tid]? = some t) (hrd : ready abi tid c t = true)
    (hc : callOf abi t = some (.write fd buf n)) (hj : c.2.wr tid = 0) (hcell : CellAt t.st d 4)
    (hpc : t.st.st.2 = Spike.Lib.A64.PrintD.pcSvc lab) (hl : Spike.Lib.A64.WriteAb.spLoad t.st 8 = some l)
    (hr : Refusal l.toNat r) :
    sysStep abi Arch.armv8 tid c (.ret r) =
        some ([.writeErr], (c.1.withThread tid (retThread abi t r) c.1.mem, c.2)) ∧
      Spike.Lib.A64.WriteAb.Ab lab (retThread abi t r).st := by
  refine ⟨?_, .inl ⟨?_, l, hl, ?_⟩⟩
  · unfold sysStep
    simp only [ht, hrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hc, hj, Nat.lt_irrefl,
      not_eintr_of_refused hr.1, hr.1, back]
  · rw [retThread_st]
    show nextPc t.st = _
    rw [nextPc_of_cellAt hcell, hpc]; rfl
  · rw [retThread_st]
    simpa [abi] using hr

/-- **A refusal exists at every stored length**: `write` returning `0`. -/
theorem refusal_zero (l : BitVec 64) : Refusal l.toNat 0 := by
  refine ⟨by decide +kernel, fun j hj hle he => ?_⟩
  have hlt : j < 2 ^ 64 := Nat.lt_of_le_of_lt hle l.isLt
  have := congrArg BitVec.toNat he
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  simp only [h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
  omega

end Refused

/-- info: 'Spike.Lib.HelloPostAbW.tw_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tw_step

/-- info: 'Spike.Lib.HelloPostAbW.post_abortH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_abortH

/-- info: 'Spike.Lib.HelloPostAbW.refused_enters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms refused_enters

/-- info: 'Spike.Lib.HelloPostAbW.refusal_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms refusal_zero

end Spike.Lib.HelloPostAbW
