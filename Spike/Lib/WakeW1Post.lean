/-
**A step of the worker after the spawn keeps `Post`** (data in `Spike/Lib/WakeW1.lean`, `Spike/Lib/WakeW1Compat.lean`).

Off its unpark and exit rows, a step of thread 1 (`step1_cases`) is

- an instruction off a system call: by the row of `WSide.closed` at the
  worker's pair, `post_silent`, `post_choice`, `post_fnc`, `post_rtLoad`
  (`WakeW1Instr`), `post_rtStore`, `post_rtRmw` (`WakeW1Rt`), `post_store`
  (`WakeW1Store`); the rows of other source terms are not at a worker term
  (`WTerm`), the unpark row is `atUnpk`, the system-call rows are not off a
  system call;
- a certified promise: `post_prom1` (`WakeW1Prom`);
- a system call: the `Out.sys` row (`post_sys`), the `emit` row excluded by
  `WCompat.sysOk`, the `texit` row `atTexit`, the instruction rows by
  `WCompat.sysExec`;
- a `clone`: excluded by the same rows (`SysOk` excludes `clone`);
- a range transfer: excluded, no transfer site at the worker's states
  (`WCompat.noSite`).

- `sysStep_ready`, `spawnStep_ready`: a kernel step is at a system call
  with a call (a `clone` for `spawnStep`).
- `sys_rows`: at a system call of the worker other than its exit, the row
  is `Out.sys`.
- `post_step1_of`: the obligation `post_step1`.
-/
import Spike.Lib.WakeW1Prom
import Spike.Lib.WakeW1Sys
import Spike.Lib.WakeW1Step

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt

/-! ## Kernel steps are at a system call -/

/-- **A system-call step is at a system call, with a call.** -/
theorem sysStep_ready {A : Arch} {tid : Nat} {c : Config isaLSE2 × KState} {p : Pick}
    {r : List Ev × (Config isaLSE2 × KState)} {t : Thread isaLSE2} (ht : c.1.threads[tid]? = some t)
    (h : sysStep abi A tid c p = some r) : abi.atSys t.st = true ∧ ∃ call, callOf abi t = some call := by
  unfold sysStep at h
  rw [ht] at h
  by_cases hr : ready abi tid c t = true
  · refine ⟨by simp only [ready, Bool.and_eq_true] at hr; exact hr.1.1, ?_⟩
    cases hc : callOf abi t with
    | none => simp [hr, hc] at h
    | some call => exact ⟨call, rfl⟩
  · simp [hr] at h

/-- **A `clone` step is at a system call decoding to `clone`.** -/
theorem spawnStep_ready {tid j : Nat} {c c' : Config isaLSE2 × KState} {r : BitVec 64} {t : Thread isaLSE2}
    (ht : c.1.threads[tid]? = some t) (h : spawnStep abi tid c j r = some c') :
    abi.atSys t.st = true ∧ ∃ st tl, callOf abi t = some (.clone st tl) := by
  unfold spawnStep at h
  rw [ht] at h
  by_cases hr : ready abi tid c t = true
  · refine ⟨by simp only [ready, Bool.and_eq_true] at hr; exact hr.1.1, ?_⟩
    cases hc : callOf abi t with
    | none => simp [hr, hc] at h
    | some call =>
      cases call with
      | clone st tl => exact ⟨st, tl, rfl⟩
      | _ => simp [hr, hc] at h
  · simp [hr] at h

variable {Q : WakeRel} {D : WSide Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **At a system call of the worker other than its exit the row is
`Out.sys`**: the `emit` row is a `write` to the output (`WCompat.sysOk`),
the `texit` row is `atTexit` at a source `ret` (excluded by `hnt`), every
instruction row's instruction is not the fault `WCompat.sysExec` asks
there. -/
theorem sys_rows (hC : WCompat Q D μ Λ arch) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hnt : ¬ Q.atTexit t s ∨ ∀ a, s1.term ≠ .ret a) (hat : abi.atSys t1.st = true) {call : Call} (hd : callOf abi t1 = some call) :
    SysOk wakeSrc (D.ms w) t1.st (Ctl.of s1) call ∧
      ∀ s' ∈ certSuccs abi t1.st call, ∃ c', LocalRun wakeSrc (Ctl.of s1) c' ∧ D.Wi w s' c' := by
  have hwi := h.pt1.1
  cases D.closed w _ _ hwi with
  | outL hl =>
    cases hl with
    | out r =>
      cases r with
      | sys K call' hK ha hd' hok hX =>
        rw [hC.K w] at hK; cases hK
        have e : call' = call := Option.some.inj (hd'.symm.trans hd)
        subst e
        exact ⟨hok, hX⟩
      | emit K buf n Pw Qw hK ha hd' =>
        rw [hC.K w] at hK; cases hK
        rcases hC.sysOk w _ _ _ hwi ha hd' with h' | ⟨hnw, -⟩
        · cases h'
        · exact absurd rfl (hnw 1 buf n)
      | choice P tree he hsil hX =>
        obtain ⟨m, rfl⟩ := hC.sysExec w _ _ _ hwi hat he
        cases hsil
      | _ =>
        obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat ‹isaLSE2.exec t1.st = some _›
        cases hm
    | ldSt _ _ _ _ _ _ _ _ _ he =>
      obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat he
      cases hm
  | unpk _ _ _ _ _ _ _ _ _ _ he =>
    obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat he
    cases hm
  | texit K a hK ha hd' ht =>
    rw [hC.K w] at hK; cases hK
    rcases hnt with hnt | hnr
    · exact absurd (by rw [hC.atTexit]; exact ⟨t1, h.t1_get, ha, hd'⟩) hnt
    · exact absurd ht (hnr a)
  | fnc _ _ _ he =>
    obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat he
    cases hm

/-! ## The obligation -/

/-- **`post_step1`**: a step of the worker other than its unpark and exit
rows keeps `Post`, matched by a source run with no observable event. -/
theorem post_step1_of (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D) (hwf : Λ.WF) {t t' : Cfg}
    {s : TermRun.Cfg} {es : List Ev} (hpost : Q.Post Λ t s) (hnu : ¬ Q.atUnpk t s) (hnt : ¬ Q.atTexit t s)
    (hs : (machine (kernel 2)).Step μ 1 t es t') :
    ∃ s', (wakeS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := post_parts hC hpost
  have hex : SrcSem.mainExit s = [] := hC.mainLive t s hpost hs.runs.2.1
  have hwi := h.pt1.1
  have hctl := h.wCtl
  rcases step1_cases h.t1_get hs with ⟨rfl, hns, outs, o, hso, ho, rfl, hco⟩ | ⟨rfl, m, hwt, rfl, hc⟩ |
    ⟨p, hsy, hca⟩ | ⟨rfl, j, r, hsp⟩ | ⟨rfl, k, hsite, -⟩
  · -- an instruction, by the worker's row
    cases D.closed w _ _ hwi with
    | outL hl =>
      cases hl with
      | out r =>
        cases r with
        | silent s' c' he hr hX => exact post_silent hC h hex hns hso ho hco he hr hX
        | choice P tree he hsil hX => exact post_choice hC h hex hns hso ho hco he hsil hX
        | load kl A g x' a e ty w' he ht =>
          rcases wterm_let hctl.term ht with h' | h' <;> rw [h'] at ht <;> simp [wkStore, wkUnpark] at ht
        | store kr A V s' x' a b e ty tb wa wb he ht hea hva heb hvb hX htag =>
          exact post_store hC hx hwf h hex hns hso ho hco he ht hea hva heb hvb hX
        | rtStore kr L V s' c' he hrt hmp hG hr hX =>
          exact post_rtStore hC hwf h hex hns hso ho hco he hmp hG hr hX
        | rtLoad kl L g c' he hrt hmp hr hX => exact post_rtLoad hC h hex hns hso ho hco he hr hX
        | rtRmw k' L op g c' he hrt hmp hr hX => exact post_rtRmw hC hwf h hex hns hso ho hco he hmp hr hX
        | sys K call hK ha =>
          rw [hC.K w] at hK; cases hK; rw [hns] at ha; cases ha
        | holdLoad kl A g x' sa u v e he hxs =>
          obtain ⟨-, ⟨a, t', pw, μ', ht, -⟩ | ⟨b, i, t', pw, ti, iws, μ', sb, k', ht, -⟩⟩ := hxs <;>
            rcases wterm_let hctl.term ht with h' | h' <;> rw [h'] at ht <;> simp [wkStore, wkUnpark] at ht
        | xchgStore kr A V s' x' sa u v e tv wv wold he hxs =>
          obtain ⟨-, ⟨a, t', pw, μ', ht, -⟩ | ⟨b, i, t', pw, ti, iws, μ', sb, k', ht, -⟩⟩ := hxs <;>
            rcases wterm_let hctl.term ht with h' | h' <;> rw [h'] at ht <;> simp [wkStore, wkUnpark] at ht
        | ctrRmw k' op g x' τ e n he hrt hm hs =>
          rcases hs with ⟨a, -, -, ht, -⟩ | ⟨-, a, -, ht, -⟩ <;>
            rcases wterm_let hctl.term ht with h' | h' <;> rw [h'] at ht <;> simp [wkStore, wkUnpark] at ht
        | alloc s' A x' a τ e ta ws k' wold old us he ht =>
          rcases wterm_let hctl.term ht with h' | h' <;> rw [h'] at ht <;> simp [wkStore, wkUnpark] at ht
        | newStore kr A V s' x' a t e w' wold old _ he hm ht =>
          rcases wterm_let hctl.term ht with h' | h' <;> rw [h'] at ht <;> simp [wkStore, wkUnpark] at ht
        | emit K buf n Pw Qw hK ha =>
          rw [hC.K w] at hK; cases hK; rw [hns] at ha; cases ha
        | fence k' s' c' he hr hX =>
          cases hr with
          | loc hr => exact post_fnc hC h hex hns hso ho hco he hr hX
          | pub _ hps _ =>
            -- the worker's terms publish nothing
            obtain ⟨-, -, x', a, e, ta, ta', ws, hpt, -⟩ := hps
            rcases hpt with ⟨ht, -⟩ | ⟨r, ht, -⟩ <;>
              rcases wterm_let hctl.term ht with h' | h' <;> rw [h'] at ht <;> simp [wkStore, wkUnpark] at ht
      | ldSt kl A g x' a e ty w' V he ht =>
        rcases wterm_let hctl.term ht with h' | h' <;> rw [h'] at ht <;> simp [wkStore, wkUnpark] at ht
    | unpk k' A B op g x' a e ty jw he hrt hmp hop ht =>
      have hst : s1.term = wkUnpark := by
        rcases wterm_let hctl.term ht with h' | h'
        · rw [h'] at ht; simp [wkStore] at ht
        · exact h'
      exact absurd (by rw [hC.atUnpk]; exact ⟨s1, h.s1_get, hst⟩) hnu
    | texit K a hK ha =>
      rw [hC.K w] at hK; cases hK; rw [hns] at ha; cases ha
    | fnc k' s' c' he hr hX => exact post_fnc hC h hex hns hso ho hco he hr hX
  · -- a certified promise
    exact post_prom1 hC hx hwf h hex hwt hc
  · -- a system call, by the `Out.sys` row
    obtain ⟨hat, call, hd⟩ := sysStep_ready h.t1_get hsy
    obtain ⟨hok, hX⟩ := sys_rows hC h (.inl hnt) hat hd
    obtain ⟨rfl, s', hr, hp⟩ := post_sys hC h hex hat hd hok hX hsy hca
    exact ⟨s', hr, hp⟩
  · -- no `clone`: the rows exclude it
    obtain ⟨hat, st, tl, hd⟩ := spawnStep_ready h.t1_get hsp
    exact absurd rfl ((sys_rows hC h (.inl hnt) hat hd).1.2.1 st tl)
  · -- no range transfer: no site at the worker's states
    obtain ⟨a, ha, t1', ht1, hpc⟩ := hsite
    obtain rfl : t1' = t1 := Option.some.inj (ht1.symm.trans h.t1_get)
    have hn := siteAt_eq_none_iff.mp (hC.noSite w _ _ hwi)
    cases k with
    | take => exact absurd (ha.trans (congrArg some hpc.symm)) hn.1
    | release => exact absurd (ha.trans (congrArg some hpc.symm)) hn.2

/-- info: 'Spike.Lib.WakeW1.post_step1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_step1_of

end Spike.Lib.WakeW1
