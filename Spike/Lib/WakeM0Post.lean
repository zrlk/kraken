/-
**A step of main after the spawn keeps `Post`** (`post_step0`; data in `Spike/Lib/WakeM0.lean`,
`Spike/Lib/WakeM0Compat.lean`). The thread-0 counterpart of
`Spike/Lib/WakeW1Post.lean`.

While the process runs (every step does), main's state and control are in
`Mi` (`Parts.mi0`), and a step of thread 0 (`step1_cases`) is

- an instruction off a system call: by the row of `MSide.closed`,
  `post_silent0`, `post_choice0`, `post_rtLoad0` (`WakeM0Instr`),
  `post_rtStore0`, `post_rtRmw0` (`WakeM0Rt`), the flag load `post_flag0`
  (`Out.load` and `OutL.ldSt` at `wlBody`, `mterm_load`); the rows of other
  source terms are not at main's terms (`WakeM0Rows`), the system-call rows
  are not off a system call;
- a certified promise: `post_prom0` (`WakeM0Prom`);
- a system call: a returning one (`post_sys0`), or `exit_group`: its exit
  off every abort site (`Step.sys`, `exit_off0`) is main's exit
  (`post_exit0`), its abort ends the process with the source stuttering
  (`post_exited0`);
- a `clone`: excluded by the `Out.sys` row (`SysOk` excludes `clone`);
- a range transfer: excluded, no transfer site at main's states
  (`WCompat0.noSite0`).

- `exit_off0`: an exit event is off every abort site (`Step.sys`).
- `post_step0_of`: the obligation `post_step0`.
-/
import Spike.Lib.WakeM0Exit
import Spike.Lib.WakeM0Flag
import Spike.Lib.WakeM0Prom
import Spike.Lib.WakeM0Rt
import Spike.Lib.WakeM0Rows

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt Spike.Lib.WakeW1

/-- **An exit event is off every abort site** (`Step.sys`). -/
theorem exit_off0 {μ : Marks} {tid : Nat} {t t' : (machine (kernel 2)).Cfg} {es : List Ev} {e : Fin 256}
    (hs : (machine (kernel 2)).Step μ tid t es t') (he : Ev.exit e ∈ es) :
    ∀ k a, μ.abortAt k = some a → ¬ (machine (kernel 2)).AtAddr a t tid := by
  cases hs with
  | sys _ _ _ _ hx => exact hx e he
  | _ => simp at he

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

/-- **`post_step0`**: a step of main keeps `Post`, matched by a source run
with its observable events (main's exit at its `exit_group`, none
otherwise). -/
theorem post_step0_of (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = WakeKR.KR r0 r1) (hown : Q.own = WakeOwn.wakeOwn) (hwf : Λ.WF) {t t' : Cfg}
    {s : TermRun.Cfg} {es : List Ev} (hpost : Q.Post Λ t s) (hs : (machine (kernel 2)).Step μ 0 t es t') :
    ∃ s', (wakeS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := post_parts hC hpost
  have ht0 : t.1.threads[0]? = some t0 := by rw [h.th]; rfl
  have hx : t.2.exited = none := hs.runs.2.1
  have hmi : M.Mi w t0.st (Ctl.of s0) := h.mi0 hPT0 hKR hx
  have hctl := h.mCtl hPT0
  rcases step1_cases ht0 hs with ⟨rfl, hns, outs, o, hso, ho, rfl, hco⟩ | ⟨rfl, m, hwt, rfl, hc⟩ |
    ⟨p, hsy, hca⟩ | ⟨rfl, j, r, hsp⟩ | ⟨rfl, k, hsite, -⟩
  · -- an instruction, by main's row
    cases M.closed w _ _ hmi with
    | out r =>
      cases r with
      | silent s' c' he hr hX => exact post_silent0 hC hC0 hPT0 hKR hown h hso ho hco he hr hX
      | choice P tree he hsil hX => exact post_choice0 hC hC0 hPT0 hKR hown h hso ho hco he hsil hX
      | load kl A g x' a e ty w' he ht hev hv =>
        obtain ⟨hb, -, -, rfl, -⟩ := mterm_load hctl.term ht
        exact post_flag0 hC hC0 hPT0 hKR hown h hso ho hco hx hb he hev hv
      | store kr A V s' x' a b e ty tb wa wb he ht => exact (mterm_not_store hctl.term ht).elim
      | rtStore kr L V s' c' he hrt hmp hG hr hX =>
        exact post_rtStore0 hC hC0 hPT0 hKR hown hwf h hso ho hco hx he hmp hG hr hX
      | rtLoad kl L g c' he hrt hmp hr hX => exact post_rtLoad0 hC hC0 hPT0 hKR hown h hso ho hco he hr hX
      | rtRmw k' L op g c' he hrt hmp hr hX =>
        exact post_rtRmw0 hC hC0 hPT0 hKR hown hwf h hso ho hco hx he hmp hr hX
      | sys K call hK ha =>
        rw [hC0.K0 w] at hK; cases hK; rw [hns] at ha; cases ha
      | holdLoad kl A g x' sa u v e he hxs => exact (mterm_not_xchgSite hctl.term hxs).elim
      | xchgStore kr A V s' x' sa u v e tv wv wold he hxs => exact (mterm_not_xchgSite hctl.term hxs).elim
      | ctrRmw k' op g x' τ e n he hrt hm hs =>
        rcases hs with ⟨a, -, -, ht, -⟩ | ⟨-, a, -, ⟨_, ht⟩, -⟩
        · exact (mterm_not_newBuf hctl.term ht).elim
        · rcases mterm_let hctl.term ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
      | alloc s' A x' a τ e ta ws k' wold old us he ht => exact (mterm_not_newBuf hctl.term ht).elim
      | newStore kr A V s' x' a t e w' wold old _ he hm ht =>
        obtain ⟨_, ht⟩ := ht
        rcases mterm_let hctl.term ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
      | emit K buf n Pw Qw hK ha =>
        rw [hC0.K0 w] at hK; cases hK; rw [hns] at ha; cases ha
      | fence k' s' c' he hr hX =>
        cases hr with
        | loc hr => exact post_fnc0 hC hC0 hPT0 hKR hown h hso ho hco he hr hX
        | pub _ hps _ =>
          -- main's terms publish nothing
          obtain ⟨-, -, x', a, e, t, t', ws, hpt, -⟩ := hps
          rcases hpt with ⟨ht, -⟩ | ⟨r, ht, -⟩ <;>
            rcases mterm_let hctl.term ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
    | ldSt kl A g x' a e ty w' V he ht hev hv =>
      obtain ⟨hb, -, -, rfl, -⟩ := mterm_load hctl.term ht
      exact post_flag0 hC hC0 hPT0 hKR hown h hso ho hco hx hb he hev hv
  · -- a certified promise
    exact post_prom0 hC hC0 hPT0 hKR hown hwf h hx hwt hc
  · -- a system call
    obtain ⟨hat, call, hd⟩ := sysStep_ready ht0 hsy
    by_cases hg : ∃ v, call = .exitGroup v
    · obtain ⟨v, rfl⟩ := hg
      obtain ⟨-, call', hc', hcases⟩ := sysStep_cases ht0 hsy (fun fd buf n hw => by
        rw [hd] at hw; cases hw)
      rw [hd] at hc'
      cases hc'
      rcases hcases with ⟨_, _, _, _, _, _, hw, -⟩ | ⟨_, -, -, hg', -⟩ | ⟨hw, -⟩ | ⟨v', hw, hcase⟩
      · cases hw
      · exact absurd rfl (hg' v)
      · cases hw
      · cases hw
        rcases hcase with ⟨-, rfl, rfl⟩ | ⟨k, -, -, rfl, rfl⟩
        · -- main's exit
          have hoff : ¬ ∃ k a, μ.abortAt k = some a ∧ pcOf t0.st = a := fun ⟨k, a, ha, hpc⟩ =>
            exit_off0 hs (List.mem_singleton_self _) k a ha ⟨t0, ht0, hpc⟩
          exact post_exit0 hC hC0 hPT0 hKR h hmi hat hd hoff
        · -- an abort: the process ends, the source stutters
          exact ⟨s, .refl _, post_exited0 hKR hpost _⟩
    · obtain ⟨rfl, s', hr, hp⟩ := post_sys0 hC hC0 hPT0 hKR hown h hmi hat hd
        (fun v e => hg ⟨v, e⟩) hsy hca
      exact ⟨s', hr, hp⟩
  · -- no `clone`: the row excludes it
    obtain ⟨hat, st, tl, hd⟩ := spawnStep_ready ht0 hsp
    exact absurd rfl ((sys_rows0 hC0 hmi hat hd).1.2.1 st tl)
  · -- no range transfer: no site at main's states
    obtain ⟨a, ha, t0', ht0', hpc⟩ := hsite
    obtain rfl : t0' = t0 := Option.some.inj (ht0'.symm.trans ht0)
    have hn := siteAt_eq_none_iff.mp (hC0.noSite0 w _ _ hmi)
    cases k with
    | take => exact absurd (ha.trans (congrArg some hpc.symm)) hn.1
    | release => exact absurd (ha.trans (congrArg some hpc.symm)) hn.2

/-- info: 'Spike.Lib.WakeM0.post_step0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_step0_of

end Spike.Lib.WakeM0
