/-
**A step of the allocation-capable consumer**
(`Spike/Lib/X64ConsumerA.lean`): every step from `RSA` is matched by a
source run landing in `RSA` (`r_stepA`, `r_stepS` with the arena).

From `PreSA` (`pre_stepA`, `pre_stepS`'s cases): the take, a local run of
the source, the thread's promises and the memory kept (`AllocInvAt` along
the frame run); an instruction (`instr_stepA`); a promise, the source
stuttering (`AllocInvAt.promise`); a kernel step, as in `pre_stepS`, the
promises and the memory kept.

- `allocInvAt_prom`: `AllocInvAt` for a thread with the same promises.
- `pre_stepAX`: the step off the output `write`, for rows under any
  `msOfAX … ab`.
- `pre_stepA`, `r_stepA`: the step.
-/
import Spike.Lib.X64ConsumerAInstr

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena}

/-- **`AllocInvAt` depends on the thread's promises only**
(`AllocInvAt.prom_keep`). -/
theorem allocInvAt_prom {lbl : Lbl} {lsize : Lsize} {th th' : Thread isa} {tm : Memory} {hu : Nat} {c : Ctl}
    (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c) (hp : th'.prom = th.prom) :
    AllocInvAt Λ lbl lsize th' tm ar.heap ar.cells ar.ctr ar.units ar.off hu c :=
  h.prom_keep (fun _ _ _ _ => by rw [hp]) fun _ _ _ _ hm => hp ▸ hm

/-- **Every step from `PreSA` off the output `write` is matched**, for
rows under any `msOfAX … ab` (`pre_stepS` with the arena): thread 0 is at no
`write(1, …)` (`hne`). -/
theorem pre_stepAX {ab : Option (State → Prop)} (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab)
    (hsafe : SrcSafeS P p I) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hps : PromSharedA Λ P p G own I rS Tk μ ar) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev} (h : PreSA Λ P p G own I rS Tk μ ar t s)
    (hne : ∀ th buf n, t.1.threads = #[th] → abi.atSys th.st = true → Kernel.callOf abi th ≠ some (.write 1 buf n))
    (hs : T.M.Step μ tid t es t') :
    ∃ s', (SrcSem.source P p).Run s (obs es) s' ∧ RSA Λ P p G own I rS Tk μ ar t' s' := by
  have hpre := h
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, hz, hh, hwr, hcert0, hs0, hσ, hp, hI, hhi, hw,
    hb, hinv, hown, hmi, hfi, hgi, hoo, hai, hfr, hco, tr, hreach⟩ := h
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
  · -- the take: a local run of the source
    obtain ⟨a, ha, hpc⟩ := htk
    obtain ⟨hntk, ⟨n, sz, hcn⟩, hsys, -, -, -, -, hrun⟩ := hT.site _ _ _ _ _ hI a ha hpc
    have hat : T.M.AtSite μ .take t 0 := ⟨a, ha, th, ht1, hpc⟩
    have hnr : ¬ T.M.AtSite μ .release t 0 := fun ⟨a', ha', t2, ht2, hpc'⟩ => by
      cases (show some t2 = some th from ht2.symm.trans ht1)
      exact hN.noSite _ _ _ _ _ hI a' ha' hpc'
    have htake := (Kernel.step_at_take ht1 hsys hat hnr hs).2
    obtain ⟨hes, rfl⟩ := step_takeA hN hT ht1 hI ha hpc hs
    subst hes
    have hsa : Kernel.siteAt abi μ th.st = some .take := by
      unfold Kernel.siteAt; rw [ite_eq_left_iff.mpr (fun h => absurd (by rw [ha, ← hpc]; rfl) h)]
    have hca := Kernel.certAfter_take ht1 htake hsa
      hsys (X64.deps_of_atNop (atNop_of_cellAt hcn)) (fun a _ => by rw [hk]; exact hz a) hcert0
    obtain ⟨c', fs', hlr, hI', htk'⟩ := hrun t.2.pmem
    have hj : j = 0 := by
      rcases hwr with h | ⟨h, -⟩
      · exact h
      · rw [hsys] at h; cases h
    subst hj
    obtain rfl : hl = [] := by
      rcases hh with ⟨h, -⟩ | ⟨-, h, -⟩
      · exact h
      · exact absurd h hntk
    have hk' : ({ t.2 with held := (0, rS) :: t.2.held, pmem := Kernel.eraseRange t.2.pmem rS } : Kernel.KState) =
        KS E Λ 0 [(0, rS)] (Kernel.eraseRange pm rS) := by rw [hk]; rfl
    obtain ⟨s', hrun', hpre'⟩ := pre_localJA (J := I) (u := { th with st := abi.skip (abi.setDmem th.st
        (Kernel.copyRange t.2.pmem (abi.dmem th.st) rS)) })
      (t' := (t.1.withThread 0 _ t.1.mem, _)) hP (withThread_one hth) hk'
      (fun a => by rw [Kernel.byte_eraseRange]; split <;> simp [hz])
      (.inr ⟨rfl, htk', hT.owned _ _ _ _ _ hI' htk'⟩) (hca _ (by erw [withThread_one hth]; rfl)) hs0 hσ
      hp hI' hw ⟨hb.1, hb.2⟩ ⟨hinv.1, hinv.2, hinv.3⟩ hown hmi hfi hgi
      (by show ExtRows.OwnOk (own (abi.skip _) fs') _ _
          rw [hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownTake _ _ _ _ _ hI a ha hpc]; exact hoo)
      (allocInvAt_prom (allocInvAt_frameRun hai hlr) rfl) hfr hco ⟨tr, hreach⟩ hhi hcr
      (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hlr
    exact ⟨s', hrun', .inl hpre'⟩
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
  have hsite := no_siteA hN ht1 hI hnt
  have hready := atSys_of_ready (t := t) (th := th)
  have hsp := no_spawnA (t' := t') hN hT ht1 hI
  have hwj : t.2.wr 0 = j := wr_one hk
  have hwr' := wr_le hk hwr
  rcases X64Ext.step_cases_site ht1 hw hinv hs hsp hsite with
    ⟨rfl, hns, outs, o, hso, ho, rfl, hw', hc⟩ | ⟨rfl, w, rfl, hinv', hc, hwt⟩ | ⟨pk, hsys, hcert, hi⟩
  · -- an instruction
    have hj : j = 0 := by
      rcases hwr with h | ⟨h, -⟩
      · exact h
      · rw [hns] at h; cases h
    subst hj
    exact instr_stepA hP hN hsafe hT hrd hwf hGpl hok hth hk hz hh hs0 hσ hp hI hhi hw hb hinv hown hmi hfi hgi
      hoo hai hfr hco hreach hnt hns hso ho hw' hc
  · -- a promise: the source stutters
    have hlast : t.1.mem.last ≤ (t.1.mem.append w).1.last := by rw [Memory.last_append]; exact Nat.le_succ _
    exact ⟨s, .refl _, .inl ⟨_, th0, j, lbl, lsize, ts, hl, pm, hd, withThread_one hth, ⟨E, hk⟩, hz, hh, hwr, hc, hs0,
      hσ, hp, hI, hhi, hw, ⟨hb.views.mono hlast, hb.regs.mono hlast⟩, hinv', ownMsgs_append hwt hown,
      memIn_append (hps t s th w hpre hth hwt hc).1 hmi,
      ⟨fits_promise_cert_on (soloFit64CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc hfi.1, initFits_append hfi.2 w⟩,
      hgi.append (hps t s th w hpre hth hwt hc).2,
      ownOk_promise hinv.coh hinv.mem.tq_nodup (fun p hp => (hinv.mem.tq_le p hp).2) hoo w, hai.promise w rfl, hfr,
      hco, tr, hreach⟩⟩
  · -- a kernel step
    obtain ⟨hr, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsys hwr'
    have hsys' := hready hr
    obtain ⟨call', hdc, hnx, -⟩ := hN.sysOkX hT hI hsys'
    obtain rfl : call = call' := Option.some.inj (hcall.symm.trans hdc)
    have hnw : ∀ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) ≠ some (.write 1 buf n) :=
      fun buf n => hne th buf n hth hsys'
    have hfd : ∀ fd buf n, call = .write fd buf n → fd ≠ 1 := fun fd buf n he h1 => by
      subst he h1; exact hnw buf n hcall
    rcases hcases with ⟨fd, buf, n, rd', b, u, rfl, rfl, hlt, hrb, hust, hes, rfl⟩ |
      ⟨r, rfl, hx, hg, hev, hmem, u, hu, hsu, hpu⟩ | ⟨hex, -⟩ | ⟨v, rfl, hx⟩
    · -- a byte of a `write` to `fd ≠ 1`: no event
      rw [ite_eq_right_iff.mpr (fun h => absurd h (hfd fd buf n rfl))] at hes
      subst hes
      refine ⟨s, .refl _, .inl ⟨u, th0, j + 1, lbl, lsize, ts, hl, pm, hd, withThread_one hth, ⟨E, by rw [hk]; rfl⟩, hz,
        hust ▸ hh, ?_, hcert u (by rw [withThread_one hth]; rfl), hs0, hσ, hp, hust ▸ hI, hhi, hust ▸ hw,
        ExtThread.bnd_readByte abi hb hrb, ExtThread.inv1_readByte abi hinv hrb, hown, hmi, hfi, hgi,
        by rw [hust, Kernel.readByte_prom hrb]; exact hoo, allocInvAt_prom hai (Kernel.readByte_prom hrb), hfr, hco,
        tr, hreach⟩⟩
      refine .inr ⟨hust ▸ hsys', fd, buf, n, ?_, hwj ▸ hlt⟩
      show Kernel.decode _ (abi.nr u.st) (abi.arg u.st) = _
      rw [hust]; exact hcall
    · -- a return: the row's frame run, then the local run to the successor
      obtain ⟨c₁, fs₁, call', hr0, hd', -, hx'⟩ := hN.sysRowX hT hI hsys' hnw
      obtain rfl : call = call' := Option.some.inj (hcall.symm.trans hd')
      obtain ⟨c', fs', hlr, hI'⟩ := hx' _ hsu
      have hbu : u.Bnd t'.1.mem.last := by
        rw [hmem]
        rcases ExtThread.bnd_sysStep abi ht1 hb hsys with he | ⟨u', he, hb'⟩
        · rw [he, hth] at hu; cases hu; exact hb
        · rw [he] at hu
          obtain rfl : u' = u := Option.some.inj ((show (t.1.withThread 0 u' t.1.mem).threads[0]? = some u' by
            simp only [Config.withThread, hth]; rfl).symm.trans hu)
          exact hb'
      have hu1 : t'.1.threads = #[u] ∧ Inv1 Λ lbl lsize ts u t'.1.mem s.mem := by
        rcases hi with he | ⟨u', he, hinv'⟩
        · rw [he] at hu ⊢; rw [hth] at hu; cases hu; exact ⟨hth, hinv⟩
        · rw [he] at hu ⊢
          have h1 : (t.1.withThread 0 u' t.1.mem).threads = #[u'] := withThread_one hth
          obtain rfl : u' = u := Option.some.inj ((show (t.1.withThread 0 u' t.1.mem).threads[0]? = some u' by
            simp only [Config.withThread, hth]; rfl).symm.trans hu)
          exact ⟨h1, hinv'⟩
      have hk' : t'.2 = KS E Λ 0 hl pm := by
        rcases ExtThread.sysStep_ret_kstate abi ht1 hsys (fun h => hx (Option.some.inj
          (hcall.symm.trans h))) (fun v h => hg v (Option.some.inj (hcall.symm.trans h))) with he | ⟨he, hw0⟩
        · rw [he, hk]; rfl
        · rw [he, hk]
          rcases hwr with rfl | ⟨-, fd, buf, n, hc', -⟩
          · rfl
          · have := hw0 fd buf n hc'; rw [hwj] at this; subst this; rfl
      have hobs : obs es = [] := by
        rcases hev with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
      rw [hobs]
      have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := hsu
      obtain ⟨s', hrun, hpre⟩ := pre_localJA (J := I) (own := own) hP hu1.1 hk' hz
        (hh.of_iff (hT.sys _ _ _ _ _ hI hsys' _ hcall _ hsu') (hT.owned _ _ _ _ _ hI')) (hcert u hu) hs0 hσ hp hI'
        (ExtThread.sysStep_wideInv abi wideInv ht1 hw hsys hwr' hu) hbu hu1.2 (by rw [hmem]; exact hown)
        (by rw [hmem]; exact hmi) (by rw [hmem]; exact hfi) (by rw [hmem]; exact hgi)
        (by rw [hmem, hpu, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'),
              hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hsys' _ hcall _ hsu', hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
            exact hoo)
        (by rw [hmem]; exact allocInvAt_prom (allocInvAt_frameRun hai (hr0.trans hlr)) hpu) hfr hco ⟨tr, hreach⟩
        hhi hcr (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') (hr0.trans hlr)
      exact ⟨s', hrun, .inl hpre⟩
    · exact absurd hex hnx
    · rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨k, rfl, -, rfl, rfl⟩
      · -- `exit_group`: `main`'s exit at depth 0 (off every abort site, `Step.sys`)
        have hoff : ∀ k a, μ.abortAt k = some a → pcOf th.st ≠ a := fun k a ha hpc =>
          exit_off hs (List.mem_singleton_self _) k a ha ⟨th, ht1, hpc⟩
        obtain ⟨c₁, fs₁, call', hr0, hd', ⟨-, -, -, hex⟩, -⟩ := hN.sysRowX hT hI hsys' hnw
        obtain rfl : Kernel.Call.exitGroup v = call' := Option.some.inj (hcall.symm.trans hd')
        obtain ⟨c', hlr, ⟨hfs, hpl⟩, hexit⟩ := hex v rfl (fun ⟨k, a, ha, hpc⟩ => hoff k a ha hpc)
        subst hfs
        have hrun : (SrcSem.source P p).Run s
            (mainExit { s with ths := s.ths.set! 0 { th0 with term := c'.term, env := c'.env, stack := [] } })
            { s with ths := s.ths.set! 0 { th0 with term := c'.term, env := c'.env, stack := [] } } :=
          (hr0.trans (FrameRun.ofLocal hlr [])).run_source hP h0 rfl rfl hσ rfl hp hcr
            (hP.noExit hreach)
        have hlt : 0 < s.ths.size := by rw [hs0]; exact Nat.zero_lt_one
        rw [hexit _ { th0 with term := c'.term, env := c'.env, stack := [] } (by simp [hlt]) rfl rfl rfl] at hrun
        refine ⟨_, hrun, .inr ⟨th, { th0 with term := c'.term, env := c'.env, stack := [] }, j, lbl, lsize, ts, hl, pm,
          _, hth, ⟨E, by rw [hk]⟩, hz, hh, set_one hs0, hσ, hp, .of_placedS (PlacedS.ofNil hpl), hinv, hown, hmi, _,
          reach_run hreach hrun⟩⟩
      · -- an abort: the process ends, the source stutters
        exact ⟨s, .refl _, .inr ⟨th, th0, j, lbl, lsize, ts, hl, pm, _, hth, ⟨E, by rw [hk]⟩, hz, hh, hs0, hσ, hp,
          by have hpl := hN.place _ _ _ _ _ hI; exact hpl, hinv, hown, hmi, tr, hreach⟩⟩

/-- **Every step from `PreSA` is matched** (`pre_stepS` with the arena):
`pre_stepAX`, the rows under `msOfA` at no `write(1, …)` (`NodesA.sysOk`). -/
theorem pre_stepA (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hps : PromSharedA Λ P p G own I rS Tk μ ar) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev} (h : PreSA Λ P p G own I rS Tk μ ar t s)
    (hs : T.M.Step μ tid t es t') :
    ∃ s', (SrcSem.source P p).Run s (obs es) s' ∧ RSA Λ P p G own I rS Tk μ ar t' s' := by
  refine pre_stepAX hP hN hsafe hT hps hrd hwf hGpl hok h (fun th buf n hth hsys hc => ?_) hs
  obtain ⟨th', th0, -, lbl, lsize, -, -, -, hd, hth', -, -, -, -, -, -, -, -, hI, -⟩ := h
  rw [hth] at hth'
  cases (Array.mk.injEq _ _).mp hth' |> List.cons.inj |>.1
  obtain ⟨call, hdc, -, -, hfd⟩ := hN.sysOk hT hI hsys
  exact hfd 1 buf n (Option.some.inj (hdc.symm.trans hc)) rfl

/-- **Every step from `RSA` is matched** (`r_stepS` with the arena): from
`PreSA` by `pre_stepA`; after the exit no thread steps. -/
theorem r_stepA (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hps : PromSharedA Λ P p G own I rS Tk μ ar) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev} (h : RSA Λ P p G own I rS Tk μ ar t s)
    (hs : T.M.Step μ tid t es t') :
    ∃ s', (SrcSem.source P p).Run s (obs es) s' ∧ RSA Λ P p G own I rS Tk μ ar t' s' := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  · exact pre_stepA hP hN hsafe hT hps hrd hwf hGpl hok h hs
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hk]) hs).elim

end Spike.Lib.X64ConsumerA
