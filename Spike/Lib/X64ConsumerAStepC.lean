/-
**A step of the x86-64 arena consumer with the `clone` path**: the x86-64
side of `Spike/Lib/A64ConsumerAStep.lean`'s `pre_stepAXC` and
`pre_stepAXCH`, which
`Spike/Lib/X64ConsumerAStep.lean` lacks. Same names, same namespace
(`X64ConsumerA`).

- `pre_stepAXC`: `pre_stepAX` under `NodesA … Cl` with the `clone` path
  `ClonePathS p I Cl`: at a `Cl` state the step is a refusal of the `clone`
  (`Spike.Lib.CloneOne.clone_step_nodormant`), landing by `hC.err`;
  elsewhere the rows off `Cl` (`NodesA.sysRowXC`, `no_spawnAC`).
- `pre_stepAXCH`: the same over `HeldPathS` (`pre_stepAXH`).

**Unlike AArch64**: `pre_stepAX`/`pre_stepAXH` stay direct proofs (on
AArch64 they are `pre_stepAXC`/`pre_stepAXCH` at `ClonePathS.none`), so the
existing x86-64 files are unchanged.
-/
import Spike.Lib.X64ConsumerACoreH
import Spike.Lib.X64ConsumerAStep
import Spike.Lib.X64ConsumerAInstrH
import Spike.Lib.CloneOne
import Spike.Lib.Handover

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena}

/-- **Every step from `PreSA` off the output `write` is matched**, for
rows under any `msOfAX … ab` and `NodesA … Cl` with the `clone` path `hC`
(`pre_stepS` with the arena): thread 0 is at no `write(1, …)` (`hne`); at a
`Cl` state the step is a refusal of the `clone` (one slot, none dormant),
landing by `hC.err`. -/
theorem pre_stepAXC {ab : Option (State → Prop)} {Cl : State → Prop} (hP : HookOK P p)
    (hN : NodesA Λ p μ rd G own ar I ab Cl) (hC : ClonePathS p I Cl)
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
  by_cases hcl : Cl th.st
  · -- at a `clone`: the kernel's refusal, the row's frame run by `hC.err`
    obtain ⟨hsys', st, tl, hdc⟩ := hC.svc _ _ _ _ _ hI hcl
    have hsi := siteAt_noneA hN hI hnt
    have h1 : t.2.slots.size = 1 := by rw [hk]; rfl
    have hr0 : t.2.runs 0 = true := by rw [hk]; rfl
    obtain ⟨rfl, r, hr, rfl⟩ := Spike.Lib.CloneOne.clone_step_nodormant (Spike.Lib.CloneOne.nodormant_one h1 hr0)
      ht1 hsys' hdc hsite hs
    have hj : j = 0 := by
      rcases hwr with h | ⟨-, fd, buf, n, hc', -⟩
      · exact h
      · cases (show some (Kernel.Call.clone st tl) = some (.write fd buf n) from hdc.symm.trans hc')
    subst hj
    have hpn : th.prom = [] := Spike.Lib.Handover.prom_nil_of_clone (K := abi) hsi hsys' hdc hcert0
    obtain ⟨c', fs', hlr, hI'⟩ := hC.err _ _ _ _ _ hI hcl r hr
    have hsu := ret_mem_certSuccs_clone (s := th.st) (st := st) (tl := tl) hr
    have hst : (Kernel.retThread abi th r).st = abi.ret th.st r := Kernel.retThread_st (K := abi) th r
    have hpr : (Kernel.retThread abi th r).prom = th.prom := Kernel.retThread_prom (K := abi) th r
    obtain ⟨s', hrun', hpre'⟩ := pre_localJA (J := I) (own := own) (u := Kernel.retThread abi th r)
      (t' := (t.1.withThread 0 (Kernel.retThread abi th r) t.1.mem, t.2)) hP (withThread_one hth) hk hz
      (hh.of_iff (by rw [hst]; exact hT.sys _ _ _ _ _ hI hsys' _ hdc _ hsu)
        (fun h => by rw [hst] at h ⊢; exact hT.owned _ _ _ _ _ hI' h))
      (certOkC_of_prom_nil (by rw [hpr]; exact hpn)) hs0 hσ hp (by rw [hst]; exact hI')
      (by rw [hst]; exact wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)) (ExtThread.bnd_retThread abi hb r)
      (ExtThread.inv1_retThread abi hinv r) hown hmi hfi hgi
      (by rw [hst, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'),
            hN.ownSys _ _ _ _ _ (IRun.of hI) hsys' _ hdc _ hsu]
          exact hoo)
      (allocInvAt_prom (allocInvAt_frameRun hai hlr) hpr) hfr hco ⟨tr, hreach⟩ hhi hcr
      (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hlr
    exact ⟨s', hrun', .inl hpre'⟩
  have hready := atSys_of_ready (t := t) (th := th)
  have hsp := no_spawnAC (t' := t') hN hT ht1 hI hcl
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
    obtain ⟨call', hdc, hnx, -⟩ := hN.sysOkXC hT hI hsys' hcl
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
      obtain ⟨c₁, fs₁, call', hr0, hd', -, hx'⟩ := hN.sysRowXC hT hI hsys' hnw hcl
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
        obtain ⟨c₁, fs₁, call', hr0, hd', ⟨-, -, -, hex⟩, -⟩ := hN.sysRowXC hT hI hsys' hnw hcl
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

/-- **Every step from `PreSAH` off the output `write` is matched**, for
rows under any `msOfAX … ab` and `NodesA … Cl` with the `clone` path `hC`
(`pre_stepS` with the arena): thread 0 is at no `write(1, …)` (`hne`); at a
`Cl` state the step is a refusal of the `clone` (one slot, none dormant),
landing by `hC.err`. Over `HeldPathS` (`pre_stepAXC`). -/
theorem pre_stepAXCH {ab : Option (State → Prop)} {Cl : State → Prop} (hP : HookOK P p)
    (hN : NodesA Λ p μ rd G own ar I ab Cl) (hC : ClonePathS p I Cl)
    (hsafe : SrcSafeS P p I) {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H)
    (hps : PromSharedAH Λ P p G own I H μ ar) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev} (h : PreSAH Λ P p G own I H μ ar t s)
    (hne : ∀ th buf n, t.1.threads = #[th] → abi.atSys th.st = true → Kernel.callOf abi th ≠ some (.write 1 buf n))
    (hs : T.M.Step μ tid t es t') :
    ∃ s', (SrcSem.source P p).Run s (obs es) s' ∧ RSAH Λ P p G own I H μ ar t' s' := by
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
    obtain ⟨⟨n, sz, hcn⟩, hsys, hrun⟩ := hT.site _ _ _ _ _ hI a ha hpc
    obtain ⟨-, -, -, -, hHt⟩ := hT.held _ _ _ _ _ _ hI hh a ha hpc
    have hat : T.M.AtSite μ .take t 0 := ⟨a, ha, th, ht1, hpc⟩
    have hnr : ¬ T.M.AtSite μ .release t 0 := fun ⟨a', ha', t2, ht2, hpc'⟩ => by
      cases (show some t2 = some th from ht2.symm.trans ht1)
      exact hN.noSite _ _ _ _ _ hI a' ha' hpc'
    have htake := (Kernel.step_at_take ht1 hsys hat hnr hs).2
    obtain ⟨hes, rfl⟩ := step_takeAT hN hT.toTakeSiteS ht1 hI ha hpc hs
    subst hes
    have hsa : Kernel.siteAt abi μ th.st = some .take := by
      unfold Kernel.siteAt; rw [ite_eq_left_iff.mpr (fun h => absurd (by rw [ha, ← hpc]; rfl) h)]
    have hca := Kernel.certAfter_take ht1 htake hsa
      hsys (X64.deps_of_atNop (atNop_of_cellAt hcn)) (fun a _ => by rw [hk]; exact hz a) hcert0
    obtain ⟨c', fs', hlr, hI'⟩ := hrun t.2.pmem
    have hj : j = 0 := by
      rcases hwr with h | ⟨h, -⟩
      · exact h
      · rw [hsys] at h; cases h
    subst hj
    have hk' : ({ t.2 with
          held := (0, Kernel.siteRange abi th.st) :: t.2.held,
          pmem := Kernel.eraseRange t.2.pmem (Kernel.siteRange abi th.st) } : Kernel.KState) =
        KS E Λ 0 ((0, Kernel.siteRange abi th.st) :: hl) (Kernel.eraseRange pm (Kernel.siteRange abi th.st)) := by
      rw [hk]; rfl
    obtain ⟨s', hrun', hpre'⟩ := pre_localJAH (J := I) (u := { th with st := abi.skip (abi.setDmem th.st
        (Kernel.copyRange t.2.pmem (abi.dmem th.st) (Kernel.siteRange abi th.st))) })
      (t' := (t.1.withThread 0 _ t.1.mem, _)) hP (withThread_one hth) hk'
      (fun a => by rw [Kernel.byte_eraseRange]; split <;> simp [hz])
      (hHt _ _ _ hI') (hca _ (by erw [withThread_one hth]; rfl)) hs0 hσ
      hp hI' hw ⟨hb.1, hb.2⟩ ⟨hinv.1, hinv.2, hinv.3⟩ hown hmi hfi hgi
      (by show ExtRows.OwnOk (own (abi.skip _) fs') _ _
          rw [hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownTake _ _ _ _ _ hI a ha hpc]; exact hoo)
      (allocInvAt_prom (allocInvAt_frameRun hai hlr) rfl) hfr hco ⟨tr, hreach⟩ hhi hcr
      (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hlr
    exact ⟨s', hrun', .inl hpre'⟩
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
  have hsite := no_siteA hN ht1 hI hnt
  by_cases hcl : Cl th.st
  · -- at a `clone`: the kernel's refusal, the row's frame run by `hC.err`
    obtain ⟨hsys', st, tl, hdc⟩ := hC.svc _ _ _ _ _ hI hcl
    have hsi := siteAt_noneA hN hI hnt
    have h1 : t.2.slots.size = 1 := by rw [hk]; rfl
    have hr0 : t.2.runs 0 = true := by rw [hk]; rfl
    obtain ⟨rfl, r, hr, rfl⟩ := Spike.Lib.CloneOne.clone_step_nodormant (Spike.Lib.CloneOne.nodormant_one h1 hr0)
      ht1 hsys' hdc hsite hs
    have hj : j = 0 := by
      rcases hwr with h | ⟨-, fd, buf, n, hc', -⟩
      · exact h
      · cases (show some (Kernel.Call.clone st tl) = some (.write fd buf n) from hdc.symm.trans hc')
    subst hj
    have hpn : th.prom = [] := Spike.Lib.Handover.prom_nil_of_clone (K := abi) hsi hsys' hdc hcert0
    obtain ⟨c', fs', hlr, hI'⟩ := hC.err _ _ _ _ _ hI hcl r hr
    have hsu := ret_mem_certSuccs_clone (s := th.st) (st := st) (tl := tl) hr
    have hst : (Kernel.retThread abi th r).st = abi.ret th.st r := Kernel.retThread_st (K := abi) th r
    have hpr : (Kernel.retThread abi th r).prom = th.prom := Kernel.retThread_prom (K := abi) th r
    obtain ⟨s', hrun', hpre'⟩ := pre_localJAH (J := I) (own := own) (u := Kernel.retThread abi th r)
      (t' := (t.1.withThread 0 (Kernel.retThread abi th r) t.1.mem, t.2)) hP (withThread_one hth) hk hz
      (by rw [hst]; exact hT.sys _ _ _ _ _ _ hI hh hsys' _ hdc _ hsu _ _ _ _ hI')
      (certOkC_of_prom_nil (by rw [hpr]; exact hpn)) hs0 hσ hp (by rw [hst]; exact hI')
      (by rw [hst]; exact wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)) (ExtThread.bnd_retThread abi hb r)
      (ExtThread.inv1_retThread abi hinv r) hown hmi hfi hgi
      (by rw [hst, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'),
            hN.ownSys _ _ _ _ _ (IRun.of hI) hsys' _ hdc _ hsu]
          exact hoo)
      (allocInvAt_prom (allocInvAt_frameRun hai hlr) hpr) hfr hco ⟨tr, hreach⟩ hhi hcr
      (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hlr
    exact ⟨s', hrun', .inl hpre'⟩
  have hready := atSys_of_ready (t := t) (th := th)
  have hsp := no_spawnACT (t' := t') hN hT.toTakeSiteS ht1 hI hcl
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
    exact instr_stepAH hP hN hsafe hT hrd hwf hGpl hok hth hk hz hh hs0 hσ hp hI hhi hw hb hinv hown hmi hfi hgi
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
    obtain ⟨call', hdc, hnx, -⟩ := hN.sysOkXCT hT.toTakeSiteS hI hsys' hcl
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
      obtain ⟨c₁, fs₁, call', hr0, hd', -, hx'⟩ := hN.sysRowXCT hT.toTakeSiteS hI hsys' hnw hcl
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
      obtain ⟨s', hrun, hpre⟩ := pre_localJAH (J := I) (own := own) hP hu1.1 hk' hz
        (hT.sys _ _ _ _ _ _ hI hh hsys' _ hcall _ hsu' _ _ _ _ hI') (hcert u hu) hs0 hσ hp hI'
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
        obtain ⟨c₁, fs₁, call', hr0, hd', ⟨-, -, -, hex⟩, -⟩ := hN.sysRowXCT hT.toTakeSiteS hI hsys' hnw hcl
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

end Spike.Lib.X64ConsumerA

/-- info: 'Spike.Lib.X64ConsumerA.pre_stepAXC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.pre_stepAXC

/-- info: 'Spike.Lib.X64ConsumerA.pre_stepAXCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.pre_stepAXCH
