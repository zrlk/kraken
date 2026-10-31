/-
**The x86-64 arena consumer's `clone`-path progress, trace invariant and
abort over a held predicate**: the x86-64 side of
`Spike/Lib/A64ConsumerACorrect.lean`'s `pre_progressACH`, `r_progressACH`,
`ti_step_ofACH`, `ti_stepACH`, `ti_runACH`, `r_abortACH` (A64 commit
189f60ec), over `HeldPathS`. Same names, same namespace (`X64ConsumerA`).
-/
import Spike.Lib.X64ConsumerACorrectC
import Spike.Lib.X64ConsumerAStepC

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {E : Entry}

/-- **Before the exit there is progress** at any depth, for rows under any
`NodesA … ab Cl` with thread 0 off `Cl` (`hnc`; at a `Cl` state, a `clone`,
the one-slot configuration faults: `Spike.Lib.WakePre.Pre1.progressClone_of`
there). `pre_progressA`'s argument. Over `HeldPathS`. -/
theorem pre_progressACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H) (hwf : Λ.WF)
    (hsvc : WriteNoPromAH Λ P p G own I H μ ar)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : PreSAH Λ P p G own I H μ ar t s)
    (hnc : ∀ th, t.1.threads = #[th] → ¬ Cl th.st) : T.M.Progress μ t := by
  have hwnp := hsvc t s
  have hpre := h
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, hh, hwr, hcert, hs0, hσ, hp, hI, -, hw, hb,
    hinv, hown, hmi, -, -, -, -, -, -, hre⟩ := h
  have ht : t.1.threads[0]? = some th := by rw [hth]; rfl
  have hrk : t.2.runs 0 = true := by rw [hk]; rfl
  have hxk : t.2.exited = none := by rw [hk]; rfl
  have hruns : T.M.runs t 0 := ⟨⟨th, ht⟩, hxk, by show ¬ (t.2.runs 0 = false); rw [hrk]; simp⟩
  have hnh : th.halted = false := by
    by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
    · obtain ⟨a, ha, hpc⟩ := htk
      obtain ⟨n, sz, hcn⟩ := (hT.site _ _ _ _ _ hI a ha hpc).1
      simp [Thread.halted, Kraken.Promising.Lower.X64.exec_nop hcn]
    cases hs : abi.atSys th.st
    · obtain ⟨c₁, fs₁, -, -, hout⟩ := hN.rowNS hI (fun a ha hpc => htk ⟨a, ha, hpc⟩) hs
      have := Out.exec_isSome rfl hs hout
      simp only [Thread.halted]
      cases he : isa.exec th.st
      · rw [he] at this; cases this
      · simp
    · obtain ⟨sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
      simp [Thread.halted, Kraken.Promising.Lower.X64.exec_syscall hc]
  refine ⟨?_, .inr ⟨⟨0, hxk, hruns.2.2, th, ht, fun h => by rw [hnh] at h; cases h.1⟩, fun tid hl => ?_⟩⟩
  · rintro (⟨tid, m, ⟨⟨t1, ht1⟩, -, -⟩, hns, outs, hs, hm⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, ht1, -, -, hns, hex, htouch⟩))
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      have hs' : stepOne Arch.tso th 0 t.1.mem = some outs := by simp only [stepThread, ht1] at hs; exact hs
      cases hsy : abi.atSys th.st
      · by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
        · obtain ⟨a, ha, hpc⟩ := htk
          obtain ⟨n, sz, hcn⟩ := (hT.site _ _ _ _ _ hI a ha hpc).1
          exact Kraken.Promising.Lower.stepOne_silent_no_error Arch.tso 0 (Kraken.Promising.Lower.X64.exec_nop hcn)
            (Kraken.Promising.Lower.silentTree_done _) hs' m hm
        · obtain ⟨c₁, fs₁, -, -, hout⟩ :=
            hN.rowNS hI (fun a ha hpc => htk ⟨a, ha, hpc⟩) hsy
          exact outA_no_error hsy hout hs' m hm
      · exact hns ⟨th, ht1, hsy⟩
    · unfold Kernel.faultAt at hf
      split at hf
      · rename_i t1 ht1
        obtain ⟨rfl, rfl⟩ := get_one hth ht1
        rw [hnh, Bool.or_false] at hf
        cases hsy : abi.atSys th.st
        · simp [hsy] at hf
        · obtain ⟨call, hd, -, hcl⟩ := hN.sysOkXCT hT.toTakeSiteS hI hsy (hnc th hth)
          rw [show Kernel.callOf abi th = some call from hd] at hf
          cases call with
          | clone st tl => exact hcl st tl rfl
          | _ => simp at hf
      · cases hf
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      rw [hk] at htouch
      exact hN.mapped _ _ _ _ _ hI hns e hex (touches_mono (fun _ _ h => mapped_KS h) htouch)
  · obtain ⟨-, -, t1, ht1, -⟩ := hl
    obtain ⟨rfl, rfl⟩ := get_one hth ht1
    by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
    · -- at the take site: the take
      obtain ⟨a, ha, hpc⟩ := htk
      obtain ⟨⟨n, sz, hcn⟩, -, -⟩ := hT.site _ _ _ _ _ hI a ha hpc
      obtain ⟨hsub, hpos, hrod, hdj, -⟩ := hT.held _ _ _ _ _ _ hI hh a ha hpc
      have hf : Kernel.fresh t (Kernel.siteRange abi th.st) = true := fresh_ofH hwf hk hsub hpos hrod hdj hmi
      exact ⟨[], _, .xfer .take hruns ⟨a, ha, th, ht, hpc⟩
        (Kernel.xfer_take (K := abi) Arch.tso 1 ht hrk hxk (atNop_of_cellAt hcn) hf)⟩
    have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
    have hsite := no_siteA hN ht hI hnt
    cases hs : abi.atSys th.st
    · have hnsys : ¬ T.M.atSys t 0 := fun ⟨t2, ht2, h2⟩ => by
        cases (show some t2 = some th from ht2.symm.trans ht)
        have h3 : abi.atSys th.st = true := h2
        rw [hs] at h3; cases h3
      by_cases hpn : th.prom = []
      · obtain ⟨c₁, fs₁, -, -, hout⟩ := hN.rowNS hI hnt hs
        obtain ⟨outs, o, hso, ho, hpo⟩ :=
          outA_progress (tid := 0) (mem := t.1.mem) hpn hb hs hout
        exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, certOkC_of_prom_nil hpo, rfl⟩)⟩
      · obtain ⟨t', mem', hr, hp'⟩ := hcert
        cases hr with
        | refl => exact absurd hp' hpn
        | step hs1 hrest =>
          obtain ⟨outs, o, hso, ho, rfl⟩ := hs1
          replace hso : stepOne Arch.tso th 0 t.1.mem = some outs :=
            (Kernel.certSem_step_of_not_site (x := t.2) (siteAt_noneA hN hI hnt) hs).symm.trans hso
          exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, ⟨t', mem', hrest, hp'⟩, rfl⟩)⟩
    · have hr := Kernel.ready_of abi (t := th) (c := t) hs hrk hxk
      obtain ⟨call, hd, hnx, hcl⟩ := hN.sysOkXCT hT.toTakeSiteS hI hs (hnc th hth)
      have hc : Kernel.callOf abi th = some call := hd
      have hsys : ∀ c', (kernel 1).sys μ 0 t [] c' → ∃ es c', T.M.Step μ 0 t es c' :=
        fun c' h => ⟨[], c', .sys hruns h (by simp) (by simp) (by simp)⟩
      by_cases hpn : th.prom = []
      rotate_left
      · -- with promises: no `write` (`WriteNoPromA`), none at `exit_group`; elsewhere `Kernel.sys_progress`
        have hsn := siteAt_noneA hN hI hnt
        cases call with
        | write fd buf n => exact absurd (hwnp th hpre hth hs ⟨fd, buf, n, hc⟩) hpn
        | exitGroup v => exact absurd (Kernel.prom_nil_of_exit hsn hs hd (.inr ⟨v, rfl⟩) hcert) hpn
        | exit => exact absurd rfl hnx
        | clone st tl => exact absurd rfl (hcl st tl)
        | _ =>
          obtain ⟨r, es, c', h, hca⟩ := Kernel.sys_progress ht hr hsn hc (fun _ _ _ h => by cases h)
            (fun _ _ h => by cases h) hpn hcert
          obtain rfl := Kernel.sysStep_ret_nil ht hc (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
            (fun h => by cases h) (fun _ h => by cases h) h
          exact hsys c' ⟨.ret r, h, hca⟩
      cases call with
      | write fd buf n =>
        by_cases hj : t.2.wr 0 = 0
        · exact hsys _ (Kernel.sys_writeIntr (K := abi) Arch.tso 1 ht hr hpn hc hj)
        · exact hsys _ (Kernel.sys_writeRet (K := abi) Arch.tso 1 ht hr hpn hc (Nat.pos_of_ne_zero hj))
      | futexWait => exact hsys _ (Kernel.sys_futexWait (K := abi) Arch.tso 1 ht hr hpn hc)
      | futexWake k => exact hsys _ (Kernel.sys_futexWake (K := abi) Arch.tso 1 ht hr hpn hc)
      | rtSigaction => exact hsys _ (Kernel.sys_rtSigaction (K := abi) Arch.tso 1 ht hr hpn hc)
      | archSetFs a => exact hsys _ (Kernel.sys_archSetFs (K := abi) Arch.tso 1 ht hr hpn hc)
      | exitGroup v =>
        by_cases hab : ∃ k a, μ.abortAt k = some a ∧ pcOf th.st = a
        · -- at an abort site: the abort
          obtain ⟨k, a, ha, hpc⟩ := hab
          obtain ⟨-, hv⟩ := hA.at_ _ _ _ _ _ hI k a ha hpc
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroupAbort (K := abi) Arch.tso 1 k ht hr hpn hc (hv v hd))
            (by simp) (fun k' hk => by obtain rfl : k' = k := by simpa using hk
                                       exact ⟨a, ha, th, ht, hpc⟩) (fun e he => by simp at he)⟩
        · have hnoab : ∀ k a, μ.abortAt k = some a → ¬ T.M.AtAddr a t 0 := fun k a ha ⟨t2, ht2, hpc⟩ => by
            cases (show some t2 = some th from ht2.symm.trans ht); exact hab ⟨k, a, ha, hpc⟩
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroup (K := abi) Arch.tso 1 ht hr hpn hc) (by simp)
            (fun k hk => by simp at hk) (fun _ _ => hnoab)⟩
      | exit => exact absurd rfl hnx
      | clone st tl => exact absurd rfl (hcl st tl)

/-- **There is progress from `RS`**, thread 0 off `Cl` (`pre_progressAC`). Over `HeldPathS`. -/
theorem r_progressACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H) (hwf : Λ.WF)
    (hsvc : WriteNoPromAH Λ P p G own I H μ ar)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : RSAH Λ P p G own I H μ ar t s)
    (hnc : ∀ th, t.1.threads = #[th] → ¬ Cl th.st) : T.M.Progress μ t :=
  h.elim (fun h => pre_progressACH hN hA hT hwf hsvc h hnc) post_progressSAH

/-- **`TIC` is kept by every step from thread 0 at a state of the fragment**
(`ti_step_ofA` with the `clone` phase): at a `Cl` state the step is a
refused `clone` (one slot, none dormant), which emits `cloneErr`; elsewhere
`Ac` is not entered (`AbortPathSC.instrC`, `sysC`, `takeC`). Over `HeldPathS`. -/
theorem ti_step_ofACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hC : ClonePathS p I Cl) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {H : State → List (Nat × Range) → Prop}
    (hT : HeldPathS Λ p μ I H)
    {t t' : T.M.Cfg} {tid : Nat} {es pre : List Ev} {th : Thread isa} {j : Nat} {E : Entry}
    {hl : List (Nat × Range)} {pm : _root_.Mem 64} {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat}
    {sm : WeakMem.Memory} {c : Ctl} {fs : List TermRun.Frame}
    (hth : t.1.threads = #[th]) (hk : t.2 = KS E Λ j hl pm) (hwr : WrOk th j) (hI : I lbl lsize th.st c fs)
    (hw : WideSt th.st) (hinv : Inv1 Λ lbl lsize ts th t.1.mem sm)
    (hs : T.M.Step μ tid t es t') (hti : TIC Ab Ac pre t) : TIC Ab Ac (pre ++ es) t' := by
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  have hget : ∀ {v : Thread isa} {mem : Memory} {u : Thread isa},
      (t.1.withThread 0 v mem).threads[0]? = some u → u = v :=
    fun h => by
      simp only [Config.withThread, hth] at h
      exact (Option.some.inj h).symm
  by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
  · -- the take enters neither phase (`AbortPathSC.take`, `takeC`)
    obtain ⟨a, ha, hpc⟩ := htk
    obtain ⟨-, rfl⟩ := step_takeAT hN hT.toTakeSiteS ht1 hI ha hpc hs
    refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
    · by_cases hab0 : Ab th.st
      · exact List.mem_append_left _ (hti.1 th ht1 hab0)
      obtain rfl := hget hu
      exact absurd hab (hA.take _ _ _ _ _ hI hab0 a ha hpc _)
    · by_cases hac0 : Ac th.st
      · exact List.mem_append_left _ (hti.2 th ht1 hac0)
      obtain rfl := hget hu
      exact absurd hac (hA.takeC _ _ _ _ _ hI hac0 a ha hpc _)
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
  have hsite := no_siteA hN ht1 hI hnt
  by_cases hcl : Cl th.st
  · -- at a `clone`: its refusal, with `cloneErr`
    obtain ⟨hsys', st, tl, hdc⟩ := hC.svc _ _ _ _ _ hI hcl
    have h1 : t.2.slots.size = 1 := by rw [hk]; rfl
    have hr0 : t.2.runs 0 = true := by rw [hk]; rfl
    obtain ⟨rfl, r, hr, rfl⟩ := Spike.Lib.CloneOne.clone_step_nodormant (Spike.Lib.CloneOne.nodormant_one h1 hr0)
      ht1 hsys' hdc hsite hs
    refine ⟨fun u hu hab => ?_, fun _ _ _ => List.mem_append_right _ (List.mem_singleton_self _)⟩
    by_cases hab0 : Ab th.st
    · exact List.mem_append_left _ (hti.1 th ht1 hab0)
    obtain rfl := hget hu
    obtain ⟨fd, buf, n, he, -⟩ := hA.sys _ _ _ _ _ hI hab0 hsys' _ hdc _ (ret_mem_certSuccs_clone hr)
      (by rw [← Kernel.retThread_st (K := abi)]; exact hab)
    cases he
  rcases X64Ext.step_cases_site ht1 hw hinv hs (no_spawnACT hN hT.toTakeSiteS ht1 hI hcl) hsite with
    ⟨rfl, hns, outs, o, hso, ho, rfl, -, -⟩ | ⟨rfl, w, rfl, -, -, -⟩ | ⟨pk, hsys, -, -⟩
  · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
    · by_cases hab0 : Ab th.st
      · exact List.mem_append_left _ (hti.1 th ht1 hab0)
      obtain rfl := hget hu
      exact absurd hab (stepOne_allInv Arch.tso hso ho (hA.instr _ _ _ _ _ hI hab0 hns)
        ⟨fun _ => trivial, fun _ _ => trivial⟩).1
    · by_cases hac0 : Ac th.st
      · exact List.mem_append_left _ (hti.2 th ht1 hac0)
      obtain rfl := hget hu
      exact absurd hac (stepOne_allInv Arch.tso hso ho (hA.instrC _ _ _ _ _ hI hac0 hns)
        ⟨fun _ => trivial, fun _ _ => trivial⟩).1
  · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
    · obtain rfl := hget hu
      exact List.mem_append_left _ (hti.1 _ ht1 hab)
    · obtain rfl := hget hu
      exact List.mem_append_left _ (hti.2 _ ht1 hac)
  · obtain ⟨hr, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsys (wr_le hk hwr)
    rcases hcases with ⟨fd, buf, n, rd', b, u', rfl, rfl, -, -, hust, -, rfl⟩ |
      ⟨r, rfl, -, -, -, -, u', hu', hsu, -⟩ | ⟨-, -, -, rfl⟩ | ⟨v, rfl, ⟨-, -, rfl⟩ | ⟨k, -, -, -, rfl⟩⟩
    · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
      · obtain rfl := hget hu
        exact List.mem_append_left _ (hti.1 _ ht1 (hust ▸ hab))
      · obtain rfl := hget hu
        exact List.mem_append_left _ (hti.2 _ ht1 (hust ▸ hac))
    · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
      · by_cases hab0 : Ab th.st
        · exact List.mem_append_left _ (hti.1 th ht1 hab0)
        refine List.mem_append_right _ ?_
        have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := Option.some.inj (hu'.symm.trans hu) ▸ hsu
        obtain ⟨fd, buf, n, rfl, hrf⟩ := hA.sys _ _ _ _ _ hI hab0 (atSys_of_ready hr) _ hcall _ hsu' hab
        obtain ⟨hc', hes⟩ := sysStep_write_ret ht1 hcall (wr_le hk hwr _ _ _ hcall) hsys
        have hu2 : u = Kernel.retThread abi th r := by rw [hc'] at hu; exact hget hu
        rw [hes (hrf r (by rw [hu2, Kernel.retThread_st]))]
        exact List.mem_singleton_self _
      · by_cases hac0 : Ac th.st
        · exact List.mem_append_left _ (hti.2 th ht1 hac0)
        have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := Option.some.inj (hu'.symm.trans hu) ▸ hsu
        exact absurd hac (hA.sysC _ _ _ _ _ hI hac0 (atSys_of_ready hr) hcl _ hcall _ hsu')
    all_goals
      refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
      · obtain rfl : th = u := Option.some.inj (ht1.symm.trans hu)
        exact List.mem_append_left _ (hti.1 _ ht1 hab)
      · obtain rfl : th = u := Option.some.inj (ht1.symm.trans hu)
        exact List.mem_append_left _ (hti.2 _ ht1 hac)

/-- **`TIC` is kept by every step from `RS`** (`ti_step_ofAC`). Over `HeldPathS`. -/
theorem ti_stepACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hC : ClonePathS p I Cl) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H) {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es pre : List Ev} (h : RSAH Λ P p G own I H μ ar t s)
    (hs : T.M.Step μ tid t es t') (hti : TIC Ab Ac pre t) : TIC Ab Ac (pre ++ es) t' := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  rotate_left
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hk]) hs).elim
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, -, hwr, -, hs0, hσ, hp, hI, -, hw, hb, hinv,
    hown, hmi, -⟩ := h
  exact ti_step_ofACH hN hC hA hT hth hk hwr hI hw hinv hs hti

/-- **`TIC` along every run from `RS`.** Over `HeldPathS`. -/
theorem ti_runACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hC : ClonePathS p I Cl) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H)
    (hstep : ∀ {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev},
      RSAH Λ P p G own I H μ ar t s → T.M.Step μ tid t es t' → ∃ s', RSAH Λ P p G own I H μ ar t' s')
    {t t' : T.M.Cfg} {tr : List Ev} (hr : T.M.Run μ t tr t') :
    ∀ {s pre}, RSAH Λ P p G own I H μ ar t s → TIC Ab Ac pre t → TIC Ab Ac (pre ++ tr) t' := by
  induction hr with
  | refl => intro s pre _ h; rwa [List.append_nil]
  | step hs _ ih =>
    intro s pre hR h
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨s', hR'⟩ := hstep hR hs
    rw [← List.append_assoc]
    exact ih hR' (ti_stepACH hN hC hA hT hR hs h)

/-- **An abort from `RS` is justified**, with the `clone` phase
(`r_abortA`; a `threads` abort in the phase `Ac` by `TIC`, after a refused
`clone`: `AbortJustified.of_cloneErr`). Over `HeldPathS`. -/
theorem r_abortACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hsafe : SrcSafeS P p I) (hwf : Λ.WF) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {B : Budget} (hB : B.cells = ar.cells) {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H)
    {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es tr : List Ev} {k : AbortKind} (h : RSAH Λ P p G own I H μ ar t s)
    (hti : TIC Ab Ac tr t) (hs : T.M.Step μ tid t es t') (hk : Ev.abort k ∈ es) :
    ∃ w i, Components T.M Λ w t ((SrcSem.source P p).core s) ∧ w.thr i = some tid ∧
      AbortJustified B (SrcSem.source P p) tr s i k := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hx⟩, _⟩
  rotate_left
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hx]) hs).elim
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk'⟩, -, hh, -, -, hs0, hσ, hp, hI, -, -, -, hinv,
    hown, hmi, -, -, -, hai, hfr, -, tr', hre⟩ := h
  obtain ⟨a, ha, t2, ht2, hpc⟩ := hs.abort_at hk
  obtain ⟨rfl, rfl⟩ := get_one hth ht2
  obtain ⟨w, hw, hw0⟩ := components_oneSXH hwf hth (by rw [hk']; rfl) (hT.own _ _ hh) hmi hs0
    (by have hpl := hN.place _ _ _ _ _ hI; exact hpl) hinv hown
  refine ⟨w, 0, hw, hw0, ?_⟩
  have hi : s.ths[0]? = some th0 := by rw [hs0]; rfl
  obtain ⟨⟨rfl, hab⟩ | ⟨rfl, hc, he⟩ | ⟨rfl, hheap⟩ | ⟨rfl, hac⟩, -⟩ := hA.at_ _ _ _ _ _ hI k a ha hpc
  · exact hti.1 th ht2 hab
  · exact abortJustified_overflow_sourceS hi hc hσ hp (noBigNumT_of_envSmallS hi he)
  · have hr := hheap.at_heapCtr hai.heapCtrA
    exact abortJustified_heap_sourceA hi (by rw [hB]; exact hr) hσ hp
      (Spike.Lib.fresh_of_placed (fun m hmem => (hinv.mem.lbl_mem m hmem).imp fun _ h => h.1) hfr.fresh)
      (hsafe.box _ _ hre)
  · exact AbortJustified.of_cloneErr (hti.2 th ht2 hac)

end Spike.Lib.X64ConsumerA

/-- info: 'Spike.Lib.X64ConsumerA.pre_progressACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.pre_progressACH

/-- info: 'Spike.Lib.X64ConsumerA.r_progressACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.r_progressACH

/-- info: 'Spike.Lib.X64ConsumerA.ti_step_ofACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ti_step_ofACH

/-- info: 'Spike.Lib.X64ConsumerA.ti_stepACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ti_stepACH

/-- info: 'Spike.Lib.X64ConsumerA.ti_runACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ti_runACH

/-- info: 'Spike.Lib.X64ConsumerA.r_abortACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.r_abortACH
