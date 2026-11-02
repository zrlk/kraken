/-
**hello.w on AArch64: a step of main after the spawn keeps `Post`** (row
`HelloAssembly.HelloRows.post_step0`, the twin of
`WakeM0Post.post_step0_of` at hello's worker data `PT1h` and kernel
relation `KRH`; the twin of `WakeM0Rt`, `WakeM0Prom`, `WakeM0Flag` and
`WakeM0Post`, see `Spike/Lib/HelloM0Keep.lean`).

- `post_frame0H`, `post_local0H`, `PartsH.prom_le0`, `post_rtw0H`,
  `post_rtStore0H`, `post_rtRmw0H`, `prom_good0H`, `post_prom0H`,
  `post_flag0H`, `post_step0H_of`: as wake's (without the `H`).
- `mainCompatH`: `MainCompatH` from `HelloCompat` (`relW` changes `PT1`
  only, so wake's `WCompat.cT` at `relW` is about `Q`'s `C` and `SR`).
- `post_step0H`: `HelloRows.post_step0`'s statement, at `Q.PT0 = PT0 M`,
  `Q.KR = KRH r0 r1`, `Q.own = wakeOwn` (each `rfl` at `HelloQ.helloQ`) and
  main's source `helloSrc`.
-/
import Spike.Lib.HelloM0Keep
import Spike.Lib.HelloAssembly

namespace Spike.Lib.HelloM0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc Spike.Lib.WorkerSrcStep
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt Spike.Lib.WakeW1 Spike.Lib.WakeM0
open Spike.Lib.WakeMLive (wlRet MainLive)
open Spike.Lib.HelloW1 (WSideH PT1h PartsH post_partsH)
open Spike.Lib.HelloKRE (KRHE)
open Spike.Lib.A64HelloWriteK (KRH krh_live)
open Scc.Sem.MemRel (SLatest)

section

variable {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **`Post` after a step of main**, the protocol given at the new target
memory and mirrored promises (`post_frame0H'` with `hprot` and `hm` in one). -/
theorem post_frame0H (hC : MainCompatH Q D) (hPT0 : Q.PT0 = PT0 M) (hKR : Q.KR = KRHE D r0 r1)
    {s' : TermRun.Cfg} {t0' : Thread isaLSE2} {s0' : TermRun.TTh} {mem' : Memory} {tp' : List Nat}
    (hth : t.1.threads = #[t0, t1]) (hs' : s'.ths = #[s0', s1]) (hs1 : s.ths[1]? = some s1)
    (hsm : s'.mem = s.mem) (hstr : s'.trace = s.trace)
    (hpt1 : HelloEmitPh.PT1hE D w t.1.mem s.mem t1 s1)
    (hprot : CProt (Q.SR w) (Q.C w) oc mem' t1 s.mem s1 ts tp' sp)
    (hkr : Q.KR w t s)
    (hcore : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
      (fun i => if i = 0 then Q.own w 0 t0'.st s0'.stack else Q.own w 1 t1.st s1.stack)
      mem' t0' t1 s'.mem s0' s1 ts tp' sp)
    (hpre : PreC (Q.SR w) (Q.C w).cT mem' t0'.views) (hpt0 : PT0 M w mem' s'.mem t0' s0')
    (hlive : s0'.term ≠ wlRet) :
    Q.Post Λ (t.1.withThread 0 t0' mem', t.2) s' := by
  have hth' := withThread0 (t0' := t0') (mem := mem') hth
  refine ⟨w, ⟨t0', t1, s0', s1, ts, tp', sp, hth', hs', hcore, ?_, ?_, oc, ?_⟩, ?_⟩
  · simp only [WakeRel.PTw, ite_true]
    exact ⟨hpre, by rw [hPT0]; exact hpt0⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hC.pt1]
    rw [hsm]
    exact hpt1
  · rw [hsm]; exact hprot
  · rw [hKR] at hkr ⊢
    obtain ⟨⟨hn, h0, h1, hh, -, htr⟩, hlk⟩ := hkr
    refine ⟨⟨hn, h0, h1, hh, fun _ s0'' h => ?_, by simp only [SrcSem.traceOf, hstr] at htr ⊢; exact htr⟩,
      HelloKRE.lk_frame0 hlk ?_ (by rw [hs', hs1]; rfl) rfl⟩
    · rw [hs'] at h
      cases (show some s0' = some s0'' from h)
      exact hlive
    · show (t.1.withThread 0 t0' mem').threads[1]? = t.1.threads[1]?
      rw [hth', hth]; rfl

/-- **A step of main matched by a local run of main's source keeps
`Post`**: thread 0 replaced by `t0'` and the memory by `mem'`, the core,
the protocol and `PreC` at the new target state (main's old source
thread), main's source after a local run from its control to `c'` with
`Mi w t0'.st c'`. -/
theorem post_local0H (hC : MainCompatH Q D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {t0' : Thread isaLSE2} {mem' : Memory} {tp' : List Nat} {c' : Ctl}
    (hcore : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
      (fun i => if i = 0 then Q.own w 0 t0'.st s0.stack else Q.own w 1 t1.st s1.stack) mem' t0' t1 s.mem s0 s1
      ts tp' sp)
    (hprot : CProt (Q.SR w) (Q.C w) oc mem' t1 s.mem s1 ts tp' sp)
    (hpre : PreC (Q.SR w) (Q.C w).cT mem' t0'.views)
    (hr : LocalRun M.p (Ctl.of s0) c') (hmi : M.Mi w t0'.st c') :
    ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 t0' mem', t.2) s' := by
  have hpt0 := h.pt0M hPT0
  have hctl' := localRun_mCtl hr (h.mCtl hPT0) M.wl
  let s0' : TermRun.TTh := { s0 with term := c'.term, env := c'.env }
  have hc'eq : Ctl.of s0' = c' := by
    obtain ⟨tm, en, hd⟩ := c'
    have : hd = none := hctl'.hold
    subst this; rfl
  have hlive : c'.term ≠ wlRet := hC0.live0 w _ _ hmi
  have hs' : ({ s with ths := s.ths.set! 0 s0' } : TermRun.Cfg).ths = #[s0', s1] := by
    show s.ths.set! 0 s0' = _
    rw [h.ths]; rfl
  have hex' : SrcSem.mainExit { s with ths := s.ths.set! 0 s0' } = [] :=
    mainExit_of_notRet hs' hctl'.term hlive
  have hrun : (srcS M.p arch).Run s [] { s with ths := s.ths.set! 0 s0' } :=
    WakeM0Src.localRunS_run_source_0 (P := srcPo 2 arch M.p) rfl hr.toS h.s0_get rfl rfl hpt0.2.2.1
      hpt0.2.1 hpt0.2.2.2.2.2.1 hex'
  refine ⟨_, hrun, post_frame0H (s := s) hC hPT0 hKR h.th hs' h.s1_get rfl rfl h.pt1 hprot h.kr ?_ hpre ?_ hlive⟩
  · exact core0_same hcore (by simp) rfl rfl hcore.bnd0 hcore.cov0 hcore.scov0 hcore.own0 hcore.own_disj
      (fun L v hm => hcore.own_cov 0 L v (by decide) hm) hcore.noProm0
  · exact ⟨.inl (hc'eq ▸ hmi), hpt0.2.1, hpt0.2.2.1, hctl'.term, hctl'.env, hpt0.2.2.2.2.2.1, hpt0.2.2.2.2.2.2⟩

/-- main's promises are at most the memory's last timestamp. -/
theorem PartsM.prom_le0 (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : ∀ p ∈ t0.prom, p ≤ t.1.mem.last := by
  intro p hp
  obtain ⟨-, m, hg, -⟩ := h.core.prom0 p hp
  exact Scc.Sem.Memory.le_last_of_get? hg

/-! ## An out-of-label write of main -/

/-- **An out-of-label write of main keeps `Post`**: the message
`⟨wordLoc a, V, 0⟩` (`a` mapped for writing, so in main's footprint and
outside every label; `V` a 64-bit `G` value) appended, or one of main's
promises of it fulfilled; the new thread's bound, cover, no-promise fact and
`PreC` at the new memory; main's source after a local run into `Mi`. -/
theorem post_rtw0H (hC : MainCompatH Q D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) (hown : Q.own = WakeOwn.wakeOwn) (hwf : Λ.WF)
    (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {t0' : Thread isaLSE2} {mem' : Memory} {a : Nat} {V : Val} {c' : Ctl}
    (hmp : (M.ms w).mp (wordLoc a) true) (hfit : V.toNat < 2 ^ 64) (hG : Q.G w (wordLoc a) V)
    (hcase : (mem' = (t.1.mem.append ⟨wordLoc a, V, 0⟩).1 ∧ t0'.prom = t0.prom) ∨
      (∃ q ∈ t0.prom, t.1.mem.get? q = some ⟨wordLoc a, V, 0⟩ ∧ mem' = t.1.mem ∧ t0'.prom = t0.prom.erase q))
    (hb : t0'.Bnd mem'.last) (hcov : CohCoversL t0'.views t0'.prom mem' ((Q.P w).cov 0))
    (hnp : (Q.P w).noProm t0'.st → t0'.prom = [])
    (hpre : PreC (Q.SR w) (Q.C w).cT t.1.mem t0'.views)
    (hr : LocalRun M.p (Ctl.of s0) c') (hmi : M.Mi w t0'.st c') :
    ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 t0' mem', t.2) s' := by
  obtain ⟨hf, hout, hin⟩ := hC0.mpW0 w _ hmp
  have hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT := by
    obtain ⟨a', hcT, hx, ho⟩ := hC.cT w
    rw [hcT]; exact inLabel_wordLoc h.core.mem hwf hx ho
  have hne : wordLoc a ≠ (Q.C w).cT := fun e => hout (e ▸ hcTin)
  have hown' : ∀ (st : isaLSE2.State) (mem : Memory) (prom : List Nat),
      ExtRows.OwnOk ((fun i => if i = 0 then Q.own w 0 st s0.stack else Q.own w 1 t1.st s1.stack) 0) mem prom := by
    intro st mem prom L v h0; simp [hown, WakeOwn.wakeOwn] at h0
  have hdisj : ∀ (st : isaLSE2.State) L v v', (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 st s0.stack else Q.own w 1 t1.st s1.stack) 0 →
      (L, v') ∈ (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st s1.stack) 1 → False := by
    intro st L v v' h0; simp [hown, WakeOwn.wakeOwn] at h0
  have hocov : ∀ (st : isaLSE2.State) L v, (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 st s0.stack else Q.own w 1 t1.st s1.stack) 0 → (Q.P w).cov 0 L := by
    intro st L v h0; simp [hown, WakeOwn.wakeOwn] at h0
  rcases hcase with ⟨rfl, hp⟩ | ⟨q, hq, hg, rfl, hp⟩
  · -- the append
    have hpl := h.prom_le0
    have hcore := core0_append h.core
      (own' := fun i => if i = 0 then Q.own w 0 t0'.st s0.stack else Q.own w 1 t1.st s1.stack)
      (w := ⟨wordLoc a, V, 0⟩) (t0' := t0') (sm' := s.mem) (s0' := s0) (ts' := ts) (tp' := tp) (sp' := sp)
      (by simp) rfl hf (.inl rfl) (h.core.mem.runtime_write hout)
      (fun k hk => by rw [hp]; exact h.core.tp_prom k hk)
      (fun k w' hk hg' hin' => by
        have hk1 : k ∈ t0.prom ∨ k ∈ t1.prom := by rw [hp] at hk; exact hk
        have hle : k ≤ t.1.mem.last := by
          rcases hk1 with hk0 | hk1
          · exact hpl k hk0
          · obtain ⟨-, w1, hg1, -⟩ := h.core.prom1 k hk1
            exact Scc.Sem.Memory.le_last_of_get? hg1
        rw [Scc.Sem.Memory.get?_append_le hle] at hg'
        exact h.core.prom_tp k w' hk1 hg' hin')
      h.core.sp_prom rfl hin hfit hG hb hcov h.core.frzS h.core.scov0 h.core.scov1 (hown' _ _ _) (hdisj _)
      (hocov _)
      (fun k hk => by
        rw [hp] at hk
        obtain ⟨hTk, w', hg', ht'⟩ := h.core.prom0 k hk
        exact ⟨hTk, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg', ht'⟩)
      hnp
    exact post_local0H hC hC0 hPT0 hKR h hcore (cProt_append0 h.prot hne) (hpre.append h.core.T_le _) hr hmi
  · -- the fulfilment
    have hq0 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) (h.core.prom0 q hq).1
    have hts : ∀ k, ts k ≠ some q := fun k hk =>
      hout (img_inLabel h.core.mem hwf h.core.narrow hk hq0 hg)
    have hTcq : ∀ Tc kc, oc = some (Tc, kc) → Tc ≠ q := by
      rintro Tc kc hoc rfl
      obtain ⟨-, -, -, ⟨w', hg', hl, -⟩, -⟩ := h.prot.some_msg Tc kc hoc
      rw [hg] at hg'; cases hg'
      exact hne hl
    have hcore := core0_fulfil h.core hg hout hts
      (own' := fun i => if i = 0 then Q.own w 0 t0'.st s0.stack else Q.own w 1 t1.st s1.stack)
      (by simp) hp hb hcov (hown' _ _ _) (hdisj _) (hocov _) hnp
    exact post_local0H hC hC0 hPT0 hKR h hcore (cProt_erase h.prot hTcq) hpre hr hmi

/-! ## The runtime-write rows -/

section Rows

variable (hC : MainCompatH Q D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
  (hKR : Q.KR = KRHE D r0 r1) (hown : Q.own = WakeOwn.wakeOwn) (hwf : Λ.WF)
  (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
  {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
  (hso : stepOne Arch.armv8 t0 0 t.1.mem = some outs) (ho : .ok o ∈ outs)
  (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 o.thread o.mem)
include hC hC0 hPT0 hKR hown hwf h hso ho hco

/-- **main's runtime-store row keeps `Post`.** -/
theorem post_rtStore0H {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : isaLSE2.State} {c' : Ctl}
    (hx : t.2.exited = none)
    (he : isaLSE2.exec t0.st = some (.store kr false L V fun _ => .done s')) (hmp : (M.ms w).mp L true)
    (hGV : (M.ms w).G L V) (hr : LocalRun M.p (Ctl.of s0) c') (hX : M.Mi w s' c') :
    ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  have hwide := hC0.wide0 w _ _ (h.mi0 hPT0 hKR hx)
  have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
  have hfit : V.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
  rw [hC0.G0 w] at hGV
  obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
  obtain ⟨hst, hc⟩ := stepOne_store_cases Arch.armv8 he hso ho h.prom_le0
  have hb := (stepOne_bnd _ hso ho h.core.bnd0).1
  have hcov := stepOne_cohL _ hso ho h.core.cov0
  have hpre := h.preC.mono (stepOne_getCoh_mono _ _ hso ho _)
  have hmi : M.Mi w o.thread.st c' := hst ▸ hX
  rcases hc with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
  · exact post_rtw0H hC hC0 hPT0 hKR hown hwf h hmp hfit hGV (.inr ⟨q, hq, hg, hm, hp⟩) hb hcov
      (fun hn => hC0.noProm0 w _ _ _ hn hco) hpre hr hmi
  · exact post_rtw0H hC hC0 hPT0 hKR hown hwf h hmp hfit hGV (.inl ⟨hm, hp⟩) hb hcov
      (fun hn => hC0.noProm0 w _ _ _ hn hco) hpre hr hmi

/-- **main's runtime-RMW row keeps `Post`**: the value read is a `G` value
(the memory's invariant; main owns no word); no write keeps memory and
promises (`post_instrKeep0H`), a write is out of label (`post_rtw0H`). -/
theorem post_rtRmw0H {k : Kraken.RmwKind} {L : Loc} {op : Val → Option Val} {g : Val → isaLSE2.State}
    {c' : Ctl} (hx : t.2.exited = none) (he : isaLSE2.exec t0.st = some (.rmw k false L op fun v => .done (g v)))
    (hmp : (M.ms w).mp L true) (hr : LocalRun M.p (Ctl.of s0) c')
    (hX : ∀ old, (M.ms w).G L old → (∀ u, (L, u) ∈ (M.ms w).own t0.st → old = u) →
      (∀ new, op old = some new → (M.ms w).G L new) ∧ M.Mi w (g old) c') :
    ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  have hwide := hC0.wide0 w _ _ (h.mi0 hPT0 hKR hx)
  have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
  have hfit : ∀ old v, op old = some v → v.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
  rw [hC0.G0 w] at hX
  simp only [hC0.own0 w, List.not_mem_nil, false_implies, implies_true, true_implies] at hX
  obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
  obtain ⟨old, tr, hst, hrd, hcase⟩ := stepOne_rmw_casesR Arch.armv8 he hso ho h.prom_le0
  obtain ⟨hGn, hXo⟩ := hX old (h.core.memInv.read? hrd)
  have hmi : M.Mi w o.thread.st c' := hst ▸ hXo
  rcases hcase with ⟨-, hm, hp⟩ | ⟨new, hop, hc⟩
  · exact post_instrKeep0H hC hC0 hPT0 hKR hown h hso ho hco hm hp hr hmi
  · have hb := (stepOne_bnd _ hso ho h.core.bnd0).1
    have hcov := stepOne_cohL _ hso ho h.core.cov0
    have hpre := h.preC.mono (stepOne_getCoh_mono _ _ hso ho _)
    exact post_rtw0H hC hC0 hPT0 hKR hown hwf h hmp (hfit old new hop) (hGn new hop) hc.symm hb hcov
      (fun hn => hC0.noProm0 w _ _ _ hn hco) hpre hr hmi

end Rows

/-- info: 'Spike.Lib.HelloM0.post_rtRmw0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_rtRmw0H

end

section

variable {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch} {w : Q.ι}

/-! ## The promise row -/

variable {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **A certified promise of main is `Good0`**: from `CInv0` at the
promising configuration, `cstep0` gives `StepG` (`certOkC_prom_good_cfg`). -/
theorem prom_good0H (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hmi : M.Mi w t0.st (Ctl.of s0)) {m : Msg}
    (hc : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 (Live.Sem.promThread t0 t.1.mem m)
      (t.1.mem.append m).1) :
    Good0 Q Λ w m := by
  have hq : CInv0 Q M w (Live.Sem.promThread t0 t.1.mem m, (t.1.mem.append m).1) :=
    { mi := ⟨Ctl.of s0, hmi, h.mCtl hPT0⟩
      msgs := msgsExcept_promise (Scc.Sem.MemInv.msgsExcept h.core.memInv _) m
      init := fun l => by
        show Q.G w l ((t.1.mem.append m).1.initVal l)
        rw [(Memory.Prefix.append _ _).initVal]; exact h.core.memInv.1 l
      le := fun p hp => by
        show p ≤ (t.1.mem.append m).1.last
        rw [Memory.last_append]
        rcases List.mem_append.mp hp with hp | hp
        · exact Nat.le_succ_of_le (h.prom_le0 p hp)
        · rw [List.mem_singleton.mp hp]; exact Nat.le_refl _ }
  have hG : StepG Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 (CInv0 Q M w) (Good0 Q Λ w) :=
    fun x y hx' hs _ => cstep0 hC0 hx' hs
  exact certOkC_prom_good_cfg hG hq hc (p := t.1.mem.last + 1) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    (Scc.Sem.Memory.get?_append_new)

/-- **main's certified promise keeps `Post`**: the promised message is
`Good0` (`prom_good0H`), out of every placed label, so off `cT`; the source
stutters (`post_local0H`). -/
theorem post_prom0H (hC : MainCompatH Q D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) (hown : Q.own = WakeOwn.wakeOwn) (hwf : Λ.WF)
    (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hx : t.2.exited = none) {m : Msg} (hwt : m.tid = 0)
    (hc : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 (Live.Sem.promThread t0 t.1.mem m)
      (t.1.mem.append m).1) :
    ∃ s', (srcS M.p arch).Run s [] s' ∧
      Q.Post Λ (t.1.withThread 0 (Live.Sem.promThread t0 t.1.mem m) (t.1.mem.append m).1, t.2) s' := by
  have hmi := h.mi0 hPT0 hKR hx
  obtain ⟨hf, hin, hG, hb8, hfit, hout⟩ := prom_good0H hC0 hPT0 h hmi hc
  have hpl := h.prom_le0
  have hlast : (t.1.mem.append m).1.last = t.1.mem.last + 1 := Memory.last_append _ _
  have hnew : (t.1.mem.append m).2 = t.1.mem.last + 1 := rfl
  have hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT := by
    obtain ⟨a', hcT, hx, ho⟩ := hC.cT w
    rw [hcT]; exact inLabel_wordLoc h.core.mem hwf hx ho
  have hne : m.loc ≠ (Q.C w).cT := fun e => hout (e ▸ hcTin)
  have hb : (Live.Sem.promThread t0 t.1.mem m).Bnd (t.1.mem.append m).1.last := by
    have hle : t.1.mem.last ≤ (t.1.mem.append m).1.last := by rw [hlast]; exact Nat.le_succ _
    exact ⟨h.core.bnd0.views.mono hle, h.core.bnd0.regs.mono hle⟩
  have hcov : CohCoversL (Live.Sem.promThread t0 t.1.mem m).views (Live.Sem.promThread t0 t.1.mem m).prom
      (t.1.mem.append m).1 ((Q.P w).cov 0) := Inv2Rely.CohCoversL.promise h.core.cov0 m
  have hpr : ∀ k ∈ (Live.Sem.promThread t0 t.1.mem m).prom, (Q.SR w).T < k ∧
      ∃ w', (t.1.mem.append m).1.get? k = some w' ∧ w'.tid = 0 := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨hTk, w', hg', ht'⟩ := h.core.prom0 k hk
      exact ⟨hTk, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg', ht'⟩
    · rw [List.mem_singleton.mp hk]
      exact ⟨Nat.lt_succ_of_le h.core.T_le, m, Scc.Sem.Memory.get?_append_new, hwt⟩
  have hnp : (Q.P w).noProm (Live.Sem.promThread t0 t.1.mem m).st → (Live.Sem.promThread t0 t.1.mem m).prom = [] :=
    fun hn => hC0.noProm0 w _ _ _ hn hc
  have hcore := core0_append h.core
    (own' := fun i => if i = 0 then Q.own w 0 (Live.Sem.promThread t0 t.1.mem m).st s0.stack
      else Q.own w 1 t1.st s1.stack)
    (w := m) (t0' := Live.Sem.promThread t0 t.1.mem m) (sm' := s.mem) (s0' := s0) (ts' := ts) (tp' := tp)
    (sp' := sp) (by simp) hwt hf (.inl rfl) (h.core.mem.runtime_write hout)
    (fun k hk => by
      rcases h.core.tp_prom k hk with h0 | h1
      · exact .inl (List.mem_append_left _ h0)
      · exact .inr h1)
    (fun k w' hk hg' hin' => by
      rcases hk with hk0 | hk1
      · rcases List.mem_append.mp hk0 with hk0 | hk0
        · rw [Scc.Sem.Memory.get?_append_le (hpl k hk0)] at hg'
          exact h.core.prom_tp k w' (.inl hk0) hg' hin'
        · rw [List.mem_singleton.mp hk0, hnew, Scc.Sem.Memory.get?_append_new] at hg'
          cases hg'
          exact absurd hin' hout
      · obtain ⟨-, w1, hg1, -⟩ := h.core.prom1 k hk1
        rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg1)] at hg'
        exact h.core.prom_tp k w' (.inr hk1) hg' hin')
    h.core.sp_prom hb8 hin hfit hG hb hcov h.core.frzS h.core.scov0 h.core.scov1
    (fun L v h0 => by simp [hown, WakeOwn.wakeOwn] at h0) (fun L v v' h0 => by simp [hown, WakeOwn.wakeOwn] at h0)
    (fun L v h0 => by simp [hown, WakeOwn.wakeOwn] at h0) hpr hnp
  exact post_local0H hC hC0 hPT0 hKR h hcore (cProt_append0 h.prot hne) (h.preC.append h.core.T_le m)
    (LocalRun.refl _) hmi

/-- info: 'Spike.Lib.HelloM0.post_prom0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_prom0H

end

section

/-! ## The flag load -/

variable {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **main's flag load keeps `Post`**: at `wlBody`, a load of `⟨A, 8⟩` with
`A` the word `c`'s pointer represents (the row's data: `Out.load`,
`OutL.ldSt`). A pre-spawn `0` stutters; the worker's `1` is matched by the
source's load of `kc`. -/
theorem post_flag0H (hC : MainCompatH Q D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) (hown : Q.own = WakeOwn.wakeOwn)
    (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 t0 0 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 o.thread o.mem)
    (hx : t.2.exited = none) (ht : s0.term = wlBody) {kl : Kraken.LoadKind} {A : BitVec 64} {g : Val → isaLSE2.State}
    (he : isaLSE2.exec t0.st = some (.load kl false ⟨A, 8⟩ fun v => .done (g v)))
    {ty : Ty} {wd : TermRun.Word} (hev : TermRun.evalAt s0.env (.var "c") = some (ty, [wd]))
    (hv : ValRep (M.lbl w) wd.val A.toNat) :
    ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  have hpt0 := h.pt0M hPT0
  have hmi : M.Mi w t0.st (Ctl.of s0) := h.mi0 hPT0 hKR hx
  have hctl := h.mCtl hPT0
  -- the address is the flag's `cT`
  obtain ⟨cty, cμ, cu, hcv, hcell, hcu⟩ := hpt0.2.2.2.2.1
  have hwd : wd = M.cw w := by
    rw [hcv] at hev; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hev
    exact hev.2.symm
  have hty : ty = cty := by
    rw [hcv] at hev; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hev
    exact hev.1.symm
  subst hwd hty
  obtain ⟨a', hcT, hcTa, hcTo⟩ := hC.cT w
  have hv' := hv
  rw [hC0.cw0 w, hC0.lbl0 w] at hv'
  obtain ⟨-, x0, hx0, hA⟩ := hv'
  rw [hcTa] at hx0; cases hx0
  have hA' : A = BitVec.ofNat 64 a' := by
    apply BitVec.eq_of_toNat_eq
    have := A.isLt
    simp only [BitVec.toNat_ofNat]
    omega
  have hloc : (⟨A, 8⟩ : Loc) = (Q.C w).cT := by rw [hcT, hA']; rfl
  have heC : isaLSE2.exec t0.st = some (.load kl false (Q.C w).cT fun v => .done (g v)) := by
    rw [← hloc]; exact he
  obtain ⟨hm, hpre, v, hst, h01⟩ := stepOne_load_c Arch.armv8 h.prot h.preC heC hso ho
  obtain ⟨-, hp⟩ := stepOne_load_keep' 0 he hso ho
  obtain ⟨hne, heq⟩ := hC0.flagLd w t0.st (Ctl.of s0) kl A g ty (M.cw w) hmi ht he hev hv
  rcases h01 with rfl | ⟨Tc, kc, hoc, rfl⟩
  · -- `0`: the source stutters
    exact post_instrKeep0H hC hC0 hPT0 hKR hown h hso ho hco hm hp (.refl _)
      (hst ▸ hne 0 (by decide))
  · -- `1`: the source loads `kc`
    subst hoc
    obtain ⟨-, -, -, -, m, hmk, -, hmv⟩ := h.prot.some_msg Tc kc rfl
    have hi := h.s0_get
    obtain ⟨th', hstep, ht', he', hp', hσ', hk', htl', hcoh⟩ :=
      src_load_latest0 (TermRun.gOf M.p (srcPo 2 arch M.p).k (srcPo 2 arch M.p).arch s 0) s.mem s.pairs s0
        (ht.trans rfl) hcv (hC0.cw0 w) hcell hcu (slatest_kc h.prot) hmk
    let w' : TermRun.Word := ⟨m.val, m.view, kc⟩
    have hmi' : M.Mi w o.thread.st (Ctl.of th') := by
      have : Ctl.of th' = ⟨wlIf, ("d", loadTy ty, [w']) :: s0.env, none⟩ := by
        simp only [Ctl.of, ht', he']; rfl
      rw [this, hst]
      exact heq 1 w' (by decide) (hC0.rd1 w w' hmv) (by rw [show w'.val = .num 1 from hmv]; exact ⟨by decide, rfl⟩)
    have hs' : ({ s with ths := s.ths.set! 0 th' } : TermRun.Cfg).ths = #[th', s1] := by
      show s.ths.set! 0 th' = _
      rw [h.ths]; rfl
    have hi' : ({ s with ths := s.ths.set! 0 th' } : TermRun.Cfg).ths[0]? = some th' := getElem?_set!_self hi th'
    have hlive : th'.term ≠ wlRet := by rw [ht']; simp [wlIf, WakeMLive.wlRet]
    have hex : SrcSem.mainExit s = [] :=
      mainExit_of_notRet h.ths hpt0.2.2.2.1 (by rw [ht]; simp [wlBody, WakeMLive.wlRet])
    have hex' : SrcSem.mainExit { s with ths := s.ths.set! 0 th' } = [] :=
      mainExit_of_notRet hs' (by rw [ht']; exact .inr (.inr (.inl rfl))) hlive
    have hrun : (srcS M.p arch).Run s [] { s with ths := s.ths.set! 0 th' } :=
      LRun.step (step := fun c es c' => ∃ i, (srcS M.p arch).step i c es c') ⟨0, WakeM0Src.source_step_nil' (P := srcPo 2 arch M.p) rfl
        (.inl (.inl ⟨SrcMem.mem_threadSteps hi hstep, certified_nil hi' (by rw [hp']; exact hpt0.2.2.2.2.2.1)⟩))
        hex hex' rfl⟩ (LRun.refl _)
    have hb := (stepOne_bnd _ hso ho h.core.bnd0).1
    have hcov := stepOne_cohL _ hso ho h.core.cov0
    rw [hm] at hb hcov
    refine ⟨_, hrun, ?_⟩
    rw [hm]
    refine post_frame0H (s := s) hC hPT0 hKR h.th hs' h.s1_get rfl rfl h.pt1 h.prot h.kr ?_ hpre ?_ hlive
    · refine core0_same h.core (by simp) hp hp' hb hcov
        (fun k m' hk hf => Nat.le_trans (h.core.scov0 k m' hk hf) (hcoh _)) ?_ ?_ ?_
        (fun hn => hC0.noProm0 w _ _ _ hn hco)
      · intro L v h0; simp [hown, WakeOwn.wakeOwn] at h0
      · intro L v v' h0; simp [hown, WakeOwn.wakeOwn] at h0
      · intro L v h0; simp [hown, WakeOwn.wakeOwn] at h0
    · refine ⟨.inl hmi', by rw [hk']; exact hpt0.2.1, by rw [hσ']; exact hpt0.2.2.1,
        by rw [ht']; exact .inr (.inr (.inl rfl)), ?_, by rw [hp']; exact hpt0.2.2.2.2.2.1,
        by rw [htl']; exact hpt0.2.2.2.2.2.2⟩
      rw [he']
      exact envC_cons hpt0.2.2.2.2.1 (by decide) _ _

/-- info: 'Spike.Lib.HelloM0.post_flag0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_flag0H

end

section

variable {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

/-- **`post_step0`**: a step of main keeps `Post`, matched by a source run
with its observable events (main's exit at its `exit_group`, none
otherwise). -/
theorem post_step0H_of (hC : MainCompatH Q D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) (hown : Q.own = WakeOwn.wakeOwn) (hwf : Λ.WF) {t t' : Cfg}
    {s : TermRun.Cfg} {es : List Ev} (hpost : Q.Post Λ t s) (hs : (machine (kernel 2)).Step μ 0 t es t') :
    ∃ s', (srcS M.p arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := post_partsM hC.pt1 hpost
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
      | silent s' c' he hr hX => exact post_silent0H hC hC0 hPT0 hKR hown h hso ho hco he hr hX
      | choice P tree he hsil hX => exact post_choice0H hC hC0 hPT0 hKR hown h hso ho hco he hsil hX
      | load kl A g x' a e ty w' he ht hev hv =>
        obtain ⟨hb, -, -, rfl, -⟩ := mterm_load hctl.term ht
        exact post_flag0H hC hC0 hPT0 hKR hown h hso ho hco hx hb he hev hv
      | store kr A V s' x' a b e ty tb wa wb he ht => exact (mterm_not_store hctl.term ht).elim
      | rtStore kr L V s' c' he hrt hmp hG hr hX =>
        exact post_rtStore0H hC hC0 hPT0 hKR hown hwf h hso ho hco hx he hmp hG hr hX
      | rtLoad kl L g c' he hrt hmp hr hX => exact post_rtLoad0H hC hC0 hPT0 hKR hown h hso ho hco he hr hX
      | rtRmw k' L op g c' he hrt hmp hr hX =>
        exact post_rtRmw0H hC hC0 hPT0 hKR hown hwf h hso ho hco hx he hmp hr hX
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
        | loc hr => exact post_fnc0H hC hC0 hPT0 hKR hown h hso ho hco he hr hX
        | pub _ hps _ =>
          -- main's terms publish nothing
          obtain ⟨-, -, x', a, e, t, t', ws, hpt, -⟩ := hps
          rcases hpt with ⟨ht, -⟩ | ⟨r, ht, -⟩ <;>
            rcases mterm_let hctl.term ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
    | ldSt kl A g x' a e ty w' V he ht hev hv =>
      obtain ⟨hb, -, -, rfl, -⟩ := mterm_load hctl.term ht
      exact post_flag0H hC hC0 hPT0 hKR hown h hso ho hco hx hb he hev hv
  · -- a certified promise
    exact post_prom0H hC hC0 hPT0 hKR hown hwf h hx hwt hc
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
          exact post_exit0H hC hC0 hPT0 hKR h hmi hat hd hoff
        · -- an abort: the process ends, the source stutters
          exact ⟨s, .refl _, post_exited0H hKR hpost _⟩
    · obtain ⟨rfl, s', hr, hp⟩ := post_sys0H hC hC0 hPT0 hKR hown h hmi hat hd
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

/-- info: 'Spike.Lib.HelloM0.post_step0H_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_step0H_of

end

/-! ## At `HelloCompat` -/

section Hello

open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloW1Store (relW wsideW NoWrite)
open Spike.Lib.HelloAssembly (HelloCompat)

variable {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch} {AbW : isaLSE2.State → Prop}
  {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D}

/-- **`MainCompatH` from `HelloCompat`**: `WCompatH.pt1`, and wake's
`WCompat.cT` at `relW` (whose `C` and `SR` are `Q`'s). -/
theorem mainCompatH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) : MainCompatH Q D :=
  ⟨hC.1.pt1, hC.2.1.cT⟩

/-- **`post_step0`** (`HelloAssembly.HelloRows.post_step0`): a step of main
keeps `Post`, matched by a source run with its observable events. -/
theorem post_step0H (hPT0 : Q.PT0 = PT0 M) (hKR : Q.KR = KRHE D r0 r1) (hown : Q.own = WakeOwn.wakeOwn)
    (hwf : Λ.WF) (hp : M.p = helloSrc) :
    HelloCompat Q D M μ Λ arch AbW hcw hem →
      ∀ t es t' s, Q.Post Λ t s → (machine (kernel 2)).Step μ 0 t es t' →
        ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  intro hC t es t' s hpost hs
  rw [← hp]
  exact post_step0H_of (mainCompatH hC) hC.2.2.2 hPT0 hKR hown hwf hpost hs

end Hello

/-- info: 'Spike.Lib.HelloM0.post_step0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_step0H

end Spike.Lib.HelloM0
