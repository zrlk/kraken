/-
**The worker's unpark** (data in
`Spike/Lib/WakeW1.lean`, `Spike/Lib/WakeW1Compat.lean`).

At `atUnpk` the source worker is at `let w = unpark j in ret `, past its
store, with no promise (`Parts.past_noProm`). Its target `swpal(1)` on
main's permit word (`OutT.unpk`) is an out-of-label write of `1` (`mpW`),
appended or fulfilling a promise, and the source takes its `unpark` of
main (`TermRun.thrOfTid` by main's thread label, `WCompat.tid0`): main's source
permit is set, the worker moves to `ret `, memory is kept
(`unpark_src_i`, `wake_unpark_get`). Main's side is kept by the frame facts
with the permit (`WCompatX.pt0p`, `WCompatX.krp`). Every other step at
`atUnpk` is a row `post_step1_of` already handles (the local rows stutter:
no local step from `wkUnpark`).

- `post_frame0`: `post_frame` with main's source permit set.
- `post_unpk`: the `unpk` row keeps `Post`, the source taking its unpark.
- `unpark_src_of`: the obligation `unpark_src`.
-/
import Spike.Lib.WakeW1Post

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc Spike.Lib.WorkerSrcStep
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt

variable {Q : WakeRel} {D : WSide Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

/-- **`Post` after a worker step setting main's source permit**
(`post_frame` with `s0` replaced by `{ s0 with permit := p }`; main's side
by `WCompatX.pt0p` and `WCompatX.krp`, the core and the protocol read no
permit). -/
theorem post_frame0 (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D) {w : Q.ι} {t : Cfg} {s s' : TermRun.Cfg}
    {t0 t1 t1' : Thread isaLSE2} {s0 s1' : TermRun.TTh} {mem' : Memory} {ts' : Nat → Option Nat}
    {tp' sp' : List Nat} {s1 : TermRun.TTh} (p : Option Nat) (hth : t.1.threads = #[t0, t1])
    (hs : s.ths = #[s0, s1]) (hs' : s'.ths = #[{ s0 with permit := p }, s1'])
    (hpre : PreC (Q.SR w) (Q.C w).cT t.1.mem t0.views) (hpt0 : Q.PT0 w t.1.mem s.mem t0 s0)
    (hkr : Q.KR w t s) (hT : (Q.SR w).T ≤ t.1.mem.last)
    (hm : W1Mem (Q.P w) (Q.C w).cS t.1.mem s.mem mem' s'.mem)
    (hcore : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st s1'.stack)
      mem' t0 t1' s'.mem s0 s1' ts' tp' sp')
    (hpt1 : PT1 D w mem' s'.mem t1' s1')
    (hprot : HelloProt (Q.SR w) (Q.C w) (Q.pT w) mem' t0 t1' s'.mem s0 s1' ts' tp' sp')
    (htr : s'.trace = s.trace) :
    Q.Post Λ (t.1.withThread 1 t1' mem', t.2) s' := by
  have hth' := withThread1 (t1' := t1') (mem := mem') hth
  refine ⟨w, ⟨t0, t1', { s0 with permit := p }, s1', ts', tp', sp', hth', hs', { hcore with }, ?_, ?_, hprot⟩, ?_⟩
  · simp only [WakeRel.PTw]
    exact ⟨preC_w1 hpre hT hm, hx.pt0p w _ _ t0 s0 _ _ p hpt0 hm⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hC.pt1]
    exact hpt1
  · refine hx.krp w t _ s s' s0 p hkr rfl ?_ (by rw [hs]; rfl) (by rw [hs']; rfl) htr
    show (t.1.withThread 1 t1' mem').threads[0]? = t.1.threads[0]?
    rw [hth', hth]; rfl

variable {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **The `unpk` row keeps `Post`**: the worker's RMW writing `1` to main's
permit word, out of every label (appended, or fulfilling a promise), is
matched by the source worker's `unpark` of main. -/
theorem post_unpk (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D) (hwf : Λ.WF)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hex : SrcSem.mainExit s = [])
    (hns : abi.atSys t1.st = false) {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 o.thread o.mem)
    {k : Kraken.RmwKind} {A : BitVec 64} {op : Val → Option Val} {g : Val → isaLSE2.State} {x : String}
    {a : At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (he : isaLSE2.exec t1.st = some (.rmw k false ⟨A, 8⟩ op fun v => .done (g v)))
    (hmp : (D.ms w).mp ⟨A, 8⟩ true) (hop : ∀ old, op old = some 1)
    (ht : (Ctl.of s1).term = .let_ x (.ext .unpark a) e)
    (hev : TermRun.evalAt (Ctl.of s1).env a = some (ty, [jw]))
    (hX : ∀ old, (D.ms w).G ⟨A, 8⟩ old → (∀ u, (⟨A, 8⟩, u) ∈ (D.ms w).own t1.st → old = u) →
      (D.ms w).G ⟨A, 8⟩ 1 ∧ D.Wi w (g old) ⟨e, (x, ExtName.unpark.sig.2, []) :: (Ctl.of s1).env, none⟩) :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  have hctl := h.wCtl
  have hcw := hC.cwv w
  have hstk : s1.stack = [] := h.pt1.2.1
  -- the source worker at its unpark, past its store, with no promise
  have hst : s1.term = wkUnpark := by
    rcases wterm_let hctl.term ht with h' | h'
    · rw [h'] at ht; simp [wkStore] at ht
    · exact h'
  have hnps : ¬ PreSplit s1.term := by
    rw [hst]; rintro (hp | hp) <;> simp [wkUnpark, wkTail, wkBody] at hp
  have hcj := hctl.cj hnps
  change s1.term = _ at ht
  rw [hst] at ht
  simp only [wkUnpark, Expr.let_.injEq] at ht
  obtain ⟨rfl, hop', rfl⟩ := ht
  simp only [Op.ext.injEq, true_and] at hop'
  subst hop'
  obtain ⟨rt, jw', hj, hjw⟩ := hcj.2
  change TermRun.evalAt s1.env _ = _ at hev
  change TermRun.evalAt s1.env _ = _ at hj
  rw [hj] at hev
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hev
  obtain ⟨-, rfl⟩ := hev
  have hs1p : s1.promises = [] := h.past_noProm hC (.inl hst)
  have hs0g : s.ths[0]? = some s0 := by rw [h.ths]; rfl
  have htid := hC.tid0 w _ _ _ _ h.pt0
  have hw : TermRun.thrOfTid s jw' = some 0 := by
    unfold TermRun.thrOfTid
    rw [hjw]
    simp [mainTidW, h.ths, htid]
  -- the source unpark
  let s1x : TermRun.TTh := { s1 with term := .ret .unit, env := ("w", ExtName.unpark.sig.2, []) :: s1.env }
  let pm : Option Nat := some (max (s0.permit.getD 0) (TermRun.relView s1.vs))
  have hc : TermRun.Certified wakeSrc (srcPo 2 arch wakeSrc).k (srcPo 2 arch wakeSrc).arch
      (TermRun.extCfg s 1 s1 "w" .unpark (.ret .unit) [jw'] []) 1 :=
    certified_nil (TermExtStep.extCfg_ths_self h.s1_get "w" .unpark (.ret .unit) [jw'] [] (by decide)) (by simpa using hs1p)
  have hstep := unpark_src_i (P := srcPo 2 arch wakeSrc) (p := wakeSrc) rfl (by decide) h.s1_get hst hj hc hex
  have hrun : (wakeS arch).Run s [] (TermRun.wake (TermRun.extCfg s 1 s1 "w" .unpark (.ret .unit) [jw'] []) 1 (TermRun.relView s1.vs)
      .unpark [jw']) :=
    LRun.step (step := fun c es c' => ∃ i, (wakeS arch).step i c es c') ⟨1, hstep⟩ (LRun.refl _)
  have hsm : (TermRun.wake (TermRun.extCfg s 1 s1 "w" .unpark (.ret .unit) [jw'] []) 1 (TermRun.relView s1.vs) .unpark [jw']).mem =
      s.mem := by rw [TermExtStep.wake_mem]; simp [TermRun.extCfg]
  have hE : (TermRun.extCfg s 1 s1 "w" .unpark (.ret .unit) [jw'] []).ths = #[s0, s1x] := by
    show s.ths.set! 1 _ = _; rw [h.ths]; rfl
  have hw' : TermRun.thrOfTid (TermRun.extCfg s 1 s1 "w" .unpark (.ret .unit) [jw'] []) jw' = some 0 := by
    rw [thrOfTid_extCfg h.s1_get "w" (by decide) _ [jw'] [] jw', hw]
  have hs' : (TermRun.wake (TermRun.extCfg s 1 s1 "w" .unpark (.ret .unit) [jw'] []) 1 (TermRun.relView s1.vs) .unpark [jw']).ths =
      #[{ s0 with permit := pm }, s1x] := by
    simp only [TermRun.wake, hw']
    unfold TermRun.setPermit
    rw [hE]
    rfl
  -- the target RMW: an out-of-label write of `1`
  have hL : (⟨A, 8⟩ : Loc) = wordLoc A.toNat := ExtRows.loc_wordLoc rfl
  rw [hL] at he hmp hX
  obtain ⟨hf, hout, hin⟩ := hC.mpW w _ hmp
  obtain ⟨old, tr, hst', hrd, hc'⟩ := stepOne_rmw_casesR Arch.armv8 he hso ho h.prom_le
  have hGo := h.core.memInv.read? hrd
  rw [← hC.G w] at hGo
  obtain ⟨hG1, hXo⟩ := hX old hGo (fun u hu => by simp [hC.own w, hx.own1] at hu)
  rw [hC.G w] at hG1
  have hwi : D.Wi w o.thread.st (Ctl.of s1x) := hst' ▸ hXo
  have hpT1 : (Q.C w).passT t1.st := (hC.pass w _ _ h.pt1.1).mpr (.inl hst)
  have hpT' : (Q.C w).passT o.thread.st := (hC.pass w _ _ hwi).mpr (.inr rfl)
  have hT0 := ((cProt_iff _ _ _).mp h.prot).1
  have hS := ((cProt_iff _ _ _).mp h.prot).2.1
  have hpassS : (Q.C w).passS s1x := (Parts.passS_iff (w := w) hC s1x).mpr ⟨hstk, .inr rfl⟩
  have hb := (stepOne_bnd _ hso ho h.core.bnd1).1
  have hcov := stepOne_cohL _ hso ho h.core.cov1
  have hown := h.own_step hC hns hso ho
  have hnp : (Q.P w).noProm o.thread.st → o.thread.prom = [] := fun hn => hC.noProm w _ _ _ hn hco
  have hown' : ExtRows.OwnOk
      ((fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 o.thread.st s1.stack) 1) o.mem
      o.thread.prom := by
    simp only [Nat.one_ne_zero, ite_false]; rw [hstk]; exact hown
  have hdisj : ∀ L v v', (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st s1.stack) 0 →
      (L, v') ∈ (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 o.thread.st s1.stack) 1 →
      False := fun L v v' _ h1 => by simp [hstk, hx.own1] at h1
  have hocov : ∀ L v, (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 o.thread.st s1.stack) 1 →
      (Q.P w).cov 1 L := fun L v h1 => by simp [hstk, hx.own1] at h1
  -- the assembly, for either outcome
  have hfin : ∀ (tp' : List Nat),
      (o.mem = t.1.mem ∨ ∃ m : Msg, o.mem = (t.1.mem.append m).1 ∧ m.tid = 1 ∧ (Q.P w).foot 1 m.loc) →
      Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
        (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 o.thread.st s1.stack) o.mem t0 o.thread
        s.mem s0 s1 ts tp' sp →
      CProtT (Q.SR w) (Q.C w) oc o.mem t1 ts tp' →
      (∀ Tc kc, oc = some (Tc, kc) → Tc ∈ tp' → Tc ∈ o.thread.prom) → (∀ k ∈ tp', k ∈ tp) →
      o.thread.prom.Nodup →
      ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
    intro tp' hm hcore hT hpw htp hnd
    refine ⟨_, hrun, post_frame0 (ts' := ts) (tp' := tp') (sp' := sp) hC hx pm h.th h.ths hs' h.preC h.pt0 h.kr
      h.core.T_le ?_ ?_ ?_ ?_ (by rw [TermExtStep.wake_trace]; simp [TermRun.extCfg, CoreTerm.ExtName.events])⟩
    · rw [hsm]; exact ⟨hm, .inl rfl⟩
    · rw [hsm]; exact { hcore with }
    · rw [hsm]
      refine ⟨hwi, hstk, h.pt1.2.2.1, .inr (.inr (.inr (.inr rfl))), fun hp => ?_, fun _ => ?_,
        by simp [s1x, hs1p], fun k hk => by simp [s1x, hs1p] at hk, hnd⟩
      · exfalso; rcases hp with hp | hp <;> simp [wkTail, wkBody] at hp
      · have hcj' : EnvCJ (D.cw w) s1.env := hcj
        simpa [s1x, EnvCJ, TermRun.evalAt, TermRun.lookupE, List.find?_cons] using hcj'
    · rw [hsm]
      have hS0 : CProtS (Q.SR w) (Q.C w) oc s.mem s1 tp' sp :=
        ⟨hS.smsg, hS.some_msg, fun Tc kc hoc htp' => hS.prom_worker Tc kc hoc (htp _ htp'), hS.pre_lt,
          hS.prom_view⟩
      exact ⟨oc, (cProt_iff _ _ _).mpr ⟨⟨hT.tmsg, hT.some_msg, hpw, fun _ => hT.pass_done hpT1,
        fun hn => absurd hpT' hn⟩, cProtS_unpark hS0 hpassS rfl, ⟨fun _ => hpassS, fun _ => hpT'⟩⟩⟩
  rcases hc' with ⟨hop', -⟩ | ⟨new, hop', hc'⟩
  · rw [hop old] at hop'; cases hop'
  have hn1 : new = 1 := by rw [hop old] at hop'; exact (Option.some.inj hop').symm
  subst hn1
  rcases hc' with ⟨q, hq, hg, hm, hp⟩ | ⟨hm, hp⟩
  · -- the fulfilment
    have hq0 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) (h.core.prom1 q hq).1
    have hts : ∀ k, ts k ≠ some q := fun k hk =>
      hout (img_inLabel h.core.mem hwf h.core.narrow hk hq0 hg)
    have hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT := by
      obtain ⟨a', hcT, hx', ho'⟩ := hC.cT w
      rw [hcT]; exact inLabel_wordLoc h.core.mem hwf hx' ho'
    have hTcq : ∀ Tc kc, oc = some (Tc, kc) → Tc ≠ q := by
      rintro Tc kc hoc rfl
      obtain ⟨-, -, w', hg', hl, -⟩ := hT0.some_msg Tc kc hoc
      rw [hg] at hg'; cases hg'
      exact hout (by rw [show wordLoc A.toNat = (Q.C w).cT from hl]; exact hcTin)
    have hT' : CProtT (Q.SR w) (Q.C w) oc o.mem t1 ts (tp.erase q) :=
      { hT0 with
        tmsg := fun k w' hk hTk hl => hT0.tmsg k w' (hm ▸ hk) hTk hl
        some_msg := fun Tc kc hoc => by rw [hm]; exact hT0.some_msg Tc kc hoc
        prom_worker := fun Tc kc hoc htp => hT0.prom_worker Tc kc hoc (List.mem_of_mem_erase htp)
        pass_done := fun hps => by
          obtain ⟨Tc, kc, hoc, hn⟩ := hT0.pass_done hps
          exact ⟨Tc, kc, hoc, fun hm' => hn (List.mem_of_mem_erase hm')⟩
        pass_prom := fun hps Tc kc hoc =>
          (List.mem_erase_of_ne (hTcq Tc kc hoc)).mpr (hT0.pass_prom hps Tc kc hoc) }
    have hcore := Inv2Core.core1_fulfil h.core hg hout hts
      (own' := fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 o.thread.st s1.stack)
      (by simp) hp (hm ▸ hb) (hm ▸ hcov) (hm ▸ hown') hdisj hocov hnp
    rw [← hm] at hcore
    exact hfin (tp.erase q) (.inl hm) hcore hT'
      (fun Tc kc hoc htp => by
        rw [hp]
        exact (List.mem_erase_of_ne (hTcq Tc kc hoc)).mpr (hT0.prom_worker Tc kc hoc (List.mem_of_mem_erase htp)))
      (fun k hk => List.mem_of_mem_erase hk) (by rw [hp]; exact h.nodup.erase q)
  · -- the append
    have hpl := h.prom_le
    have hT' : CProtT (Q.SR w) (Q.C w) oc o.mem t1 ts tp := by
      rw [hm]
      exact
      { hT0 with
        tmsg := fun k w' hk hTk hl => by
          by_cases hk' : k = t.1.mem.last + 1
          · subst hk'
            rw [Scc.Sem.Memory.get?_append_new] at hk
            cases hk
            obtain ⟨a', hcT, hx', ho'⟩ := hC.cT w
            have hin' : InLabel (Q.SR w).lbl (Q.SR w).lsize (wordLoc A.toNat) := by
              rw [show wordLoc A.toNat = (Q.C w).cT from hl, hcT]
              exact inLabel_wordLoc h.core.mem hwf hx' ho'
            exact absurd hin' hout
          · exact hT0.tmsg k w' (CohCoversP.get?_append_ne hk hk') hTk hl
        some_msg := fun Tc kc hoc => by
          obtain ⟨h1, h2, w', hg', h3⟩ := hT0.some_msg Tc kc hoc
          exact ⟨h1, h2, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg',
            h3⟩ }
    have hcore := core1_append h.core
      (own' := fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 o.thread.st s1.stack)
      (w := ⟨wordLoc A.toNat, 1, 1⟩) (t1' := o.thread) (sm' := s.mem) (s1' := s1) (ts' := ts) (tp' := tp)
      (sp' := sp) (by simp) rfl hf (.inl rfl) (h.core.mem.runtime_write hout)
      (fun k hk => by rw [hp]; exact h.core.tp_prom k hk)
      (fun k w' hk hg' hin' => by
        have hk1 : k ∈ t0.prom ∨ k ∈ t1.prom := by rw [hp] at hk; exact hk
        have hle : k ≤ t.1.mem.last := by
          rcases hk1 with hk0 | hk1
          · obtain ⟨-, w0, hg0, -⟩ := h.core.prom0 k hk0
            exact Scc.Sem.Memory.le_last_of_get? hg0
          · exact hpl k hk1
        rw [Scc.Sem.Memory.get?_append_le hle] at hg'
        exact h.core.prom_tp k w' hk1 hg' hin')
      h.core.sp_prom rfl hin (show (1 : Val).toNat < 2 ^ 64 by decide) hG1 (hm ▸ hb) (hm ▸ hcov) h.core.frzS
      h.core.scov0 h.core.scov1 (hm ▸ hown') hdisj hocov
      (fun k hk => by
        rw [hp] at hk
        obtain ⟨hTk, w', hg', ht'⟩ := h.core.prom1 k hk
        exact ⟨hTk, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg', ht'⟩)
      hnp
    rw [← hm] at hcore
    exact hfin tp (.inr ⟨_, hm, rfl, hf⟩) hcore hT'
      (fun Tc kc hoc htp => by rw [hp]; exact hT0.prom_worker Tc kc hoc htp) (fun k hk => hk)
      (by rw [hp]; exact h.nodup)

/-- info: 'Spike.Lib.WakeW1.post_unpk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_unpk

/-- **`unpark_src`**: a step of the worker at its unpark keeps `Post`: the
`unpk` row by `post_unpk`, the other rows as in `post_step1_of`, matched by
a source run with no observable event. -/
theorem unpark_src_of (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D) (hwf : Λ.WF) {t t' : Cfg}
    {s : TermRun.Cfg} {es : List Ev} (hpost : Q.Post Λ t s) (hu : Q.atUnpk t s)
    (hs : (machine (kernel 2)).Step μ 1 t es t') :
    ∃ s', (wakeS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := post_parts hC hpost
  have hex : SrcSem.mainExit s = [] := hC.mainLive t s hpost hs.runs.2.1
  have hwi := h.pt1.1
  have hctl := h.wCtl
  have hst : s1.term = wkUnpark := by
    rw [hC.atUnpk] at hu
    obtain ⟨s1', h1, hterm⟩ := hu
    rw [h.s1_get] at h1
    cases h1
    exact hterm
  have hnr : ∀ a, s1.term ≠ .ret a := fun a h' => by rw [hst] at h'; simp [wkUnpark] at h'
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
          have h2 : (Ctl.of s1).term = wkUnpark := hst
          rw [h2] at ht; simp [wkUnpark] at ht
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
    | unpk k' A B op g x' a e ty jw he hrt hmp hop ht hh hev hv hA hX =>
      exact post_unpk hC hx hwf h hex hns hso ho hco he hmp hop ht hev hX
    | texit K a hK ha =>
      rw [hC.K w] at hK; cases hK; rw [hns] at ha; cases ha
    | fnc k' s' c' he hr hX => exact post_fnc hC h hex hns hso ho hco he hr hX
  · -- a certified promise
    exact post_prom1 hC hx hwf h hex hwt hc
  · -- a system call, by the `Out.sys` row
    obtain ⟨hat, call, hd⟩ := sysStep_ready h.t1_get hsy
    obtain ⟨hok, hX⟩ := sys_rows hC h (.inr hnr) hat hd
    obtain ⟨rfl, s', hr, hp⟩ := post_sys hC h hex hat hd hok hX hsy hca
    exact ⟨s', hr, hp⟩
  · -- no `clone`: the rows exclude it
    obtain ⟨hat, st, tl, hd⟩ := spawnStep_ready h.t1_get hsp
    exact absurd rfl ((sys_rows hC h (.inr hnr) hat hd).1.2.1 st tl)
  · -- no range transfer: no site at the worker's states
    obtain ⟨a, ha, t1', ht1, hpc⟩ := hsite
    obtain rfl : t1' = t1 := Option.some.inj (ht1.symm.trans h.t1_get)
    have hn := siteAt_eq_none_iff.mp (hC.noSite w _ _ hwi)
    cases k with
    | take => exact absurd (ha.trans (congrArg some hpc.symm)) hn.1
    | release => exact absurd (ha.trans (congrArg some hpc.symm)) hn.2

/-- info: 'Spike.Lib.WakeW1.unpark_src_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unpark_src_of

end Spike.Lib.WakeW1
