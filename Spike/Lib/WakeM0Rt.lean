/-
**main's runtime writes** (`post_step0`). The
thread-0 counterpart of `Spike/Lib/WakeW1Rt.lean`.

A runtime write of main (`Out.rtStore`, `Out.rtRmw`) is to a word outside
every placed label (`WCompat0.mpW0`), so not the flag's `cT`: the target
appends main's message or fulfils one of main's promises (an unmirrored
one), main's source takes a local run.

- `core0_fulfil`: a fulfilment of an out-of-label promise of thread 0 keeps
  the core (`WakeW1.Inv2Core.core1_fulfil`'s twin).
- `cProt_erase`: a target promise other than the flag's `Tc` leaving the
  mirrored ones keeps the protocol.
- `post_frame0`: `post_frame0'` with the protocol given at the new target
  memory and mirrored promises.
- `post_local0`: a step of main to `t0'` and `mem'`, the core, protocol and
  `PreC` at the new target state, matched by a local run of main's source
  into `Mi`, keeps `Post`.
- `post_rtw0`: an out-of-label write of main, appended or fulfilled, keeps
  `Post`.
- `post_rtStore0`, `post_rtRmw0`: main's runtime-write rows keep `Post`.
-/
import Spike.Lib.WakeM0Instr
import Spike.Lib.WakeW1Rt

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt Spike.Lib.WakeW1
open Spike.Lib.WakeMLive (wlRet)

/-- **A fulfilment of an out-of-label promise of thread 0** with no source
preimage keeps the core: memory unchanged, the promise leaves thread 0's
promises and the mirrored ones; thread 0's own facts at the new state. -/
theorem core0_fulfil {I : ISA} {Λ : Scc.Sem.Layout} {R : SpawnRec} {P : Inv2Params I}
    {G : Loc → Val → Prop} {own : Nat → List (Loc × Val)} {tm : Memory} {t0 t1 : Thread I}
    {sm : WeakMem.Memory} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {q : Nat} {wq : Msg} (hg : tm.get? q = some wq)
    (hout : ¬ InLabel R.lbl R.lsize wq.loc) (hts : ∀ k, ts k ≠ some q) {t0' : Thread I}
    {own' : Nat → List (Loc × Val)} (ho1 : own' 1 = own 1) (hp : t0'.prom = t0.prom.erase q)
    (hb : t0'.Bnd tm.last) (hc : CohCoversL t0'.views t0'.prom tm (P.cov 0))
    (hown : ExtRows.OwnOk (own' 0) tm t0'.prom) (hdisj : ∀ L v v', (L, v) ∈ own' 0 → (L, v') ∈ own 1 → False)
    (hocov : ∀ L v, (L, v) ∈ own' 0 → P.cov 0 L) (hnp : P.noProm t0'.st → t0'.prom = []) :
    Inv2Core Λ R P G own' tm t0' t1 sm s0 s1 ts (tp.erase q) sp :=
  { h with
    mem := memRelP_tp_erase h.mem hts
    tp_prom := fun k hk => by
      have hne : k ≠ q := (h.mem.tp_nodup.mem_erase_iff.mp hk).1
      rcases h.tp_prom k (List.mem_of_mem_erase hk) with h0 | h1
      · left; rw [hp]; exact (List.mem_erase_of_ne hne).mpr h0
      · exact .inr h1
    prom_tp := fun k w hk hg' hin => by
      have hk' : k ∈ t0.prom ∨ k ∈ t1.prom :=
        hk.imp_left fun h0 => by rw [hp] at h0; exact List.mem_of_mem_erase h0
      have hne : k ≠ q := by
        rintro rfl; rw [hg] at hg'; cases hg'; exact hout hin
      exact (List.mem_erase_of_ne hne).mpr (h.prom_tp k w hk' hg' hin)
    bnd0 := hb
    cov0 := hc
    own0 := hown
    own1 := by rw [ho1]; exact h.own1
    own_disj := by rw [ho1]; exact hdisj
    own_cov := fun i L v hi hm => by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact hocov L v hm
      · rw [ho1] at hm; exact h.own_cov 1 L v hi hm
    prom0 := fun k hk => h.prom0 k (by rw [hp] at hk; exact List.mem_of_mem_erase hk)
    noProm0 := hnp }

/-- **A target promise other than the flag's leaving the mirrored ones keeps
the protocol.** -/
theorem cProt_erase {I : ISA} {R : SpawnRec} {C : CRec I} {oc : Option (Nat × Nat)} {tm : Memory}
    {t1 : Thread I} {sm : WeakMem.Memory} {s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    (h : CProt R C oc tm t1 sm s1 ts tp sp) {q : Nat} (hq : ∀ Tc kc, oc = some (Tc, kc) → Tc ≠ q) :
    CProt R C oc tm t1 sm s1 ts (tp.erase q) sp :=
  { h with
    prom_worker := fun Tc kc hoc htp => h.prom_worker Tc kc hoc (List.mem_of_mem_erase htp)
    pass_done := fun hps => by
      obtain ⟨Tc, kc, hoc, hn⟩ := h.pass_done hps
      exact ⟨Tc, kc, hoc, fun hm => hn (List.mem_of_mem_erase hm)⟩
    pass_prom := fun hps Tc kc hoc => (List.mem_erase_of_ne (hq Tc kc hoc)).mpr (h.pass_prom hps Tc kc hoc) }

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **`Post` after a step of main**, the protocol given at the new target
memory and mirrored promises (`post_frame0'` with `hprot` and `hm` in one). -/
theorem post_frame0 (hC : WCompat Q D μ Λ arch) (hPT0 : Q.PT0 = PT0 M) (hKR : Q.KR = WakeKR.KR r0 r1)
    {s' : TermRun.Cfg} {t0' : Thread isaLSE2} {s0' : TermRun.TTh} {mem' : Memory} {tp' : List Nat}
    (hth : t.1.threads = #[t0, t1]) (hs' : s'.ths = #[s0', s1]) (hsm : s'.mem = s.mem)
    (hstr : s'.trace = s.trace)
    (hpt1 : PT1 D w t.1.mem s.mem t1 s1) (hprot : CProt (Q.SR w) (Q.C w) oc mem' t1 s.mem s1 ts tp' sp)
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
    obtain ⟨hn, h0, h1, hh, -, htr⟩ := hkr
    refine ⟨hn, h0, h1, hh, fun _ s0'' h => ?_, by simp only [SrcSem.traceOf, hstr] at htr ⊢; exact htr⟩
    rw [hs'] at h
    cases (show some s0' = some s0'' from h)
    exact hlive

/-- **A step of main matched by a local run of main's source keeps
`Post`**: thread 0 replaced by `t0'` and the memory by `mem'`, the core,
the protocol and `PreC` at the new target state (main's old source
thread), main's source after a local run from its control to `c'` with
`Mi w t0'.st c'`. -/
theorem post_local0 (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = WakeKR.KR r0 r1) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {t0' : Thread isaLSE2} {mem' : Memory} {tp' : List Nat} {c' : Ctl}
    (hcore : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
      (fun i => if i = 0 then Q.own w 0 t0'.st s0.stack else Q.own w 1 t1.st s1.stack) mem' t0' t1 s.mem s0 s1
      ts tp' sp)
    (hprot : CProt (Q.SR w) (Q.C w) oc mem' t1 s.mem s1 ts tp' sp)
    (hpre : PreC (Q.SR w) (Q.C w).cT mem' t0'.views)
    (hr : LocalRun wakeSrc (Ctl.of s0) c') (hmi : M.Mi w t0'.st c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 t0' mem', t.2) s' := by
  have hpt0 := h.pt0M hPT0
  have hctl' := localRun_mCtl hr (h.mCtl hPT0)
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
  have hrun : (wakeS arch).Run s [] { s with ths := s.ths.set! 0 s0' } :=
    WakeM0Src.localRunS_run_source_0 (P := srcPo 2 arch wakeSrc) rfl hr.toS h.s0_get rfl rfl hpt0.2.2.1
      hpt0.2.1 hpt0.2.2.2.2.2.1 hex'
  refine ⟨_, hrun, post_frame0 (s := s) hC hPT0 hKR h.th hs' rfl rfl h.pt1 hprot h.kr ?_ hpre ?_ hlive⟩
  · exact core0_same hcore (by simp) rfl rfl hcore.bnd0 hcore.cov0 hcore.scov0 hcore.own0 hcore.own_disj
      (fun L v hm => hcore.own_cov 0 L v (by decide) hm) hcore.noProm0
  · exact ⟨.inl (hc'eq ▸ hmi), hpt0.2.1, hpt0.2.2.1, hctl'.term, hctl'.env, hpt0.2.2.2.2.2.1, hpt0.2.2.2.2.2.2⟩

/-- main's promises are at most the memory's last timestamp. -/
theorem _root_.Spike.Lib.WakeW1.Parts.prom_le0 (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : ∀ p ∈ t0.prom, p ≤ t.1.mem.last := by
  intro p hp
  obtain ⟨-, m, hg, -⟩ := h.core.prom0 p hp
  exact Scc.Sem.Memory.le_last_of_get? hg

/-! ## An out-of-label write of main -/

/-- **An out-of-label write of main keeps `Post`**: the message
`⟨wordLoc a, V, 0⟩` (`a` mapped for writing, so in main's footprint and
outside every label; `V` a 64-bit `G` value) appended, or one of main's
promises of it fulfilled; the new thread's bound, cover, no-promise fact and
`PreC` at the new memory; main's source after a local run into `Mi`. -/
theorem post_rtw0 (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = WakeKR.KR r0 r1) (hown : Q.own = WakeOwn.wakeOwn) (hwf : Λ.WF)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {t0' : Thread isaLSE2} {mem' : Memory} {a : Nat} {V : Val} {c' : Ctl}
    (hmp : (M.ms w).mp (wordLoc a) true) (hfit : V.toNat < 2 ^ 64) (hG : Q.G w (wordLoc a) V)
    (hcase : (mem' = (t.1.mem.append ⟨wordLoc a, V, 0⟩).1 ∧ t0'.prom = t0.prom) ∨
      (∃ q ∈ t0.prom, t.1.mem.get? q = some ⟨wordLoc a, V, 0⟩ ∧ mem' = t.1.mem ∧ t0'.prom = t0.prom.erase q))
    (hb : t0'.Bnd mem'.last) (hcov : CohCoversL t0'.views t0'.prom mem' ((Q.P w).cov 0))
    (hnp : (Q.P w).noProm t0'.st → t0'.prom = [])
    (hpre : PreC (Q.SR w) (Q.C w).cT t.1.mem t0'.views)
    (hr : LocalRun wakeSrc (Ctl.of s0) c') (hmi : M.Mi w t0'.st c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 t0' mem', t.2) s' := by
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
    exact post_local0 hC hC0 hPT0 hKR h hcore (cProt_append0 h.prot hne) (hpre.append h.core.T_le _) hr hmi
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
    exact post_local0 hC hC0 hPT0 hKR h hcore (cProt_erase h.prot hTcq) hpre hr hmi

/-! ## The runtime-write rows -/

section Rows

variable (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
  (hKR : Q.KR = WakeKR.KR r0 r1) (hown : Q.own = WakeOwn.wakeOwn) (hwf : Λ.WF)
  (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
  {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
  (hso : stepOne Arch.armv8 t0 0 t.1.mem = some outs) (ho : .ok o ∈ outs)
  (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 o.thread o.mem)
include hC hC0 hPT0 hKR hown hwf h hso ho hco

/-- **main's runtime-store row keeps `Post`.** -/
theorem post_rtStore0 {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : isaLSE2.State} {c' : Ctl}
    (hx : t.2.exited = none)
    (he : isaLSE2.exec t0.st = some (.store kr false L V fun _ => .done s')) (hmp : (M.ms w).mp L true)
    (hGV : (M.ms w).G L V) (hr : LocalRun wakeSrc (Ctl.of s0) c') (hX : M.Mi w s' c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
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
  · exact post_rtw0 hC hC0 hPT0 hKR hown hwf h hmp hfit hGV (.inr ⟨q, hq, hg, hm, hp⟩) hb hcov
      (fun hn => hC0.noProm0 w _ _ _ hn hco) hpre hr hmi
  · exact post_rtw0 hC hC0 hPT0 hKR hown hwf h hmp hfit hGV (.inl ⟨hm, hp⟩) hb hcov
      (fun hn => hC0.noProm0 w _ _ _ hn hco) hpre hr hmi

/-- **main's runtime-RMW row keeps `Post`**: the value read is a `G` value
(the memory's invariant; main owns no word); no write keeps memory and
promises (`post_instrKeep0`), a write is out of label (`post_rtw0`). -/
theorem post_rtRmw0 {k : Kraken.RmwKind} {L : Loc} {op : Val → Option Val} {g : Val → isaLSE2.State}
    {c' : Ctl} (hx : t.2.exited = none) (he : isaLSE2.exec t0.st = some (.rmw k false L op fun v => .done (g v)))
    (hmp : (M.ms w).mp L true) (hr : LocalRun wakeSrc (Ctl.of s0) c')
    (hX : ∀ old, (M.ms w).G L old → (∀ u, (L, u) ∈ (M.ms w).own t0.st → old = u) →
      (∀ new, op old = some new → (M.ms w).G L new) ∧ M.Mi w (g old) c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
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
  · exact post_instrKeep0 hC hC0 hPT0 hKR hown h hso ho hco hm hp hr hmi
  · have hb := (stepOne_bnd _ hso ho h.core.bnd0).1
    have hcov := stepOne_cohL _ hso ho h.core.cov0
    have hpre := h.preC.mono (stepOne_getCoh_mono _ _ hso ho _)
    exact post_rtw0 hC hC0 hPT0 hKR hown hwf h hmp (hfit old new hop) (hGn new hop) hc.symm hb hcov
      (fun hn => hC0.noProm0 w _ _ _ hn hco) hpre hr hmi

end Rows

/-- info: 'Spike.Lib.WakeM0.post_rtRmw0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_rtRmw0

end Spike.Lib.WakeM0
