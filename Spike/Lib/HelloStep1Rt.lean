/-
**hello.w on AArch64: the worker's runtime writes after the spawn** (C4,
row B8-gen1, step 3b; the twin of `Spike/Lib/WakeW1Rt.lean` at `PartsH`,
the source side a frame run as in `Spike/Lib/HelloStep1P.lean`).

A runtime write of the worker (`Out.rtStore`, `Out.rtRmw` at the frames an
`OutTS.pre` run reaches) is to a word outside every placed label
(`WakeW1.WCompat.mpW` at `relW`, by `hms` at any frames): the target
appends its message or fulfils one of its (unmirrored) promises; the source
worker takes a frame run.

- `prom_leH`: the worker's promises are at most the memory's last
  timestamp (`WakeW1.Parts.prom_le`).
- `post_localH`: a worker step to `t1'` and `mem'` (kept, or one message of
  the worker in its footprint appended), the core and the target part of
  the protocol at the new memory, matched by a frame run of the source
  worker into `Wi`, keeps `Post` (`WakeW1.post_local`).
- `post_rtwH`: an out-of-label write of the worker, appended or fulfilled,
  keeps `Post` (`WakeW1.post_rtw`; the worker owns no word, `hown`).
- `post_rtStoreH`, `post_rtRmwH`: the runtime-write rows keep `Post`
  (`WakeW1.post_rtStore`, `WakeW1.post_rtRmw`).
-/
import Spike.Lib.HelloStep1P
import Spike.Lib.WakeW1Rt

namespace Spike.Lib.HelloStep1Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1 (WSideH PT1h PartsH PrintPh StorePh BufV WCompatH post_frameH storePh_not_printPh
  vbuf_of_bufV krW_of)
open Spike.Lib.HelloW1Store (NoWrite relW)
open Spike.Lib.HelloAssembly (HelloCompat)
open Spike.Lib.HelloStep1P (atQ phase_frameRun frameRun_run_source_i post_instrKeepH)
open Spike.Lib.WakeT1 (srcPo)
open Spike.Lib.WakeOwn (wakeOwn)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : WakeM0.MSide Q.ι} {AbW : isaLSE2.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : NoWrite D} {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- The worker's promises are at most the memory's last timestamp. -/
theorem prom_leH (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : ∀ p ∈ t1.prom, p ≤ t.1.mem.last := by
  intro p hp
  obtain ⟨-, m, hg, -⟩ := h.core.prom1 p hp
  exact Scc.Sem.Memory.le_last_of_get? hg

/-! ## A step of the worker with a frame run of the source worker -/

/-- **A worker step matched by a frame run of the source worker keeps
`Post`**: thread 1 replaced by `t1'` and the memory by `mem'` (kept, or one
message of the worker in its footprint appended), the core at the new
target state with the mirrored promises `tp' ⊆ tp` and the source worker at
the run's end, the target part of the protocol at the new memory (with
thread 1's old state for its store point), `Wi` at the run's end. The run
stays in the phases (`phase_frameRun`). -/
theorem post_localH (hC : WCompatH Q D μ Λ arch AbW) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hex : SrcSem.mainExit s = []) {t1' : Thread isaLSE2} {mem' : Memory} {tp' : List Nat}
    {q' : Ctl × List TermRun.Frame} (hkr : HelloW1.KrW Q D w t s t1' mem' (atQ s1 q') t.2)
    (hm : mem' = t.1.mem ∨ ∃ m : Msg, mem' = (t.1.mem.append m).1 ∧ m.tid = 1 ∧ (Q.P w).foot 1 m.loc)
    (hcore : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st q'.2) mem' t0 t1' s.mem s0
      (atQ s1 q') ts tp' sp)
    (hT : CProtT (Q.SR w) (Q.C w) oc mem' t1 ts tp')
    (hpw : ∀ Tc kc, oc = some (Tc, kc) → Tc ∈ tp' → Tc ∈ t1'.prom)
    (htp : ∀ k ∈ tp', k ∈ tp) (hnd : t1'.prom.Nodup)
    (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') (hwi : D.Wi w t1'.st q'.1 q'.2) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 t1' mem', t.2) s' := by
  obtain ⟨hph, hPP, hpass⟩ := phase_frameRun (hC.cwv w) hr rfl rfl (h.pt1.2.2.1.imp_left And.left)
  have hh : q'.1.hold = none := hr.hold_none rfl
  have hc : Ctl.of (atQ s1 q') = q'.1 := by
    obtain ⟨⟨_, _, _⟩, _⟩ := q'
    simp only at hh
    subst hh
    rfl
  have hB : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) (atQ s1 q') →
      BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) s.mem := by
    intro hP
    rcases h.pt1.2.2.1 with ⟨-, hB, -⟩ | hS
    · exact hB
    · exact absurd (hPP hP) (storePh_not_printPh hS (hC.cwv w))
  have hTm : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) (atQ s1 q') → HelloW1.PTermH (atQ s1 q') :=
    HelloStep1P.pTermH_frameRun (hC.cwv w) hr rfl rfl (h.pt1.2.2.1.imp_left fun x => ⟨x.1, x.2.2.1⟩)
  have hN : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) (atQ s1 q') →
      (atQ s1 q').promises = [] ∨ HelloW1.NoEmit (D.cw w) (atQ s1 q') := by
    intro hP
    rcases h.pt1.2.2.1 with ⟨-, -, -, hc'⟩ | hS
    · exact HelloW1.clause_frameRun (hC.cwv w) hc' hr hh hP
    · exact absurd (hPP hP) (storePh_not_printPh hS (hC.cwv w))
  have hrun := frameRun_run_source_i (P := srcPo 2 arch helloSrc) rfl (by decide) hr h.s1_get rfl rfl
    h.pt1.2.1 rfl hex
    (h.certified_phase hC hN hph h.pt1.2.1 rfl rfl hpass.mp)
  have hs' : ({ s with ths := s.ths.set! 1 (atQ s1 q') } : TermRun.Cfg).ths = #[s0, atQ s1 q'] := by
    show s.ths.set! 1 _ = _
    rw [h.ths]; rfl
  have hpT : (Q.C w).passT t1.st ↔ WPass s1 := hC.pass w _ s1 h.pt1.1 (h.pt1.2.2.1.imp_left And.left)
  have hpT' : (Q.C w).passT t1'.st ↔ WPass (atQ s1 q') := hC.pass w _ _ (by rw [hc]; exact hwi) hph
  have hpT'' : (Q.C w).passT t1'.st ↔ (Q.C w).passT t1.st := hpT'.trans (hpass.trans hpT.symm)
  refine ⟨_, hrun, post_frameH (ts' := ts) (tp' := tp') (sp' := sp) hC h.th h.ths hs' h.preC h.pt0 hkr
    h.core.T_le ⟨hm, .inl rfl⟩ hcore ?_ ?_ rfl⟩
  · exact ⟨by rw [hc]; exact hwi, h.pt1.2.1, hph.imp_left fun hP => ⟨hP, hB hP, hTm hP, hN hP⟩, h.pt1.2.2.2.1,
      h.pt1.2.2.2.2.1, hnd⟩
  · obtain ⟨-, hS, -⟩ := (cProt_iff _ _ _).mp h.prot
    have hS' : CProtS (Q.SR w) (Q.C w) oc s.mem s1 tp' sp :=
      ⟨hS.smsg, hS.some_msg, fun Tc kc hoc htp' => hS.prom_worker Tc kc hoc (htp _ htp'), hS.pre_lt,
        hS.prom_view⟩
    refine ⟨oc, (cProt_iff _ _ _).mpr ⟨⟨hT.tmsg, hT.some_msg, hpw,
      fun hq => hT.pass_done (hpT''.mp hq), fun hq => hT.pass_prom (fun h' => hq (hpT''.mpr h'))⟩,
      cProtS_vs hS' ?_ rfl ?_, ?_⟩⟩
    · rw [hC.C w]
      exact ⟨rfl, rfl⟩
    · intro hn h'
      exact hn ((HelloW1.PartsH.passS_iff hC _).mpr (hpass.mpr ((HelloW1.PartsH.passS_iff hC s1).mp h')))
    · rw [HelloW1.PartsH.passS_iff hC _]; exact hpT'

/-! ## An out-of-label write of the worker -/

/-- **An out-of-label write of the worker keeps `Post`**: the message
`⟨wordLoc a, V, 1⟩` (`a` mapped for writing, so in the worker's footprint
and outside every label; `V` a 64-bit `G` value) appended, or one of the
worker's promises of it fulfilled; the new thread's bound, cover and
no-promise fact at the new memory (the worker owns no word); the source
worker after a frame run into `Wi`. -/
theorem post_rtwH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF)
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hown : Q.own = wakeOwn) (hex : SrcSem.mainExit s = [])
    (hwr : t.2.wr 1 = 0)
    {t1' : Thread isaLSE2} {mem' : Memory} {a : Nat} {V : Val} {q' : Ctl × List TermRun.Frame}
    (hmp : (D.ms w []).mp (wordLoc a) true) (hfit : V.toNat < 2 ^ 64) (hG : Q.G w (wordLoc a) V)
    (hcase : (mem' = (t.1.mem.append ⟨wordLoc a, V, 1⟩).1 ∧ t1'.prom = t1.prom) ∨
      (∃ q ∈ t1.prom, t.1.mem.get? q = some ⟨wordLoc a, V, 1⟩ ∧ mem' = t.1.mem ∧ t1'.prom = t1.prom.erase q))
    (hb : t1'.Bnd mem'.last) (hcov : CohCoversL t1'.views t1'.prom mem' ((Q.P w).cov 1))
    (hnp : (Q.P w).noProm t1'.st → t1'.prom = [])
    (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') (hwi : D.Wi w t1'.st q'.1 q'.2) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 t1' mem', t.2) s' := by
  obtain ⟨hf, hout, hin⟩ := hC.2.1.mpW w _ hmp
  have hT0 := ((cProt_iff _ _ _).mp h.prot).1
  have hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT := by
    obtain ⟨a', hcT, hx, ho⟩ := hC.2.1.cT w
    rw [show (Q.C w).cT = wordLoc a' from hcT]; exact WakeW1.inLabel_wordLoc h.core.mem hwf hx ho
  have hO : ∀ i st fs, Q.own w i st fs = [] := fun _ _ _ => by rw [hown]; rfl
  -- the core at the frame run's end, thread 1's target state kept
  have hcore0 : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st q'.2) t.1.mem t0 t1 s.mem s0
      (atQ s1 q') ts tp sp :=
    core1_same h.core (by simp) rfl rfl h.core.bnd1 h.core.cov1 h.core.scov1
      (Consumer1.ownOk_nil (by simp [hO]) _ _) (fun L v v' _ h1 => by simp [hO] at h1)
      (fun L v h1 => by simp [hO] at h1) h.core.noProm1
  have hown' : ExtRows.OwnOk
      ((fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st q'.2) 1) mem' t1'.prom :=
    Consumer1.ownOk_nil (by simp [hO]) _ _
  have hdisj : ∀ L v v', (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st q'.2) 0 →
      (L, v') ∈ (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st q'.2) 1 → False := by
    intro L v v' _ h1; simp [hO] at h1
  have hocov : ∀ L v, (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st q'.2) 1 → (Q.P w).cov 1 L := by
    intro L v h1; simp [hO] at h1
  rcases hcase with ⟨rfl, hp⟩ | ⟨q, hq, hg, rfl, hp⟩
  · -- the append
    have hpl := prom_leH h
    have hT' : CProtT (Q.SR w) (Q.C w) oc (t.1.mem.append ⟨wordLoc a, V, 1⟩).1 t1 ts tp :=
      { hT0 with
        tmsg := fun k w' hk hTk hl => by
          by_cases hk' : k = t.1.mem.last + 1
          · subst hk'
            rw [Scc.Sem.Memory.get?_append_new] at hk
            cases hk
            exact absurd (by rw [show wordLoc a = (Q.C w).cT from hl]; exact hcTin) hout
          · exact hT0.tmsg k w' (CohCoversP.get?_append_ne hk hk') hTk hl
        some_msg := fun Tc kc hoc => by
          obtain ⟨h1, h2, w', hg', h3⟩ := hT0.some_msg Tc kc hoc
          exact ⟨h1, h2, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg',
            h3⟩ }
    have hcore := core1_append hcore0
      (own' := fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st q'.2)
      (w := ⟨wordLoc a, V, 1⟩) (t1' := t1') (sm' := s.mem) (s1' := atQ s1 q') (ts' := ts) (tp' := tp)
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
      h.core.sp_prom rfl hin hfit hG hb hcov h.core.frzS h.core.scov0 h.core.scov1 hown' hdisj hocov
      (fun k hk => by
        rw [hp] at hk
        obtain ⟨hTk, w', hg', ht'⟩ := h.core.prom1 k hk
        exact ⟨hTk, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg', ht'⟩)
      hnp
    exact post_localH hC.1 h hex (krW_of hC.1 h.kr hwr h.th) (.inr ⟨_, rfl, rfl, hf⟩) hcore hT'
      (fun Tc kc hoc htp => by rw [hp]; exact hT0.prom_worker Tc kc hoc htp) (fun k hk => hk)
      (by rw [hp]; exact h.pt1.2.2.2.2.2) hr hwi
  · -- the fulfilment
    have hq0 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) (h.core.prom1 q hq).1
    have hts : ∀ k, ts k ≠ some q := fun k hk =>
      hout (WakeW1.img_inLabel h.core.mem hwf h.core.narrow hk hq0 hg)
    have hTcq : ∀ Tc kc, oc = some (Tc, kc) → Tc ≠ q := by
      rintro Tc kc hoc rfl
      obtain ⟨-, -, w', hg', hl, -⟩ := hT0.some_msg Tc kc hoc
      rw [hg] at hg'; cases hg'
      exact hout (by rw [show wordLoc a = (Q.C w).cT from hl]; exact hcTin)
    have hT' : CProtT (Q.SR w) (Q.C w) oc t.1.mem t1 ts (tp.erase q) :=
      { hT0 with
        prom_worker := fun Tc kc hoc htp => hT0.prom_worker Tc kc hoc (List.mem_of_mem_erase htp)
        pass_done := fun hps => by
          obtain ⟨Tc, kc, hoc, hn⟩ := hT0.pass_done hps
          exact ⟨Tc, kc, hoc, fun hm => hn (List.mem_of_mem_erase hm)⟩
        pass_prom := fun hps Tc kc hoc =>
          (List.mem_erase_of_ne (hTcq Tc kc hoc)).mpr (hT0.pass_prom hps Tc kc hoc) }
    have hcore := WakeW1.Inv2Core.core1_fulfil hcore0 hg hout hts
      (own' := fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st q'.2)
      (by simp) hp hb hcov hown' hdisj hocov hnp
    exact post_localH hC.1 h hex (krW_of hC.1 h.kr hwr h.th) (.inl rfl) hcore hT'
      (fun Tc kc hoc htp => by
        rw [hp]
        exact (List.mem_erase_of_ne (hTcq Tc kc hoc)).mpr (hT0.prom_worker Tc kc hoc (List.mem_of_mem_erase htp)))
      (fun k hk => List.mem_of_mem_erase hk) (by rw [hp]; exact h.pt1.2.2.2.2.2.erase q) hr hwi

/-! ## The runtime-write rows -/

section Rows

variable (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hms : ∀ w fs, D.ms w fs = D.ms w []) (hwf : Λ.WF)
  (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hown : Q.own = wakeOwn) (hex : SrcSem.mainExit s = [])
  (hwr : t.2.wr 1 = 0)
  {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
  (hso : stepOne Arch.armv8 t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
  (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 o.thread o.mem)
include hC hms hwf h hown hex hwr hso ho hco

/-- **The runtime-store row keeps `Post`** (`OutTS.pre` with `Out.rtStore`
at the frames `fs₁`; `hms`: row B8-gen1, `rfl` at `HelloAssemblyI.DH`). -/
theorem post_rtStoreH {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : isaLSE2.State} {c₁ c' : Ctl}
    {fs₁ : List TermRun.Frame} (he : isaLSE2.exec t1.st = some (.store kr false L V fun _ => .done s'))
    (hmp : (D.ms w fs₁).mp L true) (hGV : (D.ms w fs₁).G L V)
    (hr₁ : FrameRun helloSrc (Ctl.of s1, s1.stack) (c₁, fs₁)) (hr : LocalRun helloSrc c₁ c')
    (hX : D.Wi w s' c' fs₁) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  have hwide := hC.1.wide w _ _ _ h.pt1.1
  have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
  have hfit : V.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
  have hG : (D.ms w fs₁).G = Q.G w := by rw [hms w fs₁]; exact hC.2.1.G w
  rw [hG] at hGV
  rw [hms w fs₁] at hmp
  obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
  obtain ⟨hst, hc⟩ := stepOne_store_cases Arch.armv8 he hso ho (prom_leH h)
  have hb := (stepOne_bnd _ hso ho h.core.bnd1).1
  have hcov := stepOne_cohL _ hso ho h.core.cov1
  have hwi : D.Wi w o.thread.st c' fs₁ := hst ▸ hX
  have hr' := hr₁.trans (FrameRun.ofLocal hr fs₁)
  rcases hc with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
  · exact post_rtwH hC hwf h hown hex hwr hmp hfit hGV (.inr ⟨q, hq, hg, hm, hp⟩) hb hcov
      (fun hn => hC.2.1.noProm w _ _ _ hn hco) hr' hwi
  · exact post_rtwH hC hwf h hown hex hwr hmp hfit hGV (.inl ⟨hm, hp⟩) hb hcov
      (fun hn => hC.2.1.noProm w _ _ _ hn hco) hr' hwi

/-- **The runtime-RMW row keeps `Post`** (`OutTS.pre` with `Out.rtRmw` at
the frames `fs₁`): the value read is a `G` value (the memory's invariant;
the worker owns no word); no write keeps memory and promises
(`post_instrKeepH`), a write is out of label (`post_rtwH`). -/
theorem post_rtRmwH {k : Kraken.RmwKind} {L : Loc} {op : Val → Option Val} {g : Val → isaLSE2.State}
    {c₁ c' : Ctl} {fs₁ : List TermRun.Frame}
    (he : isaLSE2.exec t1.st = some (.rmw k false L op fun v => .done (g v))) (hmp : (D.ms w fs₁).mp L true)
    (hr₁ : FrameRun helloSrc (Ctl.of s1, s1.stack) (c₁, fs₁)) (hr : LocalRun helloSrc c₁ c')
    (hX : ∀ old, (D.ms w fs₁).G L old → (∀ u, (L, u) ∈ (D.ms w fs₁).own t1.st → old = u) →
      (∀ new, op old = some new → (D.ms w fs₁).G L new) ∧ D.Wi w (g old) c' fs₁) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  have hwide := hC.1.wide w _ _ _ h.pt1.1
  have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
  have hfit : ∀ old v, op old = some v → v.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
  have hG : (D.ms w fs₁).G = Q.G w := by rw [hms w fs₁]; exact hC.2.1.G w
  have hO : ∀ s, (D.ms w fs₁).own s = [] := fun s => by
    rw [hms w fs₁]
    exact (hC.2.1.own w s).trans (by rw [show (relW Q D hcw hem).own = Q.own from rfl, hown]; rfl)
  rw [hms w fs₁] at hmp
  obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
  obtain ⟨old, tr, hst, hrd, hc⟩ := WakeW1.stepOne_rmw_casesR Arch.armv8 he hso ho (prom_leH h)
  obtain ⟨hGn, hXo⟩ := hX old (by rw [hG]; exact h.core.memInv.read? hrd)
    (fun u hu => by rw [hO] at hu; cases hu)
  have hwi : D.Wi w o.thread.st c' fs₁ := hst ▸ hXo
  have hr' := hr₁.trans (FrameRun.ofLocal hr fs₁)
  rcases hc with ⟨-, hm, hp⟩ | ⟨new, hop, hc⟩
  · exact post_instrKeepH hC h hown hex hwr hso ho hco hm hp hr' hwi
  · have hb := (stepOne_bnd _ hso ho h.core.bnd1).1
    have hcov := stepOne_cohL _ hso ho h.core.cov1
    have hGn' := hGn new hop
    rw [hG] at hGn'
    exact post_rtwH hC hwf h hown hex hwr hmp (hfit old new hop) hGn' hc.symm hb hcov
      (fun hn => hC.2.1.noProm w _ _ _ hn hco) hr' hwi

end Rows

/-- info: 'Spike.Lib.HelloStep1Rt.post_rtwH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_rtwH

/-- info: 'Spike.Lib.HelloStep1Rt.post_rtRmwH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_rtRmwH

end Spike.Lib.HelloStep1Rt
