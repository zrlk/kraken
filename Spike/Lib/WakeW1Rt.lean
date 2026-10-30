/-
**The worker's runtime writes** (data in
`Spike/Lib/WakeW1.lean`, `Spike/Lib/WakeW1Compat.lean`).

A runtime write of the worker (`Out.rtStore`, `Out.rtRmw`) is to a word
outside every placed label (`WCompat.mpW`): the target appends its message
or fulfils one of its promises (an unmirrored one: no source message maps
to it), the source worker takes a local run.

- `inLabel_wordLoc`, `img_inLabel`: a placed word is in its label; a
  target image of a source message is to a placed word.
- `memRelP_tp_erase`, `Inv2Core.core1_fulfil`: a fulfilled promise with
  no source preimage leaves the mirrored ones.
- `post_local`: a worker step to `t1'` and `mem'` (kept, or one message of
  the worker in its footprint appended), the core and the target part of
  the protocol at the new memory, matched by a local run of the source
  worker into `Wi`, keeps `Post`.
- `post_rtw`: an out-of-label write of the worker, appended or fulfilled,
  keeps `Post`.
- `stepOne_rmw_casesR`: `stepOne_rmw_casesL` with no cover (the value read
  is some message's or the initial value).
- `post_rtStore`, `post_rtRmw`: the runtime-write rows keep `Post`.
-/
import Spike.Lib.WakeW1Instr
import Scc.Sem.FixInv
import Scc.Cert.Rt.WideA64

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.WorkerSrcStep

/-! ## Placed words -/

section Placed

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}

/-- **A placed word is in its label.** -/
theorem inLabel_wordLoc (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) {sa : WeakMem.Address}
    {a : Nat} (hx : wordAddr lbl sa = some a) (ho : sa.offset < lsize sa.label) :
    InLabel lbl lsize (wordLoc a) := by
  have hlt := h.addr_lt hwf hx ho
  obtain ⟨b, hb, hc⟩ := lrange_contains_of_wordAddr hx ho
  refine ⟨sa.label, b, hb, ?_⟩
  have e : (wordLoc a).addr.toNat = a := by
    simp only [wordLoc, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [e]; exact hc

/-- **A target image of a source message is to a placed word.** -/
theorem img_inLabel (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) (hn : MemRel.Narrow tm)
    {k q : Nat} (ht : ts k = some q) (hq : 0 < q) {w' : Msg} (hg : tm.get? q = some w') :
    InLabel lbl lsize w'.loc := by
  have hk := h.lt_of_ts ht
  obtain ⟨k'', a, v, ht', ha, hw, -⟩ := h.mem_rep k sm[k] (Array.getElem?_eq_getElem hk)
  rw [ht] at ht'; cases ht'
  obtain ⟨w, hgw, hwl, -⟩ := MemRel.wordAt_msg hn hq hw
  rw [hg] at hgw; cases hgw
  rw [hwl]
  obtain ⟨b, -, ho⟩ := h.lbl_mem sm[k] (by simp)
  exact inLabel_wordLoc h hwf ha ho

/-- **A target promise with no source preimage leaves the mirrored ones.** -/
theorem memRelP_tp_erase (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {q : Nat} (hq : ∀ k, ts k ≠ some q) :
    MemRelP Λ lbl lsize ts tm sm (tp.erase q) tq sp :=
  { h with
    tp_nodup := h.tp_nodup.erase q
    tp_le := fun p hp => h.tp_le p (List.mem_of_mem_erase hp)
    prom_corr := fun k k' ht hk => by
      rw [List.mem_erase_of_ne (fun e => hq k (by rw [← e]; exact ht))]
      exact h.prom_corr k k' ht hk
    tp_tq := fun p hp => h.tp_tq p (List.mem_of_mem_erase hp) }

end Placed

/-- **A fulfilment of an out-of-label promise of thread 1** with no source
preimage keeps the core: memory unchanged, the promise leaves thread 1's
promises and the mirrored ones; thread 1's own facts at the new state. -/
theorem Inv2Core.core1_fulfil {I : ISA} {Λ : Scc.Sem.Layout} {R : SpawnRec} {P : Inv2Params I}
    {G : Loc → Val → Prop} {own : Nat → List (Loc × Val)} {tm : Memory} {t0 t1 : Thread I}
    {sm : WeakMem.Memory} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {q : Nat} {wq : Msg} (hg : tm.get? q = some wq)
    (hout : ¬ InLabel R.lbl R.lsize wq.loc) (hts : ∀ k, ts k ≠ some q) {t1' : Thread I}
    {own' : Nat → List (Loc × Val)} (ho0 : own' 0 = own 0) (hp : t1'.prom = t1.prom.erase q)
    (hb : t1'.Bnd tm.last) (hc : CohCoversL t1'.views t1'.prom tm (P.cov 1))
    (hown : ExtRows.OwnOk (own' 1) tm t1'.prom) (hdisj : ∀ L v v', (L, v) ∈ own 0 → (L, v') ∈ own' 1 → False)
    (hocov : ∀ L v, (L, v) ∈ own' 1 → P.cov 1 L) (hnp : P.noProm t1'.st → t1'.prom = []) :
    Inv2Core Λ R P G own' tm t0 t1' sm s0 s1 ts (tp.erase q) sp :=
  { h with
    mem := memRelP_tp_erase h.mem hts
    tp_prom := fun k hk => by
      have hne : k ≠ q := (h.mem.tp_nodup.mem_erase_iff.mp hk).1
      rcases h.tp_prom k (List.mem_of_mem_erase hk) with h0 | h1
      · exact .inl h0
      · right; rw [hp]; exact (List.mem_erase_of_ne hne).mpr h1
    prom_tp := fun k w hk hg' hin => by
      have hk' : k ∈ t0.prom ∨ k ∈ t1.prom :=
        hk.imp_right fun h1 => by rw [hp] at h1; exact List.mem_of_mem_erase h1
      have hne : k ≠ q := by
        rintro rfl; rw [hg] at hg'; cases hg'; exact hout hin
      exact (List.mem_erase_of_ne hne).mpr (h.prom_tp k w hk' hg' hin)
    bnd1 := hb
    cov1 := hc
    own0 := by rw [ho0]; exact h.own0
    own1 := hown
    own_disj := by rw [ho0]; exact hdisj
    own_cov := fun i L v hi hm => by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [ho0] at hm; exact h.own_cov 0 L v hi hm
      · exact hocov L v hm
    prom1 := fun k hk => h.prom1 k (by rw [hp] at hk; exact List.mem_of_mem_erase hk)
    noProm1 := hnp }

variable {Q : WakeRel} {D : WSide Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-! ## A step of the worker with a local run of the source worker -/

/-- **A worker step matched by a local run of the source worker keeps
`Post`**: thread 1 replaced by `t1'` and the memory by `mem'` (kept, or one
message of the worker in its footprint appended), the core at the new
target state with the mirrored promises `tp' ⊆ tp`, the target part of the
protocol at the new memory (with thread 1's old state for its store point),
the source worker after a local run from its control to `c'` with
`Wi w t1'.st c'`. -/
theorem post_local (hC : WCompat Q D μ Λ arch) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hex : SrcSem.mainExit s = []) {t1' : Thread isaLSE2} {mem' : Memory} {tp' : List Nat} {c' : Ctl}
    (hm : mem' = t.1.mem ∨ ∃ m : Msg, mem' = (t.1.mem.append m).1 ∧ m.tid = 1 ∧ (Q.P w).foot 1 m.loc)
    (hcore : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st s1.stack) mem' t0 t1' s.mem s0 s1
      ts tp' sp)
    (hT : CProtT (Q.SR w) (Q.C w) oc mem' t1 ts tp')
    (hpw : ∀ Tc kc, oc = some (Tc, kc) → Tc ∈ tp' → Tc ∈ t1'.prom)
    (htp : ∀ k ∈ tp', k ∈ tp) (hnd : t1'.prom.Nodup)
    (hr : LocalRun wakeSrc (Ctl.of s1) c') (hwi : D.Wi w t1'.st c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 t1' mem', t.2) s' := by
  have hi := h.s1_get
  have hcw := hC.cwv w
  have hctl' := localRun_wCtl hcw hr h.wCtl
  let s1' : TermRun.TTh := { s1 with term := c'.term, env := c'.env }
  have hc'eq : Ctl.of s1' = c' := by
    obtain ⟨tm, en, hd⟩ := c'
    have : hd = none := hctl'.hold
    subst this; rfl
  have hrun : (wakeS arch).Run s [] { s with ths := s.ths.set! 1 s1' } :=
    localRunS_run_source_i (P := srcPo 2 arch wakeSrc) rfl (by decide) hr.toS hi rfl rfl h.pt1.2.2.1 hex
      (h.certified_set hC hr)
  have hs' : ({ s with ths := s.ths.set! 1 s1' } : TermRun.Cfg).ths = #[s0, s1'] := by
    show s.ths.set! 1 s1' = _
    rw [h.ths]; rfl
  have hpass := localRun_pass hcw hr h.wCtl
  have hpT : ∀ (st : isaLSE2.State) (c : Ctl), D.Wi w st c →
      ((Q.C w).passT st ↔ (c.term = wkUnpark ∨ c.term = .ret .unit)) := hC.pass w
  have hpT' : (Q.C w).passT t1'.st ↔ (Q.C w).passT t1.st := by
    rw [hpT _ _ hwi, hpT _ _ h.pt1.1, hpass]
  refine ⟨_, hrun, post_frame (ts' := ts) (tp' := tp') (sp' := sp) hC h.th h.ths hs' h.preC h.pt0 h.kr h.core.T_le
    ⟨hm, .inl rfl⟩ ?_ ?_ ?_ rfl⟩
  · exact core1_same hcore (by simp) rfl rfl hcore.bnd1 hcore.cov1 hcore.scov1 hcore.own1 hcore.own_disj
      (fun L v hm => hcore.own_cov 1 L v (by decide) hm) hcore.noProm1
  · exact ⟨hc'eq ▸ hwi, h.pt1.2.1, h.pt1.2.2.1, hctl'.term, hctl'.body, hctl'.cj, h.pt1.2.2.2.2.2.2.1,
      h.pt1.2.2.2.2.2.2.2.1, hnd⟩
  · obtain ⟨-, hS, -⟩ := (cProt_iff _ _ _).mp h.prot
    have hS' : CProtS (Q.SR w) (Q.C w) oc s.mem s1 tp' sp :=
      ⟨hS.smsg, hS.some_msg, fun Tc kc hoc htp' => hS.prom_worker Tc kc hoc (htp _ htp'), hS.pre_lt,
        hS.prom_view⟩
    refine ⟨oc, (cProt_iff _ _ _).mpr ⟨⟨hT.tmsg, hT.some_msg, hpw,
      fun hq => hT.pass_done (hpT'.mp hq), fun hq => hT.pass_prom (fun h' => hq (hpT'.mpr h'))⟩,
      cProtS_vs hS' (by rw [hC.C w]; exact ⟨rfl, rfl⟩) rfl ?_, ?_⟩⟩
    · intro hn h'
      exact hn ((Parts.passS_iff hC s1').mpr ⟨h.pt1.2.1, hpass.mpr ((Parts.passS_iff hC s1).mp h').2⟩)
    · rw [Parts.passS_iff hC s1', hpT _ _ hwi]
      exact ⟨fun h' => ⟨h.pt1.2.1, h'⟩, fun h' => h'.2⟩

/-! ## An out-of-label write of the worker -/

/-- **An out-of-label write of the worker keeps `Post`**: the message
`⟨wordLoc a, V, 1⟩` (`a` mapped for writing, so in the worker's footprint
and outside every label; `V` a 64-bit `G` value) appended, or one of the
worker's promises of it fulfilled; the new thread's bound, cover, owned
words and no-promise fact at the new memory; the source worker after a
local run into `Wi`. -/
theorem post_rtw (hC : WCompat Q D μ Λ arch) (hwf : Λ.WF) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hex : SrcSem.mainExit s = []) {t1' : Thread isaLSE2} {mem' : Memory} {a : Nat} {V : Val} {c' : Ctl}
    (hmp : (D.ms w).mp (wordLoc a) true) (hfit : V.toNat < 2 ^ 64) (hG : Q.G w (wordLoc a) V)
    (hcase : (mem' = (t.1.mem.append ⟨wordLoc a, V, 1⟩).1 ∧ t1'.prom = t1.prom) ∨
      (∃ q ∈ t1.prom, t.1.mem.get? q = some ⟨wordLoc a, V, 1⟩ ∧ mem' = t.1.mem ∧ t1'.prom = t1.prom.erase q))
    (hb : t1'.Bnd mem'.last) (hcov : CohCoversL t1'.views t1'.prom mem' ((Q.P w).cov 1))
    (hown : ExtRows.OwnOk (Q.own w 1 t1'.st []) mem' t1'.prom)
    (hnp : (Q.P w).noProm t1'.st → t1'.prom = [])
    (hr : LocalRun wakeSrc (Ctl.of s1) c') (hwi : D.Wi w t1'.st c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 t1' mem', t.2) s' := by
  obtain ⟨hf, hout, hin⟩ := hC.mpW w _ hmp
  have hT0 := ((cProt_iff _ _ _).mp h.prot).1
  have hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT := by
    obtain ⟨a', hcT, hx, ho⟩ := hC.cT w
    rw [hcT]; exact inLabel_wordLoc h.core.mem hwf hx ho
  have hst : s1.stack = [] := h.pt1.2.1
  have hown' : ExtRows.OwnOk
      ((fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st s1.stack) 1) mem' t1'.prom := by
    simp only [Nat.one_ne_zero, ite_false]; rw [hst]; exact hown
  have hdisj : ∀ L v v', (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st s1.stack) 0 →
      (L, v') ∈ (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st s1.stack) 1 → False := by
    intro L v v' h0 h1
    simp only [ite_true] at h0
    simp only [Nat.one_ne_zero, ite_false] at h1
    rw [hst] at h1
    exact hC.ownDisj w _ _ _ L v v' h0 h1
  have hocov : ∀ L v, (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st s1.stack) 1 → (Q.P w).cov 1 L := by
    intro L v h1
    simp only [Nat.one_ne_zero, ite_false] at h1
    rw [hst] at h1
    exact hC.ownCov w _ L v h1
  rcases hcase with ⟨rfl, hp⟩ | ⟨q, hq, hg, rfl, hp⟩
  · -- the append
    have hpl := h.prom_le
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
    have hcore := core1_append h.core
      (own' := fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st s1.stack)
      (w := ⟨wordLoc a, V, 1⟩) (t1' := t1') (sm' := s.mem) (s1' := s1) (ts' := ts) (tp' := tp) (sp' := sp)
      (by simp) rfl hf (.inl rfl) (h.core.mem.runtime_write hout)
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
    exact post_local hC h hex (.inr ⟨_, rfl, rfl, hf⟩) hcore hT'
      (fun Tc kc hoc htp => by rw [hp]; exact hT0.prom_worker Tc kc hoc htp) (fun k hk => hk)
      (by rw [hp]; exact h.nodup) hr hwi
  · -- the fulfilment
    have hq0 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) (h.core.prom1 q hq).1
    have hts : ∀ k, ts k ≠ some q := fun k hk =>
      hout (img_inLabel h.core.mem hwf h.core.narrow hk hq0 hg)
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
    have hcore := Inv2Core.core1_fulfil h.core hg hout hts
      (own' := fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st s1.stack)
      (by simp) hp hb hcov hown' hdisj hocov hnp
    exact post_local hC h hex (.inl rfl) hcore hT'
      (fun Tc kc hoc htp => by
        rw [hp]
        exact (List.mem_erase_of_ne (hTcq Tc kc hoc)).mpr (hT0.prom_worker Tc kc hoc (List.mem_of_mem_erase htp)))
      (fun k hk => List.mem_of_mem_erase hk) (by rw [hp]; exact h.nodup.erase q) hr hwi

/-! ## The runtime-write rows -/

/-- **An RMW's outcomes, with no cover**: it reads some value the memory
holds at its word and keeps memory and promises (no write), or fulfils one
of the thread's promises of the new value, or appends it. -/
theorem stepOne_rmw_casesR {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {k : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hpl : ∀ p ∈ t.prom, p ≤ mem.last) :
    ∃ old tr, o.thread.st = g old ∧ mem.read? (wordLoc a) tr = some old ∧
      ((op old = none ∧ o.mem = mem ∧ o.thread.prom = t.prom) ∨
       (∃ new, op old = some new ∧
        ((∃ q ∈ t.prom, mem.get? q = some ⟨wordLoc a, new, tid⟩ ∧ o.mem = mem ∧ o.thread.prom = t.prom.erase q) ∨
          (o.mem = (mem.append ⟨wordLoc a, new, tid⟩).1 ∧ o.thread.prom = t.prom)))) := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_rmw_iff] at hr
  obtain ⟨tr, old, c1, hx, rfl, hcase⟩ := hr
  obtain ⟨hm0, hp0⟩ := rmwFenceOpt_mem_prom A
    ({ views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } : Kraken.Promising.Ctx)
  obtain ⟨v, hrd, hvo, hce⟩ := readSuccs_shape A _ hx
  have hm1 : c1.mem = mem := (congrArg Ctx.mem hce).trans hm0
  have hp1 : c1.prom = t.prom := (readSuccs_prom A _ hx).trans hp0
  simp only at hvo hrd
  subst hvo
  rw [hm0] at hrd
  refine ⟨old, tr, finishInstr_st hth, hrd, ?_⟩
  rw [(finishInstr_relKey hth).1, hm]
  rcases hcase with ⟨hop, rfl⟩ | ⟨new, c2, hop, hw, rfl⟩
  · obtain ⟨h1, h2⟩ := rmwFenceOpt_mem_prom A c1
    exact .inl ⟨hop, h1.trans hm1, h2.trans hp1⟩
  · refine .inr ⟨new, hop, ?_⟩
    obtain ⟨h1, h2⟩ := rmwFenceOpt_mem_prom A
      (Lower.rmwBump (A.rmwKind k) noRet (wordLoc a) { c2 with rmwWrote := true })
    obtain ⟨h3, h4⟩ := rmwBump_mem_prom (A.rmwKind k) noRet (wordLoc a) { c2 with rmwWrote := true }
    rw [h1, h3, h2, h4]
    simp only
    rcases (Lower.mem_writeSuccs_iff A tid _).mp hw with ⟨q, hq, hg, -, rfl⟩ | ⟨-, rfl⟩
    · rw [hp1] at hq
      rw [hm1] at hg
      refine .inl ⟨q, hq, hg, hm1, ?_⟩
      show c1.prom.erase q = _
      rw [hp1]
    · refine .inr ⟨?_, ?_⟩
      · show (c1.mem.append _).1 = _
        rw [hm1]
      · show (c1.prom ++ [c1.mem.last + 1]).erase (c1.mem.last + 1) = t.prom
        rw [hm1, hp1]
        exact List.erase_append_singleton_self fun hmem => by
          have h1 : @LE.le Nat instLENat (mem.last + 1) mem.last := hpl _ hmem
          omega

section Rows

variable (hC : WCompat Q D μ Λ arch) (hwf : Λ.WF) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
  (hex : SrcSem.mainExit s = []) (hns : abi.atSys t1.st = false)
  {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
  (hso : stepOne Arch.armv8 t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
  (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 o.thread o.mem)
include hC hwf h hex hns hso ho hco

/-- **The runtime-store row keeps `Post`.** -/
theorem post_rtStore {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : isaLSE2.State} {c' : Ctl}
    (he : isaLSE2.exec t1.st = some (.store kr false L V fun _ => .done s')) (hmp : (D.ms w).mp L true)
    (hGV : (D.ms w).G L V) (hr : LocalRun wakeSrc (Ctl.of s1) c') (hX : D.Wi w s' c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  have hwide := hC.wide w _ _ h.pt1.1
  have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
  have hfit : V.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
  rw [hC.G w] at hGV
  obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
  obtain ⟨hst, hc⟩ := stepOne_store_cases Arch.armv8 he hso ho h.prom_le
  have hb := (stepOne_bnd _ hso ho h.core.bnd1).1
  have hcov := stepOne_cohL _ hso ho h.core.cov1
  have hown := h.own_step hC hns hso ho
  have hwi : D.Wi w o.thread.st c' := hst ▸ hX
  rcases hc with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
  · exact post_rtw hC hwf h hex hmp hfit hGV (.inr ⟨q, hq, hg, hm, hp⟩) hb hcov hown
      (fun hn => hC.noProm w _ _ _ hn hco) hr hwi
  · exact post_rtw hC hwf h hex hmp hfit hGV (.inl ⟨hm, hp⟩) hb hcov hown
      (fun hn => hC.noProm w _ _ _ hn hco) hr hwi

/-- **The runtime-RMW row keeps `Post`**: the value read is a `G` value
(the memory's invariant), the owned value if the worker owns the word (its
latest write not promised, under its cover); no write keeps memory and
promises (`post_instrKeep`), a write is out of label (`post_rtw`). -/
theorem post_rtRmw {k : Kraken.RmwKind} {L : Loc} {op : Val → Option Val} {g : Val → isaLSE2.State} {c' : Ctl}
    (he : isaLSE2.exec t1.st = some (.rmw k false L op fun v => .done (g v))) (hmp : (D.ms w).mp L true)
    (hr : LocalRun wakeSrc (Ctl.of s1) c')
    (hX : ∀ old, (D.ms w).G L old → (∀ u, (L, u) ∈ (D.ms w).own t1.st → old = u) →
      (∀ new, op old = some new → (D.ms w).G L new) ∧ D.Wi w (g old) c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  have hwide := hC.wide w _ _ h.pt1.1
  have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
  have hfit : ∀ old v, op old = some v → v.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
  rw [hC.G w] at hX
  simp only [hC.own w] at hX
  obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
  -- the value read, with its facts, and the outcome
  obtain ⟨old, hst, hGo, hoo, hcase⟩ : ∃ old, o.thread.st = g old ∧ Q.G w (wordLoc a) old ∧
      (∀ u, (wordLoc a, u) ∈ Q.own w 1 t1.st [] → old = u) ∧
      ((op old = none ∧ o.mem = t.1.mem ∧ o.thread.prom = t1.prom) ∨
       (∃ new, op old = some new ∧
        ((∃ q ∈ t1.prom, t.1.mem.get? q = some ⟨wordLoc a, new, 1⟩ ∧ o.mem = t.1.mem ∧
            o.thread.prom = t1.prom.erase q) ∨
          (o.mem = (t.1.mem.append ⟨wordLoc a, new, 1⟩).1 ∧ o.thread.prom = t1.prom)))) := by
    by_cases hL : ∃ v0, (wordLoc a, v0) ∈ Q.own w 1 t1.st []
    · obtain ⟨v0, hv0⟩ := hL
      have hcL := hC.ownCov w _ _ v0 hv0
      obtain ⟨old, tr, hst, hl, hrd, hc⟩ := stepOne_rmw_casesL Arch.armv8 he hso ho h.core.cov1 hcL h.prom_le
      refine ⟨old, hst, h.core.memInv.read? hrd, h.own1.read hl hrd, ?_⟩
      rcases hc with hc | ⟨new, hop, ⟨q, hq, hg, -, hm, hp⟩ | hc⟩
      · exact .inl hc
      · exact .inr ⟨new, hop, .inl ⟨q, hq, hg, hm, hp⟩⟩
      · exact .inr ⟨new, hop, .inr hc⟩
    · obtain ⟨old, tr, hst, hrd, hc⟩ := stepOne_rmw_casesR Arch.armv8 he hso ho h.prom_le
      exact ⟨old, hst, h.core.memInv.read? hrd, fun u hu => absurd ⟨u, hu⟩ hL, hc⟩
  obtain ⟨hGn, hXo⟩ := hX old hGo hoo
  have hwi : D.Wi w o.thread.st c' := hst ▸ hXo
  rcases hcase with ⟨-, hm, hp⟩ | ⟨new, hop, hc⟩
  · exact post_instrKeep hC h hex hns hso ho hco hm hp hr hwi
  · have hb := (stepOne_bnd _ hso ho h.core.bnd1).1
    have hcov := stepOne_cohL _ hso ho h.core.cov1
    have hown := h.own_step hC hns hso ho
    exact post_rtw hC hwf h hex hmp (hfit old new hop) (hGn new hop) hc.symm hb hcov hown
      (fun hn => hC.noProm w _ _ _ hn hco) hr hwi

end Rows

/-- info: 'Spike.Lib.WakeW1.post_rtw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_rtw

/-- info: 'Spike.Lib.WakeW1.post_rtRmw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_rtRmw

end Spike.Lib.WakeW1
