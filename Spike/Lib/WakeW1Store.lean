/-
**The worker's flag store** (data in
`Spike/Lib/WakeW1.lean`, `Spike/Lib/WakeW1Compat.lean`).

The `Out.store` row of the worker is its `store rel c 1` (`wkStore`): the
target stores `1` to `cT` and either fulfils its promise `Tc` of it (the
source fulfils the paired `kc`, `store_fulfil_src`) or appends (then no
promise of `c` is outstanding, a dead one would fail certification; the
source appends, `store_append_src`).

- `MemRelP.ts_uniq`: a positive image has one preimage.
- `stepOne_store_append_coh`: an appending store raises the coherence view
  of its location past the old memory.
- `stepOneWith_dord`, `coh_lt_of_certOkC`: under any certification
  semantics, an outstanding promise of a certified thread is above its
  coherence view of the location (Kraken's `coh_lt_of_certOkN`).
- `Inv2Core.core1_mem`: a step of thread 1 with both memories and the map
  unchanged keeps the core, the bookkeeping the row's.
- `envCJ_cons`: `EnvCJ` survives binding another variable.
- `post_store`: the store row keeps `Post`.
-/
import Spike.Lib.WakeW1Rt

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.WorkerSrcStep

/-! ## Generic facts -/

/-- **A positive image has one preimage**: two source messages imaged at
the same positive timestamp are one. -/
theorem MemRelP.ts_uniq {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) (hn : MemRel.Narrow tm)
    {k1 k2 q : Nat} (h1 : ts k1 = some q) (h2 : ts k2 = some q) (hq : 0 < q) : k1 = k2 := by
  have hk1 := h.lt_of_ts h1
  have hk2 := h.lt_of_ts h2
  obtain ⟨_, a1, v1, e1, ha1, hw1, -⟩ := h.mem_rep k1 sm[k1] (Array.getElem?_eq_getElem hk1)
  obtain ⟨_, a2, v2, e2, ha2, hw2, -⟩ := h.mem_rep k2 sm[k2] (Array.getElem?_eq_getElem hk2)
  rw [h1] at e1; cases e1
  rw [h2] at e2; cases e2
  obtain ⟨w1, g1, l1, -⟩ := MemRel.wordAt_msg hn hq hw1
  obtain ⟨w2, g2, l2, -⟩ := MemRel.wordAt_msg hn hq hw2
  rw [g1] at g2; cases g2
  obtain ⟨-, -, o1⟩ := h.lbl_mem sm[k1] (by simp)
  obtain ⟨-, -, o2⟩ := h.lbl_mem sm[k2] (by simp)
  have hlt1 := h.addr_lt hwf ha1 o1
  have hlt2 := h.addr_lt hwf ha2 o2
  have ea : a1 = a2 := MemRel.wordLoc_inj (by omega) (by omega) (l1.symm.trans l2)
  subst ea
  have el := h.wordAddr_inj ha1 ha2 o1 o2
  rcases Nat.lt_trichotomy k1 k2 with hl | he | hl
  · have := h.ts_mono k1 k2 q q _ _ (Array.getElem?_eq_getElem hk1) (Array.getElem?_eq_getElem hk2) el h1 h2 hq hq hl
    omega
  · exact he
  · have := h.ts_mono k2 k1 q q _ _ (Array.getElem?_eq_getElem hk2) (Array.getElem?_eq_getElem hk1) el.symm h2 h1 hq
      hq hl
    omega

/-- **An appending store raises the coherence view of its location** past
the old memory's last timestamp. -/
theorem stepOne_store_append_coh {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {kr : StoreKind} {a : Nat} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (happ : o.mem = (mem.append ⟨wordLoc a, v, tid⟩).1) :
    mem.last + 1 ≤ o.thread.views.getCoh (wordLoc a) := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_store_iff] at hr
  obtain ⟨rfl, hw⟩ := hr
  obtain ⟨-, e2⟩ := finishInstr_relKey hth
  have e3 : o.thread.views.coh = c'.views.coh := by have := congrArg Views.coh e2; exact this
  have hge : o.thread.views.getCoh (wordLoc a) = c'.views.getCoh (wordLoc a) := by
    unfold Views.getCoh; rw [e3]
  rw [hge]
  rcases (Lower.mem_writeSuccs_iff A tid _).mp hw with ⟨q, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · exfalso
    rw [hm] at happ
    have e : mem = (mem.append ⟨wordLoc a, v, tid⟩).1 := happ
    have := congrArg Memory.last e
    rw [Kraken.Promising.Memory.last_append] at this
    exact Nat.succ_ne_self _ this.symm
  · show mem.last + 1 ≤ (Views.setCoh _ (wordLoc a) (mem.last + 1)).getCoh (wordLoc a)
    rw [Views.getCoh_setCoh, ite_eq_left_of_eq_true _ _ (eq_self _)]
    exact Nat.le_max_right _ _

section Cert

variable {I : ISA} (A : Arch) {cs : CertSem I} {tid : Nat}

/-- **One step under any certification semantics orders fulfilment after
`coh`** (`stepOne_dord`'s `coh` half, for `cs.step`). -/
theorem stepOneWith_dord {t : Thread I} {mem : Memory} {outs : List (Except String (Kraken.Promising.Outcome I))}
    {o : Kraken.Promising.Outcome I} (hstep : cs.step A t tid mem = some outs) (ho : .ok o ∈ outs) :
    (∀ l, t.views.getCoh l ≤ o.thread.views.getCoh l) ∧ mem.Prefix o.mem ∧
      ∀ ts ∈ t.prom, ts ∉ o.thread.prom → ∀ w, mem.get? ts = some w → t.views.getCoh w.loc < ts := by
  obtain ⟨tree, st, c', -, hr, hth, hm⟩ := stepOneWith_runOut A hstep ho
  have hw := runTree_dord A tid _ tree _ st c' hr
  obtain ⟨hp, hv⟩ := finishInstr_relKey hth
  have hcoh : o.thread.views.coh = c'.views.coh := by have := congrArg Views.coh hv; exact this
  refine ⟨fun l => ?_, by rw [hm]; exact hw.mem, fun ts h1 h2 w hw' => ?_⟩
  · have := hw.coh l
    simp only [Views.getCoh, hcoh] at this ⊢
    exact this
  · rw [hp] at h2
    exact (hw.prom ts h1 h2).2 w hw'

/-- **A certified thread has no dead promise** (under any certification
semantics): every outstanding promise is above the thread's coherence view
of its location. -/
theorem coh_lt_of_certOkC {t : Thread I} {mem : Memory} (hc : CertOkC A cs tid t mem) {ts : Time} {w : Msg}
    (hts : ts ∈ t.prom) (hw : mem.get? ts = some w) : t.views.getCoh w.loc < ts := by
  obtain ⟨t', mem', h, hp⟩ := hc
  suffices ∀ p q, ThreadNPC A cs tid p q → q.1.prom = [] → ∀ ts w, ts ∈ p.1.prom → p.2.get? ts = some w →
      p.1.views.getCoh w.loc < ts from this _ _ h hp ts w hts hw
  intro p q h
  induction h with
  | refl p => intro hq ts w hts _; rw [hq] at hts; cases hts
  | @step p q r hs _ ih =>
    intro hq ts w hts hw
    obtain ⟨outs, o, hstep, ho, rfl⟩ := hs
    obtain ⟨hcoh, hpre, hful⟩ := stepOneWith_dord A hstep ho
    by_cases hin : ts ∈ o.thread.prom
    · refine Nat.lt_of_le_of_lt (hcoh _) (ih hq ts w hin ?_)
      show o.mem.get? ts = some w
      rw [hpre.get? (Kraken.Promising.Memory.le_last_of_get? hw)]; exact hw
    · exact hful ts hts hin w hw

end Cert

/-- **A step of thread 1 with both memories and the map unchanged** keeps
the core: the mirrored promises, the source promises, thread 1's bound,
cover, source cover, owned words, promises and no-promise fact are the
row's. -/
theorem Inv2Core.core1_mem {I : ISA} {Λ : Scc.Sem.Layout} {R : SpawnRec} {P : Inv2Params I}
    {G : Loc → Val → Prop} {own : Nat → List (Loc × Val)} {tm : Memory} {t0 t1 : Thread I}
    {sm : WeakMem.Memory} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {t1' : Thread I} {s1' : TermRun.TTh}
    {own' : Nat → List (Loc × Val)} {tp' sp' : List Nat} (ho0 : own' 0 = own 0)
    (hmem : MemRelP Λ R.lbl R.lsize ts tm sm tp' [] sp')
    (htp : ∀ k ∈ tp', k ∈ t0.prom ∨ k ∈ t1'.prom)
    (hpt : ∀ k w, (k ∈ t0.prom ∨ k ∈ t1'.prom) → tm.get? k = some w → InLabel R.lbl R.lsize w.loc → k ∈ tp')
    (hsp : ∀ k, k ∈ sp' ↔ k ∈ s0.promises ∨ k ∈ s1'.promises)
    (hb : t1'.Bnd tm.last) (hc : CohCoversL t1'.views t1'.prom tm (P.cov 1))
    (hsc : ∀ k m, sm[k]? = some m → P.frzS m.loc → k ≤ s1'.vs.coh m.loc)
    (hown : ExtRows.OwnOk (own' 1) tm t1'.prom) (hdisj : ∀ L v v', (L, v) ∈ own 0 → (L, v') ∈ own' 1 → False)
    (hocov : ∀ L v, (L, v) ∈ own' 1 → P.cov 1 L)
    (hpr : ∀ k ∈ t1'.prom, R.T < k ∧ ∃ w, tm.get? k = some w ∧ w.tid = 1)
    (hnp : P.noProm t1'.st → t1'.prom = []) :
    Inv2Core Λ R P G own' tm t0 t1' sm s0 s1' ts tp' sp' :=
  { h with
    mem := hmem
    tp_prom := htp
    prom_tp := hpt
    sp_prom := hsp
    bnd1 := hb
    cov1 := hc
    scov1 := hsc
    own0 := by rw [ho0]; exact h.own0
    own1 := hown
    own_disj := by rw [ho0]; exact hdisj
    own_cov := fun i L v hi hm => by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [ho0] at hm; exact h.own_cov 0 L v hi hm
      · exact hocov L v hm
    prom1 := hpr
    noProm1 := hnp }

/-- **`EnvCJ` survives binding `d`.** -/
theorem envCJ_cons {cw : TermRun.Word} {env : TermRun.Env} (h : EnvCJ cw env) (ty : Ty) (ws : List TermRun.Word) :
    EnvCJ cw (("d", ty, ws) :: env) := by
  simpa [EnvCJ, TermRun.evalAt, TermRun.lookupE, List.find?_cons] using h

/-- A list of at most one element containing `k` is `[k]`. -/
theorem eq_single_of_length {l : List Nat} {k : Nat} (hl : l.length ≤ 1) (hk : k ∈ l) : l = [k] := by
  rcases l with _ | ⟨k1, _ | ⟨k2, l⟩⟩
  · cases hk
  · simp at hk; rw [hk]
  · simp at hl

variable {Q : WakeRel} {D : WSide Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-! ## The store row -/

section Rows

variable (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D) (hwf : Λ.WF)
  (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
  (hex : SrcSem.mainExit s = []) (hns : abi.atSys t1.st = false)
  {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
  (hso : stepOne Arch.armv8 t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
  (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 o.thread o.mem)
include hC hx hwf h hex hns hso ho hco

/-- **The store row keeps `Post`**: the worker's `store rel c 1`. -/
theorem post_store {kr : Kraken.StoreKind} {A : BitVec 64} {V : Val} {s' : isaLSE2.State} {x : String}
    {a b : At} {e : Expr} {ty tb : Ty} {wa wb : TermRun.Word}
    (he : isaLSE2.exec t1.st = some (.store kr false ⟨A, 8⟩ V fun _ => .done s'))
    (ht : (Ctl.of s1).term = .let_ x (.store true a b none) e)
    (hea : TermRun.evalAt (Ctl.of s1).env a = some (ty, [wa])) (hva : ValRep (D.lbl w) wa.val A.toNat)
    (heb : TermRun.evalAt (Ctl.of s1).env b = some (tb, [wb])) (hvb : ValRep (D.lbl w) wb.val V.toNat)
    (hX : D.Wi w s' ⟨e, (x, .unit, []) :: (Ctl.of s1).env, none⟩) :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  -- the source worker is at its store
  have hst1 : s1.term = wkStore := by
    rcases h.pt1.2.2.2.1 with h1 | h1 | h1 | h1 | h1 <;>
      first
      | exact h1
      | (exfalso; change s1.term = _ at ht; rw [h1] at ht; simp [wkTail, wkBody, wkUnpark] at ht)
  have hnps : ¬ PreSplit s1.term := by
    rw [hst1]; rintro (hp | hp) <;> simp [wkStore, wkTail, wkBody] at hp
  have hcj := h.pt1.2.2.2.2.2.1 hnps
  change s1.term = _ at ht
  rw [hst1] at ht
  simp only [wkStore, Expr.let_.injEq] at ht
  obtain ⟨rfl, hop, rfl⟩ := ht
  simp only [Op.store.injEq, true_and, and_true] at hop
  obtain ⟨rfl, rfl⟩ := hop
  -- the address is `cT`, the value `1`
  obtain ⟨cty, cμ, cu, hcv, hcell, hcu⟩ := hcj.1
  have hwa : wa = D.cw w := by
    change TermRun.evalAt s1.env _ = _ at hea
    rw [hcv] at hea; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea
    exact hea.2.symm
  subst hwa
  obtain ⟨a', hcT, hcTa, hcTo⟩ := hC.cT w
  rw [hC.cwv w, hC.lbl w] at hva
  obtain ⟨-, x0, hx0, hA⟩ := hva
  rw [hcTa] at hx0; cases hx0
  have hA' : A = BitVec.ofNat 64 a' := by
    apply BitVec.eq_of_toNat_eq
    have := A.isLt
    simp only [BitVec.toNat_ofNat]
    omega
  subst hA'
  simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at heb
  obtain ⟨-, rfl⟩ := heb
  have hV : V = 1 := by
    apply BitVec.eq_of_toNat_eq
    change 1 < 2 ^ 64 ∧ V.toNat = 1 at hvb
    rw [hvb.2]; rfl
  subst hV
  have he' : isaLSE2.exec t1.st = some (.store kr false (wordLoc a') 1 fun _ => .done s') := he
  -- facts shared by both outcomes
  have hcw := hC.cwv w
  have hpT := hC.pass w
  have hnpT : ¬ (Q.C w).passT t1.st := by
    rw [hpT _ _ h.pt1.1]
    change ¬ (s1.term = wkUnpark ∨ s1.term = .ret .unit)
    rw [hst1]; rintro (hp | hp) <;> simp [wkStore, wkUnpark] at hp
  obtain ⟨hst, hc⟩ := stepOne_store_cases Arch.armv8 he' hso ho h.prom_le
  have hwi : D.Wi w o.thread.st ⟨wkUnpark, ("d", .unit, []) :: s1.env, none⟩ := by rw [hst]; exact hX
  have hpost : (Q.C w).passT o.thread.st := (hpT _ _ hwi).mpr (.inl rfl)
  obtain ⟨hT0, hS, hl⟩ := (cProt_iff _ _ _).mp h.prot
  have hAt : AtStore (D.cw w) (Q.C w).cS s1 := ⟨hst1, h.pt1.2.1, h.pt1.2.2.1, hcj.1, hcw⟩
  have hs0 : s0.promises = [] := hx.sp0 w _ _ _ _ h.pt0
  have hb := (stepOne_bnd _ hso ho h.core.bnd1).1
  have hcov := stepOne_cohL _ hso ho h.core.cov1
  have hown := h.own_step hC hns hso ho
  have hnp : (Q.P w).noProm o.thread.st → o.thread.prom = [] := fun hn => hC.noProm w _ _ _ hn hco
  have hstk : s1.stack = [] := h.pt1.2.1
  have hown' : ∀ (s1' : TermRun.TTh), s1'.stack = [] → ExtRows.OwnOk
      ((fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 o.thread.st s1'.stack) 1) o.mem
      o.thread.prom := by
    intro s1' hs; simp only [Nat.one_ne_zero, ite_false]; rw [hs]; exact hown
  have hdisj : ∀ (s1' : TermRun.TTh), s1'.stack = [] → ∀ L v v', (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st s1.stack) 0 →
      (L, v') ∈ (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 o.thread.st s1'.stack) 1 →
      False := by
    intro s1' hs L v v' h0 h1
    simp only [ite_true] at h0
    simp only [Nat.one_ne_zero, ite_false] at h1
    rw [hs] at h1
    exact hC.ownDisj w _ _ _ L v v' h0 h1
  have hocov : ∀ (s1' : TermRun.TTh), s1'.stack = [] → ∀ L v, (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 o.thread.st s1'.stack) 1 →
      (Q.P w).cov 1 L := by
    intro s1' hs L v h1
    simp only [Nat.one_ne_zero, ite_false] at h1
    rw [hs] at h1
    exact hC.ownCov w _ L v h1
  have hpt1 : ∀ (vs : WeakMem.VState) (mem' : Memory) (sm' : WeakMem.Memory), o.thread.prom.Nodup →
      PT1 D w mem' sm' o.thread (afterStore s1 vs []) := by
    intro vs mem' sm' hnd
    refine ⟨hwi, hstk, h.pt1.2.2.1, .inr (.inr (.inr (.inl rfl))), fun hp => ?_, fun _ => envCJ_cons hcj _ _,
      by simp [afterStore], fun k hk => by simp [afterStore] at hk, hnd⟩
    exfalso
    change PreSplit wkUnpark at hp
    rcases hp with hp | hp <;> simp [wkUnpark, wkTail, wkBody] at hp
  have hscS : ∀ (vs : WeakMem.VState), (∀ b, b ≠ (Q.C w).cS → vs.coh b = s1.vs.coh b) →
      ∀ (sm' : WeakMem.Memory), (∀ k m, sm'[k]? = some m → (Q.P w).frzS m.loc → k ≤ s1.vs.coh m.loc) →
      ∀ k m, sm'[k]? = some m → (Q.P w).frzS m.loc → k ≤ (afterStore s1 vs []).vs.coh m.loc := by
    intro vs hvo sm' hsc k m hk hz
    show k ≤ vs.coh m.loc
    rw [hvo m.loc (fun e => hC.cSfrz w (e ▸ hz))]
    exact hsc k m hk hz
  have hpassS : ∀ (vs : WeakMem.VState), (Q.C w).passS (afterStore s1 vs []) := fun vs =>
    (Parts.passS_iff (w := w) hC _).mpr (wPass_afterStore hstk vs [])
  rcases hc with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
  · -- the fulfilment: `q` is the protocol's `Tc`, the source fulfils `kc`
    have hTq : (Q.SR w).T < q := (h.core.prom1 q hq).1
    obtain ⟨kc, hoc, -⟩ := hT0.tmsg q _ hg hTq hcT.symm
    subst hoc
    have hqtp : q ∈ tp := hT0.pass_prom hnpT q kc rfl
    have hkc1 : kc ∈ s1.promises := hS.prom_worker q kc rfl hqtp
    have hs1p : s1.promises = [kc] := eq_single_of_length h.pt1.2.2.2.2.2.2.1 hkc1
    have hkcsp : kc ∈ sp := (h.core.sp_prom kc).mpr (.inr hkc1)
    obtain ⟨-, m, hm', hml, hmv⟩ := hS.some_msg q kc rfl
    have hnpS : ¬ (Q.C w).passS s1 := fun hps => hnpT (hl.mpr hps)
    obtain ⟨hmv', hob⟩ := fulfil_ok hS hnpS hkcsp hm'
    rw [hC.C w] at hmv' hob
    obtain ⟨vs, hstep, -, hvo⟩ := store_fulfil_src (P := srcPo 2 arch wakeSrc) (p := wakeSrc) rfl h.s1_get hAt
      hs1p hm' hml hmv hmv' hob hex
    have hrun : (wakeS arch).Run s [] { s with ths := s.ths.set! 1 (afterStore s1 vs []) } :=
      LRun.step (step := fun c es c' => ∃ i, (wakeS arch).step i c es c') ⟨1, hstep⟩ (LRun.refl _)
    have hs' : ({ s with ths := s.ths.set! 1 (afterStore s1 vs []) } : TermRun.Cfg).ths =
        #[s0, afterStore s1 vs []] := by
      show s.ths.set! 1 _ = _
      rw [h.ths]; rfl
    obtain ⟨-, hts, -⟩ := hT0.some_msg q kc rfl
    have hq0 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) hTq
    have huniq : ∀ k2, ts k2 = some q → k2 = kc := fun k2 h2 =>
      MemRelP.ts_uniq h.core.mem hwf h.core.narrow h2 hts hq0
    have hqn : q ∉ tp.erase q := h.core.mem.tp_nodup.not_mem_erase
    rw [hm]
    rw [hm] at hb hcov hown'
    refine ⟨_, hrun, post_frame (ts' := ts) (tp' := tp.erase q) (sp' := sp.erase kc) hC h.th h.ths hs' h.preC
      h.pt0 h.kr h.core.T_le ⟨.inl rfl, .inl rfl⟩ ?_ (hpt1 vs _ _ (by rw [hp]; exact h.nodup.erase q)) ?_ rfl⟩
    · refine Inv2Core.core1_mem h.core (by simp) (h.core.mem.fulfil hts huniq) ?_ ?_ ?_ hb ?_
        (hscS vs hvo s.mem h.core.scov1) (hown' _ hstk) (hdisj _ hstk)
        (hocov _ hstk) ?_ hnp
      · intro k hk
        have hne : k ≠ q := (h.core.mem.tp_nodup.mem_erase_iff.mp hk).1
        rcases h.core.tp_prom k (List.mem_of_mem_erase hk) with h0 | h1
        · exact .inl h0
        · right; rw [hp]; exact (List.mem_erase_of_ne hne).mpr h1
      · intro k w' hk hg' hin
        have hne : k ≠ q := by
          rintro rfl
          rcases hk with h0 | h1
          · obtain ⟨-, w0, hg0, ht0⟩ := h.core.prom0 _ h0
            rw [hg] at hg0; cases hg0; cases ht0
          · rw [hp] at h1; exact h.nodup.not_mem_erase h1
        have hk' : k ∈ t0.prom ∨ k ∈ t1.prom :=
          hk.imp_right fun h1 => by rw [hp] at h1; exact List.mem_of_mem_erase h1
        exact (List.mem_erase_of_ne hne).mpr (h.core.prom_tp k w' hk' hg' hin)
      · intro k
        constructor
        · intro hk
          obtain ⟨hne, hk'⟩ := h.core.mem.sp_nodup.mem_erase_iff.mp hk
          rcases (h.core.sp_prom k).mp hk' with h0 | h1
          · rw [hs0] at h0; cases h0
          · rw [hs1p] at h1; exact absurd (List.mem_singleton.mp h1) hne
        · rintro (h0 | h1)
          · rw [hs0] at h0; cases h0
          · simp [afterStore] at h1
      · exact hcov
      · intro k hk
        rw [hp] at hk
        exact h.core.prom1 k (List.mem_of_mem_erase hk)
    · refine ⟨some (q, kc), (cProt_iff _ _ _).mpr ⟨⟨hT0.tmsg, hT0.some_msg, fun Tc kc' hoc htp => ?_,
        fun _ => ⟨q, kc, rfl, hqn⟩, fun hn => absurd hpost hn⟩, cProtS_fulfil hS hkcsp (hpassS vs) hqn,
        ⟨fun _ => hpassS vs, fun _ => hpost⟩⟩⟩
      cases hoc; exact absurd htp hqn
  · -- the append: no promise of `c` is outstanding (it would be dead)
    obtain _ | ⟨Tc, kc⟩ := oc
    rotate_left
    · exfalso
      have hTc : Tc ∈ t1.prom := hT0.prom_worker Tc kc rfl (hT0.pass_prom hnpT Tc kc rfl)
      obtain ⟨-, -, wq, hgq, hlq, -⟩ := hT0.some_msg Tc kc rfl
      have hle : Tc ≤ t.1.mem.last := h.prom_le Tc hTc
      have hgq' : o.mem.get? Tc = some wq := by
        rw [hm, Scc.Sem.Memory.get?_append_le hle]; exact hgq
      have h1 := coh_lt_of_certOkC _ hco (by rw [hp]; exact hTc) hgq'
      have h2 := stepOne_store_append_coh Arch.armv8 he' hso ho hm
      rw [hlq, hcT] at h1
      have h3 : @LT.lt Nat instLTNat (o.thread.views.getCoh (wordLoc a')) Tc := h1
      have h4 : @LE.le Nat instLENat (t.1.mem.last + 1) (o.thread.views.getCoh (wordLoc a')) := h2
      omega
    have hs1p : s1.promises = [] := by
      cases hp1 : s1.promises with
      | nil => rfl
      | cons k ks =>
        obtain ⟨Tc, hoc⟩ := h.src_prom hC (k := k) (by rw [hp1]; exact List.mem_cons_self)
        cases hoc
    obtain ⟨vs, hstep, -, hvo⟩ := store_append_src (P := srcPo 2 arch wakeSrc) (p := wakeSrc) rfl h.s1_get hAt
      hs1p hex
    let mS : WeakMem.Msg :=
      ⟨(Q.C w).cS, .num 1, Promises.storeMview (wTh s1.vs (D.cw w)) (TermRun.dataE 1 one) [0] true⟩
    have hrun : (wakeS arch).Run s []
        { s with mem := s.mem.push mS, ths := s.ths.set! 1 (afterStore s1 vs []) } :=
      LRun.step (step := fun c es c' => ∃ i, (wakeS arch).step i c es c') ⟨1, hstep⟩ (LRun.refl _)
    have hs' : ({ s with mem := s.mem.push mS, ths := s.ths.set! 1 (afterStore s1 vs []) } : TermRun.Cfg).ths =
        #[s0, afterStore s1 vs []] := by
      show s.ths.set! 1 _ = _
      rw [h.ths]; rfl
    have hfoot : (Q.P w).foot 1 (wordLoc a') := hcT ▸ hC.cTfoot w
    have hnew : (Q.SR w).T < t.1.mem.last + 1 := Nat.lt_succ_of_le h.core.T_le
    have htpn : t.1.mem.last + 1 ∉ tp := fun htp => by
      have := (h.core.mem.tp_le _ htp).2
      omega
    have hspn : s.mem.size ∉ sp := fun hk => by
      have := h.core.mem.sp_lt _ hk
      omega
    have hmemR := h.core.mem.store (a := a') (v := 1) (tid := 1) (m := mS) hcTa hcTo ⟨by decide, rfl⟩ false
    simp only [Bool.false_eq_true, ite_false] at hmemR
    have hpl := h.prom_le
    rw [hm]
    rw [hm] at hb hcov hown'
    refine ⟨_, hrun, post_frame (ts' := fun k => if k = s.mem.size then some (t.1.mem.last + 1) else ts k)
      (tp' := tp) (sp' := sp) hC h.th h.ths hs' h.preC h.pt0 h.kr h.core.T_le
      ⟨.inr ⟨_, rfl, rfl, hfoot⟩, .inr ⟨mS, rfl, rfl⟩⟩ ?_ (hpt1 vs _ _ (by rw [hp]; exact h.nodup)) ?_ rfl⟩
    · refine core1_append h.core (by simp) rfl hfoot (.inr ⟨mS, rfl⟩) hmemR
        (fun k hk => by rw [hp]; exact h.core.tp_prom k hk) ?_ ?_ rfl (hcT ▸ hC.cTin w) (show (1 : Val).toNat < 2 ^ 64 by decide)
        (hcT ▸ hx.Gc w) hb hcov (Inv2Rely.frzS_push h.core.frzS (hC.cSfrz w))
        (Inv2Rely.scov_push h.core.scov0 (hC.cSfrz w))
        (hscS vs hvo _ (Inv2Rely.scov_push h.core.scov1 (hC.cSfrz w))) (hown' _ hstk) (hdisj _ hstk)
        (hocov _ hstk) ?_ hnp
      · intro k w' hk hg' hin'
        have hk1 : k ∈ t0.prom ∨ k ∈ t1.prom := by rw [hp] at hk; exact hk
        have hle : k ≤ t.1.mem.last := by
          rcases hk1 with hk0 | hk1
          · obtain ⟨-, w0, hg0, -⟩ := h.core.prom0 k hk0
            exact Scc.Sem.Memory.le_last_of_get? hg0
          · exact hpl k hk1
        rw [Scc.Sem.Memory.get?_append_le hle] at hg'
        exact h.core.prom_tp k w' hk1 hg' hin'
      · intro k
        rw [h.core.sp_prom k, hs1p]
        simp [afterStore]
      · intro k hk
        rw [hp] at hk
        obtain ⟨hTk, w', hg', ht'⟩ := h.core.prom1 k hk
        exact ⟨hTk, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg', ht'⟩
    · refine ⟨some (t.1.mem.last + 1, s.mem.size), (cProt_iff _ _ _).mpr ⟨⟨?_, ?_, ?_,
        fun _ => ⟨_, _, rfl, htpn⟩, fun hn => absurd hpost hn⟩,
        cProtS_append hS h.core.S_le (hpassS vs) htpn hspn, ⟨fun _ => hpassS vs, fun _ => hpost⟩⟩⟩
      · intro k w' hk hTk hl'
        by_cases hk' : k = t.1.mem.last + 1
        · subst hk'
          rw [Scc.Sem.Memory.get?_append_new] at hk
          cases hk
          exact ⟨s.mem.size, rfl, rfl⟩
        · obtain ⟨kc, hoc, -⟩ := hT0.tmsg k w' (CohCoversP.get?_append_ne hk hk') hTk hl'
          cases hoc
      · intro Tc kc hoc
        cases hoc
        exact ⟨hnew, by simp, _, Scc.Sem.Memory.get?_append_new, hcT.symm, rfl, rfl⟩
      · intro Tc kc hoc htp
        cases hoc
        exact absurd htp htpn

end Rows

/-- info: 'Spike.Lib.WakeW1.post_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_store

end Spike.Lib.WakeW1
