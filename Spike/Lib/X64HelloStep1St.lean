/-
**hello.w on x86-64: the worker's flag store after `print` returns** (the
twin of `X64WakeW1.post_store` at `PartsH`, with a
frame-run prefix).

From the print phase the frame-aware rows (`HelloSegThrS.OutTS.pre`,
`.top`) may run the source worker through `print`'s return to the store
(`wkStore`, the store phase) and then take `Out.store` there: the
target's `store rel c 1`. The source runs the frame run to the store
(`X64HelloStep1P.frameRun_run_source_i`, its end certified by
`PartsH.certified_phase`), then its store, fulfilling the flag's promise
`kc` (`WorkerSrc.store_fulfil_src`) or appending
(`WorkerSrc.store_append_src`), as in `X64WakeW1.post_store`. The target
worker was in the print phase, so not past its store point.

- `post_storeH`: the store row after a frame run into the store phase
  keeps `Post`.

x86-64 twin of `Spike/Lib/HelloStep1St.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, the target's store is an x86-64 store under `Arch.tso`
(`stepOne Arch.tso` at `isa`).
-/
import Spike.Lib.X64HelloStep1Rt
import Spike.Lib.X64HelloOwn1

namespace Spike.Lib.X64HelloStep1St

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1 (WSideH PT1h PartsH PrintPh StorePh WCompatH post_frameH storePh_not_printPh
  printPh_not_pass krW_of)
open Spike.Lib.X64HelloW1Store (NoWrite relW)
open Spike.Lib.X64HelloAssembly (HelloCompat)
open Spike.Lib.X64HelloStep1P (atQ frameRun_run_source_i)
open Spike.Lib.WorkerSrcStep (getElem?_set!_self mainExit_eq)
open Spike.Lib.X64WakeT1 (srcPo)
open Spike.Lib.X64HelloOwn1 (Own1H)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : X64WakeM0.MSide Q.ι} {AbW : isa.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : NoWrite D} {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **The store row after a frame run into the store phase keeps `Post`**:
from the print phase the source worker runs to the store `c₁` (the store
phase on an empty stack, at `wkStore`), where the target's store is the
worker's `store rel c 1` (`X64WakeW1.post_store`, the source's frame run
first). -/
theorem post_storeH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF)
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hown : Own1H Q D Λ) (hex : SrcSem.mainExit s = [])
    (hwr : t.2.wr 1 = 0)
    (hP : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1)
    {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hso : stepOne Arch.tso t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 1) 1 o.thread o.mem)
    {c₁ : Ctl} (hr₁ : FrameRun helloSrc (Ctl.of s1, s1.stack) (c₁, []))
    (hS₁ : StorePh (D.cw w) (atQ s1 (c₁, []))) (ht₁ : c₁.term = wkStore)
    {kr : Kraken.StoreKind} {A : BitVec 64} {V : Val} {s' : isa.State} {x : String}
    {a b : At} {e : Expr} {ty tb : Ty} {wa wb : TermRun.Word}
    (he : isa.exec t1.st = some (.store kr false ⟨A, 8⟩ V fun _ => .done s'))
    (ht : c₁.term = .let_ x (.store true a b none) e)
    (hea : TermRun.evalAt c₁.env a = some (ty, [wa])) (hva : ValRep (D.lbl w) wa.val A.toNat)
    (heb : TermRun.evalAt c₁.env b = some (tb, [wb])) (hvb : ValRep (D.lbl w) wb.val V.toNat)
    (hX : D.Wi w s' ⟨e, (x, .unit, []) :: c₁.env, none⟩ []) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  have hC1 := hC.1
  have hC2 := hC.2.1
  have hx := hC.2.2.1
  -- the source worker at the store, after the frame run
  let th1 : TermRun.TTh := atQ s1 (c₁, [])
  have hcj : X64WakeW1.EnvCJ (D.cw w) c₁.env := hS₁.2.2
  rw [ht₁] at ht
  simp only [wkStore, Expr.let_.injEq] at ht
  obtain ⟨rfl, hop, rfl⟩ := ht
  simp only [Op.store.injEq, true_and, and_true] at hop
  obtain ⟨rfl, rfl⟩ := hop
  -- the address is `cT`, the value `1`
  obtain ⟨cty, cμ, cu, hcv, hcell, hcu⟩ := hcj.1
  have hwa : wa = D.cw w := by
    rw [hcv] at hea; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea
    exact hea.2.symm
  subst hwa
  obtain ⟨a', hcT, hcTa, hcTo⟩ : ∃ a, (Q.C w).cT = wordLoc a ∧ wordAddr (Q.SR w).lbl (Q.C w).cS = some a ∧
      (Q.C w).cS.offset < (Q.SR w).lsize (Q.C w).cS.label := hC2.cT w
  have hlbl : D.lbl w = (Q.SR w).lbl := hC2.lbl w
  rw [hC1.cwv w, hlbl] at hva
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
  have he' : isa.exec t1.st = some (.store kr false (wordLoc a') 1 fun _ => .done s') := he
  -- facts shared by both outcomes
  have hcw' := hC1.cwv w
  have hnpT : ¬ (Q.C w).passT t1.st := by
    rw [hC1.pass w _ s1 h.pt1.1 (.inl hP)]; exact printPh_not_pass hP
  have hAt : AtStore (D.cw w) (Q.C w).cS th1 := ⟨ht₁, rfl, h.pt1.2.1, ⟨cty, cμ, cu, hcv, hcell, hcu⟩, hcw'⟩
  obtain ⟨hst, hc⟩ := stepOne_store_cases Arch.tso he' hso ho (X64HelloStep1Rt.prom_leH h)
  have hwi : D.Wi w o.thread.st ⟨wkUnpark, ("d", .unit, []) :: c₁.env, none⟩ [] := by rw [hst]; exact hX
  have hSa : ∀ vs, StorePh (D.cw w) (afterStore th1 vs []) := fun _ =>
    ⟨rfl, .inr (.inl rfl), X64WakeW1.envCJ_cons hcj _ _⟩
  have hpost : (Q.C w).passT o.thread.st :=
    (hC1.pass w _ (afterStore th1 th1.vs []) hwi (.inr (hSa _))).mpr (wPass_afterStore rfl _ _)
  obtain ⟨hT0, hS, hl⟩ := (cProt_iff _ _ _).mp h.prot
  have hs0 : s0.promises = [] := hx.sp0 w _ _ _ _ h.pt0
  have hb := (stepOne_bnd _ hso ho h.core.bnd1).1
  have hcov := stepOne_cohL _ hso ho h.core.cov1
  have hnp : (Q.P w).noProm o.thread.st → o.thread.prom = [] := fun hn => hC2.noProm w _ _ _ hn hco
  -- the worker's owned words: read as their values, none of them the flag word `cT = wordLoc a'`
  have hown1 : ExtRows.OwnOk (Q.own w 1 o.thread.st []) t.1.mem t1.prom := h.ownOk1 hown _ _
  have hout : ∀ L v, (L, v) ∈ Q.own w 1 o.thread.st [] → wordLoc a' ≠ L := fun L v hv e =>
    hown.cT w _ _ _ _ _ _ _ v h.core.mem (by rw [hcT, e]; exact hv)
  have hdisj : ∀ L v v', (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st s1.stack) 0 →
      (L, v') ∈ (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 o.thread.st []) 1 →
      False :=
    h.ownDisj1 hown _ _
  have hocov : ∀ L v, (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 o.thread.st []) 1 →
      (Q.P w).cov 1 L :=
    h.ownCov1 hown _ _
  have hpt1 : ∀ (vs : WeakMem.VState) (mem' : Memory) (sm' : WeakMem.Memory), o.thread.prom.Nodup →
      PT1h D w mem' sm' o.thread (afterStore th1 vs []) := fun vs _ _ hnd =>
    ⟨hwi, h.pt1.2.1, .inr (hSa vs), by simp [afterStore], fun k hk => by simp [afterStore] at hk, hnd⟩
  have hscS : ∀ (vs : WeakMem.VState), (∀ b, b ≠ (Q.C w).cS → vs.coh b = s1.vs.coh b) →
      ∀ (sm' : WeakMem.Memory), (∀ k m, sm'[k]? = some m → (Q.P w).frzS m.loc → k ≤ s1.vs.coh m.loc) →
      ∀ k m, sm'[k]? = some m → (Q.P w).frzS m.loc → k ≤ (afterStore th1 vs []).vs.coh m.loc := by
    intro vs hvo sm' hsc k m hk hz
    show k ≤ vs.coh m.loc
    rw [hvo m.loc (fun e => hC2.cSfrz w (e ▸ hz))]
    exact hsc k m hk hz
  have hpassS : ∀ (vs : WeakMem.VState), (Q.C w).passS (afterStore th1 vs []) := fun vs =>
    (PartsH.passS_iff (w := w) hC1 _).mpr (wPass_afterStore rfl vs [])
  -- the source's frame run to the store
  have hrun₁ : (helloS arch).Run s [] { s with ths := s.ths.set! 1 th1 } :=
    frameRun_run_source_i (P := srcPo 2 arch helloSrc) rfl (by decide) hr₁ h.s1_get rfl rfl h.pt1.2.1 rfl hex
      (h.certified_phase hC1 (fun hP' => absurd hP' (storePh_not_printPh hS₁ hcw')) (.inr hS₁) h.pt1.2.1 rfl rfl
        (fun hw => absurd hw (not_wPass_atStore hAt)))
  have hmid : ({ s with ths := s.ths.set! 1 th1 } : TermRun.Cfg).ths[1]? = some th1 :=
    getElem?_set!_self h.s1_get th1
  have hexm : SrcSem.mainExit { s with ths := s.ths.set! 1 th1 } = [] := by
    rw [mainExit_eq (c := s) (by show (s.ths.set! 1 th1)[0]? = s.ths[0]?; rw [h.ths]; rfl)]; exact hex
  have hset : ∀ th : TermRun.TTh, (s.ths.set! 1 th1).set! 1 th = #[s0, th] := fun th => by
    rw [set!_set!, h.ths]; rfl
  rcases hc with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
  · -- the fulfilment: `q` is the protocol's `Tc`, the source fulfils `kc`
    have hTq : (Q.SR w).T < q := (h.core.prom1 q hq).1
    obtain ⟨kc, hoc, -⟩ := hT0.tmsg q _ hg hTq hcT.symm
    subst hoc
    have hqtp : q ∈ tp := hT0.pass_prom hnpT q kc rfl
    have hkc1 : kc ∈ s1.promises := hS.prom_worker q kc rfl hqtp
    have hs1p : s1.promises = [kc] := X64WakeW1.eq_single_of_length h.pt1.2.2.2.1 hkc1
    have hkcsp : kc ∈ sp := (h.core.sp_prom kc).mpr (.inr hkc1)
    obtain ⟨-, m, hm', hml, hmv⟩ := hS.some_msg q kc rfl
    have hnpS : ¬ (Q.C w).passS s1 := fun hps => hnpT (hl.mpr hps)
    obtain ⟨hmv', hob⟩ := fulfil_ok hS hnpS hkcsp hm'
    rw [hC1.C w] at hmv' hob
    obtain ⟨vs, hstep, -, hvo⟩ := store_fulfil_src (P := srcPo 2 arch helloSrc) (p := helloSrc) rfl hmid hAt
      hs1p hm' hml hmv hmv' hob hexm
    have hrun : (helloS arch).Run s [] { s with ths := (s.ths.set! 1 th1).set! 1 (afterStore th1 vs []) } :=
      LRun.trans hrun₁
        (LRun.step (step := fun c es c' => ∃ i, (helloS arch).step i c es c') ⟨1, hstep⟩ (LRun.refl _))
    have hs' : ({ s with ths := (s.ths.set! 1 th1).set! 1 (afterStore th1 vs []) } : TermRun.Cfg).ths =
        #[s0, afterStore th1 vs []] := hset _
    obtain ⟨-, hts, -⟩ := hT0.some_msg q kc rfl
    have hq0 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) hTq
    have huniq : ∀ k2, ts k2 = some q → k2 = kc := fun k2 h2 =>
      X64WakeW1.MemRelP.ts_uniq h.core.mem hwf h.core.narrow h2 hts hq0
    have hqn : q ∉ tp.erase q := h.core.mem.tp_nodup.not_mem_erase
    have hnd := h.pt1.2.2.2.2.2
    rw [hm]
    rw [hm] at hb hcov
    refine ⟨_, hrun, post_frameH (ts' := ts) (tp' := tp.erase q) (sp' := sp.erase kc) hC1 h.th h.ths hs' h.preC
      h.pt0 (krW_of hC1 h.kr hwr h.th) h.core.T_le ⟨.inl rfl, .inl rfl⟩ ?_
      (hpt1 vs _ _ (by rw [hp]; exact hnd.erase q)) ?_ rfl⟩
    · refine X64WakeW1.Inv2Core.core1_mem h.core (by simp) (h.core.mem.fulfil hts huniq) ?_ ?_ ?_ hb ?_
        (hscS vs hvo s.mem h.core.scov1) (show ExtRows.OwnOk (Q.own w 1 o.thread.st []) _ _ by
          rw [hp]; exact X64WakeM0.ownOk_erase_out hown1 hg (hout · ·)) hdisj hocov ?_ hnp
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
          · rw [hp] at h1; exact hnd.not_mem_erase h1
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
      have hle : Tc ≤ t.1.mem.last := X64HelloStep1Rt.prom_leH h Tc hTc
      have hgq' : o.mem.get? Tc = some wq := by
        rw [hm, Scc.Sem.Memory.get?_append_le hle]; exact hgq
      have h1 := X64WakeW1.coh_lt_of_certOkC _ hco (by rw [hp]; exact hTc) hgq'
      have h2 := X64WakeW1.stepOne_store_append_coh Arch.tso he' hso ho hm
      rw [hlq, hcT] at h1
      have h3 : @LT.lt Nat instLTNat (o.thread.views.getCoh (wordLoc a')) Tc := h1
      have h4 : @LE.le Nat instLENat (t.1.mem.last + 1) (o.thread.views.getCoh (wordLoc a')) := h2
      omega
    have hs1p : s1.promises = [] := by
      cases hp1 : s1.promises with
      | nil => rfl
      | cons k ks =>
        obtain ⟨Tc, hoc⟩ := h.src_prom hC1 (k := k) (by rw [hp1]; exact List.mem_cons_self)
        cases hoc
    obtain ⟨vs, hstep, -, hvo⟩ := store_append_src (P := srcPo 2 arch helloSrc) (p := helloSrc) rfl hmid hAt
      hs1p hexm
    let mS : WeakMem.Msg :=
      ⟨(Q.C w).cS, .num 1, Promises.storeMview (wTh s1.vs (D.cw w)) (TermRun.dataE 1 one) [0] true⟩
    have hrun : (helloS arch).Run s []
        { s with mem := s.mem.push mS, ths := (s.ths.set! 1 th1).set! 1 (afterStore th1 vs []) } :=
      LRun.trans hrun₁
        (LRun.step (step := fun c es c' => ∃ i, (helloS arch).step i c es c') ⟨1, hstep⟩ (LRun.refl _))
    have hs' : ({ s with mem := s.mem.push mS, ths := (s.ths.set! 1 th1).set! 1 (afterStore th1 vs []) } :
        TermRun.Cfg).ths = #[s0, afterStore th1 vs []] := hset _
    have hfoot : (Q.P w).foot 1 (wordLoc a') := hcT ▸ hC2.cTfoot w
    have hnew : (Q.SR w).T < t.1.mem.last + 1 := Nat.lt_succ_of_le h.core.T_le
    have htpn : t.1.mem.last + 1 ∉ tp := fun htp => by
      have := (h.core.mem.tp_le _ htp).2
      omega
    have hspn : s.mem.size ∉ sp := fun hk => by
      have := h.core.mem.sp_lt _ hk
      omega
    have hmemR := h.core.mem.store (a := a') (v := 1) (tid := 1) (m := mS) hcTa hcTo ⟨by decide, rfl⟩ false
    simp only [Bool.false_eq_true, ite_false] at hmemR
    have hpl := X64HelloStep1Rt.prom_leH h
    rw [hm]
    rw [hm] at hb hcov
    refine ⟨_, hrun, post_frameH (ts' := fun k => if k = s.mem.size then some (t.1.mem.last + 1) else ts k)
      (tp' := tp) (sp' := sp) hC1 h.th h.ths hs' h.preC h.pt0 (krW_of hC1 h.kr hwr h.th) h.core.T_le
      ⟨.inr ⟨_, rfl, rfl, hfoot⟩, .inr ⟨mS, rfl, rfl⟩⟩ ?_ (hpt1 vs _ _ (by rw [hp]; exact h.pt1.2.2.2.2.2)) ?_ rfl⟩
    · refine core1_append h.core (by simp) rfl hfoot (.inr ⟨mS, rfl⟩) hmemR
        (fun k hk => by rw [hp]; exact h.core.tp_prom k hk) ?_ ?_ rfl (hcT ▸ hC2.cTin w)
        (show (1 : Val).toNat < 2 ^ 64 by decide)
        (hcT ▸ hx.Gc w) hb hcov (Inv2Rely.frzS_push h.core.frzS (hC2.cSfrz w))
        (Inv2Rely.scov_push h.core.scov0 (hC2.cSfrz w))
        (hscS vs hvo _ (Inv2Rely.scov_push h.core.scov1 (hC2.cSfrz w)))
        (show ExtRows.OwnOk (Q.own w 1 o.thread.st []) _ _ by
          rw [hp]; exact Inv2Rely.OwnOk.append_out hown1 (hout · ·)) hdisj hocov ?_ hnp
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

/-- info: 'Spike.Lib.X64HelloStep1St.post_storeH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_storeH

end Spike.Lib.X64HelloStep1St
