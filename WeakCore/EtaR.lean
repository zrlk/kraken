import WeakCore.EtaP
import WeakCore.EtaNC
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
/-! **EtaR**: the η lineage invariant `EtaInv` on the internal
RetPw-free layer N, and its preservation by promise steps, extern moves (E1) and thread steps (L4).

* Thread steps: non-publish terms through NLayer `tstepMF_stepBN` (its `PubWinT` premise is vacuous off publish
  terms) or the cap port `tstep_capBN`, publish terms through the shadow publish `pub_stepN` (EtaP).
* The per-step scope is W's `ScopeD`, obtained exactly as the existing ♭ chain obtains `ScopeAtB`
  (WinScope `scopeAtB_of`): from W's `RunScope` at the source by `TermCertScope.scopeD_of` and the ♭ copy of
  `scope_termV`, which reads only the `VarsOKB` component of `FInvB` (so the continuation, `ResumeBN`, is
  irrelevant).  No new scope predicate.
* Counts at `x`: NLayer's `CntX` export, under the oracle `¬ BufInitL th x`; `ExtB` by `Foot_extB`. -/
namespace CertWinProof
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat
  TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat
  TermOwnK3.Flat TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **The η lineage at `c`** (anchor `E0`): thread `i`'s N-typing env `E` extends the anchor, its counts at `x`
are at most the anchor's.  (The supply conjunct `∃ b, FreshSup P b E` was dropped: never consumed.) -/
def EtaInv (p : Prog) (k : Promises.Knobs) (arch : Arch) (E0 : TEnv) (i : Nat) (x : AllocLabel)
    (c : Cfg) : Prop :=
  ∃ th E, c.ths[i]? = some th ∧ ThInvEBN c.lbase c.n i p E th ∧ MemInvB (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    (gOf p k arch c i).boxFence = true ∧ ExtB E0 E ∧ E.ini x ≤ E0.ini x ∧ E.rini x ≤ E0.rini x ∧
    TyOKE (gOf p k arch c i) E ∧ RecFresh (gOf p k arch c i) i th.nalloc

/-! ### (L2) promise steps -/

theorem eta_prom {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel}
    {c : Cfg} {a : Address} {v : WeakMem.Val} {w : Ts} (hI : EtaInv p k arch E0 i x c) :
    EtaInv p k arch E0 i x (promise c i a v w) := by
  obtain ⟨th, E, hth, hT, hm, hb, hx, h4, h5, hTy, hRc⟩ := hI
  obtain ⟨-, h2, h3⟩ := promise_inv (a := a) (v := v) (w := w) hth
  exact ⟨_, E, h2, (by rw [show (promise c i a v w).lbase = c.lbase from congrArg G.lbase (gOf_promise (p := p) (k := k) (arch := arch)), promise_n]; exact hT), by rw [gOf_promise, h3]; exact MemInv_promStB hm, by rw [gOf_promise]; exact hb,
    hx, h4, h5, by rw [gOf_promise]; exact hTy, by rw [gOf_promise]; exact hRc⟩

/-! ### (E1) extern moves (ports of KLayer `ThInvRE_extB`/`ThInvRE_curB` to N, resource-free) -/

theorem ThInvEBN_ext {p : Prog} {E : TEnv} {th : TTh} {x : String} {n : ExtName} {a : At} {e : Expr}
    {rt : Ty} {ws rs : List Word} {i : Nat} {tr : List Event} {vv : VState} {pm : Option Ts} (hn : n ≠ .current)
    (hterm : th.term = .let_ x (.ext n a) e) (hev : evalAt th.env a = some (rt, ws)) (hrs : rs ∈ n.resultsL i ws tr)
    (hR : ThInvEBN glb gnum gi p E th) :
    ThInvEBN glb gnum gi p E { th with term := e, env := (x, n.sig.2, rs) :: th.env, vs := vv, permit := pm } := by
  obtain ⟨ρ, η, cx, hCE, hE, hT, htv, hi, hpw, hDy⟩ := hR
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | ext hu _ hsub hb =>
    have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
    have htv1 := use_TvOK hu htv
    have htv' := (bind_TvOK hb htv1.1 (TermTv.extSig_tb _ _) (TermTv.extSig_mg _)).1
    obtain ⟨hi1, rt1, ws1, hev1, hvr1, hl1⟩ := use_FInvB (bkG := False) hu hi
    rw [hev] at hev1; cases hev1
    obtain ⟨hz, hl⟩ := ext_resB (bkG := False) (σs := th.σs) hn (VR_subB (bkG := False) hi1.1 hsub _ _ hvr1)
      hl1.2.2.1 hrs
    refine ⟨ρ, η, c', hCE, hE, he, htv', bind_FInvB hb hi1 (VRR_VRB _ (RLink_ofB hE.2.1 hE.2.2) hz) hl, ?_, hDy.letW hterm rfl⟩
    show RetPwN th.σs th.stack c'.ret
    rw [hret]; exact hpw

theorem ThInvEBN_cur {p : Prog} {E : TEnv} {th : TTh} {x : String} {a : At} {e : Expr}
    {l : AllocLabel} (hterm : th.term = .let_ x (.ext .current a) e) (hs : E.sto l = some ⟨.unit, none⟩)
    (hp : E.pfr l = some 0) (hR : ThInvEBN glb gnum gi p E th) :
    ThInvEBN glb gnum gi p E { th with term := e, env := (x, .tid, [cst (.loc ⟨l, 0⟩ 0)]) :: th.env } := by
  obtain ⟨ρ, η, cx, hCE, hE, hT, htv, hi, hpw, hDy⟩ := hR
  subst hCE
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | ext hu _ hsub hb =>
    have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
    have htv1 := use_TvOK hu htv
    have htv' := (bind_TvOK hb htv1.1 (by simp [ExtName.sig, tb]) (by simp [ExtName.sig, mg])).1
    obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
    have hvr : (VRF False) ρ η .tid (shp .tid) [cst (.loc ⟨l, 0⟩ 0)] :=
      ⟨l, ⟨.unit, none⟩, rfl, hs, rfl, 0, hp, .inr (.inl fun _ _ => Nat.zero_le _)⟩
    have hlay : Lay th.σs .tid .tid [cst (.loc ⟨l, 0⟩ 0)] :=
      ⟨fun us h => by simp [accs] at h; subst h; rfl, by first | rfl | simp [etok, close, substTs, skel],
        by simp [wc, accs], trivial, by first | rfl | simp [etok, close, substTs, lyt]⟩
    refine ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hlay, ?_, hDy.letW hterm rfl⟩
    show RetPwN th.σs th.stack c'.ret
    rw [hret]; exact hpw

theorem eta_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel}
    {c c' : Cfg} (hI : EtaInv p k arch E0 i x c) (hs : c' ∈ extSteps c i) (hTA : TermTyped.TidAt i c E0) :
    EtaInv p k arch E0 i x c' := by
  obtain ⟨th, E, hth, hT, hm, hb, hx, h4, h5, hTy, hRc⟩ := hI
  rcases TermTyped.extSteps_res hs hth with ⟨x1, n1, a1, e1, rt1, ws1, rs1, hterm, hn1, hev1, hrs1, rfl⟩ |
      ⟨x1, a1, e1, lb, hterm, htl, rfl⟩
  · exact ⟨_, E, set_self hth, (by rw [extSteps_n hs]; exact ThInvEBN_ext hn1 hterm hev1 hrs1 hT), by rw [gOf_ext hs]; exact hm,
      by rw [gOf_ext hs]; exact hb, hx, h4, h5, by rw [gOf_ext hs]; exact hTy, by rw [gOf_ext hs]; exact hRc⟩
  · obtain ⟨hbs, hbp⟩ := TermTyped.Flat.tidBox_extB hx (hTA th hth lb htl)
    exact ⟨_, E, set_self (tr := c.trace) hth, (by rw [extSteps_n hs]; exact ThInvEBN_cur hterm hbs hbp hT), by rw [gOf_ext hs]; exact hm,
      by rw [gOf_ext hs]; exact hb, hx, h4, h5, by rw [gOf_ext hs]; exact hTy, by rw [gOf_ext hs]; exact hRc⟩

/-! ### (L4) thread steps -/

theorem eta_step {p : Prog} [ProgRetIall p] (hP : ProgT p) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {c c' : Cfg}
    (hrs : TermScope.RunScope c) (hI : EtaInv p k arch E0 i x c) (hs : c' ∈ threadSteps p k arch c i)
    (hc : Certified p k arch c' i) (hsx : E0.sto x ≠ none)
    (hnb : ∀ th, c.ths[i]? = some th → ¬ BufInitL th x) : EtaInv p k arch E0 i x c' := by
  obtain ⟨th, E, hth, ⟨ρ, η, cx, hCE, hE, hT, htv, hi, hRP, hDy⟩, hm, hbf, hx0, hini, hrini, hTy, hRc⟩ := hI
  subst hCE
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc
  rw [hth] at hth'
  cases hth'
  have hg := TermTyped.gOf_thread hs
  have hn : 0 < (gOf p k arch c i).n := Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth))
  have hsxE : (CE η).sto x ≠ none := fun h0 => by
    cases hc0 : E0.sto x with
    | none => exact hsx hc0
    | some cl =>
      have h1 := hx0.2.2.2.2.1 x cl hc0
      rw [h0] at h1; cases h1
  have hnd : isDone th = false := by
    cases hd : isDone th
    · rfl
    · rw [TermStep.tstep_done hd] at hr; cases hr
  have hns := TermTyped.not_spawnT_of_steps hth hs
  have hsD : ScopeD th.σs cx th.term := by
    have h := hrs i th hth
    exact TermCertScope.scopeD_of h.ok (TermScope.Flat.scope_termVB hT hi.2.1 h.ok h.env hns)
  have hnone : (CE η).sto (freshLabel (gOf p k arch c i).lbase (gOf p k arch c i).n (gOf p k arch c i).i th.nalloc) = none :=
    (hm.2.2.2.1.1 th.nalloc (Nat.le_refl _)).1
  have hsub := TermTyped.tysOf_thread hs hth e3 hRc
  have fin : ∀ E', ThInvEBN c.lbase c.n i p E' r.2.2 → MemInvB (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2) →
      ExtB (CE η) E' → E'.ini x ≤ (CE η).ini x → E'.rini x ≤ (CE η).rini x →
      TyOKE { gOf p k arch c i with tys := tysUpd (gOf p k arch c i).tys th r.2.2 } E' →
      RecFresh { gOf p k arch c i with tys := tysUpd (gOf p k arch c i).tys th r.2.2 } i r.2.2.nalloc →
      EtaInv p k arch E0 i x c' := by
    intro E' h1 h2 h3 h4 h5 h6 h7
    refine ⟨r.2.2, E', e3, (by rw [(threadSteps_lbase hs).1, threadSteps_n hs]; exact h1), ?_, by rw [hg]; exact hbf,
      Ext_transB hx0 h3, Nat.le_trans h4 hini, Nat.le_trans h5 hrini, ?_, ?_⟩
    · rw [hg, e1, e2, MemInvB_tys]; exact h2
    · rw [hg]; exact TyOKE_mono hsub h6
    · rw [hg]
      exact RecFresh_sub (g := { gOf p k arch c i with tys := tysUpd (gOf p k arch c i).tys th r.2.2 })
        (g' := { gOf p k arch c i with tys := tysOf c' }) hsub rfl rfl h7
  by_cases hpub : ∃ y a e, th.term = .let_ y (.publish a) e
  · obtain ⟨y, a, e, hterm⟩ := hpub
    have hpsc : PubScope cx a := TermOwnK4.pubScope_of (by rw [← hterm]; exact hsD)
    obtain ⟨-, hR⟩ := pub_stepN (g := gOf p k arch c i) (mem := c.mem) (pairs := c.pairs) hterm hP hT hi hE htv hm
      hpsc hRP hPS hDy
    obtain ⟨E1, h1, h2, h3⟩ := hR r hr
    have hk := tyOKE_tstepB (W := fun _ => True) hn hr EFoot_reflB hTy hRc
      (hnew_none hr hRc (fun _ _ _ _ h => by rw [hterm] at h; cases h))
    rcases h3 with rfl | ⟨lab, V, hl, rfl⟩
    · exact fin _ h1 h2 (Ext_reflB (Coh_CEB η) (CohR_CEB η)) (Nat.le_refl _) (Nat.le_refl _) hk.1 hk.2
    · exact fin _ h1 h2 (ext_shE η lab V) (Nat.le_refl _) (Nat.le_refl _) (TyOKE_stoD (shE_sto η lab V) hk.1) hk.2
  · have hnp : ∀ y a e, th.term ≠ .let_ y (.publish a) e := fun y a e h => hpub ⟨y, a, e, h⟩
    rcases hsD with hst | ⟨-, hcap⟩
    · by_cases hnw : ∃ x a T e, th.term = .let_ x (.new a T) e
      · obtain ⟨x1, a, T, e, hterm⟩ := hnw
        obtain ⟨-, hR⟩ := tstepM_newNCN (g := gOf p k arch c i) (mem := c.mem) (pairs := c.pairs) hterm
          (by rw [hterm] at hst; exact hst) hP hn hT hi hE htv hm hRP hPS hDy
        obtain ⟨E', hNC, -, ⟨hfoot, hcnt⟩, h1, h2⟩ := hR r hr
        have h1' := h1
        obtain ⟨ρ', η', cx', hCE', -⟩ := h1'
        subst hCE'
        have hext : ExtB (CE η) (CE η') := Foot_extB ⟨hfoot, fun l hl => fresh_blankB hm hl⟩
        obtain ⟨c4, c5⟩ := hcnt x hsxE (hnb th hth)
        have hk := tyOKE_tstepB hn hr hfoot hTy hRc
          (TermStep.hnew_of hr hRc (show DyFr (gOf p k arch c i).p annNew (progTgts (gOf p k arch c i).p) η th.σs th.term from hDy)
            (fun k => (hE.2.1 k).1) hNC)
        exact fin _ h1 h2 hext c4 c5 hk.1 hk.2
      · have hnn : ∀ x a T e, th.term ≠ .let_ x (.new a T) e := fun x a T e h => hnw ⟨x, a, T, e, h⟩
        obtain ⟨-, hR⟩ := tstepMF_stepBN (g := gOf p k arch c i) (mem := c.mem) (pairs := c.pairs) hP rfl hn hnd hst
          hT hi hE htv hm hbf (PAx_of_step hs hc hth) (fun _ _ _ _ _ _ h => absurd h (hnp _ _ _)) hRP hPS hSub hSig hTy
          (hDy := hDy)
        obtain ⟨E', ⟨hfoot, hcnt⟩, h1, h2⟩ := hR r hr hpa
        have h1' := h1
        obtain ⟨ρ', η', cx', hCE', -⟩ := h1'
        subst hCE'
        have hext : ExtB (CE η) (CE η') := Foot_extB ⟨hfoot, fun l hl => fresh_blankB hm hl⟩
        obtain ⟨c4, c5⟩ := hcnt x hsxE (hnb th hth)
        have hk := tyOKE_tstepB hn hr hfoot hTy hRc (hnew_none hr hRc hnn)
        exact fin _ h1 h2 hext c4 c5 hk.1 hk.2
    · obtain ⟨-, hR⟩ := tstep_capBN (g := gOf p k arch c i) (mem := c.mem) (pairs := c.pairs) hP hcap hT hi hE htv hDy
      obtain ⟨h1, hsm⟩ := hR r hr
      have hk := tyOKE_tstepB (W := fun _ => True) hn hr EFoot_reflB hTy hRc
        (fun c0 t hc0 _ => by rw [hnone] at hc0; cases hc0)
      exact fin _ h1 (MemInv_sameB hm hsm) (Ext_reflB (Coh_CEB η) (CohR_CEB η)) (Nat.le_refl _) (Nat.le_refl _)
        hk.1 hk.2

/-! ### The lineage along a certified solo run (the oracle `¬ BufInitL` at every certified source) -/

theorem eta_solo {p : Prog} [ProgRetIall p] (hP : ProgT p) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hps : TermScope.ProgScopeOK p = true) {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat}
    {x : AllocLabel} (hsx : E0.sto x ≠ none) {c c2 : Cfg} (h : Solo p k arch i c c2) :
    Certified p k arch c2 i → TermScope.RunScope c → TermTyped.TidAt i c E0 →
    (∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ∀ th, c0.ths[i]? = some th → ¬ BufInitL th x) →
    EtaInv p k arch E0 i x c → EtaInv p k arch E0 i x c2 := by
  induction h with
  | refl => exact fun _ _ _ _ hI => hI
  | thread hs hrest ih =>
    intro hc2 hrs hTA hO hI
    have hc' := certified_of_solo hrest hc2
    have hc := certified_of_solo (.thread hs hrest) hc2
    exact ih hc2 (TermCertScope.drf_thread hps hrs hs) (TermTyped.tidAt_thread hs hTA)
      (fun c0 h3 => hO c0 (.thread hs h3))
      (eta_step hP hPS hSub hSig hrs hI hs hc' hsx (hO _ (.refl _) hc))
  | prom a v w hw hrest ih =>
    intro hc2 hrs hTA hO hI
    exact ih hc2 (TermCertScope.drf_prom hrs) (TermTyped.tidAt_prom hTA) (fun c0 h3 => hO c0 (.prom a v w hw h3))
      (eta_prom hI)
  | ext hs hrest ih =>
    intro hc2 hrs hTA hO hI
    exact ih hc2 (TermCertScope.drf_ext hrs hs) (TermTyped.tidAt_solo (p := p) (k := k) (arch := arch) (.ext hs (.refl _)) hTA)
      (fun c0 h3 => hO c0 (.ext hs h3)) (eta_ext hI hs hTA)

end CertWinProof
