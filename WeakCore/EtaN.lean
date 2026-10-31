import WeakCore.EtaR
import WeakCore.PlantedHolder
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
/-! **EtaN**: NoHold at the adversarial typing `CE η` of a window publish,
from the η lineage (EtaR) seeded at `η` itself.

* `fulfil_siteN`: the site of a fulfilling write at the lineage env (NLayer `wrSiteA_okUBN`, on `ResumeBN`).
* `eta_fulfil`: an outstanding promise at `x` at the publish point is fulfilled at an initialised unit of a lineage
  env `E` with `ExtB (CE η) E` and counts at `x` at most `η`'s.
* `noHold_eta`: (b) by contradiction through `bfail_holder` (PreHolder), `bfail_pfr` (Eg's genuine frontier),
  the frontier lineage and `unseen_of_pinnedB`; (a)/(c) from (b) and `InitR` at `E`.

Named premises of `noHold_eta` beyond PubWinSAN's antecedents and the window: `hK` (ContE, from contE_f4),
`hO` (the oracle `¬ BufInitL` along the certified run), the holder's `hlab`/`hnp`,
`hsc` (W's `ScalIni Eg` clause, ♭ copy `ScalFlat.ScalIni`), `hbf` (boxFence at `c1`). -/
namespace CertWinProof
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat
  TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat
  TermOwnK3.Flat TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- ♭ form of `unseen_of_pinned` (same proof, `OwnHidPB`). -/
theorem unseen_of_pinnedB {E' η : TEnv} {mem : Memory} {vs : VState} {P : List Ts} {l : AllocLabel} {c : Cell}
    (hH : OwnHidPB E' mem vs P) (hs : E'.sto l = some c) (ho : c.owner = some E'.tid)
    (hi : E'.ini l = η.ini l) (hr : E'.rini l = η.rini l) (hb : ¬ (ZW E' l ∨ η.ini l ≤ η.rini l)) :
    ¬ E'.seen l := by
  have hlt : E'.rc l < E'.ini l := by
    unfold TEnv.rc; rw [hi, hr]
    have : ¬ η.ini l ≤ η.rini l := fun h => hb (Or.inr h)
    omega
  obtain ⟨-, -, hns, -⟩ := hH.2 l c hs ho hlt
  exact hns fun hz => hb (Or.inl hz)

/-- The published cell of a publish term exists at the N-typing env. -/
theorem pub_sto {p : Prog} {E : TEnv} {th : TTh} {y : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word}
    {ad : Address} (hT1 : ThInvEBN glb gnum gi p E th) (hterm : th.term = .let_ y (.publish a) e)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad 0]) : E.sto ad.label ≠ none := by
  obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, -⟩ := hT1
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  cases hop with
  | publish hu hsh hb =>
    obtain ⟨u, c₁, hu⟩ : ∃ u c₁, cx.use a = .ok (.ptr .own u, c₁) := ⟨_, _, hu⟩
    obtain ⟨-, lab, c, pw, μr, ru, hea', hpw, hsto, -⟩ := ownPtr_invB hu hi
    rw [hea] at hea'
    simp only [Option.some.injEq, Prod.mk.injEq] at hea'
    obtain ⟨-, rfl⟩ := hea'
    simp only [List.map, hpw, List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws
    subst hws
    show η.sto lab ≠ none
    rw [hsto]; exact Option.some_ne_none _
  | publishBuf hu hsh hb =>
    obtain ⟨n, k, u, c₁, hu⟩ : ∃ n k u c₁, cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) :=
      ⟨_, _, _, _, hu⟩
    obtain ⟨-, μr, nr, ur, ψ, wsb, hea', hvb, -⟩ := ownBuf_invB (bkG := False) hu hi
    rw [hea] at hea'
    simp only [Option.some.injEq, Prod.mk.injEq] at hea'
    obtain ⟨-, rfl⟩ := hea'
    simp only [VRF, VRb2] at hvb
    obtain ⟨hv, -⟩ := hvb
    rcases hv with ⟨hnull, -, -⟩ | ⟨ad', c, U, hws', hsto, -⟩
    · rw [hnull] at hws; simp at hws
    · rw [hws'] at hws
      simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws
      subst hws
      show η.sto ad'.label ≠ none
      rw [hsto]; exact Option.some_ne_none _

/-- **The site of a fulfilling write** (N form of WinPubSplit `fulfil_siteB`, at the η-lineage env). -/
theorem fulfil_siteN {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat}
    {x : AllocLabel} {c c' : Cfg} {th : TTh} {t : Ts} {m : Msg}
    (hth : c.ths[i]? = some th) (hrs : TermScope.RunScope c) (hvI : TermViewInv.ViewInv c)
    (hI : EtaInv p k arch E0 i x c) (hs : c' ∈ threadSteps p k arch c i) (hnb : ¬ BufInitL th x)
    (hsx : E0.sto x ≠ none)
    (ht : t ∈ th.promises) (hn : t ∉ TermFul.promsOf c' i) (hm : c.mem[t]? = some m) (hl : m.loc.label = x) :
    ∃ E, MemInvB (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧ ExtB E0 E ∧
      E.ini x ≤ E0.ini x ∧ E.rini x ≤ E0.rini x ∧
      ∃ cl, E.sto x = some cl ∧ InitR E cl x m.loc.offset ∧
        (InitRr E cl x m.loc.offset ∨ (∀ f, E.pfr x = some f → f < t) ∨ E.seen x) := by
  obtain ⟨th1, E, hth1, ⟨ρ, η, cx, hCE, hE, hT, htv, hFI, -⟩, hmi, -, hx0, hini, hrini, -⟩ := hI
  rw [hth] at hth1
  cases hth1
  subst hCE
  have hsxE : (CE η).sto x ≠ none := fun h0 => by
    cases hc0 : E0.sto x with
    | none => exact hsx hc0
    | some cl =>
      have h1 := hx0.2.2.2.2.1 x cl hc0
      rw [h0] at h1; cases h1
  have hns := TermTyped.not_spawnT_of_steps hth hs
  have hscD : ScopeD th.σs cx th.term := by
    have h := hrs i th hth
    exact TermCertScope.scopeD_of h.ok (TermScope.Flat.scope_termVB hT hFI.2.1 h.ok h.env hns)
  have hvr := TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI (.refl _) hth
  obtain ⟨th', r, hth', hr, e1, e2, e3, -⟩ := threadSteps_inv hs
  rw [hth] at hth'
  cases hth'
  have hW := TermWrSiteA.Flat.wrSiteA_okUBN hE hT htv hFI hmi hscD hvr hr
  have hn' : t ∉ r.2.2.promises := by rwa [promsOf_some e3] at hn
  have hrm : r.1[t]? = some m := (tstep_grow hr).1 t m hm
  refine ⟨CE η, hmi, hx0, hini, hrini, ?_⟩
  rcases hW t m hn' hrm with ⟨hnp, -⟩ | hfr | ⟨cl, hcl, hIR, hor⟩ |
      ⟨x1, bb, ib, v, e, hterm, rt, w, ad, rti, wi, n, cl, hbb, hw, -, -, hadl, -, -⟩
  · exact absurd ht hnp
  · exfalso
    obtain ⟨j, hj, -, hjl⟩ := hfr
    have := (hmi.2.2.2.1.1 j hj).1
    rw [← hjl, hl] at this
    exact hsxE this
  · rw [hl] at hcl hIR hor
    refine ⟨cl, hcl, hIR, ?_⟩
    rcases hor with h | h | h | h
    · exact Or.inl h
    · exfalso
      have := hmi.2.2.1 t ht
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le this h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact absurd ⟨x1, bb, ib, v, e, rt, [w], ad, hterm, hbb, by simp [hw], hadl.trans hl⟩ hnb

/-- **(L5) The lineage at the fulfilment**: an outstanding promise `t` at `x` at the publish point `c1` is
fulfilled, along the certificate, at an initialised unit of a lineage env. -/
theorem eta_fulfil {p : Prog} [ProgRetIall p] (hP : ProgT p) (hPS : PwSkel) (hSub : PwSubS)
    (hSig : PwSig) (hps : TermScope.ProgScopeOK p = true) {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat}
    {x : AllocLabel} {c1 : Cfg} {th1 : TTh} {t : Ts} {m : Msg} (hsx : E0.sto x ≠ none)
    (hc1 : Certified p k arch c1 i) (hth1 : c1.ths[i]? = some th1) (hrs : TermScope.RunScope c1)
    (hvI : TermViewInv.ViewInv c1) (hTA : TermTyped.TidAt i c1 E0)
    (hO : ∀ c0, Solo p k arch i c1 c0 → Certified p k arch c0 i → ∀ th, c0.ths[i]? = some th → ¬ BufInitL th x)
    (hI : EtaInv p k arch E0 i x c1)
    (ht : t ∈ th1.promises) (hm : c1.mem[t]? = some m) (hl : m.loc.label = x) :
    ∃ E, ExtB E0 E ∧ E.ini x ≤ E0.ini x ∧ E.rini x ≤ E0.rini x ∧ (∃ g s, MemInvB g E s) ∧
      ∃ cl, E.sto x = some cl ∧ InitR E cl x m.loc.offset ∧
        (InitRr E cl x m.loc.offset ∨ (∀ f, E.pfr x = some f → f < t) ∨ E.seen x) := by
  have hpw : PWF c1 i := by
    obtain ⟨th, E, hth, -, hmi, -⟩ := hI
    rw [hth1] at hth
    cases hth
    refine ⟨fun q hq => Nat.lt_of_succ_lt (hmi.1.2.2 q hq), fun t ht => ?_⟩
    rw [promsOf_some hth1] at ht
    exact ⟨MemInv_promLtB hmi t ht, MemInv_nopairB hmi t ht⟩
  obtain ⟨c', hs, hnp⟩ := hc1
  have hn' : t ∉ TermFul.promsOf c' i := by rw [noPromises_nil hnp]; exact List.not_mem_nil
  obtain ⟨m', hm', c1a, c2, th1a, hs1, hst, hs4, hth1a, hm1a, ht1a, hn2, -, -, -⟩ :=
    solo_fulfil hs hpw t (by rw [promsOf_some hth1]; exact ht) hn'
  rw [hm] at hm'
  cases hm'
  have hc1a : Certified p k arch c1a i := ⟨c', .thread hst hs4, hnp⟩
  have hIa := eta_solo hP hPS hSub hSig hps hsx hs1 hc1a hrs hTA hO hI
  obtain ⟨E, hmE, h1, h2, h3, h4⟩ := fulfil_siteN hth1a (TermCertScope.solo_drf hps hs1 hrs)
    (TermViewInv.viewInv_solo hvI hs1) hIa hst (hO c1a hs1 hc1a th1a hth1a) hsx ht1a hn2 hm1a hl
  exact ⟨E, h1, h2, h3, ⟨_, _, hmE⟩, h4⟩

/-- Eg's genuine frontier when (b) fails at an anchored typing (the first half of `bfail_holder`). -/
theorem bfail_pfr {g : G} {Eg : GEnv} {c : Cfg} {i : Nat} {th : TTh} {S : AllocLabel → Prop} {η : TEnv}
    {l : AllocLabel} (hm0 : MemInv g (Cut Eg i S) (stOf c.mem c.pairs th))
    (hExt : Ext (Cut Eg i S) (CE η)) (hA : IniAnch (Cut Eg i S) (CE η)) (hsn : η.sto l ≠ none)
    (hlab : (∃ cl0, Eg.sto l = some cl0 ∧ cl0.owner = some i) ∨ Eg.ini l = 0)
    (hb : ¬ (ZW (CE η) l ∨ η.ini l ≤ η.rini l)) :
    ∃ cl0 F, cl0.owner = some i ∧ η.sto l = some cl0 ∧ Eg.pfr l = some F := by
  have hnb : ¬ η.ini l ≤ η.rini l := fun h => hb (Or.inr h)
  have hdis : ¬ Eg.ini l ≤ Eg.rini l := fun hle => hnb (DebtG3.b_of_anchor_le hExt hA hsn hle)
  obtain ⟨cl0, hEg, ho0⟩ : ∃ cl0, Eg.sto l = some cl0 ∧ cl0.owner = some i := by
    rcases hlab with h | h
    · exact h
    · exact absurd (by rw [h]; exact Nat.zero_le _) hdis
  have hcut : (Cut Eg i S).sto l = some cl0 := DebtG3.cutSto_own hEg ho0
  have hηs : η.sto l = some cl0 := hExt.2.2.2.2.1 l cl0 hcut
  obtain ⟨F, hF⟩ : ∃ F, Eg.pfr l = some F := by
    cases hq : Eg.pfr l with
    | some F => exact ⟨F, rfl⟩
    | none =>
      have hOH := hm0.2.2.2.2.2.1.2 l cl0 hcut ho0
      have : ¬ (Cut Eg i S).rc l < (Cut Eg i S).ini l := fun hlt => by
        obtain ⟨f, hf, -⟩ := hOH hlt
        simp only [Cut_pfr] at hf; rw [hq] at hf; cases hf
      exact absurd (by unfold TEnv.rc at this; simp only [Cut_ini, Cut_rini] at this; omega) hdis
  exact ⟨cl0, F, ho0, hηs, hF⟩

/-- **(L6) NoHold at the adversarial typing of a window publish.** -/
theorem noHold_eta {p : Prog} [ProgRetIall p] (hP : ProgT p) (hPS : PwSkel) (hSub : PwSubS)
    (hSig : PwSig) (hps : TermScope.ProgScopeOK p = true) {k : Promises.Knobs} {arch : Arch} {Eg : GEnv}
    {S : AllocLabel → Prop} {i : Nat} {c c1 : Cfg} {th th1 : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {y : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word} {ad : Address}
    (hth : c.ths[i]? = some th) (hsolo : Solo p k arch i c c1) (hc1 : Certified p k arch c1 i)
    (hth1 : c1.ths[i]? = some th1)
    (hrs : TermScope.RunScope c) (hvI : TermViewInv.ViewInv c) (hTA : TermTyped.TidAt i c (Cut Eg i S))
    (hPH : TermPredHold.PredHoldG Eg c) (hPT : TermMain.PromTyAOK Eg c)
    (hm0 : MemInv (gOf p k arch c i) (Cut Eg i S) (stOf c.mem c.pairs th))
    (hE : EnvOK p η) (hT : Typed p cx th1.term) (htv : TvOK cx)
    (hF : FInv ρ η th1.σs (Resume p th1.stack) cx th1.env)
    (hm : MemInv (gOf p k arch c1 i) (CE η) (stOf c1.mem c1.pairs th1))
    (hExt : Ext (Cut Eg i S) (CE η)) (hA : IniAnch (Cut Eg i S) (CE η))
    (hR : RiniMem (Cut Eg i S) (CE η) (stOf c1.mem c1.pairs th1))
    (hterm : th1.term = .let_ y (.publish a) e) (hea : evalAt th1.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) (hns : ¬ (CE η).seen ad.label)
    (hK : ContE c1.lbase c1.n i p th1 (CE η))
    (hbf : (gOf p k arch c1 i).boxFence = true)
    (hO : ∀ c0, Solo p k arch i c1 c0 → Certified p k arch c0 i → ∀ th, c0.ths[i]? = some th →
      ¬ BufInitL th ad.label)
    (hlab : (∃ cl0, Eg.sto ad.label = some cl0 ∧ cl0.owner = some i) ∨ Eg.ini ad.label = 0)
    (hnp : ¬ Eg.pubd ad.label)
    (hsc : ScalFlat.ScalIni Eg)
    (hTy : TyOKE (gOf p k arch c1 i) (CE η)) (hDy : DyFr p annNew (progTgts p) η th1.σs th1.term)
    (hRc : RecFresh (gOf p k arch c1 i) i th1.nalloc) :
    NoHold (CE η) (stOf c1.mem c1.pairs th1) ad.label := by
  have hT1 : ThInvEBN c1.lbase c1.n i p (CE η) th1 := eta_seed hK hE hT htv hF hDy
  have hsx : (CE η).sto ad.label ≠ none := pub_sto hT1 hterm hea hws
  have hI1 : EtaInv p k arch (CE η) i ad.label c1 :=
    ⟨th1, CE η, hth1, hT1, FlatAnchor.MemInv_B hm, hbf, Ext_reflB (Coh_CEB η) (CohR_CEB η), Nat.le_refl _,
      Nat.le_refl _, hTy, hRc⟩
  have hrs1 := TermCertScope.solo_drf hps hsolo hrs
  have hvI1 := TermViewInv.viewInv_solo hvI hsolo
  have hTA1 : TermTyped.TidAt i c1 (CE η) := TermTyped.tidAt_mono hExt (TermTyped.tidAt_solo hsolo hTA)
  have fulfil := fun {t : Ts} {m : Msg} (ht : t ∈ th1.promises) (hm : c1.mem[t]? = some m)
      (hl : m.loc.label = ad.label) =>
    eta_fulfil hP hPS hSub hSig hps hsx hc1 hth1 hrs1 hvI1 hTA1 hO hI1 ht hm hl
  -- pinned counts and cell at a lineage env
  have pin : ∀ E : TEnv, ExtB (CE η) E → E.ini ad.label ≤ (CE η).ini ad.label →
      E.rini ad.label ≤ (CE η).rini ad.label →
      E.ini ad.label = η.ini ad.label ∧ E.rini ad.label = η.rini ad.label ∧
        ∀ c, η.sto ad.label = some c → E.sto ad.label = some c := fun E hX h1 h2 =>
    ⟨Nat.le_antisymm h1 (hX.2.2.2.2.2.1 ad.label), Nat.le_antisymm h2 (hX.rini ad.label),
      fun c hc => hX.2.2.2.2.1 ad.label c hc⟩
  -- (b)
  have hB : ZW (CE η) ad.label ∨ η.ini ad.label ≤ η.rini ad.label := Classical.byContradiction fun hb => by
    obtain ⟨cl, hcl⟩ : ∃ cl, η.sto ad.label = some cl := by
      cases hq : η.sto ad.label with
      | none => exact absurd hq hsx
      | some cl => exact ⟨cl, rfl⟩
    obtain ⟨h, a', m', hal, -, hout, hm1, hml, hhF, hniw⟩ :=
      DebtG3.bfail_holder hPH hPT hth hm0 hsolo hExt hA hR hcl hns hlab hnp hsc hb
    obtain ⟨cl0, F, ho0, hηs, hF⟩ := bfail_pfr hm0 hExt hA hsx hlab hb
    have ho : cl.owner = some i := by rw [hcl] at hηs; cases hηs; exact ho0
    obtain ⟨E, hX, hi, hr, ⟨g', s', hmE⟩, clE, hsE, -, hor⟩ := fulfil hout hm1 (by rw [hml, hal])
    obtain ⟨hiE, hrE, hstE⟩ := pin E hX hi hr
    have hcc : clE = cl := Option.some.inj (hsE.symm.trans (hstE cl hcl))
    rw [hcc] at hor hsE
    rcases hor with hr' | hf' | hseen
    · apply hniw
      intro c N e us hc hty hus
      rw [hal] at hc
      have hc' : c = cl := Option.some.inj (hc.symm.trans hcl)
      rw [hc'] at hty
      have h1 := hr' N e us hty hus
      have hrc : E.rc ad.label = (CE η).rc ad.label := by
        unfold TEnv.rc; rw [hiE, hrE]; rfl
      rw [hal, ← hrc, ← hml]
      exact h1
    · have hFc : (CE η).pfr ad.label = some F := hExt.2.2.2.2.2.2.1 ad.label F (by simpa only [Cut_pfr] using hF)
      have hFE : E.pfr ad.label = some F := hX.2.2.2.2.2.2.1 ad.label F hFc
      have h1 := hf' F hFE
      have h2 := hhF F hF
      exact absurd (Nat.lt_of_lt_of_le h1 h2) (Nat.lt_irrefl _)
    · have hzw : ¬ (ZW E ad.label ∨ η.ini ad.label ≤ η.rini ad.label) := by
        rintro (hz | hz)
        · exact hb (Or.inl ((ZW.stoAt (E := CE η) (E' := E) (by rw [hsE]; exact hcl.symm)).1 hz))
        · exact hb (Or.inr hz)
      have hown : cl.owner = some E.tid := by
        rw [ho, hX.2.2.2.1, hExt.2.2.2.1]; rfl
      exact unseen_of_pinnedB hmE.2.2.2.2.2.1 hsE hown hiE hrE hzw hseen
  -- no HoldW at x
  have hH : ∀ f, ¬ HoldW (CE η) (stOf c1.mem c1.pairs th1) ad.label f := by
    rintro f ⟨t, ht, m, hm1, hl, -, -, hniw⟩
    obtain ⟨E, hX, hi, hr, -, cl, hsE, hIR, -⟩ := fulfil ht hm1 hl
    obtain ⟨hiE, hrE, hstE⟩ := pin E hX hi hr
    apply hniw
    intro c N e us hc hty hus
    rw [hl] at hc
    have hcc : cl = c := Option.some.inj (hsE.symm.trans (hstE c hc))
    rw [hcc] at hIR
    have h1 := hIR N e us hty hus
    rw [hl]
    rcases hB with ⟨c', N', e', us', hc', hty', hus', h0⟩ | hle
    · rw [hc] at hc'
      cases hc'
      rw [hty] at hty'
      cases hty'
      rw [hus] at hus'
      cases hus'
      rw [h0] at h1
      simp at h1
    · have hrc : (CE η).rc ad.label = η.ini ad.label := by
        unfold TEnv.rc; exact Nat.min_eq_left hle
      rw [hrc, ← hiE]
      exact h1
  exact ⟨fun f _ _ => hH f, hB, fun _ u => hH u⟩

end CertWinProof
