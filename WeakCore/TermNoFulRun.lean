import WeakCore.TermPtrKey
import WeakCore.TermFootNG
import WeakCore.TermFootBP0
import WeakCore.TermPtrRtsThr
import WeakCore.TermK2aLd

/-! # TermNoFulRun (the v3c `NoFulPlRun` run, ported to K-2a v3d on D-B)

`NoFulPlRunGL` / `NFInv` / `nfInv_prom` / `nfInv_thread` / `nfInv_run` / `noFulPlRunGL_of`: from
`stmt_v3c/TermPtrKey.lean` L427–L743 (deleted as dead code in the D-B cleanup), ported to the v3d
binder list of `PtrRtsThreadGL`: `NFInv` also carries the cell of `a`, its frontier, `E.box a = none` and
`BoxSep` at `tmin` (kept here along thread and promise steps); fresh labels are not `a`.  One staged
input (a named Prop, hypothesis of `noFulPlRunGL_of` only):
* `FootNCB p`: the `FootNC` with clause (1) of `FootBP` (`FootB1`) on the witness.
The return-link fact of v3d is `ThInvE`'s `RetPw`.
-/

namespace TermPtrKey
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermBal TermOwnKey TermOwnPub
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)


section NoFulRun
open TermCert TermGlob TermTyped

/-- (staged) **`FootNC` with `FootB1`** on the witness: the global resource-free footprint stepper
with clause (1) of `TermFootBP0.FootBP`. -/
def FootNCB (p : Prog) : Prop :=
  ∀ {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p], ProgT p → g.p = p → 0 < g.n → isDone th = false →
    ScopeD th.σs cx th.term → Typed p cx th.term → FInv ρ η th.σs (Resume p th.stack) cx th.env →
    EnvOK p η → TvOK cx → MemInv g (CE η) (stOf mem pairs th) → g.boxFence = true →
    PAx g mem pairs th → PubWinT (CE η) (stOf mem pairs th) th →
    (∀ l, BufInitOn th l → ¬ g.zf l) → (∀ l, TermOwnG0Defs.PubAt th l → g.pf l) → RetPw th.σs th.stack cx.ret →
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧
        (∀ l, TermOwnG0Defs.PubAt th l → E'.pfr l ≠ none) ∧ TermFootNC.FootNCE (CE η) E' r ∧
        TermFootBP0.FootB1 g th.nalloc th.env r E' ∧ TermTyped.BumpIf th E'

/-- `NoFulPlRun` with `ThLbl` at the start, the box fence, the start's fresh labels
outside `sto` and `StoClo` of the start environment (the bridge's `StoClo_Cut`); (v3c)
every cell of `sto` laid out. -/
def NoFulPlRunGL (p : Prog) (k : Promises.Knobs) (arch : Arch) : Prop :=
  ∀ (j : Nat) (a : AllocLabel) (c1 : Cfg) (th1 : TTh) (E1 : TEnv) (sto : TermPtrRts.Sto) (t : Ts),
    k.storeDepRts = true → (∀ l c, E1.sto l = some c → sto l = some c) →
    (∀ c0, Solo p k arch j c1 c0 → Certified p k arch c0 j → ScopeAt p j c0) → TermViewInv.ViewInv c1 →
    ∀ Eu Ea : TEnv, (∀ c0, Solo p k arch j c1 c0 → Certified p k arch c0 j → NoHoldPubA p k arch Eu Ea j c0) →
    AnchR Eu Ea E1 (stOf c1.mem c1.pairs th1) → Ext Ea E1 →
    c1.ths[j]? = some th1 → ThInvE p E1 th1 → MemInv (gOf p k arch c1 j) E1 (stOf c1.mem c1.pairs th1) →
    TermPtrRts.PtrRtsE sto (stOf c1.mem c1.pairs th1) th1 a →
    TermPtrRts.tminOf sto (stOf c1.mem c1.pairs th1) a = some t →
    c1.boxFence = true → (∀ q, th1.nalloc ≤ q → sto (freshLabel c1.lbase c1.n j q) = none) →
    TermPtrRts.ThLbl { pfr := E1.pfr, box := E1.box } th1 → StoClo E1 →
    TermScope.ProgScopeOK p = true → TermScope.ThScope th1 →
    (∀ t', TermPtrRts.tminOf sto (stOf c1.mem c1.pairs th1) a = some t' →
      TermPtrRts.MemRtsC sto t' a c1.mem c1.pairs th1.promises) →
    TermPtrRts.GranuleWP sto c1.mem c1.pairs th1.promises → (∀ l cl, sto l = some cl → LayT cl.ty) →
    (∃ cl, E1.sto a = some cl) → E1.pfr a ≠ none → E1.box a = none →
    (∀ t', TermPtrRts.tminOf sto (stOf c1.mem c1.pairs th1) a = some t' → TermPtrRts.BoxSep E1 t' a c1.mem) →
    ∀ c2 th2, TermOwnG0Defs.SoloNP p k arch j a c1 c2 → Certified p k arch c2 j → c2.ths[j]? = some th2 →
      t ∈ th2.promises

/-- The invariant carried along the owner's solo run (proof-local). -/
def NFInv (p : Prog) (k : Promises.Knobs) (arch : Arch) (j : Nat) (a : AllocLabel) (t : Ts) (Eu Ea : TEnv) (c : Cfg) : Prop :=
  ∃ th E S, c.ths[j]? = some th ∧ ThInvE p E th ∧ MemInv (gOf p k arch c j) E (stOf c.mem c.pairs th) ∧
    (∀ l cl, E.sto l = some cl → S l = some cl) ∧ TermPtrRts.PtrRtsE S (stOf c.mem c.pairs th) th a ∧
    TermPtrRts.tminOf S (stOf c.mem c.pairs th) a = some t ∧ c.boxFence = true ∧
    (∀ q, th.nalloc ≤ q → S (freshLabel c.lbase c.n j q) = none) ∧
    TermPtrRts.ThLbl { pfr := E.pfr, box := E.box } th ∧ StoClo E ∧ TermScope.ThScope th ∧
    (∀ t', TermPtrRts.tminOf S (stOf c.mem c.pairs th) a = some t' →
      TermPtrRts.MemRtsC S t' a c.mem c.pairs th.promises) ∧
    TermPtrRts.GranuleWP S c.mem c.pairs th.promises ∧ (∀ l cl, S l = some cl → LayT cl.ty) ∧
    (∃ cl, E.sto a = some cl) ∧ E.pfr a ≠ none ∧ E.box a = none ∧
    (∀ t', TermPtrRts.tminOf S (stOf c.mem c.pairs th) a = some t' → TermPtrRts.BoxSep E t' a c.mem) ∧
    AnchR Eu Ea E (stOf c.mem c.pairs th) ∧ Ext Ea E

theorem nfInv_prom {p : Prog} {k : Promises.Knobs} {arch : Arch} {j : Nat} {a : AllocLabel} {t : Ts} {Eu Ea : TEnv} {c : Cfg}
    {ad : Address} {v : WeakMem.Val} {w : Ts} (hJ : NFInv p k arch j a t Eu Ea c) :
    NFInv p k arch j a t Eu Ea (promise c j ad v w) := by
  obtain ⟨th, E, S, hth, hE, hm, hES, hR, ht, hbf, hfr, hL, hSC, hD, hC, hG, hLay, hsa, hpa0, hba, hBS, hA, hXa⟩ := hJ
  have e := promise_inv (a := ad) (v := v) (w := w) hth
  have hlt : ∀ u ∈ th.promises, u < c.mem.size := hm.2.2.1
  have htm : TermPtrRts.tminOf S (promSt (stOf c.mem c.pairs th) ad v w) a = some t :=
    TermPtrStab.tminOf_grow rfl hlt
      (fun u hu => TermPtrRts.edgeB_congr rfl (TermPtrStab.push_get (hlt u hu))) ht
  have hbf' : (promise c j ad v w).boxFence = c.boxFence := by unfold promise; split <;> rfl
  have hlb : (promise c j ad v w).lbase = c.lbase := by unfold promise; split <;> rfl
  refine ⟨{ th with promises := th.promises ++ [c.mem.size] }, E, S, e.2.1, hE, ?_, hES, ?_, ?_,
    hbf'.trans hbf, ?_, hL, hSC, ⟨hD.ok, hD.σs, hD.env, hD.stk⟩, ?_, ?_, ?_, hsa, hpa0, hba, ?_, anchR_prom hth hA, hXa⟩
  · rw [TermTyped.gOf_promise, e.2.2]; exact MemInv_promSt hm
  · rw [e.2.2]
    intro t' ht'
    rw [htm] at ht'
    cases ht'
    obtain ⟨hM, hRt⟩ := hR t ht
    refine ⟨fun u m hu hE0 hnp => ?_, hRt⟩
    have hne : u ≠ c.mem.size := fun h => hnp (List.mem_append_right _ (List.mem_singleton.2 h))
    exact hM u m (TermPtrStab.push_get_ne hu hne) hE0 (fun h => hnp (List.mem_append_left _ h))
  · rw [e.2.2]; exact htm
  · rw [hlb, TermStep.promise_n]; exact hfr
  · intro t' ht'
    rw [e.2.2, htm] at ht'
    cases ht'
    rw [e.1]
    intro u m cl hu hnp hcl hn hslot
    have hne : u ≠ c.mem.size := fun h => hnp (List.mem_append_right _ (List.mem_singleton.2 h))
    have hu0 := TermPtrStab.push_get_ne hu hne
    refine hC t ht u m cl hu0 (fun h => hnp (List.mem_append_left _ h)) hcl hn ?_
    rcases hslot with ⟨hv, hc⟩ | ⟨v, m0, hv, hvp, hm0, hl, hc⟩
    · exact .inl ⟨hv, hc⟩
    · refine .inr ⟨v, m0, hv, hvp, ?_, hl, hc⟩
      have hvne : v ≠ c.mem.size := by
        intro h
        have h3 : v + 1 < c.mem.size := hv ▸ (Array.getElem?_eq_some_iff.1 hu0).1
        rw [h] at h3
        exact Nat.lt_irrefl _ (Nat.lt_of_succ_lt h3)
      exact TermPtrStab.push_get_ne hm0 hvne
  · rw [e.1]; exact TermGranW.granuleWP_promise hG
  · exact hLay
  · intro t' ht'
    rw [e.2.2, htm] at ht'
    cases ht'
    intro l B hB o w0 hw hN f hf
    rcases hBS t ht l B hB o w0 hw hN f hf with h | h
    · exact .inl h
    · refine .inr fun u m hu hl hv => ?_
      have htl : t < c.mem.size := hlt t (TermPtrRts.tminOf_spec ht).1
      rw [e.1] at hu
      by_cases hue : u = c.mem.size
      · rw [hue]; exact Nat.le_of_lt htl
      · exact h u m (TermPtrStab.push_get_ne hu hue) hl hv

theorem nfInv_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {j : Nat} {a : AllocLabel} {t : Ts}
    {c c' : Cfg} {Eu Ea : TEnv} [ProgRetIall p] [WrIniC] (hP : ProgT p) (hK : TermPtrRts.PtrRtsThreadGL p) (hFN : FootNCB p)
    (hk : k.storeDepRts = true)
    (hps : TermScope.ProgScopeOK p = true) (hJ : NFInv p k arch j a t Eu Ea c) (hs : c' ∈ threadSteps p k arch c j)
    (hnp : ∀ th, c.ths[j]? = some th → ¬ TermOwnG0Defs.PubAt th a) (hc' : Certified p k arch c' j)
    (hsc : ScopeAt p j c) (hwin : NoHoldPubA p k arch Eu Ea j c) (hvI : TermViewInv.ViewInv c)
    (hscR : ∀ c0, Solo p k arch j c' c0 → Certified p k arch c0 j → ScopeAt p j c0)
    (hwinR : ∀ c0, Solo p k arch j c' c0 → Certified p k arch c0 j → NoHoldPubA p k arch Eu Ea j c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    NFInv p k arch j a t Eu Ea c' := by
  classical
  obtain ⟨th, E, S, hth, hE, hm, hES, hR, ht, hbf, hfr, hL, hSC, hD, hC, hG, hLay, hsa, hpa0, hba, hBS, hA, hXa⟩ := hJ
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc'
  rw [hth] at hth'
  cases hth'
  obtain ⟨-, -, -, -, -, -, -, hsz⟩ := TermFul.threadSteps_inv hs
  have hlb := threadSteps_lbase hs
  obtain ⟨ρ, η, cx, hCE, hEO, hT, htv, hFI, hrp⟩ := id hE
  subst hCE
  have hn : 0 < (gOf p k arch c j).n := by
    show 0 < c.n
    rcases Nat.lt_or_ge j c.ths.size with h1 | h1
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n h1)
    · simp [h1] at hth
  have hsc0 := hsc th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hEO hT htv hFI
  have hw0 := hwin th hth ρ η cx hEO hT htv hFI hm hXa hA.1 hA.2.2.1
  have hpx := PAx_of_step hs hc' hth
  obtain ⟨E', hF, hX, hE', hm', hPf, ⟨hNC0, hNC40⟩, hB1, hBump⟩ := (hFN hP rfl hn (tstep_notDone hr) hsc0 hT hFI hEO
    htv hm hbf hpx hw0 (fun _ _ h => h) (fun _ _ => trivial) hrp).2 r hr hpa
  have hA' := anchR_tstep hF hm' hBump hEO hT htv hFI hm hsc0 (TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI (.refl _) hth) hr hXa hA
  have hXa' : Ext Ea E' := Ext_trans hXa hX
  let S' : TermPtrRts.Sto := fun l =>
    if FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc l then E'.sto l else S l
  have h2 : ∀ l cl, E'.sto l = some cl → S' l = some cl := by
    intro l cl h
    by_cases hf : FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc l
    · simp only [S', hf, ↓reduceIte]; exact h
    · simp only [S', hf, ↓reduceIte]
      rcases hF.1.2.2.1 l with e | ⟨hf', -⟩
      · rw [e] at h; exact hES l cl h
      · exact absurd hf' hf
  have h3 : ∀ l cl, S l = some cl → S' l = some cl := by
    intro l cl h
    by_cases hf : FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc l
    · obtain ⟨q, hq, -, rfl⟩ := hf
      cases (h.symm.trans (hfr q hq))
    · simp only [S', hf, ↓reduceIte]; exact h
  have hNF : ∀ u ∈ r.2.2.promises, ∀ m, r.1[u]? = some m → S m.loc.label = none → S' m.loc.label = none := by
    intro u hu m hmu hS
    have hnf := promAlloc_locS (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hs hc' hscR (TermViewInv.viewInv_thread hvI hs) hwinR hth hm hSC hbf e1 e2 e3 hr hF hE' hm' hA' (.inr hXa') hu hmu
    simp only [S', hnf, ↓reduceIte]; exact hS
  have h4 : ∀ l cl, S' l = some cl → S l = none → (CE η).sto l = none ∧ E'.sto l = some cl := by
    intro l cl h hS
    by_cases hf : FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc l
    · simp only [S', hf, ↓reduceIte] at h; exact ⟨(hF.2 l hf).1, h⟩
    · simp only [S', hf, ↓reduceIte] at h; rw [h] at hS; cases hS
  have hfrS : ∀ l, FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc l → S l = none := fun l hf => by
    obtain ⟨q, hq, -, rfl⟩ := hf
    exact hfr q hq
  have hNC : ∀ q ∈ r.2.1, ∀ (m0 : Msg) (cl : Cell), r.1[q]? = some m0 → S' m0.loc.label = some cl →
      S m0.loc.label = none → TwoAtT cl.ty m0.loc.offset := by
    intro q hq m0 cl h0 hc hS
    by_cases hf : FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc m0.loc.label
    · simp only [S', hf, ↓reduceIte] at hc
      exact hNC0 q hq m0 cl h0 hc (hF.2 _ hf).1
    · simp only [S', hf, ↓reduceIte] at hc; rw [hc] at hS; cases hS
  have hNC4 : ∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), r.1[v]? = some mv → v ∉ r.2.2.promises →
      S' mv.loc.label = some cl → S mv.loc.label = none → mv.loc.offset = o + 1 → TwoAtT cl.ty o →
      (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ r.2.1, v = q + 1 := by
    intro v mv cl o hv hP hc hS ho hT
    by_cases hf : FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc mv.loc.label
    · simp only [S', hf, ↓reduceIte] at hc
      exact hNC40 v mv cl o hv hP hc (hF.2 _ hf).1 ho hT
    · simp only [S', hf, ↓reduceIte] at hc; rw [hc] at hS; cases hS
  have hLay' : ∀ l cl, S' l = some cl → LayT cl.ty := by
    intro l cl h
    by_cases hf : FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc l
    · simp only [S', hf, ↓reduceIte] at h
      rcases hF.1.2.2.1 l with e | ⟨-, T, eT, -, -, hNA⟩
      · rw [e] at h; exact hLay l cl (hES l cl h)
      · rw [eT] at h; cases h; exact layT_of_newAtT hNA
    · simp only [S', hf, ↓reduceIte] at h; exact hLay l cl h
  have hfa : ∀ l, FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc l → l ≠ a := fun l hf hla => by
    obtain ⟨cl, hcl⟩ := hsa
    have h0 := hfrS l hf
    rw [hla, hES a cl hcl] at h0
    cases h0
  have hpeq : E'.pfr a = (CE η).pfr a := by
    rcases hF.1.2.2.2.2.2.1 a with h | ⟨h, -⟩ | ⟨hf, -⟩
    · exact h
    · exact absurd h hpa0
    · exact absurd rfl (hfa a hf)
  have hlt0 : t < c.mem.size := hm.2.2.1 t (TermPtrRts.tminOf_spec ht).1
  have hold : ∀ u m, u < c.mem.size → r.1[u]? = some m → c.mem[u]? = some m := fun u m hu h => by
    exact ((TermLiveProps.tstep_ext _ _ _ _ r hr).mem.get u hu).symm.trans h
  obtain ⟨⟨hR', htm⟩, hL', hC', hG'⟩ := hK (gOf p k arch c j) (CE η) E' { pfr := (CE η).pfr, box := (CE η).box }
    { pfr := E'.pfr, box := E'.box } S S' c.mem c.pairs th a r hk hES h2 h3 h4
    (fun l f h h' => by change (CE η).pfr l = none at h'; rw [h] at h'; cases h')
    (fun l B h h' => by change (CE η).box l = none at h'; rw [h] at h'; cases h')
    (fun l f h h' => by change E'.pfr l = none at h'; rw [h] at h'; cases h')
    (fun l B h h' => by change E'.box l = none at h'; rw [h] at h'; cases h')
    (fun l f h => hX.2.2.2.2.2.2.1 l f h) (fun l B h => hX.2.2.2.2.2.2.2.2.1 l B h)
    hE hm hR (hnp th hth) hr hF hE' hpa hNF hL (hsc th hth (TermTyped.not_spawnT_of_steps hth hs)) hD hps (fun t' h => hC t' h) hG hfrS hLay hNC hNC4
    rfl hP hfa hba hB1 hPf (fun _ _ => hE) (fun t' h => hBS t' h)
  refine ⟨r.2.2, E', S', e3, hE', ?_, h2, ?_, ?_, hlb.2.trans hbf, ?_, hL', StoClo_EFoot hF.1 hSC,
    TermScope.tstep_drf hps hD hr, fun t' h => ?_, ?_, hLay', ?_, by rw [hpeq]; exact hpa0, ?_, ?_, (by rw [e1, e2]; exact hA'), hXa'⟩
  · rw [TermTyped.gOf_thread hs, e1, e2]; exact hm'
  · rw [e1, e2]; exact hR'
  · rw [e1, e2]; exact htm t ht
  · intro q hq
    rw [hlb.1, TermStep.threadSteps_n hs]
    by_cases hf : FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc (freshLabel c.lbase c.n j q)
    · simp only [S', hf, ↓reduceIte]; exact (hm'.2.2.2.1.1 q hq).1
    · simp only [S', hf, ↓reduceIte]; exact hfr q (Nat.le_trans (tstep_nalloc hr) hq)
  · rw [e1, e2] at h ⊢; exact hC' t' h
  · rw [e1, e2]; exact hG'
  · obtain ⟨cl, hcl⟩ := hsa
    rcases hF.1.2.2.1 a with h | ⟨hf, -⟩
    · exact ⟨cl, h.trans hcl⟩
    · exact absurd rfl (hfa a hf)
  · rcases hF.1.2.2.2.1 a with h | ⟨hf, -⟩
    · exact h.trans hba
    · exact absurd rfl (hfa a hf)
  · intro t' ht'
    rw [e1, e2, htm t ht] at ht'
    cases ht'
    rw [e1]
    intro l B hB o w0 hw hN f hf
    rw [hpeq] at hf
    rcases hF.1.2.2.2.1 l with hbl | ⟨hfl, -⟩
    · rw [hbl] at hB
      rcases hBS t ht l B hB o w0 hw hN f hf with h | h
      · exact .inl h
      · refine .inr fun u m hu hl hv => ?_
        by_cases hul : u < c.mem.size
        · exact h u m (hold u m hul hu) hl hv
        · exact Nat.le_trans (Nat.le_of_lt hlt0) (Nat.le_of_not_lt hul)
    · refine .inr fun u m hu hl hv => ?_
      by_cases hul : u < c.mem.size
      · exfalso
        have hu0 := hold u m hul hu
        obtain ⟨q, hq1, hq2, hql⟩ := hfl
        have hml : m.loc.label = freshLabel (gOf p k arch c j).lbase (gOf p k arch c j).n (gOf p k arch c j).i q := by
          rw [hl]; exact hql
        have hin := (hm.2.2.2.1.1 q hq1).2.1 u m hu0 hml
        have hin' := TermPtrRtsThr.alloc_noFulfil hr (Nat.lt_of_le_of_lt hq1 hq2) u hin hul
        exact promAlloc_locS (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hs hc' hscR (TermViewInv.viewInv_thread hvI hs) hwinR hth hm hSC hbf e1 e2 e3 hr hF hE' hm' hA' (.inr hXa') hin' hu
          ⟨q, hq1, hq2, hml⟩
      · exact Nat.le_trans (Nat.le_of_lt hlt0) (Nat.le_of_not_lt hul)

theorem nfInv_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {j : Nat} {a : AllocLabel} {t : Ts} {Eu Ea : TEnv}
    [ProgRetIall p] [WrIniC] (hP : ProgT p) (hK : TermPtrRts.PtrRtsThreadGL p) (hFN : FootNCB p)
    (hk : k.storeDepRts = true)
    (hps : TermScope.ProgScopeOK p = true) {c c2 : Cfg} (h : TermOwnG0Defs.SoloNP p k arch j a c c2) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    Certified p k arch c2 j → (∀ c0, Solo p k arch j c c0 → Certified p k arch c0 j → ScopeAt p j c0) →
    TermViewInv.ViewInv c →
    (∀ c0, Solo p k arch j c c0 → Certified p k arch c0 j → NoHoldPubA p k arch Eu Ea j c0) →
    NFInv p k arch j a t Eu Ea c → NFInv p k arch j a t Eu Ea c2 := by
  induction h with
  | refl => exact fun _ _ _ _ hJ => hJ
  | thread hs hnp hrest ih =>
    intro hc2 hsc hvI hwin hJ
    have hc' := certified_back hrest.toSolo hc2
    have hc := certified_back (.thread hs hrest.toSolo) hc2
    exact ih hc2 (fun c0 h0 => hsc c0 (.thread hs h0)) (TermViewInv.viewInv_thread hvI hs)
      (fun c0 h0 => hwin c0 (.thread hs h0))
      (nfInv_thread (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hK hFN hk hps hJ hs hnp hc' (hsc _ (.refl _) hc) (hwin _ (.refl _) hc) hvI
        (fun c0 h0 => hsc c0 (.thread hs h0)) (fun c0 h0 => hwin c0 (.thread hs h0)))
  | prom ad v w hw hrest ih =>
    intro hc2 hsc hvI hwin hJ
    exact ih hc2 (fun c0 h0 => hsc c0 (.prom ad v w hw h0)) (TermViewInv.viewInv_prom hvI hw)
      (fun c0 h0 => hwin c0 (.prom ad v w hw h0))
      (nfInv_prom hJ)

/-- **NoFulPlRun**, conditional on K-2a (`PtrRtsThreadGL`) and `FootNC`: along the owner's solo run not
publishing `a`, `tmin` stays an outstanding promise. -/
theorem noFulPlRunGL_of {p : Prog} {k : Promises.Knobs} {arch : Arch} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hK : TermPtrRts.PtrRtsThreadGL p) (hFN : FootNCB p) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : NoFulPlRunGL p k arch := by
  intro j a c1 th1 E1 sto t hk hES hsc hvI Eu Ea hwin hA1 hXa1 hth1 hE1 hm1 hR1 ht1 hbf hfr hL1 hSC1 hps hD1 hC1 hG1 hLay1 hsa hpa hba
    hBS c2 th2 hrun hc2 hth2
  obtain ⟨th, E, S, hth, -, -, -, -, ht, -⟩ :=
    nfInv_run (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hK hFN hk hps hrun hc2 hsc hvI hwin
      ⟨th1, E1, sto, hth1, hE1, hm1, hES, hR1, ht1, hbf, hfr, hL1, hSC1, hD1, hC1, hG1, hLay1, hsa, hpa, hba, hBS, hA1, hXa1⟩
  rw [hth2] at hth
  cases hth
  exact (TermPtrRts.tminOf_spec ht).1

end NoFulRun

end TermPtrKey

#print axioms TermPtrKey.noFulPlRunGL_of
