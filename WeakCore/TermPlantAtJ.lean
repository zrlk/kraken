import WeakCore.TermPlantAtI
import WeakCore.TermPtrKey
import WeakCore.TermPromClos
import WeakCore.TermPtrStab
import WeakCore.TermRiniCoh

/-! # TermPlantAtJ: the plant-index clause across a thread step (key gate)

`plantIdx_thread`: `PlantIdxG` (gate `KeyG`, D2 final) at the producer's post-state
`EgT Eg g n n' E' c'` with frames/holdings `upd Tot i Tot'`, `upd HP i HP'`.
* fresh labels: no frontier (`fresh_blank` + `EFoot`), so vacuous;
* frontier newly set at an old label: own cell of the stepper (`EFoot`), so a `publish l`
  (`PfrG` at `pf := PubAt th`), which consumes the own key of `l` (the `PubConsumeC`, staged
  for the route-B output; `keyHeld_not_pub_C`): key spent;
* old frontier: the old clause (old key: foreign frames unchanged; the stepper's by
  The `ownKey_noIncrease_thread_noHS`) and `idxBody_keep`, with the `tminG_thread(_fgn)`,
  `NoFulT` for the edge, `tstep_fulCoh`, `threadSteps_coh`, `fpSync` filtering.
-/

namespace TermPlantAtJ
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermLiveProps (CohAt CfgCoh)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`PlantIdxG` across a thread step of `i`.** -/
theorem plantIdx_thread {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l))
    (hk : k.storeDepRts = true)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hb1 : TermBal.AllocGT p k arch Sp Init MintOK c0)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    (hPC : TermPtrKey.PubConsumeC th C)
    (hPA : TermPromClos.PromAllocF p k arch Sp Init MintOK c0)
    (hN : TermPlantAtT.NoFulT TermPtrRts.tminG p k arch Sp Init MintOK c0)
    (hcc : CfgCoh c)
    (hI : TermPlantAtT.PlantIdxG TermPtrRts.tminG Eg Tot HP c) :
    TermPlantAtT.PlantIdxG TermPtrRts.tminG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')
      (upd Tot i Tot') (upd HP i HP') c' := by
  intro j thj l cl hthj hsto hown hpf hkey
  have hpfrE : (CE η).pfr = Eg.pfr := by rw [Y.1]; rfl
  have hext := (TermCert.tstep_appUp X.hr).2.1
  have hmem : ∀ u, u < c.mem.size → c'.mem[u]? = c.mem[u]? := fun u hu => by
    rw [X.e1]
    exact (hext u c.mem[u] (Array.getElem?_eq_getElem hu)).trans (Array.getElem?_eq_getElem hu).symm
  have hfpS : ∀ q u, u ∈ (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').fpOf q →
      u ∈ Eg.fpOf q ∨ c.mem.size ≤ u := fun q u hu =>
    Or.inl (List.mem_filter.1 (show u ∈ TermStepper.fpSync Eg c' q from hu)).1
  rw [TermOwnPub.EgT_pfr] at hpf
  by_cases hfr : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
  · exfalso
    rw [TermOwnPub.EgT_sto_fresh hfr] at hsto
    obtain ⟨hs0, -, -, hp0⟩ := fresh_blank hm hfr
    rcases Z.1.2.2.2.2.2.1 l with e | ⟨-, F', -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨-, -, e⟩
    · rw [e] at hpf; exact hpf hp0
    · rw [hs0] at hc1; cases hc1
    · rw [e] at hsto; cases hsto
  rw [TermOwnPub.EgT_sto_old hfr] at hsto
  by_cases hp0 : Eg.pfr l = none
  · exfalso
    rcases Z.1.2.2.2.2.2.1 l with e | ⟨-, F', -, -, -, hown1, -⟩ | ⟨hf, -, -⟩
    · rw [e, hpfrE] at hpf; exact hpf hp0
    · by_cases hji : j = i
      · subst hji
        have hs1 : (CE η).sto l ≠ none := by
          obtain ⟨c1, hc1, -⟩ := hown1; rw [hc1]; exact Option.some_ne_none _
        have hne : E'.pfr l ≠ (CE η).pfr l := by rw [hpfrE, hp0]; exact hpf
        have hz := TermPtrKey.keyHeld_not_pub_C hb1 X Y Z hK hPC hfr (hPfr l hs1 hne)
        unfold TermPlantAtT.KeyG at hkey
        rw [upd_self, upd_self] at hkey
        omega
      · obtain ⟨c1, hc1, ho1⟩ := hown1
        rw [Y.1] at hc1
        have h2 := TermPlantAtT.sto_of_cut hc1
        rw [hsto] at h2
        cases h2
        rw [hown, CE_tid, Y.2.1] at ho1
        exact hji (Option.some.inj ho1)
    · exact hfr hf
  by_cases hji : j = i
  · subst hji
    have e : thj = r.2.2 := by rw [X.e3] at hthj; exact (Option.some.inj hthj).symm
    subst e
    have hkey0 : TermPlantAtT.KeyG Tot HP j l := by
      have h1 := TermPtrKey.ownKey_noIncrease_thread_noHS hb1 X Y Z hK hfr
      unfold TermPlantAtT.KeyG at hkey ⊢
      rw [upd_self, upd_self] at hkey
      omega
    have h := hI j th l cl X.hth hsto hown hp0 hkey0
    obtain ⟨t, mP, htm, hmP, htP, hle, -, -⟩ := hI j th l cl X.hth hsto hown hp0 hkey0
    have hNo := hN X hk hsto hown hp0 hkey0 htm hmP htP hle
    have hfrP : ∀ u ∈ r.2.2.promises, ∀ m, r.1[u]? = some m →
        ¬ FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc m.loc.label := fun u hu m hm hF =>
      (hPA X Y (Z.toC _ _ _ _ _) hS hPfr _ hF u m hu (by rw [X.e1]; exact hm)).1 rfl
    have htm' := TermPtrStab.tminG_thread X E' hfrP
      (fun t' ht' => by rw [htm] at ht'; cases ht'; exact hNo.1) j
    exact TermPlantAtI.idxBody_keep h htm' (fun u hu => X.inv.plt j th u X.hth hu) hmem
      (fun t' m' ht' hm' _ _ => by
        rw [htm] at ht'; cases ht'; rw [hmP] at hm'; cases hm'; exact hNo)
      (TermPlantAtF.tstep_fulCoh X.hr (hcc j th X.hth))
      ((TermLiveProps.threadSteps_coh X.hc' hcc).2.2 j th r.2.2 X.hth X.e3) (hfpS j)
  · have hthj0 : c.ths[j]? = some thj := by rw [← X.ho j hji]; exact hthj
    have hkey0 : TermPlantAtT.KeyG Tot HP j l := by
      unfold TermPlantAtT.KeyG at hkey ⊢
      rw [TermPtrKey.ownKey_noIncrease_other hji l] at hkey
      exact hkey
    exact TermPlantAtI.idxBody_keep (hI j thj l cl hthj0 hsto hown hp0 hkey0)
      (TermPtrStab.tminG_thread_fgn X E' hji) (fun u hu => X.inv.plt j thj u hthj0 hu) hmem
      (fun _ _ _ _ h1 h2 => ⟨h1, h2⟩) (fun u h1 h2 => absurd h1 h2) (fun _ => Nat.le_refl _) (hfpS j)

/-- **`PlantIdxG` across a promise of `j`** (plant `TermPlantF.plantOf`, `EgP`). The planting
case is `idxBody_plant` with `plant_vWr` fed by the typed promised state (`hTE1`, `hm1`, the
producer's `ThSys`) and the `PtrRtsG` there (`hG'`); `UndefInCell` (G2) is staged. -/
theorem plantIdx_prom (hV0 : TermViewInv.ViewInvR p k arch Sp c0) {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {N : AllocLabel → Nat} {HP' HS' : Res}
    {cr' db' : Ts → Res} {S1 : AllocLabel → Prop}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hk : k.storeDepRts = true)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0)
    (hspec : PlantSpec Eg (TermPlantF.plantOf c Eg j a v w) j c.mem.size)
    (hNE : TermPtrStab.NoEdgeUnpl Eg c)
    (hU : ∀ S, TermPlantAtI.MsgInCell (Cut Eg j S) (stOf c.mem c.pairs th))
    (hNP : TermPtrKey.NoFulPlRunGL p k arch)
    (hwin1 : ∀ c2, Solo p k arch j (promise c j a v w) c2 → Certified p k arch c2 j →
      TermTyped.NoHoldPubA p k arch (Cut Eg j S1) (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size) j S1) j c2)
    (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hTE1 : ThInvE p (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size) j S1)
      { th with promises := th.promises ++ [c.mem.size] })
    (hm1 : MemInv (gOf p k arch (promise c j a v w) j)
      (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size) j S1)
      (stOf (promise c j a v w).mem (promise c j a v w).pairs { th with promises := th.promises ++ [c.mem.size] }))
    (hG' : TermPtrRts.PtrRtsGL (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size) Tot (upd HP j HP')
      (promise c j a v w))
    (hBP' : TermPtrRts.BoxPlantSep (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size) Tot (upd HP j HP')
      (promise c j a v w))
    (hI : TermPlantAtT.PlantIdxG TermPtrRts.tminG Eg Tot HP c) :
    TermPlantAtT.PlantIdxG TermPtrRts.tminG (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size) Tot
      (upd HP j HP') (promise c j a v w) := by
  intro q thq l cl hthq hsto hown hpf hkey
  have hsto0 : Eg.sto l = some cl := hsto
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hmemP : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by rw [hpi.1]
  have hmem : ∀ u, u < c.mem.size → (promise c j a v w).mem[u]? = c.mem[u]? := fun u hu => by
    rw [hmemP, Array.getElem?_push]; simp [Nat.ne_of_lt hu]
  cases hP : TermPlantF.plantOf c Eg j a v w l with
  | some f =>
    obtain ⟨hp0, ⟨c2, hc2, ho2⟩, -, -⟩ := hspec l f hP
    rw [hsto0] at hc2
    cases hc2
    rw [hown] at ho2
    cases ho2
    have e : thq = { th with promises := th.promises ++ [c.mem.size] } := by
      rw [hpi.2.1] at hthq; exact (Option.some.inj hthq).symm
    subst e
    obtain ⟨S, -, -, hm, -⟩ := X.inv.thr j th X.hth
    have hfo := X.inv.fpok j th S X.hth
    have hAn : TermTyped.AnchR (Cut Eg j S1) (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size) j S1) (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size) j S1)
        (stOf (promise c j a v w).mem (promise c j a v w).pairs { th with promises := th.promises ++ [c.mem.size] }) :=
      TermTyped.anchR_plant (s0 := stOf c.mem c.pairs th) hm.2.2.2.1.2 hm1
        (fun l0 c3 h ho => cutSto_own (TermPlantAtT.sto_of_cut (Eg := (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size))
          (i := j) (S := S1) h) ho) rfl (fun _ => Nat.le_refl _)
        (fun t m ht hm' => by
          have ht' : t ∉ th.promises ++ [c.mem.size] := ht
          have e : (promise c j a v w).mem[t]? = some m := hm'
          have hlt := (Array.getElem?_eq_some_iff.1 e).1
          rw [hmemP, Array.size_push] at hlt
          have h2 : t ≠ c.mem.size := fun h => ht' (List.mem_append_right _ (List.mem_singleton.2 h))
          refine ⟨fun h => ht' (List.mem_append_left _ h), ?_⟩
          show c.mem[t]? = some m
          rw [← hmem t (by omega)]; exact e)
        (fun l0 c3 N3 e3 us3 f0 hs3 _ _ _ _ _ h1 => by
          have h1' : (match TermPlantF.plantOf c Eg j a v w l0 with | some f => some f | none => Eg.pfr l0) = some f0 := h1
          show f0 < (promise c j a v w).mem.size
          rw [hmemP, Array.size_push]
          cases hq : TermPlantF.plantOf c Eg j a v w l0 with
          | none =>
            simp only [hq] at h1'
            exact Nat.lt_succ_of_le (Nat.le_trans (X.inv.frlt l0 c3 f0
              (TermPlantAtT.sto_of_cut (Eg := EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size) (i := j) (S := S1) hs3) h1')
              (Nat.sub_le _ _))
          | some f1 =>
            simp only [hq] at h1'
            cases h1'
            exact Nat.lt_succ_of_le (hspec l0 _ hq).2.2.1)
        (TermRiniCoh.riniCoh_prom (s := stOf c.mem c.pairs th) _ (TermRiniCoh.hltOwn_sys X.inv X.hth)
          (fun l f e => ⟨(hspec l f e).1, (hspec l f e).2.1, (hspec l f e).2.2.1⟩)
          (fun t ht => List.mem_append_left _ ht)
          (fun t ht => by show (promise c j a v w).mem[t]? = c.mem[t]?; exact hmem t ht)
          (by show (promise c j a v w).mem.size = c.mem.size + 1; rw [hmemP, Array.size_push])
          (fun _ => List.mem_append_right _ (List.mem_singleton_self _))
          hm.2.2.2.1.2 (X.inv.riniCoh j th S X.hth))
    have hpf1 : (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size).pfr l = some f := by
      show (match TermPlantF.plantOf c Eg j a v w l with | some f => some f | none => Eg.pfr l) = some f
      rw [hP]
    have htm := TermPtrStab.tminG_plant (N := N) (n := c.mem.size) hNE X.hth
      (fun _ _ h => TermPlantF.plantOf_some X.hth h) X.inv.plt hsto0 hown hp0 hP
    have hR1 := TermPtrRts.ptrRtsE_of_G hG'.1 hpi.2.1 hsto hown hpf1 hkey
    have ht1 := (TermPtrRts.tminG_eq hpi.2.1).symm.trans htm
    have hv := TermPlantAtI.plant_vWr (hV0 := hV0) X hk hNP (TermCertScope.certScopeP_of hps h0d) hwin1 hAn (sto := Eg.sto)
      (fun l0 c3 h => TermPlantAtT.sto_of_cut (Eg := EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size)
        (i := j) (S := S1) h) hTE1 hm1 hR1 ht1
      (by have hb : (promise c j a v w).boxFence = c.boxFence := by unfold promise; split <;> rfl
          rw [hb]; exact X.inv.bf)
      (fun q hq => by
        have hb : (promise c j a v w).lbase = c.lbase := by unfold promise; split <;> rfl
        rw [hb, TermStep.promise_n]; exact TermPtrKey.fresh_sto_none X.inv X.hth q hq)
      (TermPtrKey.thLbl_cut hG'.2.1 hpi.2.1)
      (fun l0 c3 h => X.inv.clo l0 c3 (TermPlantAtT.sto_of_cut (Eg := EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size)
        (i := j) (S := S1) h)) hps
      (by have hD0 := TermScope.run_drf hps h0d X.run j th X.hth
          exact ⟨hD0.ok, hD0.σs, hD0.env, hD0.stk⟩)
      (fun t' h => hG'.2.2.2 j _ l cl f hpi.2.1 hsto hown hpf1 hkey t' (by rw [TermPtrRts.tminG_eq hpi.2.1]; exact h))
      (by
        have hGW : TermPtrRts.GranuleW Eg.sto c.mem c.pairs := by
          rcases X.inv.granW hk with h | h
          · have := (Array.getElem?_eq_some_iff.1 X.hth).1
            omega
          · exact h
        rw [hmemP, show (promise c j a v w).pairs = c.pairs by rw [hpi.1]]
        exact TermGranW.granuleWP_promise (TermGranW.granuleWP_of _ hGW))
      (X.inv.stoLay hk) ⟨cl, cutSto_own hsto hown⟩
      (by rw [Cut_pfr, hpf1]; exact Option.some_ne_none f)
      (by
        rw [Cut_box]
        cases e : Eg.box l with
        | none => exact e
        | some B => rw [X.inv.boxSto l B e] at hsto0; cases hsto0)
      (fun t' ht' lb B hB o w0 hw hN f' hf' => by
        rw [Cut_box] at hB
        rw [Cut_pfr] at hf'
        exact hBP' lb B hB o w0 hw j _ l cl f' t' hpi.2.1 hsto hown hf' hkey
          (by rw [TermPtrRts.tminG_eq hpi.2.1]; exact ht') hN)
      (TermTyped.tidAt_prom (TermMain.tidAt_cutG (Eg := EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size)
        (fun th2 hth2 lb hlb => by
          obtain ⟨hs2, hp2⟩ := X.inv.tidBox j th2 hth2 lb hlb
          refine ⟨hs2, ?_⟩
          show (match TermPlantF.plantOf c Eg j a v w lb with | some f => some f | none => Eg.pfr lb) = some 0
          cases hq : TermPlantF.plantOf c Eg j a v w lb with
          | none => exact hp2
          | some f2 => rw [(hspec lb f2 hq).1] at hp2; cases hp2) S1))
      (fun th2 hth2 hl2 => by
        rw [hpi.2.1] at hth2; cases hth2
        have hb := (X.inv.tidBox j th X.hth l hl2).1
        rw [hsto0] at hb; cases hb; simp at hown)
    have hcs : (Cut Eg j S).sto l = some cl := cutSto_own hsto0 hown
    exact TermPlantAtI.idxBody_plant htm hmemP rfl rfl hv
      (fun u m hu hm2 hl => TermPlantAtI.priv_le_coh hm (hU S) hcs hown hp0 hu hm2 hl)
      (fun u hu => by
        have e2 : TermStepper.fpProm Eg j c.mem.size j = Eg.fpOf j := by simp [TermStepper.fpProm]
        exact e2 ▸ hu)
      (fun u hu => hfo.1 u hu)
      (fun u m hu hm2 hl => hfo.2 u m hu hm2 ⟨⟨cl, by rw [hl]; exact hcs, hown⟩, by rw [hl]; exact hp0⟩)
  | none =>
    have hpf0 : Eg.pfr l ≠ none := by
      have e2 : (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size).pfr l = Eg.pfr l := by
        show (match TermPlantF.plantOf c Eg j a v w l with | some f => some f | none => Eg.pfr l) = Eg.pfr l
        rw [hP]
      rw [← e2]; exact hpf
    by_cases hqj : q = j
    · subst hqj
      have e : thq = { th with promises := th.promises ++ [c.mem.size] } := by
        rw [hpi.2.1] at hthq; exact (Option.some.inj hthq).symm
      subst e
      have hkey0 : TermPlantAtT.KeyG Tot HP q l := by
        have h1 := TermPtrKey.ownKey_noIncrease_prom_noHS X hA hdb l
        unfold TermPlantAtT.KeyG at hkey ⊢
        rw [upd_self] at hkey
        simp only [Res.add_apply] at hkey ⊢
        omega
      have h := hI q th l cl X.hth hsto0 hown hpf0 hkey0
      obtain ⟨t, -, htm, -⟩ := hI q th l cl X.hth hsto0 hown hpf0 hkey0
      exact TermPlantAtI.idxBody_keep h ((TermPtrStab.tminG_prom_own_some X.hth X.inv.plt htm).trans htm.symm)
        (fun u hu => X.inv.plt q th u X.hth hu) hmem
        (fun _ _ _ _ h1 h2 => ⟨List.mem_append_left _ h1, h2⟩)
        (fun u h1 h2 => absurd (List.mem_append_left _ h1) h2) (fun _ => Nat.le_refl _)
        (fun u hu => by
          have e2 : TermStepper.fpProm Eg q c.mem.size q = Eg.fpOf q := by simp [TermStepper.fpProm]
          exact Or.inl (e2 ▸ hu))
    · have hthq0 : c.ths[q]? = some thq := by rw [← promise_other hqj]; exact hthq
      have hkey0 : TermPlantAtT.KeyG Tot HP q l := by
        unfold TermPlantAtT.KeyG at hkey ⊢
        rw [upd_other _ _ hqj] at hkey
        exact hkey
      exact TermPlantAtI.idxBody_keep (hI q thq l cl hthq0 hsto0 hown hpf0 hkey0)
        (TermPtrStab.tminG_prom_fgn X.hth X.inv.plt hqj) (fun u hu => X.inv.plt q thq u hthq0 hu) hmem
        (fun _ _ _ _ h1 h2 => ⟨h1, h2⟩) (fun u h1 h2 => absurd h1 h2) (fun _ => Nat.le_refl _)
        (fun u hu => by
          have e2 : TermStepper.fpProm Eg j c.mem.size q = Eg.fpOf q ++ [c.mem.size] := by simp [TermStepper.fpProm, hqj]
          rw [show (EgP Eg (TermPlantF.plantOf c Eg j a v w) N j c.mem.size).fpOf q =
            TermStepper.fpProm Eg j c.mem.size q from rfl, e2] at hu
          rcases List.mem_append.1 hu with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Nat.le_of_eq (List.mem_singleton.1 h1).symm))

end

end TermPlantAtJ

#print axioms TermPlantAtJ.plantIdx_thread
#print axioms TermPlantAtJ.plantIdx_prom
