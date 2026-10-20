import WeakCore.TermPoolStaging

/-! # TermPoolBal: the pool balance, net-key and rid members

Proofs of the six mechanical pool members of `TermPoolStaging`: `poolBalT`, `poolKnetT`, `poolRidT`
(thread step, at `crN`) and `poolBalP`, `poolKnetP`, `poolRidP` (promise step, pool unchanged).
Copies of `TermBal.balT_D` / `TermOwnFresh.knetT_F` / `TermBal.ridT_N` and `balP_proof` /
`knetP_proof` / `ridP_N` at the credits plus pool `crPl cr pl`:
* thread step (`keyT_pool`): the stepper kept old pool items sit at its post-step promises, a
  sublist of its old ones (`TermFul.tstep_fulfil`, nodup by `PromNodupR`), so their sum is at most
  the old pool sum (`plStep_le`); the new items `plh` and the transfer `δ = dc + dh` are paid by `IneqH`;
* promise step (`keyP_pool`): the new promise carries no pool credit (`PoolTag`: pool credits sit at
  old promises, below the memory size);
* mint room at `crPl` (`room_pool`): pool credits are key-free (`CrKeys` in `PoolTag`), so a fresh
  own label has no load at `crPl` either.
-/

namespace TermPoolBal
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCrBII TermBal TermOwnFresh TermPoolStaging
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Sums -/

theorem tsum_map_add (f g : Ts → Nat) : ∀ (L : List Ts),
    (L.map (fun t => f t + g t)).sum = (L.map f).sum + (L.map g).sum
  | [] => rfl
  | a :: L => by simp only [List.map_cons, List.sum_cons, tsum_map_add f g L]; omega

theorem tsum_zero (f : Ts → Nat) : ∀ (L : List Ts), (∀ t ∈ L, f t = 0) → (L.map f).sum = 0
  | [], _ => rfl
  | a :: L, h => by
    simp only [List.map_cons, List.sum_cons, h a (List.mem_cons_self ..),
      tsum_zero f L (fun t ht => h t (List.mem_cons_of_mem _ ht))]

theorem nsum_zero (f : Nat → Nat) (h : ∀ n, f n = 0) : ∀ (L : List Nat), (L.map f).sum = 0
  | [] => rfl
  | a :: L => by simp only [List.map_cons, List.sum_cons, h a, nsum_zero f h L]

theorem pSum_key (s : St) (f : Ts → Res) (key : Key) :
    pSum s f key = (s.promises.map (fun t => f t key)).sum := by
  unfold pSum
  rw [res_sum_apply, List.map_map]
  rfl

theorem pSum_add (s : St) (f g : Ts → Res) (key : Key) :
    pSum s (fun t => f t + g t) key = pSum s f key + pSum s g key := by
  rw [pSum_key, pSum_key, pSum_key]
  simp only [Res.add_apply]
  exact tsum_map_add _ _ _

/-- The load at the credits plus pool splits into the credit load and the pool sums. -/
theorem keyLoad_crPl (c : Cfg) (Tot HP : Nat → Res) (HS : Res) (cr pl : Nat → Ts → Res) (key : Key) :
    KeyLoad c Tot HP HS (crPl cr pl) key =
      KeyLoad c Tot HP HS cr key + ((List.range c.ths.size).map (fun n => pSumAt c n (pl n) key)).sum := by
  unfold KeyLoad
  have e : ∀ n ∈ List.range c.ths.size, (Tot n + HP n + pSumAt c n (crPl cr pl n)) key =
      (Tot n + HP n + pSumAt c n (cr n)) key + pSumAt c n (pl n) key := fun n _ => by
    show (Tot n + HP n) key + pSumAt c n (fun t => cr n t + pl n t) key = _
    rw [pSumAt_add]
    simp only [Res.add_apply]
    omega
  rw [List.map_congr_left e,
    nsum_map_add (fun n => (Tot n + HP n + pSumAt c n (cr n)) key) (fun n => pSumAt c n (pl n) key)]
  omega

/-- The balance clause at one key is the load bound. -/
theorem bal_key (c : Cfg) (Tot HP : Nat → Res) (HS : Res) (f : Nat → Ts → Res) (key : Key) :
    (thSum c.ths.size (fun i => Tot i + pSumAt c i (f i) + HP i) + HS) key = KeyLoad c Tot HP HS f key := by
  unfold KeyLoad
  rw [Res.add_apply, thSum_apply]
  have e : ∀ n ∈ List.range c.ths.size, (Tot n + pSumAt c n (f n) + HP n) key =
      (Tot n + HP n + pSumAt c n (f n)) key := fun n _ => by
    simp only [Res.add_apply]
    omega
  rw [List.map_congr_left e]

theorem debt_key (c : Cfg) (db : Nat → Ts → Res) (key : Key) :
    thSum c.ths.size (fun i => pSumAt c i (db i)) key = KeyDebt c db key := by
  unfold KeyDebt
  rw [thSum_apply]

/-- Pool credits are key-free: no own-key load. -/
theorem pl_own_zero {Eg : GEnv} {c : Cfg} {pl : Nat → Ts → Res} (htag : PoolTag Eg c pl) (n : Nat)
    (l : AllocLabel) : pSumAt c n (pl n) (.own l) = 0 := by
  cases hc : c.ths[n]? with
  | none => unfold pSumAt; rw [hc]; rfl
  | some thn =>
    rw [pSumAt_some hc, pSum_key]
    refine tsum_zero _ _ (fun t _ => ?_)
    by_cases hz : pl n t = .zero
    · rw [hz]; rfl
    · exact (htag.1 n thn t hc hz).2.1 l

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

-- Thread step

/-- The stepper pool after its step sums to at most its old pool plus the new items. -/
theorem plStep_le (hN : PromNodupR p k arch Sp c0) {c cq : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c cq Eg Tot HP HS cr db i th r) (pl : Nat → Ts → Res) (plh : Ts → Res)
    (key : Key) :
    pSum (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) key ≤
      pSumAt c i (pl i) key + pSum (stOf r.1 r.2.1 r.2.2) plh key := by
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  have hsub := (TermFul.tstep_fulfil (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hm0) X.hr).1
  have hnd : r.2.2.promises.Nodup := hsub.nodup (hN c X.run i th X.hth)
  rw [pSumAt_some X.hth, pSum_key, pSum_key, pSum_key]
  have e : ∀ t ∈ (stOf r.1 r.2.1 r.2.2).promises,
      plStep pl i (stOf r.1 r.2.1 r.2.2) plh t key = pl i t key + plh t key := fun t ht => by
    simp only [plStep, ht, ↓reduceIte, Res.add_apply]
  rw [List.map_congr_left e, tsum_map_add (fun t => pl i t key) (fun t => plh t key)]
  exact Nat.add_le_add_right
    (nsum_le_of_nodup (f := fun t => pl i t key) th.promises hnd (fun x hx _ => hsub.subset hx)) _

/-- Pointwise-bounded list sums. -/
theorem tsum_le_map {f g : Ts → Nat} (h : ∀ t, f t ≤ g t) : ∀ (L : List Ts), (L.map f).sum ≤ (L.map g).sum
  | [] => Nat.le_refl _
  | a :: L => by simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h a) (tsum_le_map h L)

/-- The stepper's kept pool share `plq` (`StepCrQ`, away from the post promises) plus its pool after
the step sums to at most its old pool plus the new items. -/
theorem plStep_leQ (hN : PromNodupR p k arch Sp c0) {c cq : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c cq Eg Tot HP HS cr db i th r) (pl : Nat → Ts → Res) (plh plq : Ts → Res)
    (hplq : ∀ t, plq t = .zero ∨ plq t = pl i t) (hnot : ∀ t, plq t ≠ .zero → t ∉ r.2.2.promises)
    (key : Key) :
    pSum (stOf c.mem c.pairs th) plq key + pSum (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) key ≤
      pSumAt c i (pl i) key + pSum (stOf r.1 r.2.1 r.2.2) plh key := by
  classical
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  have hsub := (TermFul.tstep_fulfil (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hm0) X.hr).1
  have hnd : r.2.2.promises.Nodup := hsub.nodup (hN c X.run i th X.hth)
  rw [pSumAt_some X.hth, pSum_key, pSum_key, pSum_key, pSum_key]
  have e : ∀ t ∈ (stOf r.1 r.2.1 r.2.2).promises,
      plStep pl i (stOf r.1 r.2.1 r.2.2) plh t key = pl i t key + plh t key := fun t ht => by
    simp only [plStep, ht, ↓reduceIte, Res.add_apply]
  rw [List.map_congr_left e, tsum_map_add (fun t => pl i t key) (fun t => plh t key)]
  let g : Ts → Nat := fun t => if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t key else 0
  have eg : ∀ t ∈ (stOf r.1 r.2.1 r.2.2).promises, pl i t key = g t := fun t ht => by
    simp only [g, ht, ↓reduceIte]
  rw [List.map_congr_left eg]
  have h1 := nsum_le_of_nodup (f := g) th.promises hnd (fun x hx _ => hsub.subset hx)
  have h2 : ((stOf c.mem c.pairs th).promises.map (fun t => plq t key + g t)).sum ≤
      ((stOf c.mem c.pairs th).promises.map (fun t => pl i t key)).sum := by
    refine tsum_le_map (fun t => ?_) _
    by_cases hz : plq t = .zero
    · have e0 : plq t key = 0 := by rw [hz]; rfl
      rw [e0]
      by_cases hm : t ∈ (stOf r.1 r.2.1 r.2.2).promises
      · simp only [g, hm, ↓reduceIte]; omega
      · simp only [g, hm, ↓reduceIte]; omega
    · have hm : t ∉ (stOf r.1 r.2.1 r.2.2).promises := hnot t hz
      have ep : plq t = pl i t := (hplq t).resolve_left hz
      simp only [g, hm, ↓reduceIte, ep]; omega
  rw [tsum_map_add (fun t => plq t key) g] at h2
  have h3 : ((stOf c.mem c.pairs th).promises.map g).sum = (th.promises.map g).sum := rfl
  have h4 : ((stOf r.1 r.2.1 r.2.2).promises.map g).sum = (r.2.2.promises.map g).sum := rfl
  omega

/-- **One key across a thread step at `crN`, generic in the released pool `pq`**: master of
`keyT_pool` (`pq` = the stepper's `plq`) and `TermPoolBalP.keyT_poolP` (`pq = plDis`). -/
theorem keyT_poolG (hN : PromNodupR p k arch Sp c0) {c cq : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {Totq HPq HSq C F : Res} {crq dbq δ dc dh plh pq : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c cq Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hdd : ∀ t, dc t + dh t ≤ δ t)
    (hI : ∃ Fd : List Ts, (∀ t, δ t ≠ .zero → t ∈ Fd) ∧
      Totq + (HPq + HSq) + pSum (stOf r.1 r.2.1 r.2.2) crq + pSum (stOf r.1 r.2.1 r.2.2) plh + Res.sum (Fd.map δ) +
          pSum (stOf c.mem c.pairs th) (db i) + C ≤
        Rf + Rs + (HP i + HS) + pSum (stOf c.mem c.pairs th) (cr i) + pSum (stOf c.mem c.pairs th) pq +
          pSum (stOf r.1 r.2.1 r.2.2) dbq + F)
    (key : Key) (b : Nat) (hroom : KeyLoad c Tot HP HS (crPl cr pl) key + F key ≤ b + KeyDebt c db key)
    (hpl : pSum (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) key +
        pSum (stOf c.mem c.pairs th) pq key ≤ pSumAt c i (pl i) key + pSum (stOf r.1 r.2.1 r.2.2) plh key) :
    KeyLoad cq (upd Tot i Totq) (upd HP i HPq) HSq (crN cr pl i crq (stOf r.1 r.2.1 r.2.2) plh dc dh) key ≤
      b + KeyDebt cq (upd db i dbq) key := by
  have hi : i < c.ths.size := lt_of_getq X.hth
  have hnd := hN c X.run
  obtain ⟨-, -, -, -, -, -, hsum⟩ := Y
  obtain ⟨Fd, hFd, hineq⟩ := hI
  have hI := hineq key
  have hT := congrFun hsum key
  have hδ := CrShift_sum hFd X.inv.disj hnd key (List.range c.ths.size) List.nodup_range
  have hδ2 : ((List.range c.ths.size).map (fun n => pSumAt c n (fun t => dc t + dh t) key)).sum ≤
      ((List.range c.ths.size).map (fun n => pSumAt c n δ key)).sum :=
    nsum_mono (fun n => pSumAt_mono c n hdd key)
  have eo : ∀ n, n ≠ i → pSumAt cq n (crN cr pl i crq (stOf r.1 r.2.1 r.2.2) plh dc dh n) key =
      pSumAt c n (crPl cr pl n) key + pSumAt c n (fun t => dc t + dh t) key := by
    intro n hn
    rw [thread_pSumAt_other X hn, pSumAt_key, pSumAt_key, pSumAt_key, ← tsum_map_add]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [crN, crPl, updD, hn, ↓reduceIte, Res.add_apply]
    omega
  have ei : pSumAt cq i (crN cr pl i crq (stOf r.1 r.2.1 r.2.2) plh dc dh i) key =
      pSum (stOf r.1 r.2.1 r.2.2) crq key + pSum (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) key := by
    rw [thread_pSumAt_self X]
    show pSum (stOf r.1 r.2.1 r.2.2) (fun t => updD cr i crq dc i t +
      updD pl i (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) dh i t) key = _
    rw [updD_self, updD_self]
    exact pSum_add _ _ _ _
  have ec : pSumAt c i (crPl cr pl i) key = pSum (stOf c.mem c.pairs th) (cr i) key + pSumAt c i (pl i) key := by
    show pSumAt c i (fun t => cr i t + pl i t) key = _
    rw [pSumAt_add, pSumAt_some X.hth (cr i)]
  have hsp := nsum_map_add (fun n => (Tot n + HP n + pSumAt c n (crPl cr pl n)) key)
    (fun n => pSumAt c n (fun t => dc t + dh t) key) (List.range c.ths.size)
  have hs1 := sum_range_upd (f := fun n => (Tot n + HP n + pSumAt c n (crPl cr pl n)) key +
      pSumAt c n (fun t => dc t + dh t) key)
    (g := fun n => (upd Tot i Totq n + upd HP i HPq n +
      pSumAt cq n (crN cr pl i crq (stOf r.1 r.2.1 r.2.2) plh dc dh n)) key) hi
    (fun n hn => by
      simp only [Res.add_apply]
      rw [upd_other _ _ hn, upd_other _ _ hn, eo n hn]
      omega)
  have hs2 := sum_range_upd (f := fun n => pSumAt c n (db n) key) (g := fun n => pSumAt cq n (upd db i dbq n) key) hi
    (fun n hn => by
      rw [upd_other _ _ hn, thread_pSumAt_other X hn])
  rw [upd_self, upd_self] at hs1
  rw [upd_self, thread_pSumAt_self X, pSumAt_some X.hth (db i)] at hs2
  unfold KeyLoad KeyDebt at hroom ⊢
  rw [TermStep.threadSteps_size X.hc']
  simp only [Res.add_apply] at hs1 hs2 hroom hI hT hsp ei ⊢
  omega

/-- **One key across a thread step at `crN`, at any bound `b`** (`knetT_keyB` with the pool). -/
theorem keyT_pool (hN : PromNodupR p k arch Sp c0) {c cq : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {Totq HPq HSq C F : Res} {crS crq dbq δ dc dh plh : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c cq Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hQ : StepCrQ cr pl i r.2.2.promises crS) (hdd : ∀ t, dc t + dh t ≤ δ t)
    (hI : IneqH Totq HPq HSq C F Rf Rs (HP i + HS) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) crS crq
      (db i) dbq plh δ)
    (key : Key) (b : Nat) (hroom : KeyLoad c Tot HP HS (crPl cr pl) key + F key ≤ b + KeyDebt c db key) :
    KeyLoad cq (upd Tot i Totq) (upd HP i HPq) HSq (crN cr pl i crq (stOf r.1 r.2.1 r.2.2) plh dc dh) key ≤
      b + KeyDebt cq (upd db i dbq) key
 := by
  obtain ⟨plq, hcrS, hplq, hnot⟩ := hQ
  obtain ⟨Fd, hFd, h⟩ := hI
  refine keyT_poolG (pq := plq) (C := C) hN X Y hdd ⟨Fd, hFd, Res.le_def.2 fun kk => ?_⟩ key b hroom ?_
  · have h1 := Res.le_def.1 h kk
    have e := pSum_add (stOf c.mem c.pairs th) (cr i) plq kk
    rw [show crS = fun t => cr i t + plq t from funext hcrS] at h1
    simp only [Res.add_apply] at h1 e ⊢
    omega
  · have := plStep_leQ hN X pl plh plq hplq hnot key
    omega

/-- **Mint room at the credits plus pool** (`TermOwnFresh.mintRoomF_at` at `crPl`). -/
theorem room_pool (hb1 : AllocGT p k arch Sp Init MintOK c0) (hres : TicketFreeRun p k arch Sp c0) {c cq : Cfg}
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {Eo : TEnv} {Totq HPq HSq C F : Res} {crS crq dbq δ : Ts → Res} {rc : Nat → Nat}
    (X : TCtxX p k arch Sp Init MintOK c0 c cq Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r Eo Totq HPq HSq C F crq dbq Rf Rs (HP i + HS)
      crS (db i) δ)
    (hcl : ClaimAt th.term C F) (htag : PoolTag Eg c pl) (hof : OwnFreshZ c Tot HP HS cr)
    (hrc : RidOK c Tot HP HS (crPl cr pl) db rc) (hle : rc i ≤ η.rid) :
    ∀ key, ExclKey key → F key ≠ 0 → KeyLoad c Tot HP HS (crPl cr pl) key + F key ≤ 1 + KeyDebt c db key := by
  have htid : η.tid = i := Y.2.1
  have hleq : rc η.tid ≤ η.rid := by rw [htid]; exact hle
  have ha := ridFresh_of hrc hleq
  intro key hk hF
  have hMS : MintStep (gOf p k arch c i) η (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) C F := Z.2.2.2.2.2.2.1
  have h1 := MintStep_le_one hMS key
  cases key with
  | rg n =>
    rcases TermOnce.MintStep_rg hMS n with h0 | ⟨e, -⟩ | ⟨j, hC, hf⟩
    · exact absurd h0 hF
    · subst e
      have := ha.1
      omega
    · obtain ⟨x, w, tk, e, he⟩ := hcl n j hC hf
      have h := hres c X.run i th X.hth
      rw [he] at h
      simp [exprNoTicket, opTicket] at h
  | wd n =>
    rcases TermOnce.MintStep_wd hMS n with h0 | ⟨e, -⟩
    · exact absurd h0 hF
    · subst e
      have := ha.2
      omega
  | own l =>
    obtain ⟨j, hj1, -, hl⟩ := hb1 X Y (Z.toC _ _ _ _ _) l hF
    have hlq : l = freshLabel c.lbase c.n i j := hl
    subst hlq
    rw [keyLoad_crPl, keyLoad_zero hof X.hth hj1, nsum_zero _ (fun n => pl_own_zero htag n _)]
    omega
  | _ => exact hk.elim

/-- **`poolBalT`**: the balance after a thread step at `crN`, mint `M + F`. -/
theorem poolBalT_of : poolBalT p k arch Sp Init MintOK c0 := by
  intro hM hN c cq Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs Eo Totq HPq HSq C F crS crq dbq δ dc dh plh X Y Z hQ hdd hP
    _ hI
  obtain ⟨M, hMo, hb⟩ := hP.bal
  refine ⟨M + F, hM X Y (Z.toC _ _ _ (cr i) (db i)) M hMo, Res.le_def.2 fun key => ?_⟩
  have hold := hb key
  have e1 := bal_key c Tot HP HS (crPl cr pl) key
  have e2 := debt_key c db key
  simp only [Res.add_apply] at hold e1
  have h := keyT_pool (pl := pl) hN X Y hQ hdd hI key (Init key + M key + F key) (by omega)
  have g1 := bal_key cq (upd Tot i Totq) (upd HP i HPq) HSq (crN cr pl i crq (stOf r.1 r.2.1 r.2.2) plh dc dh) key
  have g2 := debt_key cq (upd db i dbq) key
  simp only [Res.add_apply] at g1 ⊢
  omega

/-- **`poolKnetT`**: net key bounds after a thread step at `crN`. -/
theorem poolKnetT_of : poolKnetT p k arch Sp Init MintOK c0 := by
  intro hb1 hres hN c cq Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs Eo Totq HPq HSq C F crS crq dbq δ dc dh plh rc
    X Y Z hQ hdd hP _ _ _ hI hcl hof hrc hle key hk
  have hroom : KeyLoad c Tot HP HS (crPl cr pl) key + F key ≤ 1 + KeyDebt c db key := by
    by_cases hF : F key = 0
    · have := hP.knet key hk
      rw [keyNet_iff] at this
      omega
    · exact room_pool hb1 hres X Y Z hcl hP.tag hof hrc hle key hk hF
  exact keyT_pool hN X Y hQ hdd hI key 1 hroom

/-- **`poolRidT`**: rid freshness after a thread step at `crN` (`ridT_N` with the pool). -/
theorem poolRidT_of : poolRidT p k arch Sp Init MintOK c0 := by
  intro hres hN c cq Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs Eo Totq HPq HSq C F crS crq dbq δ dc dh plh rc
    X Y Z hQ hdd _ _ hI hcl hrc hle
  have htid : η.tid = i := Y.2.1
  have hleq : rc η.tid ≤ η.rid := by rw [htid]; exact hle
  obtain ⟨-, hU, hmono⟩ := TermOnce.fresh_bump hleq
  refine ⟨TermOnce.ridSet rc η.tid (η.rid + 1), fun n hn key hkey => ?_⟩
  have hn0 : ¬ TermOnce.RidUsed rc n := fun h => hn (hmono n h)
  have hnf : n ≠ ridNext η := fun e => hn (e ▸ hU)
  have hcl : ∀ j, ¬ (C = Res.one (.ep n j) ∧ F = Res.one (.rg n)) := fun j ⟨h1, h2⟩ => by
    obtain ⟨x, w, tk, e, he⟩ := hcl n j h1 h2
    have h := hres c X.run i th X.hth
    rw [he] at h
    simp [exprNoTicket, opTicket] at h
  have hMS : MintStep (gOf p k arch c i) η (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) C F := Z.2.2.2.2.2.2.1
  have hF0 : F key = 0 := by
    rcases hkey with rfl | rfl
    · rcases TermOnce.MintStep_rg hMS n with h0 | ⟨e, -⟩ | ⟨j, h1, h2⟩
      · exact h0
      · exact absurd e hnf
      · exact absurd ⟨h1, h2⟩ (hcl j)
    · rcases TermOnce.MintStep_wd hMS n with h0 | ⟨e, -⟩
      · exact h0
      · exact absurd e hnf
  have hold : KeyLoad c Tot HP HS (crPl cr pl) key ≤ KeyDebt c db key := hrc n hn0 key hkey
  have h := keyT_pool (pl := pl) hN X Y hQ hdd hI key 0 (by omega)
  unfold KeyLoad KeyDebt at h
  omega

-- Promise step

/-- **One key across a promise step at `crPl`, at any bound `b`** (pool unchanged). -/
theorem keyP_pool {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HPq HSq : Res} {crq dbq : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HPq + HSq) (cr j) (db j) crq dbq)
    (htag : PoolTag Eg c pl) (key : Key) (b : Nat)
    (hold : KeyLoad c Tot HP HS (crPl cr pl) key ≤ b + KeyDebt c db key) :
    KeyLoad (promise c j a v w) Tot (upd HP j HPq) HSq (crPl (upd cr j crq) pl) key ≤
      b + KeyDebt (promise c j a v w) (upd db j dbq) key := by
  have hj : j < c.ths.size := lt_of_getq X.hth
  unfold PAcct at hA
  have hAq := congrFun hA key
  have hz : pl j c.mem.size = .zero := Classical.byContradiction fun hne =>
    Nat.lt_irrefl _ (X.inv.plt j th _ X.hth (htag.1 j th _ X.hth hne).1)
  have eo : ∀ n, n ≠ j → pSumAt (promise c j a v w) n (crPl (upd cr j crq) pl n) = pSumAt c n (crPl cr pl n) :=
    fun n hn => by
      rw [promise_pSumAt_other hn]
      unfold crPl
      rw [upd_other _ _ hn]
  have ej : pSumAt (promise c j a v w) j (crPl (upd cr j crq) pl j) key =
      pSum (promSt (stOf c.mem c.pairs th) a v w) crq key + pSum (stOf c.mem c.pairs th) (pl j) key := by
    rw [promise_pSumAt_self X.hth]
    show pSum (promSt (stOf c.mem c.pairs th) a v w) (fun t => upd cr j crq j t + pl j t) key = _
    rw [upd_self, pSum_add]
    congr 1
    rw [pSum_key, pSum_key]
    show ((th.promises ++ [c.mem.size]).map (fun t => pl j t key)).sum = (th.promises.map (fun t => pl j t key)).sum
    rw [List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hz, Res.zero_apply, Nat.add_zero]
  have ec : pSumAt c j (crPl cr pl j) key = pSum (stOf c.mem c.pairs th) (cr j) key +
      pSum (stOf c.mem c.pairs th) (pl j) key := by
    rw [pSumAt_some X.hth]
    exact pSum_add _ _ _ _
  have hs1 := sum_range_upd (f := fun n => (Tot n + HP n + pSumAt c n (crPl cr pl n)) key)
    (g := fun n => (Tot n + upd HP j HPq n + pSumAt (promise c j a v w) n (crPl (upd cr j crq) pl n)) key) hj
    (fun n hn => by
      rw [upd_other _ _ hn, eo n hn])
  have hs2 := sum_range_upd (f := fun n => pSumAt c n (db n) key)
    (g := fun n => pSumAt (promise c j a v w) n (upd db j dbq n) key) hj
    (fun n hn => by
      rw [upd_other _ _ hn, promise_pSumAt_other hn])
  rw [upd_self] at hs1
  rw [upd_self, promise_pSumAt_self X.hth, pSumAt_some X.hth] at hs2
  unfold KeyLoad KeyDebt at hold ⊢
  rw [TermStep.promise_size]
  simp only [Res.add_apply] at hs1 hs2 hold hAq ej ec ⊢
  omega

/-- **`poolBalP`**: the balance after a promise step, same mint. -/
theorem poolBalP_of : poolBalP p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db pl j th a v w HPq HSq crq dbq X hA hP
  obtain ⟨M, hMo, hb⟩ := hP.bal
  refine ⟨M, hMo, Res.le_def.2 fun key => ?_⟩
  have hold := hb key
  have e1 := bal_key c Tot HP HS (crPl cr pl) key
  have e2 := debt_key c db key
  simp only [Res.add_apply] at hold e1
  have h := keyP_pool X hA hP.tag key (Init key + M key) (by omega)
  have g1 := bal_key (promise c j a v w) Tot (upd HP j HPq) HSq (crPl (upd cr j crq) pl) key
  have g2 := debt_key (promise c j a v w) (upd db j dbq) key
  simp only [Res.add_apply] at g1 ⊢
  omega

/-- **`poolKnetP`**: net key bounds after a promise step. -/
theorem poolKnetP_of : poolKnetP p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db pl j th a v w HPq HSq crq dbq X hA hP key hk
  exact keyP_pool X hA hP.tag key 1 (hP.knet key hk)

/-- **`poolRidP`**: rid freshness after a promise step, same counters. -/
theorem poolRidP_of : poolRidP p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db pl j th a v w HPq HSq crq dbq X hA hP
  obtain ⟨rc, hrc⟩ := hP.rid
  refine ⟨rc, fun n hn key hkey => ?_⟩
  have h := keyP_pool X hA hP.tag key 0 (Nat.le_trans (hrc n hn key hkey) (Nat.le_add_left _ 0))
  unfold KeyLoad KeyDebt at h
  omega

end

#print axioms keyT_poolG

end TermPoolBal

#print axioms TermPoolBal.keyT_pool
#print axioms TermPoolBal.keyP_pool
#print axioms TermPoolBal.room_pool
#print axioms TermPoolBal.poolBalT_of
#print axioms TermPoolBal.poolKnetT_of
#print axioms TermPoolBal.poolRidT_of
#print axioms TermPoolBal.poolBalP_of
#print axioms TermPoolBal.poolKnetP_of
#print axioms TermPoolBal.poolRidP_of
